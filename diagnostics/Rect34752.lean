import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_34752.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_34752
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffeffffffffffff,0xfefefffffffefffefffc,0xfffffafaeeeeaa00ffff,0xfffffffffffeffffffff,0xfffffefefffffffefffe,0xfffcfffffafaeeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[4,7]⟩,⟨.or,[1,2]⟩,⟨.or,[3,9]⟩,⟨.or,[2,4]⟩,⟨.or,[1,5]⟩,⟨.or,[5,7]⟩,⟨.or,[3,5]⟩,⟨.or,[8,14]⟩,⟨.and,[6,10]⟩,⟨.and,[15,0]⟩,⟨.and,[8,12]⟩,⟨.and,[13,11]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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
def g49Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g49C : List ColumnInfo := []
def g49A : List (List Nat) := [[],[84],[64],[64,80],[80,64],[80]]
def g49D3 (j : Nat) := if j=0 then 0x7 else 0
def g49L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g49D3)
  | _ => emptyPacking
def g49I (_ _ : Nat) : Option (Nat × Nat) := none
def g49 : Forest := ⟨49,3,fun i => g49Y[i]?.getD (0,0),g49C,g49A,g49L,g49I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49P3_0 : CutRow g49 3 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g49B3 : CutRow g49 3 0 1 := g49P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49T : mixedTables g49 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g49 0 0
  · exact mixedEmpty g49 1 0
  · exact mixedEmpty g49 2 0
  · exact g49B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49G : graphValid g49 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low49 : Lower true (varsX 49) (graphGoal 49) 4 := mixedLower (g:=g49) (i:=0) (hints:=4) (before_sound [] baseKnown) g49G g49T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K49 := extendKnown [] 4 [(49,[]),(145,[117,101]),(146,[16,117,101]),(161,[84,116,100]),(164,[32,16,84,116,100]),(176,[64,16,33,50,83,115,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V49 : Known true K49 := extend_ok (m:=49) baseKnown low49 (by decide +kernel)
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
theorem g27G : graphValid g27 (boundsBefore K49) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := mixedLower (g:=g27) (i:=0) (hints:=67) (before_sound K49 V49) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K49 4 [(27,[]),(45,[33,84]),(54,[80,32,50]),(75,[96,16,49,67,84]),(77,[96,16,33,50,67,84]),(83,[16,99,83]),(86,[16,32,67,99,83]),(89,[48,65,33,96,32,82]),(90,[16,48,32,66,98,82]),(102,[32,83,100]),(105,[48,81,33,96,64]),(114,[16,80,32,99]),(116,[32,65,99,81]),(139,[116,84,101]),(141,[33,116,84,101]),(195,[16,99,116,83,84]),(197,[32,16,99,116,83,84]),(201,[97,33,115,67,82,84]),(202,[16,48,32,114,100,82]),(212,[32,65,99,113,81]),(226,[16,80,32,99,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V49 low27 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3de871ff81fc7ffc7b,0xd0e3ff03f8fff8f7a1c7])),(BitVec.ofNat 152 (word80 [0x81a892451429080903,0x51248a2852101206a249]))),((BitVec.ofNat 152 (word80 [0xc6980e3ffe007cff8d,0x301c7ffc00f9ff1a6038])),(BitVec.ofNat 152 (word80 [0x169adb66193212902d,0x35b6cc326425205a6b6d]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfb978fffffff80fff7,0x2f1fffffff01ffee5e3f])),(BitVec.ofNat 152 (word80 [0x124882040202000,0x2491040804040000492]))),((BitVec.ofNat 152 (word80 [0x66ff03fffffff000c,0xdfe07ffffffe0019bfc0])),(BitVec.ofNat 152 (word80 [0x26464930418040c24c,0x8c926083008184991924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := [(2,0,49,0,4)]
def g51A : List (List Nat) := [[],[80]]
def g51D4 (j : Nat) := if j=0 then 0x1f else 0
def g51L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g51D4)
  | _ => emptyPacking
def g51I (_ _ : Nat) : Option (Nat × Nat) := none
def g51 : Forest := ⟨51,4,fun i => g51Y[i]?.getD (0,0),g51C,g51A,g51L,g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51P4_0 : CutRow g51 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51B4 : CutRow g51 4 0 1 := g51P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : mixedTables g51 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g51 0 0
  · exact mixedEmpty g51 1 0
  · exact mixedEmpty g51 2 0
  · exact mixedEmpty g51 3 0
  · exact g51B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 5 := mixedLower (g:=g51) (i:=0) (hints:=68) (before_sound K27 V27) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K27 5 [(51,[]),(53,[33,84]),(150,[16,32,116,84,101]),(153,[64,49,33,117,101]),(166,[32,116,100]),(210,[64,97,32,50,49,117]),(228,[80,97,32,49,66,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V27 low51 (by decide +kernel)
def g147Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0)]
def g147C : List ColumnInfo := [(1,0,146,0,4)]
def g147A : List (List Nat) := [[],[116],[16],[16,116]]
def g147D4 (j : Nat) := if j=0 then 0x1f else 0
def g147L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g147D4)
  | _ => emptyPacking
def g147I (_ _ : Nat) : Option (Nat × Nat) := none
def g147 : Forest := ⟨147,4,fun i => g147Y[i]?.getD (0,0),g147C,g147A,g147L,g147I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147P4_0 : CutRow g147 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g147B4 : CutRow g147 4 0 1 := g147P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147T : mixedTables g147 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g147 0 0
  · exact mixedEmpty g147 1 0
  · exact mixedEmpty g147 2 0
  · exact mixedEmpty g147 3 0
  · exact g147B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147G : graphValid g147 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low147 : Lower true (varsX 147) (graphGoal 147) 5 := mixedLower (g:=g147) (i:=0) (hints:=68) (before_sound K51 V51) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K147 := extendKnown K51 5 [(147,[]),(178,[16,80,32,50]),(180,[32,65,49,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V147 : Known true K147 := extend_ok (m:=147) V51 low147 (by decide +kernel)
def g177Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g177C : List ColumnInfo := [(1,0,176,0,4),(16,0,161,0,4),(32,0,145,0,4),(128,0,49,0,4)]
def g177A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116],[64],[64,117],[64,80],[64,80,112],[64,112,80],[64,112],[80,64],[80,64,116],[80],[80,112],[80,116],[80,116,64],[112,64,84],[112,64],[112,80],[112],[112,84,64],[112,84]]
def g177D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g177D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g177H4 (j : Nat) := if j=0 then 0x241c else 0
def g177D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g177H5 := limbs80 #[#[0x800008c125509f30c008,0x3483]]
def g177D6 (j : Nat) := if j=0 then 0x3904f else 0
def g177H6 := limbs80 #[#[0x1000001620071001ea,0x424000000000000]]
def g177L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g177D3)
  | 4 => (3,2,2,0,0,5,0,g177D4)
  | 5 => (1,1,2,0,0,0,0,g177D5)
  | 6 => (1,0,2,0,0,0,0,g177D6)
  | _ => emptyPacking
def g177I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 3 0 5 1 0 g177H4
  | 5 => lookupWord 2 11 2 9 2 3 g177H5
  | 6 => lookupWord 1 17 0 9 0 5 g177H6
  | _ => fun _ => none
def g177 : Forest := ⟨177,6,fun i => g177Y[i]?.getD (0,0),g177C,g177A,g177L,g177I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P3_0 : CutRow g177 3 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B3 : CutRow g177 3 0 2 := g177P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P4_0 : CutRow g177 4 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B4 : CutRow g177 4 0 3 := g177P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P5_0 : CutRow g177 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B5 : CutRow g177 5 0 1 := g177P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P6_0 : CutRow g177 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B6 : CutRow g177 6 0 1 := g177P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177T : mixedTables g177 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g177 0 0
  · exact mixedEmpty g177 1 0
  · exact mixedEmpty g177 2 0
  · exact g177B3
  · exact g177B4
  · exact g177B5
  · exact g177B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177G : graphValid g177 (boundsBefore K147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low177 : Lower true (varsX 177) (graphGoal 177) 7 := mixedLower (g:=g177) (i:=0) (hints:=4) (before_sound K147 V147) g177G g177T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K177 := extendKnown K147 7 [(177,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V177 : Known true K177 := extend_ok (m:=177) V147 low177 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff003ff80fffffff0,0x3ffffe03ff4b19901c7])),(BitVec.ofNat 152 (word80 [0x2a1a8251a148a02a1,0xa84a0a458a44b1811249]))),((BitVec.ofNat 152 (word80 [0x7ffffc0000ffc07fff,0xfc00ffffc068db260038])),(BitVec.ofNat 152 (word80 [0x44c132362c191344c9,0x326c8c891360d3265b6d]))),((BitVec.ofNat 152 (word80 [0x7fffffffff00007fff,0xffff0000000ff00e8e00])),(BitVec.ofNat 152 (word80 [0x1705c0b8305e1c1701,0xc0702f0e1c0db00eb6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x800000000000007fff,0xffffffffff99af6d703f])),(BitVec.ofNat 152 (word80 [0x180600c04060201802,0x80300000190c082492]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x60080300008000600c,0x300c010202240704924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(2,0,53,0,5)]
def g55A : List (List Nat) := [[],[33,84]]
def g55D5 (j : Nat) := if j=0 then 0x3f else 0
def g55L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g55D5)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,5,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P5_0 : CutRow g55 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B5 : CutRow g55 5 0 1 := g55P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : mixedTables g55 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g55 0 0
  · exact mixedEmpty g55 1 0
  · exact mixedEmpty g55 2 0
  · exact mixedEmpty g55 3 0
  · exact mixedEmpty g55 4 0
  · exact g55B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K177) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 6 := mixedLower (g:=g55) (i:=0) (hints:=1348) (before_sound K177 V177) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K177 6 [(55,[]),(59,[80,50]),(61,[64,33,49,80]),(157,[64,33,49,112,80,101]),(171,[80,50,116,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V177 low55 (by decide +kernel)
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
theorem g79G : graphValid g79 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 5 := mixedLower (g:=g79) (i:=0) (hints:=16778851) (before_sound K55 V55) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K55 5 [(79,[]),(94,[64,33,49]),(110,[80,50,64]),(143,[48,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V55 low79 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe001ffc07ff01ffe00,0x3fffff80ffd35632000f])),(BitVec.ofNat 152 (word80 [0x48d4128d0522c8549a,0x92522916299346225555]))),((BitVec.ofNat 152 (word80 [0xfffe00007fffffffff,0xc007ffff01a3adc80ff0])),(BitVec.ofNat 152 (word80 [0x80981b160644809813,0x36032244d030cc81111]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfff80000003f407df000])),(BitVec.ofNat 152 (word80 [0x2e05c18178702e01c,0x380bc387033007d3333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x130160205808130120,0x2404c00000643114aaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1c01800060001c01c0,0x38070040808cd300cccc]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := []
def g87A : List (List Nat) := [[],[32,100]]
def g87D4 (j : Nat) := if j=0 then 0x1f else 0
def g87L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g87D4)
  | _ => emptyPacking
def g87I (_ _ : Nat) : Option (Nat × Nat) := none
def g87 : Forest := ⟨87,4,fun i => g87Y[i]?.getD (0,0),g87C,g87A,g87L,g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P4_0 : CutRow g87 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g87B4 : CutRow g87 4 0 1 := g87P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87T : mixedTables g87 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g87 0 0
  · exact mixedEmpty g87 1 0
  · exact mixedEmpty g87 2 0
  · exact mixedEmpty g87 3 0
  · exact g87B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 5 := mixedLower (g:=g87) (i:=0) (hints:=16778820) (before_sound K79 V79) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K79 5 [(87,[]),(103,[33,84]),(107,[16,48,82,32,100,64]),(122,[48,82,100]),(234,[48,82,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V79 low87 (by decide +kernel)
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
theorem g91G : graphValid g91 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := mixedLower (g:=g91) (i:=0) (hints:=16777283) (before_sound K87 V87) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K87 7 [(91,[]),(118,[16,32,67,99,83]),(203,[116,84]),(205,[33,116,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007fffe1ffc00ffe1,0xfffffc3cf28ce6007c1f])),(BitVec.ofNat 152 (word80 [0x4850280444288a2144,0x420208803208c65294a5]))),((BitVec.ofNat 152 (word80 [0xfff803ffffffff0001,0xff0fffc3517a93f003e0])),(BitVec.ofNat 152 (word80 [0x8261304801300c0988,0x420900a413882318c63]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc001ffffffffe,0xffffcadd91c0f83ff])),(BitVec.ofNat 152 (word80 [0x8041108841104200,0x8844200084c018842108]))),((BitVec.ofNat 152 (word80 [0x1fffffffff,0xfff000004f27e80ffc00])),(BitVec.ofNat 152 (word80 [0x130582611182208c01,0x1008c110492721294a52]))),((BitVec.ofNat 152 (word80 [0xffffffffe000000000,0x33aa61bf00000])),(BitVec.ofNat 152 (word80 [0x1c0603801e03c0f011,0xe08f02213a8619ce739c]))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(0,64,49,2,5),(64,0,51,0,5),(1,0,114,0,4),(2,64,49,0,4),(32,0,83,0,4)]
def g115A : List (List Nat) := [[],[80]]
def g115D4 (j : Nat) := if j=0 then 0x57d4d20 else 0
def g115D5 := limbs80 #[#[0x480e140fd30ff20fd20,0x4088]]
def g115H5 (j : Nat) := if j=0 then 0x80 else 0
def g115D6 (j : Nat) := if j=0 then 0x18989f else 0
def g115H6 := limbs80 #[#[0xb60800000000000391c,0x200]]
def g115L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g115D4)
  | 5 => (3,1,3,0,0,5,0,g115D5)
  | 6 => (1,0,3,0,0,0,0,g115D6)
  | _ => emptyPacking
def g115I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g115H5
  | 6 => lookupWord 1 13 0 7 2 1 g115H6
  | _ => fun _ => none
def g115 : Forest := ⟨115,6,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P4_0 : CutRow g115 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B4 : CutRow g115 4 0 1 := g115P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P5_0 : CutRow g115 5 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B5 : CutRow g115 5 0 3 := g115P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P6_0 : CutRow g115 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B6 : CutRow g115 6 0 1 := g115P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : mixedTables g115 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g115 0 0
  · exact mixedEmpty g115 1 0
  · exact mixedEmpty g115 2 0
  · exact mixedEmpty g115 3 0
  · exact g115B4
  · exact g115B5
  · exact g115B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 7 := mixedLower (g:=g115) (i:=0) (hints:=16777284) (before_sound K91 V91) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K91 7 [(115,[]),(117,[33,84]),(121,[64,49,33]),(213,[33,116,84]),(217,[64,49,33,117]),(218,[64,97,32,50,49,117]),(227,[116]),(233,[80,49,33,64,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V91 low115 (by decide +kernel)
def g151Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffc07fe03fff,0xe00ffffe07f469d401c7])),(BitVec.ofNat 152 (word80 [0xa0a86a128d0a458a05,0x46a250a4b29029d49249]))),((BitVec.ofNat 152 (word80 [0xfffff00007fffc07f,0xfff007fff813a68c0e38])),(BitVec.ofNat 152 (word80 [0xc1304c1b160c891309,0x84c360c924d1a28c9249]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000007f,0xfffff800000bc8b47000])),(BitVec.ofNat 152 (word80 [0x5c1705c182f0e1c2e,0x70382f1c70bc8b5b6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(BitVec.ofNat 152 (word80 [0x60180602030102030,0x8040300000654212492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x80200800040000040,0x10080400000000024924]))),(0x0,0x0)]
def g151C : List ColumnInfo := [(1,0,150,0,5)]
def g151A : List (List Nat) := [[],[16]]
def g151D5 (j : Nat) := if j=0 then 0x3f else 0
def g151L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g151D5)
  | _ => emptyPacking
def g151I (_ _ : Nat) : Option (Nat × Nat) := none
def g151 : Forest := ⟨151,5,fun i => g151Y[i]?.getD (0,0),g151C,g151A,g151L,g151I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151P5_0 : CutRow g151 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g151B5 : CutRow g151 5 0 1 := g151P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151T : mixedTables g151 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g151 0 0
  · exact mixedEmpty g151 1 0
  · exact mixedEmpty g151 2 0
  · exact mixedEmpty g151 3 0
  · exact mixedEmpty g151 4 0
  · exact g151B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151G : graphValid g151 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 6 := mixedLower (g:=g151) (i:=0) (hints:=1860) (before_sound K115 V115) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K115 6 [(151,[]),(167,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V151 : Known true K151 := extend_ok (m:=151) V115 low151 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ffff0fffc03f,0xfff0fffff9560600f0ff])),(BitVec.ofNat 152 (word80 [0x202828140220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffffc01fff0ffffc0,0x1fff0ff01cb5390f0f00])),(BitVec.ofNat 152 (word80 [0x40b0305814020b0305,0x81402042189511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffe0000ffffff,0xe0000fff23b56600000f])),(BitVec.ofNat 152 (word80 [0x8ac141615844ac2426,0x15844a8023b164eeeeee]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30181806088300808,0x6000304014868444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0202018000c03030,0x18088c08462084888888]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(0,8,146,1,5),(2,0,153,0,5),(8,0,147,0,5),(1,8,146,0,4),(16,0,139,0,4),(128,0,27,0,4)]
def g155A : List (List Nat) := [[],[116]]
def g155D4 (j : Nat) := if j=0 then 0x5dd4543 else 0
def g155D5 (j : Nat) := if j=0 then 0x108404fd43 else 0
def g155H5 (j : Nat) := if j=0 then 0x20 else 0
def g155D6 (j : Nat) := if j=0 then 0x2c458bf else 0
def g155H6 (j : Nat) := if j=0 then 0x40 else 0
def g155L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g155D4)
  | 5 => (1,1,3,0,0,0,0,g155D5)
  | 6 => (1,0,3,0,0,0,0,g155D6)
  | _ => emptyPacking
def g155I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g155H5
  | 6 => lookupWord 1 2 0 4 0 0 g155H6
  | _ => fun _ => none
def g155 : Forest := ⟨155,6,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P4_0 : CutRow g155 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B4 : CutRow g155 4 0 1 := g155P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_0 : CutRow g155 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B5 : CutRow g155 5 0 1 := g155P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P6_0 : CutRow g155 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B6 : CutRow g155 6 0 1 := g155P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : mixedTables g155 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g155 0 0
  · exact mixedEmpty g155 1 0
  · exact mixedEmpty g155 2 0
  · exact mixedEmpty g155 3 0
  · exact g155B4
  · exact g155B5
  · exact g155B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K151) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 7 := mixedLower (g:=g155) (i:=0) (hints:=67) (before_sound K151 V151) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K151 7 [(155,[]),(173,[33,84]),(211,[16,99,83]),(242,[16,80,32,99]),(244,[32,65,99,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V151 low155 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fe3fc03fc3f8ffe0,0x3fc7fff1d67c000f0f0f])),(BitVec.ofNat 152 (word80 [0x141482828288120142,0x82904024047c11111111]))),((BitVec.ofNat 152 (word80 [0xfe003fffc003ff1fff,0xc007e7fe313b00f000f0])),(BitVec.ofNat 152 (word80 [0x189913131311204983,0x13209240b13b55555555]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffc001fff,0xfff807ffc5a10f00f0ff])),(BitVec.ofNat 152 (word80 [0x202004040400400204,0x4010080000022222222]))),((BitVec.ofNat 152 (word80 [0xffffc0000000001fff,0xfffff8003bc8f000ff00])),(BitVec.ofNat 152 (word80 [0x40c018181821848c08,0x180203093b8044444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x810020202002001010,0x20040400000088888888]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(2,0,177,0,7)]
def g179A : List (List Nat) := [[],[116],[80],[80,116]]
def g179D7 (j : Nat) := if j=0 then 0x3f else 0
def g179L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g179D7)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,7,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P7_0 : CutRow g179 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B7 : CutRow g179 7 0 1 := g179P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : mixedTables g179 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g179 0 0
  · exact mixedEmpty g179 1 0
  · exact mixedEmpty g179 2 0
  · exact mixedEmpty g179 3 0
  · exact mixedEmpty g179 4 0
  · exact mixedEmpty g179 5 0
  · exact mixedEmpty g179 6 0
  · exact g179B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 8 := mixedLower (g:=g179) (i:=0) (hints:=68) (before_sound K155 V155) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K155 8 [(179,[]),(181,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V155 low179 (by decide +kernel)
def g182Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x3fc7f1ffd31dc000f00f])),(BitVec.ofNat 152 (word80 [0x1448a4a45121102292,0x82902488430dc5555555]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0xc007fffc23ba600f00f0])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b03,0xb214011219a63333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c04,0xc0188201c1222222222]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443018,0x100200c2026494444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x20040100000008888888]))),(0x0,0x0)]
def g182C : List ColumnInfo := [(2,0,180,0,5),(4,0,178,0,5),(16,0,166,0,5),(32,0,150,0,5)]
def g182A : List (List Nat) := [[],[33,84]]
def g182D6 (j : Nat) := if j=0 then 0x2709f else 0
def g182L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g182D6)
  | _ => emptyPacking
def g182I (_ _ : Nat) : Option (Nat × Nat) := none
def g182 : Forest := ⟨182,6,fun i => g182Y[i]?.getD (0,0),g182C,g182A,g182L,g182I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P6_0 : CutRow g182 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B6 : CutRow g182 6 0 1 := g182P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182T : mixedTables g182 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g182 0 0
  · exact mixedEmpty g182 1 0
  · exact mixedEmpty g182 2 0
  · exact mixedEmpty g182 3 0
  · exact mixedEmpty g182 4 0
  · exact mixedEmpty g182 5 0
  · exact g182B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182G : graphValid g182 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low182 : Lower true (varsX 182) (graphGoal 182) 7 := mixedLower (g:=g182) (i:=0) (hints:=270599488) (before_sound K179 V179) g182G g182T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K182 := extendKnown K179 7 [(182,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V182 : Known true K182 := extend_ok (m:=182) V179 low182 (by decide +kernel)
def g185Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc7fc07fc7ffffc07f,0xc7ffffff909d100f0fff])),(BitVec.ofNat 152 (word80 [0x80081008010008100,0x80100100000001111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff8007f87fff80,0x7f87f87aacdc000000f])),(BitVec.ofNat 152 (word80 [0x5155125512a1552255,0x14a152102acdceeeeeee]))),((BitVec.ofNat 152 (word80 [0x7ffffff8007fffff,0xf8007ff87b2860f0f0f0])),(BitVec.ofNat 152 (word80 [0x6206040600c2060406,0xc20401322822222222]))),((BitVec.ofNat 152 (word80 [0xff80000000007fffff,0xffff80000ff28f00ff00])),(BitVec.ofNat 152 (word80 [0x801818182304180818,0x10018220dd004444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x6020600400603060,0x260460444006d8888888]))),(0x0,0x0)]
def g185C : List ColumnInfo := [(8,0,177,0,7)]
def g185A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116]]
def g185D7 (j : Nat) := if j=0 then 0x3f else 0
def g185L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g185D7)
  | _ => emptyPacking
def g185I (_ _ : Nat) : Option (Nat × Nat) := none
def g185 : Forest := ⟨185,7,fun i => g185Y[i]?.getD (0,0),g185C,g185A,g185L,g185I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P7_0 : CutRow g185 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B7 : CutRow g185 7 0 1 := g185P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185T : mixedTables g185 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g185 0 0
  · exact mixedEmpty g185 1 0
  · exact mixedEmpty g185 2 0
  · exact mixedEmpty g185 3 0
  · exact mixedEmpty g185 4 0
  · exact mixedEmpty g185 5 0
  · exact mixedEmpty g185 6 0
  · exact g185B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185G : graphValid g185 (boundsBefore K182) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low185 : Lower true (varsX 185) (graphGoal 185) 8 := mixedLower (g:=g185) (i:=0) (hints:=3) (before_sound K182 V182) g185G g185T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K185 := extendKnown K182 8 [(185,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V185 : Known true K185 := extend_ok (m:=185) V182 low185 (by decide +kernel)
def g199Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x1ff80ffc0009ede81c0])),(BitVec.ofNat 152 (word80 [0x45a8a51a2a458a12a2,0xd4251a148b009e8eb6db]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfe0000fffff8da218e07])),(BitVec.ofNat 152 (word80 [0x8130362c0c891304c0,0x98362c191248d2019249]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffffff00000ff10e7038])),(BitVec.ofNat 152 (word80 [0x1c038300f0e1c0700,0xe038301e1c0ad10a1249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580b,0x14000a000112c646db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x18040c0202500704924]))),(0x0,0x0)]
def g199C : List ColumnInfo := [(2,0,197,0,4)]
def g199A : List (List Nat) := [[],[33]]
def g199D4 (j : Nat) := if j=0 then 0x3f else 0
def g199L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g199D4)
  | _ => emptyPacking
def g199I (_ _ : Nat) : Option (Nat × Nat) := none
def g199 : Forest := ⟨199,4,fun i => g199Y[i]?.getD (0,0),g199C,g199A,g199L,g199I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199P4_0 : CutRow g199 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g199B4 : CutRow g199 4 0 1 := g199P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199T : mixedTables g199 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g199 0 0
  · exact mixedEmpty g199 1 0
  · exact mixedEmpty g199 2 0
  · exact mixedEmpty g199 3 0
  · exact g199B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199G : graphValid g199 (boundsBefore K185) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low199 : Lower true (varsX 199) (graphGoal 199) 5 := mixedLower (g:=g199) (i:=0) (hints:=16778855) (before_sound K185 V185) g199G g199T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K199 := extendKnown K185 5 [(199,[]),(206,[48,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V199 : Known true K199 := extend_ok (m:=199) V185 low199 (by decide +kernel)
def g214Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0)]
def g214C : List ColumnInfo := [(4,0,210,0,5)]
def g214A : List (List Nat) := [[],[113,98]]
def g214D5 (j : Nat) := if j=0 then 0x3f else 0
def g214L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g214D5)
  | _ => emptyPacking
def g214I (_ _ : Nat) : Option (Nat × Nat) := none
def g214 : Forest := ⟨214,5,fun i => g214Y[i]?.getD (0,0),g214C,g214A,g214L,g214I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214P5_0 : CutRow g214 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g214B5 : CutRow g214 5 0 1 := g214P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214T : mixedTables g214 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g214 0 0
  · exact mixedEmpty g214 1 0
  · exact mixedEmpty g214 2 0
  · exact mixedEmpty g214 3 0
  · exact mixedEmpty g214 4 0
  · exact g214B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g214G : graphValid g214 (boundsBefore K199) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low214 : Lower true (varsX 214) (graphGoal 214) 6 := mixedLower (g:=g214) (i:=0) (hints:=285279808) (before_sound K199 V199) g214G g214T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K214 := extendKnown K199 6 [(214,[]),(230,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V214 : Known true K214 := extend_ok (m:=214) V199 low214 (by decide +kernel)
def g248Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc003ff0ffc3ffc00ff,0xffffffc02b3e79000fc0])),(BitVec.ofNat 152 (word80 [0x90a80a204890a92a42,0x91204088292e194d34d3]))),((BitVec.ofNat 152 (word80 [0xfffc000fffffffff00,0x3ff0fffec8a9d703f03f])),(BitVec.ofNat 152 (word80 [0x2304c411002300c13,0x4209020009d3145145]))),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x4c090026104c03004,0x584120172a00828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2702e08b8227024098,0x26009c110691e4b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x3803000c00380380e0,0x3808e0208d5204c30c30]))),(0x0,0x0)]
def g248C : List ColumnInfo := [(0,8,176,64,5)]
def g248A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116],[99],[99,117],[99,84],[99,84,116],[99,116,84],[99,116]]
def g248D5 (j : Nat) := if j=0 then 0x3f else 0
def g248L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g248D5)
  | _ => emptyPacking
def g248I (_ _ : Nat) : Option (Nat × Nat) := none
def g248 : Forest := ⟨248,5,fun i => g248Y[i]?.getD (0,0),g248C,g248A,g248L,g248I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g248P5_0 : CutRow g248 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g248B5 : CutRow g248 5 0 1 := g248P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g248T : mixedTables g248 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g248 0 0
  · exact mixedEmpty g248 1 0
  · exact mixedEmpty g248 2 0
  · exact mixedEmpty g248 3 0
  · exact mixedEmpty g248 4 0
  · exact g248B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g248G : graphValid g248 (boundsBefore K214) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low248 : Lower true (varsX 248) (graphGoal 248) 6 := mixedLower (g:=g248) (i:=0) (hints:=1128620032) (before_sound K214 V214) g248G g248T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K248 := extendKnown K214 6 [(248,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V248 : Known true K248 := extend_ok (m:=248) V214 low248 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xffe29798e321cb00f0ff])),(BitVec.ofNat 152 (word80 [0x14000a8004a001480,0x14e0948880008a111111]))),((BitVec.ofNat 152 (word80 [0xffffc0000ffffc0,0x7d409d2ed1b2000f00])),(BitVec.ofNat 152 (word80 [0xa6a0532836ca09910,0x666d409d2e5182bbbbbb]))),((BitVec.ofNat 152 (word80 [0xfffffffff000000,0x1cf88f852b660f0000])),(BitVec.ofNat 152 (word80 [0x3380a9c02a700ade02,0xb814d88c852b66777777]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffff,0xff216395b13d3d00000f])),(BitVec.ofNat 152 (word80 [0x5c0cce033380cce024,0xc0016315313d35eeeeee]))),((BitVec.ofNat 152 (word80 [0xfff000000000000000,0x115e685ddcf0f00ff0])),(BitVec.ofNat 152 (word80 [0x6000f0003c000f0007,0x100a40418c70444444]))),(0xcea977125e06fff000,(BitVec.ofNat 152 (word80 [0x800f0003c000f00038,0xa2133125000888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,6),(4,0,59,0,6),(8,0,55,0,6),(0,4,27,32,5),(1,0,54,0,4),(1,8,54,0,4),(16,2,45,0,4),(32,4,27,0,4)]
def g63A : List (List Nat) := [[],[33,84],[64,33,49,80],[64,49],[80,50],[80,49,33,64]]
def g63D4 (j : Nat) := if j=0 then 0x4d576d0630 else 0
def g63D5 := limbs80 #[#[0x5d0630bdd9510f9d4910,0x930c0b759230f]]
def g63H5 (j : Nat) := if j=0 then 0x8 else 0
def g63D6 := limbs80 #[#[0xb0942c07f503bc61f510,0x1908328d3081d4a]]
def g63H6 := limbs80 #[#[0x3112214c00001078107c,0x2a1e]]
def g63D7 (j : Nat) := if j=0 then 0x3ea881bf else 0
def g63H7 := limbs80 #[#[0x180000000000000001,0xc0024322000000111090,0xea1090801940000001c,0x44b00000]]
def g63L : Nat → Packing
  | 4 => (1,3,3,0,0,0,0,g63D4)
  | 5 => (4,2,3,0,0,5,0,g63D5)
  | 6 => (3,1,3,0,0,6,0,g63D6)
  | 7 => (1,0,3,0,0,0,0,g63D7)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g63H5
  | 6 => lookupWord 2 11 2 9 2 3 g63H6
  | 7 => lookupWord 3 31 1 9 2 3 g63H7
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P4_0 : CutRow g63 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B4 : CutRow g63 4 0 1 := g63P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : CutRow g63 5 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : CutRow g63 5 0 4 := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : CutRow g63 6 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_2 : CutRow g63 6 2 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : CutRow g63 6 0 3 := (@joinRow g63 6 0 2 1 g63P6_0 g63P6_2)
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
  · exact g63B4
  · exact g63B5
  · exact g63B6
  · exact g63B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K248) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := mixedLower (g:=g63) (i:=0) (hints:=1347) (before_sound K248 V248) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K248 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V248 low63 (by decide +kernel)
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
def K95 := extendKnown K63 8 [(95,[]),(111,[33,84]),(126,[64,33,49,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8001fffffff00ff55,0xa23193a23c000003f03f])),(BitVec.ofNat 152 (word80 [0x510d44251052161455,0x822190a2289249249249]))),((BitVec.ofNat 152 (word80 [0xffffe0007fffff00eb,0x7e8d8016080fc0000fc0])),(BitVec.ofNat 152 (word80 [0x6049813604642426e9,0x76098006005145145145]))),((BitVec.ofNat 152 (word80 [0xffffffff800000001d,0x8e4ae985c3f000fc0000])),(BitVec.ofNat 152 (word80 [0x800e00380178383819,0x8a0a8185c030c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff20,0x49c585ecf4003f000fff])),(BitVec.ofNat 152 (word80 [0x21008402180000000,0x8c40508d52492492492]))),((BitVec.ofNat 152 (word80 [0x11,0x75383e5b40003ffff000])),(BitVec.ofNat 152 (word80 [0x46011804600404000,0x75102a50024924924924]))),((BitVec.ofNat 152 (word80 [0xce,0x937660389bffc0000000])),(BitVec.ofNat 152 (word80 [0x7801e007800808006,0x17460381b8e38e38e38]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7),(2,0,117,0,7),(4,0,115,0,7),(0,64,49,6,6),(64,0,55,0,6),(16,0,103,0,5),(32,0,87,0,5)]
def g119A : List (List Nat) := [[],[33,84]]
def g119D5 (j : Nat) := if j=0 then 0x4fb7059243 else 0
def g119D6 := limbs80 #[#[0xed8143bd58443be58043,0x59243fed8143e7d0e43b,0x401413142f3185b400bf,0x1002628]]
def g119H6 (j : Nat) := if j=0 then 0x0 else 0
def g119D7 := limbs80 #[#[0x47888807f90ffa87fc43,0x6a1474365a981d90ea61,0x190e]]
def g119H7 := limbs80 #[#[0x30000000,0x620000000000d5000000,0xc900c300110014]]
def g119D8 (j : Nat) := if j=0 then 0x468817f else 0
def g119H8 (j : Nat) := if j=0 then 0x68520000076 else 0
def g119L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g119D5)
  | 6 => (6,2,3,0,0,6,0,g119D6)
  | 7 => (3,1,3,0,0,7,0,g119D7)
  | 8 => (1,0,3,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g119H6
  | 7 => lookupWord 1 29 0 8 3 1 g119H7
  | 8 => lookupWord 1 7 0 7 2 1 g119H8
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
theorem g119G : graphValid g119 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := mixedLower (g:=g119) (i:=0) (hints:=16778564) (before_sound K95 V95) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K95 9 [(119,[]),(123,[80,50]),(125,[64,33,49,80]),(235,[80,50,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V95 low119 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0xfe98ba2e079c9000f0ff])),(BitVec.ofNat 152 (word80 [0x5805000a8012801480,0x5290a82c040881111111]))),((BitVec.ofNat 152 (word80 [0xfc003fffc0003fffc0,0x1e50ab87c19600f0f00])),(BitVec.ofNat 152 (word80 [0x9029805300db009901,0x99a50aa8641843333333]))),((BitVec.ofNat 152 (word80 [0x3fffffffc00000,0x738da5275700f00000])),(BitVec.ofNat 152 (word80 [0xe0ce0a9c0a9c0ade0a,0xe0718ca5275707777777]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffff,0xfc85179497b3d000000f])),(BitVec.ofNat 152 (word80 [0x1702ce02ce02ce013,0x5179093b35eeeeeee]))),((BitVec.ofNat 152 (word80 [0xffffc0000000000000,0x45f462f96d0f000ff0])),(BitVec.ofNat 152 (word80 [0x1800f000f000f001c,0x401442994504444444]))),(0x0,0x0),(0x0,0x0),(0x33a4dd980e26ffff000,(BitVec.ofNat 152 (word80 [0x20030003000300020,0xa411000a028888888]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(4,0,155,0,7)]
def g159A : List (List Nat) := [[]]
def g159D7 (j : Nat) := if j=0 then 0x7f else 0
def g159L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g159D7)
  | _ => emptyPacking
def g159I (_ _ : Nat) : Option (Nat × Nat) := none
def g159 : Forest := ⟨159,7,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_0 : CutRow g159 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B7 : CutRow g159 7 0 1 := g159P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : mixedTables g159 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g159 0 0
  · exact mixedEmpty g159 1 0
  · exact mixedEmpty g159 2 0
  · exact mixedEmpty g159 3 0
  · exact mixedEmpty g159 4 0
  · exact mixedEmpty g159 5 0
  · exact mixedEmpty g159 6 0
  · exact g159B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 8 := mixedLower (g:=g159) (i:=0) (hints:=1859) (before_sound K119 V119) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K119 8 [(159,[]),(175,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V119 low159 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffff800fffffe03,0xfecbaa01b20000f00f0f])),(BitVec.ofNat 152 (word80 [0x148a01506a0940a458,0xa6cb0a00321111111111]))),((BitVec.ofNat 152 (word80 [0xffc07fffff001ffffc,0x34e5baa81000f0000f0])),(BitVec.ofNat 152 (word80 [0x191322624c4d88c891,0x334e5a2a815555555555]))),((BitVec.ofNat 152 (word80 [0x7fffffffe00000,0xd372d62500f000f000])),(BitVec.ofNat 152 (word80 [0x5e1c0b80700e02f0e1,0xc0c332d6253333333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf922299d6b0f000f00ff])),(BitVec.ofNat 152 (word80 [0x60200c008010030000,0x202195082222222222]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(BitVec.ofNat 152 (word80 [0x8000300300600c0102,0x10c428c04444444444]))),(0x0,0x0),(0x665142404fffff00000,(BitVec.ofNat 152 (word80 [0x40040080100000,0x8888888888]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(2,0,181,0,8)]
def g183A : List (List Nat) := [[],[33,84]]
def g183D8 (j : Nat) := if j=0 then 0x7f else 0
def g183L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
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
  · exact mixedEmpty g183 5 0
  · exact mixedEmpty g183 6 0
  · exact mixedEmpty g183 7 0
  · exact g183B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := mixedLower (g:=g183) (i:=0) (hints:=1348) (before_sound K159 V159) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K159 9 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V159 low183 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffc03ffffff,0xec8bac8b448000f0f0ff])),(BitVec.ofNat 152 (word80 [0xa005000808000080,0x28020880448111111111]))),((BitVec.ofNat 152 (word80 [0xfff0007ffffc03ffc0,0x19246d9c8e200f000f00])),(BitVec.ofNat 152 (word80 [0x28c2961450a0a8a109,0x98246c9c860555555555]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff80000003ffff,0xcd31f67620a00000000f])),(BitVec.ofNat 152 (word80 [0xb10b1859613132ca11,0x531f676202eeeeeeeee]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x2531855ba60f00f0ff0])),(BitVec.ofNat 152 (word80 [0x20020018000000c02,0x2011001382222222222]))),(0x45c462c771f000ff000,(BitVec.ofNat 152 (word80 [0x3c03c01e01c1c0f01c,0x45c442c021444444444]))),(0x0,0x0),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0xc00c00600202030020,0x1808340014888888888]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(2,0,185,0,8)]
def g187A : List (List Nat) := [[],[116]]
def g187D8 (j : Nat) := if j=0 then 0x7f else 0
def g187L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g187D8)
  | _ => emptyPacking
def g187I (_ _ : Nat) : Option (Nat × Nat) := none
def g187 : Forest := ⟨187,8,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : CutRow g187 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : CutRow g187 8 0 1 := g187P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : mixedTables g187 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g187 0 0
  · exact mixedEmpty g187 1 0
  · exact mixedEmpty g187 2 0
  · exact mixedEmpty g187 3 0
  · exact mixedEmpty g187 4 0
  · exact mixedEmpty g187 5 0
  · exact mixedEmpty g187 6 0
  · exact mixedEmpty g187 7 0
  · exact g187B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 9 := mixedLower (g:=g187) (i:=0) (hints:=67) (before_sound K183 V183) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K183 9 [(187,[]),(189,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc00ffffffffffffff,0x4c25363f4a4801f0001f])),(BitVec.ofNat 152 (word80 [0x481610542128429029,0x4804363e02414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff800,0xf0155d26a8b03e0003e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cc,0xf015542288a0c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d2d30f87c0007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,0x388452830f80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bd9e8000f801f])),(BitVec.ofNat 152 (word80 [0x1c047008e011c0180,0x89c801d9aa94a5294a]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0x262215c2005294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x52288407016318c6318]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,7)]
def g207A : List (List Nat) := [[],[33],[48,118],[48,33,118]]
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
theorem g207G : graphValid g207 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := mixedLower (g:=g207) (i:=0) (hints:=16778851) (before_sound K187 V187) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K187 8 [(207,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V187 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0xb361d03e280001f0001f])),(BitVec.ofNat 152 (word80 [0x42a135092845216141,0xb261d01428294a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x16e8554587003e007fe0])),(BitVec.ofNat 152 (word80 [0x4c02601b006424262,0x10605505810842108421]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c2c299d107c00f8000])),(BitVec.ofNat 152 (word80 [0x17003801c017838381,0x98c24019d118c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4fe283ab8f8000003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x48a282a105294a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [9,0x1711a3877600000ffc00])),(BitVec.ofNat 152 (word80 [0xe00b805c02e0040408,0x711a28226e739ce739c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x41140240048421084210]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(2,0,213,0,7),(4,0,211,0,7),(0,64,145,6,6),(1,0,214,0,6),(64,0,151,0,6),(16,0,199,0,5),(65,0,150,0,5),(128,0,87,0,5),(18,0,197,0,4),(129,0,86,0,4)]
def g215A : List (List Nat) := [[]]
def g215D5 := limbs80 #[#[0x35d2a6c0a9eb954d8153,0xc]]
def g215D6 := limbs80 #[#[0xb58853bd58453be58053,0x54130d7d4e53bed8153b,0x5130f794d30f754d30fe,0x330bfd9530bf59530ef5,0x30ef55330f754f30fed4,0xdf54f50df54d50bf597,0xfed8153fe18153bf58f5,0xf95153ef55153bfd8153,0x95253ef55253bf58253e,0x483c2a1800bf59653ef,0xc96908a847e78726c666,0x8d2ccc6c0bab4aea8a29,0x11f00872021701c3ded,0x147c03c]]
def g215H6 (j : Nat) := if j=0 then 0x341c else 0
def g215D7 := limbs80 #[#[0xd50ff987f4c37ca9bd54,0xa7fe53fea9ff14ffea1f,0xd0bf4d9f0ba3e0f803fe,0x478c0c291228c059d445,0x82453c60628a72c60614,0x828c1239451818e314d1,0x8a3028e410ce58c07194,0xa41460918e41]]
def g215H7 := limbs80 #[#[0xe40000780,0x7480000000000000000,0x8000000000000000000c,0x5980000000011,0x2e0000000002de000071,0x9180000770000000009d,0xdb0000000001880000,0x192aa00000d00000000,0xa25c00c08039b7100594,0xe3a,0x500003d60000728e6000,0x3]]
def g215D8 (j : Nat) := if j=0 then 0x3421017f else 0
def g215H8 := limbs80 #[#[0x900000000f300c80044c,0x800056d591d2c77]]
def g215L : Nat → Packing
  | 5 => (2,3,4,0,0,3,0,g215D5)
  | 6 => (27,2,4,0,0,8,0,g215D6)
  | 7 => (10,1,4,0,0,9,0,g215D7)
  | 8 => (1,0,4,0,0,0,0,g215D8)
  | _ => emptyPacking
def g215I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 0 5 1 0 g215H6
  | 7 => lookupWord 6 101 2 9 5 0 g215H7
  | 8 => lookupWord 2 17 2 8 4 0 g215H8
  | _ => fun _ => none
def g215 : Forest := ⟨215,8,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_0 : CutRow g215 5 0 2 := by
  apply polarBlock (data:=fun _ => (word80 [0x20004020520,0x11420200040205201142])) rfl
  decide +kernel
theorem g215B5 : CutRow g215 5 0 2 := g215P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_0 : CutRow g215 6 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_5 : CutRow g215 6 5 22 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400a1502c,0x4241004400a1502c4261,0x4400a1502c42610044,0xa1502c4241004400a1,0x502c4261004400a1502c,0x4261004400a1502c4241,0x4400a1502c42300044,0xa1502c4230004400a1,0x502c4241004400a1502c,0x4241004400a1502c4241,0x4400a1502c42410044,0xa1502c4261004400a1,0x502c4231004400a1502c,0x4230004400a1502c4241,0x4400a1502c42410044,0xa1502c4261004400a1,0x502c4231004400a1502c,0x4231004400a1502c4230])) rfl
  decide +kernel
theorem g215B6 : CutRow g215 6 0 27 := (@joinRow g215 6 0 5 22 g215P6_0 g215P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : CutRow g215 7 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_2 : CutRow g215 7 2 8 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B7 : CutRow g215 7 0 10 := (@joinRow g215 7 0 2 8 g215P7_0 g215P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P8_0 : CutRow g215 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B8 : CutRow g215 8 0 1 := g215P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : mixedTables g215 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g215 0 0
  · exact mixedEmpty g215 1 0
  · exact mixedEmpty g215 2 0
  · exact mixedEmpty g215 3 0
  · exact mixedEmpty g215 4 0
  · exact g215B5
  · exact g215B6
  · exact g215B7
  · exact g215B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 9 := mixedLower (g:=g215) (i:=0) (hints:=16778820) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 9 [(215,[]),(231,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffff83fffff628eb,0x10b3680003f800003fff])),(BitVec.ofNat 152 (word80 [0x10a0810801040220a2,0x10816812244891224489]))),((BitVec.ofNat 152 (word80 [0xffffc1ffe02d788,0x15ccc201fc000fffc000])),(BitVec.ofNat 152 (word80 [0x2c00a004008225088,0x150c40060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff000001ffffbd84c,0x8b211e000007f000007f])),(BitVec.ofNat 152 (word80 [0x83042c10885001d84c,0x920164c993264c99326]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f4,0x691ab3fe0000001fff80])),(BitVec.ofNat 152 (word80 [0x240130000260480440,0x2812932850a142850a14]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x91713,0xa28774000007ffe00000])),(BitVec.ofNat 152 (word80 [0x3809c0211380880713,0xa28320b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0xc00e00421c01048915,0x424004c183060c183060]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(0,8,146,65,6),(0,64,145,10,6),(1,8,146,64,5),(2,64,145,8,5),(8,64,145,2,5),(9,0,210,0,5),(72,0,147,0,5),(17,0,202,0,4),(18,0,201,0,4),(24,0,195,0,4),(65,0,146,0,4),(65,8,146,0,4),(129,0,90,0,4),(144,0,75,0,4),(192,0,27,0,4)]
def g219A : List (List Nat) := [[],[116],[16,99],[16,99,116]]
def g219D5 := limbs80 #[#[0x54d504c3965855354130,0x30e5b61]]
def g219D6 := limbs80 #[#[0x3aca9aa09847f7558d10,0xfb2a698221fc5453044,0x437cb2a60887db634c11,0x10bf2ea98221bed95304,0x4436ea9ac6885fb754c1,0xd10cf8eab1a21b7dcd63,0x34433fbaac6884fd7558,0x8d109faebb1a213fdd56,0x614c37db0aa0984ff75d,0x54d309faebb0a61b754f,0x5654c33fb2aa89875d51,0x3d89409fae3b2a613fdc,0xd7614cafdb82a6a06ed5,0x71d81539fae3b2a653f5,0x825221f1c191603004fd,0x643403d3a3734312e2b2,0x4615e5b5855524f4c494,0x3302c0218806]]
def g219H6 := limbs80 #[#[0x6c0000025,0xc120]]
def g219D7 := limbs80 #[#[0xf58d10fe4c110bbd8940,0xd8530fe54130bfd8d10b,0x9530bf59530f754d30bf,0x153bfd9532bfd8532bfd,0x40ff55130ff4c520bfd8,0xff54d10ff54d42ff54d,0xff54d20ffd8d10ff58d1,0xf59130ff58530ff54530,0x58953ff58153ff59530f,0x94a44cea2b0600a400ff,0x6a7a4e7f9221f7d9bf5e,0xb08c0afcbdaf0baae4b2,0x8f9718680245c6b14c3,0xc1418014a1b913a2108e,0x10165830081c34386088,0x11a3921a212c3151870c,0x8d4c0e025183860a1012,0x393243438608080c0249,0x8a440f1438608092e11a,0xe2404c70e100881e2850,0x202072810b0c1070c100,0x46303068e107]]
def g219H7 := limbs80 #[#[0x360000000000c5248184,0x4cc20001340010cb008,0xbb349000105bc1925c04,0x1e1a4778c029a2,0x95001c364e58b0010240,0xd0e04a88b17a1fc04005,0x414d8e185cba2293000]]
def g219D8 := limbs80 #[#[0xd32fea07f4c3fa41fd10,0x3288cc36007f54ffa85f,0x70658e22242402234f66,0x9228432099638642862c,0x32079428c94451cd025,0x50c996330920594284a9,0x1c64e48a180]]
def g219H8 := limbs80 #[#[0x120400006000183815e1,0x6145a0a0580000000000,0x4ac6600104800489f315,0x800d8d0440000069c001,0x100124000000a4c634c1,0x3844719322d7670074,0xc1000c08c5c588000,0x80000000008d69fa1b0c,0x38000000000010fc10ac,0x22001f1e8cc85fdb8310,0x74bc980008a6]]
def g219D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g219H9 := limbs80 #[#[0x19400cd0000161000012,0x7d3d8130021,0x11800c40000000000000,0x90000091000010c00,0x27380001280000]]
def g219L : Nat → Packing
  | 5 => (2,4,5,0,0,3,0,g219D5)
  | 6 => (29,3,5,0,0,8,0,g219D6)
  | 7 => (26,2,5,0,0,10,0,g219D7)
  | 8 => (7,1,5,0,0,9,0,g219D8)
  | 9 => (1,0,5,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 17 0 6 1 1 g219H6
  | 7 => lookupWord 8 47 5 11 5 2 g219H7
  | 8 => lookupWord 11 73 5 11 5 2 g219H8
  | 9 => lookupWord 3 41 2 9 3 2 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : CutRow g219 5 0 2 := by
  apply polarBlock (data:=fun _ => (word80 [0x4404432036,0x4220010400190c164821])) rfl
  decide +kernel
theorem g219B5 : CutRow g219 5 0 2 := g219P5_0
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
theorem g219P6_2 : CutRow g219 6 2 27 := by
  apply polarBlock (data:=fun _ => (word80 [0x10400190c16,0x48420028005228168150,0x60a28160a20b200a04,0x60305a0516200200281,0x60a20950010400190c16,0x48420060a28160a20b20,0x824028340a2c1600104,0x190c1648320060a281,0x60a20b200060a28160a2,0xb200044044321144230,0x10400190c1648420104,0x190c16484201040019,0xc164842010400190c16,0x4842010400190c164842,0x10400190c1648420104,0x190c16483201040019,0xc164832010400190c16,0x4831010400190c164831,0x10400190c1648310104,0x190c16483101040019,0xc164821010400190c16,0x4821010400190c164820])) rfl
  decide +kernel
theorem g219B6 : CutRow g219 6 0 29 := (@joinRow g219 6 0 2 27 g219P6_0 g219P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : CutRow g219 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_1 : CutRow g219 7 1 11 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_12 : CutRow g219 7 12 4 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_16 : CutRow g219 7 16 10 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400c1603442410044,0xc16034424100440443,0x21144241004800824024,0x8251010400190c164842,0x10400190c1648420044,0xc16034424101040019,0xc164842010400190c16,0x4842010400190c164842])) rfl
  decide +kernel
theorem g219B7 : CutRow g219 7 0 26 := (@joinRow g219 7 0 12 14 (@joinRow g219 7 0 1 11 g219P7_0 g219P7_1) (@joinRow g219 7 12 4 10 g219P7_12 g219P7_16))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : CutRow g219 8 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : CutRow g219 8 0 7 := g219P8_0
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
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0x451d37930c4801f003ff])),(BitVec.ofNat 152 (word80 [0x581400540128029029,0x40141692044042108421]))),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff800,0xfa255c2e0c903e007c00])),(BitVec.ofNat 152 (word80 [0x90a602980db01320cc,0xea055c220c80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d2d3ab80000f8000])),(BitVec.ofNat 152 (word80 [0xe13844e089c11bc170,0x3944d293a982d6b5ad6b]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bd9efc000001f])),(BitVec.ofNat 152 (word80 [0x1c017002e005c0180,0x2894809d9898c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0xaa214c1205294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x1522a0402036318c6318]))),(0x0,0x0)]
def g222C : List ColumnInfo := [(4,0,218,0,7)]
def g222A : List (List Nat) := [[]]
def g222D7 (j : Nat) := if j=0 then 0x7f else 0
def g222L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g222D7)
  | _ => emptyPacking
def g222I (_ _ : Nat) : Option (Nat × Nat) := none
def g222 : Forest := ⟨222,7,fun i => g222Y[i]?.getD (0,0),g222C,g222A,g222L,g222I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P7_0 : CutRow g222 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B7 : CutRow g222 7 0 1 := g222P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222T : mixedTables g222 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g222 0 0
  · exact mixedEmpty g222 1 0
  · exact mixedEmpty g222 2 0
  · exact mixedEmpty g222 3 0
  · exact mixedEmpty g222 4 0
  · exact mixedEmpty g222 5 0
  · exact mixedEmpty g222 6 0
  · exact g222B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : graphValid g222 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 8 := mixedLower (g:=g222) (i:=0) (hints:=285304384) (before_sound K219 V219) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K219 8 [(222,[]),(238,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V219 low222 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff83ffffffc1f530a,0x312e3a40000fc003f03f])),(BitVec.ofNat 152 (word80 [0x8508210020840130a,0x1243205145145145145]))),((BitVec.ofNat 152 (word80 [0x3ff83fffe0206a,0xe621f48003f03f000fc0])),(BitVec.ofNat 152 (word80 [0x2610020809002200a,0x6401b0830c30c30c30c3]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0003fffffb49c,0x90d84280fc0000fc0fff])),(BitVec.ofNat 152 (word80 [0x108004410420000094,0x90184008208208208208]))),((BitVec.ofNat 152 (word80 [0xffffffffc000008945,0x6856a9bf000000fff000])),(BitVec.ofNat 152 (word80 [0x2300088008c0848840,0x68428892492492492492]))),((BitVec.ofNat 152 (word80 [0x9171,0x19b1dc4000003f000000])),(BitVec.ofNat 152 (word80 [0xbc022f022f01089171,0x19b04c7cf3cf3cf3cf3c]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0xc00430043002104401,0x2800560820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(0,64,177,2,8),(64,0,179,0,8),(1,0,242,0,7),(2,64,177,0,7),(16,0,227,0,7),(32,0,211,0,7),(128,0,115,0,7),(33,0,210,0,5),(17,0,226,0,4),(48,0,195,0,4),(129,0,114,0,4),(160,0,83,0,4)]
def g243A : List (List Nat) := [[],[116],[80],[80,116]]
def g243D5 := limbs80 #[#[0x4c950483d254d524c120,0x483b2595324c120f4953,0x5d5324c120ecb654c930,0x54120d69755493048372,0xe6b6354950482da61532,0x81a50e02dae0d5254120,0x201e32b26]]
def g243D6 := limbs80 #[#[0x3b4a92a0907c9324c120,0xfd2a49824137dcd6548,0x83f4992a0907d9534c12,0x20bf6e0b2a41db54d524,0x4837db2a60906f9654c1,0x920df6c6a82417e5d530,0x248377b2a64906ed654c,0x4920ddac6a9241fadc15,0x53482f7b9aa4906ef635,0xd8d209feeab1a413f5d9,0x165482efb9aca904fd75,0x359520db8e6b2a41bedc,0xcf654827fb9aca906df7,0x73581529feeca92613f5,0xe4b110027eb9ec0a95df,0x9489e4c2490a7839194b,0x369a8ce6430978b6582a,0x8842a08fe7c3c9d8e670,0x1710d0927317884e61c4,0x40220100402071e0]]
def g243H6 := limbs80 #[#[0x28003a8000000170,0xf2a400c60000000001a2,0x14192583002abdc583,0x90000000048400]]
def g243D7 := limbs80 #[#[0xb4c920fe54120fe4c120,0xd8d20bf58d20fb54920f,0x8152bfd9520bf59520bf,0x930ff59520ff54d20bfd,0x20ffd8152ff58152ff54,0x360a81f84e09000ff58d,0x7f9ce691865d14a4b0fc,0x80b35a4188c739071622,0xce2586248c44cd588728,0xc81492241b11f31c8c44,0x810a2225859331d5c76c,0x2c80a4d714a6cc6156cc,0x871a245050718a215584,0x1a4c70485288564c704]]
def g243H7 := limbs80 #[#[0xc83400e2b0a491401182,0x15641a3860000062ae0,0xe17c140008a0040,0xfc4,0x9c1e2393500000148fe6,0x2d0600000000165f49b8,0x3348e800001c404a0008,0xb1800800001a2a8cc36,0x59100000000000d4a00,0x1c00f022574847a20000,0xe4841a9995e000e40,0x15]]
def g243D8 := limbs80 #[#[0xc79aa407f54bfa61fd20,0x98c2b469338d145aa224,0x11ac8c4]]
def g243H8 := limbs80 #[#[0xa4b11673001cc60e208b,0x8c00000000b1f2040,0x14d000008240052bc881,0x2c0036800000c06a674,0x8000001468ced00000f0,0x34c00b380011]]
def g243D9 (j : Nat) := if j=0 then 0x1654231bf else 0
def g243H9 := limbs80 #[#[0xb0000051008400,0x8200a8ec000000]]
def g243L : Nat → Packing
  | 5 => (9,4,4,0,0,6,0,g243D5)
  | 6 => (30,3,4,0,0,9,0,g243D6)
  | 7 => (15,2,4,0,0,10,0,g243D7)
  | 8 => (3,1,4,0,0,7,0,g243D8)
  | 9 => (1,0,4,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 3 29 3 10 4 2 g243H6
  | 7 => lookupWord 11 79 4 11 5 2 g243H7
  | 8 => lookupWord 6 43 3 10 4 2 g243H8
  | 9 => lookupWord 1 17 0 8 2 2 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : CutRow g243 5 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_2 : CutRow g243 5 2 7 := by
  apply polarBlock (data:=fun _ => (word80 [0x20801028060,0x114300210100c0421143,0x4010400454030310400,0x14004540213110001100,0x454081320048030344c4,0x82201000108045208132])) rfl
  decide +kernel
theorem g243B5 : CutRow g243 5 0 9 := (@joinRow g243 5 0 2 7 g243P5_0 g243P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : CutRow g243 6 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_3 : CutRow g243 6 3 5 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_8 : CutRow g243 6 8 22 := by
  apply polarBlock (data:=fun _ => (word80 [0x20204028120,0x303200200080c0222160,0x208000a042290520048,0x30380c4825100210100,0xc0421120002104024102,0x11200021040241021120,0x2001402052011611000,0x88502a06400210100,0xc0421120002104024102,0x112000210100c0421120,0x10010100c14090540021,0x100c042115000220080,0xc0222120040014024140,0x21410048030380c48241,0x280082402281400200,0x1100846011510408000a,0x442a0420048030380c4,0x82400208000a04229041])) rfl
  decide +kernel
theorem g243B6 : CutRow g243 6 0 30 := (@joinRow g243 6 0 3 27 g243P6_0 (@joinRow g243 6 3 5 22 g243P6_3 g243P6_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : CutRow g243 7 0 9 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_9 : CutRow g243 7 9 5 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_14 : CutRow g243 7 14 1 := by
  apply polarBlock (data:=fun _ => 0x48030380c48251) rfl
  decide +kernel
theorem g243B7 : CutRow g243 7 0 15 := (@joinRow g243 7 0 9 6 g243P7_0 (@joinRow g243 7 9 5 1 g243P7_9 g243P7_14))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : CutRow g243 8 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : CutRow g243 8 0 3 := g243P8_0
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
theorem g243G : graphValid g243 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := mixedLower (g:=g243) (i:=0) (hints:=16777284) (before_sound K222 V222) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K222 10 [(243,[]),(245,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V222 low243 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffe0ffe0ffff7222,0x914baa40000fc0fc003f])),(BitVec.ofNat 152 (word80 [0x940142004204403202,0x1432a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfe0000ffffffe0394a,0x8626748003f03f000fc0])),(BitVec.ofNat 152 (word80 [0x18058402800082380a,0x840250830c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad94,0xb0d84280fc000003f03f])),(BitVec.ofNat 152 (word80 [0x202600130411000990,0xb018408a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9bf00000003ffc0])),(BitVec.ofNat 152 (word80 [0xc04800240026048044,0x944a914514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc4000003ffc0000])),(BitVec.ofNat 152 (word80 [0x17008b808b8088171,0x18b08478e38e38e38e38]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x18010c010c0104401,0x42800460820820820820]))),(0x0,0x0)]
def g246C : List ColumnInfo := [(2,0,244,0,7),(4,0,242,0,7),(64,0,182,0,7),(128,0,118,0,7),(0,64,176,6,6),(16,0,230,0,6),(32,0,214,0,6),(2,64,176,4,5),(4,64,176,2,5),(18,0,228,0,5),(36,0,210,0,5),(66,0,180,0,5),(80,0,166,0,5),(96,0,150,0,5),(6,0,176,0,4),(6,64,176,0,4),(20,0,226,0,4),(34,0,212,0,4),(70,0,176,0,4),(82,0,164,0,4),(100,0,146,0,4),(130,0,116,0,4),(132,0,114,0,4),(144,0,102,0,4),(160,0,86,0,4),(192,0,54,0,4)]
def g246A : List (List Nat) := [[],[33,84]]
def g246D5 := limbs80 #[#[0x54530443f04c9214c110,0x4839a5895254110f5153,0x5cd5254120e696354950,0x54120d6b73549504835a,0xf1932551504c38e58d54,0x551504c3c6cc95454130,0x4cb935815354932e3b62,0x6015354932e4f6054d52,0x55132b4f8054d524cad3,0xe1f30d95544cb874c365,0xd95544ca8f6036555132,0x53f39332d272100a3f80,0x17b756f69635d57514b4,0x1c22084038]]
set_option maxRecDepth 16000 in
def g246D6 := limbs80 #[#[0x3b4a92a0904bd75d9110,0xe72a8a8261ce5515048,0xca5fbb2a9984ef725953,0x32c7acaaa065ae551600,0x4cb1eba2ca194bf76550,0x110c7ecaaa265d354d52,0x442fcbae40887f151c8,0xc110fe2a298221fc4853,0x50442fdbaa60887d9324,0x54530f9a6490a61de549,0xb20443f998e408875d53,0x24c110bf2e790221fa54,0x9530443eca9a60886f96,0x6254110bf2ea98221be5,0xdcd504437cb1aa0886f9,0xf644c910bf6e0992217e,0xfdd9324427ebb264886b,0xed6254910bf6e0a92213,0x3f5d9524435fb22a4886,0x4ff75589109fee6b1221,0x1fa549304827fb92ca88,0x7da534c120fb2a69824,0x41be59530483dcaa2609,0x905fb754c120bf2ea982,0x2417edcd504837cb1aa0,0x6906ed6354920edaa6a9,0x1a413fdc5634837db82c,0xc6906de5358d20dbaa6b,0xb1a413f5d5634835eaa2,0xaca904ff71595209feea,0xca8e41bd58551c827fb9,0x92c3906f531587209fae],#[0xa6a96413f5cd61c8376a,0xb8ac7906ed6354b20eda,0xca6b1e41b754d63c827f,0xebaac7906bd5458f20db,0xfaa6b2e413fdd563c827,0xfdb8aa0986fb6154130c,0xfb664a8261f64c9504c2,0x37db12a0987795254130,0xddec490a617edc9504c,0xc27eb96c2985df735453,0x309faebb0a61b754f614,0x4c3e6a9264987db704c9,0x930dbaca99261e755132,0x24c2eebaa64986df654c,0xc930f3aa99926177dd53,0x624c2eebae64986dd65c,0xd8930dbaa7b12613f5c7,0x9534c27ebaec4986bd54,0x294d30bbee4a9a61d754,0x49654c27fb8aca985dd7,0x7259530dd8e4b2a619f5,0x5c7654c27fb92ca986ef,0xd524cb309fae5b2a613f,0x759532cc3ceaa265987c,0xdf754cb30bbaea99661b,0xb754d62cc376a92c5985,0x4fd7558b30d7aa8b1661,0x1d754953cc27fbaac598,0x867d5259730d7aa4b266,0xa13f5cf615427eb96c2a,0xa867f6354950eda64a92,0x2a1bbccb625427eb8ec4],#[0x6a84fd71d8d509fae7b1,0xa2a13f5cf635427eb96c,0xa8a873f3255150e7a64a,0xaa2a1cf58d545439eb12,0xec0996f930d8132e7cc6,0x7b0265bb54b604ca7eb8,0xa6c0996de53d8132dbaa,0xebb02653f5d7604cb5ea,0xa9aa4995ef71549329fe,0xae329265dbd95524cbb6,0xfb2aa89967f6555132bd,0xfeeab2a653fdc1654cb9,0x3ea96ca994fd70d9532c,0xddaa4b0c65bd545618cb,0xa7ebaac3196bd5458632,0x2ddac6a9465db54d528c,0xca7ebaac7196bd5458e3,0x42cfaa6b2c653fdd5638,0x90b7aa9ac3215ef7254d,0xe429faeab1c85b754d63,0x54b3ea9acb214ff7558,0x85529fae7b02a53f5c76,0x6154b3ea9ec2a94fd70d,0xd8d529fae1b1aa53f5cf,0x56194b6f21ec6a94fd71,0x158e529fae6b0ca5bd4c,0xcc625527eb9ec4aa4ff7,0xb007000b7ae7b12a96f5,0x7b0d0164250370600940,0x1882e4550a7140264450,0x3d4790ef1d03746b0d3,0x34851072084047f0fb1f],#[0x9111f2384648b1132204,0x1372684c49712b250494,0xf298524a31432804f49d,0xc8584af15b2b0554a914,0x5e4bb1732e05b4b51672,0x4c718b310614c117f2f8,0x31a3340674cd19732864,0xbb3706d4d91af3586a4d,0x3a0734e51c7388704df1,0x794f11df3b8764eb1d3,0xf4fd1f73e87c4f71eb3d,0x920f418825032034007,0x2274488850f21b430855,0xf4788e51b2334608b515,0xa89452724b4909152123,0x9a5332634c09752d2574,0x53f27b4f09d53926f4d8,0xb293520a3545287508a0,0xab550a955129f538a654,0x580af55d2b7568ac5572,0xb55692cf598b25632c3,0x403090c101b856f2db5b,0xa128c1150f08543e2436,0x4a490e298a24324c0a34,0x3628a890d29268a8c4a2,0x8403003c1020418148c,0x10309040030f26089b,0x441211008]]
def g246H6 := limbs80 #[#[0x7e0aa049c17004420e08,0x51e91758788d4006137,0x4880010e000000,0x30c341ba2006e036f840,0x808385b942621b35d900,0x14]]
set_option maxRecDepth 16000 in
def g246D7 := limbs80 #[#[0xf55150af59330afd9110,0x59432af59032be58032c,0xc110fec8110bd586429f,0x510bf58910fe54110fe4,0x20fe54120fe4c120bf59,0xef55120bf58d20fb549,0xfb54b20bf58720bf5952,0xf59720ef55320bf58f20,0x4c930bfd8530fe54130b,0x4d30bfd8930f7cc930f7,0x130ef55130f794d30f75,0x30bfd9530bf59530ef95,0xf754f30bf58b30f74cb,0xbfd8550bf59730ef5533,0xfd8d50bfd8950df54950,0xd8132bf59432ef55032b,0x5132fb94932fb54932bf,0x532bf59532ef95132ef5,0x32fb54a32bf58632bfd9,0x2bf59632ef55232bf58e,0xbfd8152bf59642bf58e4,0xfd8d52df54d52bfd8552,0xd8954bf58e52bf58652b,0xc910efd8954ef18954bf,0x520ff4c520ff54910ff4,0x30ff48530ff54720ff54,0x2ff55132ff54d40ff545,0xff54d20ffcc520ff54d4,0xf54f20ffcc720ff94d20,0x4c930ff58530ff94f20f,0x4d30ff58930ff54930ff,0x550ff54b30ff59530ff5],#[0x50ffcc950ff4c950ff58,0x2ff98d50ff58d50ff589,0xff54932ffd8132ff5813,0xf59532ffd9132ff59132,0x54e42ff54e32ffd9532f,0x8d52ff58552ff58152ff,0xff59152ff98d52ff5,0x30d30b809607b059030,0x61e41c91991691471171,0x2fc2d32aa26c24a22820,0xd3eb3c93a037034031e,0xf51f4da4b849646d42f4,0x6226005d05ae58c56a54,0x4872670b6e26a467b64b,0xe85382a7f37bc7a17637,0x9799499208f78c789086,0x91a68a46a1d9ed9c49a9,0xeb2cb11af6ae2ac7ab3a,0xbb8bb2bacb98b7db69b4,0xe2bdcbd6bd0bcabc4bbe,0xcc06c00bfabf4beebe8b,0xc30c2ac24c1ec18c12c0,0x5ac54c4ec48c42c3cc36,0x8e08495006c6cc66c60c,0x32b24789271c01a20593,0x430310186071048a1818,0x2c1e14d858c4050e3091,0x552a31e212230928a1e3,0x60a4878c40303242478c,0xa8746244c24498658a8,0x8f10883024c42e911891,0xb950c11182022488d251],#[0xa911c00a28c0c0c80f14,0xc68d1518f10181803042,0x8b0910e8c60c10101805,0x10c8498848283223c52a,0x6401c64c888286892221,0x148c88a608e20c910c04,0x313464848d1518f11262,0x23182254202021602326,0x8a106891418508080a32,0x8c3ca112401460406344,0x51e5440a1200d146068a,0x80892a3172a901891430,0x952480a101012a286080,0x4123051714ca28300223,0x62430a18ba3101812618,0x8688c848302345464184,0x3982e111820200746509,0x42461014305080808046,0x470630509103092e1831,0x80892e3198c11141472,0x80e5c51a0c4050e28406,0x8b8c18201c480b8c1810,0xc25c50a60b8619080080,0x48a18262130c80c10100,0xe9450c2039910202030c,0xc21c126101cc88984430,0x63c4960c5090a1171c1,0x5888f0d0c0224041e14b,0x83024410c862c204]]
def g246H7 := limbs80 #[#[0x800400063821022000c0,0xc04109f0843830490000,0x3810010010442a91410c,0xc320d00a082042185222,0x125f4f80002c824f0d99,0x14ae0001acf02dd4350a,0xf3130000000a9c000000,0x193a20004944001e83ca,0x386ccc00151b83d0002a,0x5632927070002472884e,0x846f8548be0000002983,0xd8d6126044bc43571282,0xeb0bf103897e99d24186,0x1cad66,0x1a5000035ac4d00,0x38f2b0f0b470880000,0xe7400000026a979aeaf8,0x3173c24000000289b,0xac213,0xc9d2630000ca400,0x381600000,0x184900000000,0x1180,0x3370000000,0x293e0000000000174469,0x93fc940000000000000,0x105d00021c651800,0x6200000,0x29e07800000000000000,0xeb082180020de000852f,0x3ac80000000000000001,0x74800000000000000551],#[0x68246329735191ce9ca,0x4282b3c80000f4600000,0x7aaab56dd93654c6c6d,0x1266f2c949612bead1,0xdb500030b00008104620,0xc001ea3000000206df53,0x10000003130160a8d0ab,0xf395430000054c3,0xb5f27d9916f4000a1980,0xe74c9475b0501002f0fc,0xe8f41f00024b8c78109c,0x216800002f11b7d0e,0xf4300000000001e2c406,0xb5d8011c7,0x1a03000000014c00000,0x3c99c00151c00000000,0x32a0000001a3945c000f,0x511e5d186e87600001d7,0x7d6f852000707ab1f801,0xd14d9240000000510c1f,0xf684eb1420310360b675,0xaa230000001567d0cf8,0x8bc000aa430800020ab4,0xa5ae35000340a06c21a4,0x4c182c3854f1a9094000,0xc441b8c10b516b1d23f,0x2d6a0c31096000000000,0xcc00060e8003338000c3,0x185a000455b15d2,0x8c200030408e0001c8a0,0x20d091548f29d0000000,0xc53cc728544a44000c73],#[0xcb1d087308303bb44347,0xdf502e12308fa1445029,0x240c88000805c6800031,0xa9363db8a5c3ed]]
def g246D8 := limbs80 #[#[0xf20fe907f4437ca9bd54,0x65fd50fea07fcc3fa61f,0xbfc85fd42ff197f4cbf8,0x780c001fd54ff297f54,0x318ae24c841bc5410833,0x419e1cd523438f6390d5,0x90451319e304a261a428,0x40d1c201828d1c2988,0x44c601468d0a24c710e5,0xa8114248e1906c642620,0x46a2620408019251838c,0xe39b19060e2c65126082,0x308bc21a630268518a40,0x1a60419038c34260648a]]
def g246H8 := limbs80 #[#[0x25010033021002360027,0xd10003001994222d0b00,0x5e89c8f110000002a,0xf46000000545,0xdaf0000,0x0,0xd3d63000000000000000,0x786b000a08e0524c3e21,0x56e000dc30000ae08,0x90d23355000000000000,0x93300000030c0006cac,0x83000141f39000b2b00,0xa18000,0x0,0x3600000000000000,0x434000ba000011e000,0x542e758da450e9e9c880,0x967c4a84472,0x26000a01000000000000,0xe4200073e2,0xa3800000000051fd4,0x43127000816000000000,0x20463b6b700071b73af,0x0,0xbc7000250000000000,0x549d00065bd8fccecc50,0xf1000042ab5f0000007a,0x304e39dce549d2c9a73d,0x5c0016c000000a4754fe,0xa25cd000000c5e0c256,0x231000000000000,0xbf17000000000de10000],#[0xb8a0000000002d0000a4,0x0,0x5d80000000,0x0,0x1300043222d000000000,0xf00000055d000000b492,0x50770a00060300000073,0x28409d4e000000000,0xb120000000,0xd5c0007cb85700,0x262000000,0x206d0d0,0xf53000000c9c03546600,0x95d8200061a00000026d,0x50f000f21a,0xe1914d000000000c1500,0x8d5000000252,0x422000748acf0,0x0,0xd60000000000,0x5610000000,0x59b6a000f1d00000000,0x3769ef56000000000114,0x72c21cec19295dd000a,0x55a000000c8900000,0xb000068824000b2f000,0x664000000f990000008,0x10200023c000d2000000,0xa9f000a51000,0x3690000]]
def g246D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g246H9 := limbs80 #[#[0x580067a5a12800018621,0x80dc400000000005d9c,0x1d09611ce86000d78018,0x68a002a1923c6e,0x5fcc0000144800000000,0x751c00000000017458f3,0x26f95b]]
def g246L : Nat → Packing
  | 5 => (18,4,5,0,0,8,0,g246D5)
  | 6 => (188,3,5,0,0,11,0,g246D6)
  | 7 => (111,2,5,0,0,12,0,g246D7)
  | 8 => (17,1,5,0,0,10,0,g246D8)
  | 9 => (1,0,5,0,0,0,0,g246D9)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 7 37 5 10 5 1 g246H6
  | 7 => lookupWord 60 389 6 13 8 1 g246H7
  | 8 => lookupWord 39 397 4 12 7 1 g246H8
  | 9 => lookupWord 7 47 5 10 5 1 g246H9
  | _ => fun _ => none
def g246 : Forest := ⟨246,9,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_0 : CutRow g246 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_1 : CutRow g246 5 1 17 := by
  apply polarBlock (data:=fun _ => (word80 [0xc222028088,0x263100840111884c4441,0x4400a1502c42300084,0x111884c4431004400a1,0x502c422000840111884c,0x442100840111884c4421,0x840111884c44210084,0x111884c444000840111,0x884c444000840111884c,0x444000840111884c4440,0x820281c0a824100084,0x111884c442000840111,0x884c442000c22281c0a8,0x26100280640281201630])) rfl
  decide +kernel
theorem g246B5 : CutRow g246 5 0 18 := (@joinRow g246 5 0 1 17 g246P5_0 g246P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : CutRow g246 6 0 12 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_12 : CutRow g246 6 12 9 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_21 : CutRow g246 6 21 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x840111,0x884c443100840111884c,0x4431004400a1502c4240,0x4400a1502c42300044,0xa1502c4230004400a1,0x502c4240004400a1502c,0x423000840111884c4441,0xc14402410416200084,0x111884c444100840111,0x884c444100410301c0c4,0x122000840111884c4431,0x840111884c443100c1,0x4301c0c4162000840111,0x884c443000840111884c,0x443100840111884c4431,0x820281c0a824200084,0x111884c443000840111,0x884c443000840111884c,0x443000840111884c4430,0x840111884c44600084,0x111884c442000840111,0x884c442000840111884c,0x442002850111884c5441,0x410402410412200446,0xa1502c624000410402,0x41041220004000a1502c,0x426000c22281c0a82621,0x2080012082490410044,0xa1502c424000410301,0xc0c41220004000a1502c,0x426002020020982c3021,0x1000230189c082540280,0x630188e0165102850111,0x884c5430040800321048,0xa0420088011280488440,0x2806402812016510285,0x1118848543010002301,0x89c08254100100a05928,0x90531000228151a08243])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_69 : CutRow g246 6 69 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400a1,0x502c4230004400a1502c,0x4230004400a1502c4230,0x4400a1502c42600044,0xa1502c422000840111,0x884c444102080032182c,0x905200840111884c4441,0x840111884c44310084,0x111884c443100840111,0x884c444100c14301c0c4,0x162000840111884c4431,0x840111884c44310084,0x111884c443100840111,0x884c444100c22281c0a8,0x263100840111884c4431,0x2080032182c90520084,0x111884c443100840111,0x884c443100840111884c,0x446100840111884c4431,0x840111884c44310084,0x111884c443100840111,0x884c443100840111884c,0x446100840111884c4421,0x840111884c442000c1,0x4301c0c4162000c14301,0xc0c416200088028340a8,0x84510088010280488441,0x4460021102c62300084,0x111884c443000840111,0x884c443000840111884c,0x443000840111884c4420,0x840111884c44200280,0x64020920165102806301,0x88e0165100840111884c,0x444100840111884c4441,0x840111884c44410084,0x111884c446100840111,0x884c443100840111884c,0x443100c14301c0c41620])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_117 : CutRow g246 6 117 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400a1,0x502c4260004400a1502c,0x4230004400a1502c4230,0x4400a1502c424000c1,0x4301c0c41620004400a1,0x502c4230004400a1502c,0x4230004400a1502c4240,0x840111884c44410044,0xa1502c424000c22281,0xc0a82631004400a1502c,0x42500a04030380e0d062,0x4400a1502c42300044,0xa1502c4230004400a1,0x502c4230004400a1502c,0x423000c2240281082631,0xc22281c0a8263100c2,0x2281c0a8263100840111,0x884c443100840111884c,0x443100c22281c0a82621,0x4400a1502c42400084,0x111884c443000c22402,0x8108263100840111884c,0x445100820281c0a82431,0x840111884c44510084,0x111884c445100840111,0x884c444100820281c0a8,0x243102020030982c3032,0x840111884c44410040,0x4024104125002020030,0x982c303200820281c0a8,0x243100840111884c4431,0xc14301c0c416200082,0x281c0a8243100c22402,0x8108263100c22280c0a8,0x2631004400a1502c4230,0xc224028108263100c2,0x2281c0a8263100c22281,0xc0a82631004400a1502c,0x423000c22281c0a82621])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_165 : CutRow g246 6 165 23 := by
  apply polarBlock (data:=fun _ => (word80 [0x410301,0xc0c4122000410301c0c4,0x122000410301c0c41220,0xc14402410416200044,0xa1502c4240004400a1,0x502c4230004400a1502c,0x4230004400a1502c4240,0x840111884c444100c1,0x4301c0c4162000c14402,0x4104162000840111884c,0x444100840111884c4441,0x4400a1502c42400084,0x111884c444100840111,0x884c444100840111884c,0x444100840111884c4431,0x440081502442300c04,0x60341c07062004400a1,0x502c4240004400a1502c,0x4240004400a1502c4240])) rfl
  decide +kernel
theorem g246B6 : CutRow g246 6 0 188 := (@joinRow g246 6 0 69 119 (@joinRow g246 6 0 12 57 g246P6_0 (@joinRow g246 6 12 9 48 g246P6_12 g246P6_21)) (@joinRow g246 6 69 48 71 g246P6_69 (@joinRow g246 6 117 48 23 g246P6_117 g246P6_165)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : CutRow g246 7 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_7 : CutRow g246 7 7 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_55 : CutRow g246 7 55 13 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_68 : CutRow g246 7 68 10 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_78 : CutRow g246 7 78 33 := by
  apply polarBlock (data:=fun _ => (word80 [0x820281,0xc0a82431004400a1502c,0x4240004400a1502c4240,0x4400a1502c42400082,0x281c0a8243100840111,0x884c4441004400a1502c,0x4240004400a1502c4240,0x4400a1502c42400048,0x28340a4825000480082,0x40248250004400a1502c,0x424000840111884c4441,0x840111884c44410084,0x111884c444100840111,0x884c444100820281c0a8,0x243100840111884c4441,0x840111884c44410202,0x30982c3032004400a1,0x502c424000840111884c,0x444100840111884c4441,0x840111884c44410084,0x111884c444100840111,0x884c4441020800120824,0x905200840111884c4441,0x840111884c44410048,0x30380c4825000840111,0x884c444100840111884c,0x44410088028340a88451])) rfl
  decide +kernel
theorem g246B7 : CutRow g246 7 0 111 := (@joinRow g246 7 0 55 56 (@joinRow g246 7 0 7 48 g246P7_0 g246P7_7) (@joinRow g246 7 55 13 43 g246P7_55 (@joinRow g246 7 68 10 33 g246P7_68 g246P7_78)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_0 : CutRow g246 8 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_2 : CutRow g246 8 2 15 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B8 : CutRow g246 8 0 17 := (@joinRow g246 8 0 2 15 g246P8_0 g246P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P9_0 : CutRow g246 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B9 : CutRow g246 9 0 1 := g246P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246T : mixedTables g246 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g246 0 0
  · exact mixedEmpty g246 1 0
  · exact mixedEmpty g246 2 0
  · exact mixedEmpty g246 3 0
  · exact mixedEmpty g246 4 0
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
theorem low246 : Lower true (varsX 246) (graphGoal 246) 10 := mixedLower (g:=g246) (i:=0) (hints:=287376704) (before_sound K243 V243) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K243 10 [(246,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V243 low246 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc1ffffffffff7302e,0x4b8e80003f8001fffff])),(BitVec.ofNat 152 (word80 [0x84082002080023004,0x904808102040810204]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fff07ffc1f04f21,0xcd27ca000007f000007f])),(BitVec.ofNat 152 (word80 [0x508814120904004821,0xcd2682468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0xffe00007fffe0b48e8,0x93c11601fc000fe03f80])),(BitVec.ofNat 152 (word80 [0x6001182042002108a8,0x81411412244891224489]))),((BitVec.ofNat 152 (word80 [0xfffffff800000894d0,0x691ab3fe00000fffc000])),(BitVec.ofNat 152 (word80 [0x800220008c08488440,0x600aa224489122448912]))),((BitVec.ofNat 152 (word80 [0x91717,0xa28774000007f0000000])),(BitVec.ofNat 152 (word80 [0x113c044f010891716,0x228174b972e5cb972e5c]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0x21c00870021044113,0x1e0001c183060c183060]))),(0x0,0x0)]
def g249C : List ColumnInfo := [(0,64,177,8,8),(64,0,185,0,8),(8,64,177,0,7),(16,0,233,0,7),(32,0,217,0,7),(128,0,121,0,7),(1,0,248,0,6),(48,0,201,0,4),(144,0,105,0,4),(160,0,89,0,4)]
def g249A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116]]
def g249D4 (j : Nat) := if j=0 then 0x194b835d5528c120 else 0
def g249D5 := limbs80 #[#[0x54a30483d254d524c120,0x483b2595324c120d6975,0x615324c120ecb654c930,0x8c120bcb854c930482f2,0xe4d6554d32482f2e0d52,0x6123060393d815354932,0xc2a91e]]
def g249H5 (j : Nat) := if j=0 then 0x10 else 0
def g249D6 := limbs80 #[#[0xa3fbaac6907c9324c120,0xf9a6498241d354d524c,0x83f4a9260905ef724c12,0x20bf2eb18241fa54a304,0x4cb6eb1aa7107cd534c9,0x120bdae5302657bdc960,0x4837cb2a60907eb724c,0xc120df2cb18241bed953,0x32483e7b1a64906fb658,0x4c920ddeca99241bb595,0x953482f7baa64905ed75,0x358d209fceca9a413f5d,0xd563482bfbaac6906df6,0x7558d20cfeeab1a419f1,0xdc9538827ebaec6904ff,0xf7558e209faeca9c417b,0xf5da604cabfbaac0994f,0xfd75d8132ddaa5b02653,0x3f5c3654ca7fb82ca994,0x409a4a239025f1b08801,0xc9d8e670369a8c75d2b5,0x448a39168842a08fe7c3,0xeac54a9946a04ea692e9,0xf008314e48c4b85aac95,0xf8f00c205e3c1243178,0x60830428224100000002]]
def g249H6 := limbs80 #[#[0x160400000a,0x12169754600000000000,0x3c050000000000000000,0xd0c00000000001ce31,0x1040,0x2c1000,0x4c3a200,0x42000000001c38000006,0x1c8000883e0c]]
def g249D7 := limbs80 #[#[0xb4c920fe8c120fe4c120,0x58e20bfd8d20bf58d20f,0x9532fb54932bfd8132bf,0xd20ff4c120bfd9532bf5,0x20ffd8d20ff58d20ff54,0x2ff98132ff58132ff54e,0xe8961b04207800ff5953,0x81c86a986589263d8d82,0x146c948c497a40889f87,0x860f1187c941878f2506,0x21315358f21711d48c5c,0xc705641c5c721c41541b,0x49207c465648f22481c3,0x9131c06523146c55c871,0x2461835031d55031940c,0x501c41958c71140e1806,0x234]]
def g249H7 := limbs80 #[#[0x4046c2de4d7191277080,0x1049a1203d28f91a0220,0x5c1b60b000480801908e,0xdd272828000000000104,0x5042a423e13492380724,0x14646913e8c7f061042a,0x91720a6d2511006b9116,0x453045307e41c81c707b,0x4885c4b49530c7817d0d,0xe62430c9c7bc09449d09,0x97a8de0e000c46314282,0x1601908780280fe0662,0x3a6000188530eda2c0,0x610352e09800142c0000,0x11a040914b0d8003]]
def g249D8 := limbs80 #[#[0x86909007f4cbfc41fd20,0x1c870d683348689ab41c,0x1131ea4]]
def g249H8 := limbs80 #[#[0x82270,0xe0000007110000000,0xd2400000000000080792,0xd25409c00e2d,0xf808000d42000d238050,0xc02000a2250b000e2ca0,0x121,0x1000b8b0000,0x10d000b03000c0c00,0xa06004,0xa1470000000000000000,0x38138e00064100ad2,0xe10000000]]
def g249D9 (j : Nat) := if j=0 then 0x1543217f else 0
def g249H9 := limbs80 #[#[0xc20772423c1000016000,0x1c0b40034d]]
def g249L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g249D4)
  | 5 => (9,4,4,0,0,6,0,g249D5)
  | 6 => (39,3,4,0,0,9,0,g249D6)
  | 7 => (18,2,4,0,0,10,0,g249D7)
  | 8 => (3,1,4,0,0,7,0,g249D8)
  | 9 => (1,0,4,0,0,0,0,g249D9)
  | _ => emptyPacking
def g249I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g249H5
  | 6 => lookupWord 4 67 1 11 4 3 g249H6
  | 7 => lookupWord 18 83 6 13 6 3 g249H7
  | 8 => lookupWord 8 83 3 12 5 3 g249H8
  | 9 => lookupWord 2 17 0 9 2 3 g249H9
  | _ => fun _ => none
def g249 : Forest := ⟨249,9,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P4_0 : CutRow g249 4 0 1 := by
  apply polarBlock (data:=fun _ => 0x104000b84124810) rfl
  decide +kernel
theorem g249B4 : CutRow g249 4 0 1 := g249P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P5_0 : CutRow g249 5 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P5_2 : CutRow g249 5 2 7 := by
  apply polarBlock (data:=fun _ => (word80 [0x20860320e2,0x91000210400c1021130,0x100000808520a0520202,0x4028120114310010100,0x45409032002104024102,0x11431000108045208132])) rfl
  decide +kernel
theorem g249B5 : CutRow g249 5 0 9 := (@joinRow g249 5 0 2 7 g249P5_0 g249P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_0 : CutRow g249 6 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_3 : CutRow g249 6 3 9 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_12 : CutRow g249 6 12 27 := by
  apply polarBlock (data:=fun _ => (word80 [0x210100c042,0x11200202000884223032,0x208603218209100020,0x86032182091000210100,0xc0421120002000824022,0x81600022040281022130,0x220402810221300400,0x4024140306200210100,0xc0421120002104024102,0x112000210100c0421120,0x210100c04211200400,0xa0442a06300220080,0xc022216000210100c042,0x112000210100c0421120,0x4010402414030520408,0x824060a04200210402,0x41021150002800824022,0x8140100200084502a053,0x2001402052011510208,0xa0422904102001402,0x52011510208000a0422,0x90411001010085409043])) rfl
  decide +kernel
theorem g249B6 : CutRow g249 6 0 39 := (@joinRow g249 6 0 3 36 g249P6_0 (@joinRow g249 6 3 9 27 g249P6_3 g249P6_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_0 : CutRow g249 7 0 10 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_10 : CutRow g249 7 10 7 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_17 : CutRow g249 7 17 1 := by
  apply polarBlock (data:=fun _ => 0x20860321820910) rfl
  decide +kernel
theorem g249B7 : CutRow g249 7 0 18 := (@joinRow g249 7 0 10 8 g249P7_0 (@joinRow g249 7 10 7 1 g249P7_10 g249P7_17))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P8_0 : CutRow g249 8 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B8 : CutRow g249 8 0 3 := g249P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P9_0 : CutRow g249 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B9 : CutRow g249 9 0 1 := g249P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249T : mixedTables g249 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g249 0 0
  · exact mixedEmpty g249 1 0
  · exact mixedEmpty g249 2 0
  · exact mixedEmpty g249 3 0
  · exact g249B4
  · exact g249B5
  · exact g249B6
  · exact g249B7
  · exact g249B8
  · exact g249B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 10 := mixedLower (g:=g249) (i:=0) (hints:=50331651) (before_sound K246 V246) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K246 10 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V246 low249 (by decide +kernel)
def g250Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8001fffc03fffff63,0x44e29b013c003f03f03f])),(BitVec.ofNat 152 (word80 [0x501940428680a21422,0x44409101382082082082]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffe000003fff003c,0x78de8447880000fc0000])),(BitVec.ofNat 152 (word80 [0x6211886b0b10c4263c,0x48d684078934d34d34d3]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffbc,0x8889e994640fc0000fff])),(BitVec.ofNat 152 (word80 [0x8042010c0002080014,0x894814445145145145]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000081,0x4f4585ecd3f000000fc0])),(BitVec.ofNat 152 (word80 [0x9c02700c04f03881,0x4e4485c810a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x91,0x75383e5b400000fff000])),(BitVec.ofNat 152 (word80 [0x4e013801027004081,0x31282a5842cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x7001c002038008048,0x91322020830c30c30c30]))),(0x0,0x0)]
def g250C : List ColumnInfo := [(8,0,242,0,7)]
def g250A : List (List Nat) := [[],[116]]
def g250D7 (j : Nat) := if j=0 then 0x7f else 0
def g250L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g250D7)
  | _ => emptyPacking
def g250I (_ _ : Nat) : Option (Nat × Nat) := none
def g250 : Forest := ⟨250,7,fun i => g250Y[i]?.getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_0 : CutRow g250 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B7 : CutRow g250 7 0 1 := g250P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250T : mixedTables g250 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g250 0 0
  · exact mixedEmpty g250 1 0
  · exact mixedEmpty g250 2 0
  · exact mixedEmpty g250 3 0
  · exact mixedEmpty g250 4 0
  · exact mixedEmpty g250 5 0
  · exact mixedEmpty g250 6 0
  · exact g250B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low250 : Lower true (varsX 250) (graphGoal 250) 8 := mixedLower (g:=g250) (i:=0) (hints:=289497152) (before_sound K249 V249) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K249 8 [(250,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V250 : Known true K250 := extend_ok (m:=250) V249 low250 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7472aee051d0c438,0x7420800000000fe03fff])),(BitVec.ofNat 152 (word80 [0x2824322e405040c010,0x30209122448912244891]))),((BitVec.ofNat 152 (word80 [0x12753742b03278696,0x98a8001fc00001fc000])),(BitVec.ofNat 152 (word80 [0xcc2353742901278496,0x1808b162c58b162c58b]))),((BitVec.ofNat 152 (word80 [0xea196fdd5a071560,0x21900fe0007f0000000])),(BitVec.ofNat 152 (word80 [0x706a182fcd4a070460,0x218070e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xfe4b8cf8af25604d19,0x4dc7f0000000000007f])),(BitVec.ofNat 152 (word80 [0x804b8cd0af21200508,0x4dc0e1c3870e1c3870e]))),((BitVec.ofNat 152 (word80 [0x10b6918ec2092866,0xe8db000003f8001fff80])),(BitVec.ofNat 152 (word80 [0x1004818682002860,0x485b2448912244891224]))),((BitVec.ofNat 152 (word80 [0x22c951708cbc330a,0x9174800003ffffe00000])),(BitVec.ofNat 152 (word80 [0xc1503004b8130a,0x81044891224489122448]))),((BitVec.ofNat 152 (word80 [0x19d24061534aaeac1,0x3277ffffc0000000000])),(BitVec.ofNat 152 (word80 [0x19420001014886a01,0x2370e1c3870e1c3870]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(2,0,125,0,9),(4,0,123,0,9),(8,0,119,0,9),(1,0,126,0,8),(16,0,111,0,8),(32,0,95,0,8),(64,0,63,0,8),(0,64,49,14,7),(8,64,49,6,6),(17,0,110,0,5),(33,0,94,0,5),(48,0,79,0,5),(65,8,54,0,4),(80,2,45,0,4),(96,4,27,0,4)]
def g127A : List (List Nat) := [[],[33,84],[64,33,49,80],[64,49],[80,50],[80,49,33,64]]
def g127D7 := limbs80 #[#[0xbef8259540f395454140,0xbf7815d940d7f7559540,0x35794d98009fd85dd160,0x1821a884005e5c782486,0x3]]
def g127D8 := limbs80 #[#[0xd75503fca828177dcd60,0x2a817fdd160bfeeaa05f,0xffaeca07fd75503feb,0x20696421d4c64b18054,0x2890f2c70564235d23c7,0xb0c491cb2891c6cb1c08,0x11ce1051f1c0c147195c,0x1e34905872ca2635458d,0x34c]]
def g127H8 := limbs80 #[#[0x7c400c4000000000,0x284000000142,0x7b00000000010000,0x618]]
def g127D9 := limbs80 #[#[0xe328249cc0ff583fd40,0x6ad071848e41ed52]]
def g127H9 := limbs80 #[#[0x2c3661ab8c0140000005,0x1220000000000c2100,0x614016700000000062]]
def g127D10 (j : Nat) := if j=0 then 0xca864203ff else 0
def g127H10 := limbs80 #[#[0xe1f9900000320000,0x3584000000]]
def g127L : Nat → Packing
  | 7 => (5,3,4,0,0,7,0,g127D7)
  | 8 => (8,2,4,0,0,9,0,g127D8)
  | 9 => (2,1,4,0,0,6,0,g127D9)
  | 10 => (1,0,4,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 29 0 9 3 2 g127H8
  | 9 => lookupWord 2 29 3 9 3 2 g127H9
  | 10 => lookupWord 1 17 0 8 1 3 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : CutRow g127 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1 : CutRow g127 7 1 4 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : CutRow g127 7 0 5 := (@joinRow g127 7 0 1 4 g127P7_0 g127P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : CutRow g127 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_1 : CutRow g127 8 1 4 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_5 : CutRow g127 8 5 3 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : CutRow g127 8 0 8 := (@joinRow g127 8 0 1 7 g127P8_0 (@joinRow g127 8 1 4 3 g127P8_1 g127P8_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : CutRow g127 9 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : CutRow g127 9 0 2 := g127P9_0
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
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := mixedLower (g:=g127) (i:=0) (hints:=16778563) (before_sound K250 V250) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K250 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V250 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffd817c545c20ed,0x432241000007c00f83ff])),(BitVec.ofNat 152 (word80 [0x4800a0805c1048206c,0x1020104210842108421]))),((BitVec.ofNat 152 (word80 [0xfc00009946938753bc,0x3e48150000f800007c00])),(BitVec.ofNat 152 (word80 [0x9083308946138703ac,0x3e48112d6b5ad6b5ad6b]))),((BitVec.ofNat 152 (word80 [0x3ac47b0792510,0xaaaa3a001f0001f00000])),(BitVec.ofNat 152 (word80 [0xe015c38c45b0792510,0x2aa2181ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0xfffff92e274bd758f0,0x4291788000000000001f])),(BitVec.ofNat 152 (word80 [0x126012e234b975890,0x429178fbdef7bdef7bde]))),((BitVec.ofNat 152 (word80 [0x42f1aeb16816,0xc650c03e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x380000a1a4304810,0x250c10842108421084]))),((BitVec.ofNat 152 (word80 [0x8b0240ae8e0b,0x21dcaafc00003fff8000])),(BitVec.ofNat 152 (word80 [0x1c000030240860203,0x48a2a1084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x6748939029300,0xd01391ffffffc0000000])),(BitVec.ofNat 152 (word80 [0x20004700008009000,0xc0100042108421084210]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(2,0,189,0,9),(4,0,187,0,9),(8,0,183,0,9),(0,8,182,1,8),(10,0,181,0,8),(16,0,175,0,8),(32,0,159,0,8),(128,0,63,0,8),(1,0,182,0,7),(1,8,182,0,7),(18,0,173,0,7),(0,2,45,144,6),(16,8,166,1,6),(20,0,171,0,6),(24,0,167,0,6),(32,8,150,1,6),(34,0,157,0,6),(40,0,151,0,6),(130,0,61,0,6),(136,0,55,0,6),(3,0,180,0,5),(3,8,180,0,5),(16,2,45,128,5),(17,0,166,0,5),(17,8,166,0,5),(32,4,27,128,5),(33,0,150,0,5),(33,8,150,0,5),(48,0,143,0,5),(128,2,45,16,5),(128,8,54,1,5),(19,8,164,0,4),(50,0,141,0,4),(52,0,139,0,4),(129,8,54,0,4),(144,0,45,0,4),(144,2,45,0,4),(160,0,27,0,4),(160,4,27,0,4)]
def g191A : List (List Nat) := [[],[33,84]]
def g191D5 := limbs80 #[#[0x70547e05655914254630,0x514258110f095956450b,0x86995450960443e21655,0x443c63925d56558110ba,0x4254630d8c6416559154,0x9954509518c3d0576551,0x2f07a65514254630bc16,0x54630f4169d54509518c,0x74551518c3c857659142,0x17965d15454630d45659,0x630b4569974551518c35,0x551518c3c15645d95454,0x745956454630d1565976,0xd1565d65591518c3c15,0x5518c3c47925d9655463,0x5d96554630d15e517659,0x761d65591548c2c57a4,0x48c341d975956455230e,0xf815923087569597e056,0x69564545605021d7a565,0x46e25a55914254560b8c,0x350951b496995450b705,0x99355142547706a95516,0xf07a664d5450951dc165,0x5151dc168d9655142546,0x660d5454761564e59835,0x7a464d6559151c9561b9,0xcc56139460d65546e1,0x3c36302a241e18120c06,0x78726c66605a544e4842,0xb4aea8a29c96908a847e,0xd2ccc6c0ba]]
set_option maxRecDepth 16000 in
def g191D6 := limbs80 #[#[0xa12c08874c5d55450110,0x21c717559560443d42c8,0x514254630e92baaa8a12,0x18c3a2ae8aa2a3187c15,0xacbf02b2461c55765955,0xa84a8f4955142dc1518e,0xf059355142547e0aa8b1,0x5450951b92cb2a8a12a3,0x43c4acab2284a8dc9e59,0xa284b0221eb165591404,0x887b85954258110fd0a,0x56559142443d62c8aa2c,0x54630f1ab2ac8aa221ea,0xb8aeca12a3187e159142,0xc8a8c61d5576551518c3,0x87555957454630f2ab2a,0x559150503c3acab22a91,0x140f58b22a2b0281e396,0xacab22a2a078e5955458,0xb82a3ea56450951583c6,0x5959542dc151ed2b2285,0xd545478eacab26e0a8f,0x1f33c92cab22a3757966,0x9c12caa8f9564d655915,0xaa97579460d65546ecb2,0x5978159154f0eb2ac8b9,0x40443c3acac1ac8aa78d,0xd8c32a8a0221f3165551,0xa280885ec6595450110d,0x17e39259540442f672ca,0x55458110d78c32caa022,0x442de32caa2c08879c59],#[0xc92cab0221af165e1160,0x84885bce516558110f71,0xa59655142443e4acaaa2,0x550910bd3cb2a8a12217,0x23eb2bc3ac8884f9e616,0x2eab2a213e594e096544,0x187c55915454630eb3c1,0x96551518c2eab2caa2a3,0x4630eaacbaa8a8c61757,0xaaecb22a3187655d1645,0x8a8c615d597591518c39,0x7d1e4965546309ebcc2c,0x595518c2eaf28b2aa318,0x30aebca2eca8c61d5597,0xeab22a9185f1e4986546,0xa461c9d76591548c3a3a,0x765d6455230ccec3ac8a,0x1548c333b0cba2a91856,0xc6ec32ecaa46199f865d,0xc3aa9184776617655230,0x619d575e05648c23bf2c,0x5f81592309eacaf02b24,0x48c3b2f02ba2c9186756,0xfc2ae8b2461c9d655d16,0x2c91863761d6559230cc,0x8df855d9648c39af02bb,0x8759230a6fcaaecb2461,0xc23bf2ac3ac918675e45,0xb2a8a82811dd95e11768,0xa05ce6595454140e9cb,0x98659150502e772caa2a,0x58140f98aa2a2b0281ab],#[0xd732caa2c0a079c59551,0xc8b0281eb39159160502,0x6aee156458140e5cbaa,0x655151502d772ab22c0a,0x540b9acb2a8a8a81d357,0xaecb2aa2a05cde595454,0xb2281c3d76595545038e,0x7d657815d940e1ebaaca,0x5151583e4aa8a12a2b04,0xb3acb2a8a8ac1e35645,0x8b2aa2b0799e49655456,0x2a367794595515838eee,0x65954dc151e9ab22a9b8,0x70547acf24b2ee0a8d5d,0x92c82a8a12a357794597,0x2a86a8fc96595450951f,0x3b569859543547e8f24b,0x18355151dab4c2a8b1aa,0x5476ab0cc1aa8a8fc559,0xc930caa2a37679261954,0xc8a8ed564d8655151db3,0x6590e09655463eb21c3a,0x359551db2c2704b2aa37,0xe7cb21c12eca8ed56118,0x2c8b9aa99ce97e096550,0xaa6375db865cd54d4fc3,0x7059564552e3f2ac1ac8,0xd954d1fc02cab22a9c3f,0xac61c0aecaa679483815,0x7b8ac91f590e05765533,0x575e5573dc564ceac2ae,0x603715933e2a0c06e2b2],#[0x648fbcab01b8ac91f595,0x2ac1ee2b267561583dc5,0x8ac99755061771592baf,0x9e4985dc5648fbc830bb,0x5735933ab26c2ee2b267,0xcaebaf0ab9ac9a5f8559,0xc3105509a0ec12012000,0x30f41b02dc500931021b,0x4d2944f4981282364388,0x2f65b8b095e2b654ca81,0x6ccd59a3340674c8183,0x45072013e879ced1d238,0x132234408750d2174288,0x23b4708d51922f4588a5,0x34a0935252474889051f,0xd09953125f4b89652b25,0x9f53d2774e89c53726b4,0x54928f518a2543283500,0x52a7548a854f29b530a5,0xbf578ae55b2b3560ab55,0x5a8b45672cb590b15612,0x8ba5732e35c0b756d2d7,0x57f2fb5f0bd5792ef5d,0x8b313620c3585307608c,0x32b650c959131f638c65,0x3680cf59d337668cc597,0xb0d55a934f698d25a334,0xdb5b53676c8d85af35b6,0x4f081f0903f0a180903,0x7c2e24240fc1c27c209,0x7c10fc16202231880b88,0xb1ec90bc2083490d88d1],#[0x26f08241b41e001c7244,0x821f0824080507341e00,0x4c2420901f0826090309,0x82413420901091c3082,0x24080005004000011845,0x9824082605c30982098,0x811041004000260902,0x4209410981184030961,0xe098641420440e0811f,0x4c]]
def g191H6 := limbs80 #[#[0x2e01800c1000006caac0,0x8151ea35e54000008224,0x800a01413865c1000002,0x629c810300044600309,0x10588de1073b6700000,0xe840060a41a000000000,0x391785001e64c940ec30,0x485b11f75b0080000000,0xca00000000787000003c,0x61700007c003]]
set_option maxRecDepth 16000 in
def g191D7 := limbs80 #[#[0xfb15450110f255450951,0xdf17550110fb16450110,0xfe14258110bf18650110,0xbf38458110ef16458110,0xdf17558110ef16558110,0xfa55450910df37558110,0xde57550910fa56450910,0x9f78759110d757555110,0xd757559510be78259510,0xf555454630fc54254630,0xf556554630dd57454630,0xd9d7455230dd57654630,0xbd781592309dd8755230,0xcdd7659230d9d7459230,0x9df845da309dd8759230,0xeb96458140f395454140,0x9f7815d940f355454540,0xde542dc151e756554560,0xd7565dc151d7554dc151,0xfa56450951fc56350951,0xbd78650d51f556550d51,0xbd78458d51f555458d51,0xf356455151f558355151,0xb778655151b758655151,0x9f78759151e756559151,0xf558359551f678259551,0xbe7825d951b778459551,0x9dd85dd943bcf8259543,0x9f7815d954e3d6559154,0x9f580dc564dd573dc564,0x9f585dc564dd583dc564,0xff15458110ff16550110],#[0xfb56455110fe56550910,0xef56559110f756555110,0xfd56454630bf7855d910,0xf9d6455230fd58654630,0xedd6559230ddd7655230,0xfb96454140ddd7559230,0xfb95458140ff15158140,0xfb56454540ef96558140,0xf3d6555140f756554540,0xfe54254560ebd6559140,0xef56454560f755454560,0xdf564dc151ebd6455160,0xf758459551f758655151,0xf9d645cd54bf7805d951,0xfb78159154bdf865cd54,0xef565dc564f9d8359154,0xedd655cd64bf585dc564,0xff18458110bdf855cd64,0xfe58550910ff18558110,0xbf58655110fe58650910,0xfe78259510bf78655110,0xfd58454630bf78459510,0xbdf8655230bdd8655230,0xfd78159230ddd8755230,0xddd8759230bdf8559230,0xdf97654140ddd845da30,0xbfb8558140df97558140,0xdbd7655140df57654540,0xbbf8655140bbd8655140,0xdbd7559140fb78159140,0xbef8259540bbf8559140,0x9fd8759540cfd7659540],#[0xdf7815d9409ff865d540,0xdf774545609ff855d940,0xef78159160afd8655160,0xaff8559160cff7559160,0xf7580551519fd85dd160,0xfcf8259543f758059551,0xdde8755163dde8759543,0x9fd86dc154dbd64dc154,0xbbf8059154ddd765cd54,0x9ff805d954bf7815d954,0xddd835d954df7815d954,0xcfd65dc1649fd80dd954,0xdf570dc5649fd85dc164,0xdf575dc564bf580dc564,0xdf585dc564df580dc564,0xbef825d564ddd755cd64,0x20409c0009fd80dd564,0x417d0a984801ec0cc051,0xc8a984f825210687b038,0xf23cf1d28dc867e30c16,0x76130894248022b108c7,0xc3c5e22d795f0aa451f2,0x3a81c50dc26b73421920,0xd0e083d4051f5cf48771,0xc4cca5e127890946fa28,0xd5572a7d529a8a53ec9c,0xf15e82e996d4b4058b2b,0x24d8f6c5162130a9836b,0xd116783361992cba655b,0xb6f1b5ad7a6acb505a52,0xae7071eb8b9c2cdf56e5,0x43e1def0f5779b3be9d6],#[0x5f029811bfe5fb0fb77d,0x29c13608f04181dc0d60,0xef071835c1960bf0598,0x84dc25611f089841c1f6,0x617f0b9859c2b614f0a1,0x9871c3761af0d1865c31,0x3620f10187dc3d61df0e,0x31895c49623f119889c4,0x55629f1498a1c4f626f1,0x1798b9c5b62cf1618adc,0x4de1111918c5c6162ff,0x13183028703216e4f1d2,0x460482708481f0c2c14e,0x903e208b84240f890963,0x41170784240f8ac1e10,0x4e0f0a12c61c3fc21109,0xf87c2634244820883a1,0xb009426f098d891f84c6,0x8d891209c22687c48205,0x589148dc2e0e24482d05,0x3e028dc2c48b4705d178,0x31710291b85c1c48905a,0x304e09418b88118340a3,0x5287058f88128146442,0xa303110270680c7a322,0x251e8b880c1e0c4407c,0x87b8145440b47e00311,0x87a10207a8fc0062205e,0x605e0f03841b0c0bc062,0xc1087093037040fc2e00,0x6c48c0bc2f0b1220702d,0x58b49880a1d08707842],#[0x421491785c1a48804e13,0x1c031f0d45648cc7e170,0xe0a428b4917842612074,0x2d24563e030d45248ac7,0x147c3314922f0521476,0x5c1120a1188705921c17,0x30738580e089060e0438,0x70b82241785c11208041,0x7c1a382f0dc2a28c2608,0x118870592261621c2128,0x2a3c402c2f0b82261208,0x74244a3d1b0b891033c,0x80fc24370781051a8ec6,0x46c90e8fc105e1b0bc21,0x78564880bc2f09922010,0x202f0f856370784361c1,0x41185091206c260c2448,0x8091c8a1090126b0d842,0x42419402059188642104,0x78445043c091812930,0xd09084d09084c2484874,0x312289986240c4d09084,0x6244130226044d82c089,0xc48160849890c4c24c1,0x10e2362b0d841014380b,0x82261c4c1661b05001ce,0x2190882307438c34070b,0x38383088398e18641747,0x31182240704c31182116,0xe104813070785e108c,0x9b1b8]]
def g191H7 := limbs80 #[#[0x14208021c0000014009,0xbc58000009820a0460b6,0x20218f84153c1010a,0x124a004446c98310e,0xa300000070000400165c,0x8810002a3c000000504e,0x8001c6f53e0002620c32,0x593085881100018a,0x24f207a0000cda0fa00,0x220005c3c000000f9d00,0x976a280004014279ccea,0xa6d11d49a1a960000005,0x84d8000001,0xa60000000000593,0x14c30e190894f848000,0x2fe82000000020d88b00,0x4210800003b80006,0x831e49d0af5636b60000,0x9064a4252c4250002939,0x262683e00000018dc000,0x9000200d938459000000,0xe28820c001e3,0x64d39b9d384de5400000,0x15587662fe2bc13f4ac8,0x21e000240041b103a434,0xe08148f05a0004d280f7,0x9123b00fd2789a000c0b,0xeb91066b869205ca3d40,0xfc4855258001a2c024d1,0x44090d133846f0300020,0x825681c32d94e8712141,0x69da4b0a07e356871],#[0xbc8345294691b3c90c2e,0x50001248000a19000319,0x8ece263100068cc00020,0x1d10b00038c345f00078,0x915cb883052038da6534,0xe7564d0001ece60a0006,0x186d91205ee004a60d2b,0x566b107821c0a1c37c92,0x50002202000313e9c983,0xdd828d47000192600082,0x1fda30001b560003e3d2,0xcf198b12120af84361fa,0x31a1025cc168a98e40b7,0xd4c7128d4ee8f206a525,0x7548a253a9a000991657,0xe08b4000a74fef3,0x92dd188000497f8900,0x24e00000]]
def g191D8 := limbs80 #[#[0x542443f8b0221fc50110,0x8c617ddd510beaea887e,0x51bbaed185dd748c3eaa,0xfd543547f2a12a37ddc1,0xab2aa3dd55151faac6a8,0xd163bbeeca1ddf7550fb,0x887f554442fbb8ac977d,0x3fabaa21fd59510feac8,0x759230fbaa9187f57644,0xa2a07f960503fca8281f,0x503deb2281ef55140fea,0x1fd54560bfaeca05fd75,0xeae0a8dff745837eb22c,0x76547faba2a3fd59151f,0x2a9f755163fbacaa1ff5,0x4f7ac8aa7dd73552ffb8,0xff70592ffbb2a97f5d95,0xb2ac9f75cd64feee2b25,0x160ffacaa05ff755937e,0x7fd75593febb2a9ff55,0xfeb82c9ff5c154ffae8b,0x704783e02e82100d8003,0x8bc0aa89908187406485,0x249111018f60ea8df0cd,0x917d9701629531439301,0x9f21dc9c71b99ac19898,0x62a53247a36226a17205,0x72c7ab029ea8f281a722,0xb36324b15303af42e4ad,0xc11f1b6bb6a368b57343,0xb1457051c24909c7c6c2,0x14dc2c7c61f1888771b0],#[0x1f1054430b0518922474,0x1431f151b06207c2c146,0x207c7c6c1c0080c190,0xc2c11049187b1b151f07,0x6537271e191708bc7c5,0xc786c145492106005a4,0x4203161b051d24816908,0x1c16c9c710c1c2452076,0xe1477271443051f08988,0x1f070024385c1c00f090,0xf070a147c1c013090c15,0x6c2c1464589242f271a1,0x251b0b04907c58014471,0x87801447451dc2c14689,0x215161c4227070874545,0x1b070116206124680c1c,0xc6054647c1c04588191d,0x9c1c2c047181f0b07006,0x1d005a270b051a609220,0x6061cc1c2c046181842,0x5c2c1c089289307091f0,0xb070224a1c1a1707468,0xc146892490885d1c1a17,0xb01162484010851dc287,0x2c145c0221c90881f070,0x550b047441245870603c,0x510484543c2c1862420,0x7c2c110161f0b0428748,0x391f0217051a24712484,0x47061346c1c08745891c,0xec1c0491c1c1f0b07012,0x70170b07011e18811c70],#[0x308478685c2c1c02c90,0xd1f07030870726241c,0x88c706c2c1c04924182,0xc0c149241f271a140307,0x1f0b07011a14813c60e,0x8080346c0c1c2241c989,0x22191a090a05045e2498,0xd05011f089458242891c,0x11cc2c02420989072150,0x2685434]]
def g191H8 := limbs80 #[#[0x85418402544012204000,0x8c41f1a0400206043070,0x57031600202491018606,0x1010220c13260078f031,0x303a300204868a1018,0x6915c1c51896d2000000,0x631b606e51d234393680,0x42d2ef4d210ba1a26b00,0x217228fc32599a8cfc,0x16c2200029c144f4580,0xb995cd9a8691310a5a4c,0x3261572b2d9e516b113f,0xd68b6d98000000a3a507,0xb090980e404000304789,0xaa2be167c4a7780006c,0xa280010820003a048bda,0x1f00050bbf240000001,0x3d85d3044782eba14000,0xb109bba857c000640915,0x8cd48c90255e0388b18c,0x10848831a5e46000e0,0x3e39dc000030f3731800,0x1c414085836027026e,0x5d340011542490000,0x7cf203548b8000001f39,0xe0004a004a3d6ab26505,0x40e97c3bc020003ed077,0x4ea828000001a34fcbfa,0x84a11f5653bdc9cf40a4,0xe8800078620e4c6cd1e3,0x5a2c00058e0005c44873,0xa4500011fd268b2fba1],#[0xd586c8cfa4bc2a59bc00,0x9400064f410c03c000e0,0x101a276e7236815e9ec4,0xf0c646b1450fc24588e1,0x3ab28f451808723e8a18,0x4005a170005247137849,0x780461600000015e,0x59929495a3b117d42dca,0x2f6ace18720614a42862,0x20d463444535603eca72,0xa6421f0003236c290006,0x42344fdd510000000000,0x3d77e27e876f17675386,0x69df4000000a0ce95813,0x38000a877a7c001e7851,0xa721e80b400000060911,0xe38000404b801255527f,0x203294bece463f337502,0x143aa38856d12e000]]
def g191D9 := limbs80 #[#[0x63f750ff551f78c3f510,0xfd64ff553fd60ff503dd,0xfef53c82b554a671b803,0x6008180478d08fc1123e,0x424c78a1a0c2223c68b0,0x1802468f1a0c00a24600,0x98f1a141806078d143c,0x82928a1468a1e0c0124,0x1061242419c931c34181,0x393183858]]
def g191H9 := limbs80 #[#[0x22412001c3142001141,0x1081e67e72c0b003430,0x11d001b091c29f0,0x17dc00360000,0xc94623d305ec31462c00,0x3626a002054ab24d48a1,0x14840018c713ace87a,0xfc0e31000ca800156ccd,0x604000000561958b,0xf080000000000000a100,0x8000000000000051d091,0xcb8001cc,0x20001c900044eb400000,0x2720380082fc0046feb7,0x479f300012a5c1000eb4,0x1800a0a000c88a800111,0x6036000003b7c8662c9,0x32e12c2a05ca05d8d,0x186a4c2b486554997c13]]
def g191D10 (j : Nat) := if j=0 then 0x1238c2820043ff else 0
def g191H10 := limbs80 #[#[0x4413241c032319080028,0x130018401187280001,0xe45d4006700000]]
def g191L : Nat → Packing
  | 5 => (36,5,6,0,0,8,0,g191D5)
  | 6 => (160,4,6,0,0,11,0,g191D6)
  | 7 => (161,3,6,0,0,13,0,g191D7)
  | 8 => (58,2,6,0,0,12,0,g191D8)
  | 9 => (9,1,6,0,0,9,0,g191D9)
  | 10 => (1,0,6,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 10 67 3 11 6 1 g191H6
  | 7 => lookupWord 50 277 7 13 8 1 g191H7
  | 8 => lookupWord 57 283 7 13 8 1 g191H8
  | 9 => lookupWord 20 127 6 11 6 1 g191H9
  | 10 => lookupWord 3 23 3 9 4 1 g191H10
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P5_0 : CutRow g191 5 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P5_2 : CutRow g191 5 2 34 := by
  apply polarBlock (data:=fun _ => (word80 [0x20,0x84024102094000210102,0x8421130002080824022,0x9400020808240220940,0x10020080490882210401,0x4021104123211020080,0x49188a21040104021104,0x12321002008049088232,0x10020080490882320208,0x1020824113200200080,0x48220950002000804822,0x95000200100c0520950,0x200400c11209500020,0x1020852095000200082,0x40320940002001020852,0x9400020010208520950,0x200402411209500020,0x824032094000200082,0x40320940002001004852,0x9500020040241120940,0x200402411209400020,0x821032095010002080,0x49208221040104021104,0x12431002008049088231,0x4010402110412320021,0x400c102113202002400,0x85201241040800821048,0xa03100c1040281021241])) rfl
  decide +kernel
theorem g191B5 : CutRow g191 5 0 36 := (@joinRow g191 5 0 2 34 g191P5_0 g191P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_0 : CutRow g191 6 0 14 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_14 : CutRow g191 6 14 28 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_42 : CutRow g191 6 42 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x200082,0x40320950002001028052,0x96000200100c0520950,0x200402411209500020,0x4024112095000820402,0x81082431020004020920,0x12620200040209201252,0x210402410211300021,0x100c042113000200082,0x40320950002004024112,0x95000200100c0520950,0x200100c05209600020,0x4024112096000200082,0x4032096000200080c032,0x9601000010091408463,0x280082402281400200,0x24020920124210020080,0x49208253020024020920,0x12410200040209201262,0x210402410211200020,0x824032096000200402,0x41120960008801028048,0x84310202040209201252,0x20801020824903200c2,0x4024108245102002402,0x9201252040004021140,0x24630200040209201263,0x4000402114024630401,0x4021140245204080082,0x1048a03200c104028104,0x1253040800824060a053,0x2002402052012310028,0x824022816402020402,0x8120303200280080c024,0x81630200140205201142,0x4000402114024620401,0x4024140305204080082,0x4060a032100010804520,0x81430021040281041153])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_90 : CutRow g191 6 90 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x10000100,0x91408464030801020834,0x90321002008049288243,0x2002402092012420200,0x4020920126302080102,0x8249032020801020824,0x90321000010091408463,0x20881022824903201c2,0x4424118244101880102,0x804884310200a4020920,0x12420200a44229201231,0x4010402110412431000,0x20804920823210020080,0x49208254002104024102,0x11200208010208249043,0xc20402410824511002,0x804920825400280082,0x40228150020024020920,0x12420208010208249043,0xc20402410824510401,0x4021104125402000402,0x920126300210100c042,0x114000210400c1021140,0x210402410211300202,0x4020920125410010100,0x4904904300c204024108,0x24510208010280601154,0x280102804211540400,0x10804460214300820402,0x81082420040104004540,0x30431002008048228254,0x2020402090212530400,0x14004540214302020402,0x81201154100101004540,0x90431000108045208143,0x220402810221400021,0x100c042113000820402,0x81082431002000824032,0x9600020010280520950])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P6_138 : CutRow g191 6 138 22 := by
  apply polarBlock (data:=fun _ => (word80 [0x208080c022,0x9500022008240222150,0x200840229201a520202,0x4028120303202000402,0x9201263020004020920,0x12530200840229201a52,0x200840229201a620200,0x4020920126302000402,0x9201263020004020920,0x12520200840209201252,0x2008402092012620200,0x4020920126302000402,0x9201252020004020920,0x12520208000a04223054,0x2020008842230540022,0x4024102214000208082,0x4022095000280100c042,0x81500400040211402453])) rfl
  decide +kernel
theorem g191B6 : CutRow g191 6 0 160 := (@joinRow g191 6 0 42 118 (@joinRow g191 6 0 14 28 g191P6_0 g191P6_14) (@joinRow g191 6 42 48 70 g191P6_42 (@joinRow g191 6 90 48 22 g191P6_90 g191P6_138)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_0 : CutRow g191 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_1 : CutRow g191 7 1 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_49 : CutRow g191 7 49 13 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_62 : CutRow g191 7 62 37 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_99 : CutRow g191 7 99 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x10000080,0x49208275100100084502,0x90650202044281203043,0x2020008842230540401,0x84442307401480082,0x40248251014104024104,0x12310141044241141221,0x2002402092012530088,0x1028048844100220402,0x81022150020801028060,0x90640028010280428160,0x820402810824410202,0x4028120305400280082,0x4022815000210100c042,0x11400082040281082441,0x210402410211400021,0x100c042114000210402,0x41021140040004021140,0x247410010100c1409065,0x220080c02221400082,0x4028108243104010402,0x41403064040800824060,0xa0540028008240228150,0x210402410211301000,0x11008540816502020008,0x842230430208000a0422,0x90530082040281082442,0x820402810824420208,0x1028060905300820402,0x81082431004800824024,0x82510202040281203043,0x2020402812030430088,0x1028048844104080082,0x4060a054020024020920,0x12520202040281203043,0x2020402812030430022,0x2070b81a213010002080,0x49208254020024020520,0x12520082040281082430])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P7_147 : CutRow g191 7 147 14 := by
  apply polarBlock (data:=fun _ => (word80 [0x21,0x4024102114004000402,0x11402474020284028120,0x30430208000208249053,0x820402810824410208,0x1028864905300820402,0x81082441008204028108,0x24410202040281203054,0x208000a042290740021,0x100c042114002020402,0x81203043020204028120,0x30430202000884223054])) rfl
  decide +kernel
theorem g191B7 : CutRow g191 7 0 161 := (@joinRow g191 7 0 62 99 (@joinRow g191 7 0 1 61 g191P7_0 (@joinRow g191 7 1 48 13 g191P7_1 g191P7_49)) (@joinRow g191 7 62 37 62 g191P7_62 (@joinRow g191 7 99 48 14 g191P7_99 g191P7_147)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_0 : CutRow g191 8 0 18 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_18 : CutRow g191 8 18 33 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_51 : CutRow g191 8 51 4 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P8_55 : CutRow g191 8 55 3 := by
  apply polarBlock (data:=fun _ => (word80 [0x820402,0x81082452004800824024,0x82610082040281082452])) rfl
  decide +kernel
theorem g191B8 : CutRow g191 8 0 58 := (@joinRow g191 8 0 51 7 (@joinRow g191 8 0 18 33 g191P8_0 g191P8_18) (@joinRow g191 8 51 4 3 g191P8_51 g191P8_55))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : CutRow g191 9 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_5 : CutRow g191 9 5 4 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : CutRow g191 9 0 9 := (@joinRow g191 9 0 5 4 g191P9_0 g191P9_5)
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
  · exact g191B5
  · exact g191B6
  · exact g191B7
  · exact g191B8
  · exact g191B9
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
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfb02da18b421cc2951,0xe0c00001fc0000003fff])),(BitVec.ofNat 152 (word80 [0x4102d81094204c0841,0x80c48912244891224489]))),((BitVec.ofNat 152 (word80 [0x1228d2402d89e9fc1,0x1b0000fe00000fffc000])),(BitVec.ofNat 152 (word80 [0x61008c2402188c1fc1,0x90183060c183060c183]))),((BitVec.ofNat 152 (word80 [0x758ad02f634115537,0x8407f000007f0000000])),(BitVec.ofNat 152 (word80 [0x87188d02f634105513,0x803870e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xf25c4ce7abc3f04140,0x6900000003f80000007f])),(BitVec.ofNat 152 (word80 [0x25c04e623c3904100,0x6913264c993264c99326]))),((BitVec.ofNat 152 (word80 [0x85814f63a014663a,0xd6bf80000000001fff80])),(BitVec.ofNat 152 (word80 [0x5010b618010603a,0x520a142850a142850a14]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x116669158062bf0a8,0x15c0000003ffffe00000])),(BitVec.ofNat 152 (word80 [0x26211080023a028,0x14ec58b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0xce93272055b22080f,0xc3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x8e022400043220004,0x43060c183060c183060]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(4,0,219,0,10)]
def g223A : List (List Nat) := [[]]
def g223D10 (j : Nat) := if j=0 then 0xff else 0
def g223L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g223D10)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,10,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : CutRow g223 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : CutRow g223 10 0 1 := g223P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : mixedTables g223 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g223 0 0
  · exact mixedEmpty g223 1 0
  · exact mixedEmpty g223 2 0
  · exact mixedEmpty g223 3 0
  · exact mixedEmpty g223 4 0
  · exact mixedEmpty g223 5 0
  · exact mixedEmpty g223 6 0
  · exact mixedEmpty g223 7 0
  · exact mixedEmpty g223 8 0
  · exact mixedEmpty g223 9 0
  · exact g223B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 11 := mixedLower (g:=g223) (i:=0) (hints:=16778819) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 11 [(223,[]),(239,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xd2c83c9253ca252200,0xfe0000001fc07f])),(BitVec.ofNat 152 (word80 [0xd2c01c90520a212001,0x22448912244891224489]))),((BitVec.ofNat 152 (word80 [0x42af409550361b84a0,0x7f0003f800003f80])),(BitVec.ofNat 152 (word80 [0x42ad409110161b0020,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xecd729801410d27110,0x3f8001fc000fe00000])),(BitVec.ofNat 152 (word80 [0xccd628801410920010,0x60c183060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x8432279aa84d908c40,0x1fc000000007f0003fff])),(BitVec.ofNat 152 (word80 [0x41221022841808c02,0x44891224489122448912]))),((BitVec.ofNat 152 (word80 [0x1a99a692c12e442af,0xe00000000007ffffc000])),(BitVec.ofNat 152 (word80 [0x129024900004442a4,0x89122448912244891224]))),((BitVec.ofNat 152 (word80 [0x7154172748a10967d0,0x1fff800000000])),(BitVec.ofNat 152 (word80 [0x3100172648a10067cf,0x1e3c78f1e3c78f1e3c78]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x200080248180001048,0x10204081020408102040]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(2,0,245,0,10),(4,0,243,0,10),(0,64,177,6,9),(16,0,231,0,9),(32,0,215,0,9),(64,0,183,0,9),(128,0,119,0,9),(48,0,199,0,5),(144,0,103,0,5)]
def g247A : List (List Nat) := [[],[33,84]]
def g247D7 := limbs80 #[#[0xc1aeca1e37ddb835d943,0x87e9f76e116350f33f09,0x3765d943dedc9f00bb2,0x650f9bf07bb2eca1f3ee,0xdc9f00bb287ddb83e017,0xaeca1f3ee5b805d943ee,0xe9f74e0d6458fb3f09c1,0x805d163dedc9f00ba2c7,0x4a88f9c32585806bee5b,0x3c35c2f1f00b462b95a8]]
def g247D8 := limbs80 #[#[0x9fb805d943e9d6458d43,0xedf7658d43f9f8458d43,0xbdf835d943bfb805d943,0xdfb805d943cff765d943,0xedf8359163ddf835d943,0xbdf835d163bfb805d163,0xffb805d943aff865d163,0xffb805d163fdf835d943,0xeff865d163fdf835d163,0x5b14344cd5294750f800,0xaeeb5abe789060374daa,0xbf6e696272e3c08b1ec1,0x3c2b8ddb9e5c9cb8d71c,0x91c8bc4e3c328dc92c4e,0x270ae330edcf2f2e392b,0x2c08cb93971e0288e5c5,0xe5c6bf0172e4edcebf2e,0x8d5ce44749cb8f0aa365,0x3971e15738ec3b73c9cb,0x94fcb8f0ab907129]]
def g247H8 := limbs80 #[#[0xaa800000044800c2002a,0xd6002a00000710031530,0x39400c00180358,0xdc0000335ac000033f4c,0x920]]
def g247D9 := limbs80 #[#[0xe6550fbeb2a87f758d43,0x22c77fdd943bfaeca1f7,0x43ffaeca1dff7458f7eb,0x7ff7458ffeba2c7ffdd9,0x2c4991f86612c3306c00,0x9b672e58e0b910b3b4cf,0xbe58e03cb226be58e038,0x8f2ed9c8be58e044b22c,0x6ae58e1211b66be39612,0xbe04ed9ab8e584e38fb6,0xe58e0b904912ed9c9962,0x326d9cf92b8e048a26d9,0xe26d9e58e0a9249]]
def g247H9 := limbs80 #[#[0x544000034cf264113c03,0xfa007701ae7360b13c00,0xa2800c0c00f420200069,0x345,0x348e97c443823000c6]]
def g247D10 := limbs80 #[#[0xff58ffd43df9977d65,0x180f5a1c709447805229,0x8bda6524a3022b439a5,0x2b6990f28c]]
def g247H10 := limbs80 #[#[0x40cc400,0x0,0x80000035000000094000,0x6840186000000130124,0x117cfc90000000000]]
def g247D11 (j : Nat) := if j=0 then 0xea8c642047f else 0
def g247H11 (j : Nat) := if j=0 then 0x342a011e9b1 else 0
def g247L : Nat → Packing
  | 7 => (13,4,4,0,0,7,0,g247D7)
  | 8 => (18,3,4,0,0,10,0,g247D8)
  | 9 => (11,2,4,0,0,10,0,g247D9)
  | 10 => (4,1,4,0,0,8,0,g247D10)
  | 11 => (1,0,4,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 4 47 2 9 4 1 g247H8
  | 9 => lookupWord 5 37 4 10 5 1 g247H9
  | 10 => lookupWord 3 47 0 9 4 1 g247H10
  | 11 => lookupWord 1 7 0 7 2 1 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : CutRow g247 7 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_2 : CutRow g247 7 2 11 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400a1502c4240,0x4400a1502c42300044,0xa1502c4231004400a1,0x502c4231004400a1502c,0x4240004400a1502c4230,0x4400a1502c42300044,0xa1502c4241004400a1,0x502c4240004400a1502c,0x4230004400a1502c4231])) rfl
  decide +kernel
theorem g247B7 : CutRow g247 7 0 13 := (@joinRow g247 7 0 2 11 g247P7_0 g247P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : CutRow g247 8 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_2 : CutRow g247 8 2 11 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_13 : CutRow g247 8 13 5 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400a1502c42510044,0xa1502c4241004400a1,0x502c4240004400a1502c,0x4241004400a1502c4240])) rfl
  decide +kernel
theorem g247B8 : CutRow g247 8 0 18 := (@joinRow g247 8 0 2 16 g247P8_0 (@joinRow g247 8 2 11 5 g247P8_2 g247P8_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : CutRow g247 9 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_7 : CutRow g247 9 7 4 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : CutRow g247 9 0 11 := (@joinRow g247 9 0 7 4 g247P9_0 g247P9_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : CutRow g247 10 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_2 : CutRow g247 10 2 2 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : CutRow g247 10 0 4 := (@joinRow g247 10 0 2 2 g247P10_0 g247P10_2)
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
  · exact mixedEmpty g247 6 0
  · exact g247B7
  · exact g247B8
  · exact g247B9
  · exact g247B10
  · exact g247B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := mixedLower (g:=g247) (i:=0) (hints:=16778564) (before_sound K223 V223) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K223 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V223 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x4e844a219d84168000,0xff000000ff00ffff])),(BitVec.ofNat 152 (word80 [0x46800a210d00068009,0x9090909090909090909]))),((BitVec.ofNat 152 (word80 [0x27b0031d6076ae300,0xff0000ff0000ff0000])),(BitVec.ofNat 152 (word80 [0x271001196060ae305,0x5050505050505050505]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2005c746be72596000,0xff0000000000ff])),(BitVec.ofNat 152 (word80 [0x200545469212596046,0x46464646464646464646]))),((BitVec.ofNat 152 (word80 [0xa7226dd0022bc11400,0xff00000000ff00ffff00])),(BitVec.ofNat 152 (word80 [0x10245800029c10012,0x12121212121212121212]))),((BitVec.ofNat 152 (word80 [0xd91534dc13442229ff,0xffff000000])),(BitVec.ofNat 152 (word80 [0x981530541244202124,0x24242424242424242424]))),((BitVec.ofNat 152 (word80 [0xc49a93a66070a8ae00,0xffff0000000000])),(BitVec.ofNat 152 (word80 [0xc48a92a06060a00cb8,0xb8b8b8b8b8b8b8b8b8b8]))),((BitVec.ofNat 152 (word80 [0x30c990090098855dff,0xffffff00000000000000])),(BitVec.ofNat 152 (word80 [0x200880080090001cc0,0xc0c0c0c0c0c0c0c0c0c0]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(2,0,249,0,10),(8,0,243,0,10),(32,0,219,0,10),(0,64,177,10,9),(16,0,235,0,9),(64,0,187,0,9),(128,0,123,0,9),(1,0,250,0,8),(0,8,178,65,7),(33,0,218,0,7),(17,0,234,0,5),(129,0,122,0,5),(144,0,107,0,5),(146,0,105,0,4)]
def g251A : List (List Nat) := [[],[116]]
def g251D6 := limbs80 #[#[0x7058f9b394605701c163,0x61701c163a6eaa5845c0,0x31831bba4e]]
def g251D7 := limbs80 #[#[0x402c698637ddb8358130,0x6179994201634c2fa322,0x5701c163c7dbb700bb2,0x58f37308b80e0b1e7c6,0xfca30f382c71fb985c07,0xac0987b6e4163581308d,0x7da97201634c3db6edc1,0x845d930f6dbb700b1a61,0xc373f27c22ec986eee43,0x1eecbb261cfb80dd9764,0xc9872fe13765d930e6fc,0xf80e11764c3b7709c02e,0x5d930eddc8708bb2619b,0x37f21c22ec98767e4f84,0xe0382c7dbb945c07058f,0x1ee7e4f845c163cfdcc2,0xd4440f00337f28c3ce0b,0x82351487421f4c44f1e0,0xb54295449f4e2652c934,0xd13cfcbc03b75a2c55ca,0xf207cfc028a44f30af20,0x60b0ab319102c2acfc84,0xf3042c2b9b900fc8]]
def g251H7 (j : Nat) := if j=0 then 0x2df8000001c else 0
def g251D8 := limbs80 #[#[0x9bf845d930ed96358130,0xbdf8358130edd6358130,0xbfa8798130fdb8358130,0xfdb8058d30fd88058d30,0xbfb805d930edf7658d30,0xcff765d930bbf845d930,0x9ff805d930dfb805d930,0xdf9701c163dbf845d930,0xbed821c163bf5811c163,0xbdf835c163bbd841c163,0xdfb709c163bbf845c163,0x9fd879c163bdd839c163,0xffb805d930fdf8058d30,0xfdf835d930bff805d930,0xdff805d930fbf845d930,0xfbf845c163fdf835c163,0x661d41f000bfd879c163,0x8ecfe9c631e560908ea1,0x5d0369664bed6229b4f2,0xe5369f13064544c838f9,0x66ac156aaa54ea9150a9,0x780f1faf32c938f0e445,0xc7824e51c865d79d6c9c,0xe2b9f049c79561faf32d,0x71e7907e7c23a4e5c6b0,0x20ae6c787218387e15b9,0x5c050ecd3c4e1c79561c,0xe1c6b73e590809cf896e,0x4cfd5973e1c6b6420527,0x83d6c9c39f2179f015c8,0xe7c59701eb05e7c7872c,0x7a7c058a67c8b8f5b275],#[0xf970c84f5c9cf8f22e34,0xcf8f032307119baf3625,0xc840ce69397016375c9,0xf2e05c60fd6bb2e7c737,0x40ce7c4bf0e4907c94d9,0x198605c9cf8f0e4]]
def g251H8 := limbs80 #[#[0xa2b3000000000006805,0x10000000000000000000,0x65c000035,0x300000003c1d30000000,0x32,0xee002002d0000000000,0xa580000000410000000,0x94c9800280000000000,0x986c300000001450000,0xd31c000036ea48000000,0x2724000000000000003c,0x72c00002a,0xf001067d000000000000,0x2c,0xf2000002d4c380,0x465950000]]
def g251D9 := limbs80 #[#[0xd634c3fd30261fe58130,0xb4617fdd930bfaec987d,0x30ffac0985ff7058efeb,0xffc7058fffbb261ff5d9,0xfb82c7ff9c163ffae0b1,0x84e102348a21b036003f,0x6422e2a9a6a889e66a96,0x75a4c32c481f5cd6c32c,0xc871359f3c70c96235cc,0x735b1c329075b5ce4c70,0xca61e4d731f1c32588d,0xd73c16cb11e42a4d73c7,0x892a7d73930c56c892ca,0x7cb030b1c4d73c32c562,0xcf1930c89d53195933c5,0x26d73c64cb05c93355e6,0x197d64cf1cb03093]]
def g251H9 := limbs80 #[#[0xa009412c0c0003044,0x9300030ce2000f0767c,0xe26cde9e001e5000,0x24002c3800a8ca008780,0xa340d000e05c40cb404f,0x84e999d1181423800818,0x5901d1574c088569b081,0x4b431271ef70e42ee568]]
def g251D10 := limbs80 #[#[0x45c5c03fd63ff8c3fd30,0xb324a303907b566484a2,0x7accd124a041a]]
def g251H10 := limbs80 #[#[0xd689a0d2020079942004,0x72a250c0000003a9cb2,0x1304e8b000010]]
def g251D11 (j : Nat) := if j=0 then 0xc8a64203ff else 0
def g251H11 := limbs80 #[#[0x4000140009801880,0x3a0]]
def g251L : Nat → Packing
  | 6 => (3,5,4,0,0,4,0,g251D6)
  | 7 => (26,4,4,0,0,9,0,g251D7)
  | 8 => (33,3,4,0,0,11,0,g251D8)
  | 9 => (14,2,4,0,0,10,0,g251D9)
  | 10 => (3,1,4,0,0,7,0,g251D10)
  | 11 => (1,0,4,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 6 2 0 g251H7
  | 8 => lookupWord 8 127 2 10 5 1 g251H8
  | 9 => lookupWord 10 53 6 11 6 1 g251H9
  | 10 => lookupWord 4 23 1 9 4 1 g251H10
  | 11 => lookupWord 1 13 0 7 2 1 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : CutRow g251 6 0 3 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400c1,0x60344230004400c16034,0x4230010400190c164820])) rfl
  decide +kernel
theorem g251B6 : CutRow g251 6 0 3 := g251P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : CutRow g251 7 0 8 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_8 : CutRow g251 7 8 18 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400c1,0x60344241004400c16034,0x4231004400c160344240,0x4400c1603442300044,0xc160344241004400c1,0x60344231004400c16034,0x4230004400c160344241,0x4400c1603442300044,0x44321144241004400c1,0x60344241004404432114,0x4240004400c160344231,0x440443211442300044,0x4432114423000440443,0x21144230004404432114,0x4230004400c160344230])) rfl
  decide +kernel
theorem g251B7 : CutRow g251 7 0 26 := (@joinRow g251 7 0 8 18 g251P7_0 g251P7_8)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : CutRow g251 8 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_2 : CutRow g251 8 2 22 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_24 : CutRow g251 8 24 9 := by
  apply polarBlock (data:=fun _ => (word80 [0x44,0xc160344251004400c1,0x60344241004400c16034,0x4241004400c160344251,0x440443211442410044,0xc16034424100440443,0x21144251004404432114,0x42400044044321144241])) rfl
  decide +kernel
theorem g251B8 : CutRow g251 8 0 33 := (@joinRow g251 8 0 2 31 g251P8_0 (@joinRow g251 8 2 22 9 g251P8_2 g251P8_24))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : CutRow g251 9 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_7 : CutRow g251 9 7 7 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : CutRow g251 9 0 14 := (@joinRow g251 9 0 7 7 g251P9_0 g251P9_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : CutRow g251 10 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : CutRow g251 10 0 3 := g251P10_0
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
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := mixedLower (g:=g251) (i:=0) (hints:=16777283) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[]),(253,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0418928204c0afd7,0x62c00001fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x450418028204400ed3,0x42c2850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x1224e0c0c7c9c1f51,0x9a0000fe0007f0003f80])),(BitVec.ofNat 152 (word80 [0x61000c040c4c9c1b51,0x880183060c183060c183]))),((BitVec.ofNat 152 (word80 [0x75c2c42f7b0171535,0x940000003f800000000])),(BitVec.ofNat 152 (word80 [0x874c0c42e7b0171515,0x953a74e9d3a74e9d3a7]))),((BitVec.ofNat 152 (word80 [0xf258cda5aac3f04140,0x69007f000000001fc07f])),(BitVec.ofNat 152 (word80 [0x218458508c3900100,0x29050a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x85814f63a014663a,0xd6bf80000000001fff80])),(BitVec.ofNat 152 (word80 [0x5800a632000642a,0x528a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x116669158062bf0a8,0x15c0000003ffffe00000])),(BitVec.ofNat 152 (word80 [0x126291100220e028,0x142c58b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0xce93272055b22080f,0xc3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x8e022700010220004,0x43060c183060c183060]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(8,0,246,0,10)]
def g254A : List (List Nat) := [[],[33,84]]
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
theorem g254G : graphValid g254 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 11 := mixedLower (g:=g254) (i:=0) (hints:=287401280) (before_sound K251 V251) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K251 11 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V251 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff800000000003fe0,0xffffc0d107063590fcc])),(BitVec.ofNat 152 (word80 [0x108844221108844221,0x10884404002021580484]))),((BitVec.ofNat 152 (word80 [0xf0000001ff0000001f,0xf00000000081801e003f])),(BitVec.ofNat 152 (word80 [0xb0582c160b0582c160,0xb0582c000000800a001f]))),((BitVec.ofNat 152 (word80 [0x3fe00007fc000,0x1000c60103f])),(BitVec.ofNat 152 (word80 [0x70381c0e070381c0e0,0x70381c0000000400003f]))),((BitVec.ofNat 152 (word80 [0x7fc000000000000,0x7fc3000021080000f])),(BitVec.ofNat 152 (word80 [0xe472391c8e472391c8,0xe472381000000000000b]))),((BitVec.ofNat 152 (word80 [0xff80001f,0xfff800c21e0c1f01e1e1])),(BitVec.ofNat 152 (word80 [0x412090482412090482,0x4120904004041e004120]))),((BitVec.ofNat 152 (word80 [0xffffffe0,0x303e00fe001fe02])),(BitVec.ofNat 152 (word80 [0x824120904824120904,0x82412100400bc0009800]))),((BitVec.ofNat 152 (word80 [0x7ffffff00000000,0x3fc000ffffe0000])),(BitVec.ofNat 152 (word80 [0xb85c2e170b85c2e17,0xb85c3ec000f7bf40000]))),((BitVec.ofNat 152 (word80 [0xfff800000000000000,0x3fffff000000010])),(BitVec.ofNat 152 (word80 [0xc06030180c0603018,0xc0602b889c000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(1,0,254,0,11),(16,0,239,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(0,64,177,14,10),(0,8,182,65,9),(2,64,177,12,9),(8,64,177,6,9),(17,0,238,0,8),(33,0,222,0,8),(48,0,207,0,8),(80,0,175,0,8),(96,0,159,0,8),(129,0,126,0,8),(144,0,111,0,8),(160,0,95,0,8),(192,0,63,0,8),(1,64,176,14,7),(16,64,161,14,7),(32,64,145,14,7),(65,0,182,0,7),(65,8,182,0,7),(128,64,49,14,7),(17,8,166,64,6),(33,8,150,64,6),(49,0,206,0,5),(81,8,166,0,5),(97,8,150,0,5),(112,0,143,0,5),(145,0,110,0,5),(161,0,94,0,5),(176,0,79,0,5),(193,8,54,0,4),(208,2,45,0,4),(224,4,27,0,4)]
def g255A : List (List Nat) := [[],[33,84]]
def g255D7 := limbs80 #[#[0x36c661fb36195454140,0x140d71997ecd86551505,0x505033c669fb36195454,0x45c140cf1ba7ecd86551,0x5d170503666617b36197,0x19745c140d59995ecd86,0xd865d170503566e57b36,0xb3619745c140cd99a5ec,0x5ecd965d170503366e97,0x657b3659745c140d9998,0x99a5ecd965d170503566,0x366e97b3659745c140cd,0xd9b185ec5a65d170503,0x50366ce17b1699745c14,0xc140d5b195ec5a65d170,0x17050356ce57b1699745,0x755d154cdb1a5ec5a65d,0x65d57455364d603b1659,0x659755d154d93780ec59,0xc5965d57455354d643b1,0x3b1659755d154cd35a0e,0x89078604830180334de8,0x9816951392108f0d8c0a,0x211f9e1c9b19]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xe0a05f1bb36195454140,0x65d170502ecdd9b0cba2,0x762d32e8b8281766ecd9,0xa791d755d154e0d60bb6,0x150502e9bd8b2cbaae8a,0xbb2a8a82817ceee17655,0x39876195454140be7774,0x503b9ccbb0caa2a0a07b,0xa8a8281dcee5d8655150,0x76195454140de734ec32,0xd9cc3b4caa2a0a06f3ba,0x8281ecee1da655150503,0x95454140de734ed32a8a,0xdb30eaa2a0a05f3bb769,0x1eceed98755150503d9c,0x54140de736cd3aa8a828,0xeaba2a0a06f3bb669d54,0xe699755d150503e9cc32,0x40fa7370baae8a8281f4,0xa2a0a06f39a669574541,0x9975d150503e9ccbb4ab,0xb730ccbae8a8281d6e65,0xa075b9a665d7454140e,0x5d150503adcdb32eba2a,0xe9d1b0ca8281d6eed997,0x6f5975e8d8654140df32,0x505035ecc3f46c32a0a0,0xaaa8b82819f665fa3619,0x9965d5545c140fa730cb,0x3e9cd32eaaa2e0a07d3,0x8b8281f4e6d975551705,0x655545c140fa7370baaa],#[0x9cd3b2aaa2e0a0773996,0x281b6e699a755170503e,0x545c140db730cd3aa8b8,0xb34eaa2e0a06db99669d,0xb6eed9a7551705036dcd,0xc140bb7770b2ae8b8281,0xaba2e0a05dbbb9595745,0x619855d170502edddd2c,0xf3732cc2ae8b8281e6e,0x2e0a079b9a6615745c14,0x855d170503cdcdb30aba,0x732dc2ae8b8281e6eed9,0xa079b9a6e15745c140f3,0xd170503adccb32aba2e0,0xdcaae8b8281d6e61b955,0xdb9a6695745c140eb734,0x5036dcc374aba2e0a06,0x2e8b8281b6e65ba55d17,0xb5699745c140bb776acb,0x3e9cc2b48baae0a05dbb,0xb8281b6e699a45d57050,0x8d865c140f2f30cc2aea,0xcbaf46c32e0a06f9954e,0x81af6617a3619705036e,0x65c140cfb72bd1b0cb82,0xf46cb2e0a06f9954e8d9,0xf6617a3659705036ecba,0x140cfb32bd1b2cb8281a,0xcb2e0a06db975e91965c,0xd7a4659705033dccaf48,0xde734cd02eaaa2813ee6,0xa8a07d39876817555140],#[0x75d554503c9ec330ebaa,0xb4cc3aeaaa281e4f6598,0x793db661d7555140f27,0x954503c9fdb30ebaaa8a,0xd1b0caa281bc75d7a361,0x9d97e8d8655140d73b0f,0x5033cfcbf46c32a8a067,0x2caa281bce5d7a065954,0x7e819655140cf732fd03,0xe9cc2b40baae8a04fb9b,0xa281b6e699a05d574503,0x5755d140f27b0cc2aeab,0xdb30abaae8a0793d9661,0x1e4fed9855d574503c9e,0x5d140db3aebd1b0cba28,0x46c32e8a06b9d85e8d86,0xe5d7a0659745033cfcaf,0x40cf732bd032cba281b6,0xb2e8a04fb9b5e81965d1,0x7a1659745037d8a8742c,0x76b0bd0b2cba281b6d5d,0x8a06bb785e85965d140d,0x641755033dacaf42cb2e,0xeca320baa81dce61594,0x79799061d855d540eb73,0x75503c9eca30ec2aeaa0,0x3b30baa818df65ba5661,0x986e81985d540c3fb2dd,0x31dec3748cc2eaa063f,0xbaa81ceee93a0661755,0xe81985d540c7f34dd033,0xfdd3f40cc2eaa063fba6],#[0xa81ccfe97a4661755038,0x985d540c77b4dd2330ba,0x3f48cc2eaa063bfa6e91,0x87f69ba7661755038dfd,0x1540c3ff4dd3b30baa81,0x6c330aa06b5d75e8d866,0xe5fa3619855031eecbf4,0xd772e9d032cc2a818f7,0x30aa04bf9b7e81966154,0xa3659855035ecb8746cb,0xbb2fd1b2cc2a81ae75d3,0xa063df97e8d9661540c7,0x5d855031fccb740cbb0a,0xac3f26c32818fee5ba06,0x3dfb561f9361940e3bae,0x75031fccb740cab0ea05,0x32ac3a818fee5ba06558,0x96e919561d40c77b2dd2,0x35dcaa740cb30ea063bf,0xc3a81a7e5d7a06598750,0x859661d4097f36bd032c,0xaaa742cb30ea06bf150e,0x81a7d5d7a1659875035d,0x661d40c7eb2bd0b2cc3a,0x746cb30ea063f795e859,0xe7553a3659875035eca8,0xd40d3baebd1b2cc3a81a,0xcb30ea063dd95e8d9661,0x43a4659875031efcaf46,0xd37aebd232cc3a81aee5,0xa8b04bbdb5e919661d40,0x55d154583c9f4c2eaba2],#[0x30aba320aa2e1e4faa17,0x875b9965d19055170fa7,0x1545c3adcc232ec82a8b,0xc2b08aa2e1e4f619855d,0x3d976158455170f67320,0x5c31decb748cc2a8b879,0x30aa2e18fe61ba066154,0x4e8d865d170c3fb0dd3b,0x4eec2f46c32e8b86d9d5,0xa2e1977657a3619745c3,0x1865d170cbbf2bd1b0cb,0xc2f48c32e8b86db950e9,0x136f6d7a4619745c34de,0x5d170db72a9d032cba2e,0x40cb2e8b865f995e8196,0xc543a1659745c26fcdaf,0x70db6aa9d0b2cba2e1b7,0xb2e8b869f585e85965d1,0x7a1659745c34fbc2f42c,0x73aa9d1b0cc22e197d65,0x8b863dd95e8d8661170d,0x5d1805531efcaf46c330,0x4cbaae9c02a9e4f61975,0x753d965d5905d154f27b,0x74553a9ec32ebc82e8aa,0x32eaba2a9d4f6d975e41,0xfb0659755d154ba7f60c,0x5369ea874ec32e8aa5d3,0xcba2a9a6f603a7619745,0xe85965d1549b7b61d3b0,0xdbc0742cb2e8aa6f3550,0x2a99ed643a1659745535],#[0x965d154da7ae1d2b2cba,0x874acb2e8aa673d90e95,0xc6f5039761d8655279ed,0x1d54a3fb61cbb0ec32a9,0x8c830eaa63bd96e91906,0x503a1659875531dfcb74,0x4d6eaa1d0b2cc3aa9aed,0x30eaa69f570e859661d5,0xa1659875531fac8742cb,0x7aa1d232cc3aa98fde43,0xaa69bd70e919661d54d6,0x59875525ded8748cb30e,0xd1f2cc3aa9ae7501a3e,0x3dd9068f9661d54d3bae,0x5d35f8a8742c3300ba6,0xb0cc02e9a7d5d7a16198,0x95e858660174c7eb2bd0,0x36baa8742c32eaba63f7,0xbaae997de43a1619755d,0x95865d574da7a81d2b0c,0xed874ac32eaba697d80e,0xe9add543a1619855d26b,0xc1e800c7ef21d0b0cc2a,0x69c73826ecbf1201c626,0xf73e27acf29df3b274ce,0x44286d0aa0f41280cfe9,0x292d22a3f4728cd16a27,0xed3aa6f4d298d2ea574a,0x52a9f532a4d46a875029,0xacf592b0d5eab7562aad,0xf5f2bcd76ae75c2b6d6a,0x52c8d8eb17622c2d82af],#[0xd4da6b47682ced9ab2f6,0xdbeb776e2dadb2b5f6b2,0x6ba7742e6dcab8f712e0,0xd77a2f2de2bbf772ecdd,0x802fedfabef7d2f8deeb,0x30ae12c1f83304e06c07,0x6e2ac4f89310e1ec3786,0x42c7f8f31ce36c678c31,0xcaf95328e4ec9792322e,0xf9b334e66cc79832ee5a,0x1340e7ecf79e33ae72cd,0x4ce96d27a4346e8ad0fa,0xeaed57aa352ea2d3fa73,0x6d87b035eebad6fad358,0xb7b636aed2d9fb3364ec,0xbc376eeadcfb9370eded,0x382f02dffbf37cef6de7,0xef1ae2fc5388f0ee17c2,0x32e5fcb394f26e47c838,0xe8fd13a0f3ee77ce39af,0xfd73acf56ea7d43a6f4a,0xd3b8f6eed7da3b2f62eb,0x1f800705e03bef7aeefd,0xdc6f83f02061171a067c,0x8fc103631c829232723,0x4e57c282429c8b8df02,0xeb17c1cc4f81f048e07f,0xf8272be1412178478618,0x685]]
def g255H8 := limbs80 #[#[0x3c400006451b90004f,0x1708401a60071400f5b9,0xeff1cd854f3a39915000,0x806ad932c00742e9]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x5454140ece61d5454140,0xbce69d5454140ecee1d,0x57454140bcee9d545414,0x40d6e65d7454140f4e5d,0x9d545c140f4e5d5545c1,0x140e6e615745c140b6e6,0xe55745c140e6ee15745c,0x5140b6ee95745c140d6e,0xf615755d140e4f61d755,0x5d154e4f5d574e0154e4,0xce5d95454140d4f5d790,0x454140fce6195454140f,0xfce61d5454140fce6995,0x7454140fce69d5454140,0xf6e65d7454140fce695,0x58754140bf6e8d865414,0x40edee958754140bdee9,0x9d545c140fce655545c1,0x140f6e595745c140f6e6,0x655745c140f6e615745c,0xc140f6e695745c140f6e,0xe659745c140f6e619745,0x5c140f6e699745c140f6,0x5e615755c140f6e69175,0x55c140b7ee9d855c140f,0xbeee91955c140e7ee9d8,0x965c140bf6e8d865c140,0xbeee91965c140bf6e8d,0xd7555140fce681755514,0x40be7e8d8655140f4f61,0x958755140beee8196551,0x140ecfe958755140bcfe],#[0xe819755140beee819755,0xd140f6e681755d140dee,0xfe9d855d140f4f615755,0x5d140e6fe9d855d140b6,0xe7e8d865d140beee8195,0x65d140beee81965d140b,0xadfe958759540bede859,0x855d540dee651905d540,0xe5fe95875d540e5f61d,0xd985d540adfe95985d54,0x409fee81985d540a7fe9,0x81985d5409efe91985d5,0x540cefe91985d540cfee,0x696985d540c7fe9d985d,0xd540a7f69e985d540adf,0xe683985d5408ff6a6985,0x615409ef693985d5409f,0xdfe958761540af7e8d86,0x661540c7fe5d8761540a,0xafee819661540c7fe5d7,0x9761540af7e8d9661540,0xcf761f9361940afee81,0x19561d40afee819561d4,0x40afee819661d40aefe9,0x8d9661d40afde859661d,0xd60aefe919661d40af7e,0x69d54e0d60ee75d154e0,0xd60af7e9d54e0d60af7,0x7e9574e0d60e775d574e,0x55160f4f5d57455160af,0xffe9597e11609fee8197,0x55170f6e5d190551708],#[0xf4f6157455170d7e65d9,0x9755170ecf6158455170,0xaefe919855170d7ee81,0xd98551709fee81985517,0x70aef692985517097fe9,0x9f98551709fe68398551,0x170b6fe91855d17097f6,0xe8d865d170b7ee81955d,0xd170b6fe91865d170b77,0xde85965d170b7ee81965,0x60154af7e8d8661170b7,0x6fe5d7460154f4f5d574,0x5d154c7fe5d8760154d,0xbcfe95905d154f4f5d59,0x755d154f4f619755d154,0x4b6fe9d865d154f4f659,0x5965d154bede85965d15,0x54c7fe5d8761954bcfe9,0x859661d54aefe919061d,0xd54aefe919661d54afde,0xe9d95e0164af768f9661,0x15648ffe9597e01648ff,0xfe8195e1d648ffe8197e,0x60174d5fe5575601748f,0x7de85865d574afde8586,0x661574b5fe95865d574b,0x8ffe9594e0176afde858,0x95e11768ffe9590e1176,0xfee61974541408ffe81,0x97454140fee659745414,0x40fee6a57454140fee69,0x1d8654140bfeea176541],#[0x140dfe65d8654140efe6,0x6998754140dfee5d8654,0xc140efee998754140efe,0xe659545c140fee619545,0x5c140fee699545c140fe,0xfeea1655c140fee6a554,0x55c140bfeea5655c140b,0xf7e659755c140f7e6197,0x755c140f7e699755c140,0xefe619855c140f7e6a1,0x9855c140efe659855c14,0x40efee99855c140efe69,0x59955c140efe65b855c1,0x140dfe61b955c140dfe6,0x6197555140bfee95965c,0x5140fcf6597555140fcf,0xf6a17555140fcf699755,0x55140befea17655140fc,0xef61d8655140befea576,0x655140def65d8655140e,0xeef61d9655140defe5d8,0x9655140eefe1d9655140,0xbefe9d9655140def65d,0x98755140eef699875514,0x40def6999755140eefe9,0xa1655d140defe9997551,0x140befea5655d140befe,0x659755d140f6f619755d,0xd140f6f699755d140f6f,0xf619855d140f6f6a1755,0x5d140eef659855d140ee,0xefe99855d140eef69985],#[0x55d140eef65b855d140e,0xdef61b955d140def6599,0x8759540befe95965d140,0xcffe618759540bdfe95,0x58759540edfe95875954,0x409ff6a39759540cffaa,0x15905d5409ff69f98595,0x540dfe659905d540fde6,0x615945d540f7e61d905d,0xd540def659945d540fcf,0xf619855d540f6f61d945,0x5d540e7f619875d540ed,0x7f699875d540e7f65987,0x85d540e7fe99875d540e,0xcff659985d540edfe959,0x985d540e7fe9d985d540,0xdefe91985d540dfee81,0x9985d540cff619985d54,0x40cffe99985d540cff69,0x1b985d540cff65a985d5,0x540d7fe5d7661540cff6,0xe5d8661540affea17661,0x1540e7fe5d7661540cff,0xf65d9661540affea5766,0x61540cffe5d9661540cf,0xff65f9661540affe9d96,0x761540aff69f9661540c,0xeefe919761540efee819,0x97e1540cff69b9761540,0x9ff6a3955d940cff699,0x793619409ff697985d94,0x40affe958761940df75d],#[0x919561d40efee819561d,0xd40cff6599561d40eefe,0xe9d9561d40cffe599561,0x1d40cff65b9561d40e7f,0xfe959661d40cff69b956,0xe1d40aff6979661d40af,0xf769d54e0d60cff69995,0x455160ef769574e0d60e,0xeefaa17455160eefa617,0x9755160aff6a78755160,0xcffa619755160bfee81,0x19755160dfee81975516,0x60aff69e9855160cffaa,0xa7855d160e7fa61755d1,0x160bfee81955d160aff6,0x696985d160cffa61955d,0x5170fee6119055170aff,0xf6197455170dfe659905,0x55170f6f6597455170f6,0x6f6617455170f6f69974,0x455170eef6198455170f,0xd7f6599755170f6f65d8,0x9755170d7f6199755170,0xd7fe999755170d7f699,0x99855170eefe91985517,0x70dfee819855170cff65,0x9d9855170cff61998551,0x170cff65a9855170d7fe,0xe617559170cff61b9855,0x9170d7faa57559170d7f,0xfe618559170befe91855,0x591709ff6a39559170cf],#[0x7f619855d1709ff69798,0x55d170e7f65b855d170e,0xd7f61b955d170d7f6599,0x965d170b7fe95865d170,0xcff61b9561170b7fe95,0x995e1170affe95866117,0x70df75539361970cff69,0x1974601549ff69794619,0x154d7fe5d7660154eef6,0xe5d8660154affea17660,0x154affe9d8660154cff,0xf69997e0154eef69974e,0x5d154def659905d154cf,0xefe81865d154def61b90,0x5d954befe81965d154b,0x9ff683985d9549ff6a39,0x9061954cff61f9061954,0x4affe8187619549ff69f,0x19061d549ff683976195,0x54cff6599061d54eefe9,0x9d9061d54cffe599061d,0xd54cff65b9061d54e7fe,0xe819661d54cff69b9061,0x1d54aff6839661d54aff,0xf6a575e0164cff69990e,0x5d564befe91905d564cf,0xff682985d564cffa6190,0x560174e7f6197560174a,0xaffe958660174cff61b9,0x95e0174e7f69975e0174,0x4b7fe81865d574cff699,0x18661574cff61b906157],#[0x74cff69990e1574affe8,0x4391619749ff69790619,0x9ff6839561974dfd5,0x90084819404f80ca01d0,0x8128844c0fd83820c102,0x1cc86b419505f415d84f,0x61891c22c88481f78774,0x78b202ad8a4c28289be2,0x8d883478cdc31c8c082e,0xfa03d50f123b18e5c37c,0x9a45390e441e90383fd8,0xc4c092c049d123247991,0x54194b051914224f5936,0xc796dc59795e05629548,0x4989061398025ed976a5,0x9a4e68099a2655991463,0xc527019bb06d69b046a6,0x6a78a1ddc7641d1c7341,0x281f20087e79f5c7b51e,0x8a5225287f217e84a20d,0x3ca4a691923e68df22fe,0xc266498625d6962a53e9,0x28189f5a7949d4a6fc9a,0xa4ea80a998a50a8f6a23,0x3eafcabb0adbab22aae2,0xcb6ead78b4dacf4b22ac,0xbd92f22bb32e80b8fadf,0x3230c2c20303ebff2fa6,0xb30e6c3830dac3530cec,0x310ac4130fec3e30f2c3,0x12ec4a3122c473116c44,0x52c533146c50313ac4d3],#[0x6c5c316ac59315ec5631,0xc65318ec623182c5f317,0x6e31b2c6b31a6c68319a,0x731d6c7431cac7131bec,0x31fac7d31eec7a31e2c7,0x21ec863212c833206c80,0x42c8f3236c8c322ac893,0x6c98325ac95324ec9232,0xca1327ec9e3272c9b326,0xaa32a2ca73296ca4328a,0x332c6cb032bacad32aec,0x32eacb932decb632d2cb,0x30ecc23302cbf32f6cbc,0x32ccb3326cc8331acc53,0x6cd4334acd1333ecce33,0xcdd336ecda3362cd7335,0xe63392ce33386ce0337a,0xf33b6cec33aace9339ec,0x33dacf533cecf233c2ce,0x3fecfe33f2cfb33e6cf8,0x22d073416d04340ad013,0x6d10343ad0d342ed0a34,0xd19345ed163452d13344,0x223482d1f3476d1c346a,0xb34a6d28349ad25348ed,0x34cad3134bed2e34b2d2,0x4eed3a34e2d3734d6d34,0x12d433506d4034fad3d3,0x6d4c352ad49351ed4635,0xd55354ed523542d4f353,0x5e3572d5b3566d58355a,0x2f596d64358ad61357ed],#[0x8340cf19c7917c1f03c2,0x7033c1f03c2220e24911,0x3f07c0f08b83a0df19c,0x8803a0d24853833c671f,0x20d833c671c0ef07c0f0,0x490df1853833c1f03c23,0xf07c0f08c0340ca13032,0x460c43453c0fc6d1684,0xef1853833c1f03c22c92,0xc1f03c2300ea13034448,0x118308e14e84f1ac5c0f,0x3c691dc5f07c0f08b049,0x7c0f08884a112390d03,0xf03c22212847c67140cf,0xf08884a0cf19c5047c1,0xc23211833c671412f07c,0xc24704f1b83917c1f03,0xe47f07c0f08c14c12839,0x4538480e4308dc13c6e0,0x4811f1b4303bc1f03c22,0xf1ac304bc1f03c224932,0x3f07c0f09c831134380d,0x60380d0320571a8471f0,0x9c829c2917c1f01c8078,0xdc61408fc0fc1f03c203,0x19c7f0645f03c2030a71,0xc0fc0f080e29c824911f,0x2248a7205324bc671fc1,0x34360cf180ec0fc1f03c,0xc604684f07c0f090d281,0xbc1f020c070504c92833,0x3611b1fc1f0145f087b1],#[0x12a11833c1517c0f0864,0xe833c603684f07c0f091,0x12c0fc1f03c2238a04c8,0x7c0f09c830134460cf18,0x8110320771b0371684f0,0x19c5f0647f03c2030a04,0xa13c0f081129c82390df,0x2048a72053437c6717c1,0x814c8ef19c5f0703f03c,0xa70a47f07c07201e19c,0x51915284f07c0f081172,0xfc1f0bc0049c829c671,0xf03c214ca719c51508fc,0xc2a110390cf1812c0fc1,0x103bc603647f07c0f090,0x84f0511f02c5f08714e1,0xe0d833c151fc0f086837,0x210c836c5f07c0613c21,0xc44c8b1b47327c1f020c,0x2418c8b1bc0f061106c6,0x3c214ca060c8433c1f00,0x8118390cf180dc13c1f0,0x3bc604a45f07c0f090c2,0x327c1f0345830714c118,0x8433c1f03c20807c3ac6,0x12b1fc1f0145f08703cc,0xe12833c1517c0f08643a,0x190c84ac7f07c060fc21,0x214ca84a0ef0583f03c2,0x20350cf1811c13c1f03c,0xc603a47f07c0f090c2a1,0x7c044ac5f08714e12037],#[0x33c151fc0f08683b83f0,0x83ac5f07c060fc21e0e8,0x8b1b47327c1f020c210c,0xf3210cf07c20946c48c,0x208c3383f04caf0a1218,0x32c7e1383d1bc1f03c2d,0x4f4761345a0fc1f03c2,0x5f07c0f08c44a1143a0d,0x24460e8340ce1147e0e4,0xc784a11f0545f03c2191,0x4c751784e0fc1f03c214,0x230751f84e0fc1f03c21,0x2230760f47d17c1f03c2,0xc0f08661347d17c1f03c,0xfc1f03c21b47d1784f07,0x1383f07c0f086d1f45e0,0xe1383517c1f03c21b45e,0x951f84e0fc1d17c0f087,0x230880801b45f07c0f08,0xf4560fc1e13c0f087d1c,0x1f45613c1e0fc0f087d1,0xd1f453260cb1bc1f00ad,0x8f07c0b1fc2230ec340b,0xc1f0345f0880750e4374,0x7c0f0ac8202124891b23,0x3c20807d1784e0ec6f0,0x327c1f00c4350c323c1f,0xc370c70bc7d1784e0ec6,0xd4350cb1fc1f03c21f0e,0xc59224943346f07c02c1,0x7c1f03c21d926440b71d,0x17c1f03c21c214450cb1],#[0x323c1f082518214490cb,0x5e1383f04caf08a4450c,0xc6f07c03712c470cd1fc,0xc70b47f1784e0cc8326,0x90c323c1f00241b12c47,0x18c4e0fc071fc1b14a44,0xe1b83f03c12cd233b08e,0xe20d3348ce02c09b16c4,0x8025c702f86e0fc0f04c,0xd3348c7e0fc0f05c5b10,0xc09e19c5e0fc0f04d220,0x1644e0fc1f03c2e20c02,0xf0b8820130480e11f865,0x2b1c6b1f45d1386f07c0,0xc0f084e2bc105bc0e0fc,0x8c44891037c603187f07,0xed1587d1283f07c0f0,0x7c0f0891291344a0d83,0xf08c8484e037c604e44f,0x83011e1d45e0e44f07c0,0x2f0583f03c219138490d,0x87e0fc1f03c2138784e1,0xf45d13c1f03c22447513,0x1f45d13c1f03c2244760,0xe1d44e0fc1d17c0f0876,0xc21f45d1183f07c0f086,0x3c21d87d1744e0fc1f03,0x17c21d1284ec5f07c051,0xf06112213d13c1447c0b,0x906c48c8b18c9f0344,0xc1f0825181432112f07c,0xfc132bc28486050c8447],#[0x24c8846c6f03c12f11e0,0xf080e2b12c300bd13453,0xd210d833c6d0fc131fc0,0x883385f07c024b43f087,0x2324c92b23c1f0343f08,0x3c6b0fc1617c0f081228,0x7c043ac3f087b205183,0xf07c0f080e720a83347f,0x49c829c670c9043e47,0x7719c31510fa17c1f0bc,0x8603cc844bc1f03c2080,0x8251b0ee17c132bc284,0xf03c2080703cc843bc1f,0x3f07c0f08724c92523c1,0xc3f07c2328a08d1243ac,0x8261b13c4b0ed1f85e13,0x3c108c64490e323c0f0,0xf07c0057c21bc370ac6f,0x1057c0e13c2b1c6b1784,0x86f0417f0384f0ac71bc,0xfc21ec5e13c1f001af0,0xf08ca2211e13c1f0093d,0x28486c470cd0f4584bc1,0xc1f08251b13d17c132bc,0xe12f07c23288050c844f,0x387f0ac41b13c3b45d0,0x5bc0e1fc2b0c6f0415f,0xf0416f0387f0ac51bc1]]
def g255H9 := limbs80 #[#[0x800020580c200a1c2000,0x18000c1001040450020,0x2c40900840c50861d278,0x126c3b8966a1180d3200,0xbebc9800d00825033820,0x14d4b4e1eac000402c97,0x87654c4b796000148702,0x4871114d75ce10183014,0x4e0004043cf40002,0xc5800a4c1c300000,0x31a8000b350000000476,0xc418002134386c51000,0xf589e27795320e800000,0x710a15a548474d6408,0x8520000001c2e0,0x647c5d8000001c6e86f0,0x98ff1a5ccd257c229562,0x9841665db738b3c7ced2,0x4428001ead084c31981,0xf2c32e0db0b915542700,0x59e0d8c7da2200009460,0x7206876b12180008697,0x2d504ca132688000,0xc62a89423990093b5645,0x1f5f4230c23ed7d6240c,0xd800123c000041a4daa8,0xc2f800000141695d22,0xdf4d22eb223100004620,0x13305abec5a542,0x690000000043fd387d1e,0x2a6d48de38f36,0x4eb40000000007a7c00],#[0x1e5bbd103750cc00000,0x624edca80e80f0002d,0x6e3c15125dccb80d0,0xb58095c0014d354c0000,0x9b7e26f0004820001888,0xb35180021528e786cddd,0x96924cfb671a8000122,0xa5561000000085e650df,0x54a1aa7500000000012,0xa72e4721ec8c6000c325,0x52bb4aa65a0000000000,0x8e538240b8004bcdfd87,0xc58b3a16000000380502,0x6e000000000000de09a3,0x38b940a00000039,0x3ba2391059f4001e710,0xa5074f6226,0x4124a00964fb90696560,0x230cbb99aa7ea770c770,0xd4c77c8b00008a00ba4e,0x953020003532237b1800,0x4ce00040d0000001c,0x69355b5e24b178,0x800190400015a30b7d7e,0xe000e4eda7299400056d,0x1342c99a1c7258361d8,0x6c61a3f30a683e00000,0x24800000190cb46d03eb,0xa34703d30d4240005,0xd5c52175566b90007928,0xa84]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0xb72e8b8281f395454140,0xdcba2a0a074f5d574553,0xf70ea8281bf98754140f,0xcbaae0a07ee551705037,0x70ab8281bf9855c140ef,0xbaaa8a05fee55705037f,0xeaa281bbd8755140f9e,0xbaa8a05ef65d5450377f,0xaba281dbd755d140bdfc,0xae8a06efe157450377b0,0xbaa819fd875d540bdfca,0xaa04ffe5d855027fb30,0x3a817df93619409fecbf,0x6b04ff657875027ff2ac,0x2c1bdd74e0d60deeaa70,0xb04ff65f845827fb2bc2,0xe1dbd74551709feca70e,0x867fe15745c2bfb2eaa2,0x13fd95e1170affcaae8b,0x6ef5d380552fbf26c32e,0x7bf905d1549fecbf00aa,0xff643875527ff20c3aa9,0xfd97e01649fecaf00b24,0xf65f855927fb21c2ac93,0xd95e1d649fec870eb24f,0x657805d33faebc02e93f,0x91619749fec870aba4ff,0x43845da7fb29c02ed7f7,0x6541409fecaf08bb4ff6,0xd50503ff30ca8281ff97,0x5c140ffcb2ae0a07fe61,0x70503ff32ab8281ff985],#[0x5140ffccb2e0a07fe619,0x4503f7b0caa281fbd765,0x140fdec3aa8a07ef6595,0x503f7acaba281fbd9755,0x40fdecaae8a07ef61574,0x3f7b2cba281fbd865d1,0xdffc3acaa06ff61d655,0x2fff30b2a817ff975954,0xfdeca2eaa07fe6417550,0xbfb0ebaa81f7d855d540,0xfecc2eaa06ff66175503,0xff30baa81bfe985d540b,0xec3b0aa06ff61985502f,0xaecc2a817ff9761540df,0xcb30aa06ff659855037f,0x2ec2a81bfd9761540dff,0xaaeca06ff5db855037ff,0xec32817ff985d940bffc,0xb0ea05ffe55875037fb0,0xc3a81bff9561d40dfeca,0xa8b06ffe59875037fb2c,0xa2c1bff8755160fdeba2,0x8b05ffe5d54582ffb2ea,0x2c1dfd755d160dff4c2a,0xb05ffe55745837ff0aba,0xe1ff99055170dff4c2e8,0x877f65d545c3f7b08aa2,0x17fd9855170dfecc2a8b,0x5ffe61545c37fd30aa2e,0xbff8559170efebaac8b8,0xffe61645c2fff2ab22e1,0xfd955d170efec2ae8b85],#[0xf659745c3bfb0cba2e1d,0xf9561170dfec2b08b877,0xe51865c37fb0cc22e17f,0x8660154fdeba300aa5ff,0x5d805537fb0ec02a9bfd,0x5d154dfebb700aa5ffe,0x974553f7b0cba2a9fbd9,0x5d954bffc82ecaa7ef65,0x86552fff20c32a97ff98,0x1d54bffcbb0caa6ff61d,0x75537fb20c3aa97ff906,0xd54dfecb30eaa6ffe418,0x5937faebc02c9bff9661,0x74dff4c2eab25ffe4175,0xd37fb0ac02e9dfd75601,0x4dfec3300ba5ffe55805,0x2fff20c2ae9dfd865d57,0xbffc830cba6ff619855d,0xffb0eb2a817ff9561974,0xfecbaa8b07ff5d985503,0xfb0ab22e1ffd955d160f,0xec82eab27ff5d980553f,0xb2cbaa81ffd865d540ff,0xcb30aa07ff66175503ff,0x2ac3a81ffd9761540ffe,0x32a8b87ff65987503ffb,0xaa2e1ffd9655170ffec,0x308b87ff655845c3ffb3,0xc02a9ffd9660154ffecb,0xeaa7ff64187553ffb2e,0x2e9ffd9560174ffecb3,0xaba7ff641855d3ffb2cc],#[0x4800c00180000ffecb30,0x5c2ee0a5c23707a41800,0xc50a12f04530fcc3a50d,0x7261b6068a18845c115c,0x4b23ac89d21187e61e3c,0x22b20a7a29409f926889,0x32b8c573024bbb2d48af,0xa74e463798d983504cf3,0x14fc03e58f513c9cee23,0x118b451910142a905340,0x3954cd52c349d5215474,0xde5641530531d479501d,0xf5ff578b5cad6b9591d5,0x6985a0166cd92f631986,0x35dc656ff1b936ca9ac1,0xededb78f1de5765dd497,0xe15183c607680c5fbf7c,0x3918c5a2b6897e1ff867,0xe3957e50892a24638fc6,0x49e3673f9ba268898c65,0xa7c6988a45a8ada1367e,0xfa6b92accaae4aa12a3f,0x32e35b67ed36b336c5ba,0x70bdc07afb5bd0eef5ba,0x30fcabf246c77716bc47,0x73d3e3498d0e33cfcdbf,0x8dce36eada2b645d74f5,0xe76f972e4278a9e02b79,0xf73b97ed4bafbea93a3b,0x13d3ef3e7cb4f1e3c2ae,0x3d62f573d56f543d4af5,0xd86f603d7af5d3d6ef5a],#[0xaaf693d9ef663d92f633,0xe311419c1e0708af6c3d,0x419c1e0708a0703607c7,0x1e0708a0204b8dc58184,0x8a0984a09c6e191c1dc,0x6f19250d0631e8bc1e07,0x19c6c231f83c0e1514b0,0x63f0781c206101186a48,0x28ec5e0f0384571a1b45,0x4e0f0384483b8d114703,0x385472f8c53860458b8,0x44441a8e0671b08c5e0f,0x91c688d1d8bc1e070818,0x4571a198462f0781c208,0x38c53860398f83e0f038,0xce360d8fc1e070a8a583,0x1f83c0e1030809439220,0xc7e0f0385832f8d0ea2b,0x7081c404a18530771a8a,0x3c0e115c68660d8fc1e0,0x3960ce314e181262e0f8,0xe468338d8362f0781c2a,0x4a8ec5e0f03840c22240,0xcc1b1783c0e10488e34,0x71b0983e0f0385452f8d,0x983e0f0384494c241146,0x3f03841d281147e35170,0x840c241145c1e138dc16,0x8610210431f8d45e0f03,0x842551b07c7e2f07804b,0x8228f84c1f1b82c5e070,0xa0862f1a8fc1e0708184],#[0x371d8ac4c1f07810b243,0x8ac76260f83c08592cec,0x4162383c00b07c46961b,0xd0784c30158f83e0f038,0x2545c1f0781c22b83c00,0xe0f0385832c1dc648938,0x822404d22122771a8b44,0x20911c6895118bc1e070,0x8224f1a238362f0781c,0x111c440862f1a89c1e07,0x7081c451b8bc4e0f0097,0x1c20713c64931e87c1e0,0x10488118218fc6a1f078,0x84232b8d0ec2b0f83c0e,0x241147c26178dc161f03,0x1d0430f8d47e0f03840e,0x51c0ec507f0781c20a8e,0x5c3c20158e0fe0f03841,0xc707f0781c20b8fc1e00,0xe10687e0f00341e1006,0x781c20910036283f83c,0xc1e0708244f1926c5a1f,0xf03841224460862f1a87,0x44a890e210430f8d45e0,0xf0384151f09c5e1f078,0x29c1e07082c38158814e,0x6285383c0e1058702b0c,0x18f45e0f038584641403,0x2a2f0780c80f10c686c3,0x1f83c0e15141860661ac,0x84641421868459092e33,0x18c688c318b47e0f0385],#[0x6423b8cc5e0f03854706,0x783c0e1610226076220d,0x80f1022860359053e331,0x2022586622c2a3f0780c,0xcc318cc52a7078184e13,0x18c7a2f0781c2c1b20a0,0x6151783c06407886343a,0x383c0c1f09900e2c1f0e,0xe151418603e18c76314,0x821870499091e331f83c,0x414f8cc7e0f038583071,0x83c0e160d90508e18126,0xe151c18631a250c62d1f,0x1d89039908de331783c0,0x14f8cc5e0f0385830918,0xfc1e03203c488e180e64,0x1f0190122e240f6330a8,0x90703e18c66295383c2c,0x4306914651a8bc1e070a,0xc0e152118408524c7c20,0xf0781c228141063d1783,0x45046140c2406b08c7c1,0x996160ae0c91c7e0f038,0xce3514220de0f0385842,0x481dc1e070b06532c448,0xc0e151d18588d19c6a28,0xa30b0e94f8d830703783,0x29f1b061208f0781c2a2,0x38d84c1f0781c2299821,0x1e070918608c45454622,0x210ee0ca648e351e8bc,0x42228bc6e0f038453461],#[0x1248c1f1b83c0e1230a6,0x874368ac2a3f0780c80f,0x28cc60631f83c0e15151,0x843a9248c3a1b83a432,0x18306f1b83c0e131c3a5,0x63198fc1e07099070389,0x8460761d45c2053070d8,0x138ec6c187c3dc1e0323,0xc76370383c20e8f0ea2e,0xe1307c663f0781c23411,0x4c70e950e86c303ac8a2,0x6100e0683191c6e0f038,0xa850528ac7e0f0384c88,0x309017c231707c1e0708,0x832471783c0e11511850,0xd098bc1e05203c48582b,0xdc1e07098a2129249163,0x2f0781c2342448c18478,0x288c3042c8a3e1307c66,0x3191c6e0f0384c510951,0x830f70781c2641812088,0x708423c4a23476371709,0x1c2a2e20a047158dc1e0,0x2649c31489d8363f078,0x107039101aa2b1e89c1e,0x6288522761b07c1e070b,0xc0e16209c408ca6c7a28,0xf07804e4c921863e0f83,0x1c2a2620a0b85a8888e3,0x2649c314ca58362f078,0xa440491017a3b1689c1e,0x4c921862e0f83c0e1620],#[0x8b0d05a8888e2f078052,0xf1a880d067078187e113,0x40ce0f03854548941d48,0xf0307c2271621277182,0x844e304691e35102612e,0x7688914471b0f83e0f03,0xc6a2d1383c0e1244b118,0xf03844e4890221093891,0x3c0e12449c3a2289c6e0,0x1f0781c262d20a2471b8,0x81c2a42448a324d2344c,0xe0f03844f281ec5a2707,0x89e912422480be1d8b83,0x408981a0a9238bc1e070,0x413642378cc5e0f03854,0x331783c0e160c24608a2,0x84c80896238884d904ee,0x2c29126331533c1e0513,0xc66293f83c2c1f019012,0x458bc1e070a88805222,0x10a4e248d86521914663,0x19c6e0f0384c5109222,0x608d1383c0e1320b0912,0x780c4121112863168ac,0xc0e131c1c60609014e2f,0x161d49032910de350f83,0x63d1d8c0ea1f0781c264,0x81cc7e0f038543461b0c,0xa4d250d8661290c8a331,0x9c6e0f0384c70e94230e,0xf0384c887100d246101,0x83c0e161424605286c7e],#[0x71621870319051e330f,0xf6330d21c1e051f84c8,0x95383c2c2f0190122e24,0x9c1e0708a8503e1cc661,0x11511c50389015c2b0f0,0x40505c2d842470f83c0e,0x40918407f1f83c061f08,0xc36383a8dc1e070a9058,0xf0780c7e1080a49a4a86,0x1c26188ca08123080fe1,0x708d099230812e37078,0xe11b228f85c271987c1e,0x1b83c0e130c46544e250,0xc1e170190604c240e647,0x8f138943a8f85c270d8d,0x50f2811c36370781c211,0x27080ab1e87c162f038,0xa07b0f09c1e070b10532,0x5e8a88e1f0781c24794c,0xc6a1f0781c262848c0d0,0xf03854344429308d2219,0x8661290c8a331824c5e0,0x384c510942310a4e228e,0x6416112461019c6e0f0,0x30c62d158c12a1f0785c,0x1a3f83c2a2f0190122e2,0x83c0e130c46505226c66,0xe170190584c91840771b,0x4989c3987436304a8bc1,0x850918407f1783c26189,0x848c203f87c1e13144a4,0x3a4a8d8348a30a1481c2],#[0xe2088731b070d8615190,0x38820a786a2608a44e4c,0x7d20629e1a8982271493,0x190e2a320749d191a912,0xa2934a68fc40f0d63612,0xa386]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x10f0b84627568001201,0x38000001c00683302c00,0x340206000f40a0200030,0x597c3e0a268c86408008,0x40086c24180001c00420,0x2021e894020302800027,0x95c9a10810420000b980,0x81800210180c060c0000,0x1f8a8402b034fc260232,0x1b000a844027489900cf,0x6ad2d81420029581400,0x8b443b0d6e80609aeb00,0x1e4faa6d89d9,0xe86aa8d108a09826b80,0xc2f7d7f218a679850800,0x29189a4a0eaa441948cc,0x688160003a048a5d94a6,0xd666e63691b8547a8e61,0x144122210b495b87b74f,0x2ee48343984980000001,0x1a7f82a200e000188c30,0x930900e2453215000496,0x47d28485df8f1a87c0b4,0xe18652cb1e010d70ee0,0xb97ee17196d72a001bc0,0x870a0488ed088aa3760a,0xf504d54f4000518ba53c,0x15539a4ffa730bbc2c71,0x263e869f778258a09e88,0x8e0001ba2111ce776e5e,0x65cf2a1dac18b1e6d5e4,0x5a53866317c104540a63],#[0x241436c1eba3d929253f,0x688a3819ea63895a318,0x667ca0b2baa394040d40,0x21470b6401120aa4ef90,0x64daa9212c9fcb2648a1,0xaa9e4f0b18fc864085e4,0x2aafa1201a8872da0d21,0x9656131a25c2340abb92,0x8348d182dd3a20586094,0xeb1482b20437cc756250,0x20437c657930d5aa8c,0xad2117c9258ac284f072,0x5e9fbe78c1e684661cd6,0x3a2ed8101ab43c853ae5,0x139e4459ac0438000000,0xabb6d90a86560889387a,0x6000155649559f1ca99a,0xc2e41b8a69641f47a408,0x18ca43828988561f897a,0x2aa10e8ab0758a77c4e7,0x6d6de97c847d363447a3,0x146350700b03e0001231,0xd1671f2894a028660000,0x1c6df1bca6ed27ec9e09,0x4a681de24f3a51056800,0xc800161b0da7c2f881f,0x491d89371962866a1246,0xd58600000616ac48fe03,0xa66a30b1b40106269a14,0xbec0f442a14aba4d444d,0xd54a54d208eb25cc4bc1,0x9039271229995f683c22],#[0x3b6d58e9ef2265852845,0x997d00a1a0815326f7,0x4c6c44ac823a7e712d66,0x4cc070aa1c891c40d919,0xd784891c4000308f6884,0x75e7c2794031d5a5560,0xc9a88578321166000197,0x7be80c4adce50ca44218,0x2728a15489db63d6933a,0x29b268ca952000017585,0x919d401e3e851fa99,0xd385a845d6050000c610,0x1c9680000001909c7011,0x2570000c1e404fc4a000,0x21ed03518eb02770de,0xbc28747d994c2678ce40,0xa9e0007042681a217e1,0x179892d0ae49870d1b49,0xc98daa193fc168a259,0x655cd27d408598822280,0xa6c2828315e03e04141a,0xab78e8e241e37038107d,0x6a74480ea73f9649732,0x80001680810e7398e768,0x20300007a44e24,0xd7227f8c124da9c898b0,0xe00000014a538dd08241,0x40edaee3900e3668d96,0x407ab8c8f4a3f35d0983,0x1c0eb037607219d0]]
def g255D11 := limbs80 #[#[0x5c140ff950502f7e0d60,0x503ef5d140fbd54503fe,0xbfd87502ffe1540bfd85,0xe1d60bff84582ffe1d40,0x552ffe1170dfd745c2ff,0xbfd87553ef5d154bff80,0xe1564bff80592ffe1d54,0x5d2ffe0174bff87592ff,0xbff805daffe1574dfd75,0x5d540ffd65502ffe1176,0x503ff5d940ffd85503ff,0xffd54583ff61d40ffd86,0x59170ffd545c3ff5d160,0x553ff61970ffd845c3ff,0xffd86553ff5d954ffd80,0x60174ffd75593ff61d54,0x3ff61974ffd855d3ff,0xa87905f84c0388250118,0xf98e80d48c50b58a408,0x7e16c95b14993811e90b,0xe9f11d79c61b49a318f9,0x2a5a8c272a59241a2820,0x5233ab21307af22daac3,0xc1c00b23b639cb8336bb,0x707030a109c786c5c483,0x7c1c0c2842434331f191,0x1707030a0c9110cc6c54,0x47c1c0c2832438331f19,0x6120f070308c120cc6c5,0xc20c20383430231f191,0xf070308c08c7c645c1c,0xc20484430231b151e12],#[0x70064708c6c547c1c0c2,0x447c1c0191c231f15130,0x1b160f07030910908c5c,0xc6c544c1c0c211204847,0x4231f190f07030838808,0xc120ec6c347c1c0c2852,0x38231b0d1e1613070308,0xc6c347c1c0c20e204c48,0x231f150f0703083c808,0x3c808c7c345c1c0c20f2,0xc2122023170d1f070308,0x7030a10908c6c543c1c0,0x1c0c212204c4b1b0d170,0xf07030850808c6c345c,0xc344c1c2c01420231711,0xe120d1707030920c08c5,0x5c183c0c2384230311b1,0xc0c538848138cc647844,0x3835231f191707030830,0x848347c1c0c248320c74,0x523070078b148c0c46c5,0xc20c30643e0d0b1d1b1,0xc8321121148c6c547c1c,0x3a1b1d15120f07030a20,0x474483c1c0c288306538,0xf05130308e19521286c5,0xc3a462120453b1a1d160,0xf46c5878344c1c0c2482,0x231b151307030844b910,0xc4c1c0c2481128844831,0x90f07030838c191446c5,0xc2483210743431231f1],#[0xb148e0e46c3858447c1c,0x3e131d1b0f0703092038,0x48c6c347c1c0c20e3040,0x61307030a20b84231312,0x1c0c212314c3e1b0d1d1,0x48c8421110c48c6c543c,0x8c4c39231b0d17070308,0x46c5c3c1c2c048122e10,0x140f84]]
def g255H11 := limbs80 #[#[0x2818d0200003080c39b,0x818e121411b0c002060,0xc90c0800f0c18d8a00,0x18030047b502d4283006,0x1061888f0e009042200,0x8fb5a80a98360001e200,0x17a39e2f00000000016,0xe58d4e800000183f458d,0xad280000000000000000,0x2a600020b2000781,0x3a87422000000000000,0x2876220e2200a779800,0xc4800000000061bd2331,0x80800088f800000033ff,0x93e800000170771c0ae3,0xbd58f3d7bc09310ee13a,0x665d1a0a8a3c1dc018ab,0x6412fd44c4964d50abf9,0x712898b4f323b0003a,0x87c0c0000000292d1120,0x675c48000242c00043e3,0x80036080005238291adb,0x403311a40b0000009a57,0x210c6495706a3d0002a4,0x38000000460868449361,0x52b5de0ba415313e01d9,0xcade8e0000000000000e,0x3915cf122b8458003,0xaa28a0248800004b8eb4,0xfc0a56a6ce925e0afc53,0xb98dd400e1c969528190,0x7f79cfa8e84666561ed8],#[0xc0c3361e8380607528c,0x339584d56d30b0007,0x8003efa000f2180014d8,0x38b31c199ed089410a0b,0x962000a909600069a000,0x5750c00042c000000011,0x2fb8a0000000816ee72d,0x825e0ab45616d6f6000b,0xa9915a000000243b,0xcf4f320000593f2a5a0d,0xc000000000183c000320,0xc440c83e682e2ec852e1,0x676358000536000a059d,0x90b9500005280000154b,0xb3b00069a80000000003,0x3a56881857207eae593c,0x7467430ea69931b26c50,0x1000050a84df2480018c,0xfd45137e96800147155,0x121a88c29f00000035,0x84c20c00071b78fdc200,0xf3300036620005539120,0xb81000030c7ac886aa69,0x2b48da36d6e000d0d58e,0x2ce64a9442399244382,0xaa07000000000000000,0x8d88a4000ea7e939e237,0x7]]
def g255D12 := limbs80 #[#[0x4ffaa9ff5c3feb07fd40,0x4893001ff5dbfeba7fd6,0xa101c18108add5ba52dd,0x880e0c08420910323c68,0x68b1038383021151c345,0x478d0c2848302114208c,0x3868b0c2418108412207,0x44128d1618709060422a,0x68b1218783021082]]
def g255H12 := limbs80 #[#[0x240088033f144312007,0xe7048481668ea3544226,0xc490f52022cb0b3374f9,0x23e1400040660400659c,0x1b1800440b3800199c84,0x5aa77291244ad1c32203,0x9f1a12c02ba5927a1cc,0xe52e28007dc70191c909,0xfc74ad00000026144716,0x124bc2a00121bd3000f3,0x9b1c0e8c0062b0010]]
def g255D13 (j : Nat) := if j=0 then 0x7185103040088ff else 0
def g255H13 := limbs80 #[#[0x42b49600009ce0b8,0xc5d3fd008100]]
def g255L : Nat → Packing
  | 7 => (23,6,6,0,0,8,0,g255D7)
  | 8 => (232,5,6,0,0,11,0,g255D8)
  | 9 => (349,4,6,0,0,14,0,g255D9)
  | 10 => (188,3,6,0,0,14,0,g255D10)
  | 11 => (45,2,6,0,0,12,0,g255D11)
  | 12 => (7,1,6,0,0,9,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 5 31 5 9 5 0 g255H8
  | 9 => lookupWord 64 353 6 13 8 1 g255H9
  | 10 => lookupWord 107 467 9 14 9 1 g255H10
  | 11 => lookupWord 60 331 7 13 8 1 g255H11
  | 12 => lookupWord 15 71 6 11 6 1 g255H12
  | 13 => lookupWord 2 17 0 8 3 1 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : CutRow g255 7 0 23 := by
  apply polarBlock (data:=fun _ => (word80 [0x208281,0x60a20920080000a058a8,0x4263080000a058a84263,0x20860320e209200800,0x44229904263080000a0,0x58a8426300820281c0a8,0x2420080000a058a84263,0x820400c50824200800,0x4422990426300820209,0x848a2421080000182c86,0x4863080000182c864863,0x80000182c8648630082,0x209848a242108000018,0x2c86486300820281c0a8,0x2421080000182c864863,0x80000182c8648630800,0x182c86486208000018,0x2c864862080000182c86,0x4862080000182c864862])) rfl
  decide +kernel
theorem g255B7 : CutRow g255 7 0 23 := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : CutRow g255 8 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_6 : CutRow g255 8 6 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x44600a1,0x502c6240040010804460,0x21530401000844423063,0x6410a1502c43400285,0x4432118544100641443,0x21144340006410a1502c,0x4340010400190c164842,0x44600a1502c62400401,0x4004540305304080080,0x4460a063044600a1502c,0x6240004400a1502c4230,0x110c00190c16c8320044,0xa1502c423004460443,0x2114623002850111884c,0x54310064144321144330,0x6410a1502c43300800,0x182c86487408000018,0x2c864874080000182c86,0x4873080000182c864873,0x4400a1502c42400446,0x4432114624004001400,0x45402153040800084442,0xa063050600190c166842,0x4400a1502c42300285,0x44321185431004400a1,0x502c4230028504432118,0x5431006410a1502c4330,0x10400190c1648320285,0x4432118543100840111,0x884c4431110c00190c16,0xc8320285044321185431,0x2850111884c54310048,0x30344c48240044600a1,0x502c62300048020b0486,0x8240006410a1502c4330,0x480082402482400305,0x190c165832006410a1,0x502c433002850111884c,0x5431006410a1502c4330])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_54 : CutRow g255 8 54 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x820209,0x848a2432080000182c86,0x4874080000182c864874,0x440443211442410064,0x10a1502c434100220080,0xc0222160006410a1502c,0x43410446044321146240,0x440443211442300100,0x16030590096201001301,0xc0d0096201001301c0d0,0x952080000182c864874,0x80000182c8648740800,0x182c86487408000018,0x2c86487300840111884c,0x4442006410a1502c4341,0x210400c10211500028,0x80c0228160006410a1,0x502c4341004400a1502c,0x4230180411008540c154,0x410301c0c412600041,0x30184c4126000410402,0x5041250080000182c86,0x4874080000182c864874,0x80000182c8648740800,0x182c86487300820281,0xc0a82431080000182c86,0x4874080000182c864874,0x80000182c8648730305,0x190c16584204460443,0x21146240004404432114,0x4230044600a1502c6240,0x4460443211462400082,0x209848a243100820209,0x848a2431028504432118,0x544100820281c0a82431,0x820281c0a824310064,0x14432114434000820400,0xc508243100820400c508,0x24310044044321144240])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_102 : CutRow g255 8 102 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x8000442,0x29904274080000a058a8,0x42740100130184d00972,0x100130380d009620100,0x1301c0d0096208240301,0xc0c2517000210301c0c2,0x117000840111884c4451,0x200130184e011730800,0x182c86487508000018,0x2c864865004404432114,0x42500200110084601173,0x80000182c8648750800,0x182c86487508000018,0x2c864874080000182c86,0x48740100160305900972,0x1001603419009620800,0x182c86487508000018,0x2c864875080000182c86,0x48740824028340a2c170,0x280082402281700044,0x4432114425108240301,0xc0c2517000210100c042,0x1170004400a1502c4241,0x440443211442500a04,0x30184e0517302001100,0x84601173004400a1502c,0x4240040800824060a064,0x408000a0442a0640021,0x4024102114000210100,0xc0421140004404432114,0x4241004400a1502c4240,0x4400a1502c42400044,0x4432114423008000442,0x29904274008204028108,0x24310800044229904274,0x80000a058a842740800,0x4422990427301001301,0x84d0096201001301c0d0,0x9620100160341900952])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_150 : CutRow g255 8 150 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x480301,0xc0c48261006410a1502c,0x4341006410a1502c4341,0x208301a0c209300020,0x8301a0c2093008250400,0xc10251500020860320e2,0x93008250100c0425160,0x80000182c8648750800,0x182c86487508000018,0x2c864874080000a058a8,0x427500820281c0a82441,0x80000a058a842750800,0x44229904274080000a0,0x58a842740100130184d0,0x9620100128340b00962,0x100128340b009520041,0x301c0c412710041020b,0x48612610041020b0486,0x126000820209848a2442,0x80000182c8648750800,0x182c86487508000018,0x2c864874020204028120,0x30540202000884223043,0x280082402281600044,0xa1502c424100440443,0x21144230006414432114,0x43410044044321144240,0x44600a1502c62400044,0xa1502c423002850443,0x2118544202850111884c,0x54420021040241021180,0x210402410211700041,0x30184c4126008000018,0x2c864875080000182c86,0x4875080000182c864875,0x80000182c8648740800,0x182c864874080000a0,0x58a84275080000a058a8,0x4275080000a058a84275])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_198 : CutRow g255 8 198 34 := by
  apply polarBlock (data:=fun _ => (word80 [0x800,0xa058a84275080000a0,0x58a8427400820209848a,0x24720082020b048a2462,0x82028340a824620020,0x828160a20920080000a0,0x58a84274080000a058a8,0x4275080000a058a84275,0x80000a058a842750800,0xa058a8427400440081,0x60244251004400816024,0x42510044040321044241,0x410209448612710041,0x20b0486126100410209,0x84861261080000a058a8,0x4275080000a058a84275,0x80000a058a842750800,0xa058a8427408000442,0x2990427408240301c0c2,0x51700401020944c23074,0x48020b048682710048,0x2094486826100820209,0x848a246200820209448a,0x24620082040241082452,0x8000442299042740020,0x86032182092008000442,0x299042730048020b0486,0x82710048020944868261])) rfl
  decide +kernel
theorem g255B8 : CutRow g255 8 0 232 := (@joinRow g255 8 0 102 130 (@joinRow g255 8 0 6 96 g255P8_0 (@joinRow g255 8 6 48 48 g255P8_6 g255P8_54)) (@joinRow g255 8 102 48 82 g255P8_102 (@joinRow g255 8 150 48 34 g255P8_150 g255P8_198)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : CutRow g255 9 0 16 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_16 : CutRow g255 9 16 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_64 : CutRow g255 9 64 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_112 : CutRow g255 9 112 30 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_142 : CutRow g255 9 142 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x6410a1,0x502c4351028504432118,0x5452006410a1502c4351,0x10400190c1648530446,0x4432114625100840111,0x884c4452006414432114,0x43510446044321146251,0x44600a1502c62510048,0x30380c48261044600a1,0x502c62510048020b0486,0x8261006410a1502c4351,0x6410a1502c43510446,0xa1502c6251006410a1,0x502c4351004400a1502c,0x42410446044321146241,0x2850111884c54420064,0x10a1502c434104460443,0x2114625000820281c0a8,0x2441110c00190c16c852,0x820402810824410044,0x4432114425002020008,0x84223043020200088422,0x3043030500190c165852,0x4400a1502c42500446,0x4432114625000641443,0x21144350030500190c16,0x5852110c00190c16c852,0x2850111884c54510044,0x44321144240044600a1,0x502c6240110c00190c16,0xc842006410a1502c4340,0x840111884c44510285,0x4432118545100480082,0x40248260030500190c16,0x5852030500190c165852,0x2850443211854510044,0x4432114424002850443,0x21185441050600190c16,0x6842006410a1502c4340])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_190 : CutRow g255 9 190 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x440443,0x21144261004404432114,0x4261110c00190c16c863,0x210603418211400021,0x100c042114000210100,0xc042114000210100c042,0x11400021060341821140,0x210100c04211400c04,0x20b04c2e0950408000a,0x442a07500210100c042,0x114008250301c0c25140,0x210100c04211400408,0xa0442a075004400a1,0x502c4251004404432114,0x42500044044321144261,0x210100c04211400044,0xa1502c425100840111,0x884c4462002104024102,0x11400021040241021140,0x210603418211400021,0x301c0c21140004400a1,0x502c4251044604432114,0x62510044044321144241,0x4400a1502c42500446,0x4432114625000440443,0x21144240006410a1502c,0x43610048008240248271,0x210402410211400021,0x4024102114000210402,0x41021140180402098582,0xe0960446044321146251,0x820209848a24420c0c,0x824060e06400820402,0x81082442004404432114,0x425100220080c0222140,0x220080c02221400064,0x10a1502c4351004400a1,0x502c4251044604432114,0x62510285044321185452])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_238 : CutRow g255 9 238 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400a1,0x502c4250002800824022,0x8170004400a1502c4251,0x10400190c1648630202,0x4028120305402020402,0x812030540202060381a0,0x30540044044321144251,0x641443211443510044,0x4432114425102850443,0x21185452044600a1502c,0x62510064144321144351,0x202020984a230430044,0x4432114424002850443,0x21185462020204028120,0x30540c04028144e06194,0x820281c0a824520285,0x4432118546202850111,0x884c5462020204028120,0x30540202040281203043,0x2020402812030541804,0x28145a0c19600480082,0x40248271110c00190c16,0xc853044600a1502c6251,0x200301a0c209700020,0x6032182097000480303,0x80c4827100840111884c,0x4462044600a1502c6261,0x210100c04211400021,0x301c0c2114000440443,0x2114426100840111884c,0x446200210301c0c21140,0x4400a1502c42510044,0xa1502c425000210301,0xc0c21140080000182c86,0x4885006410a1502c4361,0x820209848a24520082,0x4028108245200210402,0x41021140004400a1502c,0x42510044044321144250])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_286 : CutRow g255 9 286 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x208301,0xa0c209300048020b0486,0x8271010400190c164863,0x6410a1502c43610202,0x88422305402020209,0x84a23054004404432114,0x4261010400190c164863,0x202020984a230540044,0xa1502c42510048020b,0x48682710202020984a2,0x30540020860321820930,0x6410a1502c43610285,0x111884c546200208281,0x60a20930006414432114,0x4351006410a1502c4351,0x208301a0c20930082c,0x824022c16000208603,0x21820930002086032182,0x9300202020984a23054,0x202060381a030540021,0x100c042114008240283,0x40a2c19008260080c022,0x614000410301c0c41241,0x80000182c8648850041,0x301c0c4124104460443,0x21146261006414432114,0x4361044600a1502c6261,0x4460443211462610082,0x209848a245202850443,0x2118546200820281c0a8,0x24520064144321144361,0x641443211443610082,0x209848a245200220402,0x810221500c04020944c2,0x70940446044321146261,0x641443211443610202,0x88422305400280082,0x40228170004404432114,0x42610202000884223054])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_334 : CutRow g255 9 334 15 := by
  apply polarBlock (data:=fun _ => (word80 [0x820209848a24520800,0xa058a8428500208301,0xa0c2093000820209848a,0x2452006410a1502c4361,0x2850443211854620064,0x10a1502c436100208301,0xa0c2093000208301a0c2,0x930044600a1502c6261,0x8250301c0c251400825,0x4024102514004460443,0x21146261002204028102,0x215008240301c0c25190])) rfl
  decide +kernel
theorem g255B9 : CutRow g255 9 0 349 := (@joinRow g255 9 0 142 207 (@joinRow g255 9 0 64 78 (@joinRow g255 9 0 16 48 g255P9_0 g255P9_16) (@joinRow g255 9 64 48 30 g255P9_64 g255P9_112)) (@joinRow g255 9 142 96 111 (@joinRow g255 9 142 48 48 g255P9_142 g255P9_190) (@joinRow g255 9 238 48 63 g255P9_238 (@joinRow g255 9 286 48 15 g255P9_286 g255P9_334))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : CutRow g255 10 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_3 : CutRow g255 10 3 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_51 : CutRow g255 10 51 5 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_56 : CutRow g255 10 56 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_104 : CutRow g255 10 104 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_152 : CutRow g255 10 152 9 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_161 : CutRow g255 10 161 7 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_168 : CutRow g255 10 168 20 := by
  apply polarBlock (data:=fun _ => (word80 [0x208301a0c209300044,0xa1502c426100820209,0x848a2452004400a1502c,0x42610020860321820930,0x440443211442610044,0x443211442610048020b,0x486827100820281c0a8,0x2452004400a1502c4261,0x440443211442610285,0x111884c546200641443,0x21144361008204028108,0x24520044044321144261,0x440443211442610048,0x30380c48271004400a1,0x502c4261044604432114,0x6261006410a1502c4361])) rfl
  decide +kernel
theorem g255B10 : CutRow g255 10 0 188 := (@joinRow g255 10 0 104 84 (@joinRow g255 10 0 51 53 (@joinRow g255 10 0 3 48 g255P10_0 g255P10_3) (@joinRow g255 10 51 5 48 g255P10_51 g255P10_56)) (@joinRow g255 10 104 57 27 (@joinRow g255 10 104 48 9 g255P10_104 g255P10_152) (@joinRow g255 10 161 7 20 g255P10_161 g255P10_168)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : CutRow g255 11 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_1 : CutRow g255 11 1 24 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_25 : CutRow g255 11 25 20 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : CutRow g255 11 0 45 := (@joinRow g255 11 0 1 44 g255P11_0 (@joinRow g255 11 1 24 20 g255P11_1 g255P11_25))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : CutRow g255 12 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : CutRow g255 12 0 7 := g255P12_0
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

end PEqualNP.Outside.L_meta_34752

open PEqualNP.Outside.L_meta_34752 in
theorem PEqualNP.Outside.L_meta_34752 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
