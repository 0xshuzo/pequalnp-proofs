import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52832.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52832
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfefefffffffefffffffe,0xfffffefafefaeca0ffff,0xffffffffffffffffffff,0xfffffefefffffffeffff,0xfffefffffefafefaeca0]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,4]⟩,⟨.or,[2,8]⟩,⟨.or,[1,9]⟩,⟨.or,[1,6]⟩,⟨.or,[3,7]⟩,⟨.or,[7,9]⟩,⟨.or,[6,7]⟩,⟨.and,[12,11]⟩,⟨.and,[14,10]⟩,⟨.and,[13,5]⟩,⟨.and,[8,2]⟩,⟨.and,[4,0]⟩,⟨.or,[15,16]⟩,⟨.or,[20,17]⟩,⟨.or,[21,18]⟩,⟨.or,[22,19]⟩], 23⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([2, 3, 0, 1, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([2, 3, 0, 1, 0, 0, 0, 0] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 14 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
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
def g21Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g21C : List ColumnInfo := []
def g21A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g21D3 (j : Nat) := if j=0 then 0x7 else 0
def g21L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g21D3)
  | _ => emptyPacking
def g21I (_ _ : Nat) : Option (Nat × Nat) := none
def g21 : Forest := ⟨21,3,fun i => g21Y[i]?.getD (0,0),g21C,g21A,g21L,g21I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21P3_0 : block g21 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g21B3 : block g21 3 0 1=true := g21P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21T : checkedTables g21 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g21 0 0 0 = true)
  · exact (rfl : block g21 1 0 0 = true)
  · exact (rfl : block g21 2 0 0 = true)
  · exact g21B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21G : graphValid g21 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low21 : Lower true (varsX 21) (graphGoal 21) 4 := lower_forest (g:=g21) (i:=0) (hints:=2) (before_sound [] baseKnown) g21G g21T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K21 := extendKnown [] 4 [(21,[]),(37,[84]),(49,[66,50,83]),(52,[32,16,65,49,83]),(69,[100,84]),(74,[16,50,100,84]),(133,[116,84,101]),(145,[66,50,115,83,101]),(148,[32,16,65,49,115,83,101]),(161,[82,50,116,100]),(164,[32,16,81,49,116,100]),(176,[64,16,82,49,115,99]),(194,[16,98,50,116,83,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V21 : Known true K21 := extend_ok (m:=21) baseKnown low21 (by decide +kernel)
def g53Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g53C : List ColumnInfo := [(1,0,52,0,4),(4,0,49,0,4),(16,0,37,0,4),(32,0,21,0,4)]
def g53A : List (List Nat) := [[],[84],[66],[66,82],[82,66],[82],[32],[32,84],[32,64],[32,64,80],[32,80,64],[32,80],[64,32],[64,32,82],[64],[64,80],[64,82],[64,82,32],[80,32,66],[80,32],[80,64],[80],[80,66,32],[80,66]]
def g53D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g53D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g53H4 (j : Nat) := if j=0 then 0x7540 else 0
def g53D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g53H5 := limbs80 #[#[0x110000000,0x8a000000000009308400,0x70000000600000000001,0x20800cc0]]
def g53D6 (j : Nat) := if j=0 then 0x3904f else 0
def g53H6 := limbs80 #[#[0x25003d0003100001a4,0xe00000000002800000]]
def g53L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g53D3)
  | 4 => (3,2,2,0,0,5,0,g53D4)
  | 5 => (1,1,2,0,0,0,0,g53D5)
  | 6 => (1,0,2,0,0,0,0,g53D6)
  | _ => emptyPacking
def g53I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 5 0 5 1 0 g53H4
  | 5 => lookupWord 2 31 0 9 2 3 g53H5
  | 6 => lookupWord 1 17 0 9 0 5 g53H6
  | _ => fun _ => none
def g53 : Forest := ⟨53,6,fun i => g53Y[i]?.getD (0,0),g53C,g53A,g53L,g53I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P3_0 : block g53 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B3 : block g53 3 0 2=true := g53P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P4_0 : block g53 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B4 : block g53 4 0 3=true := g53P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P5_0 : block g53 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B5 : block g53 5 0 1=true := g53P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P6_0 : block g53 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B6 : block g53 6 0 1=true := g53P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53T : checkedTables g53 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g53 0 0 0 = true)
  · exact (rfl : block g53 1 0 0 = true)
  · exact (rfl : block g53 2 0 0 = true)
  · exact g53B3
  · exact g53B4
  · exact g53B5
  · exact g53B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53G : graphValid g53 (boundsBefore K21) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low53 : Lower true (varsX 53) (graphGoal 53) 7 := lower_forest (g:=g53) (i:=0) (hints:=2) (before_sound K21 V21) g53G g53T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K53 := extendKnown K21 7 [(53,[]),(85,[101]),(149,[117,101]),(165,[84,116,100]),(177,[66,50,83,115,99]),(180,[32,16,65,49,83,115,99]),(197,[100,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V53 : Known true K53 := extend_ok (m:=53) V21 low53 (by decide +kernel)
def g71Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g71C : List ColumnInfo := [(2,0,69,0,4)]
def g71A : List (List Nat) := [[],[32]]
def g71D4 (j : Nat) := if j=0 then 0x1f else 0
def g71L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g71D4)
  | _ => emptyPacking
def g71I (_ _ : Nat) : Option (Nat × Nat) := none
def g71 : Forest := ⟨71,4,fun i => g71Y[i]?.getD (0,0),g71C,g71A,g71L,g71I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g71P4_0 : block g71 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g71B4 : block g71 4 0 1=true := g71P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g71T : checkedTables g71 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g71 0 0 0 = true)
  · exact (rfl : block g71 1 0 0 = true)
  · exact (rfl : block g71 2 0 0 = true)
  · exact (rfl : block g71 3 0 0 = true)
  · exact g71B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g71G : graphValid g71 (boundsBefore K53) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low71 : Lower true (varsX 71) (graphGoal 71) 5 := lower_forest (g:=g71) (i:=0) (hints:=98) (before_sound K53 V53) g71G g71T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K71 := extendKnown K53 5 [(71,[]),(75,[16,50]),(77,[49]),(78,[16,32,48]),(89,[49,66]),(90,[16,64,50,32]),(92,[32,49,64,16]),(163,[82,50,67,118]),(201,[49,114,66,84]),(226,[16,80,98,48,66,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V71 : Known true K71 := extend_ok (m:=71) V53 low71 (by decide +kernel)
def g99Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0)]
def g99C : List ColumnInfo := []
def g99A : List (List Nat) := [[],[96,81]]
def g99D3 (j : Nat) := if j=0 then 0xf else 0
def g99L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g99D3)
  | _ => emptyPacking
def g99I (_ _ : Nat) : Option (Nat × Nat) := none
def g99 : Forest := ⟨99,3,fun i => g99Y[i]?.getD (0,0),g99C,g99A,g99L,g99I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99P3_0 : block g99 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g99B3 : block g99 3 0 1=true := g99P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99T : checkedTables g99 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g99 0 0 0 = true)
  · exact (rfl : block g99 1 0 0 = true)
  · exact (rfl : block g99 2 0 0 = true)
  · exact g99B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99G : graphValid g99 (boundsBefore K71) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low99 : Lower true (varsX 99) (graphGoal 99) 4 := lower_forest (g:=g99) (i:=0) (hints:=101) (before_sound K71 V71) g99G g99T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K99 := extendKnown K71 4 [(99,[]),(102,[32]),(105,[49,33]),(114,[64,32,50]),(120,[64,49,32]),(139,[16,67,83,118]),(142,[16,32,67,83,118]),(154,[112,49,32,33,84,97]),(170,[112,49,32,33,97]),(232,[112,49,32,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V99 : Known true K99 := extend_ok (m:=99) V71 low99 (by decide +kernel)
def g101Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf3e58e3ffc1ffcff3e,0x58e3ffc1ffcff3e58e3f])),(BitVec.ofNat 152 (word80 [0x200012490842080200,0x1249084208020001249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfcfa71c7ffe0ff3fcf,0xa71c7ffe0ff3fcfa71c7])),(BitVec.ofNat 152 (word80 [0x400024921084100400,0x2492108410040002492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0e81f8ffff003ff0,0xe81f8ffff003ff0e81f8])),(BitVec.ofNat 152 (word80 [0x804ec924a108a2a804,0xec924a108a2a804ec924]))),((BitVec.ofNat 152 (word80 [0x19fe00ffffffc001,0x9fe00ffffffc0019fe00])),(BitVec.ofNat 152 (word80 [0xa99c924c210c030a9,0x9c924c210c030a99c924]))),(0x0,0x0),(0x0,0x0)]
def g101C : List ColumnInfo := [(32,0,69,0,4)]
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
theorem g101G : graphValid g101 (boundsBefore K99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low101 : Lower true (varsX 101) (graphGoal 101) 5 := lower_forest (g:=g101) (i:=0) (hints:=2) (before_sound K99 V99) g101G g101T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K101 := extendKnown K99 5 [(101,[]),(195,[96,33,113,80,81]),(202,[16,98,50,83,117]),(228,[32,16,113,49,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V101 : Known true K101 := extend_ok (m:=101) V99 low101 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,2,21,8,5)]
def g31A : List (List Nat) := [[],[66],[49],[49,66],[32],[32,64],[32,49],[32,49,64],[64,32],[64],[64,49,32],[64,49]]
def g31D5 (j : Nat) := if j=0 then 0x3f else 0
def g31L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g31D5)
  | _ => emptyPacking
def g31I (_ _ : Nat) : Option (Nat × Nat) := none
def g31 : Forest := ⟨31,5,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 1=true := g31P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact g31B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K101) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 6 := lower_forest (g:=g31) (i:=0) (hints:=4146) (before_sound K101 V101) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K101 6 [(31,[]),(47,[84]),(59,[66,82]),(62,[32,64,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V101 low31 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(1,0,78,0,5),(2,0,77,0,5),(4,0,75,0,5),(8,0,71,0,5),(5,0,74,0,4),(10,0,69,0,4)]
def g79A : List (List Nat) := [[],[49],[16,50],[16,32,48],[32],[32,49],[48,16,33],[48,33]]
def g79D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g79D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g79H5 := limbs80 #[#[0xe800d9000000b10000,0x2200b0]]
def g79D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g79H6 := limbs80 #[#[0x309910020725c81002d3,0x18300000001c000000,0x78645a100071bc800000,0x3d99500000289]]
def g79D7 (j : Nat) := if j=0 then 0x1605f else 0
def g79H7 := limbs80 #[#[0x7e95999005c85540,0xa20000000c0000040882,0x6900000000000002,0x3d00000120]]
def g79L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g79D4)
  | 5 => (10,2,3,0,0,7,0,g79D5)
  | 6 => (3,1,3,0,0,6,0,g79D6)
  | 7 => (1,0,3,0,0,0,0,g79D7)
  | _ => emptyPacking
def g79I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 8 2 2 g79H5
  | 6 => lookupWord 4 29 0 10 4 2 g79H6
  | 7 => lookupWord 3 31 3 9 2 3 g79H7
  | _ => fun _ => none
def g79 : Forest := ⟨79,7,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4_0 : block g79 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B4 : block g79 4 0 3=true := g79P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5_0 : block g79 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5_1 : block g79 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B5 : block g79 5 0 10=true := (@block_merge g79 5 0 1 9 g79P5_0 g79P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P6_0 : block g79 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B6 : block g79 6 0 3=true := g79P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P7_0 : block g79 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B7 : block g79 7 0 1=true := g79P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact g79B4
  · exact g79B5
  · exact g79B6
  · exact g79B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 8 := lower_forest (g:=g79) (i:=0) (hints:=4146) (before_sound K31 V31) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K31 8 [(79,[]),(91,[66]),(94,[16,32,48,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V31 low79 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := [(2,0,85,0,7)]
def g87A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g87D7 (j : Nat) := if j=0 then 0x3f else 0
def g87L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g87D7)
  | _ => emptyPacking
def g87I (_ _ : Nat) : Option (Nat × Nat) := none
def g87 : Forest := ⟨87,7,fun i => g87Y[i]?.getD (0,0),g87C,g87A,g87L,g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P7_0 : block g87 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g87B7 : block g87 7 0 1=true := g87P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g87 0 0 0 = true)
  · exact (rfl : block g87 1 0 0 = true)
  · exact (rfl : block g87 2 0 0 = true)
  · exact (rfl : block g87 3 0 0 = true)
  · exact (rfl : block g87 4 0 0 = true)
  · exact (rfl : block g87 5 0 0 = true)
  · exact (rfl : block g87 6 0 0 = true)
  · exact g87B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 8 := lower_forest (g:=g87) (i:=0) (hints:=98) (before_sound K79 V79) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K79 8 [(87,[]),(93,[49]),(151,[118]),(167,[84,118]),(205,[49,116,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V79 low87 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xf0ffffffe85e1a00f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028280,0xa2020020880612111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0xff0ff00c35f90f0000])),(BitVec.ofNat 152 (word80 [0xac26158854022b030a,0xc41422420835b9777777]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xff000fff33b526f00f0f])),(BitVec.ofNat 152 (word80 [0x3008060018440c0403,0x184080303104222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b0282c,0xa00b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x8c08c08468840888888]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := [(0,2,37,64,5),(2,0,101,0,5),(32,0,71,0,5),(1,0,102,0,4),(4,0,99,0,4),(64,2,37,0,4)]
def g103A : List (List Nat) := [[],[32]]
def g103D4 (j : Nat) := if j=0 then 0x57d4d20 else 0
def g103D5 (j : Nat) := if j=0 then 0xc8404fd20 else 0
def g103H5 (j : Nat) := if j=0 then 0xe else 0
def g103D6 (j : Nat) := if j=0 then 0x232a8bf else 0
def g103H6 (j : Nat) := if j=0 then 0xf else 0
def g103L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g103D4)
  | 5 => (1,1,3,0,0,0,0,g103D5)
  | 6 => (1,0,3,0,0,0,0,g103D6)
  | _ => emptyPacking
def g103I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g103H5
  | 6 => lookupWord 1 2 0 4 0 0 g103H6
  | _ => fun _ => none
def g103 : Forest := ⟨103,6,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : block g103 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B4 : block g103 4 0 1=true := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P5_0 : block g103 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B5 : block g103 5 0 1=true := g103P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P6_0 : block g103 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B6 : block g103 6 0 1=true := g103P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact g103B4
  · exact g103B5
  · exact g103B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 7 := lower_forest (g:=g103) (i:=0) (hints:=98) (before_sound K87 V87) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K87 7 [(103,[]),(109,[49]),(115,[66,50]),(118,[32,64,48]),(121,[49,66]),(124,[32,49,64,16]),(233,[49,114,66]),(234,[16,80,98,48,66,116]),(236,[32,49,112,16,65]),(248,[64,49,114,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V87 low103 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf001ff87fe1fffc01f,0xffffffc3665ce0007fe0])),(BitVec.ofNat 152 (word80 [0xa054051024400a8540,0xa090008a625820318c63]))),((BitVec.ofNat 152 (word80 [0xfffe0007ffe1ffffe0,0xff87ffcb173a60f801f])),(BitVec.ofNat 152 (word80 [0xc11826208804230184,0xc02109002031a65294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x260480130884c0601,0x2c21200c7c008a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb817045c111702816,0xb005c100d27c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0180060001803018,0xc046021180611084210]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(0,32,74,1,5),(32,0,75,0,5),(1,32,74,0,4),(2,0,105,0,4),(8,0,99,0,4)]
def g107A : List (List Nat) := [[],[49]]
def g107D4 (j : Nat) := if j=0 then 0x5bd4941 else 0
def g107D5 := limbs80 #[#[0x260d140ff41fd41fd21,0x2012]]
def g107H5 (j : Nat) := if j=0 then 0xc else 0
def g107D6 (j : Nat) := if j=0 then 0x18d09f else 0
def g107H6 (j : Nat) := if j=0 then 0xc1ef900000003c01d00 else 0
def g107L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g107D4)
  | 5 => (3,1,3,0,0,5,0,g107D5)
  | 6 => (1,0,3,0,0,0,0,g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g107H5
  | 6 => lookupWord 1 11 0 7 2 1 g107H6
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
theorem g107P5_0 : block g107 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 3=true := g107P5_0
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
theorem g107G : graphValid g107 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=4149) (before_sound K103 V103) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K103 7 [(107,[]),(110,[32]),(122,[64,32]),(143,[16,66,50,83,118]),(155,[16,67,83,118]),(158,[16,32,67,83,118]),(171,[16,83,118]),(174,[16,32,83,118]),(186,[16,64,32,83,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V103 low107 (by decide +kernel)
def g117Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe07ffc07f3f9ff01,0xfcfe7fc7f4800f00f0ff])),(BitVec.ofNat 152 (word80 [0x204104081020100204,0x8040080000111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff81fff803fe7ffe,0xff9ff8e150f00f0f0f])),(BitVec.ofNat 152 (word80 [0x408208102040200408,0x10080100000222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00001fffffc007fff,0xff001fff0a2f00f00ff0])),(BitVec.ofNat 152 (word80 [0x810410204080400810,0x20100200000444444444]))),((BitVec.ofNat 152 (word80 [0xfffffe000000007fff,0xffffe0001e5000fff000])),(BitVec.ofNat 152 (word80 [0xa082142850a8550a1,0x40a014125e5888888888]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x19bfff000000])),(BitVec.ofNat 152 (word80 [0xc10418306030060c1,0x82c1582499b888888888]))),(0x0,0x0),(0x0,0x0)]
def g117C : List ColumnInfo := [(32,0,85,0,7)]
def g117A : List (List Nat) := [[],[101],[66],[66,101],[32],[32,101],[32,64],[32,64,101],[64,32],[64,32,101],[64],[64,101]]
def g117D7 (j : Nat) := if j=0 then 0x3f else 0
def g117L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g117D7)
  | _ => emptyPacking
def g117I (_ _ : Nat) : Option (Nat × Nat) := none
def g117 : Forest := ⟨117,7,fun i => g117Y[i]?.getD (0,0),g117C,g117A,g117L,g117I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P7_0 : block g117 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B7 : block g117 7 0 1=true := g117P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117T : checkedTables g117 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g117 0 0 0 = true)
  · exact (rfl : block g117 1 0 0 = true)
  · exact (rfl : block g117 2 0 0 = true)
  · exact (rfl : block g117 3 0 0 = true)
  · exact (rfl : block g117 4 0 0 = true)
  · exact (rfl : block g117 5 0 0 = true)
  · exact (rfl : block g117 6 0 0 = true)
  · exact g117B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117G : graphValid g117 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 8 := lower_forest (g:=g117) (i:=0) (hints:=2) (before_sound K107 V107) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K107 8 [(117,[]),(229,[116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V107 low117 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc0fc0fc0fdf81fbf7f,0x3f7efec0007c00f83ff])),(BitVec.ofNat 152 (word80 [0x820820820810410202,0x8204040210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fff01ffe03fbf,0xfc07f7f400f801f07c1f])),(BitVec.ofNat 152 (word80 [0x41041041020820404,0x10408080421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff00001ffffc03f,0xfff807f81f003e007fe0])),(BitVec.ofNat 152 (word80 [0x82082082041040808,0x20810100842108421084]))),((BitVec.ofNat 152 (word80 [0xfffffffffe0000003f,0xfffff803e0003fff8000])),(BitVec.ofNat 152 (word80 [0x104104104082081010,0x41020201084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffc0,0x3ffffc0000000])),(BitVec.ofNat 152 (word80 [0x208208208104102020,0x82040402108421084210]))),(0x0,0x0)]
def g181C : List ColumnInfo := [(1,0,180,0,7),(4,0,177,0,7),(16,0,165,0,7),(32,0,149,0,7),(128,0,53,0,7),(5,0,176,0,4),(17,0,164,0,4),(20,0,161,0,4),(33,0,148,0,4),(36,0,145,0,4),(48,0,133,0,4)]
def g181A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116],[66],[66,117],[66,82],[66,82,114],[66,114,82],[66,114],[82,66],[82,66,116],[82],[82,114],[82,116],[82,116,66],[114,66,84],[114,66],[114,82],[114],[114,84,66],[114,84],[32],[32,117],[32,84],[32,84,116],[32,116,84],[32,116],[32,64],[32,64,117],[32,64,80],[32,64,80,112],[32,64,112,80],[32,64,112],[32,80,64],[32,80,64,116],[32,80],[32,80,112],[32,80,116],[32,80,116,64],[32,112,64,84],[32,112,64],[32,112,80],[32,112],[32,112,84,64],[32,112,84],[64,32],[64,32,117],[64,32,82],[64,32,82,114],[64,32,114,82],[64,32,114],[64],[64,117],[64,80],[64,80,112],[64,112,80],[64,112],[64,82],[64,82,114],[64,82,32],[64,82,32,112],[64,82,112,32],[64,82,112],[64,114,82],[64,114],[64,114,32,80],[64,114,32],[64,114,80],[64,114,80,32],[80,32,66],[80,32,66,116],[80,32],[80,32,114],[80,32,116],[80,32,116,66],[80,64],[80,64,116],[80],[80,112],[80,116],[80,116,64],[80,66,32],[80,66,32,114],[80,66],[80,66,112],[80,66,114],[80,66,114,32],[80,114,64,66],[80,114,64],[80,114,66],[80,114,66,64],[80,114],[80,114,32],[112,32,66,84],[112,32,66],[112,32,82],[112,32],[112,32,84,66],[112,32,84],[112,64,84],[112,64],[112,80],[112],[112,84,64],[112,84],[112,66,32,82],[112,66,32],[112,66,80],[112,66],[112,66,82,32],[112,66,82],[112,82,64],[112,82,64,66],[112,82,66,64],[112,82,66],[112,82,32],[112,82]]
def g181D3 := limbs80 #[#[0x887805915350d2148110,0x4180360709aa26498a40,0x2]]
def g181D4 := limbs80 #[#[0x48110f415350d2148110,0x54d2148110b618550d21,0xe636454d2148110e6164,0x48110b638454d2148110,0xd4d2148110e6364d4d21,0xf41544c93148110b6184,0x48110f43544c93148110,0xd913148110f814350931,0xcb374d913148110ad183,0x4c91087b805d9544c910,0x82a4854300c3874dc165,0x808103df5df82d4b78d9,0x4002820a04000000120,0x1]]
def g181H4 := limbs80 #[#[0x330000000000000,0xd0d9c40000010000]]
def g181D5 := limbs80 #[#[0xa4290221d854d2148110,0x4887c1324c520443b1a9,0x850d214811087ee8b2a6,0xc520443f0a9a4290221f,0x10fc2e498a40887e1424,0xaa26290221dc55131481,0xa40886f1644c520443b9,0x15e5d54348110de6c898,0x254d20442f5b92a69022,0x8110cf2c8a9a408876b7,0xbdba2a6902219ed91534,0xa9a408867b64d4d20442,0x221bc585604c910af2e9,0xf76551324423ebb2a899,0x44c910adae5aa2648847,0x423ebb6a8992218fd935,0xe8b2a648856f72595324,0x992219edc1654c910a7e,0x63f74595324431e3a2ca,0xa654c9108fee8b2a6488,0x24423ebb4ca992215b5c,0x7ee8b1aa48856f7254d5,0xc7a92211f5d36354910a,0xb62007a1502e0023fba2,0x364a11a43106400e2370,0xbe681926317e5e16a531,0x16821fa7b1e6781d2711,0x669825a9323e8c22a872,0xc19cc144090805739216,0x7381801800a090605101,0x300242048144070605,0x8202041810904000241d],#[0x3481002410805020c200,0xc1d2040d221200c0810,0x404000074810204000,0x41010204]]
def g181H5 := limbs80 #[#[0xb978a00c211192d10084,0xd0f4a00a0398032,0x31e38000e3c1630400,0x10649ca0cbc800180,0x4800030e00002803b003,0x38f57000005009892ac0,0x230141f32017c,0x2a940000080294c16892,0x30656852020400038c,0x10d7a1a0000424790c00,0x5830db6c600008f800c3,0x23033d312c1c9200346,0x63c3078c0005006354f4,0x8000f26ec036f060000,0x9238308000b307a92d00,0x2,0x900a0000000248d,0x800000000000000,0xb1c346320c6d48c00000,0x3d78c334600000]]
def g181D6 := limbs80 #[#[0xfc4c520443e12148110,0x10ded4d2044379534811,0x9109fd8d524427d654c9,0x8110fe50d204427d63d4,0x4c910fe58132443f9534,0x54c910dfd51324437d54,0x5354910df995324437d6,0xd6354910bfd8d524437d,0x40600dc00dfd8d524437,0xf1935a94847d0436cb22,0x414795e43886067e5de6,0x12199d20a2870d03a732,0x333a414412202b3c3486,0x5d30e0662d3a58700414,0x4467083058228466143a,0x14288a42836114488241,0x2520ca5214144294a0c0,0x7c019989809920e90215,0x1c305662346610]]
def g181H6 := limbs80 #[#[0x1101c410c01400c0145,0x1281c50410011104090,0x830035e9a0d201e51810,0x5700de808e4045818ca3,0x8007864398605c790c01,0x218a00a90e2800016518,0x8a811c60241046c0006c,0x8000000000000d0c5106,0x3c5f044c0001c00ecc47,0x1c0000300440001e0088,0x1e68a1051100100000ac,0x304348400948640000,0x2c02f001f600600002,0x2835b0615a019000000,0x53c84bc51002c8000f05,0x7c0b022fed28400c0000,0x1600000000000034f0a0,0x20e230d11000030743d2,0x9a1b4082000006460000,0x10006000000000000004,0x6000038c000000c185b0,0x23e0800400000ec8,0x99400000000000000000,0x2dcf14a021202480001f,0xa0030000107,0x7d32380382668d91c0,0x118345b1c30000060252,0xfc09a7006b34334317a1,0x304bf83674d0,0x10c9f004f000004870,0xd9f140001868e838980,0x20e07242bc0120000f3c],#[0xc185800738091a4c8,0x44478700003804fa6180,0xe403b2907200289e00cf,0x8050c034e548c0201002,0x5b22b8c396002e0e57]]
def g181D7 := limbs80 #[#[0x7f52442faa4887e48110,0x3015007f54910fe99221,0x94301030ba6694235a3f,0xa5011a6690a20e30ba66,0x38da6690a3c8a142a70,0x4]]
def g181H7 := limbs80 #[#[0x8004021200c020208180,0x35800033c5d700162800,0x38000000040617005a8,0x2120414000800051a47c,0x7284408245860a00000,0x1163c621e15802586458,0x6841c0,0x7583b010e007d81700,0xc6e81320718843800000,0xc0ebc4d802e3213801cb,0x44b80541c464a111a190,0x3426000038710011ed,0x1239c100708006f3c500,0x11e0b00849a1000028,0x35984f804da40800000,0x12c01781c1d003c81470,0x6000050741818b008b8,0xb41000021c3800010,0x4506180001424801800,0x35000000004821800048,0x40010000000058]]
def g181D8 (j : Nat) := if j=0 then 0x2d2720806fd10 else 0
def g181H8 := limbs80 #[#[0x0,0xa0b0000,0x71200000000,0x114000000000e20ae0,0x904000000f243020000,0x0,0x200000000000,0x110103000000cc06d00,0x81100000012201b00,0x1000000000621000]]
def g181D9 (j : Nat) := if j=0 then 0x219080bf else 0
def g181H9 := limbs80 #[#[0x248005aa0000004f586,0xa9e65a24800000000d0,0x38c0013]]
def g181L : Nat → Packing
  | 3 => (2,6,4,0,0,5,0,g181D3)
  | 4 => (14,5,4,0,0,7,0,g181D4)
  | 5 => (38,4,4,0,0,10,0,g181D5)
  | 6 => (18,3,4,0,0,10,0,g181D6)
  | 7 => (5,2,4,0,0,8,0,g181D7)
  | 8 => (1,1,4,0,0,0,0,g181D8)
  | 9 => (1,0,4,0,0,0,0,g181D9)
  | _ => emptyPacking
def g181I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 13 0 12 1 7 g181H4
  | 5 => lookupWord 16 101 5 15 4 7 g181H5
  | 6 => lookupWord 30 163 6 17 6 7 g181H6
  | 7 => lookupWord 17 97 7 16 5 7 g181H7
  | 8 => lookupWord 4 67 0 12 3 5 g181H8
  | 9 => lookupWord 2 17 0 11 0 7 g181H9
  | _ => fun _ => none
def g181 : Forest := ⟨181,9,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P3_0 : block g181 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B3 : block g181 3 0 2=true := g181P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P4_0 : block g181 4 0 14=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B4 : block g181 4 0 14=true := g181P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_0 : block g181 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_4 : block g181 5 4 34=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B5 : block g181 5 0 38=true := (@block_merge g181 5 0 4 34 g181P5_0 g181P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_0 : block g181 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_1 : block g181 6 1 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_7 : block g181 6 7 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B6 : block g181 6 0 18=true := (@block_merge g181 6 0 1 17 g181P6_0 (@block_merge g181 6 1 6 11 g181P6_1 g181P6_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P7_0 : block g181 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P7_3 : block g181 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B7 : block g181 7 0 5=true := (@block_merge g181 7 0 3 2 g181P7_0 g181P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P8_0 : block g181 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B8 : block g181 8 0 1=true := g181P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P9_0 : block g181 9 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B9 : block g181 9 0 1=true := g181P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : checkedTables g181 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0 = true)
  · exact (rfl : block g181 1 0 0 = true)
  · exact (rfl : block g181 2 0 0 = true)
  · exact g181B3
  · exact g181B4
  · exact g181B5
  · exact g181B6
  · exact g181B7
  · exact g181B8
  · exact g181B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 10 := lower_forest (g:=g181) (i:=0) (hints:=2) (before_sound K117 V117) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K117 10 [(181,[]),(213,[101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V117 low181 (by decide +kernel)
def g199Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g199C : List ColumnInfo := [(2,0,197,0,7)]
def g199A : List (List Nat) := [[],[118],[32],[32,118]]
def g199D7 (j : Nat) := if j=0 then 0x3f else 0
def g199L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g199D7)
  | _ => emptyPacking
def g199I (_ _ : Nat) : Option (Nat × Nat) := none
def g199 : Forest := ⟨199,7,fun i => g199Y[i]?.getD (0,0),g199C,g199A,g199L,g199I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199P7_0 : block g199 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g199B7 : block g199 7 0 1=true := g199P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199T : checkedTables g199 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g199 0 0 0 = true)
  · exact (rfl : block g199 1 0 0 = true)
  · exact (rfl : block g199 2 0 0 = true)
  · exact (rfl : block g199 3 0 0 = true)
  · exact (rfl : block g199 4 0 0 = true)
  · exact (rfl : block g199 5 0 0 = true)
  · exact (rfl : block g199 6 0 0 = true)
  · exact g199B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g199G : graphValid g199 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low199 : Lower true (varsX 199) (graphGoal 199) 8 := lower_forest (g:=g199) (i:=0) (hints:=98) (before_sound K181 V181) g199G g199T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K199 := extendKnown K181 8 [(199,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V199 : Known true K199 := extend_ok (m:=199) V181 low199 (by decide +kernel)
def g203Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00fffe3ffc01f,0xe1fe1ffc2d9c500f00f0])),(BitVec.ofNat 152 (word80 [0x5442a2a142480a8541,0x44244009299853333333]))),((BitVec.ofNat 152 (word80 [0x1ffff01ffc7fffe0,0x1ffe1fff13b20f00f0f])),(BitVec.ofNat 152 (word80 [0x1880c0c18081030181,0x88080410212921111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffe0007fffff,0xfe0001ff9e1bc000f00f])),(BitVec.ofNat 152 (word80 [0x6113030213124c2612,0x13089201e12caaaaaaa]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800404040400100804,0x400040000004444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x1808081800603018,0x11811182444688888888]))),(0x0,0x0)]
def g203C : List ColumnInfo := [(1,0,202,0,5),(2,0,201,0,5),(8,0,195,0,5),(128,0,75,0,5)]
def g203A : List (List Nat) := [[],[48,113]]
def g203D6 (j : Nat) := if j=0 then 0x4689f else 0
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
theorem g203G : graphValid g203 (boundsBefore K199) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low203 : Lower true (varsX 203) (graphGoal 203) 7 := lower_forest (g:=g203) (i:=0) (hints:=4150) (before_sound K199 V199) g203G g203T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K203 := extendKnown K199 7 [(203,[]),(206,[32]),(218,[48,113,32,66]),(227,[16,83,67,118]),(230,[16,32,83,67,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V203 : Known true K203 := extend_ok (m:=203) V199 low203 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7fffffe0ffffd80a20,0xb359cf0000ff00ff00ff])),(BitVec.ofNat 152 (word80 [0x2800420110180200,0x8149c805050505050505]))),((BitVec.ofNat 152 (word80 [0x8003fffffff80a51a1,0xdee5700000000000ff00])),(BitVec.ofNat 152 (word80 [0x24b1228048208a51a1,0xde444053535353535353]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffefe3ba,0x24800900ff00ff0000ff])),(BitVec.ofNat 152 (word80 [0xc00b040240262130,0x2480010a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0xffffffff0000209259,0x65fb340000000000ff00])),(BitVec.ofNat 152 (word80 [0x49024c009381208258,0x21bb34acacacacacacac]))),((BitVec.ofNat 152 (word80 [0x24dd46,0xb16d0ff0000ffff0000])),(BitVec.ofNat 152 (word80 [0xe0070081c0200d806,0x2161030303030303030]))),((BitVec.ofNat 152 (word80 [0x1324dd,0x980e26ffffff00000000])),(BitVec.ofNat 152 (word80 [0x70038010e0040104c9,0x180026c0c0c0c0c0c0c0]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,2,53,8,8)]
def g63A : List (List Nat) := [[],[84],[66],[66,82],[82,66],[82],[49],[49,84],[49,66],[49,66,82],[49,82,66],[49,82],[32],[32,84],[32,64],[32,64,80],[32,80,64],[32,80],[32,49],[32,49,84],[32,49,64],[32,49,64,80],[32,49,80,64],[32,49,80],[64,32],[64,32,82],[64],[64,80],[64,82],[64,82,32],[64,49,32],[64,49,32,82],[64,49],[64,49,80],[64,49,82],[64,49,82,32],[80,32,66],[80,32],[80,64],[80],[80,66,32],[80,66],[80,49,32,66],[80,49,32],[80,49,64],[80,49],[80,49,66,32],[80,49,66]]
def g63D8 (j : Nat) := if j=0 then 0x7f else 0
def g63L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g63D8)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,8,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 1=true := g63P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact (rfl : block g63 5 0 0 = true)
  · exact (rfl : block g63 6 0 0 = true)
  · exact (rfl : block g63 7 0 0 = true)
  · exact g63B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K203) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 9 := lower_forest (g:=g63) (i:=0) (hints:=4146) (before_sound K203 V203) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K203 9 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V203 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fffff87fff6a323,0xb48680000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x9402801102206a022,0xa082850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xffe003ffffff0205ed,0x63cb000003f800003f80])),(BitVec.ofNat 152 (word80 [0x2184b08a010422056d,0x224b13264c993264c993]))),((BitVec.ofNat 152 (word80 [0xfffffc0007fffb1ad1,0x92518001fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x200c02c20480912d1,0x12400a142850a142850a]))),((BitVec.ofNat 152 (word80 [0xfffffffff80008caba,0xcb8c00fe000000003f80])),(BitVec.ofNat 152 (word80 [0x4c090130027048ca92,0xc9842c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x92d42,0x4c3f7f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x700e01c04380800d00,0x4c3d3060c183060c1830]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4d414,0x28607ffffffff0000000])),(BitVec.ofNat 152 (word80 [0x801002000400000000,0x4081020408102040]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(1,0,94,0,8),(2,0,93,0,8),(4,0,91,0,8),(8,0,87,0,8),(16,0,79,0,8),(10,0,85,0,7),(0,2,21,72,6),(0,8,21,66,6),(64,0,31,0,6),(3,0,92,0,5),(5,0,90,0,5),(6,0,89,0,5),(8,2,21,64,5),(17,0,78,0,5),(18,0,77,0,5),(20,0,75,0,5),(64,2,21,8,5),(64,8,21,2,5),(21,0,74,0,4),(66,0,21,0,4),(66,8,21,0,4)]
def g95A : List (List Nat) := [[],[66],[49],[49,66],[32],[32,64],[32,49],[32,49,64],[64,32],[64],[64,49,32],[64,49]]
def g95D4 := limbs80 #[#[0x50c8ae1192d915254110,0x30c4ae13925d152d41]]
def g95D5 := limbs80 #[#[0xa8221a2b6460b5454120,0x6454950442cd325b22a4,0x94aa2a5b82848868ee13,0x12214e9921977050910e,0x5dc1424429b32632ee0a,0x4c94cbb82848843e6606,0x2210f9989977050910a7,0x5c86544315ee8c16c8a9,0xc1a84a8a809053ae4184,0x41aa98650b5150120dc5,0x49404839572eb2a84a02,0xa2eaa92809078ae59545,0x1c6b965d55250120e95c,0x55048369706a92a2a824,0xaa4b8aa0904ce6508558,0xe29645515254120da5c1,0x50483a56e8aa2a4a8241,0xa8a92a09059ae5954549,0xab84dd15254120f15b26,0x483c56e9b22a4a82419,0x8a92a09059aa5f645495,0xb745537254120d95c26e,0x48335309ba6e4a8241d2,0xaa2a0905ca64b5455150,0x6460b5454120d55b2305,0x8256f28c36a2a8a41e2b,0x2ea290527e5165dcd514,0x4e0176d452085fca30fb,0x287b283aacab0a418b88,0x2a89062ee13805d95448,0x5c970d5120c74c1301bb,0x13ec9c1ae3aa241cab64],#[0xca9066ae0b80dd165483,0x17159520e55ba6e5b82,0x38e9c1ae2b2a418b874e,0xa90627dd3835c5654831,0x3745952085f4c0e8b8ac,0xf26c0ee8b2a41aab82e0,0xa855ae497454b5054293,0x6258550c9dc22e8a96a0,0x9ba6e0a92a189f84dcd,0x852ee4174d9352543273,0x458b50b1dc82e9b26a4a,0x9018030018af74e096,0x8210781b060150480f03,0x5c16451124410f8360b,0xc88214821d4721a86719,0x4aa29c9f270992588e22,0x8db338cb2f8b62ccb02b,0xfd3e8f73a8e7390e137,0x431094190340,0x8080d05400400000000,0x814003a103a1020648,0x28540040600080050,0x1d182000001a0800,0x11801016168011800800,0x1322c81000000006]]
def g95H5 (j : Nat) := if j=0 then 0xa0a10099 else 0
set_option maxRecDepth 16000 in
def g95D6 := limbs80 #[#[0x54940483aa5954250120,0x4835a5d55250120f2954,0xd915254120e696454950,0x54120d6b74549504839a,0xe3b64d5150482da60b54,0x5d9544822fe1176d4520,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x54110f6952509504432e,0xf6b7254950442de61542,0x549504439ed915254110,0x4439e2195254110b7b84,0xa1f6254110af984d8950,0x54510bbb845c950442be,0xcf774d8951442fce0142,0xdc951442bd6136254510,0x4437a54b70509109f584,0x9977050910cf865dc142,0x509109f985dc1424433e,0xaed8219542443cb55152,0x19542442b760c6550910,0x442b7e0d65509108fd87,0x60a65509108ff8759542,0x509108fd8799542442bb,0xaed82d91524427ee0175,0xd91524432fdd36454910,0x4423fa1f64549108fd87,0xe1574d8910a7d859d952,0x195108ff845d7624423f,0xced845c8654423fe1172,0xdc9654433be117219510,0x4823fe1172995108fd84],#[0xe0d5150120fa94254540,0x50120fa942d4540482f6,0xaf986d4540482fa60b51,0x54940483ea5515250120,0x4837a5d55250120fa984,0xe096550120deb8754940,0x50120ebb8459540483ba,0xf6952545504833ee1d65,0xd4550482f6e0d5154120,0x482fa60b5154120f6952,0x2156154120f695258550,0x54120b7b8558550482de,0xbeb825c550483da54971,0xdc550482f6e0d7154120,0x483da5515254120f6952,0x5915254120f6b5454950,0x54120eeb6454950483ba,0xf6a65549504837add152,0x54950483da5d15254120,0x483da5537254120f6b74,0x5d37254120f6b54dc950,0x54120deb74dc9504837a,0xf3b5455150482fa61372,0x551504836edd15454120,0x483da6095454120afb86,0xe195454120f3b7455150,0x54120be982d51504839e,0xf6982d5150483aed9354,0xd9150483aedd36454120,0x482fae097454120afa87,0x60a6554120deb82dd150,0x54520bf180d4551482fa],#[0xcdd64dcd51482bd61b51,0xdcd5148337d937354520,0x48337d977354520cdd65,0x61b7454520cbf74d9151,0x54520abf84595514823f,0x9df835d9514827ee0176,0xdd9514826fe117654520,0x4837a5c970d45209f980,0x59170d4520deb825c351,0xd4520cfb645c3514833e,0x8fd87593514827ee1170,0x5d3514823f61f64d4520,0x482afe1165d45208ff86,0x61f65d45208ff8759751,0xd4520abf845db514823f,0x9bf845db514827ee0176,0x5db514833ee0176d4520,0x4832fe1176d4520cbc84,0x61e76d45208ff845db51,0x585209f980ddb514823f,0xc7c7559561482afe1165,0x1d5614831fdd56558520,0x4826f61075585209dd83,0x6037155120de9725c154,0x551208fd86dc5544827e,0xe3d65d5154482ee60354,0x59554482af61b5455120,0x4839ee016555120abf84,0xe017655120e3f8459554,0x55120cfb805d954482be,0xde9725c3544833e60376,0x5c354483aed9170d5120],#[0x48277e0d71d5120deb82,0x61764d5120cbf645c754,0xd5120abd87d9354482af,0xe3f84597544839ee0165,0x5db544833ee0176d5120,0x4832fe1175d9120cbf84,0xdd37059520deb72dc165,0x59520cbf76dd1654836e,0xcbf86dd1654836ee0374,0xdc165483badcb7059520,0x483aedd37059520eb874,0xe017159520af984dc165,0x59520adf835c565482be,0xcbf745c5654832f1d171,0xdc565482afe117159520,0x4832fdd37159520cbc74,0xe017459520abe871d165,0x59520ebb80dd165482be,0xcbf81dd1654832f60774,0x5c6654837a5c97099520,0x543dad8952d41509df83,0xe1152d4150d797454b50,0xd4150bbb8458b50542de,0x9fb845cb505437a5cb62,0xd895154357dcd5254550,0x5433b5cb62d4550cdf73,0xdc952585509fb805cb51,0x58550d5f73549615435b,0xabf845896154337dcd62,0x58b6154337dcf6258550,0x5433b5cb62d8550abf84,0xd8b70549508ff845cb61],#[0x54950d7954dc152543ba,0x9f984dc1525435ed5370,0xdc1525432fdd36454950,0x543dae0b7054950f6b62,0xdd37054950d7974dc152,0x54950b7984dc1525435e,0xd3f74d9152542dbe0964,0xd93525439be0b6454950,0x5427ee0174d4950cbd74,0x5d364d4950b6f8259352,0xd4950e3d74d93525434f,0xd7b805d352542dee0174,0xdc1625436e1d37058950,0x5436bdc87458950dbb74,0x60b64d8950dbb80dd162,0x58b50adf835c762542bb,0xafb805d162d42bbe0964,0x5c3515463fe1172d8151,0xd46bee0162583519f782,0x6137258351abf845c960,0x2b821012009c0600023f,0x5851c4e04c846840833c,0x869c68464860c5d05945,0x81c7e07c87447086f06d,0x789188b88a088884c834,0xb04aecab0a74a389d89,0xca8c90c54bf4bb8b7cb4,0x70decdd4d98d5ccfccc0,0x50f90bd038ffcfc0ed0e,0x3753392912551f519513,0x8162157953d5014593d5,0xd89d83d7dd77d71d6bd6],#[0xb85b25ae9aad9e195d8f,0x71d35cf9cbdc81c21bc1,0x1f21f09ecde91e31dadd,0xc60ae09605a01dfbdf8,0x4620a1ce19215611a102,0xe3d23ba37e3422be2822,0x52e4ce4b647a43e42640,0x8a67263661e5e25a656a,0xa7aa76e73271a7026c66,0x9ba97e9428e28a686a80,0xa6afeac2a86a6ea329f6,0xed32cf6cbaca2c42c06b,0xeb2e76e3adfede6daad6,0x7b03efdefa2f66f2aeca,0xb1e31cb16b10b0cf0b70,0x3ab36f3572f72732371f,0xe34cb48f45343b4233e7,0x36275eb5af57353751f4,0x73b72370b6cf6b769f66,0xbb87f8438077a778f777,0x39b797b9639278eb8d38,0xb13ad7a9ba5fa47a0b9f,0xb7c9fc63c4bc0fb8bb4f,0x415240bd5fd47d0bccfc,0x31d8c08181ba4a106120,0x28363b1814e4101e0d05,0x82450441b64080a0f724,0x10903c2040f1e84206f0,0x200401630200068c0b90,0x40d1805001f041000080,0x21161820002002001a30,0x881d10002d16002c0010],#[0x3020804020800407440e,0x40400000080400101810,0x4006039017202e46004e,0x520ac2801b09820ac682,0xd05508302020d041e0d0,0x2b481034041008109020,0x9d1ac680134808294810,0x40020ac21d1900160810,0x244048209068d6105824,0x305c2041202082763210,0x4040500040542c00480a,0x7028005007204087204e,0xa043928500141ae4a10,0x20804083c84103410002,0x1c1030a061408081a0,0xc209056404060804100a,0x2041ac2080c00208041b,0x8080068c1d18282c0040,0x10003a3040c08181018,0x20485a120060007800f0,0x841e002001c204003020,0x78008001d08204008406,0x81010008080000,0x211002047002e0020604,0x20204051408080208081,0x424080a40748080010,0x40f0a80102348c2a008c,0x120648084810309c0080,0x14082815202069010902,0x50a041408481b2308202,0xc2b182000017202e4850,0xc80b0010000258420758],#[0x502038dc2122ac8640e,0x40c0038004003000f001,0xd0010982010400081400,0x1010000002001a306c80,0x24006800a8a8010003,0x40800102800e0010002,0x7440820101020020100,0x4005028ab21903510340,0x720200001e182000000]]
def g95H6 := limbs80 #[#[0x60c3001a18581280080f,0x4b80022031e1004ad90,0xe5d07708005a0000c02,0x4a5841a9883880700c6,0x2005601d026e8f300200,0x5948d8a214143019207,0x9c99326a000400fa0be,0x1417a01ae04a0a0a19c8,0x4a75833a1252cf21c000,0xaf00000006865299ec1a,0x9202440c0057e11122b6,0x30adc1b3a104000001c3,0x49a000023e0004ab8487,0x55222683c414f0200901,0x7e13b03f701c810e8d70,0x1c10a0ec02a692583,0x2ef817689208fc0b0000,0x6835807b815c08c46ae,0x800068ce0982a6000000,0x610d0694132a9f227,0x1c1180000000,0x88273aabb283a1ac1000,0x30600000000017302,0x12c2a0000506e2028062,0x14]]
set_option maxRecDepth 16000 in
def g95D7 := limbs80 #[#[0x26eb98ca884ed7219510,0xf5284a024137dcd6544,0x826eb9ec290769525412,0x2097ae832a413d5c4654,0x4426fb9ac3a84bf74595,0x510df6c4a8221de54950,0x14437bb12a2886f76448,0x8910bf6e0a12217ddc95,0x624427eba6c4884ff745,0x595109fae432a213f5d7,0x9404827eb94ca884ff72,0x254120df2caa0241fa54,0x5150483f5b92a0907e95,0x6454120ef6a8a8241de5,0xdd1504837db22a0906f9,0x970d4520bbee6a8a417e,0xf595544827ebb6a2905f,0xfd7655120cfccaaa2419,0x7e5c3544827fbb2a8904,0x67d65d5120d7ec9aa241,0x13f5d7644827ebb6a890,0x5bf7459520bf6e0b2a4,0x41af1d1654837db82ca9,0x904ff7459520d7ee8b2a,0xa413f5da65482fcb84ca,0xa877952d41509fae932,0xaa177dcd51542fcb96a,0xa4a84fd72d8550bbee6b,0xa92a1dedc152542fdb82,0x6a4a867f64d4950cfec8,0x9b12a16fdd162542beba,0xa2c5a867d64d4b509fae],#[0xe1a8aa33f5cb605467fb,0xa12a0884ff7258351bea,0x6e4a8221fe5c950443fc,0x6a9284887f54254510ff,0xfacaa1221bf19542443f,0x7fb2a84886fe6550910d,0xefaa8a92217f5d542443,0x2ffba2a4886ff6454910,0xdfceca9221bf1d95244,0x83fda8a80907f9515012,0x20ff6a2a8241fe545504,0x483fcb8aa0907f961541,0x120ff2a8a8241fedc550,0x483fcba2a0907fb5454,0x4520ff4caa8241fedd15,0x51483fab0aa2907f7515,0x54520dfac8a8a41f7dcd,0x551482ffba2a2906ff64,0x654520dfecaa8a41bf59,0xc351482ffbb2a2905fd7,0x64d4520dfac9a8a41fe5,0x59751482feba6a2906ff,0xd76d4520dfecba8a41bf,0xf9db51482febb6a2906f,0xfd6558520bfeeda8a41b,0x7fdd561482fe3aac2906,0x5ff7155120ff2e0aa241,0x1bf59554483dfaa2a890,0x6ff7655120dfaecaa24,0x417f5c754483fcb86a89,0x906fd76d5120dfacbaa2,0xa417fdc565483fdb82ca],#[0xa906fe6559520f7ee8b2,0x2a41bfdc5654837eb8ac,0xca906ff7459520dfae8b,0xa82a17f5c665483fcb84,0x2a2a87fb62d4150ff2c5,0x5a8aa1bfd8951543bea9,0x96a2a86ff62d4550efaa,0xc4b0aa1df54961542feb,0xb92c2a86ff6258550dfa,0xac5b0aa1df54b61542ff,0xeb96c2a86ff62d8550df,0xfaa8a92a1fedc152542f,0x7fb22a4a877f5454950e,0xefec8a92a1df59152543,0x2feba6a4a86ff64d4950,0xefec9a92a1df5935254,0x43fdb82c4a877d74d495,0x50dfac8b12a1fbd89625,0x543de3a2c4a86ff64589,0x950bfee8b12a1efdd162,0x25437fb26c4a87fb70d8,0x8950dfae3b12a17f5d36,0x625437eba6c4a86ff71d,0x58b50dfac8b16a1bfdd3,0x162d437eba2c5a85ff74,0x258351dfac4b06a3bfdd,0xc960d477eb92c1a8dff7,0x816008a02e0098001bfd,0xa0da06182b0132086039,0xb850026212208984001d,0x8a1be0d5866030216e0a,0x1d88a041a1fe0f987503],#[0x5822ae14b8a104ca2521,0x19b8cc064a30a1738b40,0x7823a61cb8e006ea35a,0xe22d91208624121ff8f7,0x109e24de26392b091a46,0xa62c195c0a9a53228b94,0x880c1a5f62ef9720b6a5,0x69e34799f0cca64631d9,0x9ba0dc26d63639ad0d52,0xa75a3a39ce0e4270e37b,0x79ef0f6a79e3c79df0ec,0x8a83240da020ff27e63e,0x53a25110a872433a1510,0x1da8e646ba3211828b64,0x4a9a51127a926483a3d1,0x13729a24c7a5e12e2966,0x24ffa7c13c29d24e5a70,0x814a2a3e51ba89143aa1,0xbe553aa51512a7a533a9,0xca163ab0e57fabb15aaa,0xb8a5bbada16aab4659ba,0xafa17b2bd25dfaec1732,0x2c32613b051812c025fb,0xbb2318fac6e62fb15188,0xc2cd6665b2e194ac9e64,0x930023144d0a67fb3c19,0xf00405e4e2c00708451b,0x944860200e5121393881,0x407c2c0101108444203,0x28511c2c010130b00203,0xe4e207c01015930b0396,0x4c562100910018b14404],#[0x85030985100c08261440,0x3159040540c52f0c001,0x4402446408c5a209168b,0x40462e4c008c514131,0x40c4810408c562139317,0x47938f860040287c20aa,0x64c2184440483800a08,0xa151d1820484110d8a1,0x1e02299308408474664,0x22970840c8807c4c2a1c,0xb029040ac2c004a51500,0x180c044851110120c2b0,0x807060301c2c0a4201c,0x1244a092845004293086,0xac2c007060301a42048,0x54012081c180c042a906,0x6e4c20a0f8f0b870228,0x1c08a641b0b022b8f859,0x1c1b8f0b8701908e3c2e,0x80c04487111040121028,0x4c2c0116410170b001c1,0x7801162101044298840,0x1c0101c309f130a87004,0x8b00101a9462763e4e2a,0x1028842726c440a21429,0x1928840f64c0a210444,0xb0060a11a21064c0182b,0x301c064a22229938f868,0xa2204702884040d07060,0x280503080706640301c0,0x8b931680508066085101,0x91b04562812f09101421],#[0x24186c18046091029918,0x1003c7248608528d8a00,0xf43a2810614210e89060,0x42a210090c1a8a003c40,0xc900840244221008182,0x8e083100704402440906,0xe084c484610d0a821611,0x2c283094261468215198,0x2151b082130963c21024,0xc3593082040a640880c,0xa04282192030850d64c2,0xa3c0090a141a8c870040,0x4a313060c8f004c1840b,0xa0644c01314928c4c18,0x4a306a10d128c1a844,0x4001b08406c0084c908f,0xc18928428406a1120e8,0x12843a1051284244c00a,0x844c0068410624c00c29,0x82423c0090a1d93001a,0x28312068700402c2450b,0x42a90224c0088a101b00,0x40081028230b02905120,0x21206108f004c185a4c2,0x8a0f001984312042a90,0x664636112930028324c,0x42b0b01904120419842,0x164620a0c8f00198440a,0xa8c2c183a34010141200,0x92214250a8488440080,0x11450428c882450842a1,0xc2c1a8c8440664a322a],#[0x30b640a8500403130962,0x2890031062a10c188a84,0x1208230034424a2c0102,0xa21435928830f64a2c0,0x864102a899030864804,0x282030a08640c481a20a,0x88424a2082810aa20990,0x228928838aa2083c9302,0xc0a20c890020ac0a2641,0x8420663610c359288324,0x40824c0a211901640419,0xc2190240640823019288,0x64620b0401883c122200,0x19882]]
set_option maxRecDepth 16000 in
def g95H7 := limbs80 #[#[0x50130500b8c101530011,0x9221010062002001420,0x5001021111100000101,0x52811143212300001000,0x1909310100d608012,0x845f000000002232081,0x905260e39434000,0xb4cf145d00000000000,0x54010000309d0000000,0xe018200f703781e9000,0xe0023401e00009011000,0x280,0x0,0x6140000000000000000,0x101300002019000,0x90000c02700000000000,0xf0000000000000000d40,0x50b,0x2000000000000d43b000,0x90be00000000244,0x1074b4d4000,0xa3485000070ec0000000,0xb4cdd48c0000055,0xa025703e000054a0000,0x4015707c00000000000,0xc000000000000801d000,0xcf11a0051d0a40000f0a,0x53a8044b0abb81,0x80000000000000000000,0x4a00000000903db1c,0x91060000000,0x140700000000000],#[0xa4bc34b570dba450000,0x9000092410000000070c,0x600122b6f55,0x10570000000,0x400000000249e0000000,0x679a0d09130e90000b06,0x8094d00cc026753,0xe59a61e4000,0x913ed816c11f000,0xdf0d6000000000000000,0x6110000627ac08e181,0x0,0x0,0x0,0xc000000009406081a000,0x343,0x90000f07100000000000,0xc4abd05520880000480,0xd246f00900003159c11,0x3148000,0x321570cf24390000000,0x0,0x68d40000000,0x10000000051620000000,0xa03b000020eb40c,0xe0000a2c700000000000,0xb075a0de0000844,0xf10d700d800000000000,0x800000000d090a474302,0xb05b00000000349,0x18df19cd00000000000,0x904],#[0x0,0x864900000000000,0x85020000c492000,0x58ce82b1000,0xf0000000000000000000,0xf0dd000040c50000005,0x6000010bca0ba0000000,0x10620000000045cdf03,0x930aa404e905d0000000,0x80000000061290000f4a,0x5000000000000c437f55,0x43eb09700000000023,0x81e600000000000,0xda1ed8cd000,0x608b00000000000,0x0,0x31690000000,0x0,0x704c000054450000000,0x1000040d400000000000,0x70000000091370000d0d,0x5021d153aa26c0bdb08,0x0,0x30000000000000000000,0x206,0x0,0xf000000004041d464000,0xa56c0000715,0x10c80000000,0xe43d0000408f0000000,0x758c000,0xb436000051520000000],#[0xa0000000000000000000,0xac00e00000000040524e,0xf0e14475107a514ac4b,0xd13b60485165b0e2203,0x0,0x440ad08000000000000,0x102400000000000,0x7495000000000000000,0xa089b0a0d0700000000,0x50d0000000000000000,0x4d3000,0x9260f0000201b0000000,0x9f0580000e8190000e05,0x200d100600005117e02,0x558bc4d20000e480000,0x701ca2afc005000,0x8a0d000,0x50500000d0bb000,0x709e00000000000,0x1c6000000000000000,0xa30200000000094bb000,0xe153ee58d0000214ce02,0x3607e00000000e444958,0x7000021550000c08de8d,0x8a00000000000022b,0x60000f00328b4d446000,0x104dc06900000000a01,0xd0e5c0b650d2000,0x90000309ca5370000000,0x57457c0a390b800af753,0xe906600610000b008508,0x747e0000205e402],#[0xb124803cb0a10000000,0x40000000000000000400,0x8e04f80310000000044b,0x3b0350000000010ccc02,0x8000000000000c4c3d07,0x202c00000000409,0x0,0xf05c000,0x5d0c4000020540000000,0x500000000e895e100b0a,0x909,0x2127000,0x30ce00000000000,0x199690b2000,0x200000000000068da000,0x48077017670b7381e109,0xb0780000d10d908,0xb43a000000000000000,0x0,0xa03f40dc0000e0e4000,0xe00008065e09a0000000,0x1500f1c,0x826000030b00000000,0x40a9a89e0000000,0xc060816600000000000,0xf440000040cb000,0x706d0000000,0x8000000000000e067000,0x10e7a103000011d,0x71cd000090c60000000,0x30a600000000458f000,0x9004b06a0000903a000],#[0xf0000115c55790000000,0x2892209,0x9b0b3000062430000000,0x8046501450d5323f224,0x3e646d496e411253b000,0x660b40000b00ba54a604,0xa0073034807,0xf04740e8000,0x76451000000000000000,0xd026de08c00000000301,0x7c096f2c9a557ba0ed0c,0x80000a0b90000328650c,0x60000500a74a4000020a,0x70d30000807dc05a308,0x30820000000091c0000,0x0,0xc597000000000000000,0xd000000e000000000000,0xc46e000000000000e80,0xf02d000,0x0,0x30dad07b00000000000,0x506f00000000000,0x740c00000000a154000,0x3402d55b00000000000,0xaf0c2000000000000000,0x64d5c8740000a13,0xab2aee1db00000000000,0xb0000000014651033a45,0xc0930000b0327994909,0xc0000000000000449d59,0x80c32599413cd06],#[0x84042000010220000000,0x80d98068c07fc43,0x0,0xe0000000000000000000,0x90000000000000000a48,0x2e4cc000000001136b07,0x445990a7100,0x0,0x0,0x20100000aa1d0000000,0xe0530000000,0x947100000000a233000,0x90b5806e9a1a10ae000,0x60000b08100009012000,0xfa1c000030e,0xb0ea0000000,0x0,0x70720000000,0x0,0x661c53049e0df0000000,0xc0000929b00000000c4a,0xb0000f06b62b20000a55,0x15d00000000000071b,0xe01fe04500000000000,0xa0000805634d781d6000,0x845e0000d1c1301,0xad4aad038000004ce000,0xc9a0b10000000060c,0xb0a2d16300000000000,0x7039000,0x0,0x0],#[0x224ac000000000000000,0x545c002bf0830000210,0x504b000000000000000,0x0,0xe040fb0ad00000000000,0x549430990000000038d]]
def g95D8 := limbs80 #[#[0xd48510fe54110b7d8d51,0xd8910bf58910fd54510f,0x9510bf59510bf19510bf,0x120fe50120bfd9510bf9,0x20bf59120bfd8520fe54,0xbf59520bf19520bfd91,0xfed4150bfd9520bf9952,0xfd4950df54950bfd8550,0xd4b50bf58750bfd8950d,0x4551bfd8151bf58b50df,0x910bf58351f7d8d51fdd,0x20ff54520ff54910ff50,0xff55120ff58520ffd45,0xff99520ff59520ffd512,0xf58550ffd4550ff54550,0xd4950ff54950ffd8550f,0x8b50ffd8950ff58950ff,0x2060037000ff58351ff5,0x18615d1340fd0d40ab08,0xb327524521c2011d11af,0x73b038e36533c31a2f12,0x4eb4bb4994694474173e,0x496195e25a456d54451b,0x87a17637337036d368e6,0x90d8e48ad8688388017d,0x145202900e33262c1047,0x500290151400a4040193,0x228a245088a045202e4c,0x405c808262802228e432,0x917262802228b931408a,0x890c1016524264c51480,0xca4854a4090600890cb0],#[0x91020386ca9050c20386,0x2140ca40708080800640,0x10242804480a10386159,0x80b93100224050e1b292,0x5007c995140132628094,0xd911658030ac8472904,0x14020264078834028307,0x480a09908c0219510c45,0x626364c5804050c364c,0x48511931208a283c98b0,0x825222811480e884908a,0x251c5444818a42809488,0xb129490d1120a110a0,0x48848706010468491242,0x24311090e0c046848122,0x121031e12430885031e1,0xa0084a423890a0102831,0x27262809480e91109890,0x1208a00f931404a40528,0x8981905114440623931e,0x8a00e9089015931e1808,0xb911118040522431e1c8,0x3262402228]]
set_option maxRecDepth 16000 in
def g95H8 := limbs80 #[#[0x3a07804fa020102c7c03,0x804060002c430001436,0xc80400020086c0711000,0x30101e04010005a08091,0x94e85c04081d00004f22,0x445810002d2f990003,0x5100a010e810040b0000,0x8000e1a130082a387a83,0x79c9020020303c082e26,0x2902806240c13ddf480d,0x4a2b0200c2831831a414,0x106bd17d42b646e6c2a8,0x400dc0cd89b982978157,0x81efd03846739152c07c,0x456609cf003ce0d8c962,0xc95f0a6040a18093816d,0x23800014501949bd56d,0x220c14e516dd1dd8579,0xd10f8189d07446540003,0x77409a82d195e00003,0xc1680001ca4c00029497,0x414ac18e10d922900003,0x40605080c24a84500001,0x4273863bc01cd05d422c,0x4299d4590010000302bf,0x9100000001d4c1fa4126,0x1c680c8946800020572,0xd0d090b5845d8633d4a7,0x4175e2476133c4796138,0xc15c00010a3f867fc2a3,0x829151f5c180148e801a,0x688020d8455c96855b7],#[0x4a12071c4ecc2c3419a,0xc575915d45ff4a4085aa,0xc5b881f784d5210c095b,0x44034a18443a127d0265,0x50afc219c4d0c04700c4,0x292e019540be005c41be,0x269310677c1d1,0x44c891cc0815249899c,0x5a58c543c229803481e2,0xff843080e740e06947,0xa08e13f855b00d100ab,0xc00542258137526a41b5,0xc6e8864f40940003147f,0x90e7427fc0b4c1115058,0x4818c275c67810e889d1,0x3011dc043c09d80ef,0x8152c48400035207d588,0xc56c109841ca2114,0x847d8637412e15810024,0x825401c2c10a4203c28a,0x8166d1735073906f06df,0x802f86604ac0c2128105,0xc2e495e9851c0170c06e,0xd5f701388070862c0243,0x4a382284a12000f5c2dd,0x4a4aa939548982d78569,0x4a14e0f6915741ea0a29,0x41b1c2c500a509ae41df,0x1001595820b425dc050,0x42858469603e859980ad,0x4118582ac9180000c2a7,0x98f8648404c01f381d9],#[0x50c7502ac2cf40e94683,0xb80000612f55e401cd,0x458a826b421682040003,0x9a042d811aac459c143,0x408d06e2c26ec956c29d,0xa12400028033811486a1,0x89fb49e3018609654a5d,0x41b8000102b00002d161,0xc1af292700b000014436,0x1a186588829c0d40001,0x1798583899bd602c251,0x4f1c42bc68e403b8000,0x80dc0002515a293e855e,0x1019e407ac25a442e,0x899180d80089413e1a48,0x8640828c0001024c0001,0x81e40001c0540132,0x283c246c0f000030028,0xc52481aa42794512c50a,0x1614650d45f103295df,0x848086640000863f6914,0x92240000603a00488488,0x821cc06515f80001005b,0x644ca5bc1a6c4e142ca,0xc23f815b55efc5e8c009,0x41200001c0fac46c0015,0x85c34a5082e2810cc952,0x10262865f0a36,0xcabf81ffd0ec00848518,0x814455f31276c23349bc,0x406b1244002349b042e9,0xe14782aea83f1259017c],#[0x52790192c235c0c0c2ba,0x2012b]]
def g95D9 := limbs80 #[#[0xd51ffa87f543fa41fd10,0x51b0259b138a803fea3f,0x410202548526489000,0x101464648a50101a48a5,0x248a02051549228]]
def g95H9 := limbs80 #[#[0x84c0051e081030404100,0x1e9833c44009040089a1,0xd81500010aa022ca0112,0x207800004b7004f07,0x20f047c2d00000005048,0x2d28402a215f05a88c79,0xb0880000003028000086,0x1c087928d2070003870,0xa0e9f3180c562428000c,0x7131780c04400bec6eb4,0x4037140a290000da0415,0x6d807045900000000002,0x700010ab000210bb00b8,0xa1ef1b040f285b01,0x24a2508dc100000094,0x51b4881488809d44b0,0xd161000380bc0af62d00,0x54780000000421a86,0x60360610003c060000,0xc004000000201450c00,0x3142972a3962306800,0x230000502400090c4000,0x93045508222850009088,0x68980000000110981bb5,0xc258206565006101644a,0x300000000000000da80,0xe80380004093c8498201,0x801680a0098d07445ac2,0x1051207661f32a5813,0x1c0851bc819000042c0]]
def g95D10 (j : Nat) := if j=0 then 0x2080513f else 0
def g95H10 := limbs80 #[#[0xc21b0247a8950714980,0x480000090ec1800001d4,0x50a0a8810000009,0xa0450000589e20002828,0x580]]
def g95L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g95D4)
  | 5 => (57,5,5,0,0,10,0,g95D5)
  | 6 => (237,4,5,0,0,12,0,g95D6)
  | 7 => (187,3,5,0,0,13,0,g95D7)
  | 8 => (50,2,5,0,0,12,0,g95D8)
  | 9 => (6,1,5,0,0,8,0,g95D9)
  | 10 => (1,0,5,0,0,0,0,g95D10)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 8 1 3 g95H5
  | 6 => lookupWord 25 127 7 14 6 4 g95H6
  | 7 => lookupWord 111 1123 4 16 8 4 g95H7
  | 8 => lookupWord 98 431 9 16 8 4 g95H8
  | 9 => lookupWord 28 157 7 14 6 4 g95H9
  | 10 => lookupWord 4 31 3 11 3 4 g95H10
  | _ => fun _ => none
def g95 : Forest := ⟨95,10,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B4 : block g95 4 0 2=true := g95P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_1 : block g95 5 1 56=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 57=true := (@block_merge g95 5 0 1 56 g95P5_0 g95P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_13 : block g95 6 13 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_109 : block g95 6 109 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_205 : block g95 6 205 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 237=true := (@block_merge g95 6 0 109 128 (@block_merge g95 6 0 13 96 g95P6_0 g95P6_13) (@block_merge g95 6 109 96 32 g95P6_109 g95P6_205))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_10 : block g95 7 10 59=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_69 : block g95 7 69 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_165 : block g95 7 165 22=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 187=true := (@block_merge g95 7 0 69 118 (@block_merge g95 7 0 10 59 g95P7_0 g95P7_10) (@block_merge g95 7 69 96 22 g95P7_69 g95P7_165))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_1 : block g95 8 1 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_31 : block g95 8 31 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 50=true := (@block_merge g95 8 0 1 49 g95P8_0 (@block_merge g95 8 1 30 19 g95P8_1 g95P8_31))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P9_0 : block g95 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B9 : block g95 9 0 6=true := g95P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P10_0 : block g95 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B10 : block g95 10 0 1=true := g95P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact g95B4
  · exact g95B5
  · exact g95B6
  · exact g95B7
  · exact g95B8
  · exact g95B9
  · exact g95B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 11 := lower_forest (g:=g95) (i:=0) (hints:=4146) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 11 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff60acd,0x4aee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060884,0xce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe021d28,0x11d9d70003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208221d28,0x1c941264c993264c993]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0ca,0x83210b01fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x400c0160809009404a,0x12103142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f6,0x691ab2fe000000003f80])),(BitVec.ofNat 152 (word80 [0x8090098004e04820c6,0x6012b258b162c58b162c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x93711,0xa287740000000fffc000])),(BitVec.ofNat 152 (word80 [0x2e02e011700803711,0xa28214e1c3870e1c3870]))),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801008011,0x1e000481020408102040]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(32,0,79,0,8),(1,0,110,0,7),(2,0,109,0,7),(4,0,107,0,7),(8,0,103,0,7),(0,2,37,72,6),(0,8,37,66,6),(0,32,74,5,6),(64,0,47,0,6),(1,32,74,4,5),(2,8,37,64,5),(4,32,74,1,5),(10,0,101,0,5),(64,2,37,8,5),(64,8,37,2,5),(5,0,74,0,4),(5,32,74,0,4),(66,0,37,0,4),(66,8,37,0,4)]
def g111A : List (List Nat) := [[],[49],[32],[32,49]]
def g111D5 := limbs80 #[#[0xd935148327d937354520,0x308bd87]]
def g111D6 := limbs80 #[#[0x25ebaec8907695254120,0xfd6e4a8241fa5495048,0x82efb9aa2906bf644c52,0x20bf2e1a8a41afd91514,0x4827ebb6a2906bf64d45,0x950bf6e0a92a1bedc165,0xb0027fb92c1a8f7b7054,0xc632c144943f1c0c4441,0xb142207803c687401e4d,0xa8811004238040307071,0x81e8820306901c1c00,0x201100780402070]]
def g111H6 (j : Nat) := if j=0 then 0x18000120 else 0
def g111D7 := limbs80 #[#[0xf55350cf55150afd9120,0x59351b7d8d51af59350c,0x9520fe54120bfd8910af,0x950dfd4950df54950bf5,0x51bf58b50ef55150bfd8,0xff54520ff4c520bf583,0xff58950ff54950ffd452,0x881198520a400ffd8950,0xdec6f1855712c40cda2a,0x711bf6e2aae829662281,0xc83b10d202e4c50c3c11,0x843601a2c11a2c31a402,0x8234595931c210246c7,0xb0101a345c02080a1b26,0x1a38e1b811c114305080,0x60a101101878e1307023,0x42071c34806386900f00,0x450600c0a2a107925608,0x141808078e920c022145,0x82012020160104031215]]
def g111H7 := limbs80 #[#[0x2d653000f340000073,0xe1c000000000083,0x8b000520000000000085,0x0,0xd8d2a8999c01,0x4b6102b70800002c0,0xa80000000b1800]]
def g111D8 := limbs80 #[#[0xf50fea87f483fa21bd54,0x685400ffa8ff547fa63f,0x2238d4069c439c8c0481,0x489020308a90180d1e40,0x92388e04d80720614182,0xa30a180c3460ce060345,0x12a48022071238458121,0x8e]]
def g111H8 := limbs80 #[#[0xcc71042f9890db006305,0xe1558000223e08006,0xc001a3800000428c4cca,0x304d83030005cea0,0x8780070100f214940000,0x40100083b4991282141d]]
def g111D9 (j : Nat) := if j=0 then 0x41882017f else 0
def g111H9 := limbs80 #[#[0x6980001a4000000000,0x5880001010000152,0x6f00000,0x0,0x28c00000,0x200000000000000000,0x80000000000000ca0000,0x2e40000204974e001313]]
def g111L : Nat → Packing
  | 5 => (2,4,5,0,0,3,0,g111D5)
  | 6 => (14,3,5,0,0,9,0,g111D6)
  | 7 => (21,2,5,0,0,10,0,g111D7)
  | 8 => (8,1,5,0,0,9,0,g111D8)
  | 9 => (1,0,5,0,0,0,0,g111D9)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 7 0 5 1 0 g111H6
  | 7 => lookupWord 5 53 2 10 4 2 g111H7
  | 8 => lookupWord 7 41 4 11 5 2 g111H8
  | 9 => lookupWord 3 79 0 9 3 2 g111H9
  | _ => fun _ => none
def g111 : Forest := ⟨111,9,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : block g111 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B5 : block g111 5 0 2=true := g111P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : block g111 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_2 : block g111 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B6 : block g111 6 0 14=true := (@block_merge g111 6 0 2 12 g111P6_0 g111P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_6 : block g111 7 6 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_15 : block g111 7 15 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 21=true := (@block_merge g111 7 0 6 15 g111P7_0 (@block_merge g111 7 6 9 6 g111P7_6 g111P7_15))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8_0 : block g111 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8_1 : block g111 8 1 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B8 : block g111 8 0 8=true := (@block_merge g111 8 0 1 7 g111P8_0 g111P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P9_0 : block g111 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B9 : block g111 9 0 1=true := g111P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact g111B5
  · exact g111B6
  · exact g111B7
  · exact g111B8
  · exact g111B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 10 := lower_forest (g:=g111) (i:=0) (hints:=4146) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 10 [(111,[]),(123,[66]),(126,[32,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801ffe0fffffffe88,0x6981b4940007c00f83ff])),(BitVec.ofNat 152 (word80 [0x501401420080010280,0x68010014210842108421]))),((BitVec.ofNat 152 (word80 [0xfffe0000ffc1ff8195,0xf117528800f800000000])),(BitVec.ofNat 152 (word80 [0x611855842504520995,0xf1155281ef7bdef7bdef]))),((BitVec.ofNat 152 (word80 [0xffffffff0001fffcd7,0x856045441f0001f07c1f])),(BitVec.ofNat 152 (word80 [0x802006000608040050,0x81404440421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2e5c7a23e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x4018000800181021,0x4043a00842108421084]))),((BitVec.ofNat 152 (word80 [0x44,0x90bf89b000003fff8000])),(BitVec.ofNat 152 (word80 [0x5816008b011602004,0x10ba81a318c6318c6318]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x6018010c02180400a,0x28a010a108421084210]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(0,2,53,64,8),(2,0,117,0,8),(32,0,87,0,8),(1,0,118,0,7),(4,0,115,0,7),(16,0,103,0,7),(64,2,53,0,7),(5,0,114,0,4),(17,0,102,0,4),(20,0,99,0,4)]
def g119A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g119D6 := limbs80 #[#[0x25fba2c6907c9324c120,0xd7ee8b1a416fdd16348,0x820bc527287d86bf1180,0x171e01e3e3c03e3d]]
def g119D7 := limbs80 #[#[0xfd8d20bf58d20fe4c120,0x690884603600ff58d20b,0x2481f1cb61881c3c7257,0x78d2571c08571cb61c5,0x92]]
def g119H7 (j : Nat) := if j=0 then 0x6240e07 else 0
def g119D8 (j : Nat) := if j=0 then 0xf1a9072b0ffd20 else 0
def g119H8 := limbs80 #[#[0x13000000002200000000,0x5018a1]]
def g119D9 (j : Nat) := if j=0 then 0x5413261bf else 0
def g119H9 (j : Nat) := if j=0 then 0x284d5 else 0
def g119L : Nat → Packing
  | 6 => (4,3,4,0,0,7,0,g119D6)
  | 7 => (4,2,4,0,0,8,0,g119D7)
  | 8 => (1,1,4,0,0,0,0,g119D8)
  | 9 => (1,0,4,0,0,0,0,g119D9)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 7 0 6 2 0 g119H7
  | 8 => lookupWord 1 13 0 8 2 2 g119H8
  | 9 => lookupWord 1 3 0 6 0 2 g119H9
  | _ => fun _ => none
def g119 : Forest := ⟨119,9,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_2 : block g119 6 2 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 4=true := (@block_merge g119 6 0 2 2 g119P6_0 g119P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_3 : block g119 7 3 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 4=true := (@block_merge g119 7 0 3 1 g119P7_0 g119P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : block g119 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B8 : block g119 8 0 1=true := g119P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P9_0 : block g119 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B9 : block g119 9 0 1=true := g119P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
  · exact (rfl : block g119 5 0 0 = true)
  · exact g119B6
  · exact g119B7
  · exact g119B8
  · exact g119B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 10 := lower_forest (g:=g119) (i:=0) (hints:=98) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 10 [(125,[49]),(237,[49,116]),(249,[49,66,114]),(252,[32,49,64,16,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff60ac8,0x4caee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060880,0x400ce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe021c2c,0x13d9d30003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208221c28,0x3c941264c993264c993]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0cb,0x81210b01fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x400c0160809009404a,0x12103142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x691ab200000000003f80])),(BitVec.ofNat 152 (word80 [0x8290298014e04820d7,0x6812b2d9b366cd9b366c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803700,0xa2821060c183060c1830]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801008015,0x1c000481020408102040]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(0,8,149,2,8),(8,0,151,0,8),(1,0,158,0,7),(2,8,149,0,7),(4,0,155,0,7),(16,0,143,0,7),(128,0,31,0,6),(5,0,154,0,4),(17,0,142,0,4),(20,0,139,0,4)]
def g159A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g159D4 (j : Nat) := if j=0 then 0x1a2b6460b5454120 else 0
def g159D5 := limbs80 #[#[0x50940483aa5954250120,0x483ca5515250120eab65,0x5915254120d697554940,0x54120e6b64549504839a,0xb6982d51504835add152,0x5d9544838ed935454120,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x8d01d345ca0d141c032e,0x8080002836294c]]
def g159H5 (j : Nat) := if j=0 then 0xfb4 else 0
def g159D6 := limbs80 #[#[0x3b4a92a0907a94250120,0xfd2a4a02412fdd16548,0x837db2a80906f9655012,0x20fd6e4a8241fa549504,0x483bdaa2a09077954541,0x120df6c8a8241be59150,0x44833eb2aa8905fb7454,0x51209feecaa2413f5d95,0x544835fb26a8905f970d,0x591209faedaa2419f597,0x1654827ebaec8904ff75,0x59520b7ee8b2a417edc,0xd1654835e3a2ca906fb7,0x70995209fee8b2a41afd,0x5d3654827ebb4ca905f9,0xb7054950bf6e0a92a13f,0xfd93525433fb22a4a877,0xbf7458950afae9a92a19,0x3fdd162d427eba6c4a85,0x78a8431e4d85f258a401,0x5610fb7aba1b6d564309,0x75a2b74ea0cee5d288dc,0xee46ef5da1cde3b037bb,0x8178f049085f3f6ba9c,0x82141100f1e010649ce1,0x810000808205c7806102,0x80101c4080141c80801,0x400e0e2043820700400a,0x8604002005041020050,0x35040000a8]]
def g159H6 := limbs80 #[#[0x11310228b1428030165d,0x1614005495016c104,0x1544013b062192980000,0xe8dc5897566ac4001076,0x4007aa412a08002ac729,0x81c2920924]]
def g159D7 := limbs80 #[#[0xf59120fe54120fe50120,0xd9520bf59520bfd9120b,0x8950dfd4950df54950bf,0x120ff55120bf58b50bfd,0x20ff59520ff59120ffd5,0xff58950ff54950ff995,0x90ba2585a0c000ffd895,0xc9ce691865a144481023,0xb1c159079aa528ba107,0x648b3242c461f3906207,0x3186c55cc7149207c465,0x522105c731c4c4792217,0x54d62cc51e2cd41851b3,0x51c6185887105506cc4c,0x88710920789516245019,0xf1c065221624501c4195,0x60940c75540]]
def g159H7 := limbs80 #[#[0x2d0210200b00c50040,0x92280400000079480000,0xe060003078000ac40002,0x3124000,0x1689241b024000000285,0x38000024000c42000000,0xb4c0000000e4510,0x61c000333c0,0x12200000000000,0x6854,0x3406000,0x101,0x888000000000000,0xd01098000020e14f0400,0x837c0200000000000014,0x18989860000004,0x3042,0x1e9f0000000000000000,0x110000000,0x821f2170452a100,0x605f836000e3100000,0xf23d6680000000000,0xa160000000,0x384bec8000000000049c,0x414c8a000180,0x900000000000000001ca,0xd0ef240517c0cc0580,0x13389be0e000000100a0,0x206b9a66117308,0x8001c4721fd0c000092c,0x140ff0c]]
def g159D8 := limbs80 #[#[0xc79aa407fd43faa1fd20,0x98d13568298d131ea414,0x1ad046]]
def g159H8 := limbs80 #[#[0x1241028405,0x30c00000000000,0x94174020b000000000,0xa26000e09d2f0000001,0xe6b00000000000,0x311910d47000,0x1000000000000d030000,0x10a00000000000000043,0x90e000,0xde0fc6a000e30508b040,0xa27628000c21b06729d0,0xd01000f05000b87000,0x1070]]
def g159D9 (j : Nat) := if j=0 then 0x1542317f else 0
def g159H9 := limbs80 #[#[0xc2000000000007a80000,0x64000012400840000201,0x104000078db2]]
def g159L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g159D4)
  | 5 => (13,4,4,0,0,7,0,g159D5)
  | 6 => (39,3,4,0,0,9,0,g159D6)
  | 7 => (18,2,4,0,0,10,0,g159D7)
  | 8 => (3,1,4,0,0,7,0,g159D8)
  | 9 => (1,0,4,0,0,0,0,g159D9)
  | _ => emptyPacking
def g159I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 6 0 2 g159H5
  | 6 => lookupWord 7 37 5 11 4 3 g159H6
  | 7 => lookupWord 18 181 4 13 6 3 g159H7
  | 8 => lookupWord 8 83 2 12 5 3 g159H8
  | 9 => lookupWord 2 23 0 9 2 3 g159H9
  | _ => fun _ => none
def g159 : Forest := ⟨159,9,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P4_0 : block g159 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B4 : block g159 4 0 1=true := g159P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P5_0 : block g159 5 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B5 : block g159 5 0 13=true := g159P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_0 : block g159 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_3 : block g159 6 3 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B6 : block g159 6 0 39=true := (@block_merge g159 6 0 3 36 g159P6_0 g159P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_0 : block g159 7 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_10 : block g159 7 10 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B7 : block g159 7 0 18=true := (@block_merge g159 7 0 10 8 g159P7_0 g159P7_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P8_0 : block g159 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B8 : block g159 8 0 3=true := g159P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P9_0 : block g159 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B9 : block g159 9 0 1=true := g159P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : checkedTables g159 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g159 0 0 0 = true)
  · exact (rfl : block g159 1 0 0 = true)
  · exact (rfl : block g159 2 0 0 = true)
  · exact (rfl : block g159 3 0 0 = true)
  · exact g159B4
  · exact g159B5
  · exact g159B6
  · exact g159B7
  · exact g159B8
  · exact g159B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 10 := lower_forest (g:=g159) (i:=0) (hints:=4146) (before_sound K119 V119) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K119 10 [(159,[]),(175,[84]),(187,[66,82]),(190,[32,64,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V119 low159 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffc3ffffffe6,0xa43b0800007c00f83ff])),(BitVec.ofNat 152 (word80 [0x28140288040020c2,0xa031004210842108421]))),((BitVec.ofNat 152 (word80 [0x1ffffe0003fe1ff045,0x3d4b4e8000f800000000])),(BitVec.ofNat 152 (word80 [0x4ab118ab11284a4245,0x3d4b4ebdef7bdef7bdef]))),((BitVec.ofNat 152 (word80 [0x1ffffffffc001fff38,0xf46918001f0001f07c1f])),(BitVec.ofNat 152 (word80 [0x80c0200c0030808038,0x54400808421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xaa846f83e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x30040300040030400,0xa0046390842108421084]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c021810c0804,0x1b88421084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201000200100000,0x42108421084210]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(2,0,181,0,10)]
def g183A : List (List Nat) := [[],[84],[66],[66,82],[82,66],[82],[32],[32,84],[32,64],[32,64,80],[32,80,64],[32,80],[64,32],[64,32,82],[64],[64,80],[64,82],[64,82,32],[80,32,66],[80,32],[80,64],[80],[80,66,32],[80,66]]
def g183D10 (j : Nat) := if j=0 then 0x7f else 0
def g183L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g183D10)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,10,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P10_0 : block g183 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B10 : block g183 10 0 1=true := g183P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
  · exact (rfl : block g183 5 0 0 = true)
  · exact (rfl : block g183 6 0 0 = true)
  · exact (rfl : block g183 7 0 0 = true)
  · exact (rfl : block g183 8 0 0 = true)
  · exact (rfl : block g183 9 0 0 = true)
  · exact g183B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 11 := lower_forest (g:=g183) (i:=0) (hints:=114) (before_sound K159 V159) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K159 11 [(183,[]),(221,[49,117,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V159 low183 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff801ffffe1fffd0b7,0x1c14b00003f00003f03f])),(BitVec.ofNat 152 (word80 [0x450940500441105096,0xc00b145145145145145]))),((BitVec.ofNat 152 (word80 [0xffffe007fffff85c0a,0x958b5000fc0000fc0fc0])),(BitVec.ofNat 152 (word80 [0x160181602800215802,0x948940c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfffffff8001fffbb68,0x3851603f00003f00003f])),(BitVec.ofNat 152 (word80 [0x98020180b082400b68,0x3011428a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000063f,0xaa631000000fc0000fc0])),(BitVec.ofNat 152 (word80 [0xe04c1204c01382063d,0x2a621b2cb2cb2cb2cb2c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x984,0x66280fc0000ffffff000])),(BitVec.ofNat 152 (word80 [0x1004010004000000,0x410410410410410]))),((BitVec.ofNat 152 (word80 [0x6651,0x43c4cffffff000000000])),(BitVec.ofNat 152 (word80 [0x6018060118042401,0x43440820820820820820]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,8),(8,0,199,0,8),(128,0,79,0,8),(1,0,206,0,7),(4,0,203,0,7),(64,0,143,0,7),(5,0,202,0,5),(65,0,142,0,4),(68,0,139,0,4)]
def g207A : List (List Nat) := [[],[32]]
def g207D6 := limbs80 #[#[0xe3c1243e437a94250120,0x5]]
def g207D7 := limbs80 #[#[0xf50940bf59120fe50120,0x42a00ff58940bfd8940e,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c70c871]]
def g207H7 (j : Nat) := if j=0 then 0xa0 else 0
def g207D8 := limbs80 #[#[0xa38c2461a403fa81fd20,0x1e851c6121c]]
def g207H8 := limbs80 #[#[0x430000b8d100d000f200,0xe4]]
def g207D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g207H9 (j : Nat) := if j=0 then 0x5000010009c0 else 0
def g207L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g207D6)
  | 7 => (5,2,4,0,0,8,0,g207D7)
  | 8 => (2,1,4,0,0,6,0,g207D8)
  | 9 => (1,0,4,0,0,0,0,g207D9)
  | _ => emptyPacking
def g207I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g207H7
  | 8 => lookupWord 1 11 0 8 3 1 g207H8
  | 9 => lookupWord 1 11 0 6 1 1 g207H9
  | _ => fun _ => none
def g207 : Forest := ⟨207,9,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P6_0 : block g207 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B6 : block g207 6 0 1=true := g207P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_0 : block g207 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_4 : block g207 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B7 : block g207 7 0 5=true := (@block_merge g207 7 0 4 1 g207P7_0 g207P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P8_0 : block g207 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B8 : block g207 8 0 2=true := g207P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P9_0 : block g207 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B9 : block g207 9 0 1=true := g207P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact (rfl : block g207 4 0 0 = true)
  · exact (rfl : block g207 5 0 0 = true)
  · exact g207B6
  · exact g207B7
  · exact g207B8
  · exact g207B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 10 := lower_forest (g:=g207) (i:=0) (hints:=4146) (before_sound K183 V183) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K183 10 [(207,[]),(219,[66]),(222,[32,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V183 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf87ffe01ff8fffffe4,0x13c7300000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x110014140520200420,0x11c13084210842108421]))),((BitVec.ofNat 152 (word80 [0xff87fffe000ff1fe09,0x4badd0001f0001f00000])),(BitVec.ofNat 152 (word80 [0xa01158185641444889,0x4badd39ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0x7fffffff001ffc7,0xaa986003e0003e007c1f])),(BitVec.ofNat 152 (word80 [0xc22060201801881007,0x82184108421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffe0012,0x6c4f807c0007c0007fe0])),(BitVec.ofNat 152 (word80 [0x44180406002006110,0x6c068210842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800000000000029,0x84009f800007ffff8000])),(BitVec.ofNat 152 (word80 [0x200808004008000,0x421084210842108]))),((BitVec.ofNat 152 (word80 [0x10,0x51304ffffff800000000])),(BitVec.ofNat 152 (word80 [0x401010008010000,0x842108421084210]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(2,0,213,0,10)]
def g215A : List (List Nat) := [[],[118],[66],[66,118],[32],[32,118],[32,64],[32,64,118],[64,32],[64,32,118],[64],[64,118]]
def g215D10 (j : Nat) := if j=0 then 0x7f else 0
def g215L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g215D10)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,10,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P10_0 : block g215 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B10 : block g215 10 0 1=true := g215P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact (rfl : block g215 4 0 0 = true)
  · exact (rfl : block g215 5 0 0 = true)
  · exact (rfl : block g215 6 0 0 = true)
  · exact (rfl : block g215 7 0 0 = true)
  · exact (rfl : block g215 8 0 0 = true)
  · exact (rfl : block g215 9 0 0 = true)
  · exact g215B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 11 := lower_forest (g:=g215) (i:=0) (hints:=98) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 11 [(215,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffc3ffffffea,0xa41b1800007c00f83ff])),(BitVec.ofNat 152 (word80 [0x28140288040020ca,0xa011004210842108421]))),((BitVec.ofNat 152 (word80 [0x1ffffe0003fe1ff04d,0x2ccb4a8000f801f00000])),(BitVec.ofNat 152 (word80 [0x42b0182b1028424249,0x2ccb489ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0x1ffffffffc001fff30,0xf4691c001f003e007c1f])),(BitVec.ofNat 152 (word80 [0x80c0200c0030808030,0x44680808421084210842]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xab846f83e00000007fe0])),(BitVec.ofNat 152 (word80 [0xb0140b001400b0400,0xa18467b18c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c021810c0804,0x11108721084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201000200100000,0x42108421084210]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(2,0,229,0,8),(32,0,199,0,8),(64,0,167,0,8),(1,0,230,0,7),(4,0,227,0,7),(128,0,103,0,7),(0,2,37,192,6),(3,0,228,0,5),(5,0,226,0,5),(128,2,37,64,5),(129,0,102,0,4),(132,0,99,0,4)]
def g231A : List (List Nat) := [[],[32]]
def g231D5 (j : Nat) := if j=0 then 0x2f4e0d7254110 else 0
def g231D6 := limbs80 #[#[0x379b12a0887715254110,0x9bee6b2a41da5495048,0x436fb9aca907f1725411,0x471eda96520177dcd625,0x2d03f211a0ae22790b61,0x2c98f970104f1e4204e,0x41622]]
def g231H6 (j : Nat) := if j=0 then 0x4 else 0
def g231D7 := limbs80 #[#[0xdd8910bd58910fc54110,0x59520fe54120fd54910b,0x8950bfd8950df54950bf,0xa379688a331205400ff5,0x479122141e98e448d388,0x3298c79122e2a64388a,0x41656046588c52a4e391,0x618e450a5942e18e4a46,0x16522408a]]
def g231H7 := limbs80 #[#[0xa500004266b000581123,0x5400]]
def g231D8 := limbs80 #[#[0x88a4b807f543fa41f510,0x1ca3846481807356838c,0x2a851c612]]
def g231H8 := limbs80 #[#[0xa3c28008200000000000,0xa380249c60000001,0x73d0750,0x62040]]
def g231D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g231H9 (j : Nat) := if j=0 then 0x16007200bb249 else 0
def g231L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g231D5)
  | 6 => (7,3,4,0,0,8,0,g231D6)
  | 7 => (9,2,4,0,0,9,0,g231D7)
  | 8 => (3,1,4,0,0,7,0,g231D8)
  | 9 => (1,0,4,0,0,0,0,g231D9)
  | _ => emptyPacking
def g231I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g231H6
  | 7 => lookupWord 2 13 0 8 3 1 g231H7
  | 8 => lookupWord 2 29 0 9 4 1 g231H8
  | 9 => lookupWord 1 7 0 7 2 1 g231H9
  | _ => fun _ => none
def g231 : Forest := ⟨231,9,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P5_0 : block g231 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B5 : block g231 5 0 1=true := g231P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_0 : block g231 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P6_4 : block g231 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B6 : block g231 6 0 7=true := (@block_merge g231 6 0 4 3 g231P6_0 g231P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_3 : block g231 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_8 : block g231 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 9=true := (@block_merge g231 7 0 3 6 g231P7_0 (@block_merge g231 7 3 5 1 g231P7_3 g231P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_0 : block g231 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_1 : block g231 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B8 : block g231 8 0 3=true := (@block_merge g231 8 0 1 2 g231P8_0 g231P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P9_0 : block g231 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B9 : block g231 9 0 1=true := g231P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact g231B5
  · exact g231B6
  · exact g231B7
  · exact g231B8
  · exact g231B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 10 := lower_forest (g:=g231) (i:=0) (hints:=98) (before_sound K215 V215) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K215 10 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V215 low231 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffffffe077ae,0xa0072800000fc003ffc0])),(BitVec.ofNat 152 (word80 [0x81500a02400042338a,0xa00300030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfff800ffe0ffff3842,0x876ab28003f000fc003f])),(BitVec.ofNat 152 (word80 [0x604c008204803002,0x542b205145145145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb85846c000003f00003f])),(BitVec.ofNat 152 (word80 [0x2184108b0489000d84,0xb81804eaaaaaaaaaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc0fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xa01602c002e048045,0x154a9dc71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088071,0x204810410410410410]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104c00,0x4a800420820820820820]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,7),(2,0,233,0,7),(8,0,227,0,7),(32,0,203,0,7),(64,0,171,0,7),(128,0,107,0,7),(0,8,161,66,6),(0,32,74,129,6),(1,32,74,128,5),(2,8,161,64,5),(9,0,226,0,5),(33,0,202,0,5),(40,0,195,0,5),(64,8,161,2,5),(72,0,163,0,5),(128,32,74,1,5),(3,0,232,0,4),(41,0,194,0,4),(65,0,170,0,4),(66,0,161,0,4),(66,8,161,0,4),(74,0,161,0,4),(129,0,74,0,4),(129,32,74,0,4),(130,0,105,0,4),(161,0,74,0,4)]
def g235A : List (List Nat) := [[],[16,83,118]]
def g235D5 := limbs80 #[#[0x55140443cc5515150110,0x443cc5514154110e3965,0x5536154140e396455150,0x50550f2b80551525038e,0xb678523060333d8f72,0x50400]]
def g235D6 := limbs80 #[#[0x3cca1a808870d5450d52,0xe5aa8a9281ce5515050,0x43f8a8a80884dd74d8d5,0x10df2caa0221ee551404,0x442fcbaa80886fb65501,0x110fe282a82217edd540,0x4437cb22a0887795454,0x5110d7ac8aa221bed915,0x644427fbb2a8884fd765,0x505309faebb22213fdd5,0x1515037db0aa0a05ef72,0x4d8540f3a86b0a81cf55,0xc1545027ebaec2a06bd5,0x7059540bf6e0b2a81eed,0x5c7655027fb8acaa06fb,0xd5450550bdee4a0aa13f,0xedc1545436fb1a84a873,0x6f7055152edae0aa2a5d,0x520d0160027eb8ec0aa7,0x23d0d6320b22908e1e0,0xa2631865814a4f12e461,0x12811fe7c1ca711be6e1,0x8a9f2769c262932468a2,0xc48505c317140aaea82,0x7c508171f00504a60417,0x317045c10214045c5020,0x7100a8d88217045c8c04,0x60302105014205041411,0x1c0c20602080070,0x820404014044c368a844,0xc106020801912170c5c4,0x8217058c5c217040030],#[0x18]]
def g235H6 := limbs80 #[#[0x43ac000000480003d996,0x24c26c400039001]]
def g235D7 := limbs80 #[#[0x350d52b7d8d50e750d40,0x90e52db55152f390d52f,0x4910fe54110fe50110f3,0x110bf59110fb94910fb5,0x40bfd8540fe54140bfd9,0xef55140fb94940fb549,0xdf55150bfd9540bf5954,0xfd8154fbd8152bfd8152,0x50530ff59110ff55110b,0x9540ff58540ff54540ff,0xd42ff50950ff50550ff5,0xffd8154ff58154ff54,0x1ea314550880da164148,0xa8a4fc9d734e5a4a712c,0x3992af55b4ac540a5147,0x2542f7fef75e13926eed,0xc388697165b49b90f1b2,0x19728164c5860078a312,0x548443c18c794122a328,0xf1412e39524411882834,0x22543c72129410c904c8,0x80c488400e1419528425,0x43124d10b88543850650,0x152e117281150e141942,0x80992e3128e9c6c04a3,0x6485c30c08097242920c,0x4c51a28707144c21a34,0x2e5080710302025c546a,0x222161c3264880944906,0x64c9101a8908c60b9424,0xc7060e1a22c4c4248cb8,0x85c2248cb86383050]]
def g235H7 := limbs80 #[#[0xa32248881d81b41b8de1,0x48210000000000000d34,0x8492e95c6201e42f3191,0x9fa3f0ec0e92d0110d89,0x3c880023222502b950,0x60d5fd1655000497c14,0xd00000164f0f800f39e2,0x2013d08fa398631a4404,0xe421432421dc19]]
def g235D8 := limbs80 #[#[0xd30fe907f443dca5ed52,0xa5fd42fe997f543fa81f,0xd25a240a82a007f553fa,0xf8e01541b557aae4fa1c,0x22224024f8c280554608,0xd11088c928d150065923,0x74809638623481099213,0x10c3492046460e48a15c,0x83e3802149347951389,0x218233e23451]]
def g235H8 := limbs80 #[#[0x34f00043108c,0x600000000d000000000,0x34000001972c2e82cb00,0xd,0x499000,0xd0c000007c000000,0x880000000,0x1492a254c000,0x5c540000000000000000,0x7c3e04c0,0x81c002ec0000000,0x1ca00000000018000310,0x1a400000081400000,0x248cffc7b1ac300280,0x542000000000,0x736,0x1845eb00000000,0x172000000000f640,0xa5000000696000000,0x33059c,0x70900062c0000000,0x29d000000000000000,0x0,0x130c00,0xa3e230000000000000,0x84c001030]]
def g235D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g235H9 := limbs80 #[#[0x842,0x20000000010000132000,0xc006800001f3bc000008,0xcc00000000000a40016,0x1c0000b4b4400000000,0x22800000000000000000,0xa55d308000000000f5,0x200000001830000000]]
def g235L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g235D5)
  | 6 => (38,3,5,0,0,10,0,g235D6)
  | 7 => (34,2,5,0,0,11,0,g235D7)
  | 8 => (11,1,5,0,0,9,0,g235D8)
  | 9 => (1,0,5,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 1 8 3 1 g235H6
  | 7 => lookupWord 12 59 5 11 6 1 g235H7
  | 8 => lookupWord 12 191 2 11 6 1 g235H8
  | 9 => lookupWord 4 71 3 9 4 1 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 7=true := g235P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_1 : block g235 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_5 : block g235 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 38=true := (@block_merge g235 6 0 1 37 g235P6_0 (@block_merge g235 6 1 4 33 g235P6_1 g235P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_6 : block g235 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_23 : block g235 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 34=true := (@block_merge g235 7 0 6 28 g235P7_0 (@block_merge g235 7 6 17 11 g235P7_6 g235P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_2 : block g235 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 11=true := (@block_merge g235 8 0 2 9 g235P8_0 g235P8_2)
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
theorem g235G : graphValid g235 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=4149) (before_sound K231 V231) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K231 10 [(235,[]),(238,[32]),(250,[64,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V231 low235 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x9fe7fe01fe7f9ff8fe,0x90000003e007c00f83ff])),(BitVec.ofNat 152 (word80 [0x4004040401001000,0x21084210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ff9fffe007fe7ff1c,0x6040007c00f801f07c1f])),(BitVec.ofNat 152 (word80 [0x8008080802002000,0x42108421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe001ffffff8007ffe0,0xb000f801f003e007fe0])),(BitVec.ofNat 152 (word80 [0x10010101004004000,0x84210842108421084]))),((BitVec.ofNat 152 (word80 [0x1fffffffff80003,0xa9c1f00000003fff8000])),(BitVec.ofNat 152 (word80 [0x4a14a0a0a02802824b,0xa9d08421084210842108]))),((BitVec.ofNat 152 (word80 [0xfffe00000000000003,0x773e00001fffc0000000])),(BitVec.ofNat 152 (word80 [0xc00c0c0c130530493,0x77108421084210842108]))),((BitVec.ofNat 152 (word80 [1,0x4bfffffe00000000000])),(BitVec.ofNat 152 (word80 [0x100101010040040000,0x210842108421084210]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(32,0,213,0,10)]
def g245A : List (List Nat) := [[],[101],[116],[116,101],[66],[66,101],[66,114],[66,114,101],[114,66],[114,66,101],[114],[114,101],[32],[32,101],[32,116],[32,116,101],[32,64],[32,64,101],[32,64,112],[32,64,112,101],[32,112,64],[32,112,64,101],[32,112],[32,112,101],[64,32],[64,32,101],[64,32,114],[64,32,114,101],[64],[64,101],[64,112],[64,112,101],[64,114],[64,114,101],[64,114,32],[64,114,32,101],[112,32,66],[112,32,66,101],[112,32],[112,32,101],[112,64],[112,64,101],[112],[112,101],[112,66,32],[112,66,32,101],[112,66],[112,66,101]]
def g245D10 (j : Nat) := if j=0 then 0x7f else 0
def g245L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g245D10)
  | _ => emptyPacking
def g245I (_ _ : Nat) : Option (Nat × Nat) := none
def g245 : Forest := ⟨245,10,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P10_0 : block g245 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B10 : block g245 10 0 1=true := g245P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245T : checkedTables g245 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g245 0 0 0 = true)
  · exact (rfl : block g245 1 0 0 = true)
  · exact (rfl : block g245 2 0 0 = true)
  · exact (rfl : block g245 3 0 0 = true)
  · exact (rfl : block g245 4 0 0 = true)
  · exact (rfl : block g245 5 0 0 = true)
  · exact (rfl : block g245 6 0 0 = true)
  · exact (rfl : block g245 7 0 0 = true)
  · exact (rfl : block g245 8 0 0 = true)
  · exact (rfl : block g245 9 0 0 = true)
  · exact g245B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 11 := lower_forest (g:=g245) (i:=0) (hints:=2) (before_sound K235 V235) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K235 11 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V235 low245 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8a674e518910000000,0xff80001ff007fc01ff])),(BitVec.ofNat 152 (word80 [0x260e11081028140a,0x5028140a05028140a05]))),((BitVec.ofNat 152 (word80 [0x140484f4c590000001,0xff00000000000003fe00])),(BitVec.ofNat 152 (word80 [0x10048460c592994ca6,0x532994ca6532994ca653]))),((BitVec.ofNat 152 (word80 [0x80807d2cb0000003fe,0x3fe00ff80001ff])),(BitVec.ofNat 152 (word80 [0x8080402c8000502814,0xa05028140a05028140a]))),((BitVec.ofNat 152 (word80 [0x9ab820be0c6007fc00,0x3fe00])),(BitVec.ofNat 152 (word80 [0x8aa8209e086562b158,0xac562b158ac562b158ac]))),((BitVec.ofNat 152 (word80 [0x692c32c842aff80000,0x7fc0000ffffc0000])),(BitVec.ofNat 152 (word80 [0x80830c002a180c060,0x30180c06030180c06030]))),((BitVec.ofNat 152 (word80 [0x2748810167d0000000,0x7ffffff000000000])),(BitVec.ofNat 152 (word80 [0x27408100654e070381,0xc0e070381c0e070381c0]))),((BitVec.ofNat 152 (word80 [0x64938102186fffffff,0xffff8000000000000000])),(BitVec.ofNat 152 (word80 [0x641101001008040201,0x804020100804020100]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(32,0,95,0,11)]
def g127A : List (List Nat) := [[],[66],[49],[49,66],[32],[32,64],[32,49],[32,49,64],[64,32],[64],[64,49,32],[64,49]]
def g127D11 (j : Nat) := if j=0 then 0xff else 0
def g127L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P11_0 : block g127 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B11 : block g127 11 0 1=true := g127P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact (rfl : block g127 5 0 0 = true)
  · exact (rfl : block g127 6 0 0 = true)
  · exact (rfl : block g127 7 0 0 = true)
  · exact (rfl : block g127 8 0 0 = true)
  · exact (rfl : block g127 9 0 0 = true)
  · exact (rfl : block g127 10 0 0 = true)
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=4146) (before_sound K245 V245) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K245 12 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V245 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8a774e538110000000,0xff80001ff007fc01ff])),(BitVec.ofNat 152 (word80 [0x260e13001028140a,0x5028140a05028140a05]))),((BitVec.ofNat 152 (word80 [0x100404f4cdf0000001,0xff00000000000003fe00])),(BitVec.ofNat 152 (word80 [0x10040460c5f2994ca6,0x532994ca6532994ca653]))),((BitVec.ofNat 152 (word80 [0x80807c2cb0000003fe,0x3fe00ff80001ff])),(BitVec.ofNat 152 (word80 [0x8080402c8000502814,0xa05028140a05028140a]))),((BitVec.ofNat 152 (word80 [0xbab8a0be0c00000000,0x3fe00])),(BitVec.ofNat 152 (word80 [0xaab8a09e080d66b359,0xacd66b359acd66b359ac]))),((BitVec.ofNat 152 (word80 [0x492cb2c842a007fc00,0x7fc0000ffffc0000])),(BitVec.ofNat 152 (word80 [0x480830c002a180c060,0x30180c06030180c06030]))),((BitVec.ofNat 152 (word80 [0x2748010167dff80000,0x7ffffff000000000])),(BitVec.ofNat 152 (word80 [0x74000006546030180,0xc06030180c06030180c0]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64938102186fffffff,0xffff8000000000000000])),(BitVec.ofNat 152 (word80 [0x201181001808040201,0x804020100804020100]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(0,8,181,2,11)]
def g191A : List (List Nat) := [[],[84],[66],[66,82],[82,66],[82],[32],[32,84],[32,64],[32,64,80],[32,80,64],[32,80],[64,32],[64,32,82],[64],[64,80],[64,82],[64,82,32],[80,32,66],[80,32],[80,64],[80],[80,66,32],[80,66]]
def g191D11 (j : Nat) := if j=0 then 0xff else 0
def g191L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g191D11)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,11,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P11_0 : block g191 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B11 : block g191 11 0 1=true := g191P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact (rfl : block g191 6 0 0 = true)
  · exact (rfl : block g191 7 0 0 = true)
  · exact (rfl : block g191 8 0 0 = true)
  · exact (rfl : block g191 9 0 0 = true)
  · exact (rfl : block g191 10 0 0 = true)
  · exact g191B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 12 := lower_forest (g:=g191) (i:=0) (hints:=4146) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 12 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xcad099910500000000,0xff00000000ff00ff00ff])),(BitVec.ofNat 152 (word80 [0xc00088910505050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0xc55a0e639c000000ff,0xff000000ff00])),(BitVec.ofNat 152 (word80 [0xc1520e201c13131313,0x13131313131313131313]))),((BitVec.ofNat 152 (word80 [0x83e6580220000ff00,0xff0000ff0000ff])),(BitVec.ofNat 152 (word80 [0x81a6500020a0a0a0a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0x4d8bd01fa000000000,0xff0000000000ff00])),(BitVec.ofNat 152 (word80 [0xc89d01fa0acacacac,0xacacacacacacacacacac]))),((BitVec.ofNat 152 (word80 [0x30e1880a1900ff0000,0xff00000000ffff0000])),(BitVec.ofNat 152 (word80 [0x10e1000a1830303030,0x30303030303030303030]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x100160244cff000000,0xffffffffff00000000])),(BitVec.ofNat 152 (word80 [0x40404040,0x40404040404040404040]))),((BitVec.ofNat 152 (word80 [0xa604165c72ffffffff,0xff000000000000000000])),(BitVec.ofNat 152 (word80 [0x260410446080808080,0x80808080808080808080]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(2,0,221,0,11)]
def g223A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g223D11 (j : Nat) := if j=0 then 0xff else 0
def g223L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g223D11)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,11,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P11_0 : block g223 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B11 : block g223 11 0 1=true := g223P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0 = true)
  · exact (rfl : block g223 1 0 0 = true)
  · exact (rfl : block g223 2 0 0 = true)
  · exact (rfl : block g223 3 0 0 = true)
  · exact (rfl : block g223 4 0 0 = true)
  · exact (rfl : block g223 5 0 0 = true)
  · exact (rfl : block g223 6 0 0 = true)
  · exact (rfl : block g223 7 0 0 = true)
  · exact (rfl : block g223 8 0 0 = true)
  · exact (rfl : block g223 9 0 0 = true)
  · exact (rfl : block g223 10 0 0 = true)
  · exact g223B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=4146) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x4625875d400f000000,0xff000000ff00ff00ff])),(BitVec.ofNat 152 (word80 [0x4000831d000f050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0x60d0668aecc9000000,0xff000000ff000000ff00])),(BitVec.ofNat 152 (word80 [0x60c02608cc41131313,0x13131313131313131313]))),((BitVec.ofNat 152 (word80 [0x3020858ed200000ff,0xff0000ff0000ff])),(BitVec.ofNat 152 (word80 [0x3000040ec200a0a0a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0x4b7a9000a0be000000,0xff0000000000ff00])),(BitVec.ofNat 152 (word80 [0xb32800020beacacac,0xacacacacacacacacacac]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xa420fe2403b000ff00,0xffff0000])),(BitVec.ofNat 152 (word80 [0xa4207c200190707070,0x70707070707070707070]))),((BitVec.ofNat 152 (word80 [0xbc0950031552ff0000,0xffffffff00000000])),(BitVec.ofNat 152 (word80 [0x940950020100404040,0x40404040404040404040]))),((BitVec.ofNat 152 (word80 [0x919621a01a05ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x1600801200808080,0x80808080808080808080]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(1,0,238,0,10),(2,0,237,0,10),(4,0,235,0,10),(8,0,231,0,10),(64,0,175,0,10),(128,0,111,0,10)]
def g239A : List (List Nat) := [[],[32]]
def g239D11 (j : Nat) := if j=0 then 0x3445837f else 0
def g239L : Nat → Packing
  | 11 => (1,0,3,0,0,0,0,g239D11)
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
  · exact (rfl : block g239 0 0 0 = true)
  · exact (rfl : block g239 1 0 0 = true)
  · exact (rfl : block g239 2 0 0 = true)
  · exact (rfl : block g239 3 0 0 = true)
  · exact (rfl : block g239 4 0 0 = true)
  · exact (rfl : block g239 5 0 0 = true)
  · exact (rfl : block g239 6 0 0 = true)
  · exact (rfl : block g239 7 0 0 = true)
  · exact (rfl : block g239 8 0 0 = true)
  · exact (rfl : block g239 9 0 0 = true)
  · exact (rfl : block g239 10 0 0 = true)
  · exact g239B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=4146) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 12 [(239,[]),(251,[66]),(254,[32,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc8842210299ee0000,0x3f00003f000fc0fff])),(BitVec.ofNat 152 (word80 [0x480020002980e0410,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0x3958f7322a0350000,0xfc0000fc0000000000])),(BitVec.ofNat 152 (word80 [0x13950f7322a0343cf3,0xcf3cf3cf3cf3cf3cf3cf]))),((BitVec.ofNat 152 (word80 [0xf8d618e2f809000000,0x3f00003f00003f03f03f])),(BitVec.ofNat 152 (word80 [0x5018624801000820,0x82082082082082082082]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x213396247460000f,0xc0000fc0000fc003ffc0])),(BitVec.ofNat 152 (word80 [0x202121802060601041,0x4104104104104104104]))),((BitVec.ofNat 152 (word80 [0x245cc1d91c48203f0,0xffffc0000])),(BitVec.ofNat 152 (word80 [0x4204c41d9104806186,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0x53a8400572681fc00,0xffffff000000000])),(BitVec.ofNat 152 (word80 [0x800a80001506814104,0x10410410410410410410]))),((BitVec.ofNat 152 (word80 [0x200214809021cffff,0xfffff000000000000000])),(BitVec.ofNat 152 (word80 [0x8208,0x20820820820820820820]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(2,0,245,0,11)]
def g247A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g247D11 (j : Nat) := if j=0 then 0xff else 0
def g247L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P11_0 : block g247 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B11 : block g247 11 0 1=true := g247P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact (rfl : block g247 6 0 0 = true)
  · exact (rfl : block g247 7 0 0 = true)
  · exact (rfl : block g247 8 0 0 = true)
  · exact (rfl : block g247 9 0 0 = true)
  · exact (rfl : block g247 10 0 0 = true)
  · exact g247B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=98) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xd194a059a81c024400,0x3f00003f000fc0fff])),(BitVec.ofNat 152 (word80 [0x118420180004004410,0x41041041041041041041]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc3281c00d2cc85a000,0xfc0000fc003f03f03f])),(BitVec.ofNat 152 (word80 [0x22014009248008020,0x82082082082082082082]))),((BitVec.ofNat 152 (word80 [0x21af30c1f321795000,0x3f000000000000])),(BitVec.ofNat 152 (word80 [0xa1af30c1f3017942fb,0xefbefbefbefbefbefbef]))),((BitVec.ofNat 152 (word80 [0x84226ec55004e0800,0x3f000fc0000fc003ffc0])),(BitVec.ofNat 152 (word80 [0x84200c044000e0041,0x4104104104104104104]))),((BitVec.ofNat 152 (word80 [0x208bd3050ce250240f,0xc0000000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x2009c20508a2402186,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0x167502820823a03bf0,0xffffff000000000])),(BitVec.ofNat 152 (word80 [0x41002000822803904,0x10410410410410410410]))),((BitVec.ofNat 152 (word80 [0x2c004932231239c3ff,0xfffff000000000000000])),(BitVec.ofNat 152 (word80 [0x9222110310208,0x20820820820820820820]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(0,8,181,64,11)]
def g253A : List (List Nat) := [[],[116],[66],[66,114],[114,66],[114],[32],[32,116],[32,64],[32,64,112],[32,112,64],[32,112],[64,32],[64,32,114],[64],[64,112],[64,114],[64,114,32],[112,32,66],[112,32],[112,64],[112],[112,66,32],[112,66]]
def g253D11 (j : Nat) := if j=0 then 0xff else 0
def g253L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g253D11)
  | _ => emptyPacking
def g253I (_ _ : Nat) : Option (Nat × Nat) := none
def g253 : Forest := ⟨253,11,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P11_0 : block g253 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B11 : block g253 11 0 1=true := g253P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0 = true)
  · exact (rfl : block g253 1 0 0 = true)
  · exact (rfl : block g253 2 0 0 = true)
  · exact (rfl : block g253 3 0 0 = true)
  · exact (rfl : block g253 4 0 0 = true)
  · exact (rfl : block g253 5 0 0 = true)
  · exact (rfl : block g253 6 0 0 = true)
  · exact (rfl : block g253 7 0 0 = true)
  · exact (rfl : block g253 8 0 0 = true)
  · exact (rfl : block g253 9 0 0 = true)
  · exact (rfl : block g253 10 0 0 = true)
  · exact g253B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 12 := lower_forest (g:=g253) (i:=0) (hints:=24578) (before_sound K247 V247) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K247 12 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V247 low253 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ff800007fe007fe00,0x7fe44499900c319e10ee])),(BitVec.ofNat 152 (word80 [0xa0280a0280a0280a02,0x80a000880000009a0044]))),((BitVec.ofNat 152 (word80 [0xe000000000000001ff,0x800088e0060bc1fe0054])),(BitVec.ofNat 152 (word80 [0x6298a6298a6298a629,0x8a6088a00209c1ae0044]))),((BitVec.ofNat 152 (word80 [0x1ff801ff80000,0x7fe80f021870fe66210a])),(BitVec.ofNat 152 (word80 [0x405014050140501405,0x1400900082044640002]))),((BitVec.ofNat 152 (word80 [0x1ff,0x80000000000300780611])),(BitVec.ofNat 152 (word80 [0x956559565595655956,0x55801108000200500211]))),((BitVec.ofNat 152 (word80 [0x7fe00001ffffe00,0x10f004e383ff804822])),(BitVec.ofNat 152 (word80 [0x18060180601806018,0x60090002103a9000000]))),((BitVec.ofNat 152 (word80 [0x7ffffffe0000000,0x1000703fc0001ffbd])),(BitVec.ofNat 152 (word80 [0xe0380e0380e0380e0,0x3800000702480001ffb9]))),((BitVec.ofNat 152 (word80 [0xfff800000000000000,0x1e0007fc0000018fc0])),(BitVec.ofNat 152 (word80 [0x80200802008020080,0x20000007440000010400]))),(0x1ffff800000001f001,(BitVec.ofNat 152 (word80 [0x100401004010040100,0x40032250000000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(0,8,181,66,12),(1,0,254,0,12),(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,12),(32,0,223,0,12),(64,0,191,0,12),(128,0,127,0,12),(2,8,181,64,11),(10,0,245,0,11),(34,0,221,0,11),(40,0,215,0,11),(64,8,181,2,11),(72,0,183,0,11),(160,0,95,0,11),(0,2,53,200,10),(3,0,252,0,10),(5,0,250,0,10),(6,0,249,0,10),(17,0,238,0,10),(18,0,237,0,10),(20,0,235,0,10),(33,0,222,0,10),(36,0,219,0,10),(48,0,207,0,10),(65,0,190,0,10),(66,8,181,0,10),(68,0,187,0,10),(80,0,175,0,10),(96,0,159,0,10),(129,0,126,0,10),(130,0,125,0,10),(132,0,123,0,10),(144,0,111,0,10),(128,2,53,72,9),(192,0,63,0,9),(0,32,74,149,8),(161,0,94,0,8),(164,0,91,0,8),(1,32,74,148,7),(4,2,49,200,7),(4,32,74,145,7),(7,0,248,0,7),(16,32,74,133,7),(19,0,236,0,7),(21,0,234,0,7),(22,0,233,0,7),(37,0,218,0,7),(49,0,206,0,7),(52,0,203,0,7),(69,0,186,0,7),(81,0,174,0,7),(84,0,171,0,7),(97,0,158,0,7),(100,0,155,0,7),(112,0,143,0,7),(128,32,74,21,7),(131,0,124,0,7),(133,0,122,0,7),(134,0,121,0,7),(145,0,110,0,7),(146,0,109,0,7),(148,0,107,0,7),(5,32,74,144,6),(17,32,74,132,6),(20,32,74,129,6),(129,32,74,20,6),(132,32,74,17,6),(144,32,74,5,6),(193,0,62,0,6),(196,0,59,0,6),(208,0,47,0,6),(21,32,74,128,5),(53,0,202,0,5),(133,32,74,16,5),(145,32,74,4,5),(148,32,74,1,5),(23,0,232,0,4),(85,0,170,0,4),(101,0,154,0,4),(135,0,120,0,4),(149,0,74,0,4)]
def g255A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g255D6 := limbs80 #[#[0xf4bd0f11b85d9655d120,0xf11b661d655d120d60a,0x30ce0af4bd]]
set_option maxRecDepth 16000 in
def g255D7 := limbs80 #[#[0x42bd4725765957250120,0x57a8e3b2cb2ae4a0241b,0xf51c665d655c940482e8,0xa384d3acab22e0905d0a,0x70976595845c120b615e,0x9360bb2caba241b829c4,0x659655c940483385788d,0xbacab9280907d0af51c7,0x5d96550120fa15ea38cc,0xb2caa0241da2bc4f09b8,0x59540483b457a5e2370b,0x2a80906e8af13c26dd86,0x50120dd15e9788dbb0cb,0x241ba2bc4f09b661d65,0x4837457a5e236cc3acaa,0x5e2af51cb5d9845c960,0xbc35eab96bb308b92c09,0x8a9a76d1b25d98458120,0x57a8e134eb2ac8b8241d,0xf49ca5d96561170483d8,0x3368d92ecc22e0905e1a,0xf01b85d97459120ec54d,0x36ec32e8b2241d8abc2,0x6d9875d164483715785e,0xcb0eb2ac8906e2af0bc0,0x61d6559120d935e1780d,0x3acab2241b23bc4f01b9,0x5956448360f78fe0372c,0x2ac8906c0ff1fc46e587,0x59120e935e1780dcb0eb,0x2241d07bc7f01b961d65,0x4836c5788d9360cbacab],#[0x758af11b26c19759564,0xdb15e2784d832eb2ac89,0x23bc4f01b865d6559120,0xf78fe0370cbacab2241b,0xf1fc46e1975956448360,0x1780dbb30b2ac8906c0f,0xf03b46a17659120d935e,0x768d3b0cb2241aaabc2,0x6e17659574483355785e,0xc2ecb2ae890761af0bc0,0x5d9655d120ec1de2780d,0x32caba241d83bd0f11b8,0x59574483b077a0dbb68c,0x2ae8906e1af0bc06dd86,0x5d120dc1de2780dbb0cb,0xa241b26bc2f01b961965,0x483647789e0372c32cab,0x6e1af0bc06d98759574,0xdc1de2780db30eb2ae89,0x83bd0f11b661d655d120,0xd785e036ccc2caba241b,0xf1fc06d9985957448364,0x1781da350bb2e8906c1e,0xf03b4699875d120d4d5e,0x36dd2b30ba24199abc2,0x6dba56617448326d785e,0x82ecb2b0890645ef1fc0,0x5d96561120ec34cbb64d,0xb2cac2241b07bc7f01b9,0x5958448334d785e0372b,0xb30890649ef41cbae576,0x61120f074cbb2cd1340b],#[0x2a418b6bc2f01b6e9597,0x48354d389d9760d42ecb,0x5a9af49b4ec1a85d965,0xb43debb69d8350bb2ca9,0xa39c4ed3b06a17659520,0xd785e0368d42ecb2a41a,0xf13c06d1a85d96548354,0x3f80da350bb2ca906a8e,0xed1b46a17659520d43de,0x768d42ecb2a41a83fc7,0xec1a76196548354d785e,0x834ec32ca90669a713b2,0x69d8659520ad35e9369d,0x3b0cb2a419a39c4ed3b0,0x61d6548334d785e0768d,0x3aca90669a713b2ec1a6,0x59520ad35e9369d834cc,0x2a41587bd76d3b069987,0x483347389da760d330eb,0x669af0bc0ed1a661d65,0xc5b5e1780db74aca30e9,0x97bc7f01b6e959461d20,0xd7a0da764c3acab92c18,0xf41c4ec98759572583b0,0x1780da30eb2ae4b06e1a,0xf09b461d655c960dc35e,0xa760d130eb2ac1b86bd0,0xec1a261d65582b4d7a4d,0x8344c3acab0561ef5db4,0xa06e03e000cd1ce2769d,0x29e27c24c21c1980ea0b,0x5434032c30a2e82d42c0],#[0xa4043fe3f83d63c23923,0x46644442241c41641040,0xe44d04ca4c44be4aa488,0x85865565345124f04ea4,0x62e61a5f85d65d05ca5a,0xd669868466265c656642,0x275c7567347126f06ea6,0x78678077a77476e76876,0xb07aa7a479e79879278c,0xe80c7f87e47c27bc7b67,0x3fe00487086a86485082,0x34b487f800c04800d3d0,0xd824105045d487f80140,0xe0002430048b84bf800f,0x4328ffa03d00ee02f807,0xe009528a6213050c12f4,0x5af82fc03e80f602f805,0x120034b4843a88521f18,0x380cc20120034f40c30,0xba14180cc140cee850af,0x48140cee8508033bc0c2,0x49049f866a1c4e048100,0x9c12040350123e010e41,0x800000000007e01a880,0x7120998ff2342e63fc8d,0x3405034bc0c220d6,0x804701182000f234100,0x6850ce85fc0c2011af01,0xa142011c0460a688de03,0xc042011c046080000467,0x520405206e8504046b,0x67846e181ae19b860800],#[0x4201f800423b985a6146,0x6e182be00d880b98fe63,0x2b86,0x1ae19b86080000000000,0x10b68301182011816e18,0xba0c1011af0]]
def g255H7 (j : Nat) := if j=0 then 0x478000 else 0
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0x82e8af19855954250120,0x120f829875d965509404,0x40482e8a721765954250,0x250120f2299761965509,0x50940482e8af1d865954,0x916250120f0a99761976,0x5745894048362a6dd875,0x655d16250120f8298759,0x76597458940483b0a69d,0x69d965d16250120f0a98,0x69a765d655894048392a,0xe0a619655d17250120e4,0xb469c95d9655c940483,0x483c1a65d86595725012,0x8120f229966116454950,0x960483c2a65d845d1625,0x7258120f82965611745c,0x55c960483c1a65d65611,0x5958458120b46bc465d6,0x1da25956048368a6d1b2,0x165591725c120e869a76,0xc4619655c97048361a6e,0xaf19b8595725c120b86b,0xc69c2ed17659570482e1,0x338aed1a268165591209,0x20f069875d9926416548,0x258391ae9d7664990595,0x5c960cc69a7ec1a25957,0x940482b1af01a768965,0x54250120fa29c85d9655,0x6550940483e8a71d8659,0x75956250120fa29c661d],#[0x6d17658940483b8a711a,0x11b95d96250120f8a987,0xbc46dd96589404835aaf,0xaaf11b665d6250120b6a,0xfc29c45d9655c940482d,0x83d1a725765957250120,0x120f469c7659655c9404,0x40483d1a719975957250,0x250120f8a9866d1765c9,0x5c94048356af11b95d97,0x5d7250120b5abc46dd96,0x97659540482d6af11b66,0xb25d96550120de29b46c,0x96c97659540483d1a65d,0xf09b85d96550120d669b,0x3bc46e1765954048369a,0xe9af09b76196550120da,0xba3bc46dd8659540482,0x482e9af09b661d655012,0x8120ba3bc46d98759540,0x960483d2af11975d1625,0x6258120da6bc56e17458,0x758960482e9af15b7611,0x5917258120ba6bc56d18,0xd9845c960483d2af1197,0x1975957258120f8a9c45,0xc465d655c960483d1a71,0xaf09975d16458120f46b,0xeabc46c9a759160483d2,0x3d1af09975957458120a,0x20f43bc465d655d16048,0x482f2af11b25d974581],#[0x58120e87bc56a1765d16,0x95604836aa6d1b25d984,0xd6558120d669b4ec9975,0x9759560482d9a713b265,0x461d7658120b66bc26d1,0x595845c970482e1ef15b,0x1186595725c120f869b6,0x9c269d6559170483e1a7,0x1ef1da8595645c120ec6,0xbcabc46c97659170483a,0x82b6af11b269d645c120,0x120f839c4619655d1704,0x70483e1a70976595845c,0x45c120b87bc769965611,0x5957048366a6d1b25d98,0xd9655c120dc69b46c976,0x18659570482f1af11b25,0xb05d97459120b87bc76d,0x6e1765d16448372a6c9,0xf01b76197459120d8bbc,0xbbc06d9875d164482e2e,0xc9ef01b961d6559120b8,0xb07fc76e58759564482,0x48349ef01b961d655912,0x9120d07fc76e58759564,0x56448359a6c9b065d655,0x6559120b63bc46c19759,0x759564482c8ff11b865d,0x6616559120b07fc76e19,0x89a05d964482c9ef01b7,0x9b05d9655d120ceabb46,0xc46c1765957448371a6c],#[0xff11b85d9655d120bc3b,0x87bc06e17659574482e0,0x360ff11b85d9655d120d,0x20d83db76d1865957448,0x4482e1ef01b7619655d1,0x5d120b27bc06e5865957,0x9574482e1ef01b661d65,0x1655d120b83fc46d9875,0x9859574482c9ef01b666,0x2681765d120b07fc76d9,0x6c1765958448336aed1a,0x1db95d96561120da69b2,0xbc06e57659584482c1ff,0x1f71eb95d965611209a7,0x927dcbae57659584482c,0x8269e703b95d96561120,0x520ec6ba76c976641654,0x6548339aed1a26817659,0x659520987dc7ee9985d9,0x5d965483a9aecbb06a17,0xa17659520aa79c4ec1a8,0x1a85d965482a9ef01b46,0xb069d8659520a87fc76d,0x4ec1a76196548369aecb,0xecbb069987595209a79c,0x79c4ec1a661d6548369a,0xb3af09b469d625c1609a,0xd86db4ec98759572582,0x582e1b713b261d655c96,0xc960b87bc06d18759572,0xd65582e1bf09b461d655,0x76595709a79c4ec1a261],#[0x25d9655c331e693b0689,0x65962501209c79c4ec1a,0xd99758940483daaf11b7,0x1b76597250120f6abc46,0xc46d9975c940483d6af1,0xa711b25d96550120f5ab,0xa3bc46e17659540483f8,0x3e9af09b76196550120f,0x20fa3bc46dd865954048,0x483e9af09b661d65501,0x50120fa3bc46d9875954,0xd940483aeaed3b26a176,0xd8650120ebabc2ed1a85,0xa7619404836eaed3b269,0x26998750120dbabc2ed1,0xed1a661d404836eaed3b,0x2d766117258120dbabc2,0xbc46c9a759160483e3a7,0x3a69db25d98458120eea,0xbaebc26e97661160483e,0x82e9ef15ba5d98458120,0x120f66bc26d197595604,0x70483b6af11b269d645c,0x45c120f879ca5d965611,0x61170483e3a699b25d98,0xd9845c120b9ebc26e976,0x97659570482e5ef15ba5,0xb45d9655c120fc69c46c,0x6dd865d164483f1a709,0xf01b661d7459120f8bbc,0x7bc06e58759564483e2e,0xc8ff11b961d6559120f2],#[0xf07fc76e58759564483,0x483d9a6c9b065d655912,0x9120f66bc26c19759564,0x564483d8ef11b065d655,0x6559120f27bc06e19759,0x759564483c8ff11b865d,0x6616559120f07fc76e19,0xc1a85d964483c9ef01b7,0x3b06a17659120eaebb2e,0xc0ed1a85d964483aaeed,0xaecbb069d8659120eabb,0xabbb4ec1a7619644836b,0x36aef03b469d8659120d,0x20eabbc0699a461d6448,0x44836baecbb069987591,0x59120dabbb4ec1a661d6,0x1d644834faecbb06a587,0x58759120d3bbb4ec1a96,0xa961d644834deed7b06a,0x46a58759120d1fbb7ec1,0xed5a961d6448346fedfb,0xcbb06a58759120d17fb7,0xbb5ec1a961d644838fae,0xbeedbb06a58759120e37,0xe1fbb7ec1a961d644838,0x8389fedbb56a58759120,0x120e17fb7ed5a961d644,0x6448383fedfb66a58759,0x759120d7abb4689a065d,0x65d644839eaed1a26819,0xa19759120d7abb4ec9a0,0x1a865d644834eeed3b06],#[0xb06a19759120d2fbb6ec,0x5ed1a865d6448347eedf,0xedbb46a19759120d33fb,0xbfb7ed1a865d644834af,0x49fedbb56a19759120d1,0xd17fb7ed5a865d64483,0x48343fedfb66a1975912,0x9120d3ebb2ec1a766164,0x1644834deed7b069d985,0x9859120d2fbb6ec1a766,0x65957448349fedbb569d,0x619655d120f83fc46e17,0xdd8659574483e1ef01b7,0x1b9619655d120f83fc46,0xc46e58659574483c9ef0,0xef01b661d655d120f23f,0x83fc46d98759574483e1,0x3c9ef01b6661655d120f,0x20f07fc76d9985957448,0x4483a7aecbb06a1765d1,0x5d120e9bbb4ec1a85d97,0x1974483a6ef03b46a176,0xd865d120e9bbc069da46,0xa76197448367aecbb069,0x6a5865d120d9bbb4ec1,0xec1a9619744834faecbb,0xd7b06a5865d120d3bbb4,0xbb6ec1a9619744834dee,0xafedbb46a5865d120d2f,0xd27fb6ed5a9619744834,0x8367aecbb0699875d120,0x120d9bbb4ec1a661d744],#[0x7448366ef03b4699875d,0x85d120e37bc069ba5661,0x6617448385ff1da6e959,0x95985d120d37bc06dba5,0x1a66617448345ff1db6e,0xb0699985d120d3ebb2ec,0x7ec1a6661744834deed7,0xedfb5699985d120d1fbb,0x79976c1765958448345f,0xe9ef01b95d96561120f8,0xf27bc06e57659584482,0x483c1ff1db95d9656112,0x1120da7bc06e57659584,0x584482e9ef01b7659656,0x7661120ba7bc06d99759,0x5d984483aba659a2681,0x6817661120e9e997689a,0xc1a95d984483c3e65d96,0xfb06a57661120d2fbb6e,0xb6ed5a95d98448347eed,0xfedfb56a57661120d27f,0xffb7ed9a95d98448345,0x32faecbb06a57661120d,0x20cb7bb5ec1a95d98448,0x44830fef01baaa576611,0x61120c37fc56eaa95d98,0xd9654832def01b6e9597,0x17659520ee69b4689a05,0xa05d965483b9a709a468,0x6917659520be6bc26d1,0x6a1a45d96548379a6c9b,0x11b86917659520ea3fc4],#[0xfc76e1a45d965482e8ff,0x9ef01b46a17659520b87,0xb87fc76d1a85d965482e,0x83a9e6d3b06a17659520,0x520ea7bb4ec1a85d9654,0x65483a9ef01b46a17659,0x659520ea3fb46d1a85d9,0x5d965483a1ff1db46a17,0x918659520ea7bc0ed1a8,0xda461965483a9ef01a76,0xb76918659520ea3fc469,0x46dda461965482e9ef01,0xecbb069d8659520ba3fc,0x79b4ec1a761965483e9a,0x69eed3b069d8659520da,0xba79c4ec1a761965483,0x482e9ef01b469d865952,0x9520da7bc0ed1a761965,0xd65483a9ef01a6691875,0x8759520ea3fc4699a461,0x461d65482e9ef01b6691,0x6918759520ba3fc46d9a,0xc1a661d65482e1ff1db6,0x3b06998759520fa6bb2e,0xb4ec1a661d6548369e6d,0xe713b06998759520da7b,0xa7bc06d1a661d65482e9,0x2e1ff1db46998759520b,0x20da7bc0ed1a661d6548,0x64834fa6d3a2e81985d9,0x5d920b3ebc2693a06617,0x6176482cdef15a4e8198],#[0x1985d920b2fbc6693a06,0xa066176482c7ef1da4e8,0x691985d920d3b9b4e93,0xec1a4661764834faecbb,0xd7b0691985d920d3bbb4,0xbb6ec1a4661764834dee,0x7eedfb0691985d920d2f,0xd2bfb6e91a4661764834,0x8346fedfa4691985d920,0x920d27fb6ed5a4661764,0x7648345fedfb5691985d,0x85d920d0ffb7ed9a4661,0x65d864834faecbb0e919,0x819761920cbe9b4e8ba0,0x3a065d86482afaf09a4e,0xa4e819761920ab7bc569,0x4e93a065d86482abef19,0xecbb0e919761920cbb9b,0x7bc065ba5651874832fa,0x2def01b6e959461d20e3,0xc97fc76dba565187483,0x4832fa6d3a2e819661d2,0x1d20abebc2693a065987,0x987482a7ef1da4e81966,0x9661d20cbb9b4e93a065,0x7589705832faecbb0e91,0xe898758960ecebc26d1a,0xd3a261d62583abaf01a4,0xbb06918758960daebc06,0xc0ec9a461d625836baec,0xef01b461d655c960daeb,0x86fc26d18759572583e1],#[0x3a7af01a4e89875c960f,0x60d9ebc06d3a261d7258,0x258367aecbb0691875c9,0x59560d9ebc0ec9a461d7,0x1d65583a9e693b068987,0x98759560ea7ba4ec1a26,0xa261d6558369e6d3b068,0x6898759560da7bb4ec1,0xec1a261d65582e9e713b,0x9a46898759560da79a4,0xfc2691a261d65582e9bf,0x9ef01b46898759560ea6,0xb87fc76d1a261d65582e,0x8369ef03b46898759560,0xd60da7bc06d3a261d655,0x87582afaf09a4e819261,0x261d60ab7bc5693a0649,0x64987582abef19a4e819,0x819261d60a9fbc7693a0,0x1a25d9655c32ee6d3a4e,0xa4649905d965bc7bc06d,0x9180b5008e0002d9bf09,0xb84139821f037c05dc0,0xe09c011c820883b0069e,0x8c86c50cfc18742d1054,0x22c042e07d40f341db43,0xf13a426944b5893e11ba,0x128bb7162a2a9c51609f,0x37246ad8d0719b432186,0xd20123ea07a38eb21c6e,0x349208230044b0852105,0x51049f693a626704b909],#[0x12cb45818ac595102944,0x3618252fa25dc0b8e16a,0x6978cf19975320e62ccc,0xc39227024dcd9b203598,0x651e763bdc769ceb01d0,0x82f102d9ffa3f187c78f,0x444f489010f62198426e,0x4ca44547c88da518422b,0x995d301a5884a6893b52,0xa50e0a0a53ca27194da4,0x2daa075366a51547228a,0xb0655dc2b64566eab595,0x5b2cb5716842c8d588c,0x862ed25d30b97970badd,0xc2258212fe15f1abd4d7,0xa6440c7998bc313161d4,0xbe33426610cb3994a325,0xd1dda25341d67e0cea59,0xf6acad3dda6bb4b7692e,0x46b6536c4cd7e5ae6359,0xdf8dbce37626e6adbedb,0x571d6e2f9c4238577054,0x1d3a0073c0e699cb6392,0xeca1d843adb7576e9d1d,0x87790eea1dbdbb687690,0x9bc0d780eefd1df73be,0xf301e503c73788cf099e,0x47b28f569e96bd0079c0,0xfcbde67b8cf701edd3db,0xf961f22be327c24f7fde,0xf7e0afb61f55be987cf0,0x1d400d7fc0fe99fc33f3],#[0x43a06a40b4810f019e0,0xd82f5056a0aa414e825d,0xfcc1e6838d069a0c9c18,0x996129423f845908660,0xc86590bca15c4298850b,0x30c43487f50f361c3434,0x143a27dc4e889ab12a22,0x78b2915d22b0c55b8a5d,0x78469c8cc5186e2ea45a,0x1e763bec75d8e7b1c763,0x2916521e242c481e8fe3,0xd9c9a092cd24e648cc8d,0x2a1e53a4a549469281e4,0x597052d225874ad49583,0x2e4c49985330265ee4b9,0x32ba64dcc88990531f26,0x999cd331a6604cba9969,0x9f4d1e9a17341667fccf,0x35da6b1cd5d9aaf35466,0x59bab36a26cacd8f9b13,0x9ce0d9c0f38066fdcdf,0x3bd276a4ea79cf5396a7,0x59fab3ea27bdcf5b9e5d,0x71d0c3a12d410a80acff,0x45da8b1d143a26144428,0x5a3df47728e4d1c3a32d,0x16b8d9c78b48a28fdd1f,0xdc14424ce6c8e0b70527,0x39b2008804321dce7b82,0x8118876033e0b4e3f829,0x5a73c0496514e6c6023,0x5b8280335c7ce6c588e7],#[0x914511ce0b2e3e7363f0,0x4294123c7e66c660a504,0x76aa2d0a566c844ee473,0x959b2008959e024d4710,0x3811124238f551704b42,0x2486a3909d5c7d66c702,0x4a428b8facd8f41a609,0x5209399b1ca3941a490f,0x8f364012d239c12ccf58,0x19b04a31f921d0a628,0x8c7f04bd0b5219cd9004,0x25b28a7363012087a034,0x5ae3791e4b48623939e0,0x2f014a09227b831116e4,0x48a4e0e445971fc9b1d8,0xe1ac908125d362b06a82,0x21b4f012f22d69b19d3c,0xfa90f049a2da9b18948d,0x82210bb5362430d73341,0xbc1f9cd95c1a44f726d0,0xa00cd05d38ea47f08770,0xce79f0a0339cd8c03501,0xb1c0600455cd87c21e0f,0x92b32a21d0fb84ac2999,0x4d83144989726c18a180,0x1e44ad360c50d22509eb,0x1ae8d85043a8d746c282,0xe019f05a71fc149cd92d,0xe0a4e6c8023811905939,0x877c160238118066b8f,0x67c169c7f05173643b3,0x824c112086b9e0238118],#[0x1f811c06b38fccdb8508,0xa2e3d82599b1c091c122,0xee3ff003207c03b91cb0,0xe02f1e1812007a034e81,0x53f0551cfc06e3c601a7,0x9c284a2e094e6c801ea8,0x82539b2009004514eee1,0x24011806882a8c7b853,0x9263c0696149cdb4849,0xef0497365812087b21ae,0x82b9e02400d2a4318f21,0x8c12cc7ae6c7825c1160,0xb87fc00e02214ea06ac2,0x801809003d01a663fa07,0x714068a14ac7d48770ff,0xccd95d8201ee63ff0178,0x913b11c990b851545612,0x96e14ccd8c048023e67,0xb321ccd9401cb09263c,0x23667a238834215584bd,0x9fe0bd0bf800230e0480,0x663dd0bf802409604701,0xc04691d88efe07033fc1,0x4bfc100cfd0bf800230,0x28d097e09d0bf80ac790,0x2fc078500962811b0344,0x742fe0bf0104b1808df8,0xfce3d22dc9b1c08d033,0xdee23936470738250248,0x93b858173e1a07f03d81,0xdb8521510a2077788e4d,0xb88bc2f26c9c0b6051f0],#[0x608703ef8681710a8851,0x4ab1f02490d245b5363,0x2702482eac79292d362f,0x2a420468c7be17825a9b,0xa2da9b0230c04821e80d,0x1ff8048b0e41f5ccc63d,0xff801b13b01ffc1506a7,0x461409089db097e0b71,0x9b0230ae12025b45b536,0x4cc7fe0062d10133c25a,0x8176a6c8810d84bf04c1,0x3b0bf037c340fe07b03b,0x434414209009371fa9b2,0x4716fc00118944ec873,0xc428f506921fcc7de09f,0x2a0d0851f82b81fe0008,0x5e1743ee12e4d8d98f7c,0xa207b785e4d9242881a,0x248c10e049f0df033151,0x3501a00ccf1dc1f3cd81,0xe7c280ce73788f2b8420,0x2485dc21e0f80d406938,0x233b28f0245289c2599b,0x66a8fccd8c43f01ac29,0x1ec14ccd8b42ecc740d2,0x5a8fb09766c580e584b5,0x33b09328a7365012114,0xd485d31c9c7623c068,0xbb70dc140258a927363,0x39d11034819ce6e09233,0xc828412d47809373644e,0x54599bb09108a2910e87],#[0x8e3c88533a048c47811d,0x10d84b511d8670a666c0,0x9663a069785647e66c71,0x663f13a712d4d92428d0,0xe007410c07c048a1c90d,0x3b019fc0f31ff82e42f,0x3350d563ff054a2fc00c,0xb48ffe0a93b98ffc00c0,0x9627e0bd0bf800a58803,0x798fe468dc8ef42f2342,0xc8ee468e052e477a17e0,0x9b240a498ff42fc0fe03,0xd6068048f42e63ce25c,0x808df80b890ea3f91ea,0xfe03f801809804844efe,0xe03c9b1913a710f81e63,0x1fc8d1791c3084527c0f,0x5d8fe4d8c04f41a20ceb,0x712ccd92c9da0e085b03,0xc46b13c91c023012fd0a,0xe08099f03fc001186023,0xbe07f01742fe0095517,0x73362949713c710d447e,0xd0b99b24096033023fa1,0x2348ef11e23bf81fc05,0x47fc0fe026a2ccd96047,0x47703581a48bb31c0336,0x8804b02384ced4599b15,0x66c0962246bd0bf80e47,0x41d0bf808258e047f42d,0xfd11f802008e046fc11e,0x6fc12126b3c052426212],#[0xac7014909a84c425d634,0x51508442d81fe47f66c6,0x23858097614cc7e66c96,0xfc0731a3e67923911a01,0x1243cc7184001fe85f81,0xfe0298ffc00df80dc41,0x442198fcc70e610f42fc,0x3364490f31be85f81fc0,0x39512fc17e0009a2ee23,0xd5219893e17936046240,0xf800228c91fe4f507062,0x46e4d89f03f808c4390f,0x3023be17f002011c0660,0x419fc0f91f785fc00b03,0x62723be07f01bc2f2345,0xf8002388047019811b93,0x47023012f53623e16835,0x4023fe09f0bf808258a0,0x8dd1b1b51e047bc2f46c,0x60461d47b21fc479a580,0x2812311ef852945a0fa3,0x1b1c098046f41f46c090,0x123048528d0fde15d07d,0x15f0a390a0d7e0008e28,0x23911216911c53936047,0xf0bf821528e42e03f800,0x804801ef40c06827421,0xd2a422012006803da8e,0x20069d0301e8804801e8,0x1988047cc6b85006a201,0x37a140662011b31ae858,0x851408c6858198604702],#[0x37428604702308ec067e,0xa1dc0e0770330c08d03,0xa14201dc0cc241da0ced,0x419da142019c0ec241dd,0x170093024f867c23e008,0xf80d40916121007e0340,0x34d468603b7c30a90301,0xe061f053825a8d0d8240,0x7e0350245848402340d1,0x9c125c33e11f002a4200,0x4147c02a20442480d782,0x8922304b51003d0c067,0xe2ce010238bc14e096a2,0x8f0a438b3848502400d4,0x274301d80ce944181200,0x2f31fc8ee468803301dd,0x477234424ee63f91a185,0xae2920687121429698fe,0x118e0670181a0804841,0xfe468404601a0123e062,0x1a2014b31fc8ee468998,0xfc8ee468a0524c7f23b9,0xcc302381182029013eb1,0x2304833b4284046b80c0,0x143b4282046819840470,0x198404702304433943ea,0x52c10000a5820000460,0x30293e1af001f63fd1a1,0x84d8ff4684052ec7ba34,0xfb46860527c005786743,0x2210fc86b3120c0a4d8,0x3d01a0483d41a5c0e6],#[0xc1000a40814af0010000,0xe8d040a408149f0013a1,0x438205274684052bc005,0x33b51060470233a1437,0x450238118d0b6881008e,0x31a1014809fc8fcc7663,0x8604711d80cfd0a2723f,0x63ab1a0520c08e046742,0x2381182ac756340a41d,0x883bb4284046b80c0ec3,0x1c08c110ee511b80d428,0x14af0010000118076101,0x11c08c1361c1000a408,0x73c0520ad0a0811a0761,0xbd1e0814810290205206,0x527c004e8f06f000520,0x5c24208f447699e0d208,0x68998fcc68403570a663,0xe63b31a2814931f98ecc,0xd106604f0c09e449cc7,0x6c40605251ea8ed09222,0xb4851f0cd8714066d8d,0xd8d04b0f7802c40603b9,0x18149b0e1363417c002,0xec684249040029161df0,0xa040dc32e1836c783d8f,0x4850247234e068340230,0x80682012008fc8d21aac,0x91ab1698a0dc8d181e06,0x8e046e468683581a6293,0xd08e008a40b91a89d080,0xf8518f0178509067c8],#[0x6f850c0970337433e11f,0x52e47f23b91a2011a06,0x991fc8ee4689686bc004,0x26e0370a2a0cef0a1014,0x4f0c067b8008067388dc,0x541a723470a220d10660,0x8f80027c0cc60198283,0x40467c2c0cc3025ba19f,0xbc28378541984f858198,0x929e0409643394f6e144,0xf525c2014927a92e4258,0x927e93d4258805249fa4,0x33e12f00f80140660814,0x10808c0337c28604b74,0x285785050667010a0667,0x12c102582000833bc,0xa40814af0010000,0xa408149f0013a1c10,0x4b040000960812c1000,0x2080b8608081b865c306,0x7e035bc2f80450000000,0xa0c08c181188681011c0,0xb418404601a5c04321a6,0x61812008c034f4188834,0x18302310f420240119d0,0x808c03db808643dd4181,0xf850e066f850907b6830,0x857c25e01f003011a066,0x202300cdf0a1812dd0c3,0x84f855c190d03819be14,0x1419de142023028331c1,0x6e0c08c1a0cef0a15e14],#[0x430000258204b04021a,0x3c1a383ec088048c121c,0x12]]
def g255H8 := limbs80 #[#[0x20c78300088830258082,0x120302402073e140050,0xc180000c889003c3900e,0xcbc06056100f24803000,0x2034c0000f651443c52a,0x281a000141ba4c91,0x25124114000503400,0x440000003e42,0xfd8b1d04c00000024a30,0x6d9ea42c000547941010,0xf056046389d0d4048,0x3d4618847d4a388e0000,0x3112048214dc2c62195,0x83234fea0fd23c00,0x4e1613c07f0200003809,0x1cc5744b643471440d14,0x40000003455c616c1730,0xc2ae00e5810000000d0e,0xb205c88c0e2021b83a,0xde4738b5b09540f48d80,0xb00b4300000000305b90,0xce887c135801861d84b,0x4010fa26f147f8cb52b2,0x1905634f10a410582895,0x143c313f02de01,0xbb0000000c0514b7b0ac,0x2f0b8000e02bd1d00000,0xf20a6387424000d609c1,0xbe11871254226811583,0x7d81c446502350f753af,0x80007a8085050e800076,0xc129440e01852ff0f],#[0x4200c443b052d8370000,0xa0430000000080c00005,0x628520000a3,0x3c05c0a400022e6a10,0x46026387000080920270,0xb0198203543640c000d6,0x53e002c400b13b8a6e15,0x54b038000751a,0x780d5980942301de4a40,0x219d0002c08910a92,0xd800000002120a84000,0x39367,0x39110001c1e000000000,0x1c4c9533092000]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0xc0907a29865954250120,0x55c970483a34cbacab92,0x30ab2a84a0241e1a6196,0x7aa9865954250120f65,0x940482dd4dc2caa12809,0xb2a84a0241f8a5d96550,0x29b85954250120f6530e,0x482dd5db30aa1280907b,0x84a0241eaa6197650940,0x85d94250120f3530ebb2,0xdd5dab0ca1280905ba9b,0x241cea65d8650940482,0xd4250120b7576ec3284a,0xd32a8a9280905babb661,0x1f8a5956454940483794,0x50120dd534cb22a4a024,0xcaa92809076699659552,0xa6999554940482bb4dca,0x20aed76ccaaa4a02419d,0x12809066e9a665952501,0xd6458940483d54c3ac8b,0xc52caba2c4a0241baa69,0x907ca9765d16250120f,0x58940483b54cb2e8b128,0x4eba2c4a0241e6a61d74,0x7669955956250120db53,0x40482b74dcacab128090,0x2ac4a0241f8a6d165589,0x9975956250120f4d30eb,0x83734d3acab128090766,0x4a0241d9a6e565589404,0x5d96250120f1d30ebb2c],#[0x74dcaecb12809074e997,0x2415baed59658940482b,0x6250120e5d30ecb2c4a0,0xbb2cb12809066e9a7659,0x97a69d9758940482b75d,0x120fa52caba2e4a0241,0xab92809079a9865d1725,0x619655c940483e34bb2c,0xecd32cb2ae4a0241e9a,0x28090756997595725012,0x765c940483c74c32ecb9,0xd372bb2e4a0241d3a659,0x9071e9976197250120ab,0x9540482af5db32eb9280,0x8d12caa024169eed9855,0x669966896550120de534,0x4833b4d4b44b2a80907,0x2caa0241e1e61d765954,0x976196550120b4f370bb,0x2d3ddbb0cb2a80907279,0xa8241c3e65d865d94048,0x915254120f65308b22a4,0x4cb308a92a0907669965,0x415daed196549504839b,0x254120ecd32caa2c4a82,0x2c8b12a0905e69b65516,0x9a5958458950483d54c2,0x120e5d32cc22c4a8241e,0xb12c09056ebb46596254,0x1d7458960483d54c22e8,0xe9d32eba2c4b0241e3a6,0xc0905ae9b85d16258120],#[0x458960483974cbb08b12,0x768c3ac4b02416baedd8,0x56ebb465d6258120b5d,0x960483e54ba2c8b92c09,0xb22e4b0241d3a65d645c,0xa9845d17258120b9d36e,0x483e34b2ae8b92c09079,0xe4b0241e9a595845c960,0x76117258120f1d2ecc22,0xe34dbacab92c09071e99,0x241b9a6e9655c960483,0xd7258120b9d768bb2e4b,0xc3ae8b22c09055ebb465,0x1d2e65d7459160483c5c,0x58120d1f34ec3ac8b024,0xcaba2c09078798759574,0xe6a1655d160483a3ccba,0x20d1f350bb2e8b0241a9,0x22c0907a69b259584581,0xd656116048393ccbacac,0xcd348d12cab0241a9ee9,0x905e6bb46896558120d,0x59560483d34c3b44b2ac,0x4ed12cab0241d9a65da2,0x5e6bb76896558120dcd3,0x60482d3dda30eb2ac090,0xbacab0241e1e69d87595,0xbb465d6558120ecd764c,0x82d3ddc34eb2ac090567,0xcb02413ba6cba45d9604,0x61d7658120d1f30fd22e,0x34b2ac8b92e09058fbb4],#[0x241e3a619645c970483e,0x725c120b3d370b22e4b8,0xb308b92e090796965611,0xe5a6e1655c970482cf5d,0xc120ead372b2ae4b8241,0x8b22e09059ebb4619725,0x6197459170483e1cb2ae,0xd8f34eb2ac8b8241e2e,0x2e0906a79a8595645c12,0x865917048347cd42ecb2,0xf30cb2ae8b8241a3e69d,0x90787976595845c120f0,0x9570483e34bb344b2ae0,0x2d12cab8241b5a69da25,0xc69b25d9655c120ced35,0x482e3dda2ecb2ae0907,0x2cab8241e1e6a1765957,0xa7619655c120b4f768c3,0x34bcd434eb2ae0907879,0xb824169eed9a85957048,0x91765c1209bd365d22ec,0xdda30cbb2e09068f986e,0x4149fed99859554482c7,0x459120f07b0eb2ae8b22,0x340b2ac89058bdb85d97,0x8eed1a059564483734d1,0x120e0fb2ec3acab22417,0xb2ac890527db961d6559,0xdd985956448293fdc32e,0xb47f68d42cab224149fe,0xe890437fb56a58759120,0x65957448383ecc2ecb2a],#[0xf74cc2caba24161f6e17,0x437db6e95985d12086f,0x58448293edb72ab2b089,0xcbacac2241ada689a059,0x7fb569f9661120a4fb6d,0x48253eda74cc2aca9043,0x20b2a419dae919264165,0x76499059520ecd2ecc93,0x3b5d3b24c82ca9073698,0x2a41e1e61d7664165483,0xd9059520d8f74ebb320b,0xd1340bb2ca9071799761,0x139e6c3a45d965483734,0x59520d0fb0fd22ecb2a4,0xebb2ca904a7db8e9176,0xfedd985d965482c3fda3,0x20d4f760d42ecb2a4161,0x32ca904a7fb46a176595,0x1a76196548253edbf48c,0x4fb69d3b0cb2a4169eec,0xa904a7db6e9187595209,0x61d65482d3dd834cc3ac,0x6cd4b0eb2a412cfed1a9,0x4a7db6ea5875952094ff,0x705821bfdab49cb30e90,0x2ae4b82c133eed1a7589,0x9ba595725c160f8d364b,0x8363cd3b44b2ae0b06c7,0xcb82c171eec9a7595705,0x689655c96099f369d12e,0x36c3b44b2ae4b05e6bb0,0x2c1b1b69da259572583c],#[0x655c960f0df64c3acab9,0x834eb2ae4b0587fb461d,0x59eec1a959572582e3dd,0x9560ccf329d0324b2ac1,0xc92cab04e79b4e81925,0x6dfa06496558333ccbf4,0xacf760cbb24b2ac139e,0xacab05a7bb0689875956,0xa065d6558253eda744c3,0xd344d02cab92e139e6cb,0xb86579a9681655c970da,0x41655c3a3cbb324c82ca,0xfd1320b2ae1b1e5dba26,0xc7bb25d99059570caf32,0x55c2abdd932ec82cab85,0x2ecb2ae171eec1a25d96,0x975d9826016598fb69d1,0x6a3ed972ebb300b2f07f,0xa024119fed1a2e417659,0x194250120f75370bb284,0x4dbb0ca1280907ba9b56,0x41eea6c58750940483dd,0x250120f7536cc3a84a02,0x2ecb1280907769b56595,0xba6e57658940483f54da,0x120edd36acb2c4a0241d,0xb12809076e9b76596250,0xd1a758940483b74db32e,0xfb5368bb2e4a0241bea6,0x809075e9b95d97250120,0x75c940483af4dbb2cb92,0x36ccbae4a0241d7a6c59],#[0x7e69b25d96550120ebd,0x540483d3cdc2ecb2a809,0xc3acaa0241e9e6dd8659,0xa9a46897650120f4f36c,0x483b74cb344bb280906f,0xeca0241d7a65da25d940,0x26a17650120cfd352d12,0x5ddda350bb280906bebb,0x2416eeed1a561940483,0xd8650120b7d764d3b0ca,0xda342c3a80905bbbb469,0x16faec9a661d40482ddd,0x54120b77768d330ea024,0x8b12c0907b69b661152,0xa6dd8458960483d74dab,0x20f5d368c3ac4b0241eb,0x12c09076e9b465d62581,0x1765c960483b75da32eb,0xbd368cbae4b0241f3a6d,0x9075ebb465d7258120e,0x59160483d5cda30eb22c,0x68cbac8b0241dbaec997,0x6ee9b269d6458120ed77,0x60483e74d92ecba2c090,0xbae8b0241d7aec9975d1,0xbb56a17458120eb7768c,0x8357ddb350ba2c0906b7,0x8b0241e9e69d65611604,0x5d98458120f5d364bb30,0xbddab4ec22c09078f9a7,0x2416beed9a761160482d,0x6558120f4f368c3acab0],#[0xa32eb2ac0907679b465d,0xbba691a25d960483b3dd,0x8120bdd768d12ecb0241,0xebb2c09078f987691765,0xed5a461d60483c7cda30,0xb5f76cd230eb02416de,0xac09067e9a4e89975812,0xa465d60482bf4da744cb,0xd362c22e4b82415faec9,0x9079e9b6611725c120f3,0x9170483cf4da30cb92e0,0x4d3ac8b8241f3a6c9765,0x9fbb76a1645c120dbd36,0x483cdcda30cba2e0906,0xb08b824167eedda16117,0xb25d9845c120f4f34cb2,0x3c7cd32ecc22e09079e9,0xb824167eedda66117048,0x19655c120f8f368bb2ca,0x4d2344bb2e0907a79b46,0x4177aed1a25d9704836f,0x65c120f1f30cd22ecb82,0xb48c32e09078f9b46197,0xfeec1a961171482cfddb,0x120a7f760d4b0caa2414,0xba2c8907cb9b05d97459,0xdd865d164483c5edc2ec,0xf17b6cc3ae8b2241e2f6,0xc8907a3db461d6559120,0x75956448393edcb0eb2a,0xb70cbacab2241d9e6c19,0x727db76616559120e4f],#[0x96448393fdbb30b2ac89,0xd02ecb2241bba689a05d,0xbdb461d7659120bd7768,0x48387fdbb30bb2c89078,0xecb22416afed1a85d964,0x46a17659120d5f760d42,0xd5fda34ac32c8906abfb,0x22416beec1a761964482,0x18759120b57f68d3b0cb,0xd834cc3ac8906abda669,0x14feec1a961d64482d7d,0x59120a3ff6ed4b0eb224,0x52c3ac89063fbb06a587,0xfed9a961d644831bfdab,0x20c3ff6ed4b0eb22418b,0xbac89067e9a268197591,0x1a865d64482bddda340c,0x6ff6ad432eb22414efed,0x89052ffb66a19759120a,0x661644828ffdbb50cbac,0x60d3b30b22414feec1a5,0x537fb569d9859120a7f7,0x7448297fdb34ecc2c890,0xb2caba241f1e6c176595,0xdb4619655d120f0fb70b,0x83c3edbb0cb2ae8907a3,0xaba241c9f6e586595744,0x661655d120f0fb6cc3ac,0xf4d1340bb2e890727db6,0x24176eed1a05d9744836,0x765d120f17b68c32ecba,0xb330bb2e890717fb5661],#[0x66fed1a85d97448387fd,0xd120d3f760d42ecba241,0x8c32e89069bfb46a1765,0xec1a7619744834ded3b4,0xa7f760d4b0cba24167e,0x2e890537fb56a5865d12,0xa161d7448297fdb352c3,0xf760d330eba24166fed1,0x9059bfb4699875d120b3,0x61744829fdd8342cc2e8,0xad0b30ba2418dfe95a16,0x1ffb7685985d120a6ff6,0x44831bed374acc2e8905,0xb30ba2414df6dba56617,0xb6e95985d120c6fb63d2,0x29fdd834ccc2e890637d,0xba2414dfed5a66617448,0x5d9161120a3ff6ed3330,0xcd82ecb2b0890537fb56,0x41e1f65d7659584483d3,0x561120e4fb72bb2cac22,0xaecb2b08905a7db95d96,0x9fee5765958448393f5c,0x120e4fb2ecb2cac22416,0xcab08905a7fb76596561,0x89a05d9844831bedab4d,0xe1fb2ecb2ecc2241afa6,0x890537fb56a57661120,0x95d98448297fdb352bb3,0x760d4aecc224147fedda,0x52fdb6aa5766112097f,0x9844828fedbd52bb3089],#[0xd4aecc22410ff6eaa95d,0x7fb565d966112097f361,0x4825bedb74acbb089053,0xecb2a41f9a6c97664165,0x46817659520dcf348d02,0xc3ec3b48bb2ca905e7bb,0x2a41a9f6a1a45d965483,0x17659520f0fb68c3aecb,0xda350bb2ca905a7fba66,0x1a9f6d1a85d965482d3f,0x59520d4ff68d42ecb2a4,0x48c32ca906a7da769186,0xeec1a761965482d3fdbb,0x20b4ff68d3b0cb2a41e9,0x3aca906a7da669187595,0x1a661d65483d3dd834cc,0xfd748c9320bb24169fed,0xc9058ffb7691865d920c,0x61d76482cbfdab48c3ae,0x45d0330bb24163fed9a4,0x53f9b4e81985d920e7d7,0x764829fdd8348cc2ec90,0x2330bb2414dfed5a4661,0xfb7691985d920a5ff6cd,0x835f5d1740cbb0c9051f,0x2c3a412fe6d3a065d864,0xe959461d20a6ff6aca32,0xbedb74aca30e90637d96,0xa41afae8ba0659874825,0x625c16097f369d032cc3,0xa34eb12e0b06cf9b469d,0xb3e691a25d97058367dd],#[0x8960b9f768d12ecb82c1,0xeba2c4b078efb261d745,0x693a261d62583c5fda30,0xb5db69d130eb12c1abb,0xac4b05afbb0691875896,0x8759572582d77d9348c3,0xff68c3acab92c1e1f6d1,0xb05cfbb0691765c960f0,0x1d72582e77d9348bb2e4,0x9d130eb92c1a7b693a26,0x9fbb0691875c960b3db6,0x5582cf7d9348c3ae4b05,0x30eb2ac1e9eec1a261d6,0xa46898759560d4fb48d1,0x2d3fda344c3acab06a7f,0xb2ac169f6d3a261d6558,0x81925d960d4fb69d130e,0xcda740c92ecb066f994e,0xe12fe6d3a06498758277,0x659570f8f364bb320b2a,0x344bb2cab86c7da46897,0x7e653a0649765c2e3fda,0x1659bf369d0324bb2e19,0xc82ecb2f47f976897660,0xd3a26417659733fd2324,0xccfb68d1720bb2cb39f6,0x80907fa9b46897650120,0x761940483dddda350bb2,0x768d3b0ca0241efaec9a,0x7bebb26998750120f77,0x160483dddda34cc3a809,0xd12ecb0241ebe6e97661],#[0xe9b26917658120fdd368,0x483bf5d9348cbac0907e,0xecb8241e7e6e97661170,0x2691765c120fbd368d12,0xd5fda350bb2c8907de9b,0x2241ebeec1a761964483,0x98759120f57f68d3b0cb,0xda34cc3ac8907afbb069,0x1cfeec1a961d64483d5f,0x59120e77f68d4b0eb224,0x52c3ac890737fb56a587,0xa689a065d644838ffdbb,0x20efd764d032eb2241df,0xbac89077bbb468197591,0x1a865d644839fdd8350c,0x6ff6ad432eb2241cefed,0x89072ffb66a19759120e,0x661644838ffdbb50cbac,0x6ad3b30b2241cfeec1a7,0x72ffb669d9859120e6ff,0x74483cdfda350bb2e890,0x3b0cba241e7eec1a7619,0xbb06a5865d120f37f68d,0x839dfda352c32e89073f,0xcba241cdfed5a9619744,0x699875d120e5ff6cd4b0,0xdfda34cc3ae89079fbb0,0x241cfeec1a666174483c,0x985d120e6ff6ad3330ba,0xcaecb2b089071ffb7699,0xe9f6dd9659584483d3ed,0x1120f4fb6ccbacac2241],#[0xbb308907af996681766,0xec1a95d984483cfccbb4,0xb6ff6ad4aecc22416fe,0x3089073fbb06a5766112,0xa95d9844839bfdab52bb,0xff6ed4aecc2241cbfed9,0x906bfbb06a57661120e3,0x59844835bfdab52bb308,0xd0b2ec22416feec1a76,0xbfbb06999761120b7f76,0x5483f3cda340bb2ca905,0x2ecb2a41f9e6c1a45d96,0xb46a17659520f4fb70d2,0x3d3fda350bb2ca907a7d,0xb2a41e9f6dda46196548,0x9d8659520f4fb68d3b0c,0xedb348c3aca907a7fb46,0x41e9f6d1a661d65483d3,0x5d920f4ff68d330eb2a,0x328c82ec9077e9a46499,0xfaec9a464176483bf4d9,0x920dfd344d0328bb2417,0xca2ec9073bfb4661945d,0xd5a865176482ddfda350,0xb5ff6cd4328bb2416dfe,0xec9059ffb76a1945d920,0x466176482dfdd8348cc2,0xf6cd2330bb2416dfed5a,0x59ffb7691985d920b5f,0x1764839fcd2740cc2ec9,0xd2330bb241cfee93a066,0xbfa4691985d920e7f760],#[0x4839bfdab48cc2ec9073,0x30bb241cbfed9a466176,0xe91985d920e3ff6ed23,0xdfdd834aca30c9073fbb,0x3241cfeec19765186482,0xd9461920e77f68cbb28c,0xda34eca30c905bfbb069,0x16dfed5a765186482ddf,0x61920b5ff6cd3b28c324,0x40cbb0c907beba2e8197,0xee93a065d864835fcd27,0x20b7f369d032ec3241af,0xbb0c905bfbb069197619,0x9a465d86482dbfdab48c,0x7f761d232ec32416bfed,0xe905bfbb06859461d20d,0x65187482cffdbb42ca30,0x68cb328c3a41cfeec196,0x5bfbb06999461d20e77f,0x87482ddfda34cca30e90,0x32cc3a4167fedda6651,0x9a4e819661d20f7d745d,0x835fdd2740cb30e906bf,0xcc3a416fe6d3a0659874,0x6919661d20b7f760d232,0xfdd8748cb30e9059ffb7,0x2c1f3e6d1a25d9705835,0x8758960f5f760d230eb1,0x8348c3ae4b07aefb2691,0xe7bec9a461d72583cfdd,0x9560f4fb48d130eb2ac1,0x4c3acab07a7db4689875],#[0xec1a464976583d3fda34,0xe7f329d0324c3ac17be,0x30eb073fb94e819261d6,0xa0649875835fcd2740c9,0xf369d0324c3ac1afee93,0xb06bf994e819261d60b7,0x4987582df7d9328c930e,0xd2324c3ac1cfbec9946,0xb7fb56919261d60b7f76,0x7582d7fdb348c930eb05,0x324c3ac167fedda46498,0xb06939261d60d7f761d2,0x3e3eda344bb2cab86bfb,0xbb2cb77eec1a4649765c,0x89905d965ecfb48c9320,0xfda344c82ecb2ee7da46,0x16fbec994609805daf3,0x9c02e8024c019800cc00,0x38066c06000504042003,0x440990090c084007bc07,0x800c9c0be80b4c0ac80a,0x1c10680fb40ed00e4c0d,0x2813a41320128411d011,0x1c169815fc156014ac14,0x2819a41938188417b817,0xac1cf81c441ba81adc1a,0x4820941fe01ee41e301d,0xe4243023ac22c821fc21,0xf0278426e8267c25b024,0x142a48299428f8288c27,0x802d9c2d002c642b982b,0xec310830542fb82f1c2e],#[0x7034a43408338432d031,0xac3828378c3708365435,0xe83b4c3ab039fc393038,0xf43e883e043d383c843b,0x48419440c840143f903e,0xcc4560447c43b042e442,0x4847dc47884704469845,0x944a1049a4495048e448,0xb84cec4c504bfc4b484a,0x5450a04fa44f084e244d,0x536452c8524451d851,0x445778567c558054cc54,0x205ab45a4859c4591058,0xfc5d785cf45c705bec5b,0x78600c5f585ebc5e685d,0x5462e8627c61b0611460,0x786624657064ec642063,0xfc696068c4681066fc66,0x906c0c6b886b1c6ab069,0x946e286dd46d686ce46c,0x711c70686f546ee86e,0xc47410735c730872b472,0x587704769875fc756074,0xec796878e4786077dc77,0x687bcc7b607adc7a7079,0x447e907ddc7d707cd47c,0x6080f48088801c7fb07f,0x5483d0831c825081e481,0x58860485b0852c84c084,0xec888087b4871886c486,0x708ba48aa889dc895888,0x6c8f888ed48e088d3c8c],#[0x8093cc9300921c916890,0xac97c897149648956494,0x789bac9ab09a2c999098,0xa49ff09f0c9e409d449c,0x10a32ca290a1f4a140a0,0xb4a7d0a6d4a5f0a4f4a4,0x38ab6caae8aa04a938a8,0xbcaf20ae54ad70acd4ac,0xb0b1e4b130b094b058af,0xbcb4f0b43cb3b8b364b2,0xa0b8bcb7f0b73cb670b5,0xacbc10bb44ba78b9f4b9,0x8c03cbf70be74bd90bc,0xd4c408c33cc288c1a4c1,0xd0c7ecc6f0c624c5a0c4,0x54cbd0cb34ca50c984c8,0x68cf9cced0cdeccd08cc,0x94d350d26cd1a0d11cd0,0xd764d698d5fcd530d4,0x24daa0da04d938d89cd8,0xc0de0cdd58dcd4dbd8db,0x14e130e094e028df5cde,0x20e46ce3e8e364e2c8e2,0xece7f0e724e688e5d4e5,0xa0ec34eb38eab4e9e8e8,0x6cf018ef34ee98edccec,0x20f30cf240f1a4f108f0,0xccf648f5c4f540f4a4f4,0xf8f9ccf900f84cf750f6,0x74fcc0fc3cfc00fbacfa,0xb900ed0038ff6cfe40fd,0xf504a104050369026d01],#[0xf908b507b906d5062104,0xa50c090b6d0ad10a7d09,0xe10f2d0e910e250d410c,0xd1311122d117910950f,0xf116dd15e1151514c114,0xa51ad91a0d197118ed17,0x811e2d1d911cc51c291b,0x8d212120551fa11f051e,0xb123e5233122ad21f921,0xed26f1263d25b9251d24,0xc92a2d29912925287127,0x4d2d692c9d2c012b4d2a,0x2930752ff12f6d2ee92e,0xd34413345329131c531,0xc13825378936d535f135,0x8d3bf13b3d3a29398d38,0xe13f153e493d953d293c,0x5d41d9416d40e940653f,0x5144cd4431439542c942,0x2d47c1473d46b9463545,0x3149dd49714905489948,0xad4c294ba54af14a854a,0x694e154da94d554d014c,0x8550194fad4f294ed54e,0x89520551b1515d50f150,0x8d542153cd536152f552,0x1157a557215655557154,0xa55a3959cd597958c558,0xa95c3d5bd15b7d5af95a,0x9d5ee95e355d995d155c,0xf1623d61b9610560215f,0xcd6531649563f9638d62],#[0x3167c567596705669965,0xed6999692d68d9688568,0x96bb56b616af56a8969,0x6d6dd16d4d6cf96c8d6c,0xa1701d6fb16f2d6ec16e,0x5d720971b5716170dd70,0x17395732972ed729972,0x3575c9754574d9748574,0x977b57761770d767176,0x3d79b979357881784578,0xe97c7d7be17b457ac17a,0x4d7ee17e5d7df17d857c,0x2180b5807980257fb97f,0xdd8271821d81c9815d81,0xb9851d848183fd837982,0xb7c460a0198249cd9185,0xb82409753641c71cf60,0x259cd8e048034a4353df,0x71a36109cf7c2e0f8198,0xdc78f82c71782871e059,0xe2a09019e0b5c5e0a1c6,0x91cd9371605982971b71,0x8220219cf60b60a3c460,0xcf108778280937365022,0xd8228808808773d70d82,0x2971771f718460b60a5c,0xcddc78a059024f0f82d8,0x82871f7362819e0b60a1,0xe0b60a5c7dcd9007782d,0x971af1e282382301d819,0xb48e3c7dcd8f82d82805,0x66f1f7362a0a40925160],#[0xa5c781dbcd8a02c0280,0x82542931e050f1a300b0,0x60950a2c59c6ac78f317,0x5b17b19429b1e4c0b28c,0x6cc79006e238a3102d82,0x81a10d60930a4c5c8c1c,0xc693d0b82531e14b71a2,0xc40ba8e6094c5cc7d0a3,0x2531742931ef1a3c0c88,0xc5ec66c78208e14b2318,0x13af1f336390d60928c6,0x3c7ccd8e077238825429,0x75443023c4e88e60950a,0x7acd8b824088a38092b3,0x24b3771e2a8e50a6091c,0x1dd0a1c7ecd8aa380698,0xa3982471f429b3639510,0xb0a1c7cc68150c08e242,0xb71771982571e300e1c5,0x914cb0a4cd8258a055d0,0x93238f10097c29336320,0xcf742b0fc8e024ccd900,0x71e097337c283825e094,0x30a4cd8220808e239824,0xf23807671fc293362c8e,0xe90fe0930a48e1c7ccd8,0x69825d0b23971f336401,0xc5d0a4c6bc78c09007a0,0x23913af1f336381528c3,0x50a3c7ccd8f034824a43,0x8f1f336288e40d290e09,0x91c7d0a6cd8e03802406],#[0x29824f36509090fa8e60,0xa088082080f0d1452434,0xd20950a4c7c513cd8e08,0x3d824096737c283819b0,0x19f0a1cde908e08aa427,0x92737a424025824cc78,0xdcd9206843582570cc28,0xc3022a90dcf60930a025,0x24206731fc287362820d,0x10d60930a4c7c909cd8f,0x9825d0b31f243736401a,0xe2c7a515cd9009007a06,0x7af36220fd0d30a40948,0xc7cc670a0180c03931e0,0xc29425b3608620cf4c5c,0x20d6c310a5092cd8260c,0xa4cd8dd0b425b361722,0xc2933638264cf781825f,0xb511008e066097e0731f,0xd025c8e4cf024d094cd,0xd90096f11c280673362c,0xc0d30a50948e2c7a514c,0x182e05d91791f71a320f,0xc6096459c6e478560d83,0x3d42991722d91ef1a4e0,0x8b647dc68d83082f0249,0xb1a0555323609052e45a,0xd47ac68150d82551751e,0xfd1731bd1e3e09545dc2,0xa2c6b479233b23805dc2,0x81740b40930ba4f345d0,0xc93d025d1722cb1bd1e4],#[0x5a8b4c6f478e834c2f05,0x5d71f936281550be0974,0xd5c29c7e4d8d8398340,0x82471f70b936401de0e6,0xdc7e4d9204803e835839,0x1f81e81d81760e60d5c2,0x2494983922cf1f93638,0xe00d01764dbc78a835,0xa038034f0a07771f9363,0x5362e0e60928b5c7e4d8,0xd4ed4d9053b435824b1f,0x6381229080f90d6092c7,0x9014943453ab1f82553,0xd149081770d4c7f4d8c,0xd824082c34097344d363,0x3825b0d50a024e90b4d8,0x24948c3505d428b1ed36,0xa4092522c7c8b74d910,0x8254355360922a0fb0d5,0x36350d290d4d8208853c,0x4d8a025434148c2931f5,0x71f9363d0d6094c7a8b7,0x64d9007643f83513ac24,0x120d100fa0d44e9c7f09,0x43f83493a71f42593638,0x50d309025ad154d8c148,0x409631eb45c255364026,0xd025824d4d9009804803,0x1f5364ec402954f02650,0xe07a077435b0be0685d3,0x536402494f54d8260807,0x3409809654909271fa2d],#[0x6086280d3c454d824884,0xbe4d82606b33424f0b93,0x8260c09713d936098201,0x6082220d6c310fd0964d,0x201be4d82607424b1f93,0x64d8248a034f0b936096,0xa09793608c390fe0d24f,0xff0964d8f93c034c25f0,0x3609218260232ccbc2d0,0xd30950a6c7e4d8d7119,0x149e07428b1f93640126,0xcc781de4d8805c83f834,0xd84383f82473a7364a4e,0x79ce9cd8c08a08408273,0xb91f7365610e0f819e4,0xa06806605d84371d83f7,0x35c2e0f824825bcd8e06,0x4203f91e05cf362e10bc,0x60842e10e0f822dcd880,0x7819dcd8c04d84382573,0x99c24b36301080fbc2e4,0x47c512cd9114408433a0,0xc243819a8e20d0ceb095,0x9409014851e33a099337,0xc7547ec2f81824f0fccd,0x85d51f336501a81a019c,0x6a06806743f31db0be06,0x8e40d251347d094cd900,0xc2409673794440520cec,0xe8b1cd8e06663843570c,0x60982e170261cf152025,0x96cd8208843f231424b3],#[0x91d11425b36158230fd0,0x94cf7c2d0f852025ccd,0xf0a148099c253362823b,0x362ec31043094cd8228a,0xcd8248a092f0bc3e0673,0x43fb36258240d30fa47c,0x29b3630182cd82287e07,0x47acd8e048a38c2591f4,0x336201720d05228e50a6,0xe45e47ac68c94591e067,0x913ae255363742f81f80,0xcc7c4ed4d9009b53c09,0x3618a201d819c51781f8,0x4ed8964d8268993a6259,0x93b93c09854562593642,0xf80cc7c24e4d9014809a,0x39360902829647742f81,0xd172c7e4d8e03de07e0,0x2593608a1e47742f81f8,0x65f81f80f42ec474d8b6,0x98097e07e0333c89333,0xd514cd8e03dd0a0a409a,0x1b363019c47f81f80825,0x43cd8de07e0204bd0bd1,0x1f3183812f81f80f42f4,0x6288b1bd0be07e033173,0x31eb3645c20248cf6cd8,0xf42f81dc4780ecd8ab1d,0x628693391791f51a0602,0x82f224d3618a2c8974d8,0x8a1825c4f74d86289431,0x25c4f54d82689225d361],#[0xf74da2109a2553609a18,0x1ff0a62523f9365825a4,0xe08c83903409793c08f9,0x654c8235c2a8fb8964d8,0x3ca4370aa3e493936482,0xc4124e4d8e09a0981499,0x936096182382364f5c2e,0x3608e3d8964d8228693b,0x4d8e06793c09791ff0b9,0x3781f80e4f3c2ec4124e,0x8cf1109393d70a067936,0x63025e4f7c2819e4d823,0xd88a5d91cf0b51e06793,0x8f5360961b4f5c2b4d89,0x62f81f80ec401674d8a0,0x634d8be07e03b10058d3,0x3d11b362f81f80e4781,0x8e547b0a68d8b70be07e,0x83e63d4356360982e0d4,0x360822ec1d0d58d82088,0x47e8d82489330c3f707a,0x834a3b91f425a3631094,0x983541a8d68d82608049,0xa088849b0c43e543a360,0x97a3608c3e8d150e8d8,0xe8db4b0e048543a3df0a,0x609220260232ccd50d0f,0x1f4468d82089510a35a3,0x82188f0a06fc36086274,0x6fc360822080acb70d,0x2080bc46c1f0d8208af1,0x70d82391b07711c36082],#[0x63825f0f20d647fc2823,0x8de03c3d707b10493c3,0x8a2080bc1ec470d8208a,0xf8566cd88c4343fb360,0x530a3f706d3608a2f41d,0x3fd36184181b34d82687,0x61841c4f11254d82688a,0xf7c2825e4d8238d23fd3,0x31a3ea45937624428fe4,0x1b58d8228809a0900495,0x38a110d25a3608a26c18,0x29736400f3c2ec0f0d82,0x408e08c07606782d71f8,0xb0183c5bc660a3c78199,0x28f1f736460b40901b81,0xcd9182c08e08c0760678,0xb01e01d0159d1bc5e0a3,0x8c06607771f828f36460,0x8c2c7dc68209182c08e0,0x71f3363818e0901b2c5a,0xccd9209013b238c29825,0x2301ec8e01a30a6095c7,0xf16068f19238f1e50240,0x81a0e08382407006c062,0x64e0902401ebc7c8e4cd,0x82406807b42971ea38b3,0x81adc7b0a6cd9009143f,0xf825736382460902381f,0x95cd92090145242c2931,0x2301a49081ecc7b0a60,0xa069428b1ea437364824,0x5e093cd9009143582407],#[0x363c9081f01681d0d1bc,0x324209006807b31f824f,0x24cf08e309190ccdf0a1,0x96349337c2848238258d,0xa0c08e08c06733de060,0x962825823819ac7ccdf,0xd096cd9408e067c28b36,0x23a51490a4ec8e30a6c7,0x239424c29b1eb3640240,0x2c7b0a6cd90868042834,0x3b36521ea0f80e090d09,0x87b238869425d0bb1f24,0x6c7f42fc00231009008c,0xbf01b1e482381d819fc1,0x8db0fe07067f05076d0,0x4187c16095c7b42dc60e,0x571e067d0bf0008c341b,0xdfc160d342fc05c78ff0,0x5783f716d0b736302341,0x1dec7f42fc00230d0750,0xf0570ed0bf01b1e4fc10,0xbc6e461208d83f067825,0x1a81a019856645817647,0x60f18f1605cf1f91a50,0x3c7e4d93839834064062,0x1f81ee0e60d01d829017,0x5c0a4f0a07771f93650,0xe0e64d9207e07b839834,0x2401ee0901a0235c7bc2,0xd9003571ea2d93608c28,0x82405250d4c794ee0954,0xa08d31ef0b825d364c10],#[0xb74d8230a09006924207,0x7a93b71f936400fcc7a8,0x4d8230c07783405c0a40,0x93608c300d3095c7a8b6,0xb0964d9203493b71fc25,0x1fc5260d01a82444edc7,0x43408f31fb0ac2553640,0x4c7a8b74d8230c148439,0x531fc25d3608c300fb09,0xd360a4374d8290403e34,0x54d8248e07a07605db1e,0x6548450d02921ea1dbc4,0x85d43482443982971f53,0x2901e81d9c7a1754d8e,0x4d8290b711d360921952,0xf0b936096381e81ddc7b,0xe4df09118340a447a45c,0xc382402601a0234c7bc2,0x34b32098f0bc2593608,0x60d023a4eec7e4dd0910,0x5b1ec2993608e3c0e024,0x7c4eb0964d9003983542,0x779364a10a0fe0d0522c,0x583407e07a45cf0b31e0,0xd360a42dc2f4d825860a,0x98b7c00231007a05db1e,0x8c421ea1a5c13c16c7,0x87a868f0bf05b1f607f0,0xc1ec1a5c2ec7b0974d8c,0xe05742983ef16946f364,0x7017647bcd9205b84205,0x365610e0f81a81a019bc],#[0xa06805d71cf0a06791f7,0x7b094cdcce9184383e06,0x25b36401085250f823d4,0xc06b14809007f33b51ec,0x4ec741741a419b47ecd8,0x1c06605c06991e945736,0x95c5951dcd8e06b6397,0xc3e7360924016815e0a6,0x5cd9006af0806806609f,0x1750fa09110d47e0a152,0x71c06806751e73685c42,0x41a419b47dcd8a06a548,0xc098148545337c2445c7,0x2819ccde479433a091b0,0x81af0fbc202481a027bc,0xe09008f91eb3b425b364,0x7b0a6cd8238e94504383,0x24b371444010e0fd0964,0x479233a83883414991ec,0xa81a4c71173c2819ccde,0x5d06970ad1fb36360f81,0x8a289744745f4d8bb1d0,0xa35d16a25d0bb1bd1e3a,0x2344ecc7b8954d92080,0x51455364c5100f85210d,0x8e08d13a07606731ee2,0x50d019d892c7d4da5110,0x762531e93ad36401dd0e,0xee4d8a58e06724323e07,0x36296282911f91e91724,0x5164db891131f91c93b9,0x9364c526c302602401a5],#[0x4954408b91d13b31ee25,0x81f80e472c7e4d9a0a51,0xac1a419d17027824f42f,0x68067936b1e09e302941,0x236c798964ee4d9006a0,0x62593608c320e40d0238,0x24ecc7e4d9003493bb1f,0xf936301d81f81e829589,0xee4d8d91d06b069066b1,0x8f9363419f81f80ec7a4,0x42e4d90076067b1fd0a0,0x3023823781f80c19ec7b,0x8b71706f06cd0b71f718,0xf9363dc7f42819e4d823,0xd9408e08d839834d0b71,0xc17781f8082914eec7b4,0xbb1f5362762c1fc1ea19,0x1742f43fc06c78e08f53,0x3fd0ab1fd1a3a8fa897c,0xc16c7f468ca43d1c504a,0xb10f0dd364747742f81f,0xb4d880a4893d0be07e03,0x2b1fd1dd1a33470296c7,0x2ec798974d93d0be07e0,0x363a1fc1ea1ac1a02474,0xc09008c94493bb1f625d,0x2a5124eec7f81f80f4d8,0x8290b94993a08b625d36,0x7e03d363a5224eec7b4d,0x7dc60e948b1fd1c945e0,0x1a3a1a219f46dc5824dc,0xc85c09e868867f0571fd],#[0x461ae1a619824dc474d8,0x6a868866d1d71ed360a4,0x230525514cdb891409e8,0x544502644f00d6c30258,0x3c09606614911ee25337,0x24899ccdb511008e08d1,0x336d442ec302781a81a0,0x647b514cd95b0c096267,0x29027c8e48d0204c7589,0x7acd98067544b3609620,0xacf2c7426c26029425e4,0x5945b364742f81f80c24,0xd8c84303e08e08d91e62,0x36480fa51647d890236c,0xc06a06806762591e9453,0xa431036cd8290605d31,0x6cd8c07e07a07791eb36,0xbb36341df81e47f80a51,0x2ecd9007606791e08fd0,0x823823781f80c1de47b4,0xc067e07e02d1e545b365,0x16cd8a87706b06905db1,0xbf01d1e3023d47899d5,0x206cdd510aa25f04a35d,0xa35d1eb360a42e8e68d0,0xc1e41d5c5b42dcd8aa38,0xc39408fd0b91e0777362,0x9c860ffc1647b42fc05,0x76547717736382382361,0xc5d51dcd900a485c87a8,0x736661ee17742f81f809,0x5d877d11e07e02f0c281],#[0xc5dcd8e48448387f87b8,0xf36182921fa1ea1d951d,0x46f3628293cd8473c0a4,0xc3012bcd8fd0be07e02d,0xf01d1e4742f81f80f441,0x9885c0a487a877f0570f,0x1df44781f80bc30a05cd,0x71a4121120e1fe1ee176,0x1c0a487e87a876704d1f,0x42f81f80ac5cd1ecd8f7,0x234097c2d336348451ef,0x91dccda248ec5c09933c,0xd31f33650d202911f91e,0x33c07331dd0be07e02c5,0x8d24c74c7ccda248c0a5,0xa34933d31f336c5c3027,0x9333660d24cda248684,0x7706b0690660a531cf10,0xc7ccd8278e09ec7ec7ac,0xb1f71a481a81a019c24a,0x94b18b17d0be07e0204a,0x901230b50a6c7ecd940,0xb1f3366a90c8fa8e48d1,0x6906731c0a5d0be07e02,0x1cecd8a87e87a87706b0,0xb1eb360a41f42f81f808,0x6c7742f81f80ac7ecd8d,0xcc28c25f05b0ff01b1e3,0x32c7742f81f80ec7acd8,0x920a5d0be07e02b1fb36,0x81f808086c70016c7ec6,0xc28c25b1fb362012f42f],#[0xe1ae1a619824dc46cd8c,0xb49c2dc29c2531ef363,0x90e60ba8954d8268e08,0x9808cb459376244c4f09,0x4d8230e93b03409193c0,0xe24480d64f0263c2d896,0x9883dd0c14913a345936,0x23647b8964dcd11409a0,0x963823a1991664f44e8,0x8665c0a427e27af0b936,0xd625937148411864d822,0x2e4d95b1106644af0b93,0xc19825e47781f80e47bc,0x7e0391f936f0a582949d,0x8e08d27627706793de0,0x497647019dc2e4db4794,0x6d1e09e2827a9dc1ac1a,0x2d47e4d8198c06a06993,0xb51f937066402389dfc,0x4d8259008e08c45193cf,0x2c9fc9ea19c970295c2b,0xc258c08e067f0b536096,0x608c4023823419bc2d4d,0x44343822d225d1ef0bd3,0xe4741ac1a5c2b47e4d8d,0x47b4d8290b70a097d361,0x76067d1fd36301f81ee,0xfc13c2fc00238e08e08c,0x5d1ff0170a441dc19f47,0x5f4d88876867e07d0ff0,0x67d1ed360a42619dc282,0x47f47781f80dc2f468e8],#[0x8e08c067b1fd362a1db,0x6c7d097c13c2fc00238e,0x7e03e0770b947b36450d,0x9ec2825bcd8947b45cb1,0x4208151fc3eb3af36331,0xe382382301df47ecd8bc,0x43f424f0bf05d1ff0008,0x81fc8e547bc2e0d68d95,0x9a3608e2c1250f82381a,0xee0d48e68d8e04951ec2,0x29a3608e2024023e47a8,0xe4c7a4b70d8230d91ec,0x34531e92dc3608c30123,0xa1a6c794b70d8230a048,0x868f0bb1f507c3608c3,0xd0236c7f41f0d8240c09,0x69835b1f70ad07c36420,0x47bc2e8dd50920918490,0x8c341201a02602348d4,0x8240a048b32099a36d2c,0x5a360902a8d309647e8d,0x794b02378d8a94391fa3,0xb91f507e3608c3a1ee4,0x2374182478d8c09087af,0x91f70ad07e36420fe478,0x823f0d8e09184907b83f,0x7c36509d823019fc2e47,0x86906608de0391ef0b70,0xe479cb70d82310a7b276,0xfc36f0a4c9dc19a8fb4c,0x8f848451067c3d707a3,0x14c647bc2dc1f0d82312],#[0x6f0bc3608c382421a114,0xa70d8238da3e481c3d70,0x35c3608e330ed0d74798,0xc2fc00239086af0bd1f4,0x9a350ff47d0d0c87c13,0xe4d96242449d0d23f536,0xf607824023a91490f80,0xe2993608e3826a4ec4e6,0x74d8238c533d0d83c09a,0xe08fd36331150ff0798a,0xb68d8268887ef0bc1f43,0x43c3c72dc3608c389221,0xca5c1f0d8231093f4395,0xc3608e474421a092f0f2,0x8b542090281c3cf0bb03,0xb066282381fec6b0a01a,0xdf428198a08d077b1ad0,0x8c50b077066202382301,0x62023823019f4281d8a0,0x2027d469008c50b06707,0x8e301f81260a6093c33c,0x1a8c09007f91ac0206a0,0xe062824023e46c523090,0x291521208d70b07b068,0x1ae0a6095443c33c23c0,0xf8a09006ac0207e08e28,0x66d0a2824023c5230901,0x1df428198808e08d91b0,0xe8808e08c50b06620238,0x8cd0b066202381981dd4,0xa18296c7f477468808e0,0x20a5d4e9430653bb1fd1],#[0xc1a1890e0a4b1fd1dd1a,0xb068282421fa1ae5241e,0xa0245890a08d07a60607,0x86625b1fd1a182301e81,0x80a562460c1ec7f47746,0xd1dd1a18296c7b473468,0x101827dc7f4774688b1f,0x27dc7b473468a0a470d7,0x10808e08d076d0a20290,0x8cd0b076202381d819d5,0xa1827f47ec76c68808e0,0x282955114306545d1fb1,0x81d880a409fd1eb1cb1a,0xe08c50b0762023819f42,0x70e18295c7747dc68808,0x8295c7347dc6880a4f0d,0x9c24b0cf0834931a8924,0x33c24c68279209fc2dc2,0x484024c1ac1a4198d22c,0xf47f47b476f080a50923,0x201a50b019ac6ac40a09,0x6c69170e07af0c076348,0xa492381f81ab0a3096c4,0x687349c2dc29c25b11b1,0xa545c40db1a21176c7ec,0xdb1a18296c7ac72c6880,0x9027ec7ec76c68ab1fb1,0xa170278849334830c182,0x887a87685c0a4221a219,0x6808c2a1ea1da170290,0x64681a3890c09191be06,0xce0991a65c3824023452],#[0x26469970e08b14913ac0,0x66f0a2825c19b433c2bc,0xc00279d11208e08d91b0,0x3824c1ac1a419b433c23,0x9e097066d0cf08f00744,0xa3823823419dc43c28a0,0x27f27b27725cf080a453,0x25c19b433c23c014e8d,0x1a0230c08e08d066f0a2,0xd1aa24302421ef46981a,0x81a60d0c09008e47e46b,0xdd1b228401ee0ff46881,0x28887f07a86b069948a2,0x45d1a93a1823823746ac,0xa93a265264ef46822889,0x1a521802510608a948d1,0x619f4682586876867d1a,0x1ddc28609686770ad1a2,0x66f0cf08f00f0a31c02,0xa202341dc19bc289077,0xc35c01c287d1fd1dd1b7,0x7346dc28a0a470d70a1d,0x1fd1dd1b70a2029747b4,0xb7180922a1da19dc286d,0x46c26c06c28c868867d1,0x88067b00b0a191d819cc,0xdd1ab0a2a1a217219827,0xae1a6198248886a86885,0x8409286a86886609e2e1,0xcf08f0009f066281d819,0xf0b066182301dc1986f0,0x66096121ddc2a1987076],#[0x887770a1025dc2a19878,0x8760a4221ea1721d8290,0x919cc3ec36c28a87e87a,0x1d82908077b0cb0a181d,0x87a85dd1eb0a2a1ea172,0x76121fa1ea1d8290887e,0xc33c23c002941d8c0660,0x2c1d8608c0670761825b,0xa1d8486770a8761c19bc,0x9cb0238e86770a15c2,0x91d06282401f81ac123,0x5c2c1a3418a08c07a068,0xc07a068091d062824023,0x30240235c2c1eb418a08,0xc86984808d066f0b706,0xa2025c19b433c23c01cb,0x6e0e1808c08e08d066f0,0x66b06f0a202401ae1270,0x2c1dc198233c2890770,0x9bc288f0c30af09700f0,0x77067b06f0a202301d81,0x6b061bc291eac191a090,0xb0770a20232c18487686,0x770a261982584876867,0xa1a1dec1dc286096867b,0xe91a6c18230887686770,0x9006b048e0272c08e311,0x6282401fe126109808a0,0xa4c90c091c1a08c86970,0x66f0a321a419e12706ac,0x86ac18608f849c1b8340,0x247]]
set_option maxRecDepth 16000 in
def g255H9 := limbs80 #[#[0xa0a0000242f00000f,0x490101042d0035162b15,0x10425094d1230020303,0x83000101000525000808,0xf1615214d0001060002,0x21b4300020b050008,0x20f002f0303120f01,0x130e060417000003dc0c,0x121702010000070b0108,0x1905191f0e8505261220,0x10102905120269501f,0xc704000841000001054e,0x2a431e10312a11260a00,0x953d0058400800100008,0x1a7f33240324091b0418,0x3335110300601e26120e,0x326293f25343d044206,0x7d40012d5520091a010f,0x921c0307031309051a7d,0xa410a11408ff904a1303,0xf0664520013ef0f1f03d,0x58fb0000b0f5847e412b,0x687ef127b4ba70b08026,0xa35602164209d0dca408,0xa49c683d700f60f434c7,0x10d0073e48b544480ea,0x1006c4c5b0c9e04db854,0x54b7e46dc05600006606,0x7311707ff0c2d624911d,0x10afa47504bf000074f3,0xe89cc814a01f24194523,0x835e36cc000020440000],#[0xf80ff0ecd526a4454065,0xf0a394e20000d41a30bc,0x86af4137124b913c7087,0x3625000020ce512fe845,0x90cb228880b7e011850c,0xd427c535851ee08ea710,0x5051a4e0d40af0f8,0x9003d105a16b210834e7,0x628a268c149d80623212,0x1484115ee058105c1712,0xb04f940d135920ad34ab,0xb46e116dc05a2232e0ba,0x103fa148910f78fc4000,0xf8e52546d242a1183228,0x166678c530bd716f3422,0xa5060000560d7811,0x711396078110d036822e,0xb0a96490b15470f750b1,0x216ac4d032d7716640d5,0x4249000060f9e8460227,0x30fd00000000728fd415,0xd470e451c810693b,0xc071986400000131854c,0x3aa629b51900002450,0x64d8149570026252,0x2437d008a104e159423a,0x12300d9d0101455e8c7,0xe01d945b32a100000000,0xb20164e50000005558a3,0x40c800001030c13b,0xc024a0e1b364e5010000,0xd52ec4e960b415240000],#[0xb0ca84aa054e811f614e,0x14f284cc020d0000b14f,0xe66048e2f0cf60471027,0x4ab1b054eacfe30aa900,0x215fb06f20ebc4c6e142,0xc020a150f472f03cf53c,0x5ee28436b0a35d008f,0x42191243f1682504c094,0xd037447a1079150bd405,0x414cb226e121913d3431,0x65334875d35ad16e0000,0xa6085229303964a59302,0x615c8096000070190000,0x653e1640000046610000,0xf0ed18f3c358,0xe098215ba28d60594641,0xd287309b512a94b6344a,0x7239ea050000290cf11a,0x709e54ec0000600150de,0xc255d04338120000c095,0xd4364489a49be00b,0xf22380c000006528862e,0xf60cf203000000000000,0xe07d10ff5046c164f4b9,0xd0ac768f40819536f0d1,0x304e51520000020f1017,0xc49430f2690e,0xc44e606ef40e00000000,0xe0280000e20886cb6151,0x34a8b167e0e700000000,0x44d12f7820e311e0000,0x74ce361f88050000],#[0x60d3c0d470aed357f547,0x2465a1078133312550e0,0x1109000070e800000000,0x10e444f8c08b00be916c,0x645c205720a730fa9605,0x54a400007870f0c12505,0x5387038f0fb00001296,0x407c44cf511208d8,0xe2a8142b0000a02d,0xb457d273a07b8285915d,0xf672000084fd553170fe,0xa08044bb2009505d,0x5116e05340e266906129,0x30d606028496c370c206,0xe423354b68c6b626f160,0x306140a441321042a0a6,0x90b3a4b1912270fce887,0x6119f08610e5d0da2060,0xb90bd4070000442fe498,0x34a68901410340b5,0x35498f5f63174fb405b,0x49060000941d,0x745370c564916141d08a,0xa1a54f000000000000,0xa247000020a570e9,0x949e30aa0000f22ba088,0x9665153b000054d90000,0x68a0b80140a68d40f6,0x40a00000b4060000a8b6,0x28a5d89ef050c03b,0x6084b4b40000da59,0x31699064e0c7c124f0c4],#[0xe53df0db262ab2e4908c,0xc0ef647874eb9041,0xc4691ace0000702f121f,0x409a158d143a100f040,0xf20700000000405f6878,0xd609c6a2906be60ac02e,0x3622207e149f0000d441,0x44ed884e44f1f005502b,0x5076589f451a952f0000,0xf4569510d15561630000,0x7244401c40b6545e,0xa52a246c0000b08d,0xa231b430311c723c1128,0x14dc3089b41c040c1091,0xb1654021241e806da0bf,0x115664ff922ce120,0xc905f115f15ac09f0000,0xd44f000000003433e8f8,0x41360000a4de407526ae,0x809c812ec013950f7126,0xe032e0d23853c0c3f045,0x210c4553d22af9040000,0x400c0000000054a230a2,0x85374034b50ec06a28fd,0x7810f3a45940319018,0xf22d0000912ce630f111,0xd01e9435b4f92162c00a,0xd0abe28e991680520000,0xa147429e9452e20220cd,0x31708029754500006403,0x40b271343016c135b64f,0x18a4b00d045ae548e518],#[0x609ac08390900000,0x84930000404b220a0000,0xb60bd23df8a6d40f24a7,0x101574bd24e658f944c1,0x6012d09d96230000a153,0x70041534f0bbb102804c,0xd6cd751df869e033d145,0x502500d8b06710488077,0xa07410ddb130710e3092,0x58b4c627d5272146840b,0xf20cc06380e3060e6487,0x92300000d4c0000000a8,0x201a707092c4a0b9,0x41068363e14b4157d61a,0x5412c049c4fc40359117,0xf8d9b1384097d14d813f,0x5365f88a3023500e70cc,0x64df0f0c22452050000,0xc2a5a51660c680d70000,0x81017a03b161e432001b,0x2082e4a0b4978601f4a9,0x7139f85e3093e4f5e550,0x84cbf03e61440072e0ee,0xe464e11b0000507a,0x149940e6620b002c5ad0,0x18035852a09900000000,0x62b5649a4434629f112d,0x28a006587069a02a635c,0xd14910148650c667128c,0xb10b2603c14af62bc47d,0x76284210e68ef62d2225,0x3085f50060d0113a769d],#[0x40df962c200734926022,0xd06c310a429cb428496f,0x84a312a4]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0x4250120fe25cd4250120,0xfca5954250120fe29cd,0x54250120fca995425012,0x20eea6194250120eea61,0x515250120eea61d42501,0x120dda6555250120fca5,0x5956250120faa5916250,0x120dba6596250120f9a,0xa65d7250120f6a5d1725,0x54120e9e6196550120d7,0xda6595254120eda61152,0x254120f9a5956254120d,0xeba6116258120dba6596,0x6258120eba61d6258120,0xf9a5957258120dba65d,0xd7258120f3a5d9725812,0x20e9e5958458120d7a65,0x1d6558120f9a68965581,0x120d9e65d6558120e9e6,0x611725c120e3e61d7658,0xc120f5a595725c120e7a,0xe5d9655c120e7a619725,0x5c120e9e619655c120f1,0x9f6616559120e3e61976,0x5595208dfe95985d120c,0xdda6499059520a9fe998,0x7659520e1f61d7659520,0xa9fe918659520a9f6a1,0x9625c160a9fe9d865952,0x60b3e69d625c160f3a5c,0x9d655c160f1e595725c1,0x960b3ee89765c160f1e6],#[0xe819259560e1f61d655c,0x9560a9fe898759560b9e,0xe5d99059570b9ee81975,0x59570d5e65d9059570f1,0x1fe5d7660165b1fe8976,0x25c11099f68b905d965d,0xb7e69d425c110f7a5c94,0x9261d10f6b5d17250910,0xfea50971501208ff693,0x94250120fea595425012,0x20fea5915250120fea5d,0x595250120fda59552501,0x120bfa6995250120dfa6,0x5956250120fea5d16250,0x120dfa6556250120fba,0xa61d6250120fba5d9625,0x50120dfa65d6250120ef,0xda5957250120bfa69d62,0x250120f7a5d97250120f,0xdfa6597250120efa6197,0x6550120ede6156550120,0xafe6a16550120ebe619,0x96550120fda689655012,0x20ede61d6550120f9e5d,0x998550120ede6a165501,0x120ebe6197650120afee,0x6a17650120e7e61d7650,0x120afee958650120afe,0xee9d8650120cfe65d865,0x54120afee998750120af,0xda5516254120fda59152,0x254120fba5916254120f],#[0xdde6595454120efa6116,0x6454120bde6995454120,0xdbe6596454120f9e595,0x98454120ede595845412,0x209fee919654120cfe65,0xd16258120fba55162581,0x120fba5917258120fba5,0x6117258120f7a5d17258,0x8120f9e5955458120efa,0xe5d16458120bbe699545,0x58120ebe61d6458120fa,0xbe69d6458120dbe65d64,0x458120f9e5957458120b,0xe7e61d7458120f3e5d97,0x7458120d7e65d7458120,0xebe5958458120afe6a1,0xd8458120ebe5d9845812,0x20afee9d8458120cfe65,0x9d6558120f9e69165581,0x120fba6897658120f9e6,0xe918758120bbee917658,0x8120dfae899758120afe,0xa591725c1209fee91975,0x5c120f6e5d1645c120f7,0x3e5d9645c120f9e59564,0x45c120ebe619645c120f,0xafe6a1645c120b7e69d6,0x745c120f5e595745c120,0xede595845c120e7e619,0x9845c120e7e5d9845c12,0x20fda689655c120afee9,0xa1655c120f5e69d655c1],#[0x120dde6a5655c120ede6,0xe91765c120f7a689765c,0x5120afee91865c120b7e,0xf6616555120e9f619655,0x55120adf6a16555120cd,0xdfe998555120cdf65985,0x655120cbf6598655120a,0x8ffe9998551208ff6a58,0x7459120f8f5957459120,0xeaf6197459120f2f5d9,0x56559120e6f61d745912,0x20cbf6616559120e9f61,0x816559120abf6a165591,0x120e9f61d6559120f9e6,0x6a16559120d9f65d6559,0x9120e3f61d7659120e9f,0xf6a17659120cbf661765,0x59120abfe958659120ab,0xbfe9d8659120cbf65d86,0x759120c7f65d8759120a,0x8ffea197591208ff6a58,0x98591208ffe959859120,0xf1f5d9655d1208ffe9d,0xd655d120e9f619655d12,0x20cdf661655d120e5f61,0x61765d120e3f619765d1,0x120a7f6a1765d120c7f6,0xe95985d120a7fe99875d,0x11208ffe99985d120cdf,0xe6816561120cdfe55656,0x61120e9f5d96561120ed,0xdfe5d6561120e9f65965],#[0x561120cdf6a56561120c,0x8ff69b9561120cdfaa56,0x96611208ff6979661120,0xadfe9597611208ff69f,0x185595208ff69b976112,0x20abfe918659520adfe9,0x5190595208ffe9198595,0x520bdee919059520dde6,0x61d9059520f9e5d99059,0x9520dde65d9059520ede,0xf6199459520bdee9d905,0x59520cdf6619459520e9,0x9fe917659520f9e68176,0x659520e9f6617659520b,0xe9f6918659520e9f6a17,0x8659520e9f65d8659520,0xadfe918759520e9f69d,0xd8759520e9f699875952,0x20adf6a58759520e5f65,0x619759520adfea587595,0x520adfea19759520cdf6,0xe999859520adfe919859,0x1520adfe9d9859520e9f,0xf69396615208ff69b946,0x5d920dfa649905d9208f,0xbf61b945d9209fe68394,0x45d920c7f61f945d920c,0xabfe91865d9208ff6a39,0x985d920a7fe91875d920,0x8ffe91985d920cfee81,0xf94619208ff697946192,0x208ff69395619208ff69],#[0x939761920afee8197619,0xd20adfe959461d208ff6,0xe819661d208ff69b9461,0x49508ff6939661d20afe,0xfe918654950e9f619645,0x61950abfe918658950ad,0x3e5d1625c1608ff69392,0x65c160f9e689655c160f,0xe3f61d7458960f3e6897,0x8758960ebbe898758960,0xf1f595745c960abfe91,0xd655c960f9b689655c96,0x60d9f6a5655c960f1f69,0x89875c960b3fe91765c9,0x560a7fe91875c960e7be,0xe919259560d9f6519259,0x9560e9f61d9259560b9f,0xfe9d9259560d9f65d925,0x59560e9f6898759560b9,0x9ee819759560e9fe8987,0x25d960b9fe899759560f,0x9bf693925d960bbee819,0x9261d60afee819261d60,0xf5e681655c9708ff693,0x99059570e5f6a1655c97,0x70bdee899059570dde64,0x5d9259570f1f5d992595,0x570cdf6619259570d5f6,0xe819759570f1f6897659,0x9570b5fe899759570f5e,0xfe899859570edee81985,0x5d970b7ee81925d970ad],#[0xdfe51826016597f69392,0x260165e9f5d98260165c,0xb9fe999260165cdfe5d8,0x92601659df6939260165,0x5cdf61f9260165d9f5db,0x976601659df69f926016,0x65edee818760165b9fe8,0x819760165adfe8987601,0x9659df68b9760165bdee,0xe89905d965d9f649905d,0x1769df68b9061d65b9f,0xa68976501208ffe9192e,0x50120efe6a17650120ff,0xfe69d8650120efe69586,0x750120efe6858750120e,0xefe6998454120efe6998,0x8458120efe6958458120,0xfbe6917658120efe69d,0x19758120efe691875812,0x20dfee919758120dfe69,0x99845c120efe685845c1,0x120f7e691765c120efe6,0x685845c520efe691865c,0x5120cff6a5845c520efd,0xf6a58655120edf695865,0x59120fbe6817659120cf,0xbf6958659120ebf6a176,0x759120ebf69d8659120e,0xebf6998759120eef6918,0x9759120cff6a58759120,0xcff6a19759120dfe681,0x59859120cff695985912],#[0x20cff69d9859120cffe9,0x81765d120cffe9d98591,0x120e7f6a1765d120f7e6,0x69d865d120eef691865d,0xd120cff6a5865d120e7f,0xf699875d120e7f685875,0x5d120cff685985d120e7,0xff699985d120cffe8598,0x161120cffe99985d120c,0xaffe9d9161120cff65d9,0x9561120edf65d6561120,0xefe6817661120cff659,0xd7661120ebf659766112,0x20cff6a57661120e7f65,0xa57661120aff6a576611,0x120affea57661120cffa,0xe9d9661120cff65d9661,0x1120affe859761120aff,0xf6918659520affe99976,0x59520f9f6917659520eb,0xfe651905d920edf69187,0x45d920bfee91905d920d,0xe7f61d945d920ebf6199,0x865d920cff661945d920,0xe7f691875d920ebf691,0x1985d920affe91985d92,0x20cffe91985d920cff69,0x959461920cff65594619,0x920cff65d9461920affe,0xe919561920affe9d9461,0x1920efee819761920aff,0xf6519161d20affe91976],#[0x61d20affe919161d20cf,0xffe999461d20cff65994,0x661d20efee819661d20a,0xebf6918758960affe919,0x765c960ebfe918758960,0xe7f691875c960f3f691,0x1925d960e7fe91875c96,0x60bbfe91925d960dbf65,0x519261d60efee819261d,0xd60cffe519261d60cff6,0x6939261d60affe919261,0xd970cff6939261d60aff,0xfe91925d970d7f651925,0x5d965f9f6897660165b7,0xffe518260176f9f68990,0x2e01769ff6939260176c,0xeff6a57661120cff6919,0x9761120eff69d9661120,0xeff6999761120eff685,0x1945d920ffe691905d92,0x20eff6a1945d920ffe68,0x91985d920eff691985d9,0x920eff6959461920effe,0x6919761920eff69d9461,0x1d20effe919761920eff,0xf6999461d20eff685946,0x61d20eff6919661d20ef,0xbf691925d960effe9196,0x261d60eff6519261d60f,0xeffe919261d60eff6919,0x8260176f7f691925d970,0x6dff6519260176eff651],#[0x480000bffe91926017,0x1fd01aa014c00f9009b,0x3bd035f030c02a30250,0x593052a04c10463041b,0x75e070b06ad064f05fc,0x92908c00862080f07bc,0xaf40a8b0a2d09cf097c,0xca90c4b0bed0b9a0b47,0xe690e0b0db80d7b0d28,0xffd0f9f0f570f0f0ec7,0x1186114910eb10981050,0x12f912a6125e121611d9,0x1477142413d11389132b,0x15f515a21565151214bf,0x17aa1757170f16a61648,0x194918f618a3185b181e,0x1ac71a7f1a2c19e419a7,0x1c5b1bfd1baa1b6d1b25,0x1dad1d5a1d121cca1c8d,0x1f0a1eb71e851e531df5,0x209e2056200e1fb01f5d,0x22482200218c214420f1,0x23c62373232b22e3229b,0x257b252824d5248d2419,0x272526d2267f263725ce,0x28b92887282927cb278e,0x2a2c29ef29a729492901,0x2b942b412af92ab12a74,0x2d5f2d012c8d2c2f2bdc,0x2edd2ea02e6e2e052db2,0x302f2fe72f892f4c2f1a,0x31d93170311d30bf306c],#[0x3399333032d232743221,0x355934fb34a8344a33ec,0x371936d1365235f435ac,0x38e43886383e37eb3777,0x3a4139f939bc39743916,0x3c593bc43b713afd3a89,0x3dd73da53d733d203cb7,0x3f973f393eba3e7d3e1f,0x40ff40a1404340063fbe,0x420f41d2419541634131,0x4340430342c642944262,0x4487442943f743a44372,0x465d462045ac453844f0,0x4783473b46fe46cc46a5,0x4893484b481947f247c0,0x49fb49be494a490d48c5,0x4b4d4b1b4ae94aa14a4e,0x4c9f4c574c254bd24b95,0x4d994d674d354d034cd1,0x4eeb4ea34e5b4e134dcb,0x507f50374fe44f7b4f33,0x51e7519f5157510f50bc,0x532352fc52bf5282523a,0x54ac544e53da53b35376,0x560955b6556e553154f4,0x572456f256c056835646,0x5881584457db57a95777,0x59bd5975593858fb58b3,0x5ad85aa65a695a3759ef,0x5bfe5bab5b6e5b315aff,0x5d715d1e5caa5c785c30,0x5f1b5eb25e495deb5dae],#[0x60af605c60095fc15f63,0x627a622761c96160610d,0x647164086394634162d8,0x665d65f46596652d64cf,0x6807679e6761670366c6,0x69fe697f692168b86865,0x6bb36b766b186aaf6a51,0x6d736d2b6cac6c6f6c11,0x6f546f016eae6e456df2,0x714b70f8709a703c6fd3,0x72f572ad722371f171bf,0x74c0746d73f9739b7353,0x76b7764e75e5757c7529,0x7898782f77d1777e7720,0x7a797a0579bd79497901,0x7c5a7bf17b937b147ac1,0x7dee7da67d3d7cea7ca2,0x7f987f507efd7eb57e4c,0x816e811080a7805f7feb,0x832e82ba825c821481ab,0x850f8490841183c98376,0x86f0869d863f85f78578,0x88b0885d87f4878b8743,0x8a658a2889ca895688ed,0x8bee8ba68b5e8b168ab8,0xc4e0171ee3468c948c36,0x2b00b8c710e38790b40d,0xd05024c127364485a06e,0x71ee35c60ee39c339e82,0x8c828e3c890b40dc5e01,0xa39b1c0902c061059c5b,0xdc78e049c703382de3e0],#[0x63c7025e101dc16829e6,0x304a1413262c8c412318,0x29418c1242862cc618f2,0x28277c791c82466c702e,0xef104720919bc28418e4,0x214f1e470cd90124cf18,0x918ff36301a31c0d209,0x50c7c12f3640a2242852,0x5850cd9207fc203d2428,0x242481a31c67819f8842,0xe0ba0c4179168524648f,0x82522e47c1871a4812f0,0x1231aa3c703c0680b8ac,0x6412d1e409e23885d45c,0x24d9006815036239a2f4,0x381291c0ba0e41af1e85,0x97850770720d38f936,0x7c0d785839049c7c9b2,0x3de150d412a42a6c7048,0x424286a0918f536384b5,0x78524263e0969b23c28a,0xd049a2ca6c904807c0d,0x4a4d8f0520928ef10a79,0x726c70312384f41a0988,0x936478593c84a0d21f09,0x924f01a097e14c7e12,0x3e0ee0d78542463e4d9,0x2e84307d0a48ff3648a4,0xf84b824e6c7025e11880,0x60fc8f7363b8673d0860,0x87f0919b1c0978506708,0x2587ccd9012c5219ef0a],#[0xf336404b03467819f854,0x962900d03383fe150948,0xed0bc0f80c9ef101264d,0xe85d11e6c706a0d019c8,0x47c8c0602f8404bc0f80,0x380f0c5225a6c713d22e,0xb27825b12936421882fa,0x91e12e4d902909091ff0,0x9b066303393de1781f01,0x7c9b066348e093279c2c,0x20d28fa36304b93de154,0x47147c1aa3640a143e47,0x3f2858d8e09010f8543e,0x943f46c6096c7bc2a1a8,0xa1291f46c701e47a0d04,0xfaa1a36441f834093c2,0x6c1b8a12c1201aa3de15,0xae0f0dd1f1f0704c4358,0xb101270d8a12c2361ef0,0x1713c1348fa9b1a0f21a,0xba0f03c3088fe9b19124,0xe4f785048e0e8fc9b1e0,0x1c36412409b46c1b0812,0x8c12c23824c3de16c0aa,0x8d8f4410f8a1e1665b8d,0x6c714428511e11e1665b,0x6361014428785896e23c,0xb363b85e17c0744029e3,0x9e1cd0214425622c5a16,0xd8b0520938b718e3e0b3,0x1c6d8f1e0b414824e3dc,0xe370a0ea750a412b1746],#[0x1b460833c4620918b31e,0x4241a21a824852c5d8f7,0x504708c412b16e36c7e1,0x242904a8e38fb3630370,0x11c824e2cc6e1471e3aa,0x9214716e31c7d1c28cf,0x51c799b141882a43285e,0x40ef0a38fb36311c8258,0x8248528e38fb363d1c02,0x1c824e3f0a59b1c1ea1f,0x4c12c29485cd9011c909,0x8c7e14736284570c12c2,0x4819e14b1ee6c624304,0x350490a58fa42e6c7a42,0xbe07850c7d8d05830344,0x33b16848c6e14b1e418,0x81e14b1f634160c6780d,0x1c8c21442566c260be0b,0x1302599e711850cde12,0xb0c1250921f097852cd9,0x4180bc0f0a59b08a204c,0x850cdd8f1ac5d8fc28e3,0x2463f0a59b180d033425,0x3e0763f0a59b1c0f83b4,0xe1471f634160c11c1d83,0x951c71ea8acd91c0dc5,0x51c7d9b066221f834852,0x8f73a3d8fc280edcd898,0x6a991e0c41791704a464,0x7478f47209217516a3ec,0xa3c8c2f0488e68bd1867,0xa8e01205d85d0a68bb1b],#[0xa1bc161293323dc682a1,0xe121e45d85c2523dc682,0x478e2790ba8b518a3cce,0x2460340db45e8c33b84b,0xca78a03c85d45a8f71a1,0x690bc14825a2f4668fa2,0x4e1747e8cc240d8685c8,0x834e2e0938f91ae647f0,0x1c835049c7c9b744341c,0x35218248694ed8f53634,0x363e1a824484c79a2d36,0x91e9081205d8690a58fd,0x142790d18b31ea370919,0xe13a86a0a58b51b63f09,0xc1ac24e3e4d8c0e01409,0xd21271f2764d8e6884e,0x6a4eb8fc2526c707687e,0x4275c7c9bc24382403e0,0x4358494dda224240a483,0x12536304c09761424a9e,0x79a2d3638a443463cd16,0xb0969b1c0fe1a076848c,0x63f4d920900f81a31e68,0x41f83d0760bb0d703b0b,0xf5364516716a35c78491,0x9086a0a4125490ba8b38,0xf435052092a471f45b4d,0x6c258c069c782ed36221,0xf26c248cc0c1c41a70b2,0x8342924d9007a0d21231,0x8f9363047039e150958f,0x783bd362c1a148853095],#[0x90958fd361186034e16c,0x119c2e12b1fa6c503e06,0x8d0860fc1291ee75cd8c,0xf8e2890f99d51f84acd,0x6c6098124cf19dc2466f,0x7a3c714887d4799dc246,0xb36461f0340cd0919d33,0x4120520a243e67547e12,0x5d63b0ff03b0ba3ecd9,0x1f945849cd900d41a033,0x7ca2736384270c13025c,0xb0fb9b1c19a1a83e84a4,0x459cd92e182604b09345,0x15221f8290481242e51f,0x2b36130503fa3c1739b1,0x8f43f66c248a87c8c21,0x61085e0787ecd8451109,0x91e84acd9009b44612b3,0x12b363047043e160f8a4,0x9e8fb362c1f14885247e,0xe4648f932100703ee141,0x22e47825b1a411c23522,0x1f6364c8e81381f01d0b,0xfa24a749e07c0412c8b9,0x8c2784cc1882f22e4648,0x200e09645c8fa25265c6,0x34823846b45e8c533a3c,0x2703e0209742e8bd1f6,0x1781f0185da2f47b8d20,0x8a784eca2537c48904ba,0x31ea6f890e13424f0109,0x125372888e020905109d],#[0x969b201989d43886ac7b,0x70762889091f93a63d8,0x403093a62cc7c8d6240b,0x41a03391b62ec7d8c092,0xc06c5c9d91b63c160e0d,0x3d2748bb129361346e07,0xc64327824b1f93727481,0x84cb0ca8a4df122c2684,0x228c134240a483c27780,0x6e4e900c04f49d62526c,0xe503b1484848f98f6252,0xce47685e07c051749bb1,0x7c06c7c9d93638350680,0x91ae3e8902c181d833e0,0x1a544e3e8949b200cb8b,0xeb8f9360cc41482760e4,0x89091f53a63e8969b224,0xc0f80e85b1fa6c614828,0x8dc0f80d8fd361205d1d,0x4d8dc0412e85717a35c7,0x6f8915a3b81f01d0ae3f,0x258a4e021301219e5446,0x2419c8f62466f5114134,0x4a8acd8e12c4f11c2341,0x9366cdb0c1342604b62,0x7c0429688b3c1342604b,0x62466e511007ac3685e0,0x8fb3648331484708d48f,0x7e0f41de85e07c05174,0x3b067c0f80c8f94566c7,0xe6c2908a764783b73620,0x7c042968f7363006f09],#[0x5e0262cc618f33c4685e,0x81e09366c268ba178182,0x2699ec28e230919b2c8b,0x6c249013025e2e048690,0x2184f06a0d01998ef106,0xe07c041cd9b19c459b09,0x85e07c06cd8391502685,0x2f03e02e36c5d8fb1846,0x781f01716e3ec6900974,0x149c782eb362004d0a09,0x82e7362784b11e6c2488,0x45c8fd1a0b0180ae3ac7,0xd1e3e8b533a3f4603316,0x441012f03e03a2dc2e8d,0xbd12d36134470b44b4d8,0x9a289e82f4494d84d140,0x8d36108482e07825e9b0,0x2c702f44b4d84d128938,0x6221c43444a4cd855361,0x14926d891161589039d3,0x9be244846035e164f04b,0x9b0784cf01098e14524,0xca060278843129361146,0x9c9e096293c2c8f62526,0xbc40499360cca08e1181,0x124509e0d41a48e70b27,0x1f26c198d0720d28f936,0x470ba6c258727825f855,0x2f4d8491419f8553612c,0x7c06c402cd36308f03c1,0xe07c06c469b0582905e0,0xf4d8490ec4312059a6c4],#[0xb0723030a25a6c228923,0x69b08a203706c0b01829,0x80e8bd1ee34160c0c289,0x291768bd1f634180bc0f,0xe8720d046f0a44b47e9b,0xb0ba3d8969b1423a2183,0xa443886ac2e8f5363846,0x222143f61547e9b1c170,0xc23701b0ba3f4d8c0b85,0xbd3622a2d1f26c198811,0xf85d1fa6c238ca764783,0x81f0170ba3f4d8a0ec19,0x9781f0171761746b8f1f,0x8db1e358571e0cf4d880,0x9e9b08e2025e07c06c5e,0x96268e06763f4d8963c1,0x5d1e0edcd89e12c2f9b0,0xeecd880ef47d9b08e258,0x263707e180583052d1e0,0xe0383f0c58d058360be0,0x12e17c3387a9606c360b,0x3385e17c0787e8d05436,0x98321f834a3e8e2a2a36,0xfa364a8806f069c1d1b0,0x8e0860d024f0a47247c1,0x403e868c7e1c34586c70,0x824034872c7e1b08c302,0x7284708dc06c7e1b52c2,0x98304c096c7a5131a63,0x1b092311ea3426150d1b,0xd1b082311ea3423d50d,0x247e12a36382723d4695],#[0x23f8d8461a8d024942c5,0x3523d4b71b141201f143,0x3c34e16c1e1b0862846a,0x62c1e1b0983837c36130,0x6a3f0d841151221a23f2,0xfe1b281be1b0981c98b0,0x1e09611819c8ff0ae0e8,0x5e1ef0ae0f0d84622126,0x820d88c3610060480682,0x7880c8fc36124503c86,0xd12180e21ad1f86c238b,0x8d8471c1204870ba3f0d,0x3f8d8a87d0d78508da3f,0xe87ecd84d1423701b07a,0x4d8870959b0842a2122,0xf4d84d11c1d1fd361144,0x2608fd83536130702f47,0x8960d8fe9b082222406f,0x90d1f9364d8363e0b34d,0x509607023c9ef0a090,0xfa6c248903c2091fd361,0x4d83c1602ad36300fa3,0xc504dc078469b0842836,0x44b4d8c0850fe0fd3611,0x6dc6c22881201229dc1f,0x8c2f60f40b1b08a35830,0x6c1b0b60c1b71b08a251,0x2a538d844124902c072c,0x7f1b0842036636134306,0x413388d03c6c210ba058,0x8e363830249a068d84d1,0x842100f0810580aac402],#[0x1602ae360d86d0343f8d,0x2818292e36114442f43c,0x411c2361ef0aa864fe1b,0xc3ce0f0d8461c25a1c83,0x83d11c6c208a06bc284b,0x4385e1fa078d8471413b,0xcd212123884ac7e14b36,0xec19a12b1f852cd9211,0x17635c78492423846348,0x4066303706c0c1428337,0xe147364047076e3ecde1,0xcd8c0f01d02b346e2c1d,0x30248e11c1983bb1f851,0xa12870680cf45b8dd1fa,0xd3640490620c1c5b8fd1,0xe0ff0d03d0761481738f,0x910684ed8f14926f090,0x3d05c149c2d8f077a6c9,0x3385b1f84b4d900ff0d0,0x70969b08c384807a0d02,0xb9cdaa3200f81ab1ee1,0x37a3c905e0ac16e1f716,0xd70fb840680cc2782e7,0x9107c5248f14566f090e,0x405c13dc2833b37a3ca0,0x28b540a6c906b87dc203,0x4d900b41582fa2545148,0x49a2d45289290541a2f,0x1b836516a3ec6a990804,0x1345a99d1f63420120c0,0xb26d890a4202551ca34a,0x937274903e0682358f93],#[0x211c2303b066292c7b12,0x600ce4eb8b91ae3c249,0x3b71f26e4e833141b836,0xf83d05ca76c793bd3640,0x419d8f53aa6c9d8a1481,0x4868fe8ea24a76c7e9b2,0x7b276c7e9b6244052097,0xdb1ec4b4d8f2901a0480,0xb8f718124994928b4749,0x249012a1ac34867a35c5,0xc358690cf46b8b71ee30,0x27e85e07c074738fd365,0x6dc784f1e1ac348670b8,0x4c4acd900d41a03305da,0xb36481a03e1185248f94,0xe1181d83314923d894a2,0x680bb47d9b5444cc808,0x3b51f66d511331427835,0xe51ab1d44b47aa2b3640,0xc51b8b077289cd9013e8,0x23c1dca2736283c0740a,0xbc061eaa3716e6cb067,0xb0a4305287f0ee17703d,0x68f7365c3d020e11c5b9,0xd8770b9c7685e07c0429,0x83b05da3dcd8521e1fc3,0x1e82eb1668ecd920fc1e,0x8ecdc2e1c2923f476621,0x166c248e0bc1682bb166,0x71a128b0a48fd1ea3b71,0x88ce19431b18126c5d8f,0x23563f0b59b3484a3546],#[0x9bb1e8b8845c8510911f,0x759b20d204f06a0d0199,0xc73481481f83d07663d1,0x558ed0bc0f80a2eb1f66,0x70b614b1c6930958fb36,0x692c7a2eb36205209e12,0x38fb3661a445d63ecd88,0xd4770d61a4330a563817,0x33b36e3c278c13d1fa3,0x9588716641cd900d41a,0xeec7b9b0a43616c28613,0x7a2f47e8c092403f07a0,0x34526f89140d41a48d06,0xe1378084c0902764f0a4,0xa44fc9e92e70ba6c258,0x1a0901194ee8fd374489,0x7b85a25a6c230ea8a0fc,0x347b12537288903e06b4,0xc4b4d928cd0e21a13a29,0x51da2143e2885228f93a,0x8ce4e846d1f2898969b2,0x5ce1419c9bd1e4847476,0xf077a6c809e0d41a48e2,0xca41c2903f07a4b9c2c8,0x4d910ee19b85d1f44b4d,0xc3b867a3b81f01d1ee17,0x1dc33e07c0747e9b70a4,0x35c5b8f718124908e11a,0xae3c200d0d61a03330ba,0xb0ba6dc7950cdc5d85d1,0xc13d1dc358690bb47033,0x9940d41a02ed36e3c278],#[0x3786d0c2c5b85b1963e1,0xdf85b1fa6c198c103094,0xa1db85d3763e198e11c1,0xe141dd8b94766cb08e11,0x76405247f0f11742b47a,0x6421e43a856e16c5d9b8,0x670b82903bb0ba3dcd92,0xd05da3dcd8521a1fc3d4,0x833f0a0ef47d9b181f83,0x2343370ba3ecdc3b1c23,0x1a0d385b1f86f0e1211c,0xf86d4b0461a1203d0681,0x4946e50d1a201201ab1,0x85943c6c90441208ec8f,0x30d0901a04607b46a47b,0xf0d0e0900fc8fe36a582,0x11c609011d0ee8f83986,0x8fc6c703986b47e1b628,0x3e3650460760cfc2e8f0,0x768d219846e03a3dc2d8,0xb867a3ccb71b08c323d8,0xc3bc3560f47f1b70a4c3,0x47d83e36118808f89219,0x178d846142423d468e17,0xea764e61fd364d83d1ee,0xd3611c644508424047c1,0x81a36134804387f07b14,0xd8462a0f0a12384930be,0x24c3c11c19f85c1e64b0,0xd1ce1e65b8d846185dc,0x51a294e1f60f8d8461e9,0x121c2f0fd03c6c238c8f],#[0x25621c33843496351716,0x409f634b0a413f0b614c,0x930d61a43385ce19c21a,0xd8770b9c305234048520,0x1a40a563cb09c1261fc3,0xf0930fe1ec3b85ce11c0,0x4807ba341a046a24304,0x23034949a341ec9d6244,0x898330425da364e8e120,0x6e19c2b8425da3479492,0x8d0ef46c3370a343b86,0x34867a35c60493324847,0x238009e68890a012a1ac,0xd10f0d61a43385ce19c,0xe14509f0ee19b86708e0,0xc148ca9211c23433876,0xd282884b87f0f61dc2e7,0x7b0ee17386708e002919,0x370ce11c019d2025c3f8,0x43b866e1450a412e1dc3,0x6c246020d4238e11c23,0x1a1dc3370b60c80900ff,0xce11c0196191ea34c481,0xb070ee19b851a1dc3370,0x35848c041f8471823846,0x423de1a1191a58318240,0xd1a433c49c354a492202,0x87f86833c34e14847b0e,0x2383bc49]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x450104016120080c0200,0x320b0a048064a1e8140c,0x5406000d0741e0100048,0x703c2e00008082220090,0x91489000080d0000c070,0x80200810280e01894040,0x80e01000000400000181,0x80008060303c00000103,0x802e02080680e0200,0xe0481000300b8540e00,0xfc0101810b0020c804ac,0x2800350389c4c0200124,0x883c2200170ec042f0c8,0x2138180007080d004060,0xc02248009800088440c0,0x4630003c1613018081,0xc460e0c80000060286,0x30a44c3a008d4a60005,0x30038580c0f2e884aa06,0x8090080412018180e,0x80102e0137818012c80c,0x2018000d120755425048,0x7000482e30018087c140,0xc4302868380400020001,0x8061f2101c065c008140,0x13498290088800010000,0x240ec3a0b061104a000e,0x260695c8a923302c18b7,0x4020116c00cc040720c,0x1424710295c6e0300000,0xb1bc0866008801cc5058,0x61a080e8110001c16000],#[0xa0337000605f08004000,0xc1e010f0cc0006b58001,0x14000827800003a0b80,0x4854002303880061544,0x898aae27326110880804,0xb3c5024a000090d61826,0x1c185b800014a4e00002,0x5f0da44616828960e640,0xc244c714f8720c111e44,0x8971796864800005302,0x4d02fbe4046464506ea0,0x203ca9335c85688c9993,0x8c09b1080c3b712cb07d,0x869462702b0421ee86ea,0x16869350c326a4047ee4,0x8e806b300400003243,0xc4772191a13ada457,0x500000c14e0000702a00,0xc9f80000269,0xc3c6834287b1d2420000,0xab6834a1366131503990,0x4c140e83fa6b1f09c202,0x8ab842cec05211b5a4b,0xa60000142fd2091f0471,0x9676c44eb432fe89070,0xe1da9449da189838a000,0x2b8e16fe4c9c216fc00e,0x6bc3ec28b0d0961a1288,0x8b7e000014c62a461a09,0x299c05b4110689e4307f,0x9500001133143e6a0037,0x460da34e27b5180001a1],#[0x2d841b50b37874b13d,0x5621235c840000000001,0x8906650167282640e7c3,0xb417b1676cba80000508,0xc48000060263c4bce8ae,0x1a0db00005838103dce,0xc115b0151c12b0000000,0x6724bba405f4039a88a,0x41da7c88a1de22f22007,0xf00004890ba3d4c95240,0xc83a00119975c51050c1,0x246e1a950aa2971244ce,0x51039d21f8f09b505a41,0xe81f00000000012396a4,0xc0784b400004a482270,0x505054d880c000162347,0x6a4f310e5389ae027364,0xc121215b000050939038,0x14d3b740c0f0a8181e8,0x2d88b640fde5c1f23e60,0xc211030b403d5885900f,0xc18a0656286f4989ec0c,0x22000049095144b98662,0x34bd3287780dee173540,0xb0e0ca6f6813752c8000,0xe5683b2d859905c347af,0xda48c803db4497c1fb02,0x4a12b0558092b80ed013,0x8808a4c364cd48700001,0xc901ca714be4804a15dc,0xf924dc31720dce504681,0x25320688072843fc03a],#[0xef0bb2b00e08194c159,0x2200bd0d778641127364,0x41058933d01f506e5419,0x9019a79e423e062d198d,0x5d05b2127855f974c2b0,0xe8ec814d7e4232c32a10,0x920507e785e398720000,0xc1e44b348fd04a890434,0x388387486c4422205780,0x69d43042c26013a0000,0x21000001438a0bca90dd,0xd0000684a7d3ad61f904,0xe061910700000d1bc61e,0x17280d3c015da0cc1065,0x440000e1a20000683058,0x5208c000000000000511,0x528a1975833a1cd6002,0x79212880002c00d20290,0x9c05ee84200000000141,0x442849220099eb091196,0x5cd193008b00002c760,0xb238ac00008419000049,0xa414b05f00000013b333,0x49184cdb886723a94210,0x28a01351170211c804ec,0x8134c000036105095d18,0x8680c08d414252791c7f,0xe980001117a0000704f7,0x3047400000084e0,0xa139507668a0c000,0x14c82612c000000000,0xa9c82301944477830d80],#[0x3a1c1c2b20000c247590,0xa415b38c000120cc709d,0x6c8939120d449b9e44dc,0x2000000005828ec8cbc8,0x48844ce900330b011d9f,0x36411fb6112f11e00002,0x6f457cc9d1218f30daa9,0x410a813d7c35b61cb90c,0xf0fa2a4288303c8f7,0x6ee20a5022d0069c0e20,0xb547dc0c31213a257d58,0x18493685cc0d1ca7f,0x10f082383e38cfb605a0,0x8e6774067ada8484e3a6,0x410d82986a380e0cc821,0x1fc0820a063d99760b80,0x82c213a5047282db0d58,0xd223c4144ec076063188,0x21a000000bd1e1d7a214,0x1796a38855e400182719,0x9a9e22011586fbd1a8d1,0xc4dda836043470816ccb,0x9c5205516ff48842940,0x8d2237c32680af38e662,0x680f6926c4cece50,0x16a4078b902b9185a962,0xfa000062e38000000018,0x79071a66a164d3221dc3,0x84fe9003805300000421,0x3803ca05071001,0x6e6acf221443d740b600,0xc213222b7023c82c38df],#[0x2208c005075000000001,0x108a5025fb065810940,0x875591d4a247b045000,0x10f2a104429dec284502,0x6ac0f910576437600006,0x66886152a206a3d47a62,0x41dc694b31240069bd2e,0x2f751a60000000038130,0x7306ac000000372042a0,0xd10bf015983acc4e9621,0x92f16783854888b3a163,0x1c830023a192c000016,0x389e3001bb1345870000,0x21b7811b417a80c90835,0x10e2088e01c294e00004,0x50000290e1435f21e381,0x2078c4f092122d07b682,0x17ce086513b7800bc83b,0xb8c0baa41aa6f05904dc,0x8000181192c0b910dc92,0x1064101ec83dc524d081,0x1eb4f4680cf625ee1303,0x1ac0ea0439236560ceee,0x80ce4207a293193ac000,0x1204b000079360,0x1e22579028c490000000,0xd0bada3ec89f4c4eac20,0x624076e81b1d4042089,0x5e685f6459180c703d00,0x3c86588ee808e12093c2,0x3830781e4b109011a,0x4207a5861e06900000],#[0xa5057688fb844d492e00,0xe02a652a800039ac4014,0xc7807b6495a90c5447a,0x59033000000000087744,0x48090cb36e097b4bbc10,0x1e20534000148722086,0x3232202704452c43dd,0xa0000110e3063140aa00,0x81b2ac2300006167250e,0x2c3225c442be11859289,0x6c868012b84f44006f8,0xa495000001497a24dd01,0x47bf04b328dc04700000,0x9c088bf08b20144987fc,0x50227a10856098895240,0xa868a22da1e000002007,0xef9852f4203e025c0081,0x809a9206e08c2805a60,0x7608e024b825d80f,0x1e880641126707535262,0x485362cd9e000050071d,0x12113d26e0000a009523,0x3027988610000,0x80fad8983d835e8d80,0xd4170408300000000000,0x1c00a309bd088b098,0x59f90dee1e6a205e87fc,0xe682ecc44f6511f01b40,0x1854e40d40000251,0x1c79825f0995d3ca823a,0x8df131100bc058244a1a,0x878c62a0000000014b],#[0x116b19e6222c00004831,0x22a37df88240261760db,0x197200001e03fb8,0x906af0d980002c30a000,0x86aa17b4034305180001,0x99d1ec600cf4d85050c4,0xc2780e0a302061098d47,0x4675020283fd414090fb,0x3e70f7e344201f650ca6,0x120b884a16a2eb0ce781,0xc050821d708db85fd105,0x48188ec61d8600c18412,0x4083a5887cccb2612ae8,0x6bbb5a78308e202c33,0x187c08398999ca3c49ec,0x8b00dd564c1205842300,0xec1e62105b82d126f60b,0x80bcc2e9c0523068a857,0xe64012110e2ec2796057,0xe8609546c70b85a86682,0x917541e348411039480,0x88f69ccd518e065bc1d0,0xfa93e1a24f0068733d7c,0xc0625223169abb026a20,0x23b800000000e264f486,0x1d94174a79f422a40df7,0x111c90000000d2c05885,0x644009904c8918c000,0x3b40000c9ddb235b9771,0x69a3340000c168503289,0x608f80002503f841fc03,0x204b07a308050383e8b7],#[0xe4285e0000000035128a,0x8000041b6a867a902319,0x291501acc433364e9967,0x6066e08b7a0bac8255,0x14085800025838000000,0x49322615584a2085b400,0x16430047c48485c348,0x92c0b968e9a050844540,0x882d400000173464de03,0x129990b0000160f5e12d,0x5b920c28686a32faa28c,0xfe0e36049d85df9452c0,0xc02be845220a800024a1,0xaf48b8c100c0a41320e,0xc8c9c5843e65dae41dc2,0xd425982a36234602d621,0xef48991862291a0a0e1,0x2821b8a674523fd44a50,0xf4a51404f24288b4f441,0xa84360b7405960130305,0x7c7686092a1b200002,0x42c70a47844c5423900,0xe517000000002c467642,0x4c40000d47f2a3e8c191,0x9dc0808a1e54457810d2,0xc909a413b411a6099407,0x384380000c8789631,0x311614ea2040001b1540,0x7893490817a2abd0ced2,0xd113209b2253321fc824,0x493d48c00006843b87a6,0xb00d7c38ce2233075c8],#[0x50617845000008972b0a,0xd2be26b0000281aa0000,0x3e0c3404cbd471283e06,0x21a87a52000004862b40,0x936dc0aea1e2f03ca909,0xb10a19340e0e0f9b0076,0x8824394451583cacef10,0x282cc0a2d204b880bc81,0xcb7409f34aa00000906f,0xc00000e237c20a49335c,0x203e2086d8a35852ba06,0x1318000258afc95e0000,0x1ae01d0a34790c740ce9,0xc24cf7612cb1e6848a82,0x124e010409910f585,0x3f1137981198615a2174,0x97a1ada81c00005093e2,0x6446793e40269e20dc05,0xadf05bba4c214e6406f,0x2ef05820d8d81f40001a,0x40001f1194066e245b59,0xb2078cbd3130807ef090,0x2c7112b0388000010dbd,0x7801da89a59223b15e20,0x8224d241202a813d7014,0x465a4370000303dc13c7,0x58091a84fba073987704,0x3949c43a1c117e0ad085,0x834f13740001c1490000,0x1c086fa883c884240a4b,0x20c403136c038b48fa65,0x80338c3e70d2c01ff43a],#[0x5e592de0000b06c791d6,0x12174000002209f2e4e2,0x289e81bbc8f54ceb409,0xcea40b90a1d9433ac0a6,0xd840b1967d4c85113cda,0x112364c61151b530760b,0xa4ee430c2165e49c513b,0xa7c810ac02929f90137c,0x660ef389711480000040,0x62596435789191202a12,0x9de403080958000102bc,0x31863e4b300001863a4,0x390a3587a081d10df800,0x6b5187ea52750935542d,0x9bb03ba387cc9b4e1bc1,0x46049642a805af58114d,0x8cd2a8f9448180003e41,0x2bcc214a25d0000723c3,0xa608d65194000048e471,0x34f7720c69023c888367,0x212121fb05b045080de,0x80cf00003a5451123e,0x401e01aab4eaf059000,0x8708c1a5a04100000000,0x10847805dc918209c4,0x990ed80003d428000000,0x70fe00000417e881,0x9ec1c9103a2a8282110,0x68433e00008496612521,0x7847903c3488ed112986,0x708c602b0a1719278]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0xed2a4a8241fa94250120,0x3cb2ac0907ba58960483,0xfb0cb2a41de9725c120f,0xcbb2e0b079e595705834,0xaecb2ae1a7d8759560e7,0xb92e08859fe41765978f,0x24c3a213ff9460910efc,0x1280907fa549404827ff,0x6a0241fe97250120ff4b,0xa80907f69cd40483fb2e,0xa0241f7a6550120fbcb2,0x80906fe619404837f30a,0x8241fe96254120dfcc3a,0x906fe61150483ef2a8a,0x2417f99654120fbcb2aa,0x907be59160483fd2e4b0,0x41ef96558120dfcc22c0,0x6fe61d60483df2ecb02,0x1df9745c120bfccbac09,0x7de595704837f308b824,0xbf9865c120efcbb2e090,0xf7612734837bb08b9a41,0xfd9855120dbec2aa8906,0xf61964483cfacab22413,0xd875d1209fecc2c8906b,0x595844827fb30ba2419f,0x9561120dbf32b08906df,0x5d844827ff2cc22413ff,0x659520dbec2aca904ffe,0x1654827fb30b2a41afd8,0x59520f3ebb2ca907de64,0x854836fb30b2a41b7d87],#[0xd9209ffcb30a904ffe51,0x64833fb0ebb241afd865,0x9209ffca30c904ff6617,0x4827ff2ec32413ff9561,0x509ffcb30e904ffe5187,0x43cfacab12a1b7d86549,0x9ffc930ca86bf619625,0x3bf2e4b82c1ef9625c16,0xf3eb2ae4b06bf61d6258,0x3fb0eb92c1cfd765c960,0x3ecbacab079f64965583,0xff24c3ac16ff925d960f,0xcc82cab875f595725c27,0xb30b2ae1d7d9759570fb,0xc1300b2d7fe49765c36f,0xecc02cb77f9260165dbe,0xbb00b2edf61d80597cfa,0xc3acbe7d905d965bbfc,0x2e0884ff64b805daeff2,0xa1221ff5425c510ffca1,0x84886ff61d42443fdae4,0x241dfd745c910bfecba,0x907fe59540483ff2e2a,0x241ff96454120ffcbb28,0x907fe5d160483ff2a8b0,0x41bfd845c520ffcb22e0,0x6ff61954483efacaaa2,0x1fbd7459120bfecb2a89,0x6ff61564483dfacab224,0xbfd8759120f7ebb2c890,0xdf59574482ffb2eb2241,0xfd865d120efebb2e8907],#[0xf595844837fb22c2241b,0xd7661120dfecab08906f,0x65d844837fb2cc2241bf,0x9759520fbeca2ca906ff,0x59854837fb28c2a41f7d,0x45d920ffcc82ec906ff6,0x1864837fb30bb2417ff9,0x61920dfecab0c906ff65,0x874837fb22c3a41bfd97,0x4950dfecb30e906ff651,0x6543dfac8b12a1f7d645,0x960f7eba2c4b06ff6498,0x583dfb24bb2c1dfd745c,0x70dffc930eb06ff64987,0x97bfb24bb2e1f7d92595,0x5fbecbb00b2fdf649805,0xbeff20c3acbf7d9061d6,0xbffc9300bb6ff609805d,0xffb24c02edffd945d920,0x9004e80ee028804c0003,0xe0c302ca09f823207c01,0x126045610503d20e4034,0x8e05e2168054a14204d0,0xd87b41d507121b406841,0x896824708c6221084c1f,0xb302b90a8429089f626a,0x3e32b0c4c3000bbe2dc8,0xe3c78eaa3950dea3650d,0x434906840c10023f28f7,0xc212a849491f24699132,0xc947a50b93d84e0934a4,0x95de562155a54614ea52],#[0x7885cf17045b3168a58a,0x5064618cc61898165f51,0x66ab9a5868819de66499,0x72a1c5c7041ba66d41ae,0x9e9e387789d967529cfe,0x19fd87e59f5e7c71ed07,0x215083ea0c2822a04880,0x3548bd22a8899a1f2867,0x4e940a4b6910a3ec8e82,0x49cba6ce99ba60496ba5,0xa4a28d2a1f28129f4278,0xc8aaccaa52a2aa72a96a,0x82ca8b122c06af12b8ca,0xae70b892dceb5bad18b3,0x38bf62f96bd52f12bb1,0xf0581404b9b1f0dac213,0x1722c1223c8c238be138,0x1ae3c1226c7e1f85060,0x149e06a1226c723b8507,0x841f0488fe6c823b88e,0xee23854489b2423e1385,0x1a87d1b181c0688e0cc9,0xc1f0688f46c7e1783478,0x7b85e0d1f86c709385e0,0x27b85e0d1f26c60901a8,0x6e1783879810921b1824,0xf1b1a1107f0b08ca1c6c,0x2f1b0e86a0f01c2d8508,0x62d8c63e14181001583c,0xee3c124721466c604918,0x612141263f9b85121158,0x221463a121a146258f63],#[0x61b888521266c86318a6,0xb636146321218496798e,0x300498b6318f850863d8,0x833e3c128519b1c170b0,0x103b04b9b63e141c1a63,0x47012a2e8f63617181fe,0x8f248b05c8c23c998486,0x1404b870ba17a2e8c45a,0x4882781722c8f6361218,0x141a05c2a0da8b6368f8,0xd8489b1a1a0498f4869b,0x1ae3d16a6c823b8f0689,0x18f8489e1c1404a8e0ba,0x6a1263c9b1b850698b63,0xee1a0498fa6c7e14a40,0xf06b8563e12a6c707f85,0x2307c8fe6ca284860901,0xb844402e87d16e6e8f24,0x7986e161287d9b1c1404,0xe14a407c8f8499b184b6,0x606b850ce1f04a8f66c7,0xa8e1d164528944a8fa34,0x489925164528aa328844,0x381805c250c08b2308f4,0xa1703c0787a2e8f12a8c,0xbc4880c8310c02e09400,0x9b204923b01e209e2749,0xca0701a23833e3d12274,0x33a3a85c0f010bb8fa6,0x103b23d12e6ca220350d,0xc07840bb9ba3cb0841fe,0x266c90fc3d0ec10a1703],#[0x78598e6199ee22141261,0x8585a1462d8f63612630,0x3d9b0b8401d8b6318f0b,0xd28100139b63c2e158ee,0xe060174142c22c8f44a8,0x8527a8ba3d12a3090c09,0xf01a2e8fa34b0701a0cf,0x6c70dc360cc300b385c0,0xc4890da8e05c9e13512a,0x12ca4c0424e149e6209b,0x1a1a9ee151212d1fa6c8,0x8e421052784544a9b252,0xd85a2e8fa303018370da,0xa3c80168ba3d8d0c0501,0xb20a40701a0cf854489b,0x72902107c3be148f44a9,0xc50ec33e1703c068fa6c,0x3d8c0cc5a3985e3e9b0c,0xb180563e9b0cc40158b6,0x9b0ec4040046168fe6c3,0x1782e0f636182005a3d,0x2d0f4309c45c7078360b,0x2730b2370f8489c141e4,0xbc3f0c0d860781a0a836,0x1aa3d1c87d1b140560f0,0x721b1c1f8688f2871b14,0x46ea11c2407f850698f8,0xa2851b184ba0f854791a,0x1a23ca1c6c7e142423d1,0x9831321a86ca0901fe15,0x6a1b1c37838186218507,0xa3e1b158560c1e1248f8],#[0x560f01a3f1b1a1a09112,0x9e61b858861f66c711b8,0x43605c9e1351fa6c612d,0x47e9b200f2784947e9b1,0x2a6c50d8264150327842,0x8311681c6ca87c2483d1,0xc3620370d91885f0e079,0x6ca05f0e2208560c4dc6,0x9285a0e1707988a044d4,0x85c1ea044243f1b1c364,0x7214836204dc6c361c36,0x1a87b85e0c2427e1b201,0x88520d8183c49c6c7118,0x1c24e1583a070fc6c787,0x60d108470b87d96c6c71,0x60e10a220b8461b6588,0xc88430bc44962871b182,0xc3aa0f0144188c2e96c6,0x18a225923c2ca1c471b1,0x2680508f0b28b1b28711,0x8f85212678662e1466e1,0x74663e148499b118c62d,0xa35991a17a2e8c84a8f6,0xf849a2a6c58698b63e12,0xc8a3e1266e1f67458698,0xc2e458104528b44aa0a6,0x23012788b23d8d267121,0x4711a0ce8ba3d1263699,0x10e0282668b6368fc48b,0x9d63f12a6c60a89e2770,0x98c62c9d63f121f01288,0xb18b6311263e9d270127],#[0x2758f26f121d1845c300,0xb4498fa6e9d1ca4c0424,0x12758fa6f12212147c3,0x59ec499ba88b120a428b,0x6c71344b61a85c044c12,0xa887293010908f28b126,0xe66c94711a0ce8f4499b,0x86282f0ada30b78862c2,0x1ea16120b98b63d8d124,0x2ee1c4962d8c63c4a28,0x92148498f66c90c8310c,0xe3c2e66c90b9a485a2e0,0xf0b8813c350d03363849,0x4b1c3f0f43b14b84e6d8,0xc491899c043844985a6c,0x328f128a07b014488fa6,0x20320c4300b985a2c25a,0xdc360ce8ba3d8d0c02c,0x607c1ae14a4a3d12a6c8,0xc9c0585a3e9bc48a4184,0xc460ec3329385a3d12a6,0xd02ea3985e3e9b0cc911,0xe158b63d8c0cca13c350,0xfa6c331612124370d830,0x8528d8b0ed9b203be158,0x185a3f9b0eca0f03a0af,0xed9b143f0f42e28c52e1,0x83e178619d1833e168f0,0xbc330f2749cc5c682e0c,0x30c2d83c330f0d82c270,0x58f8721a86da214370cc,0x86e1a208f28b1b2871a1],#[0xfc6c908447e141ca3c24,0x8890331183b86b8560e8,0x2407c1ae168f60f1b118,0x98c043747d83a6c4c1c,0x1c21e149c83c2487e9b2,0xde170b092c6c390d871,0x2a18260b09fc6c2a0d86,0xf1b10060d8260b09fc6c,0x730f87f1b241e6044183,0xc6c461d218684711b854,0x2a6f12201f06b85c3d83,0x1b1189c0448274a4a3ca,0x890470ec33e170f24b]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0xa000820e0c4950410102,0xc0101838607120c0850,0x1020214080080c20116,0x6020408c5e10900340,0x40000000101ca800004,0x4002031830085000c1,0x10080070408201122808,0x6002050c0c3800208d8b,0x284250610a9706203022,0xc0001000386010800118,0x28e143020b2c340000a1,0x9a0c00200001810b0a04,0x216040020e2020604502,0x1c04011120140,0x62800002182000ca82a6,0x90900001805229d6001,0x2001600082020400104,0x68806000820a21000002,0x5008030504303000810,0xa08a80b86810c810a003,0xc35c0000427468a60c00,0x80e88f7001161346309,0x10d1010d61ec00000000,0x1c0f62091825c,0x40c200000000617e,0xaca001610a4000000000,0x6b3c82b0000001ee0000,0xb2114225088400000000,0x811ae4c50c1d84882244,0xd33a28f582aba0acecab,0xc31a0001666d2173e2ad,0xa447a08c000140f48266],#[0x12689ae720001,0xa13e00000000,0x254c000000000000a30a,0xea210146000121f80000,0x645a0000000000000001,0x1b113c28a00000001,0xc2c600000c8a0000b23c,0x2627a684872782a40000,0xc9166602c05fc1c4889c,0xcd80000ace1,0x1c2a2000106640000,0x0,0xea7600000001418ee1ae,0x27414a7f42d40001,0xa18121160000,0x2915c8464138c0700000,0x24e6e1fa0000614f,0x125b281b20c940000,0x83040000631dd28e,0xc35b651bccb12179c220,0x6197289a000141840001,0xa3168924000025fc661e,0x834c432f121eac83cd0d,0x64eb6a640000c0a9e324,0xa2fd4a38000101c20001,0xc86e000120468114cb40,0xe0ca00014ca3cd44c2c0,0x8aaa0000022b25ae,0x6636800800010a602ca4,0x9121223e63e00768473,0x20db6835294e45a5,0xc40c0000000000000000],#[0x2f468da00000001a307,0x28b20001a056a239ccc0,0x22e10a3085da65c9cd15,0x18eb7e0224a50f062,0xe339455a00000001822e,0x6a07e67446158d5580ba,0xc09fe125cd5e816240c4,0xa54000021a1ca7a6112,0x42dbe1c00000b32a0001,0x435e00000001a5480300,0xa4c625240001a91028b4,0x140340001c2a0,0x0,0x1e45deab7683068ee,0x80f02ca6000000000000,0x161f0033780ef4323,0x22ba45b400000000,0xea870eaca288e5d9a19e,0x1a17a0287aa2c,0x1524101100000,0x2c854d18c1d80000,0x88c0000161bb8eb9a600,0xe16a0001a2e200000000,0xc02f0c17923e0a3c41fc,0x84444af1a919a0c7,0x16721e46200000000,0x24b809d6048600014278,0x62481dc0000a22da132,0x101868896618220c9,0xa0026208000000008892,0x41a8082e000161c60000,0xe212a8bd73239371e41f],#[0x15b0118c40b0156928d,0x5c6a05800016d5a28a4,0xf3380001037202156886,0x1c2480001a6060001,0x68c60001a4d200005212,0xee74e0cfa233465a,0x100d9465523600000,0x2b2,0x12cd4a844ea84,0xa85a00000000699e048a,0x423ac31992d52982083a,0xeef0c2360285c2d60001,0xd3785a9203b21cca0a6,0x492b06734c8ea4e4809d,0x171f0dc8f5000006a2b,0x81aa0899e772223d8205,0x182ee000162194370,0xc190004404cde62b48d8,0xad9eca9d320de32cc653,0x426c200000000000c1a3,0xc2dc0001a9f561b60000,0x813026f34842000041d6,0x125ac00000000,0xa91e0001aa0e00000000,0x4277a18b48e564d9892f,0x209a000060e60000eef9,0x81e800000000e66e60e5,0x83034d560000c1cbe358,0x226a0420000285c0000,0xe169405c000008aac103,0xc0756494014c000189a3,0xe10108120001233d011f],#[0x5a2e12fe0d490c47220,0x108afe2633078e68b,0x1a902220e0000,0x62cd812800000000c2fe,0xe482890f602a7116,0x1cc9f82c360280000,0x8203833200000000ea3e,0x8640800a000182ec0001,0xa0520000b11a00000001,0xd0a00006c9a0001221d,0x736822fb024322c94063,0x8b0f22bfe10f21e6a270,0x2109ad3b,0x80b2e44324c1c668a050,0x80b4e691151200000000,0xd329e22301660001921b,0x22d200000000,0x168b60000a02c,0x8a7c0001c528a0640000,0x3d00dc0000e07a,0x84660000265c0001821e,0x7282e82d68fce6198ce4,0xab720000000000000000,0x73021f40000a5c1227a,0x1182834124f1e1500000,0x9f800000000cc96,0x25784a680fc00002612,0x627e000041b02eed023e,0x6611a145a2ea6365,0x10cfc18c0000c08e80de,0x1246e0860000cad40000,0xa518c1ff48dc69ae8c14],#[0xa50384840000000168de,0x1081c00000001a1a6,0x1e4a4000000000000,0xe8370295425000014246,0x82d9c88ac24e00006888,0x6416457800000039e021,0x414261e1649c000060f8,0x4ddc00004006c092c818,0x1a048f20105b80001,0x364272,0xcc08c175024bc9260000,0xe9200000001600000001,0x180a4000000000001,0x30e00000001415c0000,0x69a600bd463422ae0000,0x1e5a60000,0x891c62a6,0xcc1a00004c1000000c0c,0x604000012cde00992126,0xc526aa4c44384195e320,0x84c200000001,0xd674120033e689e0000,0x43500000000046f025aa,0xa3522d51c8b00000,0x25c348a1e11c00008d4e,0xa48fe74e0001,0x32a0001215e,0x626a0001e43acdb0,0x1e492321ccc8d4c90,0xc9e2260564a000000000,0x616481b904b5059f28c3,0x834548a240cd62160001],#[0xa31088e26158625460b8,0xe24c6cb800002083d24f,0x804dc105a07d,0x28642caca5754c980000,0x1c60ae28308f180c1,0x21c800000001ca8341f6,0x60afa0e3e14a00010d10,0x7206000000000000e06a,0xa905a268f22b60aac228,0x40240000801f2a360000,0x161eb249f64534013,0x1ea90,0x410b08cca41dc2108192,0x108140004000104b2,0x333da4ee000000006d42,0xc73c000166f8e367e2b9,0xe426000090fb0374a17d,0x4a000a100000e461a8ec,0xc0ec00000001a1d3e252,0x34b4b50f281429000d2,0x320f6a46927f429a,0x10068511e0000cdd6,0x214881f200000001d074,0x780000721400000001,0x1a201c49b26476451,0x2824a72421060000630c,0x647489280001a2e8a235,0xea75c36b66f60cb401be,0xa8ca0000c0b766500000,0x42f642f9a6420c898362,0xe27ca92c000164b062d1,0x214008e841e3c8900001],#[0x141bd272365fb,0xc35464da0000,0xc0800000001b20e80000,0xa2400000b0f828ada16e,0x68fe8660012c8061d076,0x1a206a05a00004513,0xcc92603080fee4a2e882,0xa5a0000086207032212a,0x488cc822ace3e63a0001,0xa8ec31f4230c01842b7,0xe4140000326540942497,0x25716066407e40d1e8e7,0x836c0001cf52b22fc6f5,0xa4ddc5f86811634e2e9d,0x10f345096a34008a628f,0x601c000148b9aeab61d1,0xe20c000051f80922416c,0x1a1ce0001d260646e,0x4027e1e4ace801da,0x6a22000000018328c436,0xc06c000128c50298b243,0x4a736638000002cb00d7,0xa43c6137a21a0000c4ff,0x82a2176000000000000,0xc29e2261ecb24a1fed6c,0xe8fa825a4a81e03fc73e,0x8d00000a2f000016055,0x2e9f,0xe8c800016280000100fa,0xc31348a930f7856fa411,0x84cbe26fed0e613be314,0x21980001ed4600006342],#[0xa152000000008088a490,0xe9ec015561a42122,0x6f723600000000,0x2862241b871ea0a0,0x1066b2408,0x83460001e4fc00000000,0xb0f56a93e4ab20b1,0x264e04be52d4d41200e,0xac9c248d813c00000001,0x1,0x9121c64a4296,0x311d23340001a0ea0000,0x200ded62c0be08baa0a3,0xa53488eac2920000a8cf,0xa19d81d40000208429a4,0x681762b421dea4980000,0x2cc868f3088e00002b1b,0xc2a9c83348948dac0001,0xe0334d5264ec62ce481b,0xc2bd40146c0a00000000,0x43574331ca8d506f229c,0x883800000000e32622e5,0x404e000000000001,0x1e8f80000,0x1a19a4072000180f2,0x60960000000000002d30,0x1e368000000000001,0x1aa12000000008188,0x228c00010d34000162de,0x42e600000001,0x4376000000016d702900,0xc8200000],#[0x36fca780000,0x141ac8c860000420a,0x1890de4ad433ae63c,0x48e00a42000000000000,0xe2f20000c259,0x1425e091a61b4,0xa2c54348000060e0]]
def g255D12 := limbs80 #[#[0x5c110e7d765979f59560,0x443fd5c510ff521443fe,0xff940482ff61d10bfd82,0x5c120ff960483fe54120,0x483f79cd20fdd73483fe,0xf7e65483df59520bfd84,0x61d20bfd86482ff61520,0x543df59550f7d52542ff,0xefd62583fe5c160bfd86,0x61d60efd76583bf59560,0x5c3df59570dfd725c2ff,0xf7d87597df60165dfd76,0x5c910ffd42442ffe0176,0x483ff55120ffd71483ff,0xffd65483ff5d120ffd64,0x5c960ffd62543ff5d920,0xf08a045000ffd805dbff,0x2492041c81831471020c,0x353f03a234b3062ca285,0xe6125bb5765314da48c4,0x7d178c75070b6cf68a64,0xab96692a8dc8a086480d,0xab37afbab6a71a2c9f09,0xe0ec4617061e0d06c7b6,0x1b1c4985c1e043c880d8,0x86c462e1423830fc2c47,0x61005844401b1c220b09,0x381507018588e3636170,0x486c2e0e02880842e36,0x68f092307c5e131f9b0a,0x2e3c34124d8d87c285d1,0x4784c287f3612478e8ec],#[0xd121e0b0144a3d1b1218,0x7e6c244c16028c452211,0x249b202d8b080bb0814c,0x4644874721a029ec4616,0xd1e1246130580a3d168d,0xf0926c80c05c6187c2a2,0x4b368f24381a470cf0b8,0x170c0e210f8407784c28,0x83c2e8d1f0f850583c18,0x70b8786a184e17061e05,0xf8691f1b183c171b6170,0x1d85c7870341b1b0b830,0x63617061e45a3c348c1c,0xd23e363e1706240d23c3,0x1f9b1087c61207f0b830,0x80a7b0b838fa6c7c2614,0xd9385c18901e1f4d8c86,0x68705c6d88c2e0c3c818,0x87c6c6c2e0f021e07c6c,0x217114b46c8c2e0d0224,0xb88a8636231a14830862,0x4218545a6e24a01d0b0,0x4680e1d168c47a66243c,0xb892887474071e9b8927,0x3d189e890e2380e111f9,0x24c2a3e249b1e038545a,0xe16170f862722e329202,0x3c491b230a8f8da86342,0x2307f0b830d4]]
set_option maxRecDepth 16000 in
def g255H12 := limbs80 #[#[0xc019d30020708234e000,0x9c70030810800400052,0x2148602007803bc405,0x801823002c36830880a3,0x30020c3b141021050024,0xe4f00304828050002c14,0x1003141c010c4dda,0xe0001ccb4838ea205282,0x28119f883e488949e614,0x741611910,0x6a49a000101d00000000,0xc1b96c722d2190c33a09,0x21c9d279c610001e0791,0xa02ad12302c2310d0e8,0x16681f0001c49da04000,0x89b1d28c214d24d288d4,0xa0000f138134d9a120dc,0x4e619e0001c00c000025,0x8668000087930c200032,0xc2ac00000000000e8ce,0x601c00020c2000,0x3d24800042a541080,0xbd21a00000007110a494,0xbd7006f00e4113841cb7,0x427d6340000b4d600021,0xcb009a41390140001,0xa5f94ca0d3c0fc4c4800,0xe4a0000314800000003c,0x5e01721bc000000f02c4,0x8a9a0850aee9300005a9,0x391d5921f83400034,0xdd8a491640c3a19798a6],#[0x21090a6a1ad814413,0x4845127326de20a29500,0xec01ba9a8c420000a6f1,0x4f002d8139e19b8218b1,0x4014c09000145424,0xbe330acec0001117d240,0x350000c019a23fe4ca07,0x24a780000001a069c,0xa0b545540000000d00a,0xbb800030f5826c000000,0x2ff02eb74121a19,0x7f0c40003112a0110930,0x23105182ec256e58a804,0xc23362f0000112021f04,0xa6043825ec438000b23c,0x24999630fa0002a31e82,0xb16a412703232cb81224,0x58633214802c800986ea,0xb7800080030083c49008,0x60d4000044fb8ba0001d,0xd192200000000000b490,0xc45a1d0001c570000381,0x1425305e7032c8285,0xc27600000007022c61e,0xc5020aa8204000000,0x284880000001e9600,0x283c88c80000000,0xb9099952b40000000000,0x25b9c2a49427434480e9,0xf309ca137825c082a238,0x8174000310,0x642c0004123000060e40],#[0x1c46cd0f00000000,0x30660000000000,0x250830383b3130c9bb4,0xd00000001a329b176280,0x318000143e00000005a9,0x1ddca8c81b1661f097c,0x3000000000001c9596e3,0x125e0001811614e2b7,0x62840000000b0e1e0f00,0x8270a07182d9b0e6099,0x330041306c6c58817b08,0x289c0006c60000001e12,0x141d089a83a8253a0d9,0xaa709a324421b5818919,0x486182b71958015c2648,0x4c1100974000407e742e,0x2a183400010280c11bc9,0x484cdbcb12e94de302a6,0x9050ec8a050ce83e0000,0x284050576097487088,0x10c90000565669840,0x91126894b992383804b2,0x2848000282,0x912b42e0000927502340,0x7a29a000000000000000,0x9bf073042dc010000081,0x682481eb8370000440fc,0x3000000000000000f116,0x970000a531314522c601,0x492a4ec88e026140439,0xd325749804a4c076a443,0x278000953200c19ba636],#[0xd0db07f00016048c,0xdd29580638450384e438,0xc9fa15a01104e680b509,0x28921280000c2f911250,0x7086b12b]]
def g255D13 := limbs80 #[#[0xefccbdf597ef39fdd73,0x70ffac1ff543fe907fd1,0x800ffaedff597feb8ffd,0x9e86c9744d8f82e8740d,0x160e04243c346a4a5487,0x46c88583810c0a080e1e,0xb0d0c1c38187a22160e0,0x160c2c446c78583810f0,0x8b0184858f9b121c2a22,0xa1b1a1e160c2c3c305c7,0x160c3e6c7c60e85838f1,0x7878583810b201b1a12,0x3810f1b1a160e042c3c3,0x24858]]
def g255H13 := limbs80 #[#[0x4044000104000c0b10,0x260000000002ca00000,0x572f48049c0000000002,0x7dc600000052a4000000,0x94000000000348,0x840014190000000c4e28,0x207400000000048,0x0,0x2ab02d800100a0001678,0xa20000000000000310e,0x0,0x6000000184b000000000,0x5168960e201c00000020,0x705000150000000014,0x44c00000000000000000,0x0,0xe04,0xca2000000,0x14ce000000000000,0xe090003d2800000000,0x0,0xf0080025400000000,0x91e803482910c,0x2080000924000000000,0x500005cc000000000000,0xe3,0x4b900,0x73380000000000,0x11880000aa5658000,0x2052000000286c000000,0x3a6,0x0],#[0x111800182c00000000,0x84200000000,0x50798980000000,0x934000063a,0x132af91500b8a2403000,0x79c6bc48000000000000,0x140d94c84604d200030,0x645400000000000000,0x40000000000000010110,0x1c70,0x0,0x39c000000000000,0x349521a310000000000,0xe0f800000141000000,0x8a8000519a29a9200000,0x1,0xc94e038000,0x7110000ca4000000,0x0,0x4150007b3393c00000,0x83000000000018213a00,0xe5748ab,0x82280000000000000000,0x298c001643,0xb0b8000000c9d000000,0x1c1600,0x0,0x8ac00000000000000000,0x727c,0x9a0000000000,0x2138000000,0xa0000000000000000000],#[0x18,0xc000000085700000000,0x7,0x0,0x40000000000003012000,0x325]]
def g255D14 (j : Nat) := if j=0 then 0xb08141811e6c7ff else 0
def g255H14 := limbs80 #[#[0xd12d1883bc8000c,0x384017e0400524b14000,0x200000000000301aa000,0x49c000000000000058,0x6b5000000000000,0x80000060a000c4000488,0xe8ec0c00000000e1,0x19504c0000]]
def g255L : Nat → Packing
  | 6 => (2,8,7,0,0,3,0,g255D6)
  | 7 => (88,7,7,0,0,12,0,g255D7)
  | 8 => (369,6,7,0,0,15,0,g255D8)
  | 9 => (631,5,7,0,0,16,0,g255D9)
  | 10 => (444,4,7,0,0,16,0,g255D10)
  | 11 => (162,3,7,0,0,14,0,g255D11)
  | 12 => (44,2,7,0,0,12,0,g255D12)
  | 13 => (12,1,7,0,0,10,0,g255D13)
  | 14 => (1,0,7,0,0,0,0,g255D14)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 5 1 0 g255H7
  | 8 => lookupWord 44 239 7 14 7 3 g255H8
  | 9 => lookupWord 190 877 8 16 9 3 g255H9
  | 10 => lookupWord 323 1481 9 17 10 3 g255H10
  | 11 => lookupWord 231 1373 7 16 9 3 g255H11
  | 12 => lookupWord 91 499 6 15 8 3 g255H12
  | 13 => lookupWord 28 419 3 13 6 3 g255H13
  | 14 => lookupWord 5 59 1 11 4 3 g255H14
  | _ => fun _ => none
def g255 : Forest := ⟨255,14,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P6_0 : block g255 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B6 : block g255 6 0 2=true := g255P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_6 : block g255 7 6 82=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 88=true := (@block_merge g255 7 0 6 82 g255P7_0 g255P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_31 : block g255 8 31 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_127 : block g255 8 127 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_140 : block g255 8 140 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_236 : block g255 8 236 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_332 : block g255 8 332 37=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 369=true := (@block_merge g255 8 0 140 229 (@block_merge g255 8 0 31 109 g255P8_0 (@block_merge g255 8 31 96 13 g255P8_31 g255P8_127)) (@block_merge g255 8 140 96 133 g255P8_140 (@block_merge g255 8 236 96 37 g255P8_236 g255P8_332)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_3 : block g255 9 3 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_99 : block g255 9 99 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_195 : block g255 9 195 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_227 : block g255 9 227 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_323 : block g255 9 323 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_419 : block g255 9 419 61=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_480 : block g255 9 480 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_576 : block g255 9 576 55=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 631=true := (@block_merge g255 9 0 227 404 (@block_merge g255 9 0 99 128 (@block_merge g255 9 0 3 96 g255P9_0 g255P9_3) (@block_merge g255 9 99 96 32 g255P9_99 g255P9_195)) (@block_merge g255 9 227 192 212 (@block_merge g255 9 227 96 96 g255P9_227 g255P9_323) (@block_merge g255 9 419 61 151 g255P9_419 (@block_merge g255 9 480 96 55 g255P9_480 g255P9_576))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 58=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_58 : block g255 10 58 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_154 : block g255 10 154 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_250 : block g255 10 250 63=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_313 : block g255 10 313 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_409 : block g255 10 409 10=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_419 : block g255 10 419 25=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 444=true := (@block_merge g255 10 0 250 194 (@block_merge g255 10 0 58 192 g255P10_0 (@block_merge g255 10 58 96 96 g255P10_58 g255P10_154)) (@block_merge g255 10 250 159 35 (@block_merge g255 10 250 63 96 g255P10_250 g255P10_313) (@block_merge g255 10 409 10 25 g255P10_409 g255P10_419)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_11 : block g255 11 11 88=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_99 : block g255 11 99 61=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_160 : block g255 11 160 2=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 162=true := (@block_merge g255 11 0 99 63 (@block_merge g255 11 0 11 88 g255P11_0 g255P11_11) (@block_merge g255 11 99 61 2 g255P11_99 g255P11_160))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_2 : block g255 12 2 31=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_33 : block g255 12 33 11=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 44=true := (@block_merge g255 12 0 2 42 g255P12_0 (@block_merge g255 12 2 31 11 g255P12_2 g255P12_33))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_4 : block g255 13 4 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 12=true := (@block_merge g255 13 0 4 8 g255P13_0 g255P13_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P14_0 : block g255 14 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B14 : block g255 14 0 1=true := g255P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact g255B6
  · exact g255B7
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
  · exact g255B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 14 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=14) (i:=0) (before_sound K253 V253) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_52832

open PEqualNP.Outside.L_meta_52832 in
theorem PEqualNP.Outside.L_meta_52832 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
