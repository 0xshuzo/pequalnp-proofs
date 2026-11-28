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
def K99 := extendKnown K71 4 [(99,[]),(102,[32]),(105,[49,33]),(114,[64,32,50]),(139,[16,67,83,118]),(142,[16,32,67,83,118]),(154,[112,49,32,33,84,97]),(170,[112,49,32,33,97]),(232,[112,49,32,66])]
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
def g255C : List ColumnInfo := [(0,8,181,66,12),(1,0,254,0,12),(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,12),(32,0,223,0,12),(64,0,191,0,12),(128,0,127,0,12),(2,8,181,64,11),(10,0,245,0,11),(34,0,221,0,11),(40,0,215,0,11),(64,8,181,2,11),(72,0,183,0,11),(160,0,95,0,11),(0,2,53,200,10),(3,0,252,0,10),(5,0,250,0,10),(6,0,249,0,10),(17,0,238,0,10),(20,0,235,0,10),(33,0,222,0,10),(36,0,219,0,10),(48,0,207,0,10),(65,0,190,0,10),(66,8,181,0,10),(68,0,187,0,10),(80,0,175,0,10),(96,0,159,0,10),(129,0,126,0,10),(130,0,125,0,10),(132,0,123,0,10),(144,0,111,0,10),(128,2,53,72,9),(192,0,63,0,9),(0,32,74,149,8),(161,0,94,0,8),(164,0,91,0,8),(1,32,74,148,7),(4,2,49,200,7),(4,32,74,145,7),(7,0,248,0,7),(16,32,74,133,7),(19,0,236,0,7),(21,0,234,0,7),(22,0,233,0,7),(37,0,218,0,7),(49,0,206,0,7),(52,0,203,0,7),(69,0,186,0,7),(81,0,174,0,7),(84,0,171,0,7),(97,0,158,0,7),(100,0,155,0,7),(112,0,143,0,7),(128,32,74,21,7),(131,0,124,0,7),(133,0,122,0,7),(134,0,121,0,7),(145,0,110,0,7),(146,0,109,0,7),(148,0,107,0,7),(5,32,74,144,6),(17,32,74,132,6),(20,32,74,129,6),(129,32,74,20,6),(132,32,74,17,6),(144,32,74,5,6),(193,0,62,0,6),(196,0,59,0,6),(208,0,47,0,6),(21,32,74,128,5),(53,0,202,0,5),(133,32,74,16,5),(145,32,74,4,5),(148,32,74,1,5),(85,0,170,0,4),(149,0,74,0,4)]
def g255A : List (List Nat) := [[],[66],[32],[32,64],[64,32],[64]]
def g255D7 := limbs80 #[#[0x42bd4725765957250120,0x57a8e3b2cb2ae4a0241b,0xf51c665d655c940482e8,0xa384d3acab22e0905d0a,0x70976595845c120b615e,0x9360bb2caba241b829c4,0x659655c940483385788d,0xbacab9280907d0af51c7,0x5d96550120fa15ea38cc,0xb2caa0241da2bc4f09b8,0x59540483b457a5e2370b,0x2a80906e8af4bc46dd86,0x58120dd15e9788db30eb,0x8241d8a9a76d1b25d984,0x483d857a8e134eb2ac8b,0x762a699b46c97661170,0xec55e1780dc2ecba2c89,0x26bc2f01b961d6559120,0xf78fe0372c3acab2241d,0xf11b26c19759564483a0,0x9788d832eb2ac890758a,0xf01b85d9655d120db14d,0x370bb2caba241d86bc2,0x6e17659574483b07789e,0xa30cb2ae890760ef43c4,0x61d655d120ec1de836ed,0xb2cac2241b83bd0f11b6,0x59584483b0d32ed9360b,0xb2ca90649ef41cbae576,0x59520d534e2765d8350b,0x2a41aa3bb4713b06a176,0x48354d765e0368d42ecb],#[0x6a8eed3c06d1a85d965,0xd43dd878eda350bb2ca9,0x83fb4f1db46a17659520,0xd2e9d9760d3b0cb2a41a,0x713b2ec1a761965483b0,0xa765d834cc3aca90669a,0xecbb06998759520ec34b,0xa764c3acab92c19a69c4,0xec98759572583b0d7a0d,0xa30eb2ae4b06e1af41c4,0x2e86e0f800dc35e8784d,0x8ea348ba2888a1c660ea,0x9aa6497a5894a4c91a40,0xa6a94a3a88a0a7c9da70,0xb2ac4afab8acaaca9aa0,0xcfd03fe004b8adcb5ad0,0x14033b483f800c04700,0x800fd824101044d483f8,0xf807e0002330047b84bf,0x12f44328ffa03d00ee02,0xf805e00952866203050c,0x1e1856f82fc03e80f602,0xa8812]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0x82e8af19855954250120,0x120f829875d965509404,0x40482e8a721765954250,0x250120f2299761965509,0x50940482e8af1d865954,0x916250120f0a99761976,0x5745894048362a6dd875,0x655d16250120f8298759,0x76597458940483b0a69d,0x69d965d16250120f0a98,0x69a765d655894048392a,0xe0a619655d17250120e4,0xb469c95d9655c940483,0x483c1a65d86595725012,0x8120f229966116454950,0x960483c2a65d845d1625,0x7258120f82965611745c,0x55c960483c1a65d65611,0x5958458120b46bc465d6,0x1da25956048368a6d1b2,0x165591725c120e869a76,0xc4619655c97048361a6e,0xaf19b8595725c120b86b,0xc69c2ed17659570482e1,0x338aed1a268165591209,0x20f069875d9926416548,0x258391ae9d7664990595,0x5c960cc69a7ec1a25957,0x940482b1af01a768965,0x54250120fa29c85d9655,0x6550940483e8a71d8659,0x75956250120fa29c661d],#[0x6d17658940483b8a711a,0x11b95d96250120f8a987,0xbc46dd96589404835aaf,0xaaf11b665d6250120b6a,0xfc29c45d9655c940482d,0x83d1a725765957250120,0x120f469c7659655c9404,0x40483d1a719975957250,0x250120f8a9866d1765c9,0x5c94048356af11b95d97,0x5d7250120b5abc46dd96,0x97659540482d6af11b66,0xb25d96550120de29b46c,0x96c97659540483d1a65d,0xf09b85d96550120d669b,0x3bc46e1765954048369a,0xe9af09b76196550120da,0xba3bc46dd8659540482,0x482e9af09b661d655012,0x8120ba3bc46d98759540,0x960483d2af11975d1625,0x6258120da6bc56e17458,0x758960482e9af15b7611,0x5917258120ba6bc56d18,0xd9845c960483d2af1197,0x1975957258120f8a9c45,0xc465d655c960483d1a71,0xaf09975d16458120f46b,0xeabc46c9a759160483d2,0x3d1af09975957458120a,0x20f43bc465d655d16048,0x482f2af11b25d974581],#[0x58120e87bc56a1765d16,0x95604836aa6d1b25d984,0xd6558120d669b4ec9975,0x9759560482d9a713b265,0x461d7658120b66bc26d1,0x595845c970482e1ef15b,0x1186595725c120f869b6,0x9c269d6559170483e1a7,0x1ef1da8595645c120ec6,0xbcabc46c97659170483a,0x82b6af11b269d645c120,0x120f839c4619655d1704,0x70483e1a70976595845c,0x45c120b87bc769965611,0x5957048366a6d1b25d98,0xd9655c120dc69b46c976,0x18659570482f1af11b25,0xb05d97459120b87bc76d,0x6e1765d16448372a6c9,0xf01b76197459120d8bbc,0xbbc06d9875d164482e2e,0xc9ef01b961d6559120b8,0xb07fc76e58759564482,0x48349ef01b961d655912,0x9120d07fc76e58759564,0x56448359a6c9b065d655,0x6559120b63bc46c19759,0x759564482c8ff11b865d,0x6616559120b07fc76e19,0x89a05d964482c9ef01b7,0x9b05d9655d120ceabb46,0xc46c1765957448371a6c],#[0xff11b85d9655d120bc3b,0x87bc06e17659574482e0,0x360ff11b85d9655d120d,0x20d83db76d1865957448,0x4482e1ef01b7619655d1,0x5d120b27bc06e5865957,0x9574482e1ef01b661d65,0x1655d120b83fc46d9875,0x9859574482c9ef01b666,0x2681765d120b07fc76d9,0x6c1765958448336aed1a,0x1db95d96561120da69b2,0xbc06e57659584482c1ff,0x1f71eb95d965611209a7,0x927dcbae57659584482c,0x8269e703b95d96561120,0x520ec6ba76c976641654,0x6548339aed1a26817659,0x659520987dc7ee9985d9,0x5d965483a9aecbb06a17,0xa17659520aa79c4ec1a8,0x1a85d965482a9ef01b46,0xb069d8659520a87fc76d,0x4ec1a76196548369aecb,0xecbb069987595209a79c,0x79c4ec1a661d6548369a,0xb3af09b469d625c1609a,0xd86db4ec98759572582,0x582e1b713b261d655c96,0xc960b87bc06d18759572,0xd65582e1bf09b461d655,0x76595709a79c4ec1a261],#[0x25d9655c331e693b0689,0x65962501209c79c4ec1a,0xd99758940483daaf11b7,0x1b76597250120f6abc46,0xc46d9975c940483d6af1,0xa711b25d96550120f5ab,0xa3bc46e17659540483f8,0x3e9af09b76196550120f,0x20fa3bc46dd865954048,0x483e9af09b661d65501,0x50120fa3bc46d9875954,0xd940483aeaed3b26a176,0xd8650120ebabc2ed1a85,0xa661d404836eaf0bb469,0x66117258120dbabc2ed1,0x6c9a759160483e3a72d7,0x9db25d98458120eeabc4,0xbc26d19759560483e3a6,0x6af11b269d645c120f66,0xf879ca5d96561170483b,0x83e3a699b25d9845c120,0x120fc69c46c976595704,0x64483f1a709b45d9655c,0x459120f8bbc06dd865d1,0x59564483e2ef01b661d7,0x1d6559120f27bc06e587,0x58759564483c8ff11b96,0xb065d6559120f07fc76e,0x26c19759564483d9a6c9,0xf11b065d6559120f66bc,0x7bc06e19759564483d8e,0xc8ff11b865d6559120f2],#[0xf07fc76e19759564483,0x483c9ef01b7661655912,0x9120eaebb2ec1a85d964,0x964483aaeed3b06a1765,0x8659120eabbc0ed1a85d,0x461d644836aef03b469d,0x6a58759120eabbc0699a,0xc1a961d644838faecbb0,0xbb06a58759120e37bb5e,0xb7ec1a961d644838beed,0xfedbb56a58759120e1fb,0x17fb7ed5a961d6448389,0x383fedfb66a58759120e,0x20e7abb4689a065d6448,0x44835ea68bb468197591,0x5d120f83fc46e1765957,0x9574483e1ef01b761965,0x9655d120f83fc46dd865,0x8659574483c9ef01b961,0x661d655d120f23fc46e5,0x6d98759574483e1ef01b,0x1b6661655d120f83fc4,0xfc76d99859574483c9ef,0x7aecbb06a1765d120f07,0xe9bbb4ec1a85d974483a,0x83a6ef03b46a1765d120,0x120e9bbc069da4619744,0x7448366ef03b4699875d,0x85d120e37bc069ba5661,0x6617448385ff1da6e959,0x95985d120d37bc06dba5,0x1765958448345ff1db6e],#[0xb95d96561120f879976c,0x76e57659584483c9ef01,0xf01b95d96561120f07fc,0xe996689a05d98448369e,0xa7a65da26817661120ea,0xf0f9a065d965d984483,0x4830fef01baaa5766112,0x1120c37fc56eaa95d984,0x9654832def01b6e95976,0x7659520ee69b4689a05d,0x45d965483b9a709a4681,0x6a17659520ea3fc46a1a,0xc1a85d965483a9e6d3b0,0x1b46a17659520ea7bb4e,0xb46d1a85d965483a9ef0,0xff1db46a17659520ea3f,0xa7bc0ed1a85d965483a1,0x3a9ef01a76918659520e,0x20ea3fc469da46196548,0x5483e9aecbb069d86595,0x59520da79b4ec1a76196,0x196548369eed3b069d86,0xd8659520ba79c4ec1a76,0xa461d6548369ef03b469,0x66918759520ea7bc0699,0xec1a661d65483a8ff11a,0xd3b06998759520fa6bb2,0xbb4ec1a661d6548369e6,0x9e713b06998759520da7,0xda7bc0ed1a661d65482e,0x834fa6d3a2e81985d920,0x920d3bba46d3a0661764],#[0x764834fae8bb0691985d,0x85d920d3bba4ec1a4661,0x661764834dee83b56919,0x91985d920d2fba0ed9a4,0xda4661764834afe93b66,0xb7691985d920d1fba0ed,0x4e8ba065d8648346fe93,0x5d3a2e819761920eae96,0xe9b4e8ba065d86483a7a,0x8def0196e959461d20cb,0xcb7bc06dba565187483,0x48325ff1db6e959461d2,0x1d20eae964e8ba065987,0x987483a7a5d3a2e81966,0x625c160cbe9b4e8ba065,0x261d62583b3af09b469d,0xe898758960eaebc0693a,0xc9a461d625836baf01b4,0x1b461d655c960daebc0e,0xc26d18759572583e1ef0,0xaf01a4e89875c960f86f,0x9ebc06d3a261d72583a7,0x367af03b2691875c960d,0x60ea79a4ec1a261d6558,0x5583a9ee93b068987595,0x59560da79b4ec1a261d6,0x1d6558369eed3b068987,0x98759560ba79c4ec1a26,0xa261d6558369e693b068,0x46898759560ea6fc2691,0xed1a261d6558369ef03b,0x1b4e898759560da3da4],#[0xdc12302d4047000369ef,0x34f0b84273087c1be05,0x5a215384e011c84110ec,0x9a1db47191b1467e1874,0xb24f88dd22c085c1f507,0x2a9ca2c27fc9d2269496,0x41ccda3218c252edcb15,0xa0f473ac8e373724d5b3,0x118044b10a441750093e,0x3ed4e993384b91269482,0x5a581958b54414a25105,0xc60957d15dc171c5a856,0x69799e365d590762cd86,0x431c917025b9b6c81acc,0x79eca79d9dee769dd607,0x213782f205b7fe9f8c7c,0x3088ad227a89021ec866,0x3493b649991163e48da6,0x49c666d2995e60396225,0xa5168e4a2aa870a0a679,0xd92b37ab5aa5ba81e9b3,0x72d08b236c46b066bb8a,0xae98b97ae17b742d96b5,0x42bf86f8dbd4ef0cbb4,0xecc79b178c4c70eac227,0xc82b204c7fb1f8c7cb1,0xc8bb228c88b21cc85b21,0x94b24cc91b240c8eb234,0xdb270c9ab264c97b258c,0xb294ca3b288ca0b27cc9,0x2b8cacb2acca9b2a0ca6,0xdccb5b2d0cb2b2c4cafb],#[0xcbeb2f4cbbb2e8cb8b2,0xcc7b318cc4b30ccc1b30,0xd0b33cccdb330ccab324,0x9b360cd6b354cd3b348c,0xb384cdfb378cdcb36ccd,0x3a8ce8b39cce5b390ce2,0xcccf1b3c0ceeb3b4cebb,0xcfab3e4cf7b3d8cf4b3,0xd03b408d00b3fccfdb3f,0xcb42cd09b420d06b414,0x5b450d12b444d0fb438d,0xb474d1bb468d18b45cd1,0x498d24b48cd21b480d1e,0xbcd2db4b0d2ab4a4d27b,0xd36b4d4d33b4c8d30b4,0xd3fb4f8d3cb4ecd39b4e,0x6ce3c5d45b510d42b504,0x21227344705782938b5c,0x4302110ea73bc15e0a,0x43a019705671fc149cd1,0x9d02432867343011808a,0x40192e3e7342c46f82b3,0x88df05571f39a1f82bc1,0x91e3f334330528248a1,0xe852b3442273237a14a,0x10043ace8122a3683a55,0x69201c7aa87825a14acd,0x51b84e2e3eb343811808,0x145c7d6687a0cb049241,0x8ccd0e51ba0ca4838252,0x2009491be096676c2904,0x982518fc90685314279a],#[0x825e85a904e68801f80c,0x4339a1808e43c019c63f,0xbc8f25a4111b9ce81299,0xa504913bc1788af22d71,0xf06e22ab8fe4d0ec1680,0x480090e9a15833412451,0x74095915b4d0ce9d70ce,0x3824d15d4d0c4a36905a,0x85ba9a12106b98a0f548,0x4e68ae0ca27793484010,0x482d9c7523f841b85e0f,0xf850194e68601a00cc06,0x2f0222e683e10707a73a,0x85106879c25614ccd0e0,0x8824c4b9340c40c04759,0x569a0620691284eda681,0x682801d467a341400f22,0xb82b38fe0a4e68968cf4,0x7344011808a82b9ce80c,0xe0a811808a0325c7f052,0xace3f828b9a21d1843a,0x870425ce811808a032e,0x8c0349c7e669c2844122,0xec12ccd0e047e0910f80,0xf801903c01cc8dd85171,0x8f0c08e03c019f40f71f,0x2a8dfe0371e300cff017,0x250f04a734400f1429f8,0xcd100470220a7370ce14,0x8a033414c63dc29c129,0x1e033b0a4e69a404811c,0x4b9a2c08e43c90cf0493],#[0xe811c0675208c790f382,0x663d7343c12a0890405c,0xe0070108a71033614609,0x4701e00cf31fd03dc3f,0x3350a563ea41b87fc00c,0xaec100f331ff80bc38a0,0x88dcc81c28aa1b096668,0xa66686023811b33a89c,0x6668a00dd84931e04a7,0x3b11b41990a6c25e8599,0x5e85fc00114702381173,0xe85fc01204a02300cbf0,0xc8e8475f038197e0b31e,0xe08065e85fc001146022,0x4bf04e85fc0563c80257,0x3c2804a1408b819213e8,0xf05f808250c045fc17e0,0x1e915e4d0e0458193a17,0x1c9a23837c12811c07a7,0x2c0b5f0d03e81e40eb71,0x90a484f03abc472689dc,0xe179344e057028f86dc2,0x81e7c340b4852427dc45,0x8f811c86522ba9a1b041,0x2416d63c94769a178255,0x22c63df0bc12d4d1381,0x4d0114602390f0067520,0x2454720f2e6231ed15d,0xd89c80f7e0a83338ffc,0xa04744e584bf05b8ffc0,0x1457090129a2ba9a0228,0xff0031684097e12d4d01],#[0x53444082c25f8260a663,0xf81be1a07d03c81d40b7,0xa1048047b8fd4d11d85,0xafe0008a4a272437a192,0x7883390f663ef04f8238,0x6427fc15c0ff00045214,0xa1e70972686cc7be1506,0x3cbc2f2689213c0cef0b,0x83024f86f8198a484f0,0xcc06478ee0f1e6809046,0x406539ac4795c2001a00,0xde1070780680339c73e1,0x947811e942e12ccd1242,0x47e668621f00d214719c,0xa66685a16e63a0670325,0xd84bb342c06ec25a8f60,0x84994339a2808e8a1d47,0x42d98dce3b11e0330195,0x86e0a012854739a18068,0x8819c0ca7350481985bb,0x2096a3c047b9a2271ce8,0xcd58488450c88343c414,0x44099c023e23c08caa1c,0x25a88ec338533340461e,0xd033bc2b23f33438882c,0x89c3896a689213e84b31,0xa08203c02350dc86731f,0xcbe0798ffc17217f003,0x66b1ff82a50fe00601d0,0xbf0549ccc7fe00601928,0xf05e85fc00528401d247,0xf2346e477a1791a14a13],#[0x2347027723bd0bf03cc7,0x4e4c7fa17e07f01e477,0x33023fa1731e712e4d12,0x5fc05c48751f48f10690,0xfc00c04b023a273f0404,0x4d0c89c3887c0f31ff01,0x68bc8e184228fe07f01e,0xf2686026a0cd06558fe4,0x668964e506c42b819ec7,0x89d48d8114095e853896,0x4bf81fe0008a3011a233,0x3f80ba17f004aa87f040,0x14a4989d3886a23f05f0,0xcd1204a019011bd0b99a,0x47588f11d7c0fe02e85c,0x7f01350e668b0230116,0x1a40ce45b98e019323fe,0x501182656a1ccd0aa3a8,0x4a11233e85fc0723c402,0x5fc0412870237a16b340,0xfc010046022fe08f20e8,0x909159d027212d095e88,0x9c84c425a12ab1a37e0,0x40215c0f723fb3435638,0xa04ab0a663f3344b2868,0x98d1f33a91b88c808dc2,0xe638c2000ff42fc0fe03,0x14c7fe006fc06e208901,0xcc7e63873087a17e07f0,0x240798df42fc0fe02210,0x97e0bf0004c1771199a2,0x4c49f0bc9a0229201ba8],#[0x110648f7276836315a90,0x684f81fc04621c87fc00,0x9f0bf801008c032022f2,0xe07c8fbc2fe005819011,0x1df03f80de1791a2a0cb,0x118402300c808bc9a139,0x14095a9a11f0b419fc00,0xbf04f85fc04128502301,0xd0da8f0235e17a342011,0x8ea3c90f623cd2a045e8,0xf88f7c2949ed07d1a022,0x4b022fa0fa340471408,0x23293e87af0ae83e8d0e,0x51c85067f000461408f8,0x8903484e29c9a0230af8,0xc10a90721701fc001188,0x3a10f85f]]
def g255H8 := limbs80 #[#[0xc120300301b3073e3041,0x695000000218a0000031,0x78738402090003090000,0x1896000000292fc0a88d,0x1800293f825109800000,0xa00030bb10912200031,0x4001c07850f41f8455,0x98600030fc0788180000,0x63080014120000a90,0x5268001815,0x420cd834000000803886,0x6c125a0b0003805844e1,0x21288d81260944050d50,0x899d3061db028001c0c6,0xc41e07402381e4270003,0xa85a0042a20600001536,0x3420000c60]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0xc0907a29865954250120,0x55c970483a34cbacab92,0x30ab2a84a0241e1a6196,0x7aa9865954250120f65,0x940482dd4dc2caa12809,0xb2a84a0241f8a5d96550,0x29b85954250120f6530e,0x482dd5db30aa1280907b,0x84a0241eaa6197650940,0x85d94250120f3530ebb2,0xdd5dab0ca1280905ba9b,0x241cea65d8650940482,0xd4250120b7576ec3284a,0xd32a8a9280905babb661,0x1f8a5956454940483794,0x50120dd534cb22a4a024,0xcaa92809076699659552,0xa6999554940482bb4dca,0x20aed76ccaaa4a02419d,0x12809066e9a665952501,0xd6458940483d54c3ac8b,0xc52caba2c4a0241baa69,0x907ca9765d16250120f,0x58940483b54cb2e8b128,0x4eba2c4a0241e6a61d74,0x7669955956250120db53,0x40482b74dcacab128090,0x2ac4a0241f8a6d165589,0x9975956250120f4d30eb,0x83734d3acab128090766,0x4a0241d9a6e565589404,0x5d96250120f1d30ebb2c],#[0x74dcaecb12809074e997,0x2415baed59658940482b,0x6250120e5d30ecb2c4a0,0xbb2cb12809066e9a7659,0x97a69d9758940482b75d,0x120fa52caba2e4a0241,0xab92809079a9865d1725,0x619655c940483e34bb2c,0xecd32cb2ae4a0241e9a,0x28090756997595725012,0x765c940483c74c32ecb9,0xd372bb2e4a0241d3a659,0x9071e9976197250120ab,0x9540482af5db32eb9280,0x8d12caa024169eed9855,0x669966896550120de534,0x4833b4d4b44b2a80907,0x2caa0241e1e61d765954,0x976196550120b4f370bb,0x2d3ddbb0cb2a80907279,0xa8241c3e65d865d94048,0x915254120f65308b22a4,0x4cb308a92a0907669965,0x415daed196549504839b,0x254120ecd32caa2c4a82,0x2c8b12a0905e69b65516,0x9a5958458950483d54c2,0x120e5d32cc22c4a8241e,0xb12c09056ebb46596254,0x1d7458960483d54c22e8,0xe9d32eba2c4b0241e3a6,0xc0905ae9b85d16258120],#[0x458960483974cbb08b12,0x768c3ac4b02416baedd8,0x56ebb465d6258120b5d,0x960483e54ba2c8b92c09,0xb22e4b0241d3a65d645c,0xa9845d17258120b9d36e,0x483e34b2ae8b92c09079,0xe4b0241e9a595845c960,0x76117258120f1d2ecc22,0xe34dbacab92c09071e99,0x241b9a6e9655c960483,0xd7258120b9d768bb2e4b,0xc3ae8b22c09055ebb465,0x1d2e65d7459160483c5c,0x58120d1f34ec3ac8b024,0xcaba2c09078798759574,0xe6a1655d160483a3ccba,0x20d1f350bb2e8b0241a9,0x22c0907a69b259584581,0xd656116048393ccbacac,0xcd348d12cab0241a9ee9,0x905e6bb46896558120d,0x59560483d34c3b44b2ac,0x4ed12cab0241d9a65da2,0x5e6bb76896558120dcd3,0x60482d3dda30eb2ac090,0xbacab0241e1e69d87595,0xbb465d6558120ecd764c,0x82d3ddc34eb2ac090567,0xcb02413ba6cba45d9604,0x61d7658120d1f30fd22e,0x34b2ac8b92e09058fbb4],#[0x241e3a619645c970483e,0x725c120b3d370b22e4b8,0xb308b92e090796965611,0xe5a6e1655c970482cf5d,0xc120ead372b2ae4b8241,0x8b22e09059ebb4619725,0x6197459170483e1cb2ae,0xd8f34eb2ac8b8241e2e,0x2e0906a79a8595645c12,0x865917048347cd42ecb2,0xf30cb2ae8b8241a3e69d,0x90787976595845c120f0,0x9570483e34bb344b2ae0,0x2d12cab8241b5a69da25,0xc69b25d9655c120ced35,0x482e3dda2ecb2ae0907,0x2cab8241e1e6a1765957,0xa7619655c120b4f768c3,0x34bcd434eb2ae0907879,0xb824169eed9a85957048,0x91765c1209bd365d22ec,0xdda30cbb2e09068f986e,0x4149fed99859554482c7,0x459120f07b0eb2ae8b22,0x340b2ac89058bdb85d97,0x8eed1a059564483734d1,0x120e0fb2ec3acab22417,0xb2ac890527db961d6559,0xdd985956448293fdc32e,0xb47f68d42cab224149fe,0xe890437fb56a58759120,0x65957448383ecc2ecb2a],#[0xf74cc2caba24161f6e17,0x437db6e95985d12086f,0x58448293edb72ab2b089,0xcbacac2241ada689a059,0x7fb569f9661120a4fb6d,0x48253eda74cc2aca9043,0x20b2a419dae919264165,0x76499059520ecd2ecc93,0x3b5d3b24c82ca9073698,0x2a41e1e61d7664165483,0xd9059520d8f74ebb320b,0xd1340bb2ca9071799761,0x139e6c3a45d965483734,0x59520d0fb0fd22ecb2a4,0xebb2ca904a7db8e9176,0xfedd985d965482c3fda3,0x20d4f760d42ecb2a4161,0x32ca904a7fb46a176595,0x1a76196548253edbf48c,0x4fb69d3b0cb2a4169eec,0xa904a7db6e9187595209,0x61d65482d3dd834cc3ac,0x6cd4b0eb2a412cfed1a9,0x4a7db6ea5875952094ff,0x705821bfdab49cb30e90,0x2ae4b82c133eed1a7589,0x9ba595725c160f8d364b,0x8363cd3b44b2ae0b06c7,0xcb82c171eec9a7595705,0x689655c96099f369d12e,0x36c3b44b2ae4b05e6bb0,0x2c1b1b69da259572583c],#[0x655c960f0df64c3acab9,0x834eb2ae4b0587fb461d,0x59eec1a959572582e3dd,0x9560ccf329d0324b2ac1,0xc92cab04e79b4e81925,0x6dfa06496558333ccbf4,0xacf760cbb24b2ac139e,0xacab05a7bb0689875956,0xa065d6558253eda744c3,0xd344d02cab92e139e6cb,0xb86579a9681655c970da,0x41655c3a3cbb324c82ca,0xfd1320b2ae1b1e5dba26,0xc7bb25d99059570caf32,0x55c2abdd932ec82cab85,0x2ecb2ae171eec1a25d96,0x975d9826016598fb69d1,0x6a3ed972ebb300b2f07f,0xa024119fed1a2e417659,0x194250120f75370bb284,0x4dbb0ca1280907ba9b56,0x41eea6c58750940483dd,0x250120f7536cc3a84a02,0x2ecb1280907769b56595,0xba6e57658940483f54da,0x120edd36acb2c4a0241d,0xb12809076e9b76596250,0xd1a758940483b74db32e,0xfb5368bb2e4a0241bea6,0x809075e9b95d97250120,0x75c940483af4dbb2cb92,0x36ccbae4a0241d7a6c59],#[0x7e69b25d96550120ebd,0x540483d3cdc2ecb2a809,0xc3acaa0241e9e6dd8659,0xa9a46897650120f4f36c,0x483b74cb344bb280906f,0xeca0241d7a65da25d940,0x26a17650120cfd352d12,0x5ddda350bb280906bebb,0x2416eeed1a561940483,0xd8650120b7d764d3b0ca,0xda342c3a80905bbbb469,0x16faec9a661d40482ddd,0x54120b77768d330ea024,0x8b12c0907b69b661152,0xa6dd8458960483d74dab,0x20f5d368c3ac4b0241eb,0x12c09076e9b465d62581,0x1765c960483b75da32eb,0xbd368cbae4b0241f3a6d,0x9075ebb465d7258120e,0x59160483d5cda30eb22c,0x68cbac8b0241dbaec997,0x6ee9b269d6458120ed77,0x60483e74d92ecba2c090,0xbae8b0241d7aec9975d1,0xbb56a17458120eb7768c,0x8357ddb350ba2c0906b7,0x8b0241e9e69d65611604,0x5d98458120f5d364bb30,0xbddab4ec22c09078f9a7,0x2416beed9a761160482d,0x6558120f4f368c3acab0],#[0xa32eb2ac0907679b465d,0xbba691a25d960483b3dd,0x8120bdd768d12ecb0241,0xebb2c09078f987691765,0xed5a461d60483c7cda30,0xb5f76cd230eb02416de,0xac09067e9a4e89975812,0xa465d60482bf4da744cb,0xd362c22e4b82415faec9,0x9079e9b6611725c120f3,0x9170483cf4da30cb92e0,0x4d3ac8b8241f3a6c9765,0x9fbb76a1645c120dbd36,0x483cdcda30cba2e0906,0xb08b824167eedda16117,0xb25d9845c120f4f34cb2,0x3c7cd32ecc22e09079e9,0xb824167eedda66117048,0x19655c120f8f368bb2ca,0x4d2344bb2e0907a79b46,0x4177aed1a25d9704836f,0x65c120f1f30cd22ecb82,0xb48c32e09078f9b46197,0xfeec1a961171482cfddb,0x120a7f760d4b0caa2414,0xba2c8907cb9b05d97459,0xdd865d164483c5edc2ec,0xf17b6cc3ae8b2241e2f6,0xc8907a3db461d6559120,0x75956448393edcb0eb2a,0xb70cbacab2241d9e6c19,0x727db76616559120e4f],#[0x96448393fdbb30b2ac89,0xd02ecb2241bba689a05d,0xbdb461d7659120bd7768,0x48387fdbb30bb2c89078,0xecb22416afed1a85d964,0x46a17659120d5f760d42,0xd5fda34ac32c8906abfb,0x22416beec1a761964482,0x18759120b57f68d3b0cb,0xd834cc3ac8906abda669,0x14feec1a961d64482d7d,0x59120a3ff6ed4b0eb224,0x52c3ac89063fbb06a587,0xfed9a961d644831bfdab,0x20c3ff6ed4b0eb22418b,0xbac89067e9a268197591,0x1a865d64482bddda340c,0x6ff6ad432eb22414efed,0x89052ffb66a19759120a,0x661644828ffdbb50cbac,0x60d3b30b22414feec1a5,0x537fb569d9859120a7f7,0x7448297fdb34ecc2c890,0xb2caba241f1e6c176595,0xdb4619655d120f0fb70b,0x83c3edbb0cb2ae8907a3,0xaba241c9f6e586595744,0x661655d120f0fb6cc3ac,0xf4d1340bb2e890727db6,0x24176eed1a05d9744836,0x765d120f17b68c32ecba,0xb330bb2e890717fb5661],#[0x66fed1a85d97448387fd,0xd120d3f760d42ecba241,0x8c32e89069bfb46a1765,0xec1a7619744834ded3b4,0xa7f760d4b0cba24167e,0x2e890537fb56a5865d12,0xa161d7448297fdb352c3,0xf760d330eba24166fed1,0x9059bfb4699875d120b3,0x61744829fdd8342cc2e8,0xad0b30ba2418dfe95a16,0x1ffb7685985d120a6ff6,0x44831bed374acc2e8905,0xb30ba2414df6dba56617,0xb6e95985d120c6fb63d2,0x29fdd834ccc2e890637d,0xba2414dfed5a66617448,0x5d9161120a3ff6ed3330,0xcd82ecb2b0890537fb56,0x41e1f65d7659584483d3,0x561120e4fb72bb2cac22,0xaecb2b08905a7db95d96,0x9fee5765958448393f5c,0x120e4fb2ecb2cac22416,0xcab08905a7fb76596561,0x89a05d9844831bedab4d,0xe1fb2ecb2ecc2241afa6,0x890537fb56a57661120,0x95d98448297fdb352bb3,0x760d4aecc224147fedda,0x52fdb6aa5766112097f,0x9844828fedbd52bb3089],#[0xd4aecc22410ff6eaa95d,0x7fb565d966112097f361,0x4825bedb74acbb089053,0xecb2a41f9a6c97664165,0x46817659520dcf348d02,0xc3ec3b48bb2ca905e7bb,0x2a41a9f6a1a45d965483,0x17659520f0fb68c3aecb,0xda350bb2ca905a7fba66,0x1a9f6d1a85d965482d3f,0x59520d4ff68d42ecb2a4,0x48c32ca906a7da769186,0xeec1a761965482d3fdbb,0x20b4ff68d3b0cb2a41e9,0x3aca906a7da669187595,0x1a661d65483d3dd834cc,0xfd748c9320bb24169fed,0xc9058ffb7691865d920c,0x61d76482cbfdab48c3ae,0x45d0330bb24163fed9a4,0x53f9b4e81985d920e7d7,0x764829fdd8348cc2ec90,0x2330bb2414dfed5a4661,0xfb7691985d920a5ff6cd,0x835f5d1740cbb0c9051f,0x2c3a412fe6d3a065d864,0xe959461d20a6ff6aca32,0xbedb74aca30e90637d96,0xa41afae8ba0659874825,0x625c16097f369d032cc3,0xa34eb12e0b06cf9b469d,0xb3e691a25d97058367dd],#[0x8960b9f768d12ecb82c1,0xeba2c4b078efb261d745,0x693a261d62583c5fda30,0xb5db69d130eb12c1abb,0xac4b05afbb0691875896,0x8759572582d77d9348c3,0xff68c3acab92c1e1f6d1,0xb05cfbb0691765c960f0,0x1d72582e77d9348bb2e4,0x9d130eb92c1a7b693a26,0x9fbb0691875c960b3db6,0x5582cf7d9348c3ae4b05,0x30eb2ac1e9eec1a261d6,0xa46898759560d4fb48d1,0x2d3fda344c3acab06a7f,0xb2ac169f6d3a261d6558,0x81925d960d4fb69d130e,0xcda740c92ecb066f994e,0xe12fe6d3a06498758277,0x659570f8f364bb320b2a,0x344bb2cab86c7da46897,0x7e653a0649765c2e3fda,0x1659bf369d0324bb2e19,0xc82ecb2f47f976897660,0xd3a26417659733fd2324,0xccfb68d1720bb2cb39f6,0x80907fa9b46897650120,0x761940483dddda350bb2,0x768d3b0ca0241efaec9a,0x7bebb26998750120f77,0x160483dddda34cc3a809,0xd12ecb0241ebe6e97661],#[0xe9b26917658120fdd368,0x483bf5d9348cbac0907e,0xecb8241e7e6e97661170,0x2691765c120fbd368d12,0xd5fda350bb2c8907de9b,0x2241ebeec1a761964483,0x98759120f57f68d3b0cb,0xda34cc3ac8907afbb069,0x1cfeec1a961d64483d5f,0x59120e77f68d4b0eb224,0x52c3ac890737fb56a587,0xa689a065d644838ffdbb,0x20efd764d032eb2241df,0xbac89077bbb468197591,0x1a865d644839fdd8350c,0x6ff6ad432eb2241cefed,0x89072ffb66a19759120e,0x661644838ffdbb50cbac,0x6ad3b30b2241cfeec1a7,0x72ffb669d9859120e6ff,0x74483cdfda350bb2e890,0x3b0cba241e7eec1a7619,0xbb06a5865d120f37f68d,0x839dfda352c32e89073f,0xcba241cdfed5a9619744,0x699875d120e5ff6cd4b0,0xdfda34cc3ae89079fbb0,0x241cfeec1a666174483c,0x985d120e6ff6ad3330ba,0xcaecb2b089071ffb7699,0xe9f6dd9659584483d3ed,0x1120f4fb6ccbacac2241],#[0xbb308907af996681766,0xec1a95d984483cfccbb4,0xe6ff6ad4aecc2241cfe,0x3089072ffb66a5766112,0xa95d9844838ffdbb52bb,0xff6ad4aecc2241afeec1,0x907e79b46817659520d6,0xd965483f3cd8348bb2ca,0x8d42ecb2a41e9f6e1a45,0xa7fb46a17659520f4fb6,0x5483d3edbb48c32ca907,0xb0cb2a41e9f6d1a76196,0xb66918759520f4ff68d3,0x3d3eda34cc3aca907a7d,0xbb241e9fed1a661d6548,0x51905d920efd348c9320,0xfda330ca2ec9077e9b26,0x41cfe693a0661764839d,0x85d920e7f749d0330bb2,0x348cc2ec9073fbb06919,0xdfed5a4661764839dfd2,0x920e5ff6cd2330bb241c,0xcc2ec9071ffb7691985d,0xc197651864839fdd8748,0xe77f68cbb28c3241cfee,0xc907beba2e819761920,0x65d864835fcd2740cbb,0x369d032ec3241afee93a,0x6bfbb0e919761920b7f,0x1874839fdd832cca30e9,0xd032cc3a41cefed19665,0xf9a4e819661d20f7d745],#[0x4835fdd2740cb30e906b,0x2cc3a416fe6d3a065987,0x4689765c160d7f761d23,0xd7dd8348c3ac4b07cf9b,0x92c1ebbec9a461d62583,0x1875c960f3f760d230eb,0xd2344c3acab079efb269,0x1e9f6d1a261d65583d3e,0x61d60f4ff68d130eb2ac,0x40c930eb073f994e8192,0xe693a0649875839fdca7,0x60d7f749d0324c3ac1af,0x930eb05bf9b4e819261d,0x994649875835fcca740c,0x7f761d2324c3ac1cfbec,0xeb06bbd94e919261d60d,0x5d9655c35fdd8349c930,0x48c9320bb2cbf1f6d1a2,0xee7da4689905d965ecfb,0x80002f3fda344c82ecb2,0x73805d004980330019,0x80e700cd80c000a08084,0x14881320121810800f7,0x81b00193817d01698159,0x223820d01f681da01c9,0x8285027482640250823a,0x2e382d302bf82ac0295,0x834503348327031082f7,0x3b5839f03888375035b,0x8429041283fc03dc83c6,0x49c848604758459043f,0x84fe04f084dd04cf84b6],#[0x56285490532851f0511,0x85d005b385a0058c8573,0x63d8621060a85f705e3,0x86ae069486810670865a,0x715870506f186e106ca,0x877d07698756073f8726,0x7de87d107c087a70790,0x884908328819080287f2,0x8b988ac088f8876085c,0x890908fb88f108e088d3,0x95289420934892a091c,0x89b7099d898a097f8969,0xa2a8a1409f489e109c4,0x8a800a6c8a590a488a3b,0xb088aef0acf8ab00a99,0x8b640b568b490b388b22,0xbbf8baf0b9e8b8e0b7d,0x8c0f0c018beb0bd78bcd,0xc6a8c5d0c4f8c360c22,0x8ccf0cc48cae0c9d8c84,0xd3f8d2c0d188d020cdf,0x8d920d818d710d638d56,0xdd28dc50dba8dad0d9c,0x8e400e238e0d0dea8ddd,0xe988e820e6b8e610e56,0x8eeb0ee08ed30ebf8eac,0xf3d8f2d0f1c8f0c0efb,0x8f8d0f798f6c0f5b8f4e,0xfe88fd20fbb8fae0f9a,0x902c101e901110038ff6,0x108a907a1063904a103c,0x90cb10c090b610a59098],#[0x111d911010f690e310d8,0x918e11749155113b912b,0x120d91f111da91c111a7,0x9290127992601243922d,0x131592f912e292c912ac,0x938f1375935613459332,0x141493fe13e193c813a8,0x948214659452143e9428,0x151694fa14da94be149e,0x9587156d955d15409527,0x15f795e415ca95ae159a,0x9656163c96261612960b,0x16b7969e16879677166c,0x9734171796fe16e796ce,0x179597821768974f173e,0x9821180797ee17ce97b2,0x189a9881186798511834,0x991a18fd98de18c498b4,0x198a997a1966994a1930,0x9a0d19f399da19bd99a1,0x1a929a6a1a4d9a341a23,0x9b001aec9ad31abf9aa6,0x1b649b541b409b271b13,0x9bd81bc19bab1b9a9b7b,0x1c429c261c129c051beb,0x9ca41c8d9c7d1c6c9c59,0x1d1d9cfe1ce49cd11cba,0x9d941d869d671d569d3d,0x1e0d9e031de69dd31db9,0x9e841e619e481e349e21,0x1ed99ec91eb89ea81e94,0x9f5f1f399f201f099eea],#[0x1fae9f981f879f801f75,0xa037201da0071fed9fc8,0x209ea0942080a06d204d,0xa13f2116a0f720daa0c4,0x2194a181216da15a214f,0xa1fc21e5a1d221c4a1a8,0x2281a2622245a22f2212,0xa2fe22dba2bc22a2a298,0x2374a35b2341a32e231d,0xa3d023c5a3b22398a385,0x2431a424240aa3f423e0,0xa496247ca4662455a43f,0x24fda4de24c7a4b724a3,0xa5592545a5322524a50e,0x25c9a5ad2593a5802569,0xa625260ea5fe25eda5dd,0x26a1a6882668a6522638,0xa7182704a6f126daa6be,0x2791a77e2767a7452731,0xa7fc27e2a7c927b2a7a5,0x2803a8022800a7ff27fd,0xa80b2809a8082806a805,0x2812a811280fa80e280c,0xa81a2818a8172815a814,0x2821a820281ea81d281b,0xa8292827a8262824a823,0x2830a82f282da82c282a,0xa8382836a8352833a832,0x283fa83e283ca83b2839,0xa8472845a8442842a841,0x284ea84d284ba84a2848,0xa8562854a8532851a850],#[0x285da85c285aa8592857,0xa8652863a8622860a85f,0x286ca86b2869a8682866,0xa8742872a871286fa86e,0x287ba87a2878a8772875,0xa8832881a880287ea87d,0x288aa8892887a8862884,0xa8922890a88f288da88c,0x2899a8982896a8952893,0xa8a1289fa89e289ca89b,0x204839a228a5a8a428a2,0x68838e39dc15f88c1403,0xc065482a77e1704812aa,0xdf85c1e03204a39a1c08,0x2f050e3c0aee346c2039,0x15b8bc1438db8f1f054e,0xaf052e36e3c5412032c,0xc15c14788c1239a26e2c,0x122e68a04404304239d,0x10ae76e1b055e210eb05,0x308c15c14b9a0441010c,0xe049e1f057052e2ee3ee,0x5032c15c1439ab8f140a,0xb9a200eb057050e3ee68,0x4604503a032c15c14b8f,0xa1f0570500aee35e3c50,0x4148124a1c1591b78fb9,0x9a140540500c9e3ee685,0x9de346015014b8f03a7,0x38d58f1e62f04a85263c,0x363c9815517c12a1458b,0x46d45e05704b62f63285],#[0x61498b91738d98f200d8,0xa63c292e345033219c12,0x298b98fa1478d27a1704,0x3de34781811781651bc1,0x401c29245f04a62e8526,0x7219c12517d8bd8cd8f0,0xea46d04a852271e3e668,0x9c11bc12a1478f99a1c0,0x10d46c12166aa8460468,0x51ba14c1238f59a17048,0x9a1546c0cf04966ae3c5,0x85366872a103aa1438fd,0x291811848146f048e3e,0xae3c601b38b61438f98d,0xa04a140a7a16e2ee3304,0x2b852668641229861499,0x1b04899a2012246de201,0x850704ac1299de8561e9,0x1011846f048e3c12a66b,0xf852668591b61499a043,0x491b38f99a1e46c0e8e3,0x6ee3e668803c21ec1261,0x8f1811c0f00cf04ba164,0x668702951778ba1498d7,0x1e06504948246e271e3e,0x1b819520c12a1478f99a,0xa1c06c0480cde3e66851,0x12021e51bc1238fa14d9,0xde1a286482853049e68a,0xf8a179a1c11010c1000f,0x6b8507032619412a1498,0x201c111480e77048128e],#[0x804a04898f032e1439ad,0x6704ae19850120e6b480,0x9dc1261404ab9a240cc8,0x850e685040b86044520b,0x98f92039a1e4800ca63f,0xe482e688033219c12614,0xa2011c0f00cf04ba1663,0xa1961481291b58f4a1b9,0x2f1806e63c0f1e68441e,0x108419d98b98f98ce140,0xa1259a04b1985284b668,0x684b6682e04419d86214,0xb99df0304ae1499a1ba1,0xc812bc0e63f852668704,0x9d048a1299a6a1201180,0x8500ca668581904a91b9,0x91b58f4a199a20129e23,0xf23ee34641e819614a12,0xdc8f0ab1b05f0580b722,0x5723de349c17c12c8b38,0xb05d05a04927685322e4,0x6c120a4c8b515c8fb8d1,0x1b04aa2ea3d6340a6a60,0xc7c12a8bb85a8f58d029,0x67246c0b785ba2e637a3,0x61649d68ba1458d68f24,0xe455637a3c902d815812,0xf1d06585a0b527604ba2,0x29a16c12e8b51598de8,0x9a1b06f0640b6e3f2685,0x268803ac1bc19b8538fc,0x8c07906706f048e3ee17],#[0x2dc1bc19b85b8fc9a240,0x455e3f268703e03c03a0,0xc9a78f1506604928f06e,0x40eae3f268601b01902d,0x2515b8fc9a1406c065e1,0x7286704963ea685c1bc1,0x1e219c1258fa9ca9a20a,0xa7163f04aa6870235200,0xe1998fe9a1811c28e864,0x412a685a6861a192002d,0x4048d2069a1b04810186,0xb685163da68704a619a1,0x8f915e9a2204928d8660,0x120541e619a148124a35,0xa9a04010a7504a866a68,0x428d85263ea686a19520,0x9c1298f515e9a1404a86,0x7b066271848e3f2687a1,0x1989c38fe12c9a200e88,0xe3e84b26870231a101e4,0x5a1a9a1828c87b065270,0x784aa68804ba1961204a,0xa2012c08c06412863d68,0x4ea9d04ba1904a048a9,0x7617c0d0b663ea689d88,0xda9a04b100f80f00ea86,0x8e120e3f456a68804829,0x88a9a0481086412c128a,0x662849e1726810850197,0x7726812c4036c9a04b0d,0x8621ea12c9a04b1812a2,0xb0e84963f2681004419d],#[0x65e172681284036c9a04,0x4721ec1949dc9a048140,0x27406584be1412b26811,0x45598785a1ee12c9a1f,0x8fc9a1ae23268120304b,0x63f2688023c19612a14d,0x100b507b06428fc0e851,0x8e70e68949c98f03ac9a,0x110104100e7708307b04,0xc20c1e032c8f39c39a18,0x7082e3b07ae1723ee68a,0x804a79a1c0d00cc0c80b,0xb5e685c20786b85c1e04,0x1e044b9a1008007b23c0,0x9708304ae681045c20c,0x2001e785c8f032b9a18,0x228410467012f8496686,0xb41919c612a8f8a159a2,0x3c67012e66b848703251,0x3048e1e99a2811c28ca,0xa03403303298ea8fd85f,0x7a63b617c0d0b6a3e668,0x8fa1299a200d00cc0ca8,0x28480a319c91b8194a16,0xc8c6c866e19848128e6b,0x4b39d2a304ad1539a1c0,0x87a45e84966812c5c2d0,0x682ac461ea12d9a04010,0x1e0a304a99a23a2284b6,0x84a668504661299df85a,0x61299a04415e1428c12f,0x1e178780ca6685d86208],#[0x481961e48f99a0481412,0x59a0440fc0e87b6684ac,0xd46d84b23e853668602f,0x90a351ba14c8f59a1c08,0x1928723c0ca668402d41,0x86e85f03f01c8bc8f58d,0xa20132a7412e271c4aa6,0x328a1f03f0198f89ca9,0x4c13270c4b268310403a,0xa86c4b268849cb12c9a0,0xc9a2028c13127327412c,0x4ec8ee85f03f0198f848,0xa1c077c0fc0726811c50,0xc8ee85f03f01a2d58fc9,0x85d88e9a16c4b2681103,0xc06675122668bf03f01e,0x77a1413813012c12bc0f,0x8ff03f0104aaa199a1c0,0xc04093a17a2366860328,0xf03f01e85e8879a1bc0f,0x7c0fc0662e63e6307024,0x404819dd9a0c411637a1,0xf01d9a1563a63d6688b4,0xf23ea340bc5e85f03b88,0x3105912e9a0c40d26322,0xe9a0c41285f05a449a68,0x4c1244ba68310304a89d,0x44aa68130304a89da9a0,0x7b268b04a49de9a44113,0x412b27411b23fe14c4a4,0x551e712c9a1c11506e06,0x78923268904ba98045b8],#[0xc13012c28f275482e154,0x6045c9db85d88248c9a1,0xc9a0440d273268128304,0x412b23fe172681187b12,0xd785d88248c9a1c0cb27,0x76e140cb2686f03f01c9,0x85032c9a04619e221232,0xe16a3c0cb268604ac9df,0x69db8569a13a114b7239,0x8802be9a1411aa681283,0xc076200ada685f03f01d,0xf03f01c8f02b69a17c0f,0x1a16e17c0fc07a236685,0xc6812c5c1991ba8f614d,0xa19b1a04011078c76866,0x265d87ae0f4681005d83,0x84b468621288fd1a0481,0xd1a04b1008f06547323e,0x8878a8346812c6a83519,0x7d192a0d1a1401108f61,0x8ca83477e1412b468114,0x45598aa0a1ed1a6951c0,0x12a21467468120404b0,0xdb8681084e83e88d1a04,0x4101595e1a04211e140,0x3e1a04015e200db86810,0xee238681004101788d8,0x19c8ff85045e1a046236,0xe0f620923868704ae1d4,0xd88e1a04014117c07876,0x188287b6681104101783,0xa681105e83a1e0abd9a1],#[0x3569a04c0ea5d47ae0d,0x23a9a04c1147ba683043,0xa0461a47ba68304389d2,0x6ac48851ec9df8504ac9,0x13011c08ea5f4794872,0x4681104d83035b1a0441,0x785d81e1a04614221a4b,0x80cb056e3f052e68801d,0xcc1478f032281181140e,0xc1581203603502f78b78,0x81140e80cb051e3ee688,0xa3a278bc1479a2305411,0x3f051e688c1503b03902,0x40230541181140c80eae,0xc1203558b51758fb8d0,0x7246d85304ae3e668703,0x33614c12b8f99a2411c2,0x46de3ca04704503c91b0,0x480dc0d40c1e2c0cde32,0x3c78f91b99a0331c1030,0x852e3d46d6689c120470,0xd9a2011e87b0480cc0f2,0x47c1204603e034b8f614,0x28648185263f04ae6870,0x3c98f614c12b9a2411c,0xd482e689047045033920,0x11e8670480f00ce85163,0x2c0391a278bc1279a20,0xc0f263f049e68792003d,0x232099ae142648011c0c,0x50904604a1a399d11b61,0x40ca677c0c12868e66b8],#[0x603258f99ae141811811,0x180cb851668128504a04,0x9c91b614d8fa12d9a281,0x63d66880470464a19204,0x210cc08106446e849853,0x1e01b120a1258f614d9a,0x84ba1763e483668a43c4,0x452011c1150f246d0ce,0x4603a032f82d8fe85f80,0xcbe0a0e9a17e0363c90,0xb8f685b8c1c11761fc0e,0x7e00114683582ff82c12,0x5f80b8f1fe0ae3c0cba1,0x16e68604583af82c1968,0x800451a0e60ab07ae2da,0xe0363c9f8203ad8fe85f,0x1707a0cb04be0ae1da17,0xabc8b02dc8f78dc8c241,0xb5e3f234a0340330320,0x6f0640c40c00bde31e2c,0x1903a04e02d78fc9a270,0xeae3f268a03e03cc1bc,0xf80f306f0640b4139e14,0x33045b8f785c1bc9a240,0x457268114504703cc120,0x98f29cc12a9a20066e3d,0x704ba6898200470a3a19,0x11c0ce4800f011663de1,0x68801e98f515e9a04514,0xb0640b41380f1272e3f2,0x9612b8f515c9a045180e,0x65272e3f84b268114601],#[0x3404789cb8f612c9a240,0x61584aa68803e8a3c190,0x451828c86e86411a63f,0x8114601e61298f515e9a,0xa04e0807868663f84ba6,0xf00e80b763da681386e9,0x4e43c43a788a9a0481c0,0x86f052e3ea68a8c8a190,0x38f42da9a1d0b6865048,0x3a6812032a304e03c03a,0x703c03ab8f69a04e16e2,0x641388f08b5e17268128,0x3304598f785c9ae12230,0xe1784b268114704704b0,0xd8fc9aa122006566012d,0x8118781b047c1904649c,0xa2006f06684b63d85326,0x41ec190a358f89c612c9,0x8b5e1663c0eb2689420,0x5e9a04a0c13b0640f80f,0x200f00b763da681385b8,0x33b82782d8f315f80045,0xe0b63ec0fe00114843c4,0xd8f612e9a190f10cde17,0x9e2d289e68983c833b85,0xa240b30800b80aa85307,0x3403303278e02dc8f79,0x9e140cb23ee68ac20c1e,0xc230830780d00cc0b6e3,0xa3a1e046a8f61299a99,0xc0fa672a3d84b6688020,0x383268fd9a180d228c11],#[0xcf23d286e689d8e82d83,0x9a1c0d2c6ee380c80b40,0x802c02ac14c12b8b2a2b,0x100cc0c8137878e68120,0x20a8fc142a3b9a200d1e,0xa3ce690b4842da1e4122,0xb9a140d0a8ce380cc0ca,0x666b8488b8e83383268f,0xf2867011f61812c28ca8,0x4803304d78503299ac8,0xd67284b6689034e1e784,0x61d28608307811c11b23,0x20c1ea12c8f614d9a04,0xd06428f23d84966a2848,0xd78503299ac8f2467106,0x3f6686c1e03403398e22,0x8be9a1763a0b60cee15a,0xa17637a3c7514512e88e,0x712a9a240fd467a2d44b,0xa101e0a321904589c98f,0xe80ca63dc4a286a6898,0x58fa9a4a120118116270,0x1a68803aa1ba19032b12,0xca4824780eac4a63d27,0x23e23c22d49cc9a14a1c,0x263f239273268528504e,0x604b047033aa1c9a7122,0x3a27263dc4b26898a3d8,0x8fc9a3413a28ea841132,0xd04d048e85f03f01c8e5,0x3c134604e834833832a2,0x9cc9a200d00cc0cb2696],#[0x641b819046045d8f312c,0x2006527363ec4b268114,0x3e03c04eb1249c98fc9a,0xd20ce0c963f268603a0,0xf03f01d8f49cc9a1b23a,0x80cb63fa1411b2686832,0x3f01832d8f685c9a200e,0xd5a16e3ee306046045f0,0x85032c9a04616e2e0da0,0x6f065a16e3f2687b8fe,0x4e29cd8f69a28118117,0x8583e83c43282df03f01,0xd8f1c11aa7363ea684e,0x34751e512f82e85e87f8,0x9483a38a0947ba1563fa,0x8e8ee85f03f82d8fe8d1,0x23a17c0fc07621e1ba68,0x4668e04ed8f69a101391,0xa27a17c0fc0563fa3ba3,0x434833047e85d8f312e9,0x527363ec4ba68743e83c,0xff03f01e9a1811c11528,0x70112c4ba6854a149cd8,0xa349cd8f69a04e1728f2,0x63fa39287c0fc07a6874,0xe8db8b048b8fb8c1d28d,0xd0cbe0ae3fa347433432,0x2048b88e9a190b41350c,0x3ae3da681388c34c33c3,0x9a712281350d10cd0c9a,0xd019d8604a0450a3aa19,0x8e23dc4a66aa84a04b89],#[0xa1201181162741280c82,0x604d03403304813299a6,0x2b6181284ca669a845d8,0x1903f98eb12c8f6a199a,0xa85668128404e04d91b9,0x84b04e84ac8f59a300ca,0x85f03f0184859d58e84c,0x11811723cc4b2876688e,0xc8fb12045d9a19082078,0xac4b23d286668901e4a1,0xa04e0c0b66380d00cc0c,0xf00eb23d6681386206d9,0x3c8ff014a1d9a180f80,0xcb23c11ba17668683af,0xf0183ac8f685d9a200e8,0x5a3ca87668b046045f03,0xd20ce0b76380cbc0fc0,0x46a8f132aa1d9a150ea,0x544be09467a17e03a3c6,0x1385d1bd1903fd9aaa11,0x685b9a1546d467a3d668,0x723c0eae68583b839b8b,0x2c8f685f80b872811ba1,0x687046045c20390c1ef8,0x1390b50f10e8a8ae2ee,0xde85f03f0138baa2b9a2,0xfc05e184fee68cc3cc2,0x49030fb0f30b70eba23c,0xe43c43a2a2b8bb9a1c90,0x79a08e74139e68304e43,0xfa17c0fc05a89e68504e,0x5f03f01e8838602479a1],#[0xf10ebe0ae1fe03a3c8e8,0x178613fb9a310b41390,0xc3ec3cc2dc3ae88f03f,0xf10e8e09a3ee34824124,0x8b9a2d9a1ee381390f90,0x66868c8a3ce85f03f015,0x1d8b412e67446412b856,0xa304e23e23c23a99a448,0xa17c0fc058b663e668a1,0x99a4481813a6740e263b,0xe6698b4604d1a398e98f,0x399a4480d09068e67663,0xc813a639e20122668c1a,0xc1358f98f18ea0d20ce0,0x403303284858f99a04d1,0x17c0fc0409163ee34903,0x14d8fd9a2812563162fa,0x91e51b919212023615a,0x3ba17c0fc0563e668d52,0x90f10ea0d20ce0ca6381,0x3e85f03f01038d9a150f,0xf0158fd9a1b63d668138,0xb61fe0363c6d8ee85f03,0x3f01d8f59a1985184be0,0xfc0563f668658ee85f0,0x8e002d8fd8d2413ba17c,0x6684024e85f03f01010d,0x48b88d9a1985184b63f,0x384a63de687c34c33c32,0x2a9a04c1c0fd68f85785,0x6ac48989d12021bc1651,0x206411f27412c1156872],#[0xd04b785b12c9a0451d27,0x8e270687269c489019c9,0x9a9a12813012d077a182,0x222bc9d89c045c8f712c,0xf84f1e17268128704643,0xc822fc9a0440ccb41384,0xc8891e17276c4b26a28,0xf03f01c8f785c9a2b622,0x9e14b04e93a83204ac8e,0x4ea0cb277c0fc0723f26,0xb85c9a68f281181164e8,0x4d53a83483392dc8e032,0x2180d00cf269a3c13450,0xc8804613af85a8fc9a03,0x811489f275e16a3f26a0,0x292d04eb8569a04a2011,0xcbe16a68128593e93c43,0x45832785a9a84a181180,0x44ba3de17a6811480460,0xb8568fc9a1a88286c456,0x6e1412ba683c8e834833,0xa68603e03cc8f69a04e1,0x461c1181140e80cba3f,0x4883a832e8ff82785f80,0xcbc0fa1fe0ba3fe02e1,0x384c32b8504ae9a110e9,0x1b85e8d1d0cba3da681,0x63fa68543a68fe8ef03f,0x785f800461c1181140cb,0x728b6688a19d8fa12f82,0xa128f28b562fc07c0ee1,0x79671e686632d8504a79],#[0x3ae8fd9a178800fea3f8,0xe0ba3fe0011870460450,0x785c19d1a2a87a849e17,0x23a1e04603403e91ba8f,0xa1c08ea3d85346811858,0x47046c8f51cc1991bd1,0x1a0451b23d8534681184,0x868114602361b98f495e,0xe1a0451408c68663d257,0xea0f8681147433d8f295,0x3e1a0471811d0cde1763,0x15a0f8688419045d8fe8,0xa02411f08e0cf06763ee,0x304b04591988f785d1aa,0x6012f469a54114682303,0x19612c8fd1a0471408d6,0xa1528323f46746811c55,0x68114743cc8f295045f1,0x1a1811d0f1e1723ea0fc,0xc68841ec8f045e83047f,0x1f08e0f307b23ee15a0f,0x45032f85c8f046e1a1c1,0xc0723de16e0f868a13a0,0x45214f24e90ce0c8117,0x3a83251e698c8f395e1a,0xcb876e0f47b869e1499,0xb83e1a0452411b08c89e,0x47047433227297c8f785,0x4788ff876e0de1786811,0x61ca19e8f314e1a0461b,0x10d1e17a3e8678681186,0xfa19190f82785f800462],#[0x8fa1a47aa681306a1ee8,0x46521920f01c9a2c4808,0x704c49c89bc1dc0f0470,0x63a1b074131c53268118,0x21a1ee0f314e9a04618a,0xf9e1783e87811ba6866,0x681147123435d1a04c11,0x452127a86ea83874e578,0x8433124e1d594b83e1a0,0xff875e176078681188e8,0x2a8011c4]]
set_option maxRecDepth 16000 in
def g255H9 := limbs80 #[#[0x202042440400240107,0x2010102000020032,0x3000000000100160020,0x58000010220000008002,0x10080000012082006006,0xa03c000000034808,0x1e00000000000038278,0x2,0x3199c,0x888c,0x38018,0x0,0x42c4000000000000,0x18804000000000000,0x381280000,0x0,0x0,0xd0640000000000000000,0xc2180000000342900000,0x809000000000d0df,0x0,0x188200000,0x3000c000011340000,0xd158,0x0,0x0,0x0,0x0,0x10740000000202d80000,0x3133c000000000001,0x182af12c800000000,0x198000000000000],#[0x109cc000000000000,0x41440000000000000000,0x1c0d000740003,0x424000000000000,0x382a0c20c0000,0x293280000,0xd04800000003d8040000,0xa1c2a14c0000c299,0x0,0x241b40002c0e60158,0x0,0x0,0xc4440000,0x31824000000000000,0x1928c00000000,0x35aa801d1500c0000,0x886400a4000000000000,0x1,0x2020000000000,0x0,0x8580000000148380000,0x3,0x4114000000000002830c,0x382e4,0x2c2340000000090d0,0x0,0x1199548a9e2dce334,0x0,0x0,0x0,0x0,0x8f00000000000000000],#[0x3842b,0x1516400000000,0xc2a800000001d0680000,0x1e33c000000000002,0xc3ec00000000,0x0,0x82c00000,0x38030000000000000,0xc35c0000000000000000,0xc0fc0000000000000003,0x2c26000004269a14a,0x23580000000000000000,0xa049c138839400000002,0xc9244a1c0274,0x34060,0x1a3100000000101d8,0x0,0x4300000221f800000000,0x3d10400000003,0x383f8,0x0,0x432c0000,0x0,0x1034400000000,0x361d40000,0x180e8000000000000,0x193d400000002d128,0x1040002c24e42f8,0x1803400000000,0x0,0x804400000003d3ec0000,0xd960000000100002],#[0x29190,0x0,0x81000000,0x0,0x17800000003c91d9144,0x152d400000003,0x2808b0288,0x0,0x98080000000000000000,0x2531c0002,0xd2240001018000000000,0x3a3600001,0xc09400000000000258a4,0x108b0000000000003,0x201a5003a80cc0000,0x0,0x92cc,0x0,0x2c25000000000,0x0,0x0,0x0,0x2a11800000000,0x40ac0000000000000000,0xc3640001,0x1d16c,0x0,0x0,0x51100000000000004338,0x0,0x0,0x3482c000218346044],#[0x634bc0a8000000000000,0x0,0x3ac0000000391178000,0x3c1ffd8b111c85043,0x0,0x2d340000081100000,0x0,0x183dc833c0000,0x392b992500000,0x48c800000000,0x838c0000000313240000,0x3d81c000000000000,0x0,0x3c3a00000,0x11380000000000000000,0x40f400000000,0x183c541880000,0x0,0x113c0000000000000000,0x3d3f0000000000001,0x0,0x0,0x0,0x0,0x0,0x80640000,0x2401c000000000000,0x416000000000,0x43a40000000140700000,0x1,0x208940000,0x0],#[0x3807c000150200000,0x0,0xc1e8,0x0,0x0,0xde81b80002413d88b8,0x1044000000003,0x0,0x0,0x82840000000000000000,0xc0540000000000000000,0xc38000000000,0x90a000000000,0x198c000000a1303c8,0x1c8ac00000000,0x240e0,0x30c2c,0x191f800000000,0x0,0xd89400000000000082e0,0x0,0x0,0x218aee2d8,0x0,0x242b000000000,0xc1a000000002822c0000,0x58b84174000000000001,0x0,0x0,0x380980000,0x0,0x1881400000000],#[0x0,0xd1b00000000000000000,0x0,0x0,0x0,0x83e8087c000000000000,0xc42c0000000300f00002,0x15070039a,0x1027c00038184,0x200000000000000000,0x2d3840002823a,0x8e12ec0000,0x39370,0x0,0xc03c0000,0x0,0x0,0x0,0xc05180480000c1240000,0x1,0x0,0x2009c000000000000,0x0,0xd98010d400000002828c,0x303200002,0x29378000000000000,0x0,0x0,0x0,0x0,0x0,0x102c0000000000000000],#[0xc43c0000000000000001,0x2,0x2441c,0x3815501c5429c,0x0,0x0,0x0,0x41480000000000000000,0x11700000000000000002,0x206,0x148264164,0x0,0xca200002a05000000304,0x3,0x0,0x9814000000000001232c,0x3802c00000002,0x0,0x19c00000000,0x249100000,0x201ec00000000,0x0,0xb0,0x2434c000000000000,0x21088000000000000,0x0,0x1c2fc000000000000,0x0,0x0,0x0,0xe1780000000000000000,0x12c0000000088a7],#[0xc2100003419000000000,0x3,0x353bc,0x382ec000283d40000,0x2ca14,0x182a9900000000000000,0x202d400000000,0x0,0x4ad000000000,0x2c8,0x0,0x2031400000000,0x0,0x9480000000000000000,0x1083d81ab040d,0x83280000000000000000,0x3,0x431f12940003c2280000,0x2d1c000004835d30b,0x0,0x0,0x0,0x218c4000000000000,0x0,0x49080000000000000000,0x2c8e4000182cc0001,0x411a423c0000,0x0,0x39904000000000000,0x194000200a00002a1a4,0x1,0x3d99800000000],#[0x0,0x2c16c000000000000,0x3c2bc00000000,0x0,0x2010c000012dc,0x83400000000000000000,0x3c80c000199cb,0x30240000103e0,0x42b80000,0x0,0x3187c,0x0,0x3c084,0x0,0xc14c0000000000000000,0x241af02440000,0x0,0x0,0x324000000000000,0x0,0x51400000000000000000,0x53580000d02400000003,0x0,0x4150be02480003c2a4,0x1,0x3d310000103b80000,0x0,0x0,0xc3a80000c3f0,0x11168000000000000,0x18a28,0x2c26c00000000],#[0xc8c00002d98698a00000,0x3,0x2c2f000016150,0x191d4000000000000,0x193d0c8f4,0x13740000000201bc0000,0x312c40000844f,0x2439000008140,0x81c0000000000000000,0x3d8300002,0xc0c8000188e800000000,0x1,0xd24800000001c18c0000,0x0,0x1c84000000000,0x340b40000,0xf80001d018,0x38068000000000000,0x241f8,0x2c4340000,0x0,0x0,0xd80c000000000000,0x0,0x0,0x43fc000000000000,0x201f000000000,0x1581800000000,0x0,0x0,0x0,0xd1e80000000000000000],#[0x90c9,0x1d89c000200bc,0x8c18,0xa0f40000000000000000,0x84180000000213f6,0x4410d8200000,0xd38800024c4400030220,0x3,0x0,0xc8b40003613800021054,0x40d40001c1b293480000,0x3c1300002,0xc3c000000000,0x3c8180000,0x2e017221e03f4,0x2411c0000,0x0,0x42e8000000000003114c,0x2c25c000000000003,0x3a11400000000,0x83719212c2b40000,0x0,0x0,0x0,0x0,0x43780000000000000000,0x4f,0x0,0x0,0x0,0x380580000,0x398b400004350],#[0x0,0x40d8000000000003c270,0x211f7c416,0x301e40000,0x0,0x3d03c0000,0x1a8140003d3c00000,0x0,0x0,0x2c170,0x2889c00000000,0x0,0x2d334593400000000,0x12900000000000000000,0x2,0x351540000,0x0,0x0,0x28208,0x21148000000000000,0x20448,0x0,0xc3340002d03000000000,0x110d8000000000002,0x0,0x293540000,0x400691e00000815c0000,0x2190000000000002,0xc3680000000000000000,0x2,0x0,0x300bae2d400000000],#[0x190c00000000112d8,0x0,0x3d892ac00000000005c,0x14122,0x14404,0x1836c0000,0x0,0x28a70,0xc40000000000000000,0x48c40000000000000002,0x18330000000034264,0x103b0000000000000,0x0,0x151b40000c8480000,0x0,0x0,0x0,0x381c000c3c2940000,0x2095400000000,0x0,0x0,0x3c384,0x0,0x0,0x0,0x0,0x4256c308000000000000,0x417f,0x0,0x54040001936000000000,0x0,0x63400001635400000000],#[0x0,0x2d21c00000000,0x122bb52c0,0x0,0xc2dc0000,0x0,0x93a00000000208900000,0x90ad8362,0x0,0x241340000,0x0,0xd8ab1868000000000000,0x81dc000000000002,0x44380000000000000000,0x2f40000000000000002,0x2,0x0,0x0,0x0,0x8014000000000000c8a0,0x406c0000,0x53000001200c00000000,0x12f9035800000002903a,0x696400000001,0x0,0x8310000000000003532c,0x3492c00000000,0x11940000000000000450,0x2d15c8828d892,0x0,0x0,0x0],#[0x901c000000000000,0x5364,0x40240000000241d40000,0x50c5d889,0x42800001443000028408,0x2,0x201680000,0x0,0x11780000000000000000,0x421c0003c1c800000002,0xd1a40001,0x0,0x283d2d01400000000,0x831be80f483000000000,0x377025843be,0x0,0x800002842000024224,0x3,0x6aafa04282d000000000,0x2,0x0,0x383cc0000,0x3d83800000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc078000000028898439c,0x10cf19400003490f],#[0x993c0000000000000000,0x2,0x53dc0000000000000000,0xc0080000000003548214,0x1922c0002,0xc1500000000000000000,0x0,0x0,0x0,0x50780000000000000000,0xa80010b434800000001,0x1,0x21e0000000000002c230,0x2,0x0,0x3d034c38800000000,0x2622800000000,0x508d0028d82c000001f4,0x1d322,0x158980000,0x37c0000,0x0,0x0,0x0,0x13a400000000,0x15028,0x0,0x0,0x1d88c000000000000,0x0,0x201cf83e400000000,0x0],#[0x0,0x0,0x151b8,0x0,0x1509c00000001c0ec,0x304000000,0x83b4]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0x4250120fe25cd4250120,0xfca5954250120fe29cd,0x54250120fca995425012,0x20eea6194250120eea61,0x515250120eea61d42501,0x120dda6555250120fca5,0x5956250120faa5916250,0x120dba6596250120f9a,0xa65d7250120f6a5d1725,0x54120e9e6196550120d7,0xda6595254120eda61152,0x254120f9a5956254120d,0xeba6116258120dba6596,0x6258120eba61d6258120,0xf9a5957258120dba65d,0xd7258120f3a5d9725812,0x20e9e5958458120d7a65,0x1d6558120f9a68965581,0x120d9e65d6558120e9e6,0x611725c120e3e61d7658,0xc120f5a595725c120e7a,0xe5d9655c120e7a619725,0x5c120e9e619655c120f1,0x9f6616559120e3e61976,0x5595208dfe95985d120c,0xdda6499059520a9fe998,0x7659520e1f61d7659520,0xa9fe918659520a9f6a1,0x9625c160a9fe9d865952,0x60b3e69d625c160f3a5c,0x9d655c160f1e595725c1,0x960b3ee89765c160f1e6],#[0xe819259560e1f61d655c,0x9560a9fe898759560b9e,0xe5d99059570b9ee81975,0x59570d5e65d9059570f1,0x1fe5d7660165b1fe8976,0x25c11099f68b905d965d,0xb7e69d425c110f7a5c94,0x9261d10f6b5d17250910,0xfea50971501208ff693,0x94250120fea595425012,0x20fea5915250120fea5d,0x595250120fda59552501,0x120bfa6995250120dfa6,0x5956250120fea5d16250,0x120dfa6556250120fba,0xa61d6250120fba5d9625,0x50120dfa65d6250120ef,0xda5957250120bfa69d62,0x250120f7a5d97250120f,0xdfa6597250120efa6197,0x6550120ede6156550120,0xafe6a16550120ebe619,0x96550120fda689655012,0x20ede61d6550120f9e5d,0x998550120ede6a165501,0x120ebe6197650120afee,0x6a17650120e7e61d7650,0x120afee958650120afe,0xee9d8650120cfe65d865,0x54120afee998750120af,0xda5516254120fda59152,0x254120fba5916254120f],#[0xdde6595454120efa6116,0x6454120bde6995454120,0xdbe6596454120f9e595,0x98454120ede595845412,0x209fee919654120cfe65,0xd16258120fba55162581,0x120fba5917258120fba5,0x6117258120f7a5d17258,0x8120f9e5955458120efa,0xe5d16458120bbe699545,0x58120ebe61d6458120fa,0xbe69d6458120dbe65d64,0x458120f9e5957458120b,0xe7e61d7458120f3e5d97,0x7458120d7e65d7458120,0xebe5958458120afe6a1,0xd8458120ebe5d9845812,0x20afee9d8458120cfe65,0x9d6558120f9e69165581,0x120fba6897658120f9e6,0xe918758120bbee917658,0x8120dfae899758120afe,0xa591725c1209fee91975,0x5c120f6e5d1645c120f7,0x3e5d9645c120f9e59564,0x45c120ebe619645c120f,0xafe6a1645c120b7e69d6,0x745c120f5e595745c120,0xede595845c120e7e619,0x9845c120e7e5d9845c12,0x20fda689655c120afee9,0xa1655c120f5e69d655c1],#[0x120dde6a5655c120ede6,0xe91765c120f7a689765c,0x5120afee91865c120b7e,0xf6616555120e9f619655,0x55120adf6a16555120cd,0xdfe998555120cdf65985,0x655120cbf6598655120a,0x8ffe9998551208ff6a58,0x7459120f8f5957459120,0xeaf6197459120f2f5d9,0x56559120e6f61d745912,0x20cbf6616559120e9f61,0x816559120abf6a165591,0x120e9f61d6559120f9e6,0x6a16559120d9f65d6559,0x9120e3f61d7659120e9f,0xf6a17659120cbf661765,0x59120abfe958659120ab,0xbfe9d8659120cbf65d86,0x759120c7f65d8759120a,0x8ffea197591208ff6a58,0x98591208ffe959859120,0xf1f5d9655d1208ffe9d,0xd655d120e9f619655d12,0x20cdf661655d120e5f61,0x61765d120e3f619765d1,0x120a7f6a1765d120c7f6,0xe95985d120a7fe99875d,0x11208ffe99985d120cdf,0xe6816561120cdfe55656,0x61120e9f5d96561120ed,0xdfe5d6561120e9f65965],#[0x561120cdf6a56561120c,0x8ff69b9561120cdfaa56,0x96611208ff6979661120,0xadfe9597611208ff69f,0x185595208ff69b976112,0x20abfe918659520adfe9,0x5190595208ffe9198595,0x520bdee919059520dde6,0x61d9059520f9e5d99059,0x9520dde65d9059520ede,0xf6199459520bdee9d905,0x59520cdf6619459520e9,0x9fe917659520f9e68176,0x659520e9f6617659520b,0xe9f6918659520e9f6a17,0x8659520e9f65d8659520,0xadfe918759520e9f69d,0xd8759520e9f699875952,0x20adf6a58759520e5f65,0x619759520adfea587595,0x520adfea19759520cdf6,0xe999859520adfe919859,0x1520adfe9d9859520e9f,0xf69396615208ff69b946,0x5d920dfa649905d9208f,0xbf61b945d9209fe68394,0x45d920c7f61f945d920c,0xabfe91865d9208ff6a39,0x985d920a7fe91875d920,0x8ffe91985d920cfee81,0xf94619208ff697946192,0x208ff69395619208ff69],#[0x939761920afee8197619,0xd20adfe959461d208ff6,0xe819661d208ff69b9461,0x49508ff6939661d20afe,0xfe918654950e9f619645,0x61950abfe918658950ad,0x3e5d1625c1608ff69392,0x65c160f9e689655c160f,0xe3f61d7458960f3e6897,0x8758960ebbe898758960,0xf1f595745c960abfe91,0xd655c960f9b689655c96,0x60d9f6a5655c960f1f69,0x89875c960b3fe91765c9,0x560a7fe91875c960e7be,0xe919259560d9f6519259,0x9560e9f61d9259560b9f,0xfe9d9259560d9f65d925,0x59560e9f6898759560b9,0x9ee819759560e9fe8987,0x25d960b9fe899759560f,0x9bf693925d960bbee819,0x9261d60afee819261d60,0xf5e681655c9708ff693,0x99059570e5f6a1655c97,0x70bdee899059570dde64,0x5d9259570f1f5d992595,0x570cdf6619259570d5f6,0xe819759570f1f6897659,0x9570b5fe899759570f5e,0xfe899859570edee81985,0x5d970b7ee81925d970ad],#[0xdfe51826016597f69392,0x260165e9f5d98260165c,0xb9fe999260165cdfe5d8,0x92601659df6939260165,0x5cdf61f9260165d9f5db,0x976601659df69f926016,0x65edee818760165b9fe8,0x819760165adfe8987601,0x9659df68b9760165bdee,0xe89905d965d9f649905d,0x1769df68b9061d65b9f,0xa68976501208ffe9192e,0x50120efe6a17650120ff,0xfe69d8650120efe69586,0x750120efe6858750120e,0xefe6998454120efe6998,0x8458120efe6958458120,0xfbe6917658120efe69d,0x19758120efe691875812,0x20dfee919758120dfe69,0x99845c120efe685845c1,0x120f7e691765c120efe6,0x685845c520efe691865c,0x5120cff6a5845c520efd,0xf6a58655120edf695865,0x59120fbe6817659120cf,0xbf6958659120ebf6a176,0x759120ebf69d8659120e,0xebf6998759120eef6918,0x9759120cff6a58759120,0xcff6a19759120dfe681,0x59859120cff695985912],#[0x20cff69d9859120cffe9,0x81765d120cffe9d98591,0x120e7f6a1765d120f7e6,0x69d865d120eef691865d,0xd120cff6a5865d120e7f,0xf699875d120e7f685875,0x5d120cff685985d120e7,0xff699985d120cffe8598,0x161120cffe99985d120c,0xaffe9d9161120cff65d9,0x9561120edf65d6561120,0xefe6817661120cff659,0xd7661120ebf659766112,0x20cff6a57661120e7f65,0xa57661120aff6a576611,0x120affea57661120cffa,0xe9d9661120cff65d9661,0x1120affe859761120aff,0xf6918659520affe99976,0x59520f9f6917659520eb,0xfe651905d920edf69187,0x45d920bfee91905d920d,0xe7f61d945d920ebf6199,0x865d920cff661945d920,0xe7f691875d920ebf691,0x1985d920affe91985d92,0x20cffe91985d920cff69,0x959461920cff65594619,0x920cff65d9461920affe,0xe919561920affe9d9461,0x1920efee819761920aff,0xf6519161d20affe91976],#[0x61d20affe919161d20cf,0xffe999461d20cff65994,0x661d20efee819661d20a,0xebf6918758960affe919,0x765c960ebfe918758960,0xe7f691875c960f3f691,0x1925d960e7fe91875c96,0x60bbfe91925d960dbf65,0x519261d60efee819261d,0xd60cffe519261d60cff6,0x6939261d60affe919261,0xd970cff6939261d60aff,0xfe91925d970d7f651925,0x5d965f9f6897660165b7,0xffe518260176f9f68990,0x2e01769ff6939260176c,0xeff6a57661120cff6919,0x9761120eff69d9661120,0xeff6999761120eff685,0x1945d920ffe691905d92,0x20eff6a1945d920ffe68,0x91985d920eff691985d9,0x920eff6959461920effe,0x6919761920eff69d9461,0x1d20effe919761920eff,0xf6999461d20eff685946,0x61d20eff6919661d20ef,0xbf691925d960effe9196,0x261d60eff6519261d60f,0xeffe919261d60eff6919,0x8260176f7f691925d970,0x6dff6519260176eff651],#[0x480000bffe91926017,0x1fd01aa014c00f9009b,0x3bd035f030c02a30250,0x593052a04c10463041b,0x75e070b06ad064f05fc,0x92908c00862080f07bc,0xaf40a8b0a2d09cf097c,0xca90c4b0bed0b9a0b47,0xe690e0b0db80d7b0d28,0xffd0f9f0f570f0f0ec7,0x1186114910eb10981050,0x12f912a6125e121611d9,0x1477142413d11389132b,0x15f515a21565151214bf,0x17aa1757170f16a61648,0x194918f618a3185b181e,0x1ac71a7f1a2c19e419a7,0x1c5b1bfd1baa1b6d1b25,0x1dad1d5a1d121cca1c8d,0x1f0a1eb71e851e531df5,0x209e2056200e1fb01f5d,0x22482200218c214420f1,0x23c62373232b22e3229b,0x257b252824d5248d2419,0x272526d2267f263725ce,0x28b92887282927cb278e,0x2a2c29ef29a729492901,0x2b942b412af92ab12a74,0x2d5f2d012c8d2c2f2bdc,0x2edd2ea02e6e2e052db2,0x302f2fe72f892f4c2f1a,0x31d93170311d30bf306c],#[0x3399333032d232743221,0x355934fb34a8344a33ec,0x371936d1365235f435ac,0x38e43886383e37eb3777,0x3a4139f939bc39743916,0x3c593bc43b713afd3a89,0x3dd73da53d733d203cb7,0x3f973f393eba3e7d3e1f,0x40ff40a1404340063fbe,0x420f41d2419541634131,0x4340430342c642944262,0x4487442943f743a44372,0x465d462045ac453844f0,0x4783473b46fe46cc46a5,0x4893484b481947f247c0,0x49fb49be494a490d48c5,0x4b4d4b1b4ae94aa14a4e,0x4c9f4c574c254bd24b95,0x4d994d674d354d034cd1,0x4eeb4ea34e5b4e134dcb,0x507f50374fe44f7b4f33,0x51e7519f5157510f50bc,0x532352fc52bf5282523a,0x54ac544e53da53b35376,0x560955b6556e553154f4,0x572456f256c056835646,0x5881584457db57a95777,0x59bd5975593858fb58b3,0x5ad85aa65a695a3759ef,0x5bfe5bab5b6e5b315aff,0x5d715d1e5caa5c785c30,0x5f1b5eb25e495deb5dae],#[0x60af605c60095fc15f63,0x627a622761c96160610d,0x647164086394634162d8,0x665d65f46596652d64cf,0x6807679e6761670366c6,0x69fe697f692168b86865,0x6bb36b766b186aaf6a51,0x6d736d2b6cac6c6f6c11,0x6f546f016eae6e456df2,0x714b70f8709a703c6fd3,0x72f572ad722371f171bf,0x74c0746d73f9739b7353,0x76b7764e75e5757c7529,0x7898782f77d1777e7720,0x7a797a0579bd79497901,0x7c5a7bf17b937b147ac1,0x7dee7da67d3d7cea7ca2,0x7f987f507efd7eb57e4c,0x816e811080a7805f7feb,0x832e82ba825c821481ab,0x841d8417841183c98376,0x843b8435842f84298423,0x84598453844d84478441,0x84778471846b8465845f,0x8495848f84898483847d,0xc4e0171ee34684a1849b,0x2b00b8c710e38790b40d,0xb050244127344485a06e,0x71ee35c60ee39c339d82,0x8c828e3c890b40dc5e01,0xa39a1c0902b05f055c5b,0x9c78e049c703282be3e0],#[0x63c7025e101d415829e6,0x2e4a1413062c8bc12318,0x2901841242862cc618f2,0x28273c791b824668702c,0xef1046e0919ac28418e4,0x214f1e46ccd10120ce98,0x918ff34301931c0ce09,0x50c7c12f3440a1240852,0x5850cd1207bc203c2408,0x242401931c6741978842,0xe0b60bc169168524648f,0x82522e47c1771a4812f0,0x1231aa3c703a0640b0ab,0x6412d1e409d23685945c,0x24d1006414835237a2f4,0x381291c0b60dc19f1e85,0x978507506e0cb8f934,0x780cf85837049c7c9a2,0x3be150cc12a40a687046,0x32408660918f534384a5,0xf8524063e0969a23c28a,0xc848a2aa6890460780c,0x4a4d0f0520928ef10a75,0x5268702f2384ec190968,0x934478593a84a0ca1e09,0x8e4e819095e14c7e12,0x3c0ea0cf8542463e4d1,0x2d8410790a48ff3448a3,0xf04a824e687025e11880,0x20f48f7343b8673b0820,0x87b0919a1c0978506508,0x25878cd101285199df0a],#[0xf334404a032674197854,0x1628c0c83283de150948,0xed0bc0f80c9df101224d,0xe85d11e6870680cc1948,0x47c8c05e2f84049c0f80,0x380e8c4225a68713b22e,0xb27425312934421782da,0x91e12a4d1028c9011ef0,0x9a064303293be1781f01,0x7c9a064348e091275c2c,0xe0ca8fa34304a93be154,0x46d47c19a3440a043c46,0x3d2818d0e08c1078543c,0x843d4686094c77c2a198,0xa1291f468701e4760c84,0xf2a0a34441e83208fc2,0x681b0a12811819a3be15,0xae0f0d51e1f0704b4338,0xb101230d0a12822e1df0,0x1613a1308f29a1a0ea19,0xb20f03a3048f69a1911c,0xa4ef85046e0e8f49a1e0,0xc3441230994681a8812,0xc12823023c3be16c0aa,0x8d0f4410f0a0e166578d,0x68714228111611e16657,0x4361014228385895e23c,0xb343b85e17c0744028e3,0x9d1ccfa14425622c5a15,0xd0b0520938b718e3e0ab,0xdc6d8f1e0ac14824e3dc,0xe370a0ea710a412b1745],#[0x1b45c833a45e0918b31e,0x42419a19824852c5d8f7,0x4e46c8bc12b16e36c7e1,0x142904a8db8fb3430360,0x91b824e2cc6e1471e3aa,0x9214716e31c7d1b28ce,0x51c799a141802943085a,0x40eb0a38fb34311b8258,0x8248528db8fb343d1b02,0x1b824e3f0a59a1c1e21e,0x4412c29481cd10118901,0x8c7e14734284470c1282,0x4819614b1ee68624104,0x330490a58fa40e687a40,0xbe07850c7d8d05630334,0x832b16848c6e14b1e418,0x81e14b1f634158c6740c,0x1c8ba14425668258be0b,0x12c2519d711850cd612,0xb0c1210921e095852cd1,0x4178bc0f0a59a088204b,0x850cd58f1ac5d8fc28e3,0x2463f0a59a180c832425,0x2e0763f0a59a1c0f03a4,0xe1471f634158c1181d03,0x951b71ea86cd11c0dc5,0x51c7d9a064221e832852,0x8f7383d8fc280e9cd098,0x6a981e0bc1691704a464,0x3478f46e09216516a3ec,0xa3c8c2d0488de8bd1867,0xa8d81205b8590a68bb1b],#[0x91bc161293123dc68291,0x6121e45d85c2523dc682,0x478e2750b28b518a3cce,0x2060320d745e8c33984b,0xaa74a03a85945a8f71a1,0x650b414825a2f4668fa2,0x4e1747e8cc240d4685a8,0x832e2e0938f91ae607f0,0x1b833049c7c9a742341b,0x35208248654e58f53434,0x343e19824480c79a1d34,0x81e9001205b8650a58fd,0x142750c98b31ea370919,0xd1388660a58b51b63f09,0x419c24e3e4d0c0dc1389,0xca1271f2724d0e6844e,0x664e38fc25268707487a,0x2271c7c9ac24382303c0,0x4338494d5a124238a383,0x12534304b0956142429d,0x79a1d3438a343263cd0e,0x70969a1c0f619074848c,0x63f4d1208c0f01931e68,0x41f03c0740b70cf03b0b,0xf5344515716a35c78481,0x108660a4125470b68ab8,0xe433052092a371f4574d,0x68250c065c782dd34221,0xf268240cc0c1bc1970b2,0x83228e4d100760ca1231,0x8f9343046037e150958f,0x783ad342c19146853095],#[0x50958fd341146032e16c,0x115c2e12b1fa68503c06,0xd0820f41291ee71cd0c,0xf0e2850f19c51f84acd,0x686096120ce99cc2466b,0x5a3c71468794799cc246,0xb34461e0320c90919c33,0x411c518a143c67147e12,0x5b63b0f703b0ba3ecd1,0x1e943849cd100d019832,0x7ca1734384170c12c254,0x70f39a1c1921983c84a4,0x455cd12e182584a09145,0x151a1e82904811c2d51f,0x2b3412c503da3c16b9a1,0x8f43d668240a8788ba1,0x41045e0787acd0441109,0x91e84acd1009744612b3,0x12b343046041e160f0a3,0x968fb342c1e14685247e,0xe4648f9300fc703ce141,0x22e47824b1a411b23322,0x1f6364c0e81381f01d0b,0xfa24a709e07c041248b9,0x8c2744c41782d22e4648,0x1f8e09245c8fa25261c6,0x34823646745e8c531a3c,0x2703e0209342e8bd1f6,0x1781f0185ba2f47b8d20,0x6a744e4a1535c489049a,0x31ea6b890e1302470109,0x125352848e0208c5089c],#[0x969a201909c436866c7b,0xc70742849011e93863d8,0x402f93862cc7c8d6240a,0x1983291b62ec7d8c090,0xc06c5c9c91b63c158e0d,0x3b2708b3129341306e07,0xb6412742431e93527081,0x84bb0ca864d7122c2604,0x220c130238a383a27380,0x6a4e100bc4ec9c625268,0xe503a1464808f18f6252,0xca47685e07c0516c9ab1,0x7c06c7c9c93438340660,0x91ae3e8902b181d032e0,0x19542e3e8949a200c38b,0xe38f9340c841462720dc,0x49011e53863e8969a224,0xc0f80e85b1fa68614628,0x8dc0f80d8fd3411c5d1d,0x4d0dc0412685717a35c7,0x6b8915a3b81f01d0ae3f,0x250a3e0212c1199d5426,0x201948f62466b5094130,0x4a86cd0e1284e91b2321,0x91668db0c1302584a62,0x7c0427688b3a1302584a,0x62466a5090076c3685e0,0x8fb34483214646c8cc8f,0x7c0f01d685e07c0516c,0x3a065c0f80c8f9436687,0xe682708a724783a73420,0x7c042768f7343006f09],#[0x4e0262cc618f33a4685e,0x1d091668260ba178182,0x2619dc28e230919a2c8b,0x68241012c2562d04668c,0x184d0680cc1918ef106,0xe07c041c59a19c459a09,0x85e07c06cd0381502685,0x2f03e02e36c5d8fb1846,0x381f01716e3ec6900934,0x139c782db342004d0a09,0x82d7342784b11e682408,0x45c8fd1a0ac178ae3ac7,0xd1e3e8b531a3f4603216,0x431012703e03a2dc2e8d,0xb512d34130470b44b4d0,0x98289d82d4494d04c140,0x8d34104482c0742569a0,0x28702d44b4d04c128938,0x4221b43244a4c5855341,0x147269891161589038d3,0x9ae244845033e164e84a,0x990744c701096e1451c,0x8a05e274843129341106,0x949d09428fc2c8f62526,0x7c40489340c8a08c1141,0x120509a0d019c8e70b27,0x1f268190d06e0ca8f934,0x470ba682507274257855,0x2b4d0481419785534128,0x7c06c402bd34308f03a1,0xe07c06c469a0562905e0,0xf4d0480ec4312057a684],#[0xa070302fa25a68220923,0x69a088203606a0ac17a9,0x80e8bd1ee34158c0be89,0x2916e8bd1f634178bc0f,0xc86e0c845f0a44b47e9a,0xb0ba3d8969a142322083,0xa3436866c2e8f5343845,0x1a2043d61547e9a1c168,0x822f01b0ba3f4d0c0b45,0xad3422a1d1f268190811,0x785d1fa68230ca724783,0x81f0170ba3f4d0a0e819,0x9381f0171761746b8f1f,0x8db1e358571e0cb4d080,0x969a08c2024e07c06c5e,0x94268e06563f4d0963c1,0x5d1e0e9cd09e12c2f9a0,0xeacd080eb47d9a08c258,0x263707e17056304ed1e0,0xe0383f0bd8d056360be0,0x12e17c3387a9506a360b,0x3385e17c0787e8d05236,0x96321e832a3e8daa1a34,0xea344a8806d065c1d1a0,0x8c0820c823f0a46e47c1,0x303c864c7e1b34386870,0x82303286ec7e1a08a302,0x5280708bc06c7e1a52a2,0x96304b094c7650b1963,0x1a090311da3225d5051a,0x51a080311da3223d505,0x247e12a34382623b4655],#[0x23f8d0451a8c823940c5,0x3323d4af1a141181e141,0x3c32e16c1e1a0842845a,0x5ec1e1a0963836c3412c,0x6a3f0d0401511a1923d2,0xf61a281b61a0961c97b0,0x1d0941141948ff0ae0e8,0x561df0ae0f0d0452211e,0x420588c340fc60460642,0x7480c8fc34120503a86,0x512180da19d1f868230b,0x8d0461c1184770ba3f0d,0x3f8d0a8790cf8508ba3f,0xc87acd04c1422f01b07a,0x4b8830959a0822a2022,0xb4d04c11c1d1ed341104,0x25c8f58353412c702d47,0x960d8f69a080222306d,0x9051e9344d8363c0af4d,0xfc509406c2349df0a08c,0xda68240903c2011ed340,0x4b83c15829d34300fa3,0x8504bc078469a0822835,0x44b4d0c0810f60fd3411,0x6bc68220811c11a9cc1f,0x7c2d60f40b1a08835830,0x681a8b60c1af1a088251,0xa538d043124902b070c,0x7f1a0822035634130306,0x412b88d03c68208ba058,0x7e34382f247a068d04c1,0x41100e8810560a6c402],#[0x15829e340d46d0343f8d,0x2817a92e34110442d43c,0x211822e1df0aa824f61a,0xc3ae0f0d0451c2521b83,0x83d11c68200a067c284a,0x4385e1fa078d04614133,0x8d192023684ac7e14b34,0xe819212b1f852cd1211,0x17635c78482423045346,0x4064303606a0bd428327,0x6147344046074e3ecd61,0xcd0c0ec1c82a344e2c1d,0x30240e1181903ab1f851,0xa12470660cb45b8dd1fa,0xd3440480600bdc5b8fd1,0xe0fb0c83c07413816b8f,0x8f0644e58f14726b090,0x3c05a139c2d8f075a689,0x2b85b1f84b4d100fb0c8,0x70969a08a38470780cc2,0xb5cd2a2200f019b1ee1,0x35a3c905c0a81661e716,0xd30f3840660c82682d7,0x8f07851c8f14366b090e,0x305a135c2832b35a3ca0,0x28b53ea689069879c203,0x4d100b01502ea2545148,0x48a2b4528929053fa2f,0x1b035516a3ec6a9807e4,0x1345a98d1f6341f920bc,0x9269890a32024d1ba32a,0x935270903c06422d8f93],#[0x21182283a06428ec7b12,0x5e0ca4e38b91ae3c241,0x3a71f26a4e032141b035,0xf03c05aa72c793ad3440,0x41958f538a689d0a1381,0x4828f68ea24a72c7e9a2,0x79272c7e9a624404e095,0xcb1ec4b4d0f28c198470,0xb8f71812099472874749,0x24101261a433865a35c5,0xc348670cb46b8b71ee30,0x26e85e07c074738fd345,0x69c784d1e1a4338650b4,0x2c4acd100d01983205ba,0xb34481903c11451c8f94,0xc1141d03214723d894a1,0x660b747d9a5424c8808,0x3a51f669509321426834,0xdd19b1d44b47aa1b3440,0x85138b075285cd101368,0x23c1d4a1734283b0720a,0xbc061e2a2716e68b065,0xa09c304e87d0ea16f03d,0x68f7345c3c020e11c5b9,0xc8750b5c7685e07c0427,0x3a05ba3dcd04e1e1f43,0x1e02db1668acd120f81e,0x8acd42d1c2723e474621,0x1668240e0b81602ab166,0x71a124b09c8f91e23a71,0x68ca18c30b18122c5d8f,0x23363f0ad9a3464a3446],#[0x9ab1e8b4845a8510911e,0x6d9a20d184d0680cc191,0x873461381f03c07463d1,0x558ed0bc0f80a2db1f66,0x30ae14b1c68f0958fb34,0x68ec7a2db34204e09a12,0xb8fb3461a345b63ecd08,0xc4750d219c3209d63816,0x832b34e3c268c1351f23,0x9588716641cd100d019,0xeac7b9a09c3615c28613,0x5a2f47e8c090403e0780,0x34326b89140d019c8d06,0xe1338084b08e2724e8a3,0x9c4f89e12d70ba68250,0x1908e1154e68fd354489,0x7b85a25a68228ea860f4,0xf47b12535284903c0674,0xc4b4d128c90da1913828,0x51d22043c28451a8f938,0x8ca4e045d1f2858969a2,0x5ae141949ad1e4846474,0xf075a68809a0d019c8e2,0x4a31c2703e0784b5c2c8,0x4d110ea19385d1f44b4d,0xc3a865a3b81f01d1ee17,0x1d432e07c0747e9a70a4,0x35c5b8f718120908c116,0xae3c1f8d0d21983230ba,0xb0ba69c7950c9c5d85d1,0xc1351d4348670b747032,0x9140d01982dd34e3c268],#[0x3686b0bec5b85b1963e1,0xd785b1fa68190c0ff094,0x61d385d3563e190e1181,0xe141d58b945668b08c11,0x74404e47d0ed16c2a478,0x6421dc39854e16c5d9a8,0x650b42703ab0ba3dcd12,0xc05ba3dcd04e1a1f43c4,0x32f0a0eb47d9a181f03,0x22c3270ba3ecd43a1c23,0x160cb85b1f86b0d92118,0xf8694a8451a1183c0661,0x4746a505192011819b1,0x85941c68904211c8e48f,0x28d08c1984507946647b,0xb0c8e08c0f48fe34a542,0x118608e1190e68f83786,0x8dc68703786747e1a628,0x3e3450450740cbc2e8f0,0x748ce19045e03a3dc2d8,0xa865a3ccaf1a08a323c8,0x43ac3360f47f1a70a4c3,0x47d83e34114808d88e19,0x178d0451423a3c466e17,0xea724de1ed344d83d1ee,0xd34118644308023846c1,0x81a34130804187b07b14,0xd0452a0e8a023648f0b6,0x23c3a11819785c1e64b0,0x51be1e6578d045185d4,0x119a94e1f60f8d0451e9,0x11dc2f0fd03c68230c8f]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0xe2008038100120804106,0x808114440812244e991,0x40260a08f88000038206,0x841d240011400c05ac0,0x1442c201002c0000000,0xe1c106065c98004085,0x126011304100091808c0,0x61470304007172e04005,0xa073a047807084e000,0x810a4c699000c2818214,0xf89047833a1c18100474,0x8c0a04300020c003c480,0x908180800a1428602042,0x6042843a0c196080400,0x4a809c5630600640a381,0x74519380811700440134,0xa60100943180ed581702,0x39e22e0f0034d0004080,0xa200d2920a243040200,0x9780cd05142c4043c0c3,0x600cdbc27089a8641c40,0x22cf880a200844afdd8b,0x11f2cc402f20040840,0x8107026cd000600d8e06,0x76d3ed5c9e080000d9a8,0x6508800003a00c828c14,0x21c0000282bc18743186,0x95417ce4c9bb277002dc,0x4d8f2ca27c0a1c177291,0x87635356205070bf9412,0x890f2c186e84100000,0x9820e926a60201a4c5f4],#[0x804e7013a01c80000612,0x8b6852690e6f285b9113,0x100001e1da90d22c5e5c,0x99491d1b200000835400,0x834c904fd0ac00006248,0xcc00004c844000000000,0xb641ef0bb1209c83a849,0x1e0e396fc5223cd21,0x5b9c3ae0000a2e8381e8,0xc426c2e4150c0e900a40,0x2a8ec0000a825f82,0x1c000003307a132f08c4,0x8c002b0628000000012,0x21284c24ae2cf6a78881,0xa711838d403924950a23,0x308246a885600000012a,0xe50d1bb0f6e302000074,0x9984af80003996909f,0x14c9b068800003c167,0x66622e00000000588880,0xf849ec8d164774609cb0,0x2e28000352ef62465222,0x5d068008000001e4322,0x2e032b0e450637919384,0x41f2a17860065094402c,0x34f09e5e5dd2226f2538,0xb301ca111ac28f118aa,0x14641a1fe905780e7312,0xc3440cb00489829faa23,0x7524da9436d00d20441e,0x55265ac14840a083fb51,0x82a89236000062746023],#[0x71e21980000885500007,0x620b40000380f8a044c6,0x1c0236912d0b90a10,0xdb4845541a00001d10b,0xc64081c17b3010802968,0xa861240ad816d00d7c93,0x60e714740030c237c417,0x9910eb017b18070d69a,0x38cea64320000308ebe1,0x8a38424b10c00001d9f,0x4648b36a12fb47808168,0x3f13ac50760000701de8,0x314460c9e0000a05,0x300007a45000010185,0x7c21d1a0d8800038172a,0xb4927007802e11014b10,0x24d3802f400600005b51,0xc7421ac0000e22320660,0xe61600000d0b2409540,0xa0ce5093782d9c364000,0x99f01470000183a10036,0x6791d4c1f0109b310004,0x2869c0000d21200a58c7,0x187a90831007ef496,0x4209249ad402d0,0xa02199676ca0c4c27200,0x4353c820643444467829,0x89fc16fd1c43a412883d,0x5da3d4000000003611c0,0x80167874110bd8d2b305,0x411023b508a3d036811f,0x8d822e3606388aae3988],#[0x3a01cc1e600001b0a589,0x81a549668487f48b1047,0x40846d1fa0000241bf,0xb09dc0246a49c000000,0x206b00000000089f48c4,0x12842b096d1373c18f,0xe1c2c49d304f80,0x149310000000,0x61b41330036ba18720f0,0x3d0000000000000e0680,0x34de00002c38220,0x50520000000000002096,0x80f62a80000000012341,0xba82c00000605530f9f0,0x7631800028279c41cc43,0xe62bd835c00002833,0x97417326105081341b60,0x4000040b500007820ba0,0x850ac219e18b64240172,0xce7803800000000847bb,0x32808005e202a70,0xe2060000592380000000,0x7e000022052212ac1a8,0xd3003a81200000621a89,0x8000250be000050e9385,0xf3d24dd83290138b0fc,0xb20000000004b8d242e4,0x3e1770213b949f01640c,0xc337e0bae00aa3204420,0x882f321000a72091d,0x3087ae03f7e433907700,0xa26200002046461ab321],#[0x2859619eb85c4,0x54000000000000310e40,0x2a274a19500000868388,0x14cc0000cc0480adf01d,0x8780696d200a23a00003,0x202cc8067810e80fab2,0xc47cb2536c4cbe3b5e1b,0x35c905b90bd413ee42c4,0xfcd879a0310000008350,0xa041283f04812f842801,0x31404c0c8802416942e,0xd8f4612206641bf623d1,0x2288600003840d925d28,0x23276063a282a85a6828,0x72a11dca917307268370,0xe80002c0f6e922212298,0x388b648b4000070b,0xf61fc812c400ec815,0x39e10200000844800000,0x80000000020e48000101,0x1314b00001234,0x242ce14a304f8,0x202c8000000,0x5a33a8158000,0x3222c0000,0xb0c22a0000f21f5845c0,0x484840001043000003c4,0x841819e407502503044,0xbc0032b832000000000f,0x2e188600001386d3c900,0x581024828011b90e4030,0x309e9a075b01741928],#[0x53257b00a20000000000,0xd440eb3b80001e85c010,0x8fc000058758000068fe,0x4544f0431ff33cb51f0a,0xc00000000e0ce9a08c89,0x26c4000000000000192b,0xdb000000000000032ce1,0xf00006882f430500f8f0,0xc4a8c33a1c1a2891,0x16133e833e88e3c0fa,0x448071484be88aa05200,0x20252040400004488121,0xa4b944e00be891e2514,0xe20afa1e1c46951fe4,0xda08e50ee1911ed9e200,0x8250c1a1e40b434abc1b,0x4dc19d6a036709ad08af,0x8d457fc4846826448cf1,0x141e4624b289,0x838e612090dc0001c80e,0xeca09b00000a4c2818da,0xd507841c3f0e7b88fe50,0x829a88c86425d112fb3b,0xcd9844cc189a4ae00003,0xe9207393ced17a209a46,0x621e16ac8b67b0c31411,0x1f50210a867b04611060,0xba09d8422c6210d06ce1,0xb13750498a985802ed02,0x287008fac0a841b430db,0xd9e0362b25c80142144d,0x4a8ff206d20241c9ea64],#[0xc27ae9dd52430472603c,0x57988cb00b4660c20661,0x20078d9222a08bd05094,0x5205986a88181a0b8f09,0xca00000000000016c1b,0x1610b00004221000562,0xfc4036d3de69e0000000,0xa0d600112071802e391a,0x1700001449a000040cf0,0x9c225183ecc01ab16ff4,0xe0c9f00492811008a00d,0x862311800001020cc0e1,0x5e82a0608f6026d13bd4,0x5081e88e800000000497,0x4b9a21c0000144d8328e,0x1100b640640c33e85c12,0xb6212e897730d6042781,0xd856c81f000000002946,0x154238869049b600a2,0xc908d800000000306580,0x4107710fdc1ed417134f,0x412e04c00000911a0000,0x161fc049a800000001e,0xa82ea8c0500005857000,0x4fed1a828ef467d5077,0x27f25bc0000000000002,0x30efda4800000ca2dd0,0xea4f4504191ef681c000,0x4124c9892895304bc3b6,0x8c0000c17021226a2c30,0xf85e641d2e8d10000584,0x4eb0000000000000447c],#[0x5200002a24d5ab041546,0x5692f56310807dcb1d01,0x1d9017e042d886ff837,0x4c953dc88e920eaa266c,0x2f82a01257c1cbb61770,0x1619f828243508c17608,0x90a0000787d9134d0895,0xbae06030fe9a13e10310,0xe48f4ac264201f0544c2,0x208543e9408ac8e4687b,0x80f85560184c16380f93,0xf20dc866b10de000034,0x223c8018682f51335824,0x30c0000004280001485a,0xe749c6ad63d051435880,0x5033441aa0000749e308,0x20105c8fa61670000,0x1a00004a4e400014cfb0,0x9290300007860340de04,0x1a435360b4282849f,0x27b90c5848da42200000,0x314a2c0410c1f501ac0,0x22cdc37c00012134000,0x82c98cb843259468c962,0xb22423b60d5210204876,0x800000000e12491736c3,0x21303012ce03c8039,0x157a15e6260ad6a24318,0xfb0370a4b658730d4706,0x4915a433cb15792e5821,0x844c5c01221f88900001,0x2d01d5c891421ea9143d],#[0x21b8492180d6582d230,0x600000000000c159202c,0xbc008738712c00aa2164,0x8c053105182487a3a901,0x5105e073702129089081,0x3bd0a408146443a9085d,0x4c619024a8,0xa06ee33c2c21a0000000,0x5b0000781860235a0e5,0x62e461200e005780b95e,0x449ec82800003d218c1,0x84c4d823a86c00001836,0x789a0f5432745da00001,0x9a20a6a070e2341084c0,0x84f980c1f06f70868818,0x271683ae4552b0e399e8,0x8b9020c00001874f9,0x5024e1114821b80d6800,0x39010000144280000,0x40cbea19400018a260,0x1618c00002b122824a00,0x993524eaf0ff69750000,0x7750453a1bb000030389,0xac05aac8c68066a08de8,0x1466a871e03d244d3060,0x53561041a2b5c2144012,0xffa0761613d012002dea,0x7083e663dc0b0184df03,0x88ed2095602926183a75,0x1b0dc000080edf0afa,0x6d48c1030600952cf300,0xc0645612e08d61843050],#[0x3d86a12b1271073ac315,0x79c3dc8887901f00000c,0xa81d0000414,0x605594c0000000002621,0xf0424a590b32195e0d30,0x7145c000000,0xc428712f711800000000,0x8ac32361a20000687de,0xef38640000c1a6a007a8,0x878542800000e2c,0x871a67628516190648ae,0x8ff0660214b86f983d00,0x5415a00001110b00cecb,0x13b400000000708a1b07,0x749936c0373408655083,0x2f09714170c3980000e6,0xa0922087c825d0a08690,0x3c92c9994447c7600000,0x94a22900fda052602018,0x2088187d81c508d8f07,0x8f822780ae00fce0dc,0xe20ce025800000e1a0,0x80000c2e6057e7431e00,0x1276621524098000292a,0x145040a09525054803cc,0x92b50801c3481130c92c,0x82047a0d90274ec3104f,0x1721023e0277017fa436,0xac00009274800000c880,0x54434000000003020482,0x25e783da8438708b403d,0x704c1a2002760be4021b],#[0x3947b000028257a110c4,0xb22b1248ca10e293,0x2b5489452293a2c943f4,0x1e03f1270000014,0xb82320254004c76a1800,0x61680001c06e48326203,0xdec01e00000000000007,0x5e42000001a238908f08,0xd2507bf8098488,0x6b2403c8077c05daa068,0xd00000d3b60000000070,0x88c290923d8656166000,0xa2e9461ec114a22cc158,0x3a0000647dc03d000012,0x445e0000d012007d442,0x34332881e00a98000,0xcd8043c016000061198,0x29904806a05,0x4890d47a126f5c1d7c0e,0x44ce107007fb91c850b5,0x819f415750a61a7c38,0xd87c4499ba94b60b5800,0x188b78441]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0xed2a4a8241fa94250120,0x3cb2ac0907ba58960483,0xfb0cb2a41de9725c120f,0xcbb2e0b079e595705834,0xaecb2ae1a7d8759560e7,0xb92e08859fe41765978f,0x24c3a213ff9460910efc,0x1280907fa549404827ff,0x6a0241fe97250120ff4b,0xa80907f69cd40483fb2e,0xa0241f7a6550120fbcb2,0x80906fe619404837f30a,0x8241fe96254120dfcc3a,0x906fe61150483ef2a8a,0x2417f99654120fbcb2aa,0x907be59160483fd2e4b0,0x41ef96558120dfcc22c0,0x6fe61d60483df2ecb02,0x1df9745c120bfccbac09,0x7de595704837f308b824,0xbf9865c120efcbb2e090,0xf7612734837bb08b9a41,0xfd9855120dbec2aa8906,0xf61964483cfacab22413,0xd875d1209fecc2c8906b,0x595844827fb30ba2419f,0x9561120dbf32b08906df,0x5d844827ff2cc22413ff,0x659520dbec2aca904ffe,0x1654827fb30b2a41afd8,0x59520f3ebb2ca907de64,0x854836fb30b2a41b7d87],#[0xd9209ffcb30a904ffe51,0x64833fb0ebb241afd865,0x9209ffca30c904ff6617,0x4827ff2ec32413ff9561,0x509ffcb30e904ffe5187,0x43cfacab12a1b7d86549,0x9ffc930ca86bf619625,0x3bf2e4b82c1ef9625c16,0xf3eb2ae4b06bf61d6258,0x3fb0eb92c1cfd765c960,0x3ecbacab079f64965583,0xff24c3ac16ff925d960f,0xcc82cab875f595725c27,0xb30b2ae1d7d9759570fb,0xc1300b2d7fe49765c36f,0xecc02cb77f9260165dbe,0xbb00b2edf61d80597cfa,0xc3acbe7d905d965bbfc,0x2e0884ff64b805daeff2,0xa1221ff5425c510ffca1,0x84886ff61d42443fdae4,0x241dfd745c910bfecba,0x907fe59540483ff2e2a,0x241ff96454120ffcbb28,0x907fe5d160483ff2a8b0,0x41bfd845c520ffcb22e0,0x6ff61954483efacaaa2,0x1fbd7459120bfecb2a89,0x6ff61564483dfacab224,0xbfd8759120f7ebb2c890,0xdf59574482ffb2eb2241,0xfd865d120efebb2e8907],#[0xf595844837fb22c2241b,0xd7661120dfecab08906f,0x65d844837fb2cc2241bf,0x9759520fbeca2ca906ff,0x59854837fb28c2a41f7d,0x45d920ffcc82ec906ff6,0x1864837fb30bb2417ff9,0x61920dfecab0c906ff65,0x874837fb22c3a41bfd97,0x4950dfecb30e906ff651,0x6543dfac8b12a1f7d645,0x960f7eba2c4b06ff6498,0x583dfb24bb2c1dfd745c,0x70dffc930eb06ff64987,0x97bfb24bb2e1f7d92595,0x5fbecbb00b2fdf649805,0xbeff20c3acbf7d9061d6,0xbffc9300bb6ff609805d,0xffb24c02edffd945d920,0x9004e80ee028804c0003,0xe0c302ca09f823207c01,0x126045610503d20e4034,0x8e05e2168054a14204d0,0xd87b41d507121b406841,0x896824708c6221084c1f,0xb302b90a8429089f626a,0x3e32b0c4c3000bbe2dc8,0xe3c78eaa3950dea3650d,0x434906840c10023f28f7,0xc212a849491f24699132,0xc947a50b93d84e0934a4,0x95de562155a54614ea52],#[0x7885cf17045b3168a58a,0x5064618cc61898165f51,0x66ab9a5868819de66499,0x72a1c5c7041ba66d41ae,0x9e9e387789d967529cfe,0x19fd87e59f5e7c71ed07,0x215083ea0c2822a04880,0x3548bd22a8899a1f2867,0x4e940a4b6910a3ec8e82,0x49cba6ce99ba60496ba5,0xa4a28d2a1f28129f4278,0xc8aaccaa52a2aa72a96a,0x82ca8b122c06af12b8ca,0xae70b892dceb5bad18b3,0x38bf62f96bd52f12bb1,0xf0541404b9a1f0dac213,0x1622c1223c8c238be138,0xc19e3c122687e1f8505c,0x149d06612268723b8506,0x801e0488fe68823b88e,0xde23854489a2422e1385,0x198791a181b0648e0c89,0xc1e0648f4687e1783474,0x7785e0d1e868708f85e0,0x27785e0d1e268608c198,0x6e17838758108e1a1823,0xb1a1a1107b0b088a0c68,0x2f1a0e46a0f01c2d8508,0x62d8c63e14181001583c,0xee3c1246e14668604917,0x612141263f9a85120158,0x221463a121a146258f63],#[0x61b888521266886318a6,0xb636146321218486758e,0x2f0498b6318f850863d8,0x832e3c128519a1c160ac,0x103a04b9a63e141c1963,0x46c12a2e8f63616181ee,0x8f248b0588c23c988486,0x1404b870b616a2e8c456,0x4882741622c8f6361218,0x1419058290d68b6368f8,0xc8489a1a190498f4829a,0x19e3d15a68823b8f0649,0x18f8489d1c1404a8e0b6,0x661263c9a1b850658b63,0xea190498fa687e14a30,0xe0678563e12a68707b85,0x220788fe68a1848608c1,0xb844402d87915e6a8f24,0x7586e16128799a1c1404,0xe14a30788f8499a184a6,0x6067850ca1e04a8f6687,0xa8e1d154528944a8fa34,0x489825154528aa328844,0x3817058240bc8b2308f4,0xa1703c0787a2e8f1268c,0xac4880c4300bc2d09000,0x9a204823b01e209d2709,0x8a06c1923832e3d12270,0xc32a3a85c0f010b78fa6,0x103a23d12e68a120340c,0xc07840b79aa3cb0801ee,0x266890f83c0e810a1703],#[0x78558e6199de22141221,0x458561462d8f63612630,0x3d9a0b4401d8b6318f0b,0xd28100139a63c2d158ee,0xd05c164142b22c8f44a8,0x852768ba3d12a3090bc9,0xf01a2e8fa34b06c190cb,0x6870d8350c82f0af85c0,0xc4890d68e0589d13112a,0x128a3c0423e149d6209a,0xa1a9de15121291ea688,0x8e421052744444a9a252,0xd85a2e8fa302f18360d6,0xa3c80168ba3d8d0bc501,0xa20a306c190cb854489a,0x728c200783ae148f44a9,0x850e832e1703c068fa68,0x3d8c0c85a3985e3e9a0c,0xa180563e9a0c840158b6,0x9a0e84040046168fe683,0xc1682e0f636172005a3d,0x2d0f4309b4587074350a,0x26f0b2370f8489c141d4,0xbc3f0c0d46074190a435,0x19a3d1b8791a140560f0,0x6e1a1c1e8648f2831a14,0x46aa01c2307b850658f8,0x92811a184aa0f8547519,0x1923ca0c687e142323d1,0x58312e19868a08c1ee15,0x661a1c36838176218507,0xa3e1a158560c1d1208f8],#[0x560f01a3f1a1a1908d12,0x9d61b858821e66871178,0x4350589d1311ea686129,0x47a9a200f2744847a9a1,0x2a6850d4254150327441,0x8311281c68a8782383d1,0x83520360d51785b0e075,0x68a05b0e2208560c4cc6,0x8e85a0e1607588a044c4,0x8581da044143f1a1c354,0x6214836204cc68351c35,0x1987785e0c2327a1a201,0x48520d8183c48c687114,0x1823e1583a070fc68787,0x60d108470b87995c6871,0xf60e10a220b8461a6548,0x888430bc44952831a181,0xc39a0f0144188c2e95c6,0x18a125522c2ca0c471a1,0x267c508b0b2871a28311,0x8f85212674662e1466a1,0x70663e148499a118c62d,0xa35981a16a2e8c84a8f6,0xf849a1a6858658b63e12,0x88a3e1266a1e67058658,0xc2d454104528b44a9fa6,0x23012748b23d8d263121,0x46d190ca8ba3d1263698,0x10dc272628b6368fc48b,0x9c63f12a6860a49d2730,0x58c62c9c63f121f01284,0xad8b6311263e9c270127],#[0x2718f26b121d174582f0,0xa4498fa6a9c1ca3c0423,0x12718fa6b1221204783,0x19dc499aa84b11ca3287,0x6871304a61a85c044b12,0xa84728f0108c8f287126,0xd668946d190ca8f4499a,0x86282e0a9a20b38862c2,0x1da16120b58b63d8d120,0xc2de1c4862d8c63c4928,0x8e148498f66890c4300b,0xe3c2d66890b5a38562d0,0xf0b48134340cc3263848,0x4a1c3e0f03a13b84e698,0x8481898c043744985a68,0x328f124a077014488fa6,0x20310c02f0b585a2c24a,0xd8350ca8ba3d8d0bc2b,0x507819e14a3a3d12a688,0x89c0585a3e9ac48a3184,0x8450e83228f85a3d12a6,0xcc2da3985e3e9a0c8911,0xe158b63d8c0c8a134340,0xfa68321612120360d42f,0x852898b0e99a203ae158,0x185a3f9a0e8a0ec390ab,0xe99a143e0f02d2884ee1,0x83e1685d9c1832e168f0,0xbc330f2709bc58682e0c,0x2fc2d83c330f0d42b270,0x58f86e19869a114360c8,0x86a19208f2871a283191],#[0xfc68908046e141ba3c23,0x888c321143a8678560e8,0x2307819e168f60f1a114,0x97c043647983a684b1c,0x1820e149b83c2387a9a2,0xda160ac92c68380d471,0x2918250ac9ec68290d46,0xf1a0fc60d4250ac9ec68,0x6f0f87b1a241d6044083,0xc68451d2086446117854,0x1a6b12201e06785c3d83,0x1a1149c0447270a3a3ca,0x88c460e832e170f24b]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0xa000820e0c4950410102,0xc0101838607120c0850,0x1020214080080c20116,0x6020408c5e10900340,0x40000000101ca800004,0x4002031830085000c1,0x10080070408201122808,0x6002050c0c3800208d8b,0x284250610a9706203022,0xc0001000386010800118,0x28e143020b2c340000a1,0x9a0c00200001810b0a04,0x216040020e2020604502,0x1c04011120140,0x62800002182000ca82a6,0x90900001805229d6001,0x2001600082020400104,0x68806000820a21000002,0x5008030504303000810,0xa08a80b86810c810a003,0xc35c0000427468a60c00,0x80e88f7001161346309,0x10d1010d61ec00000000,0x1c0f62091825c,0x40c200000000617e,0xaca001610a4000000000,0x6b3c82b0000001ee0000,0xb2114225088400000000,0x811ae4c50c1d84882244,0xd33a28f582aba0acecab,0xc31a0001666d2173e2ad,0xa447a08c000140f48266],#[0x12689ae720001,0xa13e00000000,0x254c000000000000a30a,0xea210146000121f80000,0x645a0000000000000001,0x1b113c28a00000001,0xc2c600000c8a0000b23c,0x2627a684872782a40000,0xc9166602c05fc1c4889c,0xcd80000ace1,0x1c2a2000106640000,0x0,0xea7600000001418ee1ae,0x27414a7f42d40001,0xa18121160000,0x2915c8464138c0700000,0x24e6e1fa0000614f,0x125b281b20c940000,0x83040000631dd28e,0xc35b651bccb12179c220,0x6197289a000141840001,0xa3168924000025fc661e,0x834c432f121eac83cd0d,0x64eb6a640000c0a9e324,0xa2fd4a38000101c20001,0xc86e000120468114cb40,0xe0ca00014ca3cd44c2c0,0x8aaa0000022b25ae,0x6636800800010a602ca4,0x9121223e63e00768473,0x20db6835294e45a5,0xc40c0000000000000000],#[0x2f468da00000001a307,0x28b20001a056a239ccc0,0x22e10a3085da65c9cd15,0x18eb7e0224a50f062,0xe339455a00000001822e,0x6a07e67446158d5580ba,0xc09fe125cd5e816240c4,0xa54000021a1ca7a6112,0x42dbe1c00000b32a0001,0x435e00000001a5480300,0xa4c625240001a91028b4,0x140340001c2a0,0x0,0x1e45deab7683068ee,0x80f02ca6000000000000,0x161f0033780ef4323,0x22ba45b400000000,0xea870eaca288e5d9a19e,0x1a17a0287aa2c,0x1524101100000,0x2c854d18c1d80000,0x88c0000161bb8eb9a600,0xe16a0001a2e200000000,0xc02f0c17923e0a3c41fc,0x84444af1a919a0c7,0x16721e46200000000,0x24b809d6048600014278,0x62481dc0000a22da132,0x101868896618220c9,0xa0026208000000008892,0x41a8082e000161c60000,0xe212a8bd73239371e41f],#[0x15b0118c40b0156928d,0x5c6a05800016d5a28a4,0xf3380001037202156886,0x1c2480001a6060001,0x68c60001a4d200005212,0xee74e0cfa233465a,0x100d9465523600000,0x2b2,0x12cd4a844ea84,0xa85a00000000699e048a,0x423ac31992d52982083a,0xeef0c2360285c2d60001,0xd3785a9203b21cca0a6,0x492b06734c8ea4e4809d,0x171f0dc8f5000006a2b,0x81aa0899e772223d8205,0x182ee000162194370,0xc190004404cde62b48d8,0xad9eca9d320de32cc653,0x426c200000000000c1a3,0xc2dc0001a9f561b60000,0x813026f34842000041d6,0x125ac00000000,0xa91e0001aa0e00000000,0x4277a18b48e564d9892f,0x209a000060e60000eef9,0x81e800000000e66e60e5,0x83034d560000c1cbe358,0x226a0420000285c0000,0xe169405c000008aac103,0xc0756494014c000189a3,0xe10108120001233d011f],#[0x5a2e12fe0d490c47220,0x108afe2633078e68b,0x1a902220e0000,0x62cd812800000000c2fe,0xe482890f602a7116,0x1cc9f82c360280000,0x8203833200000000ea3e,0x8640800a000182ec0001,0xa0520000b11a00000001,0xd0a00006c9a0001221d,0x736822fb024322c94063,0x8b0f22bfe10f21e6a270,0x2109ad3b,0x80b2e44324c1c668a050,0x80b4e691151200000000,0xd329e22301660001921b,0x22d200000000,0x168b60000a02c,0x8a7c0001c528a0640000,0x3d00dc0000e07a,0x84660000265c0001821e,0x7282e82d68fce6198ce4,0xab720000000000000000,0x73021f40000a5c1227a,0x1182834124f1e1500000,0x9f800000000cc96,0x25784a680fc00002612,0x627e000041b02eed023e,0x6611a145a2ea6365,0x10cfc18c0000c08e80de,0x1246e0860000cad40000,0xa518c1ff48dc69ae8c14],#[0xa50384840000000168de,0x1081c00000001a1a6,0x1e4a4000000000000,0xe8370295425000014246,0x82d9c88ac24e00006888,0x6416457800000039e021,0x414261e1649c000060f8,0x4ddc00004006c092c818,0x1a048f20105b80001,0x364272,0xcc08c175024bc9260000,0xe9200000001600000001,0x180a4000000000001,0x30e00000001415c0000,0x69a600bd463422ae0000,0x1e5a60000,0x891c62a6,0xcc1a00004c1000000c0c,0x604000012cde00992126,0xc526aa4c44384195e320,0x84c200000001,0xd674120033e689e0000,0x43500000000046f025aa,0xa3522d51c8b00000,0x25c348a1e11c00008d4e,0xa48fe74e0001,0x32a0001215e,0x626a0001e43acdb0,0x1e492321ccc8d4c90,0xc9e2260564a000000000,0x616481b904b5059f28c3,0x834548a240cd62160001],#[0xa31088e26158625460b8,0xe24c6cb800002083d24f,0x804dc105a07d,0x28642caca5754c980000,0x1c60ae28308f180c1,0x21c800000001ca8341f6,0x60afa0e3e14a00010d10,0x7206000000000000e06a,0xa905a268f22b60aac228,0x40240000801f2a360000,0x161eb249f64534013,0x1ea90,0x410b08cca41dc2108192,0x108140004000104b2,0x333da4ee000000006d42,0xc73c000166f8e367e2b9,0xe426000090fb0374a17d,0x4a000a100000e461a8ec,0xc0ec00000001a1d3e252,0x34b4b50f281429000d2,0x320f6a46927f429a,0x10068511e0000cdd6,0x214881f200000001d074,0x780000721400000001,0x1a201c49b26476451,0x2824a72421060000630c,0x647489280001a2e8a235,0xea75c36b66f60cb401be,0xa8ca0000c0b766500000,0x42f642f9a6420c898362,0xe27ca92c000164b062d1,0x214008e841e3c8900001],#[0x141bd272365fb,0xc35464da0000,0xc0800000001b20e80000,0xa2400000b0f828ada16e,0x68fe8660012c8061d076,0x1a206a05a00004513,0xcc92603080fee4a2e882,0xa5a0000086207032212a,0x488cc822ace3e63a0001,0xa8ec31f4230c01842b7,0xe4140000326540942497,0x25716066407e40d1e8e7,0x836c0001cf52b22fc6f5,0xa4ddc5f86811634e2e9d,0x10f345096a34008a628f,0x601c000148b9aeab61d1,0xe20c000051f80922416c,0x1a1ce0001d260646e,0x4027e1e4ace801da,0x6a22000000018328c436,0xc06c000128c50298b243,0x4a736638000002cb00d7,0xa43c6137a21a0000c4ff,0x82a2176000000000000,0xc29e2261ecb24a1fed6c,0xe8fa825a4a81e03fc73e,0x8d00000a2f000016055,0x2e9f,0xe8c800016280000100fa,0xc31348a930f7856fa411,0x84cbe26fed0e613be314,0x21980001ed4600006342],#[0xa152000000008088a490,0xe9ec015561a42122,0x6f723600000000,0x2862241b871ea0a0,0x1066b2408,0x83460001e4fc00000000,0xb0f56a93e4ab20b1,0x264e04be52d4d41200e,0xac9c248d813c00000001,0x1,0x9121c64a4296,0x311d23340001a0ea0000,0x200ded62c0be08baa0a3,0xa53488eac2920000a8cf,0xa19d81d40000208429a4,0x681762b421dea4980000,0x2cc868f3088e00002b1b,0xc2a9c83348948dac0001,0xe0334d5264ec62ce481b,0xc2bd40146c0a00000000,0x43574331ca8d506f229c,0x883800000000e32622e5,0x404e000000000001,0x1e8f80000,0x1a19a4072000180f2,0x60960000000000002d30,0x1e368000000000001,0x1aa12000000008188,0x228c00010d34000162de,0x42e600000001,0x4376000000016d702900,0xc8200000],#[0x36fca780000,0x141ac8c860000420a,0x1890de4ad433ae63c,0x48e00a42000000000000,0xe2f20000c259,0x1425e091a61b4,0xa2c54348000060e0]]
def g255D12 := limbs80 #[#[0x5c110e7d765979f59560,0x443fd5c510ff521443fe,0xff940482ff61d10bfd82,0x5c120ff960483fe54120,0x483f79cd20fdd73483fe,0xf7e65483df59520bfd84,0x61d20bfd86482ff61520,0x543df59550f7d52542ff,0xefd62583fe5c160bfd86,0x61d60efd76583bf59560,0x5c3df59570dfd725c2ff,0xf7d87597df60165dfd76,0x5c910ffd42442ffe0176,0x483ff55120ffd71483ff,0xffd65483ff5d120ffd64,0x5c960ffd62543ff5d920,0xf08a045000ffd805dbff,0x2492041c81831471020c,0x353f03a234b3062ca285,0xe6125bb5765314da48c4,0x7d178c75070b6cf68a64,0xab96692a8dc8a086480d,0xab37afbab6a71a2c9f09,0xe0ec4617061d0c8687b6,0x1a1c4785c1e043a880d0,0x868442e1423830f42c45,0x610058443e1a1c220b09,0x381507018588a3436170,0x486c2e0e02880842e34,0x68f092307c5e131f9a0a,0x2e3c32124d0d87c28591,0x4584c287b3412478e8ec],#[0xd121e0b0144a3d1b1218,0x7e68244c16028c452211,0x249a202b8b080b70814c,0x4644874721a029dc4616,0xd1e1246130580a3d168d,0xf0926880b8585f87c2a2,0x4b348f243619470cb0b8,0x160b8e200f0407584c28,0x83c2c8d1f0f850583c18,0x70b87866184e17061d05,0xf0651f1a183a161ae170,0x1d85c786c321a1b0b830,0x43617061d45a3c328c1c,0xca3e343e1706230ca3c3,0x1f9a1007861187b0b830,0x80a770b838f2687c2614,0xd1385c188c1e1e4d0c86,0x6870586b88c2e0c3a818,0x87c686c2e0f021d07c68,0x217114ac688c2e0d0223,0xb88a8234221a14830862,0x4218545a6a249f1d0b0,0x680e1d168c47a62243c,0xa892847474071e9a8927,0x3d189d890e2280e111f9,0x23c2a3e249a1e038545a,0xe16170f8626e2c328e02,0x3c471a230a8f8d282322,0x2287b0b830cc]]
set_option maxRecDepth 16000 in
def g255H12 := limbs80 #[#[0xc019d30020708234e000,0x9c70030810800400052,0x2148602007803bc405,0x801823002c36830880a3,0x30020c3b141021050024,0xe4f00304828050002c14,0x1003141c010c4dda,0xe0001ccb4838ea205282,0x28119f883e488949e614,0x741611910,0x6a49a000101d00000000,0xc1b96c722d2190c33a09,0x21c9d279c610001e0791,0xa02ad12302c2310d0e8,0x16681f0001c49da04000,0x89b1d28c214d24d288d4,0xa0000f138134d9a120dc,0x4e619e0001c00c000025,0x8668000087930c200032,0xc2ac00000000000e8ce,0x601c00020c2000,0x3d24800042a541080,0xbd21a00000007110a494,0xbd7006f00e4113841cb7,0x427d6340000b4d600021,0xcb009a41390140001,0xa5f94ca0d3c0fc4c4800,0xe4a0000314800000003c,0x5e01721bc000000f02c4,0x8a9a0850aee9300005a9,0x391d5921f83400034,0xdd8a491640c3a19798a6],#[0x21090a6a1ad814413,0x4845127326de20a29500,0xec01ba9a8c420000a6f1,0x4f002d8139e19b8218b1,0x4014c09000145424,0xbe330acec0001117d240,0x350000c019a23fe4ca07,0x24a780000001a069c,0xa0b545540000000d00a,0xbb800030f5826c000000,0x2ff02eb74121a19,0x7f0c40003112a0110930,0x23105182ec256e58a804,0xc23362f0000112021f04,0xa6043825ec438000b23c,0x24999630fa0002a31e82,0xb16a412703232cb81224,0x58633214802c800986ea,0xb7800080030083c49008,0x60d4000044fb8ba0001d,0xd192200000000000b490,0xc45a1d0001c570000381,0x1425305e7032c8285,0xc27600000007022c61e,0xc5020aa8204000000,0x284880000001e9600,0x283c88c80000000,0xb9099952b40000000000,0x25b9c2a49427434480e9,0xf309ca137825c082a238,0x8174000310,0x642c0004123000060e40],#[0x1c46cd0f00000000,0x30660000000000,0x250830383b3130c9bb4,0xd00000001a329b176280,0x318000143e00000005a9,0x1ddca8c81b1661f097c,0x3000000000001c9596e3,0x125e0001811614e2b7,0x62840000000b0e1e0f00,0x8270a07182d9b0e6099,0x330041306c6c58817b08,0x289c0006c60000001e12,0x141d089a83a8253a0d9,0xaa709a324421b5818919,0x486182b71958015c2648,0x4c1100974000407e742e,0x2a183400010280c11bc9,0x484cdbcb12e94de302a6,0x9050ec8a050ce83e0000,0x284050576097487088,0x10c90000565669840,0x91126894b992383804b2,0x2848000282,0x912b42e0000927502340,0x7a29a000000000000000,0x9bf073042dc010000081,0x682481eb8370000440fc,0x3000000000000000f116,0x970000a531314522c601,0x492a4ec88e026140439,0xd325749804a4c076a443,0x278000953200c19ba636],#[0xd0db07f00016048c,0xdd29580638450384e438,0xc9fa15a01104e680b509,0x28921280000c2f911250,0x7086b12b]]
def g255D13 := limbs80 #[#[0xefccbdf597ef39fdd73,0x70ffac1ff543fe907fd1,0x800ffaedff597feb8ffd,0x9e86c9744d8f82e8740d,0x160e04243c346a4a5487,0x46888583810c0a080e1e,0xb0d0c1c38187622160e0,0x160c2c446878583810f0,0x8b0184858f9a121c2a22,0x91a1a1e160c2c3c30587,0x160c3e687860e85838f1,0x7478583810b1f1a1a12,0x3810f1a1a160e042c3c3,0x23858]]
def g255H13 := limbs80 #[#[0x4044000104000c0b10,0x260000000002ca00000,0x572f48049c0000000002,0x7dc600000052a4000000,0x94000000000348,0x840014190000000c4e28,0x207400000000048,0x0,0x2ab02d800100a0001678,0xa20000000000000310e,0x0,0x6000000184b000000000,0x5168960e201c00000020,0x705000150000000014,0x44c00000000000000000,0x0,0xe04,0xca2000000,0x14ce000000000000,0xe090003d2800000000,0x0,0xf0080025400000000,0x91e803482910c,0x2080000924000000000,0x500005cc000000000000,0xe3,0x4b900,0x73380000000000,0x11880000aa5658000,0x2052000000286c000000,0x3a6,0x0],#[0x111800182c00000000,0x84200000000,0x50798980000000,0x934000063a,0x132af91500b8a2403000,0x79c6bc48000000000000,0x140d94c84604d200030,0x645400000000000000,0x40000000000000010110,0x1c70,0x0,0x39c000000000000,0x349521a310000000000,0xe0f800000141000000,0x8a8000519a29a9200000,0x1,0xc94e038000,0x7110000ca4000000,0x0,0x4150007b3393c00000,0x83000000000018213a00,0xe5748ab,0x82280000000000000000,0x298c001643,0xb0b8000000c9d000000,0x1c1600,0x0,0x8ac00000000000000000,0x727c,0x9a0000000000,0x2138000000,0xa0000000000000000000],#[0x18,0xc000000085700000000,0x7,0x0,0x40000000000003012000,0x325]]
def g255D14 (j : Nat) := if j=0 then 0xb08141811e687ff else 0
def g255H14 := limbs80 #[#[0xd12d1883bc8000c,0x384017e0400524b14000,0x200000000000301aa000,0x49c000000000000058,0x6b5000000000000,0x80000060a000c4000488,0xe8ec0c00000000e1,0x19504c0000]]
def g255L : Nat → Packing
  | 7 => (40,7,7,0,0,10,0,g255D7)
  | 8 => (277,6,7,0,0,14,0,g255D8)
  | 9 => (594,5,7,0,0,16,0,g255D9)
  | 10 => (444,4,7,0,0,16,0,g255D10)
  | 11 => (162,3,7,0,0,14,0,g255D11)
  | 12 => (44,2,7,0,0,12,0,g255D12)
  | 13 => (12,1,7,0,0,10,0,g255D13)
  | 14 => (1,0,7,0,0,0,0,g255D14)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 16 97 6 13 6 3 g255H8
  | 9 => lookupWord 134 2741 3 16 9 3 g255H9
  | 10 => lookupWord 302 1487 7 17 10 3 g255H10
  | 11 => lookupWord 231 1373 7 16 9 3 g255H11
  | 12 => lookupWord 91 499 6 15 8 3 g255H12
  | 13 => lookupWord 28 419 3 13 6 3 g255H13
  | 14 => lookupWord 5 59 1 11 4 3 g255H14
  | _ => fun _ => none
def g255 : Forest := ⟨255,14,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
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

private def wheelRows7Page0 : Array Nat := #[19108332572720,19262953492624,5914193036324,5914193036324,5914193036324,6051634087044,18713189552148,39603968958624,18713189552148,5776751985732,5570590409748,18713189552148,123764054450336,5652250366000,5914193036324,106674119794724,106674119794724,106674119794724,107206696509488,146308078765076,18713189552148,5914193036324,106674119794724,5914193036324,106674119794724,106674119794724,106674119794724,5914193036324,5914193036324,141858491891844,6051634087044,107206695723044]
private def wheelRows7Page1 : Array Nat := #[107206695723044,107206695723044]
private def wheelRows7 : Array (Array Nat) := #[wheelRows7Page0,wheelRows7Page1]
private def wheelRows8Page0 : Array Nat := #[18988071391312,19245773623440,18970891522128,19262953492624,114771189958666,39603961602096,5914193036324,106674119794724,6051634087044,141858491891844,5776751985732,5776751985732,5776751985732,6051634087044,5570590409748,88579682353344,5570590409748,107206703866016,158673544446144,18713189552148,5570590409748,39603968958624,39603968958624,71489747697732,141858491891844,106725660188720,19108332572720,106725660188720,123764054450336,123218585460772,123764054450336,18777865715973]
private def wheelRows8Page1 : Array Nat := #[22063515501573,22063515501573,18713189552148,5776751985732,71610008604720,71610008604720,71610008604720,141858491891844,5570590409748,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,158673544446144,158673544446144,110368848413701,106674119794724,106674119794724,106674119794724,106674119794724,141858491891844,107206696509488,18713189552148,18713189552148,5776751985732,141978752782384,141978752782384,71489747697732,141978752782384,18713189552148]
private def wheelRows8Page2 : Array Nat := #[18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,75939334587412,146308078765076,18713189552148,18713189552148,18713189552148,18713189552148,114771189958666,114771189958666,110368848413701,106674119794724,106674119794724,106674119794724,106674119794724,106674119794724,106674119794724,106674119794724,106674119794724,5914193036324,106674119794724,106674119794724,106674119794724,106674119794724,141858491891844,141858491891844,106725660172336]
private def wheelRows8Page3 : Array Nat := #[141858491891844,141858491891844,141858491891844,141858491891844,5776751985732,71489747697732,5776751985732,71489747697732,36490043195665,71489747697732,71610008604720,71489747697732,141978752782384,71489747697732,5776751985732,5776751985732,36490043195665,106725660188752,106725660188752,6051634087044,141858491891844,6051634087044,145427663978561,71610008601636,71610008601636,71610008601636,107206703866016,107206695723044,141978752779300,141978752779300,141978752779300,107206703866016]
private def wheelRows8Page4 : Array Nat := #[107206703866016,107206703866016,107206703866016,107206703866016,107206703866016,107206703866016,107206703866016,107206703866016,107206703866016]
private def wheelRows8 : Array (Array Nat) := #[wheelRows8Page0,wheelRows8Page1,wheelRows8Page2,wheelRows8Page3,wheelRows8Page4]
private def wheelRows9Page0 : Array Nat := #[79449378916362,5652246171696,5776751985732,71489747697732,6051634087044,141858491891844,18713189552148,79449378916362,79449378916362,142116193861824,18713189552148,79449378916362,79449378916362,75047037371397,71489747697732,71610008604720,141858491891844,71610008604720,71541288091728,18970891522128,71541288091728,71541288091728,158673544446144,18898126636068,158673544446144,18777865715973,22063515501573,22063515501573,22063515501573,22063515501573,18713189552148,18713189552148]
private def wheelRows9Page1 : Array Nat := #[18713189552148,75047037371397,71489747697732,141978752782384,71489747697732,71489747697732,71489747697732,71489747697732,141858491891844,141978752782384,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,18713189552148,114771189958666,114771189958666,22063515501573,110368848413701,110368848413701,106674119794724,106674119794724,106674119794724]
private def wheelRows9Page2 : Array Nat := #[141858491891844,141858491891844,141858491891844,79449378916362,79449378916362,75047037371397,71489747697732,71489747697732,71489747697732,71489747697732,71489747697732,71489747697732,71489747697732,71489747697732,71489747697732,71489747697732,36356915994672,71489747697732,71489747697732,71489747697732,71489747697732,141858491891844,141858491891844,36356915994672,141858491891844,141858491891844,141858491891844,141858491891844,79449378916362,72022331769024,71610008601636,142116193861824]
private def wheelRows9Page3 : Array Nat := #[141978752779300,107206703866016,107206703866016,107206703866016,142116193861824,142116193861824,142116193861824,142116193861824,142116193861824,142116193861824,142116193861824,142116193861824,142116193861824,142116193861824,114771189958666,114771189958666,114771189958666,114771189958666]
private def wheelRows9 : Array (Array Nat) := #[wheelRows9Page0,wheelRows9Page1,wheelRows9Page2,wheelRows9Page3]
private def wheelRows10Page0 : Array Nat := #[18713189552148,18713189552148,18713189552148,18713189552148,79449378916362,79449378916362,22063515501573,75047037371397,75047037371397,71489747697732,71489747697732,71489747697732,71489747697732,141858491891844,141858491891844,141858491891844,141858491891844,79449378916362,142116193861824,142116193861824,142116193861824,79449378916362,79449378916362,79449378916362,79449378916362]
private def wheelRows10 : Array (Array Nat) := #[wheelRows10Page0]
def cubTag (k i : Nat) : Nat :=
  match k with
  | 7 => let j := i - 6; (wheelRows7[j / 32]?.getD #[])[j % 32]?.getD 0
  | 8 => let j := i - 140; (wheelRows8[j / 32]?.getD #[])[j % 32]?.getD 0
  | 9 => let j := i - 480; (wheelRows9[j / 32]?.getD #[])[j % 32]?.getD 0
  | 10 => let j := i - 419; (wheelRows10[j / 32]?.getD #[])[j % 32]?.getD 0
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
theorem wheelProof7_0 : spanOK g255 7 0 6 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_6 : spanOK g255 7 6 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_38 : spanOK g255 7 38 2 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel7 : spanOK g255 7 0 40 := (spanMerge wheelProof7_0 (spanMerge wheelProof7_6 wheelProof7_38))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_0 : spanOK g255 8 0 31 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_31 : spanOK g255 8 31 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_127 : spanOK g255 8 127 13 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_140 : spanOK g255 8 140 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_172 : spanOK g255 8 172 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_204 : spanOK g255 8 204 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_236 : spanOK g255 8 236 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_268 : spanOK g255 8 268 9 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel8 : spanOK g255 8 0 277 := (spanMerge (spanMerge (spanMerge wheelProof8_0 wheelProof8_31) (spanMerge wheelProof8_127 wheelProof8_140)) (spanMerge (spanMerge wheelProof8_172 wheelProof8_204) (spanMerge wheelProof8_236 wheelProof8_268)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_0 : spanOK g255 9 0 3 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_3 : spanOK g255 9 3 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_99 : spanOK g255 9 99 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_195 : spanOK g255 9 195 32 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_227 : spanOK g255 9 227 96 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_323 : spanOK g255 9 323 96 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_419 : spanOK g255 9 419 61 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_480 : spanOK g255 9 480 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_512 : spanOK g255 9 512 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_544 : spanOK g255 9 544 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_576 : spanOK g255 9 576 18 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel9 : spanOK g255 9 0 594 := (spanMerge (spanMerge (spanMerge wheelProof9_0 wheelProof9_3) (spanMerge wheelProof9_99 (spanMerge wheelProof9_195 wheelProof9_227))) (spanMerge (spanMerge wheelProof9_323 (spanMerge wheelProof9_419 wheelProof9_480)) (spanMerge wheelProof9_512 (spanMerge wheelProof9_544 wheelProof9_576))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof10_0 : spanOK g255 10 0 58 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof10_58 : spanOK g255 10 58 96 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof10_154 : spanOK g255 10 154 96 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof10_250 : spanOK g255 10 250 63 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof10_313 : spanOK g255 10 313 96 := by
  apply spanOld
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof10_409 : spanOK g255 10 409 10 := by
  apply spanOld
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof10_419 : spanOK g255 10 419 25 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel10 : spanOK g255 10 0 444 := (spanMerge (spanMerge wheelProof10_0 (spanMerge wheelProof10_58 wheelProof10_154)) (spanMerge (spanMerge wheelProof10_250 wheelProof10_313) (spanMerge wheelProof10_409 wheelProof10_419)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof11_0 : spanOK g255 11 0 11 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof11_11 : spanOK g255 11 11 88 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof11_99 : spanOK g255 11 99 61 := by
  apply spanOld
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof11_160 : spanOK g255 11 160 2 := by
  apply spanOld
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel11 : spanOK g255 11 0 162 := (spanMerge (spanMerge wheelProof11_0 wheelProof11_11) (spanMerge wheelProof11_99 wheelProof11_160))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof12_0 : spanOK g255 12 0 2 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof12_2 : spanOK g255 12 2 31 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof12_33 : spanOK g255 12 33 11 := by
  apply spanOld
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel12 : spanOK g255 12 0 44 := (spanMerge wheelProof12_0 (spanMerge wheelProof12_2 wheelProof12_33))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof13_0 : spanOK g255 13 0 4 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof13_4 : spanOK g255 13 4 8 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel13 : spanOK g255 13 0 12 := (spanMerge wheelProof13_0 wheelProof13_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof14_0 : spanOK g255 14 0 1 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel14 : spanOK g255 14 0 1 := wheelProof14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelT : ∀ k ≤ 14, spanOK g255 k 0 (g255.levels k).1 := by
  intro k hk
  interval_cases k
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · exact wheelLevel7
  · exact wheelLevel8
  · exact wheelLevel9
  · exact wheelLevel10
  · exact wheelLevel11
  · exact wheelLevel12
  · exact wheelLevel13
  · exact wheelLevel14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 14 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_span (g:=g255) (top:=14) (i:=0) (before_sound K253 V253) g255G wheelT (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_52832

open PEqualNP.Outside.L_meta_52832 in
theorem PEqualNP.Outside.L_meta_52832 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
