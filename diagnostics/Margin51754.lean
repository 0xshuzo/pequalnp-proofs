import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_51754.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_51754
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffeffffffffffff,0xfffefffffffefffefffe,0xfffffafaeeeeaa00ffff,0xfffffffffffeffffffff,0xfffffffefffffffefffe,0xfffefffffafaeeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 4 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,7]⟩,⟨.or,[6,7]⟩,⟨.or,[0,1]⟩,⟨.or,[2,3]⟩,⟨.or,[3,4]⟩,⟨.or,[2,4]⟩,⟨.or,[8,13]⟩,⟨.or,[4,9]⟩,⟨.and,[15,10]⟩,⟨.and,[14,5]⟩,⟨.and,[9,11]⟩,⟨.and,[8,12]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 0, 0, 0, 0] : List Nat).getD i.val 0))

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
theorem g49P3_0 : block g49 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g49B3 : block g49 3 0 1=true := g49P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49T : checkedTables g49 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g49 0 0 0 = true)
  · exact (rfl : block g49 1 0 0 = true)
  · exact (rfl : block g49 2 0 0 = true)
  · exact g49B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49G : graphValid g49 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low49 : Lower true (varsX 49) (graphGoal 49) 4 := lower_forest (g:=g49) (i:=0) (hints:=4) (before_sound [] baseKnown) g49G g49T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
theorem g27P3_0 : block g27 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B3 : block g27 3 0 1=true := g27P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K49) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K49 V49) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K49 4 [(54,[80,32,50]),(85,[33,67,99,83]),(86,[16,32,67,99,83]),(99,[83,100]),(102,[32,83,100]),(114,[16,80,32,99]),(116,[32,65,99,81]),(212,[32,65,99,113,81]),(226,[16,80,32,99,116])]
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
theorem g51P4_0 : block g51 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51B4 : block g51 4 0 1=true := g51P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g51 0 0 0 = true)
  · exact (rfl : block g51 1 0 0 = true)
  · exact (rfl : block g51 2 0 0 = true)
  · exact (rfl : block g51 3 0 0 = true)
  · exact g51B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 5 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K27 V27) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K27 5 [(51,[]),(53,[33,84]),(89,[48,65,33,32,101]),(113,[64,97,33,50]),(139,[67,115,83,101]),(149,[33,116,84,101]),(150,[16,32,116,84,101]),(154,[16,48,32,116,84,101]),(166,[32,116,100]),(210,[64,97,32,50,49,117]),(225,[80,97,33,50,64,116]),(228,[80,97,32,49,66,116])]
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
theorem g147P4_0 : block g147 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g147B4 : block g147 4 0 1=true := g147P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147T : checkedTables g147 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g147 0 0 0 = true)
  · exact (rfl : block g147 1 0 0 = true)
  · exact (rfl : block g147 2 0 0 = true)
  · exact (rfl : block g147 3 0 0 = true)
  · exact g147B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147G : graphValid g147 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low147 : Lower true (varsX 147) (graphGoal 147) 5 := lower_forest (g:=g147) (i:=0) (hints:=68) (before_sound K51 V51) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K147 := extendKnown K51 5 [(147,[]),(153,[48,65,33,32]),(165,[33,84]),(178,[16,80,32,50]),(180,[32,65,49,83]),(201,[96,113,33,50,64,84])]
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
theorem g177P3_0 : block g177 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B3 : block g177 3 0 2=true := g177P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P4_0 : block g177 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B4 : block g177 4 0 3=true := g177P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P5_0 : block g177 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B5 : block g177 5 0 1=true := g177P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177P6_0 : block g177 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g177B6 : block g177 6 0 1=true := g177P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177T : checkedTables g177 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g177 0 0 0 = true)
  · exact (rfl : block g177 1 0 0 = true)
  · exact (rfl : block g177 2 0 0 = true)
  · exact g177B3
  · exact g177B4
  · exact g177B5
  · exact g177B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g177G : graphValid g177 (boundsBefore K147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low177 : Lower true (varsX 177) (graphGoal 177) 7 := lower_forest (g:=g177) (i:=0) (hints:=4) (before_sound K147 V147) g177G g177T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
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
theorem g55P5_0 : block g55 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B5 : block g55 5 0 1=true := g55P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact (rfl : block g55 4 0 0 = true)
  · exact g55B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K177) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 6 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K177 V177) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K177 6 [(55,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V177 low55 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x3ffffe03f90b59b81c7])),(BitVec.ofNat 152 (word80 [0x41a8251a0a458a02a1,0xa84a0a458a00b1839249]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfc00ffffc068db448e38])),(BitVec.ofNat 152 (word80 [0x8130362c0c891304c1,0x306c0c891340d3049249]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffff0000000ff02e7000])),(BitVec.ofNat 152 (word80 [0x5c0b8302f0e1c1701,0xc0702f0e1c0af02e36db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580a,0x280b00000190c686db6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x300c010202504504924]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := [(1,0,86,0,4)]
def g87A : List (List Nat) := [[],[16]]
def g87D4 (j : Nat) := if j=0 then 0x3f else 0
def g87L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g87D4)
  | _ => emptyPacking
def g87I (_ _ : Nat) : Option (Nat × Nat) := none
def g87 : Forest := ⟨87,4,fun i => g87Y[i]?.getD (0,0),g87C,g87A,g87L,g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P4_0 : block g87 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g87B4 : block g87 4 0 1=true := g87P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g87 0 0 0 = true)
  · exact (rfl : block g87 1 0 0 = true)
  · exact (rfl : block g87 2 0 0 = true)
  · exact (rfl : block g87 3 0 0 = true)
  · exact g87B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 5 := lower_forest (g:=g87) (i:=0) (hints:=1604) (before_sound K55 V55) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K55 5 [(87,[]),(103,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V55 low87 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(2,0,89,0,5)]
def g91A : List (List Nat) := [[],[96,65]]
def g91D5 (j : Nat) := if j=0 then 0x3f else 0
def g91L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g91D5)
  | _ => emptyPacking
def g91I (_ _ : Nat) : Option (Nat × Nat) := none
def g91 : Forest := ⟨91,5,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 1=true := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact (rfl : block g91 4 0 0 = true)
  · exact g91B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 6 := lower_forest (g:=g91) (i:=0) (hints:=67) (before_sound K87 V87) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K87 6 [(115,[83,100]),(117,[33,67,99,83]),(213,[33,67,99,83,117]),(214,[16,32,67,99,83,117]),(227,[83,100,116]),(230,[32,83,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)
def g118Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf007ffff87fff003ff,0xff87fffa0f5a40f801f])),(BitVec.ofNat 152 (word80 [0xa25114211008a1280a,0x201108822015a45294a5]))),((BitVec.ofNat 152 (word80 [0xfff801fff87ffffc00,0xfffffc0335af3f003e0])),(BitVec.ofNat 152 (word80 [0xc060580a0102c0302c,0x40a00108215832318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffe00007fffffff,0xf0007ffccfd11c007c1f])),(BitVec.ofNat 152 (word80 [0x80608c2223044130,0x4c22200c3c018a5294a]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb058130444c098240,0x9004c100c27c14a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc0601c000700e0380,0x8e0470211aa2098c6318]))),(0x0,0x0),(0x0,0x0)]
def g118C : List ColumnInfo := [(2,0,116,0,4),(4,0,114,0,4),(16,0,102,0,4),(32,0,86,0,4),(64,0,54,0,4)]
def g118A : List (List Nat) := [[],[82,100],[33,84],[33,65,97,81],[65,101],[65,98,81,33],[81,33,66,100],[81,98],[97,66],[97,82,65,66]]
def g118D4 (j : Nat) := if j=0 then 0x4fd5110 else 0
def g118D5 (j : Nat) := if j=0 then 0x101a0fd20fd10 else 0
def g118H5 (j : Nat) := if j=0 then 0xf0 else 0
def g118D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g118H6 := limbs80 #[#[0x6b000000005a0300,0xc23600000000610000,0x87002ed5000000009000]]
def g118L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g118D4)
  | 5 => (2,1,3,0,0,4,0,g118D5)
  | 6 => (1,0,3,0,0,0,0,g118D6)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g118H5
  | 6 => lookupWord 2 37 0 8 1 3 g118H6
  | _ => fun _ => none
def g118 : Forest := ⟨118,6,fun i => g118Y[i]?.getD (0,0),g118C,g118A,g118L,g118I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P4_0 : block g118 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B4 : block g118 4 0 1=true := g118P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5_0 : block g118 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B5 : block g118 5 0 2=true := g118P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P6_0 : block g118 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B6 : block g118 6 0 1=true := g118P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118T : checkedTables g118 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g118 0 0 0 = true)
  · exact (rfl : block g118 1 0 0 = true)
  · exact (rfl : block g118 2 0 0 = true)
  · exact (rfl : block g118 3 0 0 = true)
  · exact g118B4
  · exact g118B5
  · exact g118B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 7 := lower_forest (g:=g118) (i:=0) (hints:=18941248) (before_sound K91 V91) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K91 7 [(118,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V91 low118 (by decide +kernel)
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
theorem g151P5_0 : block g151 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g151B5 : block g151 5 0 1=true := g151P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151T : checkedTables g151 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g151 0 0 0 = true)
  · exact (rfl : block g151 1 0 0 = true)
  · exact (rfl : block g151 2 0 0 = true)
  · exact (rfl : block g151 3 0 0 = true)
  · exact (rfl : block g151 4 0 0 = true)
  · exact g151B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151G : graphValid g151 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 6 := lower_forest (g:=g151) (i:=0) (hints:=1860) (before_sound K118 V118) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K118 6 [(151,[]),(167,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V151 : Known true K151 := extend_ok (m:=151) V118 low151 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(1,0,154,0,5),(2,0,153,0,5),(8,0,147,0,5),(16,0,139,0,5)]
def g155A : List (List Nat) := [[],[64,49]]
def g155D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g155L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g155D6)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,6,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P6_0 : block g155 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B6 : block g155 6 0 1=true := g155P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact (rfl : block g155 4 0 0 = true)
  · exact (rfl : block g155 5 0 0 = true)
  · exact g155B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K151) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 7 := lower_forest (g:=g155) (i:=0) (hints:=67) (before_sound K151 V151) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K151 7 [(182,[80,32,50])]
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
  · exact (rfl : block g179 4 0 0 = true)
  · exact (rfl : block g179 5 0 0 = true)
  · exact (rfl : block g179 6 0 0 = true)
  · exact g179B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 8 := lower_forest (g:=g179) (i:=0) (hints:=68) (before_sound K155 V155) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K155 8 [(179,[]),(181,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V155 low179 (by decide +kernel)
def g203Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc03fe1fe1fff00f,0xf87f87ffff856420703f])),(BitVec.ofNat 152 (word80 [0x50282814404400a0a0,0x51011002098064049249]))),((BitVec.ofNat 152 (word80 [0x7fffc001ffe1ffff0,0x7ff87f01c9c9c381c0])),(BitVec.ofNat 152 (word80 [0x60b03058828042c0c1,0x620a01042181c98db6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffffe0001fffff,0xff80007ff233d69c0e07])),(BitVec.ofNat 152 (word80 [0x80c040600308830101,0x800c2208021380892492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf800000000001fffff,0xffffff80013c2ae00ff8])),(BitVec.ofNat 152 (word80 [0x50282811411140a0a,0x500050402c02724924]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0xce2917ff000])),(BitVec.ofNat 152 (word80 [0x60303001800180c0c,0x4604460846010724924]))),(0x0,0x0)]
def g203C : List ColumnInfo := [(2,0,201,0,5)]
def g203A : List (List Nat) := [[],[118],[48],[48,118]]
def g203D5 (j : Nat) := if j=0 then 0x3f else 0
def g203L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g203D5)
  | _ => emptyPacking
def g203I (_ _ : Nat) : Option (Nat × Nat) := none
def g203 : Forest := ⟨203,5,fun i => g203Y[i]?.getD (0,0),g203C,g203A,g203L,g203I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203P5_0 : block g203 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g203B5 : block g203 5 0 1=true := g203P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203T : checkedTables g203 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g203 0 0 0 = true)
  · exact (rfl : block g203 1 0 0 = true)
  · exact (rfl : block g203 2 0 0 = true)
  · exact (rfl : block g203 3 0 0 = true)
  · exact (rfl : block g203 4 0 0 = true)
  · exact g203B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203G : graphValid g203 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low203 : Lower true (varsX 203) (graphGoal 203) 6 := lower_forest (g:=g203) (i:=0) (hints:=99) (before_sound K179 V179) g203G g203T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K203 := extendKnown K179 6 [(211,[64,97,115,48,16]),(229,[80,97,33,115,67,64,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V203 : Known true K203 := extend_ok (m:=203) V179 low203 (by decide +kernel)
def g241Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff007fc7fc7ffc07f,0xfffffc7f91a1500ff0ff])),(BitVec.ofNat 152 (word80 [0x402010080080008101,0x1000800000001111111]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff8007ff87fff80,0x7f87ff878e3f20f00f0f])),(BitVec.ofNat 152 (word80 [0x824120910901090212,0x2109010062d02222222]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fffff,0x8007fff87b588f000ff0])),(BitVec.ofNat 152 (word80 [0x48241201212120404,0x14212001595004444444]))),((BitVec.ofNat 152 (word80 [0xe000000000007fffff,0xfff800000fe2c000f000])),(BitVec.ofNat 152 (word80 [0x170b85c25c245c2858,0x5805c1220fe2ceeeeeee]))),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x180c06006000603060,0x604602442002f8888888]))),(0x0,0x0)]
def g241C : List ColumnInfo := [(64,0,177,0,7)]
def g241A : List (List Nat) := [[],[117],[84],[84,116],[116,84],[116]]
def g241D7 (j : Nat) := if j=0 then 0x3f else 0
def g241L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g241D7)
  | _ => emptyPacking
def g241I (_ _ : Nat) : Option (Nat × Nat) := none
def g241 : Forest := ⟨241,7,fun i => g241Y[i]?.getD (0,0),g241C,g241A,g241L,g241I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g241P7_0 : block g241 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g241B7 : block g241 7 0 1=true := g241P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g241T : checkedTables g241 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g241 0 0 0 = true)
  · exact (rfl : block g241 1 0 0 = true)
  · exact (rfl : block g241 2 0 0 = true)
  · exact (rfl : block g241 3 0 0 = true)
  · exact (rfl : block g241 4 0 0 = true)
  · exact (rfl : block g241 5 0 0 = true)
  · exact (rfl : block g241 6 0 0 = true)
  · exact g241B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g241G : graphValid g241 (boundsBefore K203) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low241 : Lower true (varsX 241) (graphGoal 241) 8 := lower_forest (g:=g241) (i:=0) (hints:=4) (before_sound K203 V203) g241G g241T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K241 := extendKnown K203 8 [(241,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V241 : Known true K241 := extend_ok (m:=241) V203 low241 (by decide +kernel)
def g242Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe007fc3ff0fffc03f,0xffffff0ff1e21a00ff0f])),(BitVec.ofNat 152 (word80 [0x240900881220048480,0x8240022090c202111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff8003fff0ffffc0,0x3fe1ffff241fab0f00ff])),(BitVec.ofNat 152 (word80 [0x882209104402110109,0x842400200d09222222]))),((BitVec.ofNat 152 (word80 [0xfffffffc0000ffffff,0xc001fff01b9764f000f0])),(BitVec.ofNat 152 (word80 [0x304c12009844260602,0xb084802199260555555]))),((BitVec.ofNat 152 (word80 [0xffffff,0xfffe00001369f8000f00])),(BitVec.ofNat 152 (word80 [0xc1705c22e088b8282c,0x2c0170440329f8eeeeee]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0x18060030000c03030,0x30118088462084888888]))),(0x0,0x0)]
def g242C : List ColumnInfo := [(0,64,176,2,5),(32,0,210,0,5),(64,0,178,0,5),(2,64,176,0,4),(16,0,226,0,4),(128,0,114,0,4)]
def g242A : List (List Nat) := [[],[116]]
def g242D4 (j : Nat) := if j=0 then 0x5bd4941 else 0
def g242D5 (j : Nat) := if j=0 then 0x108404fd41 else 0
def g242H5 (j : Nat) := if j=0 then 0x90 else 0
def g242D6 (j : Nat) := if j=0 then 0x2c458bf else 0
def g242H6 (j : Nat) := if j=0 then 0xe else 0
def g242L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g242D4)
  | 5 => (1,1,3,0,0,0,0,g242D5)
  | 6 => (1,0,3,0,0,0,0,g242D6)
  | _ => emptyPacking
def g242I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g242H5
  | 6 => lookupWord 1 2 0 4 0 0 g242H6
  | _ => fun _ => none
def g242 : Forest := ⟨242,6,fun i => g242Y[i]?.getD (0,0),g242C,g242A,g242L,g242I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g242P4_0 : block g242 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g242B4 : block g242 4 0 1=true := g242P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g242P5_0 : block g242 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g242B5 : block g242 5 0 1=true := g242P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g242P6_0 : block g242 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g242B6 : block g242 6 0 1=true := g242P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g242T : checkedTables g242 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g242 0 0 0 = true)
  · exact (rfl : block g242 1 0 0 = true)
  · exact (rfl : block g242 2 0 0 = true)
  · exact (rfl : block g242 3 0 0 = true)
  · exact g242B4
  · exact g242B5
  · exact g242B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g242G : graphValid g242 (boundsBefore K241) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low242 : Lower true (varsX 242) (graphGoal 242) 7 := lower_forest (g:=g242) (i:=0) (hints:=289472576) (before_sound K241 V241) g242G g242T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K242 := extendKnown K241 7 [(242,[]),(244,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V242 : Known true K242 := extend_ok (m:=242) V241 low242 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff9,0x7261417c0b003e007c1f])),(BitVec.ofNat 152 (word80 [0x2a035012805216149,0x50600154090842108421]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff006,0x97e88c458507c00003e0])),(BitVec.ofNat 152 (word80 [0x44c12609b046424266,0x9760804581294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000001,0xd8c69299d1f8000f8000])),(BitVec.ofNat 152 (word80 [0x17003801c017838381,0xd0c49018d118c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffff2,0x4fe683ab80001f003ff])),(BitVec.ofNat 152 (word80 [0x180440220118000000,0x8e6828305294a5294a]))),((BitVec.ofNat 152 (word80 [1,0x1711a387760001fffc00])),(BitVec.ofNat 152 (word80 [0x6009804c0260040400,0x711028306a5294a5294]))),((BitVec.ofNat 152 (word80 [0xc,0xe9177e4005fffe000000])),(BitVec.ofNat 152 (word80 [0x800e00700380080800,0x28136e0004c6318c6318]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7),(2,0,117,0,6),(4,0,115,0,6),(64,0,55,0,6),(6,0,113,0,5),(16,0,103,0,5),(32,0,87,0,5),(66,0,53,0,5),(68,0,51,0,5),(17,0,102,0,4),(20,0,99,0,4),(34,0,85,0,4)]
def g119A : List (List Nat) := [[],[33,84]]
def g119D4 := limbs80 #[#[0x54d6110f865515358043,0x30e1554]]
def g119D5 := limbs80 #[#[0xf6aa9ac221ed95358043,0x3e3aa8a9887ad5516110,0xe7bb8acaa1cfb705954,0x809eee2b2c8767dcd549,0xaa479848c1]]
def g119H5 (j : Nat) := if j=0 then 0x10dcd else 0
def g119D6 := limbs80 #[#[0xd58443be580439f59741,0xd8553e7d0e439f59443b,0x9131fd50531bb58a53bd,0xd41bf59331bfd9131bf5,0x43bf58f41ef50f41ef50,0x3bfd8543bf59443f754c,0xbf58643bfd9543bf5954,0xf59243ef95243ef55243,0x55153fdd8553bf59643b,0x1800bf59253bfd9153df,0x29087e39198b4421b078,0xf36180ba5a2a1449c482,0x19c4b229087e3d9e0e46,0x1700f00461700c6242c0,0x41000005070070046,0xc10000810030000c10,0xc10c115284304104100]]
def g119H6 := limbs80 #[#[0xcab80d0000058e17a10,0xd641530052000094a]]
def g119D7 := limbs80 #[#[0xc43ffa0ff507fe63fd31,0x1fe53fea9ff90ffa87f,0x1604e362280f85d1f07c,0x8782c53120538a629207,0x18411ae0a18a481cc294,0x1038a61860a1462098b0,0x18f04145315]]
def g119H7 := limbs80 #[#[0xc1380004d1b2010e2000,0xe068,0x16400000000000,0x3c30000,0xad8994000008116c0000,0x734000032b000000008,0xf0000000000003eefd00,0x4a00070b52002c,0x46000002c595c0022c0,0x315018f5000000000,0x124000000000000f400,0x3da000d1f2000859c,0xa1c00003f]]
def g119D8 (j : Nat) := if j=0 then 0x874013f else 0
def g119H8 := limbs80 #[#[0x610000000000051c0000,0x348000000001,0x740000000000,0x3c000000,0x0,0x89000000,0x14400000000,0x80000000000000000000,0x22e0022,0x0,0x0,0x3220000000000000000,0x300000630000000009b0,0xf,0x15800003500000000e60]]
def g119L : Nat → Packing
  | 4 => (2,4,4,0,0,3,0,g119D4)
  | 5 => (8,3,4,0,0,6,0,g119D5)
  | 6 => (28,2,4,0,0,9,0,g119D6)
  | 7 => (9,1,4,0,0,9,0,g119D7)
  | 8 => (1,0,4,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 6 1 1 g119H5
  | 6 => lookupWord 3 17 4 8 3 1 g119H6
  | 7 => lookupWord 9 97 4 10 5 1 g119H7
  | 8 => lookupWord 4 137 0 9 4 1 g119H8
  | _ => fun _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P4_0 : block g119 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B4 : block g119 4 0 2=true := g119P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 8=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_7 : block g119 6 7 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 28=true := (@block_merge g119 6 0 7 21 g119P6_0 g119P6_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 9=true := g119P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : block g119 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B8 : block g119 8 0 1=true := g119P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact g119B4
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K242) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=1348) (before_sound K242 V242) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K242 9 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V242 low119 (by decide +kernel)
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
theorem g183P8_0 : block g183 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B8 : block g183 8 0 1=true := g183P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 8 := by
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
  · exact g183B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=1348) (before_sound K119 V119) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K119 9 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V119 low183 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffff8007fffffc03f,0xe1c3049387e000f00f0f])),(BitVec.ofNat 152 (word80 [0x140150350250148585,0x2143049104c111111111]))),((BitVec.ofNat 152 (word80 [0xffffff8007ffffc0,0x1a4f29807c400f00f0f0])),(BitVec.ofNat 152 (word80 [0x260260260360190909,0x9a4300805c4111111111]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000000,0x7718c2d9850f00f0000])),(BitVec.ofNat 152 (word80 [0x380b803803805e0e0e,0x3518c09985333333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff,0xc8137a47aa9f000000ff])),(BitVec.ofNat 152 (word80 [0x402c01401401600000,0x103a06a21666666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c7720000fff00])),(BitVec.ofNat 152 (word80 [0xb005805805801010,0x40c4224232ccccccccc]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006006006002020,0xa44160010888888888]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(1,0,214,0,6)]
def g215A : List (List Nat) := [[],[16]]
def g215D6 (j : Nat) := if j=0 then 0x7f else 0
def g215L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g215D6)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,6,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_0 : block g215 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B6 : block g215 6 0 1=true := g215P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact (rfl : block g215 4 0 0 = true)
  · exact (rfl : block g215 5 0 0 = true)
  · exact g215B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 7 := lower_forest (g:=g215) (i:=0) (hints:=1604) (before_sound K183 V183) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K183 7 [(215,[]),(231,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V183 low215 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff83ffffff07e4c,0x6860b6140007c1f07c1f])),(BitVec.ofNat 152 (word80 [0x50050802000210240,0x48003014210842108421]))),((BitVec.ofNat 152 (word80 [0xff80003ff07fff81c1,0xcbc118a800f83e0003e0])),(BitVec.ofNat 152 (word80 [0x602610041024009c1,0x4a4118006318c6318c63]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc0007ffffc83,0x9d3644441f00000f83ff])),(BitVec.ofNat 152 (word80 [0x480880048208800000,0x95240440842108421084]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000035,0x265c7923e000000ffc00])),(BitVec.ofNat 152 (word80 [0x901300090013021015,0x225049214a5294a5294a]))),((BitVec.ofNat 152 (word80 [0x44,0x90bf8bb000003ff00000])),(BitVec.ofNat 152 (word80 [0xe05c022e045c042004,0x90be83a39ce739ce739c]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x600430086008402a,0x8a020a108421084210]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(2,0,241,0,8)]
def g243A : List (List Nat) := [[],[116]]
def g243D8 (j : Nat) := if j=0 then 0x7f else 0
def g243L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g243D8)
  | _ => emptyPacking
def g243I (_ _ : Nat) : Option (Nat × Nat) := none
def g243 : Forest := ⟨243,8,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
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
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact (rfl : block g243 5 0 0 = true)
  · exact (rfl : block g243 6 0 0 = true)
  · exact (rfl : block g243 7 0 0 = true)
  · exact g243B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 9 := lower_forest (g:=g243) (i:=0) (hints:=68) (before_sound K215 V215) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K215 9 [(243,[]),(245,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V215 low243 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffe0ffe0ffff7222,0x914baa40000fc0fc003f])),(BitVec.ofNat 152 (word80 [0x940142004204403202,0x1432a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfe0000ffffffe0394a,0x8626748003f03f000fc0])),(BitVec.ofNat 152 (word80 [0x18058402800082380a,0x840250830c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad94,0xb0d84280fc000003f03f])),(BitVec.ofNat 152 (word80 [0x202600130411000990,0xb018408a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9bf00000003ffc0])),(BitVec.ofNat 152 (word80 [0xc04800240026048044,0x944a914514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc4000003ffc0000])),(BitVec.ofNat 152 (word80 [0x17008b808b8088171,0x18b08478e38e38e38e38]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x18010c010c0104401,0x42800460820820820820]))),(0x0,0x0)]
def g246C : List ColumnInfo := [(2,0,244,0,7),(4,0,242,0,7),(64,0,182,0,7),(128,0,118,0,7),(0,64,176,6,6),(16,0,230,0,6),(32,0,214,0,6),(2,64,176,4,5),(4,64,176,2,5),(18,0,228,0,5),(36,0,210,0,5),(66,0,180,0,5),(80,0,166,0,5),(96,0,150,0,5),(6,0,176,0,4),(6,64,176,0,4),(20,0,226,0,4),(34,0,212,0,4),(70,0,176,0,4),(82,0,164,0,4),(100,0,146,0,4),(130,0,116,0,4),(132,0,114,0,4),(144,0,102,0,4),(160,0,86,0,4),(192,0,54,0,4)]
def g246A : List (List Nat) := [[],[33,84]]
def g246D5 := limbs80 #[#[0x485304427c61f31c8110,0x443d454d514c110fc132,0xe15764c910e696254950,0x4c1208df835d9524421f,0xd697554930483d254d52,0x549504839a58d5254120,0x4838e5516354120d6b73,0xe097654d20e4d6354d52,0x54720c3f75551634823b,0xe4d6354d52c8237e0d76,0x4c9504c30fdd55458f20,0x4c3c65513254130f4952,0x5533254130dcb72cc950,0x4c930e3954d89504c3c6,0xd1f75551324c39359552,0x55132cc393595524cb30,0xcc39354d6254b30d1f75,0xdd9544c950c3f7555162,0x58d50d39545c3325430f,0xd39545c2635434b55372,0xdc5524cb9354d52d8132,0x8ca8f6036555132d4d53,0xdd55458e32e4d6354d52,0xc0c008df835c76054b0f,0x1a4c65d2b94496451b09,0x58aad4a9f4ca4d1a873c,0xe770b6daacf64b0d7ab7,0x3b1788c2e0aff7cbcdda,0xc12083c220840302,0x3040608000000]]
set_option maxRecDepth 16000 in
def g246D6 := limbs80 #[#[0x3b4a92a0904bd75d9110,0xe72a8a8261ce5515048,0xca5fbb2a9984ef725953,0x32c7acaaa065ae551600,0x4cb1eba2ca194bf76550,0x110c7ecaaa265d354d52,0x443f8a8e40887f331c8,0x8110bf2e790221fa54b2,0x30443f890a60885f975c,0x4c110fb26498221fc545,0x530443eca9a60886f962,0x54c110bf2ea98221be59,0x8950443bca92a0885fb7,0x7354110df2c6a8221be5,0xd9132442fdb8264885fb,0xf764c9109faec99221af,0xb58952442fdb82a4884f,0xfd7654910d7ec8a9221b,0x3fdd5624427fb9ac4884,0x7e9524c1209fee4b2a21,0x1f694d30483eca9a6090,0x6f9654c120f72a89824,0x417edd530482fcbaa609,0x905fb7354120df2c6a82,0x2413f5db31482fcb8662,0x6906ed6354920edaa6a9,0x9a413f5d9534836eb1aa,0xa6906dd6394d20bf2e12,0xb1a41bedc1634827ebb4,0xac6906bd5458d209fee2,0x6b2a413fdc5654827fba,0xaa3904fd76cc7209fee],#[0xa4b0e413f5d951c837ab,0xb1aa59076d5354b20dda,0xacaa9e41b758d53c8376,0xeb1ca7904fd7654f20cf,0xfee2b1e413f5da53c836,0x7fbaac7906bd5458f209,0xbf6e2a8261bed85504c2,0x3ed992a0987d93254130,0xdf6c4a8261de549504c,0xc3e699242985fb725413,0x30ebaa6a8a61bbd89214,0x4c27eb96c2985df73545,0x9309faebb0a61b754f61,0x24c3edb8264985fb704c,0xc930f3aa899261f35493,0x324c36fb2a64986dd654,0xcc930bbeea99261775d5,0x7324c36eb2e649879d54,0x554930ebaa6a9261775d,0x4f624c27eb8ec49867d6,0x75d8930d7aa9b1261b75,0x5ca534c2efb92a6984fd,0xf7159530bdee4b2a6177,0xbdc9654c376392ca984f,0xfd71d95309fee4b2a61b,0xf354932cc27eb96ca984,0x6dd654cb30f3aa899661,0x177dd532cc2eebaa6598,0x875d5354b30ddac4a966,0x619f59552cc35eb22a59,0x986dd5358b309faeca96,0xaa13fdd562cc35eaa2c5],#[0x4a84fd73d85509fae5b0,0x92a1cf55132543b6a926,0x64a85f970cc9509feec9,0x992a1cf5533254377b16,0x2c4a867f63549509faed,0x7b12a13f5c7625439eaa,0xa2c6a85ef7258d509fae,0xa931aa17e5c2635439ea,0xbb4c6a857d7598d50e7a,0xae5b1aa13f5c7635427e,0x6a96c0994fd71d81329f,0xbca7b0265b754f604cb7,0x7ebaec0996bd54d8132d,0xcfecaa9265d754d524ca,0xbb7b2aa4995ef7154932,0x2cfecaaa2657b5c6524c,0xcb3fb2aca9973f655513,0x329fae1b2a653fdc1654,0x8cb5eaa2c3196ed52586,0xe32ddac6a9465db54d52,0x38ca7ebb2a71967d6554,0x4d429feeab1c65af5516,0x5390b7aa9ac3215ef725,0x54e42dbac6a9c857bdc9,0x56390a7ebb2a72167d65,0x3d81529fae3b02a53fdd,0xcd6154aee39ac2a94fd7,0x53d85529fae1b0aa577d,0x5ca6354a7eb9ec2a967d,0xd71d8d529fae1b1aa57b,0xfdc56394afdb82c8a94f,0xbd73189549fae7b12a93],#[0x80b0038002deb9ec4aa5,0x3d83402c82501b818012,0xa05685505185004c8450,0x87b07587006886305b85,0x9b89809288d089888082,0x80b68b30ad8a80a089f0,0x8cb0c98c80c68c10bf8b,0xdd8dc0d88d70d38d00cc,0xec8eb0e78e40e28e10,0x8fd0fb8f80f68f30f18f,0xf90e10a9071019000fe,0xe11c91b1199181149111,0x92f12d92c12692312191,0x4594213e93b135934130,0x815495315194e14c9491,0x96716396216095d15b95,0x7d97a17897516f96c168,0xc18a9871859841829811,0x99919799619499319198,0xa79a61a49a119f99e19a,0x81b69b31b19b01ac9ab1,0x9c91c39c21c09bd1bb9b,0xe99e41dc9d91d19d01ce,0x81f69f51f39f01ee9ed1,0xa09205a042009fd1fb9f,0x1da1a218a17211a0e20a,0x22ea2b229a26222a1f2,0xa4123da3a236a35233a3,0x4fa4e24aa49247a46242,0xe25ca5b259a56254a512,0xf890d900c243040663a5,0x3028d284a304543c2150],#[0xa31289292438a62890c9,0x605230d8a2a2434a49a2,0x840300041003c1000810,0x420b09040030f26089b0,0x940420f06420f0904206,0x1043c0c20f030800100,0x42040208100c08300041,0x20800604020c00307080,0x1410606141000000040,0xc10304000141000c10,0x304000040001410,0x3040000c106043c0c200,0x20f04003040000001410,0x484402028c1000003c18,0x4003040010004441010,0x40050600100000,0x30410082050444100141,0x504000003001630406,0xc1000000000040208,0x4000001000c100005040,0xe2420008004003040150,0x460562430000402085,0x14106240854908830,0x5c105040030400000004,0x605c203040810014100,0x4000040c105040030400,0x8104040c100002040030,0x400004100000181000,0xd03080000610400]]
def g246H6 := limbs80 #[#[0x81208800880000070,0xc0000000014800000000,0x30968f001f08005a232,0x1634000000000,0x24ab5c00000000000,0x8f0e002c309ca0200000,0x3400002ba0000029,0x6cb00068c000000,0xc37a774f800000,0x9b800,0x146400000001f840,0x934000000,0x820ca000c1c000e1800,0x4205000000000c1000dc,0x6b41ef260000058bc2fe,0x50a00000620642456,0x900000186000a0600000,0x156400000000000f138]]
set_option maxRecDepth 16000 in
def g246D7 := limbs80 #[#[0xf55150af59330afd9110,0x59432af59032be58032c,0xc110fec8110bd586429f,0x510bf58910fe54110fe4,0x20fe54120fe4c120bf59,0xef55120bf58d20fb549,0xfb54b20bf58720bf5952,0xf59720ef55320bf58f20,0x4c930bfd8530fe54130b,0x4d30bfd8930f7cc930f7,0x130ef55130f794d30f75,0x30bfd9530bf59530ef95,0xf754f30bf58b30f74cb,0xbfd8550bf59730ef5533,0xfd8d50bfd8950df54950,0xd8132bf59432ef55032b,0x5132fb94932fb54932bf,0x532bf59532ef95132ef5,0x32fb54a32bf58632bfd9,0x2bf59632ef55232bf58e,0xbfd8152bf59642bf58e4,0xfd8d52df54d52bfd8552,0xd8954bf58e52bf58652b,0xc910efd8954ef18954bf,0x520ff4c520ff54910ff4,0x20ff54d20ff54520ffcc,0xff54720ffcc720ff94d,0xff48530ff94f20ff54f2,0xf4c930ff58530ff54530,0x54d30ff58930ff54930f,0x4d40ff54b30ff59530ff,0x950ff4c950ff58550ff5],#[0x50ff58d50ff58950ffcc,0x2ffd8132ff58132ff98d,0xff59132ff55132ff5493,0xfd9532ff59532ffd9132,0x54e42ff54d42ff54e32f,0x8d52ff58552ff58152ff,0xff59152ff98d52ff5,0x30d30b809607b059030,0x61e41c91991691471171,0x2fc2d32aa26c24a22820,0xd3eb3c93a037034031e,0xf51f4da4b849646d42f4,0x6226005d05ae58c56a54,0x4872670b6e26a467b64b,0xe85382a7f37bc7a17637,0x9799499208f78c789086,0x91a68a46a1d9ed9c49a9,0x9b25b0aaf6ae2ac7ab3a,0xbd4bb2b97b83b68b54b3,0xa6c7dc69c55c41c1fbef,0x3d41d26d0bcf7cd5cc1c,0xdf7ddcdc1da6d92d7ed6,0xa6e8be69e55e41e26e0b,0x8e08495006ee9edcec8e,0x32b24789271c01a20593,0x430310186071048a1818,0x2c1e14d858c4050e3091,0x552a31e212230928a1e3,0x60a4878c40303242478c,0xa8746244c24498658a8,0x8f10883024c42e911891,0xb950c11182022488d251],#[0xa911c00a28c0c0c80f14,0xc68d1518f10181803042,0x8b0910e8c60c10101805,0x10c8498848283223c52a,0x6401c64c888286892221,0x148c88a608e20c910c04,0x313464848d1518f11262,0x23182254202021602326,0x8a106891418508080a32,0x8c3ca112401460406344,0x51e5440a1000d146068a,0x80892a3172a901891430,0x952480a101012a286080,0x4123051714ca28300223,0x62430a18ba3101812618,0x8688c848302345464184,0x3982e111820200746509,0x42461014305080808046,0x470630509103092e1831,0x80892e3198c11141472,0x80e5c51a0c4050e28406,0x8b8c18201c480b8c1810,0xc25c50a60b8619080080,0x48a18262130c80c10100,0xe9450c2039910202030c,0xc21c126101cc88984430,0x960c309085090a1171c1,0xc1424624306604843c4,0x102a30c1853010f0a583,0x3a242316223c34300890,0x45c884182c0222111c28,0xcc15222518a44c044448],#[0x162a887882c205083170,0x885ca890c2950c1862a1,0x8889083a22a19812548,0x3034410c86182970c2a0,0x2a30cc17461844410d08,0x28214c08106048cc0418,0x5c22e5882110b95121c,0x1908806085c13]]
def g246H7 := limbs80 #[#[0xc08780a418b001a00004,0x7420a5d38c823e5d3010,0x159e060ea8d040760f02,0x78106774851401a0d020,0x801e02000361c900c004,0x6659150c0a70f0032682,0x86fe88ea0000000184a,0xf82975a8000000234ac4,0xe6137c188c2ede688387,0x1c3030aa492354eb7fb,0x5a000122ec70ad800000,0x81325c621012a4bc0192,0xc9ae436ec7e93924a040,0x49c18abac808fe12,0x6d33f30e120c57662326,0xf8e475870000000001b5,0x2785735600d964624f1a,0xde7c0e000b5e14cea6fb,0x80f302daa74c0652b204,0x6a22ccd4ba820bd8b091,0x9e0be51b1136f585a731,0x73a66cc7481d3a39abd1,0x4ce3b7b6e1f8d0462603,0x3791de6cac16227080a9,0x6c9a6100064d8446e336,0xa070000000a58639eae0,0x38e38693b34887557b1d,0xb78da873cf76b0000000,0x4f0700a8000000274322,0xa5c4a8000d7e091046e9,0x4000000d4bf0d58014,0xe3990c54e5b3d603eabb],#[0x8003c15f329ce0868981,0x42e00012db09636e744,0x644e3850f13000621000,0xce3d0000002583e1482,0x4a4e980008b9e21c85c6,0x5ec8e3024a88ca307df,0xd3fa21d0d6ec500008c9,0x251567c00008eac11637,0x824d90b5ced1863afe14,0x29692e80f811e66,0x56f58d193b3400060f80,0x67dd25eafc2cb84f48ac,0x89a53c921aa296ad53c4,0x409cd66ca46188001c3c,0x6bbb4ea44b058000000,0x5952c78a1d000566c00,0xd17605c5fe9d14f27a00,0x989047444000ad5d48be,0x62c3b2c4001b5cb6a555,0x64fb6b32cf4245bb8000,0x306ca2ccbe000,0x6742b4f2cea000355000,0x8415984f55eb46bd0640,0x20e48365c55a]]
def g246D8 := limbs80 #[#[0xf20fe907f4437ca9bd54,0x65fd50fea07fcc3fa61f,0xbfc85fd42ff197f4cbf8,0x780c001fd54ff297f54,0x318ae24c841bc5410833,0x419e1cd523438f6390d5,0x90451319e304a261a428,0x40d1c201828d1c2988,0x44c601468d0a24c710e5,0xa8114248e1906c642620,0x46a2620408019251838c,0xe39b19060e2c65126082,0x308bc21a630268518a40,0x1a60419038c34260648a]]
def g246H8 := limbs80 #[#[0x25010033021002360027,0xd10003001994222d0b00,0x5e79ccf110000002a,0xf46000000545,0xdaf0000,0x0,0xced61000000000000000,0x786b000a08e052623e01,0x56e000dc30000ae08,0x90d23352000000000000,0x93300000030c0006d0c,0x83000141f39000b2b00,0xa18000,0x0,0x3600000000000000,0x434000ba000011e000,0x542e755da450e9e9c880,0x966c5084472,0x26000a01000000000000,0xe4200073e2,0xa3800000000051fd4,0x43127000816000000000,0x20463b6b700071b73af,0x0,0xbc800024a000000000,0x549d000659d8fcc7cc50,0xf1000042ab5d0000007a,0x304e19dae519cdc9a73d,0x4c0016c000000a48549e,0xa25e8000000c5c0c256,0x231000000000000,0x8f17000000000ddf0000],#[0xb8a0000000002ca000a5,0x0,0x5d50000000,0x0,0x1300043222d000000000,0xf00000055b000000b4f2,0x50770a00060300000073,0x28409d47000000000,0xb120000000,0xd5a0007d885400,0x260000000,0x206d0d0,0xf4e000000c9c03546500,0x95d8200061a00000026d,0x50f000f21a,0xe19168000000000c1500,0x8d200000024d,0x42200074cac90,0x0,0xd5e000000000,0x55f0000000,0x56b6a000f1d00000000,0x3769ef53000000000114,0x72c21cec19295db000a,0x557000000c8900000,0xb000067824000b2f000,0x663000000f990000008,0x10200023c000d2000000,0xa9f000a4b000,0x3690000]]
def g246D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g246H9 := limbs80 #[#[0x580067a5a12800018621,0x80dc400000000005d9c,0x1d09611ce86000d78018,0x68a002a1923c6e,0x5fcc0000144800000000,0x751c00000000017458f3,0x26f95b]]
def g246L : Nat → Packing
  | 5 => (38,4,5,0,0,9,0,g246D5)
  | 6 => (198,3,5,0,0,12,0,g246D6)
  | 7 => (111,2,5,0,0,12,0,g246D7)
  | 8 => (17,1,5,0,0,10,0,g246D8)
  | 9 => (1,0,5,0,0,0,0,g246D9)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 12 127 3 11 6 1 g246H6
  | 7 => lookupWord 65 307 7 13 8 1 g246H7
  | 8 => lookupWord 39 397 4 12 7 1 g246H8
  | 9 => lookupWord 7 47 5 10 5 1 g246H9
  | _ => fun _ => none
def g246 : Forest := ⟨246,9,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_0 : block g246 5 0 38=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B5 : block g246 5 0 38=true := g246P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : block g246 6 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_12 : block g246 6 12 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_108 : block g246 6 108 90=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B6 : block g246 6 0 198=true := (@block_merge g246 6 0 12 186 g246P6_0 (@block_merge g246 6 12 96 90 g246P6_12 g246P6_108))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : block g246 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_7 : block g246 7 7 61=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_68 : block g246 7 68 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B7 : block g246 7 0 111=true := (@block_merge g246 7 0 7 104 g246P7_0 (@block_merge g246 7 7 61 43 g246P7_7 g246P7_68))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_0 : block g246 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_2 : block g246 8 2 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B8 : block g246 8 0 17=true := (@block_merge g246 8 0 2 15 g246P8_0 g246P8_2)
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
  · exact (rfl : block g246 0 0 0 = true)
  · exact (rfl : block g246 1 0 0 = true)
  · exact (rfl : block g246 2 0 0 = true)
  · exact (rfl : block g246 3 0 0 = true)
  · exact (rfl : block g246 4 0 0 = true)
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
theorem low246 : Lower true (varsX 246) (graphGoal 246) 10 := lower_forest (g:=g246) (i:=0) (hints:=287376704) (before_sound K243 V243) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K243 10 [(246,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V243 low246 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfee622179108552a18,0x4000003f000fc003f03f])),(BitVec.ofNat 152 (word80 [0x28e420049000452218,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0xb82ac8b252235093,0x40000fc003f000000fc0])),(BitVec.ofNat 152 (word80 [0x4ca82a48b002034093,0x45145145145145145145]))),((BitVec.ofNat 152 (word80 [0x1ecb5d48083808263,0x8003f000fc0000fc0000])),(BitVec.ofNat 152 (word80 [0x71ec20948082808223,0x830c30c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe400c92dea4161526,0x80fc000000003f000fff])),(BitVec.ofNat 152 (word80 [0x49206a0101124,0x8a28a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x16a6d08378928e4,0x3f00000000003ffff000])),(BitVec.ofNat 152 (word80 [0x80004a4908150808c0,0x14514514514514514514]))),((BitVec.ofNat 152 (word80 [0x3e552b025c00c55c,0x80000000ffffc0000000])),(BitVec.ofNat 152 (word80 [0x125523025c000544,0x38e38e38e38e38e38e38]))),((BitVec.ofNat 152 (word80 [0x191c1206588680781,0x7fffffff000000000000])),(BitVec.ofNat 152 (word80 [0x1181204108200400,0x20820820820820820820]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(2,0,245,0,9),(4,0,243,0,9),(64,0,183,0,9),(128,0,119,0,9),(6,0,241,0,8),(66,0,181,0,8),(68,0,179,0,8),(0,64,176,7,7),(16,0,231,0,7),(32,0,215,0,7),(1,64,176,6,6),(2,64,176,5,6),(4,64,176,3,6),(17,0,230,0,6),(18,0,229,0,6),(20,0,227,0,6),(33,0,214,0,6),(34,0,213,0,6),(36,0,211,0,6),(80,0,167,0,6),(96,0,151,0,6),(130,0,117,0,6),(132,0,115,0,6),(192,0,55,0,6),(19,0,228,0,5),(22,0,225,0,5),(37,0,210,0,5),(81,0,166,0,5),(82,0,165,0,5),(98,0,149,0,5),(144,0,103,0,5),(160,0,87,0,5),(194,0,53,0,5),(196,0,51,0,5),(145,0,102,0,4),(148,0,99,0,4),(161,0,86,0,4),(162,0,85,0,4)]
def g247A : List (List Nat) := [[],[33,84]]
def g247D5 := limbs80 #[#[0xc388dea39659543d0541,0x550e83b5c90eb2b02a1a,0x2caa1c47bb06a787dd96,0x930c088ef62d4f0fbb]]
set_option maxRecDepth 16000 in
def g247D6 := limbs80 #[#[0x7010f96165609815c043,0x9163cc531e1c61965605,0x5e998458f314c7a95845,0x4c72779659584cc531ab,0x4350531ea56196350d41,0x596550d414c76979658d,0x7a958658f4350531d8de,0x58531da565963d0d414c,0x6550d614c72d79858d43,0xd59758f4358531c9de61,0x531cb566163d0d614c74,0x58d614c7475975974358,0xa59d16358531e35ea174,0x19b56a67458d614c6e55,0xd614c6e55a5a11635853,0xa116358531b3569e8458,0xb46809458d614c6ad5a8,0x14c6ec5a22516358531b,0x16358531b956949458d6,0xe61655d1614c769794a5,0xc76556564e7458531e1d,0x458531d9559593a11614,0x163e05434c7475975968,0xa956458d81d0d31ea559,0xd31e2761d6458f434c7,0x4591634c687fa661d65d,0x7a15d16458d31b2768e7,0x31ba668084591634c7c9,0x91634c6e95a12116458d,0x4e458759131ba3688845,0xc3de5b9161d644c71b79,0x644c70bf96e518759131],#[0x95839d131c6de63915d2,0xfe9176616744c725f965,0x4c707f96595839d131a4,0x845d93186fea58421176,0x1d6458f43cc713d95e12,0x687fa661d65d0f31e276,0x58f31b2768e7459163cc,0x9159574cc6c9da79d164,0x7fa661d659d331e1de1b,0x541c1fe596560e74cc68,0x50f41507a958658d43d0,0xa859543d0541d8de5965,0x1cade598650f41506b37,0xf41507a956460d63d054,0x5954358541c9de596560,0xa52616350d6150727798,0x1507a979858d4358541e,0x54358541e8d2616550d6,0x6516390d61507a379859,0x7635656524358541da5,0x358541ba56927358d615,0x5949cd61506e95a3a516,0x63565e518358541d8d59,0x8541d8d59594a0d61507,0x3e054350747597596835,0x7a15916350d41ea55916,0x41ea5e1963e0543506e9,0x543507a37865978150d,0x15d96350d41cad65b86e,0xe8de1b9159543507c97a,0x43507a37a1e196550d41,0x8d8190d41ea559163606],#[0x75d98458e435078d5765,0x50723f965958490d41e2,0x801cd41d275d9949cd63,0x1b9159473507973a1595,0x7877a1655861cd41e1d6,0x50f41c8fe59656127350,0x8659543d07c1d7559163,0x7f97e196550f41c1f65f,0xf41f075d97558d43d070,0x59543d07c1da55d96350,0x97e196550f41c8f65f86,0x1a4fe9d865d543d0723f,0xe43d070bf97e198650f4,0x6116390f41e2761d6458,0x8fe596561243d0789d76,0x3d0687fa661d6590f41c,0x9655cf41f075d5645cd6,0xe5f8659573d0707d97e1,0x87a73a15958010d61c1f,0x510d61e99e8565608435,0xd636054358787587e456,0x874875958150d61e3521,0xd6187daa48760543587,0x458d43586e97a15d1635,0x9a02516350d61ba56867,0x61ba56849458d43586e9,0xd14358763565e457450d,0x7e456550d61d8d595919,0xa1faa087595435878778,0x43586a77a161d6550d61,0x1d6550d61a9d68787595,0xd65991e1d43587875a1e],#[0x5878d77458d8190d61c3,0x815cd61f85e8565d0e43,0x57849d17358727565653,0x745d6564e749cd61c4f6,0x5d161e0f595849d27358,0x656057010f2756564f81,0x996458d435c043e5c6a1,0x43d1ee596550d7010fc,0x50d7010fc9b96591435c,0x96595435c043f4669165,0x3b5ce85935957010fc5b,0xd7110f87b98619655c04,0x595435c443f255916350,0x25e596350d7110f47796,0x110fd15a3595435c443f,0xd655c443f0de596550d7,0xe89945957110e977a864,0xf87798619655c443b59,0x350c43f075d56458d431,0x1765954310f89f875916,0x7d97e196550c43a1faa,0xc43c1fe5f865954310f,0x65914310f07e98655765,0xf87e196450c43b27aa17,0x43e27e9b875914310f89,0x954310fc1d766516550c,0x85d96550c43e47e1d945,0xe17e1f865954310ec5ea,0x4310f85fa6e1d6550c43,0x557650c43f07691955d9,0xd5db9160d6510f45e986,0x10f877a1615815d843d1],#[0x63dc543b1de859361576,0x87765977150ecd5a1dd9,0xfc1f765974390d43b1d6,0x54d43ca765986d0e4350,0x6360a5350e8bfa461b76,0x6f765958294d43ea3591,0xd43d17ddb935965350f8,0x5916350ee99a024d6458,0xa224d6458d43ba568493,0x3b87694935916350ee8d,0x96350e8bfa65d78458d4,0x5938258d43d8765564e0,0xa5e85855916350fa1d95,0x350ee1da52616458d43b,0x8458d43ce6615902116,0x615912116350f69b7664,0xf697766448458d43ce5,0x559543da569991211635,0x787dd56550e17ea921d7,0xfda9e1f765954385f6a,0x9543d1dddb9160d6550e,0x460d6550f43f76251835,0xf7664a8359543d0fddb9,0x43e17ddb83a0d6550f46,0xd6550e735a1a5383595,0x4e4f765954398f69a94e,0xb1ee8187dd96550f61f9,0x6550ec77a161f7659543,0x1c875954391f6a787dd9,0x7ddb84e0d7650e17fa96,0x90e99fa4617835d943e2,0x65d0e43e2761d7659343],#[0x99875974390ef0fa2651,0xee1fa661d65d0e43a97e,0xd0e43f07e99875974390,0x975974390f91d9861d65,0x9d8761976d0e43bc5e85,0xe43e27e99875db4390f8,0x5916390f89d745938258,0xa1e19655d243b27e8574,0x3cd66159020d6454e87d,0xd6454f1d987640835915,0x6488359153cd56159120,0x7361d9220d6454f34d85,0x454e35fa96148359153c,0xd645ca53877ea58720d6,0x619845917294e5cda7e4,0x4e5cfa3661645ca53e2b,0x359253d665d19020d649,0xd9020d6494f4d9766408,0x4d5766448359253c7661,0x9253d635d19220d6494f,0x220d6494f4cd76648835,0xfa961c8359253c7361d9,0x63b17e8d945d96594e1d,0xd6458f2d98564083591,0x46488359163cb5615912,0xcb36159220d6458f68da,0x7458e9bba55d1801d163,0xd5801d163e2ee9974600,0x5659936047458e9f3a15,0x58e9b7a55d1811d163cb,0x811d163e2de997460474,0x85756087458e1f7a95d5],#[0xf0bf98e59741d163a79e,0x9d163c2fe9b985d07458,0x484304e00389d86dd183,0x7e0f01c8360660aa13c2,0x1662b453896120228420,0x63746b8d11963145f8b9,0x8c8910c20c4007d0f41c,0xb195d2985189a92f2524,0x98d30e604bd9752de5a4,0xd36e6c4d59a533e664c9,0xce784ed9d539e724e19b,0x84505a053fe7e4f99ed3,0x51da3545e8a511a1d42e,0x5a654be96529a4d48e90,0x9551ea2541a7d4ee9c53,0x57eae559aad54ea854da,0xeba571add5aeb4565ac5,0x6589b0d60ec057daf55d,0xa1b3d66ecc595b2563ec,0xb6d6ced85adb5569ed25,0x8744e71c5b856fede5b9,0xbaf5de8bcb78aefdd73a,0x4a06406800fe9fa3e37,0xa1e4368610aa1241e831,0x147c8d71962fc5989110,0xb79632ae52c9491d2224,0x9c336e6accf99330e5ec,0xf4868dd0aa093fa76ce7,0x46a5d45a7f4e699d2da4,0xc3580adf5a6b1d5daaf5,0x5b0b55692cf598b25632,0xbbcb77eecdc8b856f2db],#[0x6d8970a60ebfb7def8de,0x9832d654c9d9232163cc,0x345684cfd9e33966cccd,0x8eebdb5b5361eb2d43a4,0x31e41c6b8a70edfbbdf7,0x10721b09e1c1b8321f,0x2000000000000024100,0x40400000000000000002,0x41000000202000000000,0xf02081e0,0x0,0x0,0x0,0x0,0x0,0x0,0xa82000001c040000000,0x1404000000000,0x2a0800000000000000,0x1e080000001504000,0x41010000000000000000,0x30202001,0x3040400000000,0x2a080000000000,0x7081784080f0810000,0x0,0x201c2058202f08178408,0x40080000080100000100]]
def g247H6 := limbs80 #[#[0x12c00001280370160000,0xe2000000]]
set_option maxRecDepth 16000 in
def g247D7 := limbs80 #[#[0xb1a8298e78609815c043,0x63ad58658d414c7d2ac8,0xd16358531cba43acaa0a,0x14c79aee8b1ac298f355,0xab2ae8b0a63ad78458d6,0x2c698f1d5977458531e3,0x87d86594744c793ae8b2,0x6458f31c3fc32caba263,0xc72f2cac00e998f275d1,0x32ca3a66396d6560874c,0x998e1f655861d331c3ec,0x798597415070ff0cb2ae,0x58541f4ab1a86b0a8337,0xc6acba1ac2a0f8d59543,0xc6a1a83c7565dcd61507,0xe8fe196550d41e4ebb2,0x5608735072f2cac00e6a,0xd41c3ec32ca39a8396d6,0xaecb1a87a0e1f655861c,0xa1e83a3f8659543d0793,0x275917358f41e8eb2ce7,0x435870ff0cb2ae7a0f,0x1d3ab2b0221ac3a79656,0xeb2886b0e9b5958210d6,0xac387f87595435870fb0,0x5958190d61d6ab1b0321,0x43587c3acba1c86b0e9d,0x3ab2f02b9ac3a7565607,0xae8b0e9d595819cd61d,0x7a7565606745874eacbc,0x6715c043eb8b2ae2b808,0x10fab2cb39ae021f5c59],#[0xcbacab8087c797659570,0xe021d5ee5d655c043abc,0x79955d97010eaf32d3aa,0x15c043eb8b2b02b8087c,0xfae2cb40ae021e7c6198,0xa86b8087d996450d7010,0x21f1e619655c043eacb2,0x659c97110facacab92e2,0xc443e9ab2ce8b8887d65,0xeb2eb2ae221f1d5d9655,0xab8887577975957110ea,0xf1d655765c443abacb4e,0x50d7110fb2ac6a1ae221,0x43e3ac32cab8887d3565,0x2abb4e221f1d5d9659c4,0x1887c9d765914310f8eb,0x75d96550c43ccfc3ac8a,0x94310f2bf0eb2a8621f1,0xe8eb2ce921887c5d955d,0xbb48621f175d96590c43,0x8787d875d96510f8bb2a,0x457659443c3fc3aecb28,0x610f0fb0cbb4ea21d1fe,0xec2f02bb08787d856057,0xee2a1d1f657815d843c3,0x3b9902116350f93ac8b1,0x8458d439dac8908b1a87,0xf53ac9c12c6a1e2fddb,0x8908b1a8779990211635,0xca1d1f6477659543bcac,0xd875974390f33f09c1ae,0x58e43ccec3aeda1c87d1],#[0x2f2cac04e721f275d164,0xcaba48787d865967390f,0x1c5f65f8359653c3fc32,0x120d6458edb32041ac8b,0x163b66c9106b22c76d59,0xae8c08e8b1e6e5d1801d,0x39acb1bf985d07458f36,0xdd64684dcd658bfcc2e6,0x8f314c64fb2d426e6b2c,0x1deac22c798a63ed5645,0xcb266298eed61164cc53,0xa633f598593314c75eb0,0x66264cc531ddac24c998,0x314c76eacac266298cfd,0xcab1a86a0a633f796613,0x1a8298fcd5954350531f,0x3bb58650d414c7b6aeca,0x94350531ddbc3286a0a6,0x4c6f6f2ca1a8298ded65,0xb2e86a0a63f9563d0d41,0x8298f6d5db4350531f9a,0xb596d0d414c776b0da1a,0x350531f5ab22c6a0a637,0x7daac8b1a8298ebd6196,0x2c6a0a63f959458d414c,0x98fb56196350531fcb4a,0x93991414c6f6f26b2282,0x531bdbca2eca0a637b5,0x6f28bb28298f6d251765,0x6b0a639f4985d9414c7b,0xf9d5954358531f6ab1a8,0xd0d614c67ef30a1ac298],#[0x31f3ab2e86b0a63ed563,0x31a1ac298d7d65f43585,0xa63cf57458d614c67eb,0x55d16358531d7bc22c6b,0xd614c7dace8b1ac298fb,0xf6b422c6b0a63ed58458,0xb1ac298fb52516358531,0x63ed69458d614c7dab28,0x957458531f6bca2c6b0a,0x14c6def2cba2c298f9d5,0xbcc2e8b0a63cf7965d16,0x2c298df564e7458531cf,0x775959d1614c7ceacb3a,0x8458531b7acb4e8b0a63,0xc6fab27422c298f9d595,0xad08b0a63e7565a11614,0x298dbd65a8458531bbac,0x598a11614c6beb2f422c,0x50d31deab1f02a1a633f,0x76cc9c0a8698eed59381,0x2a1a63b7565e05434c7,0x8fa75916350d319facb7,0x1991434c75bf0cb1a869,0xd31d3fc32caa1a637b59,0xb30bb28698d6fe517650,0xa1a633f791619434c63f,0xed59181d0d31deab1b03,0x7434c76eacac0e8698e,0x1f4eb22c7a1a639f5766,0xcb1e8698de7e5163d0d3,0xa639dd8758f434c75bb0,0x61d65d0d31cdec3ac9a1],#[0x434c6b7f28bb68698e5f,0xffcb30fa1a639f79161f,0x22c698cfd6538158d318,0x3cbe74591634c797ae8b,0xe7458d31a7fcb2e8b1a6,0x4c6afb2b3a2c698d7764,0xcc4e8b1a634fd969d163,0xc698fb55938158d318fe,0xd591591634c6fab29c0a,0x458d31f4eba2c8b1a63e,0x7d3ce8b22c698f375d16,0x2c8b1a63cdf74591634c,0x98fa7e116458d31f4e42,0x915d1634c6dbf2cba2c6,0x8d31e6fcb2e8b1a63dd7,0xbb2d3a2c698dd7656745,0x8b1a633dd989d1634c6d,0xdf56448458d31becc810,0x211634c6f9b24422c698,0x31bebc8b08b1a6375d95,0x9422c698df56468458d,0x1a635dd97a11634c773f,0xd6478359131eebc8ae93,0x1644c69ff2cba2c898cf,0xe5fcb2e8b2263db7915d,0x3a2c898de764e7459131,0x634fd96dd1644c6b7b27,0x458759131adfca30eb22,0x44c737f28c3ac898e7de,0xfcb30eb22631ff9461d6,0xac898d6f6528759131c7,0x1fd93e1d644c67bb27c3],#[0x74991319fbc8b0732263,0xc737f30ba4c898f6de45,0x32caba2639f79161e644,0x898d6fe51765d131d3fc,0x565e05744c71ff0cbb2e,0x5d131afacb702ba263d7,0xbef22c32e898f1fe1965,0x73a263bd79160e744c6,0x8e775d9839d131daeb2b,0x6616744c67bf2cc1ce89,0x131adfca2ed3a26397d7,0xacac1ce898e3f619769d,0xbb2631ff9660e744c72f,0x6f610845d931afaca702,0x11764c6bef22c22ec98e,0x1aeec9d08bb2635f591a,0xb422ec98e6fe12845d93,0xe63e9d6458d43cc6afb2,0x5d96450f31d6fc32c6a1,0x43cc74ff0cb2a8798f2f,0x4eb22c7a1e638ff865d9,0x1e8798eb761963d0f31f,0x3cbd7659343cc73bb0eb,0xd65d0f31cdec3ac9a1e6,0xcc71fb0cbb68798e5f61,0xcb30fa1e631fd985db43,0xc798f2f5d16458f318ff,0xff965d163cc797ce8b22,0x458f318fecc2e8b1e634,0x69fb2d3a2c798d7764e7,0x2c8b1e63e9d7459163cc,0x98fa79d16458f31e6eba],#[0x965d163cc79bee8b22c7,0x8f31e6fcb2e8b1e636df,0xbb2f3a2c798db765a745,0x6b26635dd97a1163cc6b,0xf2f5d974593318fecbf0,0x5d164cc69ff2cba2c998,0x31e5ebb4e8b2663cbf96,0x2dba2c998d6f65e74593,0x26631fd98dd164cc69fb,0xf6528759331c7fcb30eb,0x974cc74ff0cb2ae998d6,0xebbc8acaba6638ff865d,0xb2ce998f1fe19655d331,0x638fd865da74cc72fb0e,0x95839d3318ffcb30f3a6,0x4cc63ff2cc1ce998e5f5,0xab1a87a0a83d77915977,0xe82a0fe598d43d0541fc,0xbb58650f41507e6acaa1,0x43d0541bdacb287a0a83,0x77ab06b1e82a0dede59,0x32c7a0a83eb56458f415,0x2a0cfd66163d0541d7ac,0x59498f415077ab0731e8,0xd05419facc4c7a0a837b,0x6eacac1e82a0eed59183,0x86b0a833f79660f41507,0xf9d5954358541f6ab1a,0x350d615067ef30a1ac2a,0x541ddbc1a86b0a83eb56,0xf30a1ac2a0eed2614358,0xb0a83ed56390d6150776],#[0x9d5964358541bdaca486,0xd61506deb2d21ac2a0f,0x1f5ab1e86b0a833f5989,0x6b1ac2a0fb55cd635854,0xa83cf77358d61507dace,0xa516358541f5aca2c6b0,0x61507ceacab9ac2a0fad,0xdaca4e6b0a836f7965cd,0x9ac2a0f9d5967358541b,0x37b79460d61506deb2d3,0x28358541f3ab2b06b0a8,0x507ceacb41ac2a0ded65,0xcbd06b0a836f596a0d61,0x86a0cfd6628358541afa,0xd663e05435077aac7c0a,0x150d41ddab2702a1a83b,0x67eb2dc0a86a0edd5978,0x2c6a1a83e9d6458d4350,0xa0dede456450d41e6ebb,0x865954350757f0cb2286,0xd419fbc8b0ca1a83a7f,0x2cc7c0a86a0fe558f815,0x2a1a83f3565e0543507f,0xeede1b8150d41ddac370,0x58d43506f6b2dc0a86a0,0x41d5fc32c6a1a83cbd76,0xecb1a86a0fe56456350d,0x1a83e9f8658d43507d3a,0xfe196550d41f9bc8acaa,0x943507b6f22bb286a0f8,0xd5fc330ca1a837b79161,0xc3286a0eede458650d41],#[0x83bd5636064350776f23,0x958190d41ddab230321a,0x35073eaecc0c86a0edd5,0xec22c721a83e9d6458e4,0x486a0f375d96390d41dc,0x3bd985924350757b0cb2,0x8490d41ddbc8b0921a83,0x737aecc2486a0ecf595,0x32ed21a833bf96612435,0x6a0f2f5d963d0d41c7ec,0x7915974350757b0cb1e8,0x58d41f5ab2302b1a83f3,0x76d08c0ac6a0eed61181,0xe6b1a83e9d645cd63507,0xfa75927358d41e6ebb2,0x69cd63506f3b2939ac6a,0xd41e5eb26e6b1a83cdd7,0xf22b22c6a0d3f65b7358,0xb1a83eb79159163506de,0xfd6478458d41bcec9d08,0x1d635079ef22bb2c6a0c,0x1aeec9d0eb1a833bf946,0x9c3ac6a0cef6538758d4,0xa833f791612635063fb2,0xe458798d41ddbc8b0931,0x73507aef22b28e6a0e7d,0x3fc32cab9a83abf86591,0x24e6a0e3fe19765cd41d,0x33bd985927350757b0cb,0x5849cd41ddbc8b0939a8,0x50737aecc24e6a0ecf59,0xc32ed39a833bf9661273],#[0xc8a0cfd64f8159141c7e,0xb593e056450776b07c0a,0x359141bdbc8b06b22837,0x6b7b2f41ac8a0ded6468,0xf02bb283bb79160e6450,0xa0d7de45835d941afac9,0x91a0d76506b7f28c1aec,0xf41adeca506bb2835f5,0xbaeab1a87a0fa7591635,0x6a1e83cdd7658d43d07a,0xf4f5d56450f41eaebacc,0x59543d0757f0cb2287a0,0x41abecbacaa1e83a7f86,0xcbaa87a0d5fe5d6550f,0x1e8397f865d543d072fb,0xfe5d8650f41c7fc32eca,0xd43d0797aecb1a87a0c7,0xf8ebaac6a1e83abf8658,0xb1a87a0fa75d96350f41,0x83f1d7598d43d07d3f0c,0x5d6550f41f1fc32caa1e,0x3d06e7f2eb2a87a0dcf6,0xec32eaa1e83d3d765d54,0x287a0ecfe197550f41d9,0xd3d955d943d0757f0cbb,0x7650f41e5fc32eca1e83,0x757f0cc3287a0d6fa63,0xbb0ca1e835bf9761943d,0x7a0cefe5d8650f41cdfc,0xd8458e43d07d3ac8b1c8,0x90f41eaebaac721e83b9,0x3bb0eb1c87a0f375d963],#[0xc921e83abd8659243d07,0xcef6616490f41cdec3a,0x661243d0767acac2487a,0xf419dfcb30921e839bd7,0xb2eb2c87a0e5f61d6590,0x21e8357f9759643d06af,0x3f6197690f41cbec32eb,0x1e43d063fb30bb487a0e,0x1e5ebb2c7a1e831ff966,0x8b9ac7a0eaf61963d0f4,0xe83d5d755cd63d07d3ac,0x5917358f41e6ebb2e6b1,0x63d069ff2cb9ac7a0f2f,0x6fcb2e6b1e83cdd645cd,0x9ac7a0fa75927358f41e,0x3cdd769cd63d07abaeb3,0x56458f41e6eb24e6b1e8,0xd07c7aeab22c7a0f1f5d,0xbaf08b1e8379d93a1163,0xc7a0c7f65f8458f41cbe,0x7d875d563d078faecbaa,0x658f41cbfc3aeab1e839,0x71ff2cc3ac7a0f1f6557,0xd0eb1e835dd93a1d63d0,0xa0f575d57398f41abeca,0x7561263d072faeac24c7,0xcf41cbec3aeb31e83b3d,0xff0cb2ae7a0f4f5d5645,0xab9e8357d9759573d074,0xe5fe19755cf41abfcbac,0x59573d071ff0cbb2e7a0,0x41d5ec32c939e83c7f86],#[0x2eb2ce7a0d5f65d659cf,0x9e8397d865d673d06aff,0xf619649cf41c7ec32ed3,0xd64d06b7f2ec1ac9a0e3,0xcbec2b06bb6835bd97a0,0x41aeda0d6f652835db41,0xc3e7791594435872fb0b,0x958150d61f6ab1b02a1a,0x35873e90ec0a86b0f9d5,0xbc8ac6a1ac38ff8758d4,0xa86b0fa75d16350d61f6,0xcdf7458d43587d3ce8b1,0x6350d61f4e4a2c6a1ac3,0x879b90eb1a86b0fa7e51,0xa6e6a1ac3cdf8758d435,0x6b0dede457450d61adec,0x5919d143587c7acaba28,0x50d61f1eb2ce8a1ac37b,0xbbb27ba286b0daf65a74,0xcaa1ac3e779159543586,0xe9f61d6550d61e3e43a,0x7595435878ff0eb2a86b,0xd618ff4c10ea1ac3a7f8,0xf2cc3a86b0cfde458750,0xa1ac33f591e1d435865f,0x7d6478750d6197ecb70e,0x6435871fb2dc3a86b0e,0x1e6fba2c721ac39f7746,0x7ba486b0eb76116390d6,0xac38fd86dd243586bbb2,0xe456590d61d3eb2b0921,0x435874fb0eb2c86b0f9d],#[0x7ec3ac7a1ac3af563607,0xac6b0f9de4565d0d61c,0x36f7915d163586deb29c,0xe7458d61b7ac8ce8b1ac,0x586cfb2b3a2c6b0db764,0xcc4e8b1ac34fd979d163,0xc6b0dbe6408458d6197e,0xed9221163586deb22422,0x458d61b3eca908b1ac36,0x6deb23422c6b0dbde458,0x508b1ac36dd93a116358,0xb0f9d597815cd61d5fc2,0x655d1735867eb29c0ae6,0xcd61afac8ce8b9ac3c7d,0xfb2b3a2e6b0e6fe12745,0x8b9ac34fd969d173586a,0xe7d5d1819cd61d3eb2f0,0x9d2735871fb0cba4e6b0,0x61cdec24e939ac35dd93,0x2b3a4e6b0f1f596749cd,0xa2c3a7d6561273586afb,0xf595839d1619fac9f02b,0x57010faf32eb2ae021e9,0xeecb1a86b8087d7b9759,0xa1ae021f5e595435c043,0x875fb9650d7010ebf32c,0x59435c043eeccb286b80,0x10f9f2c8b1ae021f76e,0xdc8acab8087d79915957,0xae021f5e64d655c043eb,0xd79985957010faf726b2,0x655c443ebdcc2cab8087],#[0xfaef2eb2ae221f5d65d,0x8acab8887d7591595711,0x221f7558d435c443ebbc,0x56550d7110fb6ac8a1ae,0x5c443afacb286b8887d7,0xb6b2ca1ae221d7de5943,0xc6b8887db79650d7110f,0x1f5d649655c443e7ab22,0x35957110faef24b2ae22,0x443ebbc9acab8887d759,0xf28b2ae221f5d651655c,0xb8887d75985957110fae,0xa75916350c43ebbcc2ca,0x8d4310fabaeab1a8621f,0x3cefc3ac6a1887cdd765,0xcb2a8621f1f5d96550c4,0x88797f875954310f4ff0,0xe5d6550c43abecbacaa1,0x4310f2fb0cbaa8621d5f,0x7ec32eca188797f865d5,0xb28621e3fe197650c43c,0x7c7d955d94310e3fd30b,0xd8650c43c7f4c2eca188,0x10e3fb2dc3a8621c7fe5,0xc3ac8a1887e9f8659143,0x8621fc76516550c43ecf,0x5f875954310fcbf0cb2a,0x650c43e6ec32eca1887d,0xebbd30bb28621f37e197,0xb0ca1887cde985d94310,0x21d77e5d8650c43cefc3,0x96e1d4310f3bf0fc3286],#[0xc43ceecb70ea18875dd,0xbac939ac621e77e5b875,0x8b1887c7d755916310f9,0xd3f65a7458c43c7fc3ac,0x6056510f8fb2abb2ca21,0x43e3ebb702b2887c7d76,0xecc1aca21ddde4583594,0x288757f9760d6510f8fa,0xf65f8359443e3ebb706b,0xd6510f8ff0ebb2ca21d5,0xcbecbb0d3a88797f8761,0xc2aec21f1fe5d855d843,0x87c7f916157610f8fb22,0x4d855d843e3ec9b0abb0,0x150fd3ac8b1ae2a1f1fe,0xfc32c6b8a87cdf7658d7,0x2e2a1f2fdd9645c543d6,0x3be989917150f57f0cb2,0x655c543e3fbb2cab8a87,0xf1ff0cbb2e2a1e9fe19,0xb2c7b8a87e9d6458f715,0x2a1f2fdd964dc543e6fb,0xf765977150ef6b23326e,0xdc543afac8eedb8a87c7,0x97ac8b1ee2a1e3f61b76,0xc7b8a87cdd6458f7150f,0x1f5de4565dc543e6fc32,0x5d0e4350f8ff0cb2ee2a,0xd43ecebb68721a87f1d6,0xb0da1c86a1f67ddb4390,0x21a87e9d6458e4350f73,0xe7e4d6490d43e6fbb2c7],#[0x964350f57b0cb2486a1d,0x3c7ec36ed21a87c7f765,0xcb2c86a1fa7dd96390d4,0xa87abd86dda4350fc7ee,0xdd96554d43f4eb22c6a9,0x5350ebbf26bb2a6a1f1f,0xfbc8b0ca9a878fd86dd9,0x14a6a1cefe518654d439,0x7bad6460a5350f79ac6c,0x58294d43dd73230529a8,0x50f3daecc14a6a1edb59,0xb22c729a879ef7660a53,0xa6a1eaf6196494d43f4e,0x7f765965350eebf26b2c,0x694d43d3ec32cb29a87c,0xe3ff30bb4a6a1d77e4d7,0x704b1a878fd86dda5350,0xa1cdf6578258d43d5eb2,0x915916350edbd2f31ac6,0x8d43f4e49ac8b1a876bf,0x3f26b22c6a1fa7a4d645,0x8b1a873be972116350fd,0xcef6478458d43c7fbb70,0xe116350f37aebc22c6a1,0x43d5fbb708b1a879bf75,0x31baac6a1d3fe597558d,0x1a878ff76e156350e3fb,0x75918158d43a7ec8eecb,0x56350ef3928c0ac6a1fa,0xf4eb2702b1a8779f9460,0xc12c6a1fa75918258d43,0x8775d95e096350fd3ac9],#[0xd56458d43daecaf04b1a,0x350fd3eeab22c6a1fa75,0xfc2ac8b1a87e9d855916,0x2c6a1fa72616458d43f4,0x7d5912116350efb32042,0x8458d43be6c9108b1a87,0xebbd2e422c6a1dd7654,0x2908b1a8779d91211635,0x6a1fa7dd88458d43dcec,0xf84a116350ef3d2e422c,0x58d43bcec8f08b1a87b9,0xdbf2cbaac6a1fa7ddb84,0xab1a877d7916156350e,0x1de7e518558d43bce4a3,0x4dd96350edbb23bb2c6a,0xd43cef43aeb31a87e9f9,0xd0fbacc6a1cf7e617598,0xb2a873dd92a1e6350f3b,0x3fddb83595439deca706,0xd56550f8feecbaacaa1e,0x3cbe43aeab2a8767f965,0xdbaacaa1f1fddb755954,0xa8797f87dd56550ecfb2,0xe1f7659543c7ec3eecb2,0x6550f8fb2bbb2caa1e3f,0xfdc830eb2a87c7f95dd9,0xacaa1cfde4587595439,0x7c7f76e056550f8feecc,0xc8359543e3fbb106b2a8,0x50eeef22c1acaa1d5fa5,0xca306b2a8773c9460d65,0xcaa1f1fdd98359543b9f],#[0x5f83a0d6550eedb2541a,0x359543e3fbb506b2a87b,0xee7b29c1acaa1d5fa5e8,0x706b2a8773e94e0d6550,0xa1d9f6477659543e3fbb,0x87dd96550fcbf27bb2ca,0x9543e3ec3eecb2a87c7c,0xfb23bb2caa1f1fe1f765,0xcb2a87c7f91dd96550f8,0xf1fa637659543e3fc9ee,0x61d6550f2fb0e43acaa1,0x43bbbc8b0eb2a8777b90,0xcbb2eaa1e5fe1e87595,0xb2878fd86ddb7550f1ff,0x7ddb835d943dcfc2706b,0x57650f1feedc2aeca1f3,0xaeec9706bb2875bf9460,0xc1aeca1f67e13835d943,0x879df85e0d7650f3bb0b,0x41855d9438fec9706bb2,0x650ebef22c2aeca1d7ee,0xfc2707bb2875df936157,0xae521f37591635c643dc,0xd6f925957290f9bac8b1,0x63d0e43f4eb22c7a1c87,0xf1fb0cbb68721eb7619,0x3ac9a1c87e9d76593439,0x721fc765165d0e43dcec,0xd875974390fe3f28b2e8,0xd0e43d6ec32eda1c87b5,0x7bb30bb68721e7761d76,0xcba1c873df9661f4390e],#[0x1fc7e4565d0e43f8ec8a,0x75974390fe3b0eb2e872,0xe43f8fcbacba1c87f1d9,0xb0ebb68721fa761976d0,0xa1c8779d985db4390fb3,0x6765987d0e43bcfcb30f,0x916390fb3f2cc3e8721f,0x3a7fcb2e8b1c87cbd745,0x9c12c721eb75938258e4,0xc877d5919516390f3bae,0x65e5458e43b6ecb4a8b1,0x6390edbf22b22c721d77,0xefc92e8b1c875df915d1,0x2ac721f37e597458e43a,0x79df876156390efaf22c,0x98655243aefcbb0ab1c8,0x90e7bf26c32a921cfbe4,0xbb3032a487b756560654,0xa921dcfe516595243cfa,0x7d875965490f4fb0cb2c,0x695243c7ec32ed2a4879,0xe3ff2cc3ca921c7f6617,0x702b248737d95e056490,0x21c7f65f8159243c7ebb,0x92e0d6490e3fb2fc12c9,0x9243ceebaf06b24873dd,0xbb2fc1ac921e77dd7835,0xab24875ed92dd56490e7,0xd3f65b7559243adeca6e,0x5d96490e3fb2fc2ac921,0x438ffc8b0eb24874ff92,0xcbc0ae921e3fe5987592],#[0xa4871fd96e057490f2fa,0xfe19655d243c7fc32cab,0x16590e3fb23c32e921f1,0xbbbc8b06b2c873dd93e1,0xc22cb21ddbe498459643,0x8777591a116590eebf26,0x4f8459643d9fc2508b2c,0x590eeef22c3acb21dd76,0xbc8b0abb4871ff966137,0x4a6a9dd7e4d6494d53af,0xa7d865925354f67b08b2,0x6494d539becc2c929aa7,0x4e6fb31324a6a9ecf612,0x22a8b1aa737f96612535,0x8a9df66408359153d9fc,0xd9220d6454efab2241ac,0x59153daec2906b22a77c,0x6bb0bc1ac8a9e7761c83,0x6b22a79de87e0d6454f,0x9ed76578359153cefba7,0x61d6454e9fb2dba2c8a,0x153afbc8b0eb22a75fb9,0xf28c3ac8a9d7be498759,0xbb2a75bd94a1d6454eb7,0xf3e4d645ca53cbfcab09,0x917294fb5ae8b22e529d,0x3e76bb2c8b94a7dae745,0xeb22e529d7b65d645ca5,0x4a7dad749917294ebdf2,0xe59745ca53af6cbcc8b9,0x7294ebdb2d3a2e529d7b,0xf7c9ac8b94a7ced6458d],#[0x22e529f6b611645ca53a,0x7ced865917294fb5d08b,0x1645ca53af6cc2c8b94a,0x94ebdb27322e529d7be6,0xcc4c8b94a7dad8499172,0xe529e7b619845ca53af6,0xed96a117294ebdf2cc22,0x458e53e5eba2c8b1ca75,0xe9fb2d3a2c729f2f9d16,0x906b24a77d99020d6494,0x29df36488359253beac8,0x7620d6494fb3ae841ac9,0x9253ceec3906b24a7cdd,0xbaedc1ac929f675d3835,0x6b24a79dd87e0d6494f9,0xc7f65f8359253cef43f0,0xe0d6494f3bae9c1ac929,0x539eecbf06b24a79dd97,0x2cba2c929f2f5d974592,0x24a7cbf965d16494e9ff,0xf6557659253e5ebb4e8b,0xd6494f1ff2cc3ac929f1,0xadeca50eb24a75ed92a1,0xb2ae929e3fe19765d253,0xa78fd865da7494eaff26,0x517659653e3eca2ecb2c,0x694ebbf26c22ed29f1fa,0xe422c8b8ac797d856117,0x2e2b1eafe11645c563d5,0x5ed921d17158ebf3203a,0x745c563abeca8e8b8ac7,0x8f37908ba2e2b1c7fa60],#[0xc4e9b8ac79bf849d1715,0x4b1cf764e84dc5638fec,0xd855937258ebbb273a2e,0xdc963cbec2ae9b92c7a7,0x2fb0b3a6e4b1d7764e74,0x9b92c71fd989d37258f,0x1f1f61564dc9639eec9d,0x3a137258f2fb0ac26e4b,0x963cbec2d09b92c75dd9,0xf26ba4c6b1d3f65a84dc,0xb22c76dd939d26358edb,0xbd6448359163b7cc8106,0xd6458eddb2441ac8b1d,0x3a7f4b906b22c767d952,0xa41ac8b1db7648835916,0x2c76de9720d6458f5bb0,0x6528359163d6fc1d06b2,0x6458edbb25c1ac8b1daf,0x7bc8aeab22c7e9f74e0d,0xaac8b1daf2517559163b,0x767d9521d6458ed7f28b,0x5801d163cfcba3003a2c,0x58f37ae8c08e8b1e7e5d,0xba3023a2c7bd59360474,0xe8b1e7d5d5811d163cfa,0xed746087458f5eb2cc08,0x41d163cf6bab043a2c79,0xe3ff30ba0e8b1e5f6157,0x2e83a2c75bf955d07458,0xb1e6fe61741d163e5fcb,0x985d47458ebef22ba8e8,0xd163d6fc3706ba2c71ff],#[0xbaebc1ae8b1cf764b835,0xaba2c79df75e0d7458f3,0xd6f251755d163afbc8ae,0x60e7458fb3ee8c1ce8b1,0x639efc8b073a2c7add86,0x2cc1ce8b1cf7e49839d1,0xa2c75bd91dd27458f5bf,0xf61b749d163cdec2ee93,0x67458eb7b31ba4e8b1f2,0xadfca2eb3a2c75f7915d,0xbaee8b1c7f663759d163,0xc73f7916177458ebef22,0x4e84dd563afbc8b0bba2,0x35972fb08b98e6b2cf76,0xec26e739acba7f966107,0xcc013c01980120000cb,0x80f701b602e804f00820,0x180b50158028204bc089,0x3f207880e301b4033a06,0x828004e6095c11d821a0,0x3c18102e605940ab814b,0x7180dc01aa034206560c,0x40907e40f6c1e483a80,0xec24d047e08c41104215,0xaa214c028a04f309b812,0x5d30b7816942c485720,0xc432d063e0c4e18182f5,0xdf01b9836786ae0d2419,0x87890eda1d4439807140,0xec40d07f90fba1f043d2,0x19822ac447887310b820,0x89531278248047f88e31],#[0xd44d40996131225dc4b2,0x43228084f309d9138e26,0x8a8c14f429b45288a301,0x85780ade15a22ae8551,0x6ae2d505a60b3516322c,0x8b6616c62d805ae8b5a1,0x445c48b8116f22db05b4,0x75e2e9c5d20ba117322e,0x8bd217942f085df8bb71,0xcc5f80bed17c02f745ea,0x8182ffc5fe0bf917ec2f,0xc3e186c30b86108c191,0x4463d0c6818ac3138623,0x9cc33506660cbf194632,0x8d131a2034206800cf81,0x846a50d471a7434c8692,0xb1c36186bf0d761adc35,0x8dac1b4836846cc8d911,0x346e28dc21b7436dc6d7,0xbcc378c6ed8dd31ba037,0x8e091c0237e46f88dee1,0xbc7160e241c423878708,0xc9a39287210e3f1c6e38,0x8e7a1ce4399472c0e551,0x8074c0e951d1a3a0073e,0xd863aec7598eb01d503a,0x8ee61dc63b8076c0ed01,0x587870f061dfc3bc4774,0xe723cc47948f261e463c,0xf5c1ea83d307a48f411,0x1c7bf8f771ede3d9c7b2,0xf543e9c7cd0f921f143e],#[0xfcd1f8a3ef47dd0fb21,0xb87f58fe31fb63f607e8,0x1840107fe0ff41fe23f,0x902f2044407c80b900f2,0x408241045208440fc81b,0xf041d4836906520b041,0x10a02130425484690852,0xf085c90b6216642c0854,0x1aa433486510c7218842,0x90fd21ea43b487510e22,0xa0890111822204420882,0x28c450c89d9133225644,0x116922c245648a8914e2,0x508c6118422f845d08b6,0x36446bc8d3919f233846,0x91d5239047148e111ba2,0xb08f491e623c647808ee,0x40a48088fd11f723de47,0x1228244a486090a92122,0x389259248248048f491d,0x4f649cc938126324c049,0x929e252c4a3894312832,0x3896312be25624aa4950,0x5c44b7c96e12d925ac4b,0x930525f04bd497412e52,0xd4999132a26444c54986,0x6924d189a19340267a4c,0x136c26c84d849ac93512,0x489c7938726fe4df09ba,0x77e4ec89d513a227344e,0x93ec27c84f5c9e793c72,0x5ca05140727fe4fdc9f7],#[0x87e50dca179422283450,0x145d28aa5148a2514472,0x34a42947d28ea51c8a35,0x956528ca501498292052,0x14c4298252f8a5b14ae2,0xa8a7114da29a4533ca66,0xa24543ca8114fa29e453,0x953a2a6454a8a91151a2,0x6caa9954b2a905500a9e,0xae855c4ab715662abc55,0x95882b0a5608abd15772,0xb8ad595a32b36564cac5,0xb8456fcade15b92b6c56,0x15d12b9c572cae415c52,0xc8af515e22bb4575caea,0xc16580cb0015fd2bea57,0x162e2c565878b0b160e2,0x50b2616492c8c590cb1b,0xcda59a8b3396642cb859,0x968b2d0659ecb3c16702,0x9cb5216a12d3c5a6cb49,0xd8a5af4b5a96ad2d545a,0x96e32db65b60b6816c82,0x24b8316fe2dec5bb8b75,0xe805cccb8b970f2e185c,0x176d2eca5d74baa97522,0x60bc817832ef65dccbb8,0xf6c5eb8bd597a32f405e,0x97e82fca5f60be317be2,0x4cc0598032ff65fe0bfa,0x6260b8c159823303660,0x1854308e60fcc1e18343],#[0x24c3e187430ce617cc2e,0x14e627cc4b988f311862,0x98d431986310c5e18af3,0xd4c7418e531ba6368c6b,0x23a6440c84190031fa63,0x193b326664c0c9699253,0x98cac995132926518c9f,0x3306640cc4198532e665,0x99cf338466d4cd699a53,0x38d0099f433d8677cceb,0x48a6908d1a9a2d344068,0x9a7234d46988d2a9a4d3,0xc4d549aa135286a30d3f,0x5ee6ba8d6e9ad5357c6a,0x9b4236746cc8d901b093,0xb4dad9b5336966d20da2,0x72a6e20dc29b8236f46d,0x1bc2376a6eb4dd01b9d3,0x4dfc9bec37c86f70de5,0x87070c0e141c20381c70,0x1c7938ba7140e241c403,0xcce559ca33936724ce43,0x9d47374e681cc8397672,0x1d1c3a287430e849cf23,0x30e9f9d373a5e749ce92,0xad47574eaa9d523a9e75,0x9d8d3b0a7608ebd1d723,0xe0ed59da33b407674eca,0xbc07760eea9dcd3b8a76,0x9e033bf677ccef59de83,0xb8f131e1e3c2c784cf05,0xc9878fcf1e1e393c6278],#[0x1e833d0079ccf309e593,0xa4f509e993d2c7a38f43,0xdd47b9cf6f9ed23d807a,0x9f033df67be0f7a9eed3,0xccf959f1e3e227c38f85,0xee87dc4fb49f573e8a7c,0x9fce3f6e7e94fc99f863,0x350001ff83fe07fa0fed,0x56808d0102018402a80,0xa0534096810d01da0334,0xd1038a06e40d6818d02d,0x12e8251046208440f881,0xa0c4417882d105620a44,0xa906ea0d541a4833d063,0x20683ed07c20f041da83,0x213a425a848108c21104,0xa90b1215a429a85290a1,0x33886510c62184430285,0xa1bf436e86bd0d3a1a44,0x950eea1da43ae873d0e3,0x3f287d90f9a1eb43d087,0x2212441e881d0ffa1fc4,0x911d2232445e889d10d,0x4ca898912d2257449489,0x2292450a89f513aa26d4,0xf515d22b245548a9d14d,0x5ca8b7516aa2cd458a8a,0xa2f445e28bb9175a2e84,0x41184230545fa8be917b,0x65c8cad191a31b46268c,0x234746888cf119ca3314,0xa11b0235846aa8d491a5],#[0x7028de51bb236e46d68d,0xa39f47248e3d1c623894,0x151dea3ba47648ea91d3,0x7bc8f6d1e9a3cb47908f,0xa3f747de8fb11f4a3e64,0x6120aa412481e901d1ff,0x87690cd215a423483690,0xa45948a29139225a43e4,0xe9239246a48ce9191230,0x94492552492485490491,0x24c5497a92d5256a4aa4,0x9926f24db49a69341264,0x9f493dd27a24f149dc93,0x25224a34943528525074,0xd2a0253d4a6a94c9295,0xaae95512a625494a8c95,0x25704ac695812aea55a4,0x592c9a58b4b0695ed2bc,0xb7c96d92d725a64b3c96,0xa5e64bbc97452e4a5c64,0x92ffa5f74bde97b12f4,0xc4a988930d26124c1498,0xa63e4c6c98b9315a6284,0x7d32ba64f4c989911320,0xd2c9a3934326794cd899,0x26c84d809af535aa6a84,0xe137826e84dc09b61368,0xe369c61388270d4e009b,0xa7434e809ce139827284,0x313bfa75e4eac9d393a5,0xf4a9e893cfa7974f289e,0x27b94f6c9ecd3d5a7a84],#[0x2d3e427c54f849efd3de,0xfb49f5d3ea27d14f9c9f,0x641b07039fb53f2a7e24,0x142007c1203f05f0060,0xc343fc01016c1426027c,0x50480fc1644f005c16,0x3f05f00507c16c140ff,0x484a0fc1418f00607c16,0x244141805b05f020f154,0xd0af0385141203f85f0,0x9e17c0138500fc00d0f0,0x5c4f00570f8583830580,0x1109e17c0a184841c3e0,0x500fc0e143825c3e17c0,0x812f0040310ac16c4f00,0xc1632212c17c0181f05,0x2141632143c17c084865,0x85027c0141805b05f021,0xf858384f0385081604b,0x4485841c384bc012127,0xc3827c0e145426c3e17c,0x2e180ae140ff005849,0x120a825c3e17c01785f,0x4500f85f00302816e17c,0x17c083c56118384b8586,0x6118384bc0868560c18a,0x850c1f4480343fc0e146,0x3c46128507fc01003f03,0x84a0ff03851a85063c08,0x851983063c0a14461183,0x7c083c50580670c1ff02,0x5806a17c0080505806a1],#[0xe1816019c384bc0a1460,0xc583848420f829c37120,0x20f829c37120e1a0a70e,0x43864291043ec3438584,0x3b110e18144410f42ac4,0xa31cc683844410f42ac,0x6e19120a8420f70e0e16,0xe11c40641b0704711c38,0x9055c40445845c3b160,0x21384a0970dc4844604c,0x70e0ff005310c346d191,0xc019c3b0a0ff00482a10,0xfc044058420a70e0f713,0x410ab110ff006428c4b0,0x7f003442c3f010f10144,0x582a1070e0ff00583cc,0x3dc4f00603c0a051c4f0,0x310c3f011a1610829c38,0xc0150ad1509f02461512,0xc09f0020160a70e09d17,0x141302415b13c0141504,0x2b13c01909b0cc444fc0,0x970fc0080644d09b0d1,0x20a70e0f713c01a1384a,0x83fc0150ab0d10f00484,0xa51c8951bc0160a841c3,0xc422a4350c90f008f188,0x1e0951bc01406717c007,0x7cc384a0ff02c51a0a5,0xc083c4848c6b17c007c5,0x10110c16d17c00e1230f,0x3093c00b44057c00c15d],#[0x1f0c0a08c2b1c13f00,0x5d13c00806717c00c0af,0x2c4f00444ec344ac4f00,0x83860240a913c0100f05,0x3f010f161083e0a70dc4,0x306f00300fc0090a442c,0xf002613c20981f0944d1,0x23081f043c00984f081f,0x801ff0030801ff003080,0x2e13c0140d03384f0040,0x4106053f00521053e0c5,0x1203c200000000000002,0x104090409040a060904,0x4810009040a060904000,0x160482001f04002410,0x1683c20580f080000000,0x1010183c10580f080404,0x480f910302410101010,0x200480f058403dc31103,0x9c00580f141670c0f0c,0x9810340410810109c37,0x48104818484483c3058,0x3344082183c0c0c00101,0xc1683c40016098203010,0x10101030103304080c30,0xc1020f040f04003c1024,0x400001000904003,0x4040a10100040600040,0x3d8108090404040404,0x100040400040010100,0x100f08160802001f0400,0x1f0444e04200001011],#[0x10401040c04103c103c1,0xe041e04103d810b8,0x1000100010980f080104,0x40004000120102048,0x1000109810026042604,0x1204120412040004000,0x101021283c2000100010,0x2810004060004000010,0x100010000004040a040,0x2420009040a040000100,0x241000001f078107810,0x10400040440420241,0x101001f040907810242,0x24100000002410041,0x400001e040908010400,0x107c1000004040409,0x404040404007c1e041,0x43074304080400101000,0xc10281d0c1d0c150c103,0x8010343040a0400281d0,0x40416848200082810,0x8001010212040000000,0x8483002607c200003c12,0x68483000848100083c44,0xa040404005a1208007c1,0x12040848104810481000,0x1e0410981048c3080904,0x3810242000000000000,0xd0108090412040f07c2,0x260400481e0413,0x81024100120404060004,0x4100090601040004104],#[0x41607c230c1048102410,0x8103c440812040a041f0,0x80200000404040904004,0x40004200582000101c30,0x80f0400001000004000,0x4040426040010102101,0x10000040010180010001,0x98100001010000801b0c,0x101e0c10001000109810,0x4108019101038102829,0x9040000100091019101e,0x3c1e181001f040,0xa040a041504000005410,0x8010020040,0x28142810101000000000,0x1e181000904000000404,0x10282000103810282910,0x28102410241000038,0x420050104002810000,0x7810400000000000042,0xa0400101080102440644,0x80100410001010a050,0x6d0b400600c168104000,0x408488483c303c84081,0xf040f0400016041f0401,0x60400001024102484081,0x60303000105810581001,0x16e0420084e0420601,0x400040004000400040,0x81604002410000000040,0xc080104007c10600c0,0x70104000200582080106],#[0x41059810b81040104090,0x160400000801e041e0,0x28102810009061283c2,0x304000090409041f8042,0xc308140601040804100c,0x20a824c40c0a07c2312,0x4c40409710207c17101,0x5090414704230dc108c6,0xc4b0c2050130d0e081c0,0x710230d4102034244608,0x5c4040828c40820040a,0x8231c13101029c40820,0x15708242410514108c37,0x1e00430d0f081d050a04,0x7c207c0a0a440783e0b8,0x2e0780110a424440c0a0,0x10191014290901032138,0x826440ec404c40400009,0xb1020000101b10c40a0a,0x81f0509b10200150409,0xc102809b103b101024c4,0x909c40409b102b10107,0x9101510102809710307c,0x40c2018150c100010101,0xc10808e0981e021816c1,0x30408048904810502052,0x3181512c308140414064,0x1044241051c108c37042,0x81058103c1001203f413,0x40f08000404041604004,0x7c10480f0804040000d0,0x4040408040d041d0410],#[0x31020800909840400184,0x31013101000906840420,0x304030414041404c4040,0x84040610161010201000,0x8407430242d080908001,0x1000424150815113420e,0xc010090409040b081000,0x80202809810370dc2705,0x400003040000a04090,0xf03c20580f0800003040,0x40170ec103d040c0f041,0x3030406c3b09040ec20,0x60140dc391020541491,0x970e041014811c30dc1,0x7c102b44080a07c2028,0x14040fd10207c1c101,0x404140544040f040d101,0x40444040f04140414070,0x1060111010001000001,0xc110c110c11104308001,0x8060400143040110100,0x40808040c101000b0503,0x815b082c101c101b041,0x11c1080c101c10105404,0x3709c1700490c111010,0x4050c107c17041704100,0x40804080543074407440,0x3040000004003440,0x20204010344040804000,0x10130010001000904c30,0x6c4040700100157082b,0x10130dc108c605c404c4],#[0x40b1013001001470423,0x144040905c405c405c4,0x5010144040000000000,0xa040020a04090615040,0x810008481000000101,0x40404051010000241,0xc100040420510200000,0xa0489040000904001010,0x40907420400002241008,0x30414040000000304090,0x14708201c20414078,0x10001000000005c204,0x23830803138308000c10,0x38307830783040e0c10,0x20c1034100c40400241,0xc09080000d310200000,0x9040024100c10241e,0x908000000000c1000000,0xf041804080400001e0c0,0x1000180c107c10001001,0x107c16088304007c107c,0x41001f0401040000058,0x100000007c1008100410,0x404040908100007c1008,0x90809080202420081f0,0x801770830801c101080,0x5c10241030406047082,0xc10106010601850107c1,0x10806101000a704207c1,0xf040704107c10481028c,0x50740850608010801001,0x400801004030808c1342],#[0xa04000000030,0x4000c10000000000000,0x490404]]
def g247H7 := limbs80 #[#[0x448138580025e04e93,0xc61202e4006244c48c0,0x808102104ad004803614,0x2c547040801070038403,0x884688f9818cc2193648,0xe66185005a4c09b18003,0x524af88f04f19d100430,0x52db54e588003c467de6,0xad551a0d8123481ff0b8,0x316ea95f0d48545b9037,0x4abbe19783dfdd8416a0,0xb255be30601d9bbc1125,0x9e463453b4a00ceb0e8a,0x156088ee1d523ed188,0xe6cf75f1347abe5a1258,0x829740e0005f5373b48a,0xfc1c6ed0000001a90566,0x198600000000005d,0x22f2500000021f1c4400,0xed800102fa5352469f9f,0x9b03ed00060ae0ac0005,0x72380039530385ce1a74,0x8000a110006e34001810,0x639a07738363df0f,0x2ccf842173b7ad159e00,0x53d51c0594000f50f6,0x3b8ce221490941805120,0x6bb107efbb058e86f18e,0x5fbc0b7804b498003fb9,0xf89b93f898a1ee452b14,0x532db1c698f3a17b0db,0xdd917b0003fae00000],#[0x189985eed7ea7c0,0x10780bd0,0x310691b6462f40004210,0x80010f00001e840001d8,0x1f309ec8000cc26054a9,0xf394fada42a8014000ac,0x5383ad247c13fae65ab2,0x35a38b600053e61647,0x776191392360000fb58,0x6a2a5e40000005c90001,0x638c02c895d803aed949,0x10f06900000020d,0x16dde558104000b4a32,0xb2b06400165136400000,0x94caa000636c0000004,0x21aebe81d0ee2d708000,0x792e18f2510a8e902e79,0xa000206d30e09900056c,0xbd3ac6b308f4808c18ab,0xe5c5c432400182705402,0x87c4b125f00058e6dc12,0x2c75660001cfa0000004,0x43d6c168c4a4453591ab,0x2ee950c1c7fd414ea227,0x50002d0ae8b21edbcd85,0x2def10006897cba00023,0x1338ce09fa73817a909c,0xcc8000a69c03800142a0,0x633404dc5bd990004f4b,0xacdf483406b98c000a6d,0xe446a1c9c864c59e0834,0x4c925c8573f1709b2ca],#[0xcc5114afc9a040096a24,0xb8d572e2404e1bb2535d,0xddfa4a58d84cee0676bb,0x35bc]]
set_option maxRecDepth 16000 in
def g247D8 := limbs80 #[#[0xed563585319f48750531,0x97d859d131e756558531,0x9ed821d3319f9801d331,0x8fd861d33197d851d331,0x9f9801cd41e756558541,0x97d851cd419ed821cd41,0xd9e73d0f418fd861cd41,0x97f875974197d8759741,0x97d85ddb4197f865d741,0x9ed821cd619f9801cd61,0x9be841cd619bd841cd61,0xe77815956197d851cd61,0xdf2715c043df1715c043,0xd79755c043dda735c043,0xcf9765c043d7a755c043,0xdf1815c043cfa765c043,0xdd9435c043df2815c043,0xd7a655c043d79655c043,0xde6725c443de5725c443,0xd75755c443db6745c443,0xcf5765c443d76755c443,0xdb5435c443cf6765c443,0xd76655c443d75655c443,0xcf5769c443d75759c443,0xcdd7650c43cf6769c443,0xd9e7490c439df8750c43,0xc7d7659443cdd7690c43,0x97f875944397d8759443,0x97d8799443c7d7699443,0xc7e765d443c7d765d443,0xc7d769d44397f865d443,0x97d879d443c7e769d443],#[0x9f581dd4439f980dd443,0xc7d855d8438fd86dd443,0x8fd879d843c7e855d843,0x9f581dd8439f980dd843,0xe9d6458d4397d85dd843,0xf1d65d0e43c7f7659543,0xd9d87d0e43f1e65d0e43,0x9f9809ce43b9e8498e43,0xc7f76595539ed82dd643,0xd6d655ca539f7815d953,0xc7d7659653b5f8359653,0x97d85dc9639ed82dda53,0x9f5811d1639f9801d163,0x97d851d1639ed821d163,0xb6d829cd65b77815cd65,0xfd563cc531d5f739cd65,0xf7565cc531bf584cc531,0xfb54350531bf586cc531,0xfd56350531fb74350531,0xfb56450531fd66350531,0xf756550531fb66450531,0xdf77650531df57650531,0xbf78650531bf58650531,0xdf57458531ef56358531,0xbf78458531df77458531,0xbf581d0d31bf78150d31,0xbf78158d319fd87d0d31,0xedd6458d31fd78158d31,0xddf7458d31ddd7458d31,0xdbd7459131ddd7498d31,0x9fd8759131dbe7459131,0xbf581991319ff8759131],#[0x9fd8799131dbd7499131,0x9fd861d131d7d651d131,0xd7d655d131df7815d131,0xbdd839d1319ff865d131,0x9fd839d131b7d859d131,0x9fd869d131d7d659d131,0x9fd86dd131d7d65dd131,0x9ff845d931df7815d931,0x9fd87d0f319fd84dd931,0xddd7458f31edd6458f31,0xddd7498f31ddf7458f31,0xdbe7459331dbd7459331,0x9fd8759331cfd7659331,0xdbd74993319ff8759331,0xd7d651d3319fd8799331,0xd7d655d3319fd861d331,0x9fd879d3319ff865d331,0xd7d659d3319fd839d331,0xd7d65dd3319fd869d331,0xf7781597319fd86dd331,0x9fd84ddb319ff845db31,0xbf583d0541fb543d0541,0xf7565d0541fb564d0541,0xfb54358541bf586d0541,0xef56358541fb74358541,0xbf78358541df77358541,0xfb78150d41bf78150d41,0xf9e6350d41f9d6350d41,0xdbd7650d41f3d6550d41,0xbbd8650d41dbf7650d41,0xbf58190d41bbf8650d41,0xf3d65d0d41bbd8490d41],#[0xbbd86d0d41dbd76d0d41,0xcfd7658d41ebd6458d41,0xbf58198d419ff8758d41,0x9fd8798d41bbd8498d41,0x9fd861cd41d7d651cd41,0xdbd64dcd41bbd849cd41,0x9fd86dcd41d7d65dcd41,0xfb78159141bf78159141,0xbbd8399141bbf8359141,0xdf7815d941f778159541,0x9fd83dd9419ff835d941,0xf9d6350f41d7d7550f41,0xf3d6550f41f9e6350f41,0xdbd7650f41f3d7550f41,0xbbd8650f41dbf7650f41,0xbbd8490f41bbf8650f41,0x9fd8790f41d7d7590f41,0xdbd76d0f41f3d65d0f41,0xddd7358f41bbd86d0f41,0xebd6458f41dde7358f41,0xcfd7658f41d7d7558f41,0x9ff8758f419fd8758f41,0xbbd8498f41ddd7398f41,0x9fd8798f41d7d7598f41,0xdbd645cf41d7d755cf41,0xd7d655cf41dbe645cf41,0xd7d759cf419ff865cf41,0x9fd869cf41d7d659cf41,0xbbf8359341d7d7559341,0xbbd8399341f3d7559341,0xb7f8759741b7d8759741,0x9ff835db41d7d765d741],#[0x9fd83ddb41d7d855db41,0xbf58110d61bf98010d61,0xe7d6510d61bed8210d61,0xafd8610d61b7d8510d61,0xedd6350d619fd8710d61,0x9ff8750d61e7d6550d61,0xf9f4390d61bf58190d61,0xe7d6590d61edd6390d61,0x9fd8790d61afd8690d61,0xe7d65d0d61bf581d0d61,0xef78158d619fd87d0d61,0x9fd841cd61cff7458d61,0xe7d655cd61bf7815cd61,0xe7d659cd61bf5819cd61,0x9fd879cd61afd869cd61,0x9fd831d1619fd84dcd61,0xe7d655d161bf7815d161,0xe7d659d161bf5819d161,0xafd869d161b7d859d161,0x9fd83dd1619fd879d161,0xdf9765c043f79655c043,0xdf9635c043df9435c043,0xdf9865c043df9655c043,0xdf5765c443f75655c443,0xdf5435c443d7d655c443,0xdf5645c443df5635c443,0xdf5865c443df5655c443,0xdf5769c443f75659c443,0xcfd7650c43d7d7550c43,0xf9d6450c439ff8750c43,0xddd7650c43f5d6550c43,0xf5d6590c43ddf8750c43],#[0xdde7358c43ddd7690c43,0xcfd7658c43d7d7558c43,0xd7d659cc439ff8758c43,0xcfd76594439fd869cc43,0xb7d8759443e7d7659443,0xd7d765d443b7f8759443,0xb7d869d443d7d769d443,0xe7d855d8439fd86dd443,0xd7d855d8439ff815d843,0xcfd815d843d7e855d843,0xcfd855d843cff815d843,0xddd63dc543cff855d843,0xdbd64dc543dde63dc543,0xd7d65dc543dbe64dc543,0xf9f4390d439fd86dc543,0xf3d6590d43f9d6390d43,0xbed8294d43bbd8690d43,0xebd6458d43ede6358d43,0xbbf8458d43bbc8458d43,0xbdf8258d43cff7658d43,0xf9f8458d43f9c8458d43,0x9fe8798d43edf7658d43,0xdde8798d43bdd8298d43,0xcff7659543bde8798d43,0x9ff865d543e7f7659543,0xcff765d9439fd86dd543,0xddf835d9439ff815d943,0x9fd81dd9439ff835d943,0xd7d655c643ddd635c643,0xd7d655ca43ddd635ca43,0xf5d65d0e43f9d64d0e43,0xbdd87d0e43bdd86d0e43],#[0xf9d76d0e43f9d65d0e43,0x9ff8758e43f9d87d0e43,0xedd6458e43bdf8258e43,0xddf8758e43ddd7458e43,0xddd7498e43bdf8758e43,0x9fd869ce43d7d659ce43,0x9fd8795243bf58195243,0xcfd7659243bdf8359243,0x9fd87992439fd8759243,0xd7d655d2439ff815d243,0x9ff865d243d7e655d243,0x9fd86dd6439fd84dd643,0x9ff825da439ff815da43,0xb7d8494d539fd84dda43,0xd7f7655153b7d8694d53,0xd7d651d153bdf8359153,0xd7d65dd1539fd861d153,0xb7f84595539fd86dd153,0x9fd84dd9539ff845d953,0xdee745ca53ded745ca53,0xded635ca53ded765ca53,0xdee645ca53ded645ca53,0xdee845ca53ded845ca53,0xbdf8359253ded865ca53,0xdbe7459253dbd7459253,0x9fd8759253cfd7659253,0xdbd74992539ff8759253,0xd7d655d2539fd8799253,0xd7d659d2539ff865d253,0xb7f83596539fd869d253,0xd7d855da539ff845da53,0x9fd84dc5639fd84dda53],#[0xcfd64dc963b7d85dc963,0xd7d85dc9639fd84dc963,0xedc8359163afd8498d63,0xbf9801d163edf8359163,0xbed821d163bf5811d163,0xb7d851d163dbd741d163,0xbdd839d163bdf835d163,0x9fd81dd163dbf749d163,0xbf7815d5639fd82dd163,0x9ff815d2639fd84dd563,0x9fd841cd659ff825d263,0xd7d731cd659fd84dcd65,0xb7e841cd65b7d841cd65,0xb7c845cd65d7f745cd65,0xd7f739cd65b7f845cd65,0xb7e849cd65b7d849cd65,0xb7e84dcd65b7d84dcd65,0xff664cc531ff564cc531,0xff56350531ff54350531,0xff56450531ff58350531,0xff58650531ff57650531,0xff74358531ff54358531,0xff67458531ff57458531,0xff68458531ff58458531,0xfdd6350d31ff78150d31,0xfbe6450d31fbd6450d31,0xdfd7650d31f7d6550d31,0xbff8650d31bfd8650d31,0xfbd64d0d31fdd63d0d31,0xdfd76d0d31f7d65d0d31,0xefd6458d31bfd86d0d31,0xdfe7458d31dfd7458d31],#[0xfdd7458d31bff8458d31,0xfdc8458d31fde7458d31,0xfde8458d31fdd8458d31,0xff58159131fdf8458d31,0xfbd7459131bff8359131,0xfbe7459131dfd7459131,0xdfd8759131dff7459131,0xdfe8759131bfd8759131,0xbfd8399131bff8759131,0xbfd8799131fbd7499131,0xf7d655d131ff7815d131,0xbff865d131dfd765d131,0xdff865d131dfd865d131,0xdfd769d131f7d659d131,0xff7815d931bfd869d131,0xdfc845d931bff845d931,0xdfe845d931dfd845d931,0xfdd6350f31dff845d931,0xfbe6450f31fbd6450f31,0xdfd7650f31f7d6550f31,0xbff8650f31bfd8650f31,0xfbd64d0f31fdd63d0f31,0xdfd76d0f31f7d65d0f31,0xefd6458f31bfd86d0f31,0xdfe7458f31dfd7458f31,0xfde7458f31fdd7458f31,0xfde8458f31fdd8458f31,0xfbd7459331bff8359331,0xfbe7459331dfd7459331,0xefd7659331dff7459331,0xbfd8759331dfd8759331,0xbff8759331dfe8759331],#[0xfbd7499331bfd8399331,0xf7d655d331bfd8799331,0xbff865d331dfd765d331,0xdff865d331dfd865d331,0xdfd769d331f7d659d331,0xdfd845db31bfd869d331,0xff563d0541dfe845db31,0xff54358541ff663d0541,0xff57358541ff64358541,0xff58358541ff67358541,0xff78150d41ff68358541,0xfde6350d41fdd6350d41,0xf7d6550d41fbd6450d41,0xbfd8650d41dfd7650d41,0xfbd6350d41bff8650d41,0xfbd8650d41fbd7650d41,0xfdd6390d41fbf8650d41,0xf7d6590d41fbd6490d41,0xbfd8690d41dfd7690d41,0xff58158d41fbd63d0d41,0xfde7358d41fdd7358d41,0xefd6458d41dff7358d41,0xfbe8458d41fbd8458d41,0xefd7658d41bff8458d41,0xbfd8758d41dfd8758d41,0xbff8758d41dfe8758d41,0xbfd8498d41fdd7398d41,0xff7815cd41bfd8798d41,0xf7d655cd41fbd645cd41,0xbff865cd41dfd765cd41,0xf7d659cd41fbd649cd41,0xbfd869cd41dfd769cd41],#[0xfbe8359141fbd8359141,0xdfe835d941dfd835d941,0xfde6350f41fdd6350f41,0xf7d6550f41fbd6450f41,0xbfd8650f41dfd7650f41,0xfbd6350f41bff8650f41,0xfbd8650f41fbd7650f41,0xfdd6390f41fbf8650f41,0xf7d6590f41fbd6490f41,0xbfd8690f41dfd7690f41,0xfdd7358f41fbd63d0f41,0xfde7358f41dfd7358f41,0xfbd8458f41efd6458f41,0xbff8458f41fbe8458f41,0xefd7658f41f7d7558f41,0xbfd8758f41dfd8758f41,0xbff8758f41dfe8758f41,0xbfd8498f41fdd7398f41,0xbfd8798f41f7d7598f41,0xf7d655cf41fbd645cf41,0xbff865cf41dfd765cf41,0xdfd865cf41dfd645cf41,0xfbd649cf41dff865cf41,0xdfd769cf41f7d659cf41,0xdfd649cf41bfd869cf41,0xfbe8359341fbd8359341,0xdfe835db41dfd835db41,0xefd6350d61ff58150d61,0xfbd7450d61dff7350d61,0xdff7450d61fbe7450d61,0xdfd8750d61dfc8750d61,0xdfe8750d61bfd8750d61],#[0xbff8750d61dff8750d61,0xbfd8490d61dff7490d61,0xefd63d0d61bfd8790d61,0xefe7458d61efd7458d61,0xefd8458d61efc8458d61,0xeff8458d61efe8458d61,0xdfd745cd61ff7815cd61,0xbff845cd61dfe745cd61,0xdfe749cd61dfd749cd61,0xbfd839d161bfd849cd61,0xf7d6550c43fdd6350c43,0xbfd8650c43dfd7650c43,0xdff8750c43bff8650c43,0xfdf8650c43fdd8650c43,0xdfe7458c43efd6458c43,0xf7f8159443f7d8159443,0xf7f8359443f7d8359443,0xf7f8759443f7d8759443,0xff7715c543dfd855d843,0xfde635c543fdd635c543,0xfbe645c543fbd645c543,0xdfd765c543f7d655c543,0xbff865c543dff765c543,0xfde63dc543fdd63dc543,0xfbe64dc543fbd64dc543,0xdfd76dc543f7d65dc543,0xbfd86dc543dff76dc543,0xdfd64dc543dfd63dc543,0xdff86dc543dfd86dc543,0xfbd6490d43fdd6390d43,0xf7d6590d43fbe6490d43,0xdff7690d43dfd7690d43],#[0xfbd7690d43bfd8690d43,0xfdd6354d43fbf7690d43,0xfbd6454d43f7d5454d43,0xf7d6554d43fbe6454d43,0xdfd7654d43f7f7554d43,0xbfd8654d43dff7654d43,0xfbd6494d43fdd6394d43,0xf7d6594d43fbe6494d43,0xdff7694d43dfd7694d43,0xbff8158d43bfd8694d43,0xefd6458d43bff8258d43,0xdfd7558d43bff8458d43,0xbff8558d43dff7558d43,0xdfe8758d43eff7658d43,0xfdf8158d43fdd8158d43,0xfdf8258d43fdd8258d43,0xfde8458d43fdc8458d43,0xfdd7558d43fdf8458d43,0xfdd8558d43fdf7558d43,0xbfe8798d43fdf8558d43,0xfdd7598d43fde8498d43,0xfde8798d43fdf7598d43,0xf7d7559543bff8359543,0xeff7659543f7f7559543,0xbfd8759543bfc8759543,0xbff8759543bfe8759543,0xf7f8159543f7d8159543,0xf7d8359543f7c8359543,0xf7f8359543f7e8359543,0xf7d8759543f7c8759543,0xf7f8759543f7e8759543,0xdfd765d543f7f755d543],#[0xbff865d543dff765d543,0xdff76dd543dfd76dd543,0xbff815d943bfd86dd543,0xbff855d943fdf835d943,0xdfd815d943eff765d943,0xdff835d943dff815d943,0xdff855d943dfd855d943,0xfdf83dd943bfd81dd943,0xdfd81dd943bfd85dd943,0xdff83dd943dff81dd943,0xdff85dd943dfd85dd943,0xdfd645ca43dfd645c643,0xf7d65d0e43fdd63d0e43,0xfdd76d0e43dfd76d0e43,0xdfd7458e43efd6458e43,0xfdd5458e43fdd8158e43,0xfdd8458e43fde5458e43,0xfdd8558e43fde8458e43,0xdfd7655243f7d6555243,0xf7d6595243bfd8655243,0xbfd8695243dfd7695243,0xbff8259243bff8159243,0xdfd7559243bff8359243,0xbff8559243dff7559243,0xdfd8759243efd7659243,0xbfd8799243bfd8399243,0xdff815d243dfd815d243,0xdfd855d243dfd655d243,0xdfd865d243dff855d243,0xbff8459643dff865d243,0xf7f8159643f7d8159643,0xf7f8259643f7d8259643],#[0xf7f8359643f7d8359643,0xf7d8459643f7c8459643,0xf7f8459643f7e8459643,0xf7f8759643f7d8759643,0xdfd845da43dfd815da43,0xf7d6494d53dfd855da43,0xf7d5458d53f7e6494d53,0xbff8458d53efd6458d53,0xfdf8359153fdc8359153,0xdff7459153bff8359153,0xdfd8759153f7d8559153,0xbfd8399153dfe8759153,0xfee645ca53fed645ca53,0xdfd7458e53efd6458e53,0xfdc8359253dfe7458e53,0xbff8359253fdf8359253,0xdfd7459253fbd7459253,0xefd7659253fbe7459253,0xbfd8759253dfd8759253,0xbff8759253dfe8759253,0xfbd7499253bfd8399253,0xdfd765d253bfd8799253,0xdfd865d253bff865d253,0xdfd769d253dff865d253,0xdfd845da53bfd869d253,0xefd645c563dfe845da53,0xdfd745c563dfc745c563,0xdff745c563dfe745c563,0xbff845c563bfc845c563,0xdfd74dc563efd64dc563,0xbfd84dc563dfe74dc563,0xdfd84dc563bfe84dc563],#[0xefd645c963dfe84dc563,0xdfe745c963dfd745c963,0xdfd74dc963efd64dc963,0xbfd84dc963dfe74dc963,0xdfd84dc963bfe84dc963,0xefd7498d63dfe84dc963,0xefc8359163efe7498d63,0xefe8359163efd8359163,0xefd7559163eff8359163,0xefc8759163eff7559163,0xdfd741d163bfd811d163,0xbfd851d163dfd751d163,0xbff825d163bff815d163,0xbff835d163fdf835d163,0xdfd755d163dfe745d163,0xbff855d163dff755d163,0xbfd819d163eff865d163,0xfdd839d163bfd829d163,0xdff749d163bfd839d163,0xdff759d163dfd759d163,0xefd869d163bfd859d163,0xdfd75dd163bfd81dd163,0xdfd81dd163bfd85dd163,0xff7815d563dfd85dd163,0xbff845d563bfc845d563,0xbfe84dd563bfd84dd563,0xdfd815d263dfe745d263,0xdfd825d263dff815d263,0xdfd855d263dff825d263,0x6600330000dff855d263,0x650132010800de00a200,0x640231020701dd019801],#[0x51032702fd02ca029702,0x3e040b03d803ae038403,0x3d04f804ce049b047104,0x45062405e805ac058205,0x56072306f906b4066f06,0x43081007e607b3078007,0x5d092a08ee08b2087608,0x800a4d0a0809c3099009,0xac0b700b3d0b010ab30a,0xbd0c8a0c4e0c1b0be80b,0xe00da40d710d3e0cf00c,0x30ed00e940e610e250d,0x4110050fb70f840f3f0f,0x761143110710c2107d10,0x751242120f11dc11a911,0x7d134a131712e412a812,0x6a1440140413da13a713,0x8d1548151514e214af14,0xe61698164a160e15c915,0x1b17df17ac1770172216,0x2318e718b4188a185718,0x2219ef19bc1989195619,0xf1adc1aa91a881a551a,0x321bf61ba81b751b4b1b,0x5e1d221cef1cb31c651c,0x931e601e1b1ddf1d9a1d,0xad1f7a1f3e1f0b1ecf1e,0x91205e202b20011fe01f,0x9921662133210020c420,0xe922ad2271222321e721,0x1e23eb23a62373232522,0x224d824a52472244824],#[0x1325e925ad257a253525,0x926df26b5268b264f26,0x3e280b27cf278a274e27,0x58291328e028ad287a28,0x572a2d29fa29be298229,0x832b472af92ac62a932a,0x942c612c2e2be92bb62b,0x8a2d572d242cf12cc72c,0x9b2e5f2e1a2de72db42d,0xac2f792f462f0a2ee02e,0xcf308a304e301b2fe82f,0xc53189315f312c30f930,0xd632a33279323d320131,0xd533a233783345330932,0xa34bc3489344d33ff33,0xee35bb35913570353d35,0xf636cc3699365d362a35,0x1037cb3798375c372936,0x57390038cd3888384c38,0x8c3a353a0239c6399339,0xaf3b7c3b373b043abf3a,0xae3c723c3f3c0c3be23b,0xbf3d8c3d503d143ce13c,0xc73e8b3e583e253df23d,0xd83f933f603f2d3efa3e,0xe940bf408c405040143f,0x3041f441b8416a412e40,0x5c432042d2429f426c42,0x88444c441943dd439843,0xab4578453c450044c444,0xfb46bf4671463545f045,0x5d482147ca4773473746],#[0xa4495f492348de489948,0xac4a704a3d4a0a49ce49,0x994b6f4b3c4b124adf4a,0xc54c924c5f4c234be74b,0xcd4d9a4d554d224cef4c,0x844e634e424e064de54d,0x684f474f144ed84ea54e,0x555046500a4fc54f924f,0x4b511850dc50a9509150,0x80524d521151cc519051,0x915355532252e652aa52,0x9054665433540053d653,0xd755a4555f54ff54cc54,0xdf56a3565e5634561355,0x3857f357ae5772571b56,0x52591f58e358a7587458,0x755a3959f459ca598559,0xaa5b775b325aed5ab15a,0xbb5c7f5c4c5c195bdd5b,0xcc5da25d6f5d335cf75c,0xef5ebc5e805e445e085d,0x1b5fdf5fa35f5e5f2b5e,0x2360f060ab6081604e60,0x2b620161c56189615f61,0xf62e562b26291625e62,0xe163b763966363634263,0xe064ad6471643563f963,0xe865b565796546651364,0x1466d86693664e661b65,0x4067fb67c8678c675067,0xca68b268916879685868,0x5d6945692d690c68e268],#[0xf069e169c0699f697e69,0x7a6a626a416a206a0869,0xf26ada6ac26aaa6a926a,0x7c6b646b436b2b6b136a,0x336c1b6bdf6bbe6b9d6b,0xb46c936c846c636c426c,0x116d026cf36ce46cd56c,0x6e6d5f6d476d2f6d176d,0xef6dd76dbf6da76d866d,0x8b6e736e526e316e106d,0x156ef46edc6ecd6eb56e,0xc36f996f6f6f576f2d6f,0x4d7035701470056fdb6f,0xe970d170a77086706570,0x46713771287119710170,0xe271c171b27191717071,0x2d721e720f720971f171,0xdb72ba72907266724e72,0x53733b7323730b72f372,0xdd73c5739b737a736b73,0x707458742e741673f573,0xc74e274ca74a9747f74,0xa875907566753c752475,0x44762c761475f375c975,0xce76ad768c7674765c76,0x4f7737771676f576e676,0x9a779477857776775e77,0xf777df77d077b877a077,0x81786978517839781877,0x278e178b778a8789078,0x95797d795c7929791a79,0x557a347a0a79f279bf79],#[0xdf7ad07aa67a857a767a,0x967b6c7b4b7b217af77a,0x327c1a7c027bd87bb77b,0xbc7ca47c957c747c4a7c,0x3d7d137cfb7cda7ccb7c,0xf47dca7d977d6d7d557d,0x757e5d7e4e7e367e1e7d,0xed7ede7ecf7eb77e967e,0x807f687f477f267f0e7e,0xf87fe97fbf7fa77f987f,0x558034802e80047ffe7f,0xd680b5809d8085806d80,0x6981518139812a811280,0xfc81db81c381a2818181,0xc582a4825f821a820b81,0x6a83528343832b82f882,0x69842483e883b5839d83,0x56853e851d84e184a584,0xfb85d185c28598858085,0x8e867686558634861385,0x686ee86df86be86a686,0x99878a877b8751872787,0x23881487f387e487c387,0x9b887a88628853883b88,0xa88f288d188c288b388,0xca899789768943892289,0x8a8a608a2d8a1589e289,0x388b208aff8ae78ab48a,0xe68bce8bb68b9e8b6b8b,0xaf8c8e8c498c288c078b,0x4b8d338d128cfa8cd98c,0x9f8d908d818d728d638d],#[0x4d8e2c8e148df38dc98d,0x1f8ef58ed48eb38e928e,0xbb8f918f798f588f2e8f,0x7b905a904290188ff78f,0x3b911a90f990d890a590,0xaa919291839162915391,0x46921c920491d191c291,0xbe92a692979288925592,0x36931e930692ee92d692,0x9c937b93639354934593,0x26940e93f693cc93b493,0xd494b39480945f943e94,0x6795589540951694f594,0xf195d995c195a0957f95,0x69964896399621960995,0x596d296ba96a2968a96,0xbc97a497719750972697,0x469825980d97da97cb97,0xd098af9897987f986798,0x63994b993c991b98f198,0xf699cc99ab9993997b99,0xad9a839a599a419a2099,0x499b3a9b229b0a9ad79a,0xee9bcd9bac9b8b9b619b,0x5d9c459c369c1e9c069b,0x29ce19cc09c969c7e9c,0x959d7d9d5c9d3b9d1a9d,0x289e109df89de09dad9d,0xc49eb59e9d9e7c9e529e,0x459f249f159efd9ee59e,0xc69fb79f9f9f759f5d9f,0x47a038a0209fff9fe79f],#[0xfea0dda0c5a0a4a05fa0,0xd0a194a161a137a11fa0,0x7ea266a24ea236a21ea1,0xeda2d5a2c6a2a5a296a2,0x53a33ba31aa30ba2fca2,0xd4a3b3a392a38ca362a3,0x8ba46aa452a41fa3f5a3,0x54a53ca512a4e8a4bea4,0xb1a5a2a593a57ba56ca5,0x282a0b06e003c5a5c9a5,0x878105182c0f837020a,0xe08e27002b8518890f06,0xc0086184056170c0e121,0xc28a080570029851415,0x481821e04147050270dc,0x30c204b0d85070843224,0x50404b8014c28a12e004,0xc37030a284b0dc004e14,0x2888a045138185141409,0x8ac4e00570a222b8018c,0xd84c283840502289c0c2,0xc0c26145c27002186130,0x5141386c27030a2e1813,0x310bc010880904613818,0x98c0e10200f0a0281c28,0x7f138a140503876282,0x10200fe2714280a070e1,0xf8a14050386638298c0e,0x3e3f1b8a0a6203860803,0x23b1422c60708190d870,0xdc6470484c25c4e28542,0x88150e09128871586c48],#[0xec7102014057001e2f15,0x2840280ae003c5057001,0x7001ec7102014057001e,0x1e2840280ae003c505,0xc40803f80141815c7627,0x71a26c389313811a1815,0x29451614466205380c,0x450551813c0a28a0c057,0x2e2f002a38268cc4e051,0x4b89c5e0054704880261,0xc50805015c0078a09098,0x313700484040280ae003,0x3689c0060c9347f14074,0x64522445c0108a8a448,0x4e00506a3d1b8a15e005,0x40280ae003c52391b8b4,0x3801418200a627001e28,0x7050278146162712e2b1,0xe0050804d1d89c0a30b4,0xe8c0b1410472371015c5,0x60502419c0a38a0a04d1,0xe00907040281347e0518,0x42bc00a0d1387f158626,0x60805015c0078ac76371,0xe003c5e3f1b8a0aa2038,0x81208e2d1380302b8f44,0x5e382813c62271780382,0xe2b1380450c0644e2f00,0xd89c0630d138830e250f,0x3097138bc00a8c150a31,0x1f8fc6050278b44e00e1,0x28c30401fc4e2850140e],#[0x783700282c57880906f0,0x68b14a2033818714110,0xe0c08e0060584b110dc0,0x8186143e0883f020c2c1,0x8802309c0a28a09a2037,0x5450984b8a15c20446,0x2612c27002a284c2584e,0x9c006080a06e13800c14,0xc10920dc27001828370,0x4160cc4e003c606f0030,0x13810f1e0b06e003c40b,0x507f003e2a6018c382b,0x6078b050941b800f160d,0x160dc007b1078284b810,0x1282c1b80c4078c1f094,0x218400f8284b8106620e,0x20ac4201f0583701881,0xae0418861a60191287f,0x313800f183e0f0b41588,0xd050489989c0220a1283,0x7c1a0ac4e004860905a0,0xf028834142d06e003c50,0xd05a27001e3418240f82,0xf101f0682f002c285a0,0x21425c04303c542a1b80,0x7c1e2848080fc37030a3,0x8607a17801f150a86e00,0x5e05105101101fc0c28a,0x143f85a27001e28481f8,0xb0bc0a20a26c283f8144,0xb86e00b85e008030784,0x430230bc0c30805a209b],#[0x97028820250a86a27002,0x43c80961b0bc0a20b850,0xf18300861c2b0ac4e0,0x28481fc0141586c2b138,0x3112878230bc06210864,0xe28481f85c370188330c,0x2f003d0f1b0a12c37001,0x1e040561b81851819c4c,0x330c3008627030b0a1c,0x27021e38200986e06144,0xac4e003c50c02187856,0xc30581e85e187f80361b,0x27001e28581385a27030,0x2404c302781851b0d85a,0xbc0a20a200b07f818514,0x9c289c0c287c30487f0,0x5142409c2f02882d1380,0x283fc0c28a0a0fd13818,0x85105103f86e06146020,0x5a27002428270b44e061,0x849186c2d138012143f8,0x83e34298618043138185,0x9e03130a40201585e061,0x1589c0c30d0a61860110,0x120261813c0c28c0a04e,0xac2900a0261813c0c28c,0x402862120861b13810,0xc3627030b091c1386c2f,0x8130c09e061588286010,0x170dc0c287c442f00185,0x60dc0090b86a27001385,0x8020160d05e0048407c1],#[0x61b120bc0850e1282c1b,0x90c1282c1b802014b00c,0xdc013081682c1a89c00,0x4307c250682f002c3416,0x37004c205a0d05e05102,0x7010a22150dc00909058,0xfc30f84b80c4c28e1243,0x851f8626c2b13800f181,0x31380330c91098970189,0xf8562700242848138513,0x86143e266261b8185183,0xa1b8012078a12c2b1381,0x2243e142586e003c542,0x85e00984849218785627,0x5184185c370188121813,0x9b81851425c30f89b818,0x1e361781860f8816048,0x6a27001e2a141486a270,0x891186c2d13800f170b8,0x43e330c300884b130bc0,0x2c37001e28202586e061,0x890e1fc2f018812170a1,0x3801214300861e1589c0,0x5428490dc0100b86c2b1,0xc37004c20490a86e0080,0x61605c361689c0090b85,0xa1609700402a1487c00,0xb44e00485c2e1b802611,0xc01e1f44e00570a2e1b0,0x7001e302b0c1f07e1589,0x10fc2f018838830d8562,0xc41a1fc0c2854461c289],#[0xb13800a170c0f0561780,0x186620830b86e00a09c2,0xae003c50782b0ac4e06,0x51a89850af021e2e170c,0x30b0a1c1e040561b818,0x9c2f0040242490c3627,0x5e05105c2b130dc0050a,0xc28c0ac2f003e203c158,0x689c0c28d860f85841c0,0x60202441c0c28d0f0405,0xf881fa20830dc0c28d8,0x44185a27001e2e1b8185,0x89c0878d85a261b800f1,0xc361689c0078a080ae16,0x61589c01689c00ae144,0x3130a4313800ac2880a1,0x9c0c28d0961860110ae0,0x26178015878a09056198,0x310a0430d89c084e148a,0x185100a0ac37030a1f14,0xc0100986e0080387a1b8,0x51b0b44c3700142a1b0b,0x30a8a14300ca2701158,0x8f620578185100c0ca27,0xc28804046178186100a,0xc8b86a27001585142bc,0x90bc04303c6c26142586,0x4c3e1025c0c30685c204,0xe0030641830430fc2f00,0xb0bc0078986c204b0a0f,0xfc204b0b86e003c70661,0xe061494203c2dc0c28a1],#[0x30c321106182405a250f,0x5e06101e2e101409c2f0,0x1709850961b800f190c8,0xf0bc08792260fe17800f,0x5e003c50c05a24484220,0x101585c37001e387f0d8,0x4c38110c85e009850fe,0x5e009850c43c9083c2f0,0x110c1642f003e28270d8,0xb818404e1450fe178016,0x8021183e86e02142c2e1,0x4283f801615091287e17,0x58689617810f108a86,0x2d86e0614607e150986e,0xa28270d85e00985c2028,0x285b8020170dc0056130,0x58587e1443c0130a864,0x985e00862430490c85e0,0x26142585067022c2c3c1,0xe1b0bc0130a0a0661780,0x121c38270d85e0058504,0x140707c661c02151087b,0x401e140503860803c14,0x70505050200f0707c6e2,0xc40c86c3823102ac7630,0xf1a1ec38550589c0880e,0x1890f20200f05053801,0x14e003c60c0218712a2f,0x50200fe007c6e202820,0x745048542413e0080605,0x1a097003a2b102ac7e00,0x884190a627028b092188],#[0x3c60651415c0a307c661,0x14e003c7a20282014e00,0x4029c0078c446202820,0x4c60a82427c0100a0ae2,0x15e008068942586c4e04,0x242415e004c60484826,0x7c687b0e14c4e04406e2,0x44e003c507850200ae00,0x20861007f003e382821,0xc0a02050200fe007c705,0xc08810080184289c0078,0x7001e3062140861c3d89,0xb47a3700283020061062,0x4a288943487011e307c2,0x3014068311490a27011e,0x10822868a48513808f24,0xf8c0a0a043800f620c22,0x89c0848e08a382b81460,0xa3f028cc41c110a23919,0xa88c3887021e30281208,0x40502008c5e03183e3c2,0xaf018c1f1829c013090,0xf8ac66283f80261410c7,0x8e14e031866284b80c60,0x828558ec6e007c50f855,0x7f018945102c0fe05158,0x3128a205825c0a2b1050,0x2c30c02380c4a29012e0,0x30803ec4a37028a342a1,0xf003e282b08140784380,0x8c388313810f14200a07,0x84e00428c284189c0078],#[0x4e00e440807f800f162b,0x1380151415c3e1704124,0x83e44e007c012041204d,0x801f0d8e106284f81441,0xa0922700304f0048182b,0x44e004060805289c0078,0x85021c0a203c5e18818b,0x148947e0518404f004c1,0xe8dc0620e43e170489c0,0xfa38238146182a140451,0xfd118dc0628dc004401,0x400c05c0130a26e00420,0x3c50903d8ac6e051060,0x745627021e3d143ec4e0,0x187e8bc06204060c0218,0x8c180430e8ac4e04407e,0x9c0898a1f0a84989c009,0x101824c4e004c461c498,0x31f80c61b880f0a02b80,0xc1408313800f1588150a,0xc00f8e0ae204029c0078,0x30b801f1010100788029,0x288287c122022700505,0xc6048938026103e09057,0x4e003c50a040400fe007,0x281110627021e5080214,0xa0a7003e3b0e05010c4,0x6128e12e04505040401e,0x4c1850080aa3f028c3,0x689c01c1220227004a27,0x2a270026308010030100,0x48080f637018a3020061],#[0xc30c0220501853138048,0x1e130a63b118dc01a12,0x28c382810030100589c,0x47e031060a8200809a3f,0x118dc06287c5048228d,0x1e302008c563f003e3,0x7837002828200610a27,0xa0e1483c1b801f1411,0x1f81861014086241e0dc,0xa43a198808e00507a26,0xa0c08c38538186100d,0x1989c00a0cc4042190fc,0x90441a0fc00c0e08c3e,0x8601208c351381871d14,0x378186170f86a2700282,0xc4048370dc04a8cc4048,0xc307c54a83781860f8a,0x541a096261b8032560fc,0x70c30341386627012a32,0x6e00412a30412ac4e003,0x112a0de0618482835898,0x70d87e05106a261f0dc0,0x6c387e89860570060a82,0xe061860202b0e1fc3700,0x30f44e06185105103f87,0x2a2d130c1fc3f002a302,0x438210dc01e8986c3f00,0x812c4c3f030c342a12c4,0x402c250ec4047010c302,0x83c1b8089141387c3700,0x37003e3e1b0fc00f8818,0xe09e061850c0510e084],#[0xe2083081fa37028a3513,0x207c27c0a28c22e05143,0x88200fe128fc0a28d470,0x1f827001e2b0e8bc00f,0xc0130604e107f8026142,0x1209c3e082848231409,0xc15c3e0f00482f0c25c,0xc11c10af00482883801f,0x40a0fe1380207f80260,0xc160fb1709c0630dc012,0xc0a38c170fb1709c0638,0x228fc0a30b182345309,0x118a2b198b84e003c510,0x87c20278186158e10e06,0x60a090461f0dc00c0d,0x549222e008450692709c,0x300c1c9253e0060a428,0x4e0030943928934106f0,0x241984e003460c1241b8,0x6a10341818e012460c1,0x61286251241b84e003,0x241022e008452483709c,0x42248208253e0060a439,0x860909040962404304c0,0x10401208240f083e1207,0x784160909830f858240f,0x40c24440786160784160,0xb03c3090584c183d874,0x830503c22203c20782c3,0x2c0a0a144487860fc082,0x8880f08240f08400108,0x10581e0a0f030f0b020f],#[0x20903e881e041e10801e,0x44407860f2207c341d10,0x81601101e330c1e440c2,0x881f0f02088302130d85,0x481e1e0410b048401824,0xd101078212078103220,0x2b0210308610026041e,0x50f0c240f0824083c241,0x98810498810488811122,0x6210643c30903d88189,0x581e103086c40c154362,0x3020a40841f050068820,0x404841f0520430530c21,0x22024241049098104884,0x104813810f8912226061,0x30f8212c0a1088209b02,0x6840f8581848484c0824,0x43e205b02090f0284220,0x44404840a0f840ac082,0x2091302087c113020922,0x8104861204d103055130,0x841f0409810487440689,0x581048612070208020c0,0xc4851130309101581081,0x88102b02c40c1409c087,0x103e160612102588107d,0x10c3e08283e16058813,0x60904c4a182a02250c15,0x544081e4409061609041,0x810b04820f83c2416102,0x1381090609c0b1024204,0x982849130312104c1208],#[0x189810903c40fe042048,0xe0430909820fe04240f1,0x424182424c4c088260f,0x48982c0c482420982426,0x60787c30f84820f84820,0x7440688120a880f09061,0xc2416044c1f0c0981090,0xf8226042c120b02087,0x4103c104e0420903c200,0x448943c30791024183c2,0x21262040f6204091304,0xfc13022310162098289,0x26041226084d04c08626,0xac183c30782b0781620a,0x82c3e1444c0898310040,0xc4130781081e83c08298,0xac3061f0503c307e0f02,0x781101e0a620620041e0,0xc88242b0210801052130,0x3e1e0f028422080a4220,0x5440c1344c3028462404,0x83c08284a261814183c1,0x78109021f08401f082d,0x204c30283a220f020a13,0x860f0c0a0c10fe182100,0x44182a1e260c1e102415,0x981850986100409c3054,0xc410140961e04402c248,0x4081409c088040503f0c,0x7818504200414c40840c,0x440102b0cc40d88c3100,0x813861006200440082],#[0xb6041e1849080f0f0c2,0x812105810905820b0282,0x400013020a04a1302205,0x412048583002c0a04e04,0x3041607841f07840a0b0,0xb002c0f1986160786161,0xf8581044d810986c2c0,0xf05060913040f0b0504,0x1218244c107c240f0d86,0x700c41c1e0848161828,0x44c160700387c1583c16,0x1c00a0a0a31038542508,0xf0581c031054260f058,0x801412c4083e08281216,0x8108b440f8444c1e0b03,0xb00c10c03062360b000,0x140460b02c1c0060721e,0xa0c890460b03800c0c,0x4343448c180683289c,0x240f0811440a0622047,0xb1041303c20903e82c41,0x4a1ec4a0881204240fa0,0x7b1030b1058819108214,0xf0813410813416206120,0xc0c2589410c3f410a820,0xc2c207d89410c82c4082,0x88084813410b080aa083,0x29881880120a6208c405,0x1080184a121418281048,0x14c40888082588102988,0x428082028105508140c,0x430886140830080a0614],#[0xa2082030291028080c11,0xa1d08122a1284150c280,0x4a108942168415082a44,0xa128742220b43a104158,0x11821f102a09a1a1040a,0x81210408613223085091,0x85450ad102049103e182,0xa1461c10882860114461,0xc1e1608881f081244082,0x7c308308481825821f0,0xe0a61b0982c0a20ec361,0x1f0502688207c15040c3,0x82180d8744082a14a206,0x4120d1012130c3e1051,0xa220203020241618214,0x20400e8818541014a208,0x441200e082250c30250c,0x186011430c3008a250c8,0x86088460408430451286,0xa30410181208090c181,0x43a208080c0489823083,0x86011446130580306010,0x8300821d1040c022881,0x411086202089430c2a14,0x10c30a8501143620a180,0x2189430c1044a1861804,0x82288c30e88087d8210,0x8a1f043ec1084cc10888,0x440430c20430982c061,0x1044618b4404240f223,0x3083f4409820b0410a85,0x17082c0f0810c30810c],#[0x131016203090414c4082,0x21303c20502688188012,0xe200814c360d104a2054,0x10150c28c1081544083,0x12420c02056205410186,0x743a0b10385112821854,0x2091108704101484220,0xa0a88182028151012208,0x22040922041582110304,0x12608544050544050420,0x2a086186c30406036082,0x1414c40840c40810c308,0x8c21040615049103008,0xa4711020321b04300c1,0x2416085020c034868961,0x841544b08300815140a,0x6182140d121804068a6,0x8188288107c1e1021121,0x3a1090304d083043042,0x10105010a82028182189,0x23061027061053061050,0x30c20a88040a0228818,0x84140420c30a20902801,0x92a23130702048808c1,0xc3e28630782048808624,0x128308141f081408a260,0x2a8987048983c1040904,0x48744c382430a8268818,0x208418709061f0809870,0x408c387820a858704128,0x305023061f101587081,0x10c4083e8362060ac3b1],#[0x7c304e1d8818203ec40c,0x78a160785830f840ac18,0x50420510424230d84c00,0x102c0a0787c40907c205,0xf8404a087c3055042c0f,0x10f85411007c30f82120,0x417a109030f820a0f854,0x287420f894212040a120,0x508401f0e86084e86101,0xa387c20551c3e1d083e1,0xc260b0040387e0814101,0x485041007c30481186,0xe106182140c120410062,0xc10f8ac31007e08230c3,0xd0e8541a061060b03c14,0x4088250a82c1a005080f,0x840c20840c10810c3081,0x861861f043f8408401f0,0x410f820861841505820,0x87f08107c14c00d840b,0x10c30c00530410c31308,0x8160787c30f829801828,0x180a0218628541043608,0x86282182c30c3ec10882,0xc028281f12311404106,0x5022861f1015430c0504,0x82103c1c20242a187c20,0x6184080a04c204200825,0x8]]
set_option maxRecDepth 16000 in
def g247H8 := limbs80 #[#[0x2060105040002031500,0x700030002240301060f,0x2010405180401080205,0x25000502061600160c02,0x401170302180f071508,0x10b0c00090100100300,0x18021213040a07051413,0x3550b000e03070b0002,0x11210d09001d000e0000,0xa0305160d00070000,0x3000401000102051400,0x10000b0502251a241b24,0x1c131300010303061342,0x101100e03051903020b,0x1230401010708050a0b,0x11030608090015041802,0x208000a290c16000300,0x5917140f01010008012e,0x35030001060a1101010d,0x113d0901010001023c14,0x1354070b050001050101,0xf7c1f1f12206809052f,0x3f06011b0c452b1c1c06,0x132f073a0c1a092b0200,0x20e00021f0006140b21,0x1d0503000b0401570500,0xd05060a132c0001020d,0x705010300023f078327,0x31412052f0104500200,0x502071300b005070400,0x6016411003c68080103,0xd0a1503043e07044f00],#[0x4030b15a30007041203,0x23e220300213709012e,0x416f17061103011f4319,0xcb530000c402826302,0x5be1cf0000000013a700,0x1441c9212b0000e26821,0xc101b92221f1c3226e91,0xfb2bc390f0f434527e21,0x8cd465c98fd2f1c43e52,0x27b25709c6627c6bc4c0,0xe7003f815fca8da048c4,0x3f04173b679039d199c2,0xd1b4600000715e000008,0xa280e6509ac016f3cad3,0xc03df3bd5430d1f871,0x72a0319203304f89fb00,0x550000f293f25ab0ca60,0x44443db26d200562d022,0x480af5e06261bde42270,0x2431b407d017a051c8,0xede415017c3085431800,0x16d2e6409ce0e9841af3,0x6f28a02d7c28e5ab222,0x613c380000512e039d83,0x61c15d83b2b01b6340b2,0xc000010e5c2fa199af3,0xa5625800000000917404,0x40942cc1529182e34b0b,0x590000c1d203afd2bb81,0xf6e28bb313d8dc82b912,0x12f24320d35e111d11,0x9be10e61684ad5f24993],#[0x4e81920000e207fad8c2,0x7eb1ec714e90da8252c4,0xae000000000000229a09,0xe9f154108dd10094138b,0x1d82c8407530690000f3,0x3361220000000020a0b4,0x7c00000000000000ccd3,0x760000618a38c7000089,0x22bc59a1942353a2fb,0x42f40a911700004af000,0x98137f724c0000939850,0x3e8132baee0000eb35e0,0xd109c099f0fcf82231,0x5b000000004302000000,0x5cb237b04a523600005a,0x134771359b3f08,0x418900000000000000,0x51000000000000000000,0xd3dd82a293,0xa40000a11c0000b40e00,0x33d3b38b015888fe03,0x9e63c76bd872e2d3b800,0xfec267923f641c7bb7c2,0x2a6937a822e21,0x6c00009227e116c0be00,0x5e214bd2b8f2bff2f811,0xea4385000000000000c4,0x2c3a95402783d7711aa2,0x5d9166a34d32b429b16a,0x93f102303e0000d28364,0x1920a75037030d9341bb,0xfea19790656869f035f3],#[0x87c15353a1f1daa00992,0x1772c7c3230000f8031b,0xe10000c0ae0000dad27b,0xd9253014191e1e36d72,0xe05d13aa4184226b34,0x436035489caa35b00,0x4428c2a071527552ec00,0x1e41a3084c000058c053,0x7cc2d690528121526632,0x9fab5071246029385610,0x3f20ec000093a52366f3,0xb37800000000e35a93,0x975843e2113156718500,0x1ba23b0000000090ce0b,0xb3b90000c2cac118b9,0xad127850931127000000,0x4ba38000001c328136e1,0xee6220d11283ab23b5e2,0x9000041d4b2af5bc271,0x4410eb8800000000c3,0x8c34040000a1a7000000,0xed001c106c0000734a7a,0x60e881b40000d32d29,0x7d000080d93310e1ea00,0x60000028012d5c38c12,0xc17100009010603cd1,0xcb311043addb59d1f200,0x5f22e58312000000005a,0x43d4d1bf0000000053,0x92a242f290abcf935000,0xbcb19143f8444762b56a,0x1500005ac40000e1b2e0],#[0x207c370000000011a6d3,0xbbf13300c62421000094,0xe362c0810000e3c5f0,0xff72e00000f919ac3000,0xdd31ca81fc00000aa391,0xe45040b26fd18d423111,0x3cb3e700000ae049ce52,0x48932f12f0e85d4243c1,0xe7a38d6449f0ee02aec4,0x391b6c000042cd640191,0x19f1a461ebe3f109ccd1,0xc1a0891277439529c424,0x35104fb0f5161a07e93,0xaa808ab02e73430000d1,0x86321f60f49058b0e34b,0xca1f0907090ad9356d0,0x59b31d805000a8f0bae2,0xb1b17383f769f8e28fd3,0x22004133d90c3403ac32,0xf60000704691a0407f93,0x38943268c30000806103,0xdb5d9316a2243159f3,0x64b282d16d92aa000000,0x79016f01785adec022b0,0x2c016bf2ce50aab0f8f3,0x887a8659d681b39078d2,0x9401385446335240970a,0xc19bd3a8bac1706b401a,0x38122ae86b73ea202410,0x71e8597369bb9b299f64,0xa1db750000c0abd0209b,0xaa0400000000439bab],#[0xfe18b93ba7125101900,0xfa0000f27a02c0e276e0,0x66b3dc31ac12a05376a1,0x13e2474a87b15ca073f4,0x791e991f4a3cd0a7fb0,0xb144f80fec0a2805773,0x182147697b53862a5af0,0x9f6429d857d39c10005b,0xbb0ad3a269b441eaa1b2,0xbd918e000062b2a148a8,0x654123721d0000000090,0x28b17b442d000090dc33,0xf481f710fa03c313b3c3,0x45b2132210000090a532,0x1e634cc29deaf10000c3,0x120000e2a831e4000054,0xc34e6b7223e62301d4,0xaa000000000000f36b00,0x5b5006b28d00000228c1,0xb023894348c167583922,0x11608ec2183af650ef50,0x50b3f06b63,0x18837bf3b10461000000,0x1463be941f00f9906d50,0xa80000743b22e9217af3,0xdb2183c21a0000000031,0xb6ab99000030d0d1605a,0x841110c0000001,0xf2641825933963bf00,0xa0000a3b41863000000,0x8b03fd2113ebc1000023,0x7611280000d98d0000eb],#[0x213038209e91080000d0,0xdce35d105e0000b1b1f3,0xd1a02bb3f3c1b8bab562,0x6660b1123561bb725680,0x8b13d0177d1d9a0a470,0x5fa092106a1004b2b780,0x6a612acaf2125cd05582,0x88a08424330000e9a073,0xaf0d2e179bac3929680,0x1592c353dff1b50000e1,0xd1f14a3082b83a0000a0,0xeb30e4f1880000f1059b,0xcc0000fab4000072e332,0x40000093a0730421a913,0x510c000072052af862,0x1c91dfe1dc0000f07a00,0xf21aee194b1cd43b699,0xe8fa620d2453000022,0x1e00000000a06370e000,0x87e0e10000e44043ff80,0x19133461c4c18c98c8f0,0xc44ca20b80d80000f1,0x2b2611e200,0xa60000524ac32c317200,0x51d0f2c500000387f3,0x2dc24fa3670b81737e00,0x1ab5bdaeda9ae6b8070,0xd244c355a357413421,0xd6c8180000645af30800,0x5b19000031afb3b770,0xc578fbcb0e0000000000,0x85482483602bb00000d1],#[0xa4e3e2712061290000e2,0x1f73fa4452b0dd48dbfb,0x7200005bfbe8374458e0,0x4d42ada3c408d88164e2,0x604a97b37451bec2c281,0xcf0000f09d50f62332c8,0xdba080e2a400009b10c0,0x73350000a24ed1,0xb010b2eb0600004c2f00,0x91301aa2380151f1bce2,0x3a0000a028d450000030,0x782f33a8eb,0xb792a700008233532b00,0x90538ee0030000019c01,0x93da0251000023e103,0x649222810b61baf1e300,0x63103600000186404343,0xc1000062d9719500004b,0xc04da8312187e8267a,0xf26048c5621200,0xc1425422db31a1f43f00,0x12fcf0c409a25ac6b8,0x45231c60c350cb59c500,0xc261e680ea9281000014,0xe193b32e52cc614671,0x63e2500000bb8a000000,0x398c726592ac33e571,0x1f71d70000612c000000,0x9462860000d3c0d3f571,0x3c72a9b85422fd0000b0,0x286262f9000014,0x2f605498c60000fa9300],#[0x63e400a30000905f11,0x5cca98628c63c2642f00,0xde0b15eac90000b30c3b,0x8011a8513b13e3d051,0xc8b3d579cbd424fb2072,0x4f300c01e50000823ec9,0xefe33bf0560000017fd1,0xd600000000c288b19e33,0xc7628913c931f9425ee8,0x3754645292000021802a,0xe1000089c70000000041,0x513a9eaa27844f0346a,0xef5a49d229e396997d44,0x140248d462922f2a9ca2,0x4742bb20aca9d436c62,0x6000000000000cb1662,0xd1d1000058427451f2,0x7c000000000000000000,0x9c221bc2d262d400006b,0x440000630303ae6ae279,0xc067b030c03b64,0xc8b37cc454a12db0d400,0x98000051d3a181cc3160,0x27919d000012f6000081,0x5c413b2846ac03e059b3,0x721c53cb64596a,0xfbc45b32b6822543c600,0x5c9b927232f2eedba0c0,0xd041efb20220a1183ec0,0xa603e0d01d30fd91573b,0x26e97ac2d3c04b2397c0,0x36f22bdbab22a5811504],#[0x18c298539eb04922d823,0xcd5353a33d126cc37104,0xa2c04e00003b1c4245d0,0xfa0294b047e1fb02df1b,0xd7305a81ced8300000fa,0xf2000092a300002388c0,0x65242573f4106831cbc3,0x5f000008ecf196509fa1,0x6eb1b0130b102380de84,0x16244be2bde2ba7456b3,0xc8000062d19131e20164,0xce00000000529c0000f1,0x9e107d00007295a1c638,0x46a40600eb7443200e29,0x498060abb9f33c33bc82,0x3c824dcb27317e1230d8,0x79943583d60077000082,0x14c3d8929990f352de00,0x15000040af984a000010,0xa07b0000942e42,0x49410f9372d2f7a0db00,0x4f0000e3462bbd529181,0xfa3317222de270da5733,0x8ff3c800001c3943f9fb,0x38b0b500001391a9c963,0x73245126b8bf21f1c8,0xb3f32903f0d0d5439a00,0x17181e60c79457000032,0x570381c40f1ae6abd428,0x54390000a383d3feeb,0x58000000000000000000,0xd3c13ac9ad916ec03a3b],#[0x950000f2dd331f000050,0x8d1bc0e40392f5e326e0,0x25d3b092790368b0b65b,0x40e26305130e927f33,0xe2cf143a5130284500,0x11000000006223939300,0xa19394000041d8e8bddb,0x610000ab1fab4dfb4c72,0x714483840000910d2b,0x2a0000702100004a4b00,0x61d611ab611b0111f4,0xcff373d0ed0000314c00,0x3272623467c273000063,0xdf35ce28480b9c33ef0,0xa2c490e7cb6f000050,0xfc4a9611f580ac000000,0xb00000000d2393b547a,0x124b62e08f744a0000c4,0x87b44233fc3142c21920,0x3a144de1626190810782,0x4310c2518f58400208b2,0x6f71e0faf31bbe382ae1,0x2842dad1cc420ecad103,0xe0dfa414e3bb04,0x3362be183b33757b4e00,0xc4d16ad2717007c3eca0,0xc5c370102a3b9c0b2178,0xbbd253e881c0d3de90,0x450074317d9083000000,0x3a00007bd5411e885000,0xf583eb40f22090d0b863,0xbfea9972abe463040830],#[0x5a0000a150899d531ba0,0x41fa9100009175c337e1,0x25840013dbb05b214508,0x4ea3630226d0960349d0,0xd5ab95e06f42c6108b18,0x2c81a5b86a41fd3274e9,0x92d30f0000b45541c760,0x4f419b939953fb5217e3,0x1176831a9b,0x6a890000125d000000,0x6e000040027377c9f900,0x3d00000000d13fb00170,0x7b0000919ac3a3000072,0x9653eed26a00000000c2,0xcbc38a50a9000010ff1b,0x9b60c90000c409a2c942,0x81ede169000082e880,0x55533100003297f3e300,0x89e3e234d0532330e1,0xa3d2619f835890b700,0x4290f179282437b31e00,0xd0937db45c6ad412edd3,0x2f62c188294209702639,0x2a43ce82f3a1e8000060,0x7bfca1f3000070f773,0x35e41bb0b461d5000000,0x4c0382c80982ff400adc,0xa0]]
set_option maxRecDepth 16000 in
def g247D9 := limbs80 #[#[0x97010f3eb2ac35f5d741,0xb0875f5d443beae221df,0x31bdae529f9f4390e7eb,0xff5614c7faa0a63fdcc5,0xe3a263f798d31fbac698,0xd131bfce898dfd744c6f,0x98dfd764c7beb2a637fd,0x7ef31e63f758f31bfeec,0xf9d331bfae998dfc74cc,0xed98f7d65cc6ffba6637,0x507fba0a837fddb31bfa,0x3efd0d41f7a86a0ff561,0x7ac8a0dff73506fe39a8,0x76507beb2a83ef99141f,0xe83ef50f41bfeeca0dfd,0x1bfce7a0dfd73d07dfa1,0x7d65d07df32683ef5934,0xbb6837f5db41efaeba0f,0xd61bf8e6b0efd63586ff,0x1dff74586fe3a2c37fdc,0xfeb8887fd5c443ff2e02,0x90c43fba8621ff67110e,0xa21f7d6510eff39887f7,0xefeba887df5d443efcc,0xbf5d843bfeea21f7e751,0xeec21efe7610efebb087,0x350fdf21a877fdc543bf,0x87df59543fbcc6a1fdd6,0xbfeeaa1dfd7550fbf32a,0xd7190effbb2877f5d943,0x1c87f7d0e43bfae521df,0x43bfce721fde6390feeb],#[0xf7e6590fbeb2c877f5d2,0xebb4877fdd643bfaeb21,0x5153efca6a9dff7690ef,0xa9dff7454efe3a2a7df5,0xeffbb2a77f5d953efaca,0xf9d253bfae929fed7294,0xed29dfd7694fbeb2ca77,0x58effb92c77fdc563bfe,0x77f1d163dfac8b1efe63,0xfae331dff7558effba2c,0x7498efeba4c77f5ca63b,0xacb7f1cd65bfaeb31dfe,0x5efee2b2f7d71596ffb9,0x7e73597beb9acbdf1cd6,0xa1a63ff50d31efee6b2f,0x131ffac898ffd634c7ff,0x8ffe744c7feba263ff99,0xffa1e63ff50f31ffaec9,0x99331ffac998ffd63cc7,0xd98ffe74cc7feba663ff,0x7ff21a83ff50d41ffae,0xff5cd41ffcc6a0ffd635,0xaeca0ffd64507ff39a83,0x3d07ff21e83ff50f41ff,0x83ff5cf41ffcc7a0ffd6,0xffaeda0ffd64d07ff39e,0xe43587fea1ac3ff10d61,0x9ac3ff5cd61ffe86b0ff,0x43ffce8b0ffd74587ff3,0xffd6510ffeb1887ff50c,0xfb8a87ff5c543ffaec21,0x4d43ffaa6a1ffe4350ff],#[0xa1ffe6350ffeb1a87ff9,0xfffbaa87ff5d543ffaca,0xfd0e43ffeeca1ffd7650,0xa921ffd5490ffeb1c87f,0x90fff32487ff59243ffc,0x7ff58d53ffaed21ffd65,0xfac729ffe6454ffeb22a,0x7494fff324a7ff59253f,0xac7ff5da53ffce929ffd,0x3ffae4b1fff7158ffeb8,0xfd7458ffe3a2c7ffdc96,0xbaac7ffdd163ffce8b1f,0x263ffae931fff7558ffe,0x5d00c80170001ff9d,0x8133047010503580a702,0x1cd06c81970600169053,0x7b0970241088820307a0,0xd0bf82e30b202ad0a482,0xe903890db83570cf031,0x11842710403f50f683bf,0xc04d512e849f12104691,0x857b1570545149850f13,0x62118185eb17305b1165,0xcb1ad069919f86631910,0x91db87531cd07191b986,0x21108191fe87c31ea078,0x3b88d322e089121d885f,0x8098525a894724b090d2,0x8a5728909fd27889bb26,0xb152bf8ad32ad0a9529e,0xcb2ea0b8d2db8b4f2cc0,0x13148c373070c012f98b],#[0x33f0cdd3308ca73230c7,0x728d9f3610d693528d27,0xd0e5d3918e233820ded3,0x8ef73b60ec53a98e8b39,0xfa53e28f6f3d50f353c5,0x5b41010214008fe33f10,0x943a90cb42c109141d90,0x4671179456913f449110,0x91922b48411f547591b7,0xf12dd4af929f4a112654,0x939b4dc13554cd931b4b,0x45950f942350213e94f1,0x1b53f14d952f949b51f1,0x5569958b55c155154e95,0x5981649589960f57815c,0xc897075ba16c55a99683,0x517b95e7977f5d817415,0x986f614183160497eb5f,0x1882b810a2e3118a9624,0x3632502018610e0428c1,0xd102a24218f8d8b8838,0x98b8048989638ee20ae0,0xa62e01626201e1188242,0x8058a898807e3e322090,0x2a26201f8f8c2588298b,0xa0d801e28486e260430a,0x88362090782e0030d880,0xc36022428a2c1e0d800a,0x360078d0d0b80881e287,0x241f890d810a3020542c,0xd801e307e242e005430c,0x790862260428e25890b0],#[0x8c142c1e890d810a3a1c,0xc89810a3852242c36007,0x343602204c28a2c123f0,0xc360428c08150d810a12,0xc13890d80150a3096204,0x89810a38962436004c28,0x4a24360428e87124218,0x90a150c8980130a30f85,0x240d800a8836202e0030,0x2436207894360428c2c,0x4c342e0090d881f0b0d8,0x428c1f890b0d80243020,0xd0b80882429309436022,0xa421c910862260428f0,0xe0090c242c124c890d81,0x8141f0b810c304a24342,0x810a36207c2e005430d8,0x62436004c28c1f88150d,0x30a142c40890d810a385,0x421889810a3c2a260054,0x10a381e260428a8a8714,0x26005430c401214890d8,0x8c081e2d0d810a304c2a,0xd0b802c3854342604284,0x4c3604205428c4c141f0,0x8a071012250d0b802c30,0x42980203800807e20562,0x20922a360078d88021e1,0xe0098d88148d808a1236,0xc1e28158020284e2090a,0x8a898060562078a60080,0xd25208705023011271f],#[0x15801e38aa3a223600a,0xa8423a3600a0d8806282,0x60040f88148f808c1230,0x1429801e3020504a3a3,0x20409930a62e0221a882,0x8e89801e38a87e3e3019,0x8563a2600794282015,0x41f888d808a308040181,0x8b80883620a0860078a2,0x62856387a260138e158d,0xc8630118a898030a0863,0x8f808c38a8a23a260230,0x620423e0230e2a298810,0x2118e118c898b8030a8a,0x801e30504e3846362e02,0xe222a3e0080c25888a8d,0x12121388242b8026309,0x802030a63e28507a2636,0x8050a60079214281e89,0x1f898e2580601810082,0x2a260102a2826218d8a1,0x8e8980283218c480447e,0x8ae2042323e00a0e2a8c,0x12142a11888d80128e3,0x2028a07e3e2840822636,0x620303e00a0c881e2980,0xa0f882a280e0d8010384,0xf80283c3c3620562e00,0x22038360040c2a11890d,0xc30142888110f810c40a,0x810c1a3052243c3600a0,0xae204c3e0430c058813],#[0x3e0040c13890f80150c3,0x1412890f810c3c4a2030,0x8a30522436004c38c3e,0xfc222e0238c143f088d8,0xe00e3e082821801e3050,0xb09802a5638504826362,0x36012101206040226258,0x108f808c384e38462c26,0x54222a360078c142908,0x7c26014148e8b0980203,0x802440a0805636284638,0xa3600a0c282610218f09,0x150f0980130c3044223,0x4228504020a43c3600c1,0x81a2e00c060a0c108b80,0x206e0060c10924580422,0x308493081b801838c20c,0x50b0d801e38411601088,0x22242c36009078f08882,0x428e3e250a890d801e3c,0xd8088243100907c36022,0x3620942c360078c1f0b0,0xc360078f890b0d80241e,0x8250d810a1238b092242,0x3c22242c36004890f088,0x22428e2c24130d810a3e,0xd0b8088243100904c360,0x2430962436042848c130,0xc360428f8f890b0d8012,0xf881f0d0b80243090204,0x890a3c22242c36007890,0xc36022078c3e1e250d80],#[0x90d881f0b810c2430942,0xd810a4c3e242c360078,0x7a242c36013101e0825,0x78f881f0d810a1430b09,0x80890c3c22242c360050,0x42c36022078c3e1e150b,0x5078c1f890d810a14305,0x150d810a403e242c3600,0x7820542e043100e2c1e,0x260428e2d0d0a1f804c3,0x90b0d801e38b0907c34,0x8b07854342e0130e2c25,0x78b0d08241f0d0b802c3,0x250d0b804c3894342e00,0xe507c2c360090b0c1e2c,0x50907050215882029801,0x50241c1408a0807e00f9,0x8e3010882a8e8d802840,0xd808a3220807850a600f,0x20907a360228d88241e8,0x600a1015881e29802036,0xf808c1238422420aa3a3,0x4e1e160e0221089082a8,0x1014282089801e30f850,0x8c38c0a8a042223e023,0xa23e0230e11882a288f8,0xf8785828980284620a8,0x141e30504e1e160e022,0x50a0860078f8d8820298,0xa0c11888c8f80282a38,0x2821580885e223a36005,0x260098a4013068704850],#[0x2a10888c8f802840a892,0xd802840a082260078a30,0x2436043903e102a890f0,0x890f0d802a3900a840a2,0xa842243e0430f902810,0xa8c402a130c89810e38c,0xf810c12384a24343e00,0x6243c360048a8e102b89,0x28e2a08110f810c3e384,0x808a3e30f8b07a342602,0x8b8823e022920c12088d,0x1a0e01212088f808a3e2,0x858309803e1a16085022,0xfe1e160c2600e143f87,0x31014120987838048385,0x8c3e2840f8c0a4223e02,0x850a086042078c108f80,0x282109801e2]]
set_option maxRecDepth 16000 in
def g247H9 := limbs80 #[#[0x3e050001140a000001,0x30501010d080003013a,0xa0c0807000b05030025,0x17170016020560050000,0x50707092a0119000209,0x514090b020339002f02,0x1130002000700000108,0x2030002171001160213,0x713010d0c1b53100000,0x2f4d15000003151f122d,0x11030301020509190002,0x5000319150913252210,0x101010b000200040000,0xd101c1200000f010608,0x20004003445431f0304,0x11207060f1300050700,0x9031b080f26259d0d03,0x1023419030a060000,0x2290403610001111917,0x10a0026001104010016,0x100c0b000102040c79,0x8001c1f000807000306,0x334933060d0207158714,0x59173626001a14123712,0x25090a480001291e000f,0x2040635080f0e0d101f,0x1f281b19012f00052e00,0xe0b0f0a150a0d097111,0x141201007b3a0f01240a,0x5070c06000c0006170a,0x3f0a110a01014f1c0906,0x1349613b0e01190f0721],#[0xc95715382a00100d3f15,0x940004125a1dd54acc43,0xedc84100c4d52982d,0x326086ff46b971f27450,0xb8000700cc318a086db5,0xb13ee9a5126186d0504e,0xda8994088b2b5d400005,0xdc0e4000097be6379b5e,0x78270a79069be1d6b8c6,0x3a4eb4366e6a9067230f,0x89534bab10000c5af12d,0x1c6912be8f2c947c21,0x21c5aacb09aaca128330,0x8c0000000884e0e44000,0x927b70e27,0xf9a0001e7e20ba00000,0x185e725122ea20000000,0x9f78134000382c4afc0f,0xaf4b0000be7ca6ec0e90,0x10821a3ece4bd228388b,0x16200009f38000a5c18b,0x49f30c22a57f01a30d29,0x6113a01f1d1a7a9ff85b,0x5181ee8da4000086124b,0x8000b8699c1ddce92b99,0xb09f500008210e131409,0x3580800066a7e6,0xfb1f03af207a215bf5c0,0x4c194273585419ded9fc,0x5322c9b9248000d244f4,0xf097951fe5f6fb670772,0xf4afb4687fd0190c648a],#[0x6598c5b2157ed477ae03,0x322db03244a16674cdfd,0x12c408f3810055420000,0x45ea58bd6b3aa7b0ad63,0x78533756000214a29591,0x344130756cb10c57da6,0x5242afc5b80000d7ac01,0xe806202ae0eb2c0d1955,0xc6d7231a37582f61ab7b,0xf08bc60d5200006c50fb,0x827c55cca26000029bff,0xe00004a8b52c10eb5c18,0x380003974a640e65d85,0x3131e84b13412611a760,0xe3cd899e271cf7b0f91d,0x4db952d8000a0e80c,0x738cc21e0002d2015420,0xe6aaff86f0001b50d4c0,0x6620003d09a923c3bf47,0x64a1b6329ee9a756,0x416972420000172170fe,0x1837e7847d8000744f84,0x16df00000002ca91126a,0x12aba51cae3ef25cca85,0x471c58705e0000a3368a,0x80000882000187b50224,0x64ea99c000001d995dd,0x350a20ce14619741125c,0xb931094225400028abc,0x3a9d49eebe27ff7e79da,0x3e5024723eb70e31fe5a,0xb0b240aa9bd8d3f9e6b],#[0x3cdc1800045200a20db6,0xb0e44651d6648629,0x8000c00fa0be91080000,0x99004cb9fbed600ee6ff,0x5a20003c4500129ee239,0x6d3f4728edb414eab49b,0x1889ec2c21a800001c4,0xdf98c4fc0739e9721400,0x753c060800002e3205ec,0xcd96e000050e767ba563,0x5bbb1dccf643e800d16d,0x72f6af9f6bbc000265cf,0xb1da5bc7e879bed40fe9,0x2c95dd193cc681856445,0xc3b970ca00016fdb0481,0xf451e41da9255a294f15,0x85201ae9aec05d18a,0xd64400032603a310,0x94000102eb32c0000000,0x7392af0282903d3435cf,0xcb0670ec0e2f19ee8118,0x480000000927957c8930,0x3bc7e40181c2cf8f2ec7,0x5a6c059deca6d4d0000a,0x36b84800000018697523,0x62fea1849000000001c2,0x6954d6ceed8c0005b412,0x300060d86db5a338000,0x316da27b9b8000251400,0x96c0606194c5a67ed5a5,0x1308c6744f2edda,0x5b4e8db5c4eb68000000],#[0x4acb11e169e904055f81,0x4701ae3a012ffdc5bc3f,0xaed3bc800018dcb0f143,0x8000c0c00000000032f2,0x64000125d520b75508fe,0x184af21a98000000006d,0x621100000003816e8f90,0x6b5d91be600002998000,0x1981c1f8475300006d,0x301700017b745e210ef0,0x9c0003bf800004184649,0x1cb816f1a15222a3333d,0xd30f20ce000142e70f25,0xea907dbf746000cf117e,0x403e2a7c756a56e01722,0xec49cabac234212f,0x7c5c3000007a80000de9,0x31e4c94d087b71957062,0x762a89bd5d7f46679362,0xd505af3bcb384e2bb09f,0x7de2e295f18000669a64,0x896a23eac7c3976d83e6,0x2d8284bfb2720002335,0x4019b821abc48a5a1a00,0xc70fd4c5ed39e5c84c16,0xc00d0e134d63a6de098d,0x21ae3f0000730a36d2e4,0x22f700006c0800025a3a,0xb8000116800000002f74,0x48f00000000fd,0x10f6800076fd0,0x4fd8000d5e517dfd24],#[0x4e35fd3918e01000,0x800060f66627fe0bb5f0,0x3955f120255b5a3,0x2195c9cd536a00,0x20fa0000540375d0,0x988288000e0a80000000,0x193721af000000017e,0x557c929308980005ae50,0x600000958e792a07c000,0x40f1c5f5ec2ba37458ca,0x8000000089b64d11bf11,0x88000385a00000003c27,0x65bcfd00002101d38da3,0xc36670880002caf00001,0xc80000971000085d8411,0x7abf56c000000060b0fa,0x30acb6892e93139dcb89,0x6000041dd30e08678000,0x801c36682800009b3d09,0x23b60001142d40b00002,0xd207a5a5c00000000000,0xe0a03c71e7d9e5641c11,0x3cbe0000ce200002,0x28b700000000000,0xde748272b50000000000,0x62dfd27731498fe7,0x18000000000014a6c000,0x41000000000000ed0ce8,0x4fc4485b1c0800000008,0x140002708c322cefc000,0x6a94a941288000000145,0x836d52a0003273ceece],#[0x8608e9b1c2556ea7fcdf,0x3dbff4000063970000e7,0x502121a8000039ed,0x427cabaaf2584f4c000,0xc10c4489c71f0bc33ae0,0x906d9551a1068a353bd0,0x8986839b0530781ca11e,0x19ece3d9ab12feeeeb2b,0xc0f5d5aba90859801169,0x51e100b3a903bcab173,0x621f4dede6110e2065c6,0xb1d416660ec1024f1218,0xe519218e8108ae29c097,0x147e7f9043000052efe0,0x188f223ad0c38ebc,0xd0838b28d00000002464,0x31ec000397b16d654,0x8f5242018eb000008040,0x97decff9da0a53a509fa,0x50443e80002b32607ec0,0xe30860e2d4280003,0xe40000000e7c1fd19b88,0xf5000019c8070af0c92b,0x817c9079796b9fb65044,0xf4f44a96c781c5b54c9,0x34c3836cb766db000133,0x62f0001e9340001399e,0xf794183be32b79bf931b,0x3980b66050ea1daee597,0x668a6bb44493d3588845,0xcb5611782f0f34167073,0x69b88bf254500c788],#[0xf382413b43ddc5923d10,0x1520eb79854ceb6f4dc,0xd66c61f93edaf383f400,0xd55300006cd985fab1a0,0x20a9dac00000000210b,0x116825c512e400,0x3228048e000000000000,0xe848189e7e0cc0000000,0x28e000050b5aac93e9ee,0x5b4f0552000313461a01,0x13430001cd44000,0x74ae2e00007b3f34fc00,0x61cfd213af931bf00002,0x14ed8f6992cffc90000,0x10fac1cd9894729c00,0xea19959a6acf06efa4c0,0x2a68a4f3647302c82876,0x6ea0000948a08b000143,0x800000012808d2a80002,0xed50a01b298324c4bd2f,0xf34544c9929a75f0a,0x800023776fc86f9998a0,0x48000038500000000006,0x1f024c8000711f62228b,0xe0b9974e000215d00009,0x280c33774569fbc0db0,0x14d6a7284e236f17a163,0x8000f6f800000001af5b,0xa8000000000010e4bf2c,0x590964bd5080009977cb,0x98df36c0000057c31add,0x7ecc949],#[0xe8dd5d8c05fb5ae00,0x20aafa0494ec000107a0,0xf0000278e6a5e00025ac,0x97c3e5550508c9401401,0x5a72d78728fc4e5dcd30,0xf30a83f34d0480000000,0x3a0a5e55f4c21cc63c6b,0x7aaa5c4bc3840004792c,0x229e00014be8000,0xaeb06165f1030c5b5e00,0x7bdc73705d3a4d4d9ba5,0x74000638174f1aa1f076,0x4ae0000000090b0d3036,0x1b62137224c00000004,0x5e2724bb781ab61ba2fd,0x2a2c4ea271000034e3a1,0xcd8f757d8929cce70145,0x367bf45fcaaa17c68157,0xf616f9c81d9a669dc,0xd18244160f1eec779400,0x415d9d87f961c4ac3c25,0x2c76598000094a83b866,0xc3b836fa8a5e89df5408,0xf0463e16595a6840bca6,0x4c266b1a300007469d1,0x80004df600034d5ce605,0x6ef4f58ff4f6dc6,0x8fea8cc0005c2f2dd200,0x8000c51c00039cb1aee1,0x1c820000a6940000034,0x129517056029674200,0xde1400062f10],#[0xc35156b5bf23684ac000,0x3de000000052c901b4e9,0x9cd900000000217108f1,0x8c000302b9169452ceb1,0xeb0ece5d12b75a1a0fc8,0x662ccc5d8725cfb47644,0xf4e980000001064976f,0x2678a0545da35550bbe0,0xe092b4c72f6e583941f7,0x837bf872984a46318413,0x6a527fd9e2aafb058b5d,0xd21ff64f0bfe4defaada,0x86d32f8556a0d20def46,0x1ae77d3929e194e6233b,0xa14403876c34ba7d9c74,0x70cde038085bdc57455b,0xe0c6e8bc71a244c6c525,0x8b45410b4289e99a0969,0xd405869b37d8be2788f5,0xe22c26953db21e967dcc,0xa0a8f7dc036d21879e4c,0x67bc8841831862b8f865,0x67782f9436019f87bcb5,0xda0304c86220000404e0,0xb7966380fd628c41d08c,0x48b44f400079aa0000c4,0xe2eb903405075f6ef94b,0xbf88e19d80000ee57bb7,0x548a89f1316fff63222,0x398de4ce08e6510486b5,0xdebc1800000002bd3978,0x383c3ce48a1842000115],#[0x1fcddb839da80003b23b,0xea115d37664b26b50cf5,0xcb708578c721b400006d,0x674a408fc73a20d0137d,0xb81f9a0adb20cdf44000,0x87824525b3755c348,0x3143da6c292c00079880,0x6398c4c211acd88a6d95,0x4ee0000dba2b8471ac86,0x98c5764363374b480002,0x807c6e42618e745c10d7,0x1c8adedd1df12ef03b83,0x62df256b0adbba482350,0x8d5a0697a06c8e46be5e,0xbe7464a7caa389005c,0x13caf218806d37511759,0x162f48ad]]
def g247D10 := limbs80 #[#[0x41ffcc7fd31df9977d65,0xfd43ff10ffd61ffd07fd,0x8ffd63ff94ffd53ff90f,0x2586d11022003fd65ff9,0x9021779da9601113a0bf,0x12006101c509004a9e69,0x40b0030a3e205801850e,0x2c00c2928816006144c,0x8e3e01e5820580185151,0xa488468a1018228049c4,0xc48e3e0111e2468b0052,0x28829103c00c34628422,0x11e3450900513103400e,0xc00c34628422c71e1201,0x1810103]]
def g247H10 := limbs80 #[#[0xc08020ca800444501,0x20402181419414479252,0x10600041800c00d8210,0x4d7160001172083840e5,0x1400481010e082a02609,0xd281cea28000300085c5,0x9537000063f9bb000440,0xb1143dae51a1a6c00026,0x8c79e3b2810f33972f7e,0x1512f1ebe565d10c51f6,0x84ce386a1a6c807b012f,0x90b08b46c08020002878,0x3058d0b640fef94a82c1,0x94a2e64b21000014a11a,0x2bbf5cdafe2f6ea455,0x4800000061943f10a40,0x51cb4b99709f3494a989,0x1120078526000b090003,0xf87e5afb5545eaad6000,0x9fdf41af16b00f42b52a,0x2959e55a000717fc4664,0xc2944fef38cff382061d,0x9a94f188dd412686d53a,0x18b63d029a690d7e6b4e,0x56052fb6c1d69a2c0803,0x52bd0001195c11627a23,0x33917e7652c000087783,0x460000680001d78fc541,0x381d0ba0007420000a,0x80c131f28ea54001e5b0,0x59400000d224811a0,0x449ce140007880000422],#[0xa5418001457790c3049b,0x18000000b2097040017b,0x942aa684ee06300053,0xf5227d3007c443120,0x9143ae20d9ca70000,0x6164000b49110b49af30,0x60000005481967f0f000,0x406e49a02f72454a447,0x2a640c246c15028c300,0x110666c66beb4a,0xf400122a0,0xe63d044000cb1c51725c,0x656d2c80000001031ab7,0x578b6a67146492406e56,0x7800163340740f986ca5,0x42964800163583930bea,0x7ef2cd5ef1c52ebcdf6,0x857323fad027b613218b,0x849214006124e800061d,0x1b2a0571fc000c9cdde,0x20003347474000000000,0x6000c62363095eaada2,0x592c25a380bcf02970,0x85dcc503b09c6ea96400,0xc1d76c42b9e30305b0dc,0xc8f386222900035a9cae,0x500012b292c000139693,0x70c04832fbf8002e74e0,0x4500008b80008e220,0x24542bc948d04b3b1000,0x89ffb1bb30384000316d,0xb8d40007790000001f11],#[0x394c0ea000539]]
def g247D11 (j : Nat) := if j=0 then 0xe20c2802ff else 0
def g247H11 := limbs80 #[#[0xa87072000224d4042a12,0x1eda5787d60042d8,0x5a800013b898d80000d7,0x60039138000000001c9,0x7ac60007ae82c80000]]
def g247L : Nat → Packing
  | 5 => (4,6,6,0,0,5,0,g247D5)
  | 6 => (251,5,6,0,0,11,0,g247D6)
  | 7 => (1128,4,6,0,0,15,0,g247D7)
  | 8 => (1019,3,6,0,0,16,0,g247D8)
  | 9 => (213,2,6,0,0,14,0,g247D9)
  | 10 => (15,1,6,0,0,10,0,g247D10)
  | 11 => (1,0,6,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 19 0 7 2 1 g247H6
  | 7 => lookupWord 75 373 7 13 8 1 g247H7
  | 8 => lookupWord 349 1721 8 16 11 1 g247H8
  | 9 => lookupWord 328 1619 8 15 10 1 g247H9
  | 10 => lookupWord 72 359 7 13 8 1 g247H10
  | 11 => lookupWord 6 41 4 9 4 1 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P5_0 : block g247 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B5 : block g247 5 0 4=true := g247P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_2 : block g247 6 2 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_98 : block g247 6 98 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_194 : block g247 6 194 57=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 251=true := (@block_merge g247 6 0 98 153 (@block_merge g247 6 0 2 96 g247P6_0 g247P6_2) (@block_merge g247 6 98 96 57 g247P6_98 g247P6_194))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_1 : block g247 7 1 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_97 : block g247 7 97 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_114 : block g247 7 114 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_210 : block g247 7 210 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_306 : block g247 7 306 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_402 : block g247 7 402 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_498 : block g247 7 498 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_594 : block g247 7 594 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_690 : block g247 7 690 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_786 : block g247 7 786 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_882 : block g247 7 882 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_978 : block g247 7 978 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_1074 : block g247 7 1074 54=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 1128=true := (@block_merge g247 7 0 498 630 (@block_merge g247 7 0 114 384 (@block_merge g247 7 0 1 113 g247P7_0 (@block_merge g247 7 1 96 17 g247P7_1 g247P7_97)) (@block_merge g247 7 114 192 192 (@block_merge g247 7 114 96 96 g247P7_114 g247P7_210) (@block_merge g247 7 306 96 96 g247P7_306 g247P7_402))) (@block_merge g247 7 498 288 342 (@block_merge g247 7 498 96 192 g247P7_498 (@block_merge g247 7 594 96 96 g247P7_594 g247P7_690)) (@block_merge g247 7 786 192 150 (@block_merge g247 7 786 96 96 g247P7_786 g247P7_882) (@block_merge g247 7 978 96 54 g247P7_978 g247P7_1074))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 95=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_95 : block g247 8 95 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_191 : block g247 8 191 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_287 : block g247 8 287 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_383 : block g247 8 383 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_479 : block g247 8 479 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_482 : block g247 8 482 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_578 : block g247 8 578 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_674 : block g247 8 674 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_770 : block g247 8 770 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_866 : block g247 8 866 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_962 : block g247 8 962 57=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 1019=true := (@block_merge g247 8 0 482 537 (@block_merge g247 8 0 287 195 (@block_merge g247 8 0 95 192 g247P8_0 (@block_merge g247 8 95 96 96 g247P8_95 g247P8_191)) (@block_merge g247 8 287 96 99 g247P8_287 (@block_merge g247 8 383 96 3 g247P8_383 g247P8_479))) (@block_merge g247 8 482 288 249 (@block_merge g247 8 482 96 192 g247P8_482 (@block_merge g247 8 578 96 96 g247P8_578 g247P8_674)) (@block_merge g247 8 770 96 153 g247P8_770 (@block_merge g247 8 866 96 57 g247P8_866 g247P8_962))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_8 : block g247 9 8 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_104 : block g247 9 104 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_128 : block g247 9 128 85=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 213=true := (@block_merge g247 9 0 104 109 (@block_merge g247 9 0 8 96 g247P9_0 g247P9_8) (@block_merge g247 9 104 24 85 g247P9_104 g247P9_128))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_2 : block g247 10 2 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 15=true := (@block_merge g247 10 0 2 13 g247P10_0 g247P10_2)
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
  · exact g247B5
  · exact g247B6
  · exact g247B7
  · exact g247B8
  · exact g247B9
  · exact g247B10
  · exact g247B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := lower_forest (g:=g247) (i:=0) (hints:=1348) (before_sound K246 V246) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K246 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V246 low247 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 12 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 12 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K247 V247) (8, 0, 247, 0, 12) (by decide +kernel) (by decide +kernel)

theorem replacementMargin 
    (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length+1 ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  have lower := g255R
  by_cases big : 15 ≤ gates.length+1
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,witnessSize.symm ▸ big,witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,by omega,correct⟩
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

end PEqualNP.Outside.L_meta_51754
