import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_32291.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_32291
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffeffff,0xfffcffffffffffeeffee,0xfefefefeeeccaa00ffff,0xfffffffffffffffffffe,0xfffffffcffffffffffee,0xffeefefefefeeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[3,5]⟩,⟨.or,[0,6]⟩,⟨.or,[3,6]⟩,⟨.or,[4,6]⟩,⟨.or,[0,7]⟩,⟨.or,[1,7]⟩,⟨.or,[5,7]⟩,⟨.and,[10,9]⟩,⟨.and,[14,12]⟩,⟨.and,[15,8]⟩,⟨.and,[13,11]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 1, 0, 0, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 1, 0, 0, 1] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 12 sevenInputs.toFinset) (gates : List Gate) (o : Nat) (window : gates.length ≠ 14)
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
def g73D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
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
def K73 := extendKnown [] 4 [(73,[]),(97,[83,67]),(98,[16,83,67]),(194,[16,99,67,84,117]),(200,[48,16,33,98,66,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V73 : Known true K73 := extend_ok (m:=73) baseKnown low73 (by decide +kernel)
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
def K43 := extendKnown K73 4 [(43,[]),(139,[112,16,49,83,101]),(163,[16,115,67,100]),(169,[48,81,33,112,66,64,100]),(170,[16,48,32,82,66,116,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V73 low43 (by decide +kernel)
def g75Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g75C : List ColumnInfo := [(2,0,73,0,4)]
def g75A : List (List Nat) := [[],[48]]
def g75D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g75L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g75D4)
  | _ => emptyPacking
def g75I (_ _ : Nat) : Option (Nat × Nat) := none
def g75 : Forest := ⟨75,4,fun i => g75Y[i]?.getD (0,0),g75C,g75A,g75L,g75I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75P4_0 : block g75 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g75B4 : block g75 4 0 1=true := g75P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75T : checkedTables g75 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g75 0 0 0 = true)
  · exact (rfl : block g75 1 0 0 = true)
  · exact (rfl : block g75 2 0 0 = true)
  · exact (rfl : block g75 3 0 0 = true)
  · exact g75B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75G : graphValid g75 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low75 : Lower true (varsX 75) (graphGoal 75) 5 := lower_forest (g:=g75) (i:=0) (hints:=99) (before_sound K43 V43) g75G g75T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K75 := extendKnown K43 5 [(75,[]),(106,[16,48,32,82,66]),(195,[16,115,67,84]),(225,[113,33,83,66]),(232,[48,81,32,114,65,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V75 : Known true K75 := extend_ok (m:=75) V43 low75 (by decide +kernel)
def g99Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0)]
def g99C : List ColumnInfo := [(1,0,98,0,4)]
def g99A : List (List Nat) := [[],[101],[16],[16,101]]
def g99D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g99L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g99D4)
  | _ => emptyPacking
def g99I (_ _ : Nat) : Option (Nat × Nat) := none
def g99 : Forest := ⟨99,4,fun i => g99Y[i]?.getD (0,0),g99C,g99A,g99L,g99I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99P4_0 : block g99 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g99B4 : block g99 4 0 1=true := g99P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99T : checkedTables g99 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g99 0 0 0 = true)
  · exact (rfl : block g99 1 0 0 = true)
  · exact (rfl : block g99 2 0 0 = true)
  · exact (rfl : block g99 3 0 0 = true)
  · exact g99B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99G : graphValid g99 (boundsBefore K75) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low99 : Lower true (varsX 99) (graphGoal 99) 5 := lower_forest (g:=g99) (i:=0) (hints:=85) (before_sound K75 V75) g99G g99T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K99 := extendKnown K75 5 [(99,[]),(105,[48,81,33,32]),(201,[113,33,50,83]),(202,[16,48,32,101,117]),(226,[80,113,32,50,67,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V99 : Known true K99 := extend_ok (m:=99) V75 low99 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(1,0,106,0,5),(2,0,105,0,5),(8,0,99,0,5),(32,0,75,0,5)]
def g107A : List (List Nat) := [[],[80,49]]
def g107D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4e09f
def g107L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g107D6)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,6,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
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
  · exact (rfl : block g107 4 0 0 = true)
  · exact (rfl : block g107 5 0 0 = true)
  · exact g107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K99 V99) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K99 7 [(107,[]),(203,[112,16,49,83]),(227,[16,115,67]),(233,[48,81,33,112,66,64]),(234,[16,48,32,82,66,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V99 low107 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(1,0,170,0,4),(2,0,169,0,4),(8,0,163,0,4),(32,0,139,0,4),(128,0,43,0,4)]
def g171A : List (List Nat) := [[],[113,83],[16,115],[16,48,80,112],[48,117],[48,81,112,16],[80,49],[80,113,48,49],[112,16,49,83],[112,81]]
def g171D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g171D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1a0fd20fd10
def g171H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6
def g171D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g171H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x680144000002,0x9c02db0f40000002d401,0x38032c00c80000000002])
def g171L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g171D4)
  | 5 => (2,1,3,0,0,4,0,g171D5)
  | 6 => (1,0,3,0,0,0,0,g171D6)
  | _ => emptyPacking
def g171I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g171H5
  | 6 => lookupWord 2 29 1 8 1 3 g171H6
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
theorem g171P5_0 : block g171 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B5 : block g171 5 0 2=true := g171P5_0
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
theorem g171G : graphValid g171 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=268435539) (before_sound K107 V107) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K107 7 [(171,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V107 low171 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ffffe1ffff90f0,0xdc966000000000fc0fff])),(BitVec.ofNat 152 (word80 [0x48520a4044081010c0,0xcc846451451451451451]))),((BitVec.ofNat 152 (word80 [0xfff800fffe1ff8380b,0x3c8d9000fc003f03f000])),(BitVec.ofNat 152 (word80 [0x80602c028040213802,0x3c0d00c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff00001fffff6c,0x1111203f000fc000003f])),(BitVec.ofNat 152 (word80 [0x80300b0881402d2c,0x11110186186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffe000063f,0x8a23500003f00003ffc0])),(BitVec.ofNat 152 (word80 [0x1104408c001182063d,0x2221924924924924924]))),((BitVec.ofNat 152 (word80 [0x984,0x46680fc003fffffc0000])),(BitVec.ofNat 152 (word80 [0x20080100002000000,0x208208208208208]))),((BitVec.ofNat 152 (word80 [0x6651,0x63c4cffffc0000000000])),(BitVec.ofNat 152 (word80 [0x1c0700e0111c044251,0x42c0cc30c30c30c30c30]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,7),(2,0,233,0,7),(8,0,227,0,7),(32,0,203,0,7),(64,0,171,0,7),(128,0,107,0,7),(3,0,232,0,5),(9,0,226,0,5),(10,0,225,0,5),(33,0,202,0,5),(34,0,201,0,5),(40,0,195,0,5),(129,0,106,0,5),(130,0,105,0,5),(136,0,99,0,5),(160,0,75,0,5),(35,0,200,0,4),(41,0,194,0,4),(65,0,170,0,4),(66,0,169,0,4),(72,0,163,0,4),(96,0,139,0,4),(137,0,98,0,4),(138,0,97,0,4),(162,0,73,0,4),(192,0,43,0,4)]
def g235A : List (List Nat) := [[],[113,83],[16,115],[16,48,80,112],[48,117],[48,81,112,16],[80,49],[80,113,48,49],[112,16,49,83],[112,81]]
def g235D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x30d095539259571d09,0x10c7060f915c87250110])
def g235D5 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x408428bf,0x2ac16e6b222145c9560b,0x7359110a6ac8905b9ac8,0x8841fe5582dcd644430b,0xf0bb9ae4b222185c85dc,0xd725911086f4c0e6b92c,0x888617e14735c9644431,0xb0e7c02e4b22210ef985,0xc8725911086ecbf06b24,0xc48842fe61741d162443,0xdeebc12cab12210df93,0x61d6494910936c970ab2,0x4a488593e4d64d4a5244,0x28ef2ab22e32922149f9,0x3619741491086fc9b0eb,0x20a48843765f83590524,0x4313ae9c1ac8292218ad,0x74e09641491086fcc2c8,0xb98a48851ee55645c052,0x4429b726b22e0292214e,0xb92591701491086fc9b0,0xeb2e848861b5d7825974,0x244255b29c12cba12210,0xdf9361d63d0910a73c92,0xcab8e848853ae49655c3,0x424430bf0bc1aeca1221,0x85f8520d7650910c5bc2,0x702bb2848862ee13805d,0x9424431b107c02eca122,0x10df9361b7550910a3ac,0x8eebb2a848861bdd582d,0x95424420ff2ac3ec6a12,0x210fb985d87050910c3c,0xbb30a382848847ce6171,0x1c1424432e30ab88e0a1,0x2219d1835c4705091085,0xfca30eb2a648841fe558,0x7591324421bb2fc1ac9a,0x82211f197e055494110f,0xa0a9a6490aa08856c652,0x81dd540442bc32540eea,0xa02218e886e097550110,0xcf041702baa80885aa64,0x88459540443536c6c168,0x6a02219c9835c8725011,0xaf1c8ae439280885a66,0x4c845894044353707a1a,0xc4a02216a992d0d62501,0x10b64c98e4b1280885aa,0xe4965d094044353306b1,0xe84a02216a992d954250,0x110d4dc1ec6a1280885a,0xa64b6350940442e532a3,0x9284a0221789931c9425,0x110bd0c88e4a1280885,0xe264e6250940442d5726,0xb1284a0221aab8358942,0x50110b54cb4a4a128088,0x5e864652509404435530,0x8b1464a0221aa98650a3,0x250110dd0a1303192808,0x86a6619434c940443553,0xca1264a0221e8b63509,0x3250110af0492ebb8a80,0x886e8609421c54044374,0x304a1482a0221ea16250,0xa4150110ce9c1ee6a0a8,0x88764dcd4350540443d,0x22c6a1a82a0221ba3825,0x94150110f50b1284a0a,0x80886e260d42c8540442,0x3e331bac42a02211f398,0x5d62150110cd943a8510,0xa8088674e0f734854044,0x2f4325a1a42a02217619,0x51c92150110be0c98e49,0xa80885e865242485404,0x42f4726a1242a0221ba3,0x835092150110bd0ca464,0x90a80885e86513248540,0x443f028699242a02218a,0xf84dc96250110c6dc3f0,0x6b2460884f4e4d819523,0x4427a726c0e8518221d,0x3175551418c110ce8ba7,0x6a0c60884f4e4d84486,0x30443b42e8a124318221,0xc9975591434c110f49c8,0xac8a1a60885e464e5450,0x530443a62eaaa2829822,0x1d917550d414c110f48b,0x228690a60887705d5324,0x85304437870899242982,0x21bc1844c9214c110ee0,0xba26490a60887b059132,0x485304421f32fc328790,0x2215e39760542c8110cf,0x1c3b02a164088674e0d7,0x350720443b22e6a1a839,0x221bc3834c941c8110f,0xc0a1a64a0e4088768509,0x71503204421bf26c3ac8,0x90221ca9765094048110]) else (word80 [0x1c3040030103010,0xae081220641850,0,0,0x4040000a00100081,0x81010100040400000000,0x8004000800480040,0x90410002001000,0x81965089011005,0x94108901080b040002e0,0x2020000004001000b516,0x8ace596b2162ac257eaf,0x15cab6566ac156aaa54e,0xa9150a9e536a614aa925,0x1ea3144a86506a013ea7,0xa4ee9d138a6e4d69a132,0xa624be9712ca564a6941,0x26a4a48e91120a3e4768,0xe11aa3245e8b114a2644,0x68810ea1a42e85108a0e,0x41682102a023fe7f0fc9,0xf63e67c0f69ea3ce790f,0x9de3b6760ea9d239e73,0xe49c6386700de9ba36e,0x6d0d89ae3566a0d299d3,0x34648c5187308604bf16,0x22be570ac9562a6540a6,0x94a28e510a093e2764e0,0x9a93225e4b0949262464,0x808e91a22e4508890e21,0x640c800fd1f43c8778ec,0x1c83706c8d119c32c640,0xc51842fc5e0b91622b85,0x58a31362604a89211e23,0x420810fc1d8398700da,0x1a83386409a128210350,0x5a0a81381a02e0500880,0xe00c00c0020ff2ac16e6,0xb0e818cd73e056218940,0x967c9b03b1484a04cee5,0x581dc14250374324c08e,0xa12813a992604705094,0x8bdcab03b8284a051e6,0x54805cb615028df2ac32,0xe530a814cf9361972985,0x40cd4c2300b94c2a0437,0x66265dcd6150299f24b2,0xee6b0a814cf925947358,0x54086fcc6e6312c2a061,0x7a1773189615030bb0bb,0x98c4b0a815a9905c9421,0x8540c6bc3f06b08c2a04,0x37e4d87d8a415031d72c,0xc06e4aa4411e990e0975,0xd0e20a37c92eab2e8710,0x43de4585dd9438821bf2,0x6c3ca8b0c411e990e097,0x5d0620a37c92eab2e831,0x437e4d86dd5418834d2,0xcbc12a8a04418f371602,0x715912087bcc2e238ac8,0x9041fe5586dcd414820f,0xf2ac3ac918a416a991d8,0xd4250120dc5c1a86a128,0x9057264c725c5404837,0x1706a12e2a0241aa9865,0xa4150120d54c328518a,0x809051be497559743082,0x95f24baac9a18414cf92,0x5d563d0c2087bc8b0bbb,0x2861051de45875954308,0x30f2cac06e6aa4214779,0x161d6550e10a3cc86eab,0x2a870861e59580dc5428,0x421bf26c36eaa0c2145f,0x9361d6550610a37c930e,0xb2a830868d6118159541,0x8428f720baacaa0c2187,0x9656037250610b1bcb2a,0x8a8a830858d659545454,0x1842c7728c0acaa04216,0x6b925d56550210f0cc9a,0xcaa1a8108696597835c5]))
def g235H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5c0e
def g235D6 (j : Nat) : Nat := if 11 ≤ j then 0 else (if j<5 then (if j<2 then (if j<1 then (word80 [0x17550630,0x4437c5d1418c110fb254,0x50630443ec551418c110,0xfd38350630442fce0941,0x8c110bf38448630442fc,0x611218c110df17448630,0x443bc591218c110fe142,0x486304427ee11754c110,0xdf3815d5304427ee1574,0x4c110ddb835d1304437c,0xe05744c110cf97559130,0x443b6e0d644c110ef381,0x591304427e61e544c110,0xaf98695130442f660e54,0x4c110bf181951304427e,0x61d544c110d797555130,0x442fce05544c110dd975,0x50d30443b6591434c110,0xbdb8250d30443f460543,0x4c1109f987d0930442be,0x61b424c110bd983d0930,0x442fc607424c1109fb87,0x50930443765d5324c110,0xdd9744c930443b659132,0x4c110df175505304437c,0x5d1414c110fb25450530,0x443ec551414c110fd143,0x50530442fce09414c110,0xfd132505304437c5d521,0x4c110bf38448530442fc,0x611214c110df17448530,0x443bc591214c110fd143,0x48530443f8549214c110,0xfe142485304427ee0d74,0xc8110df1815d3204427e,0x61e64c8110be98299320,0x4427ee1d64c8110bdb83,0x59320442fae0964c8110,0x9f987d0f20442fa60b43,0xc8110bf181d0f204427e,0x61d43c8110afb8650f20,0x443765cd43c8110deb87,0x50b20442fae0d42c8110,0xde97350b20443f860542,0xc8110be9844cb204437a,0x5d132c8110fc9434cb20,0x4437c5d141c8110bf383,0x507204437c5cd41c8110,0xfb34350720443ec50d41,0xc8110fe14250720443f8,0x4c941c8110bf1844c720,0x4437c5d131c8110fd143,0x4c720443f850931c8110,0x8ff8759320442b7e0d64,0xc8110aef82593204433d,0x59171c8110de5425c720,0x4427de1d41c81109f587,0x507204436e5d340c8110,0xbe982d0320443ea50b40,0xc8110bf181d03204436e,0x5d140c8110fa94250320,0x442fce0540c8110df171,0x503204423fe117648110,0x9f7815d1204427ee0174,0x481108fd8759120442b7,0xe0d6448110aef8259120,0x4433d5d94148110cf976,0x50120443ea5094048110,0xdf1815d0204437c5d141,0x81108df835c7625023b,0xe1d6218940ccd7358862,0x502ce6147050940b9983,0x1c142502ec6047050940,0x8f787584615031b59772,0x552209e980dc95488237,0xe0d7650620e996350d40,0x882ea60b4350120bc983,0x1c940482ea6124250120,0xbab8350940483aad8d42,0x50120ea942d85404831e,0x5977050c20cb964dc143,0x833658f7050c20c7965,0x5c2548431e59570d0e10,0xc79655c3428431e59570,0xd0610e3965d0d408438e,0x5954350210e996350d40,0x8438e5974250210e3965,0x50940843aa5894250210,0xe996450d30842a761363,0xd0d10cdb635c34344237,0xe0d76d09108df835d942,0x4439cd476550110e9b63,0xd0d40443a658d4350110,0xea962509404427ca1e21,0x50110fa1424854044237,0xe0d7650110bd38350630,0x443a6591434c110f9143,0x50530443f04c9214c110,0xdb1815d0204427ce1d41,0x8110d7175504204436c,0x5d14108110dd17350420,0x443785d12108110da174,0x48420443705cd2108110]) else (word80 [0x350d4044,0x2fc6067250110bf3815c,0x940442dea147250110b7,0x9851c940442f660c7250,0x110de9721c940442fc60,0x47250110af985d894044,0x33edd76250110cf975d8,0x940442ee6126250110bd,0x98398940442bee156250,0x110cfb7558940443aee1,0x16250110eb8845894044,0x2bee0d6250110ebb4358,0x940443ae50d6250110ee,0xb7258940443ba1c96250,0x110bbb84589404427ea1,0xf52501109f987d494044,0x2be61b5250110af98694,0x940442ee6125250110f6,0xb5294940442fc6065250,0x110af986549404427ea1,0xc52501109f9871494044,0x2be6185250110bb98414,0x940442f660c5250110bf,0x181149404436edd74250,0x110db975d0940443aed9,0x74250110eb965d094044,0x2ee60f4250110ebb63d0,0x940443ae58f4250110eb,0xb62d0940443ae58b4250,0x110af98690940442ee61,0x24250110ee9629094044,0x2fc6064250110dbb7550,0x9404436e5d54250110eb,0xb6550940443ae5954250,0x110bbb8350940443aed8,0xd4250110eb9635094044,0x3eadc94250110fa87250,0x940443aed894250110fa,0xa6250940443ea5894250,0x110faa5250940443ea54,0x94250110fb2815094044,0x3ec6054250110ee96250,0x940442be61a3250110bb,0x9848c940443ba58a3250,0x110fa9428c940442fc60,0x63250110af9864c94044,0x2ee6113250110edb634c,0x940443e650d3250110fa,0x9424c9404437c5d77150,0x110bf183dc5404437c5c,0xf7150110fb143dc54044,0x2fc60b7150110df272dc,0x540443ec50b7150110bd,0xb835c540442fc6087150,0x110fb1421c5404437cdd,0x64150110df1759054044,0x3bc5964150110bf18290,0x540443bc58a4150110fb,0x142905404437cdcd4150,0x110ef36350540443bc58,0xd4150110fb1435054044,0x2fce094150110ef36250,0x540443bc5894150110fb,0x142505404427ea1f2150,0x1109f987c8540442ee61,0x32150110bd983c854044,0x3ea50b2150110df37588,0x5404437c5d62150110ef,0x16588540442fc6122150,0x110bf18288540443ecd0,0xa2150110fb1428854044,0x37cdd52150110df17548,0x540443bcd952150110bf,0x38448540442fc6112150,0x110bf383485404437cdc,0xd2150110fb3434854044,0x3ec50d2150110fe37248,0x540443f81c92150110fb,0x34248540443f89092150,0x110fe14248540443f88c,0x92150110fe1324854044,0x3ea5092150110cdf835d,0x9404423fe0976501109e,0xf825d5404427de057550,0x110abf8459540442b7e0,0xd6450110abf845894044,0x33bdc96250110ead6250,0x9404427d60b7150110de,0x77248540443e95092150,0x110d7b75d4140442ee61,0x35050110bd983d414044,0x2fc6075050110cf97654,0x1404437cdc550501109f,0xb855d2304433ee1d648c,0x110cf97559230443b6e0,0xd648c1109f9879523044,0x2be61a548c110bf18195,0x2304427e61d548c110d7,0x97555230442fce05548c,0x1109f987d0a30442be61,0xb428c110db974d0a3044,0x2fc607428c1109fb8750,0xa304436e5d1428c110df])) else (if j<3 then (word80 [0xd9424423,0xf61b75509109f581dd54,0x24423fe1975509109fb8,0x5d5424423f61f655091,0xc7f75d9542442bb60b6,0x5509108ff8759542442b,0xb60b6450910adf835914,0x2442bbe096450910bb98,0x951424423f61b735091,0x9f581dcd424423f61f6,0x350910cdf73d8d42442b,0xb60b6350910abd84d894,0x2442f360e6250910aed8,0x694942442f9606525091,0xf2d54549424427e6037,0x150910cfa86dc1424427,0xe6177050910cfb64dc14,0x24433e59370509109f98,0x3dc1424433ed8b705091,0xdf281dc1424437c6077,0x509109f581dc1424433,0xe9db7050910cf976dc14,0x24437c9c77050910df17,0x1dc1424433e5d8705091,0xb79851c142442f660c7,0x50910df1711c1424423,0xfe11768c9109fb805d23,0x24423fe1d648c9108fd8,0x759232442b7e0d648c91,0xced7650a32442fae014,0x28c910cf5645c6324437,0x9509718c9108ff855d93,0x24423fe11764c910cfb8,0x5d9324423fe1d654c91,0x8fd8759532442bbe096,0x54c9108ff87591324423,0xf61d644c910adf835913,0x24427e617704c910cf96,0x5dc1324427e613704c91,0x8ff87593504429fe156,0x4d4110cbd7459350442b,0x7e0d64d4110cdd645cf5,0x4435755173d4110cf56,0x45c7504435d55171d411,0xdf1815d2504433ee1d6,0x494110edb8359250442b,0xee096494110af9869525,0x4436e5d25494110bf18,0x1952504436e5d1549411,0xbf38155250442bee116,0x294110cf97458a504427,0xe61f4294110af986d0a5,0x4436e5d34294110bf18,0x1d0a504427ee1d429411,0xaf98650a504436e5d14,0x294110af982d9150442d,0xe6166454110b7b855915,0x442f6e0d6454110af98,0x4d8950442dee15625411,0x9f987d0950442be61b4,0x254110b7985d0950442f,0xc60742541109fb875095,0x442fc6122154110ef36,0x448550443f84c9215411,0xabf8459740442afe116,0x2d0110ced7258b404433,0xd59571d01109f7825c74,0x4433d58971d01109f58,0x748740443795c921d011,0xdf171543404433ee1d6,0x590110d797555240442f,0xce055490110cfb8758a4,0x442fce1121901109f98,0x3dd5404437ca07755011,0xdf181dd540442fc6077,0x550110d7b759d540442f,0x660e7550110bf1819d54,0x4433e21975501109fb8,0x35d5404437ae09755011,0xde8825d5404437ce057,0x550110df0815d5404435,0xedd57550110beb825d54,0x442fa2097550110bf38,0x15d5404427ea1c755011,0xaf982d9540442ee6126,0x550110bd98399540443a,0xee116550110eb8845954,0x442bee096550110bbb8,0x459540442be61b545011,0xd7b75d51404435edd55,0x450110bf381551404427,0xe6177350110bf3815cd4,0x442be6176350110edb7,0x3d8d40442be60b635011,0x9fa87d4d404427e61f5,0x350110af986d4d404435,0xe5d753501109fa8754d4,0x4435e5d55350110ddb7,0x354d40443b6d8d535011,0xbf38154d40442ee60b4,0x350110f9b7350d40442e,0xee094350110fb18150d4,0x44376dcd4350110ed96]) else (if j<4 then (word80 [0x408439e5,0x954150210ef161505408,0x433ee19744c2109fb855,0xd1308427e61e544c210a,0xf98695130842f660e544,0xc210ed96450d308423fe,0x1572d9110cdf82dcd644,0x4337a0b7359110cdd82d,0xcd644433720b7359110c,0xdf80dcd6444337603735,0x91108fd82dcd64443b6e,0x37359110afb805cd644,0x423f61772591108fd83d,0xc96444337dcf7259110c,0xdc73dc964442b760e725,0x9110cdf739c9644433bd,0xca7259110af5819c9644,0x42be6027259110a7f855,0xc9644429f2157259110a,0xdf835c96444337dcd725,0x9110cdc735c964442bde,0x57259110afb805c9644,0x4337dcc7259110ced721,0xc964442be6177059110a,0xf983dc164443b6dcf705,0x9110ed873dc164443bcd,0xc77059110cdf73dc1644,0x4376e037359110ddb73d,0xc1644437cdc77059110c,0xdf835d3634423fe0974d,0x8d108ff855cb634423fe,0x1172d8d10cdf835db434,0x423fe0976d0d10e9f835,0x934344337d8d72d0d109,0xfb805cb434427ee1570d,0xd108fd82dd94344337e,0xd7650d108ff825d9434,0x433ee017650d10e9f835,0x9143443aee016450d10a,0xdf83591434423f61b725,0xd109f581dc9434427e6,0x37250d10df1715c1434,0x423fe1175d89108ff855,0xd3624432f5d16498910a,0xdf8359262442bbe09649,0x8910cdd645ce624423f6,0xf7458910cbf749d1624,0x42bd6067458910adf835,0xd162442bde057458910c,0xbd741d162442b760c745,0x89108fd85dcd624423f6,0x137358910aef82595624,0x432fdd26458910aed829,0x91624432fdd16458910a,0xdf8359162442bbe09645,0x89108ff845da524427ee,0x174949108fd87d92524,0x423fe1d64949108fd875,0x92524429fe156494910a,0xdf83592524439bd93529,0x4910e6d64d4a524433dd,0x917194910cf5645c6524,0x423f61f64549108ff875,0x9152442b7e0d64549108,0xfd87d8d524423fe11761,0x4910cbe865d0524432f6,0x197414910db9805d0524,0x423f61f6414910cbd74d,0x90524423fe1d64149108,0xfd87590524432f5d1641,0x4910adf8359052442bbe,0x96414910cdf645cc524,0x43375917314910cfb645,0xc0524433e59170149108,0xff855db424423fe0d76d,0x910cdf835db42443372,0xd76d09109df835db424,0x427de0575d09108fd87d,0x97424423fe1d65d09108,0xfd87597424431f5d565d,0x910aef82597424423f6,0x1f63d09108fd8758f424,0x43375cd63d0910abd84d,0x8b424433dd9571d0910c,0xf5655c7424427de0d71d,0x910cf7635c7424433d5,0x8d71d0910cf7625c7424,0x427ee1570d0910cfb655,0xc3424433e59570d09109,0xfb835c3424433ed8d70d,0x910cf9635c3424433ed,0x8970d0910aed82d92424,0x42b7e0d6490910aef825,0x92424433dd917190910c,0xf5645c6424423f617765,0x9108fd83dd9424423f6,0x37650910cbf845d9424,0x423fe0d7650910cdf835,0xd9424433720d76509108,0xff815d9424433de05765,0x910cfb805d9424425fe,0x1576509109df835d9424,0x429fe157650910adf835]) else (word80 [0x483ea508,0x7150120eeb72d8540483,0xba50b6150120bb984985,0x40483ea50a6150120bbb,0x8458540483ea50961501,0x20af98694540482be61a,0x4150120fa94290540483,0xea5094150120af9868c5,0x40483ea50a3150120f99,0x434c540483ea50931501,0x20fab8050940483ea601,0x4250120abd85dcd64082,0xafe157359020ebb805cd,0x640823f6177359020adf,0x845d563082b76167458c,0x20adf855d163083375d5,0x7458c20edb805d163082,0x7be0975d0c20c7d87597,0x430823f61d65d0c20c7d,0x75597430832f5d564d0c,0x20cdd7558f430823f617,0x7650c208ff855d943082,0x3f61b7550c20c7e87595,0x430831f61d6550c20e5d,0x83595430831fdd56550c,0x20cbf755914308337dd5,0x6350c20cf986dc143083,0x3e5977050c20cf964dc1,0x430833e5db7050c20e79,0x65dc143083ae5937050c,0x20ed963dc143082bd617,0x4358420af78550d61082,0x9f60e7459610a7d819d1,0x658429fe0d7459610a7f,0x815d1658429fe1173596,0x10c7d745cd658429fe11,0x7159610c7d745c565842,0x3f60f75592108fd85dcd,0x64842b7e0d7159210c7d,0x655ce548431f59571952,0x108fd83dd9548423fe0d,0x76552108fd86dcd54843,0x1f59773552109f980dcd,0x548431f59771552109f9,0x80dc5548423f61e5458e,0x10add8395163842be602,0x5458e10c7d8759743842,0x3f61d65d0e10c7d75597,0x438433e59570d0e108fd,0x85dd9438423fe157650e,0x108fd86dd5438427e603,0x7550e10c7e8759543843,0x1f61d6550e10e5d83595,0x438431fdd56550e10c7d,0x655c7428432f59171d0a,0x10c7d65dc5428432f593,0x7150a10ced62dc542842,0x7e6037150a10cf986dc1,0x428433e5937050a10cf9,0x76dc142843ae5937050a,0x10ee962dc1428423f61f,0x4258610af581d0961842,0xbe6034258610a7f86551,0x518429f6195454610c7d,0x87597418438f61165d06,0x10c7d7559741842af619,0x54d0610e3d6555341843,0x1f59572d0610cbd645cb,0x418427ee0172d0610ced,0x7258b418433e59570d06,0x10cf9625c3418423f61b,0x75506109fb805d541843,0x1fa1d6550610c7d87595,0x418438fa116550610e3d,0x84595418439d60565506,0x10c7f75595418431f5d5,0x6550610abf8559141842,0xaf61a5450610e3d65951,0x41842afe195450610abd,0x86551418438f59554506,0x108fd86dc9418431f597,0x7250610cbd64dc941842,0x7e6037250610e7565545,0x41843ad5915150610f35,0x54545418427e61770506,0x10df151dc141842be617,0x7650210af983dd940842,0xbe60b76502109f983dd5,0x40842bee197550210beb,0x825d5408439e61165502,0x10e7983595408439e605,0x6550210e797559540843,0x9e59554502109f985dcd,0x40842bee197350210e79,0x655cd40843ae59743502,0x10ebb7650d40843ae595,0x4350210e796550d40843,0xb658d4350210afb865c9,0x408439e5957250210eb9,0x61d0940843aedd942502,0x10e796550940843ba589,0x4250210e79655c540842,0xf6e0d7150210e7965545])))) else (if j<8 then (if j<6 then (word80 [0x36e50b70,0x505408fd83dd5648823f,0x6077559220aef825d564,0x8823f61773592208fd85,0xdc564882b7e0d7159220,0x8fd83dd9548823f60776,0x552208ff835d9548833b,0xe0976552208ff815d954,0x8823f61b7355220c7d65,0xdcd548827e6037355220,0xced86dc9548833b59372,0x552209ed81dc9548837a,0x6037255220ced76dc954,0x8839b5977255220be980,0xdc9548823f61b7155220,0x9f980dc5548837adc970,0x552208fd8795163882b7,0x60e5458e20af98095163,0x882bbe095458e209ef82,0x5d7438823f61d65d0e20,0xc7d75597438833e59570,0xd0e208fd85dd9438823f,0xe157650e208fd86dd543,0x8823f61b7150a208fd87,0x95161882bd6065458620,0xaf98095161882bde0554,0x58620af581d0961882be,0x6034258620afb8050961,0x8827be0975d06208fd87,0x597418831f5d565d0620,0xe3d65553418823f61d62,0xd0620cf9655c3418833e,0x58970d06208fd85dd941,0x8823fe157650620cdf83,0x5d941882b7e0d7650620,0x8fd86dd5418831fdd565,0x50620e3d65551418827e,0x6037250620eb65458541,0x883ad5516150620cf772,0x58541882be6177650220,0xaf983dd940882be60776,0x50220afb865d540882fa,0xe097550220e796555140,0x882fae095450220afb86,0x5cd40883ae5974350220,0xebb7650d40883ae59543,0x50220ed96350d40883ba,0x5894250220afb865c540,0x8833edd97150220bdb83,0x5c5408833edd56150220,0xebb4258540883ae50961,0x50220ef161505408823f,0x61773591208fd81dcd64,0x482bbe097359120afb80,0x5cd644823f60f7159120,0xcf7719c564482be60271,0x59120adf835c564482be,0xe017159120cf5711c564,0x482be6177059120eeb72,0xdc1644833edc77059120,0xdeb72dc1644823fe0574,0xd8d208ff845c7634823f,0xe1576d0d208ff815db43,0x4827ee1570d0d208fd85,0xdd9434823f6077650d20,0x8fd86dd5434827b60b75,0x50d20adf83591434823f,0x61b7150d209ed82dc543,0x4832f5d16498520af781,0x592614832fdd26458520,0xcbf74591614823fe0d76,0xd05208fd87d8f41482af,0x61361d05209fb855c341,0x4833ed9570d0520cfb63,0x5c3414836e50d70d0520,0xcfb615c341482bd60764,0x90520af781592414823f,0x60f76505209df835d941,0x482b7e0d7650520af581,0xd9141482bde056450520,0x8fd86dcd414823f61f63,0x50520cdf73d8d41482bd,0x6076350520abd84d8541,0x4827b60b70505208ff84,0x5da314823fe1d648c520,0x8fd8759231482b7e0d64,0x8c520cf576506314823f,0xe1d644c520beb825d540,0x482be6076550120d7b75,0x55140482fae097350120,0xaf981d8d40483e6dcd43,0x50120fa98250d404837a,0x5d77250120be983dc940,0x483ea50f7250120fa887,0x50940483eae0d4250120,0xfa98350940483eadcd42,0x50120fa97350940482fa,0xe0d4250120eeb6350940,0x483ea50d4250120fa942,0xdc540482fa60a7150120,0xfa9429c540482f6e0d71,0x50120beb825c5404837a,0x1c97150120fa9425c540]) else (if j<7 then (word80 [0x26589872,0x5e097225b0954253893f,0x24e492a249090c23f48e,0xe23a08e2234c8b222688,0x8b221487621c0861216c,0x84c20f4825207c8101fe,0x7e91f8c7c21ea87a41e,0x3077d1ddc7681d647531,0xd347471ce07321cb071d,0x1c387081be46e11b486c,0x31ad06ae1aa06a21a4c6,0x8419f867819a46631974,0x657194464b191462d187,0x861818005f117ac5e517,0x585d017045bb16b05a61,0x65c58815c056a156c54c,0x14f4525145850714044f,0x213444b0123c46e117c4,0x50110443b10684020fa8,0x3c90ee83900dbc3570cf,0xc3300c843120c0c2eb0b,0x4c2b20a4427909602370,0x87c21008041f207b01d4,0x6f01a405e816204e013,0x2048c10b03a80c002a00,0x9001e006001200300060,0x8fd83dd562d023f60,0x77558b408fd85dcd62d0,0x23f6077358b40afb805c,0xd62d023f6177158b408f,0xd83dc562d02bb60a7158,0xb40af9809c562d029fe1,0x57158b408fd83dd561d0,0x23f60b7558740af5819d,0x561d023f61773587408f,0xd82dcd61d023f6177258,0x7408fd83dc961d02b760,0xe7258740af5819c961d0,0x29fe157258740a7c855c,0x961d02b7e0d70587408f,0xf835d7625023fe0575d8,0x9408ff855cf625023fe0,0x573d89408ff855c76250,0x23fe0d71d8940cdf835c,0x7625033720d71d8940ad,0xf835c76250277e0d71d8,0x940cef625c6625033be1,0xd6218940aef815886250,0x37c60171189409f9805c,0x462502bb6076290940ce,0xf625c642502ebe096350,0x940bb985dc142502ee60,0xf7050940fab62dc14250,0x2ee6077050940bba861c,0x142502ee60470509409f,0x985dc1425027e60f7050,0x9409f981dc142502af61,0x275d8540add839d76150,0x2be60275d85408ff835d,0x7615023fe0975d85408f,0xf855cf615023fe0973d8,0x5408ff855cb615023fe0,0xd72d8540cfb805cb6150,0x33e20172d8540afb805c,0xb615023f61e42d8540af,0xb8058b615033b6197298,0x540cef655ca615036b61,0x17298540de9805ca6150,0x2bde0562985409bd87d0,0xa615036b5cb4298540db,0x970d0a615036b5c94298,0x540af582d8661503ad50,0xb6198540c7f759956150,0x2b760e6558540cdf65dc,0xd61503379977358540cd,0xd65dcd6150376e037358,0x540cdf651cd615033759,0x47358540d9f73d0d6150,0x367dcd4358540e9f6350,0xd6150337dcf6258540cd,0xf73989615033bdca6258,0x540cdf73589615023fa1,0xc6258540a7e851896150,0x29f6146258540add8318,0x96150337dcc62585409b,0xe87d096150367dcf4258,0x540d9f73509615036bdc,0x94258540ddb73dc16150,0x3761cf70585409f9805d,0x4615023fe1d6518540ae,0xf82594615027e6017218,0x5408ff87588615036b5c,0x94218540cf7875846150,0x3b5e0d6118540cf57258,0x4615023f61f65905408f,0xd87d8a415033b5cb6290,0x540af585d8641502bd60,0xb6190540eb542d864150,0x33ed957090540db9425c,0x24150337dcf6350540e9,0xf6350d415027e6177050,0x5409f983dc1415036e50,0xf70505409f982dc14150]) else (word80 [0xe619984e,0x60497fa5f897a65e3975,0x25c596da5a7966258996,0xe57d95ba568958a55c9,0x55a550950653b94b2514,0x943a50893c24ea936e4c,0x392d24a5927e499924e4,0x8d91fa46f91a645a9152,0x44e90fe43990aa424907,0xa418904a40c901a3f78f,0xc63e28f723c48eb239d8,0xe3a3888de63738d92355,0x8d1a3378cc63228c7230,0xd8bfa2e68b3a2c88ae62,0xaa8a6e28c8a1a28089ea,0x27489ba268898a25c895,0xa247890623b88b221d88,0x3a20887e61f387921d58,0x73e1c986ea1ab869618d,0x85fa16f8582151850a13,0xc84b61278486112840e0,0xf483ba0df83420c182ca,0xac829a0a0826a094821,0x607f819e058814a04380,0xf602e8035ffe7fbdfe07,0xf45fc27ea9fa47e79f8f,0x7e25f837dd1f6e7da1f5,0x97d4df447cf9f387ca5f,0x237c51f0e7bfdef07ba9,0xedb7b55ec67b01eba7aa,0xdea57a7de997a29e8479,0xb1e667981e5a7951e4e7,0x921e27783de0077c5dd9,0x76e1d9775d9d7075a9d5,0xb7555d3d74ddd317489d,0x1c7459d077405cfb73b1,0xcdd735dcd1732dcbc72b,0x5ca77261c927231c7d71,0xb9c5f7141c4170edc357,0x99c207045c026fcdbed,0x6f55bcf6f25bba6eadba,0x56e59b876e05b726d8db,0x5d6d5db516d2db3c6cb5,0xb276c61b126c31afd6bd,0xdae86b89ad36b35ac76a,0xe1aa96a8da946a15a7f6,0x9e5a73696da4c6919a37,0x68c5a19684da0d681d9f,0x867a59e3672d9c566b59,0x9e663d98065a1962654d,0x93b64b191d645d91163e,0x58f363b58e763618c962,0xe98ab6295896621d8786,0x1a5863615184560d9827,0x6061812600d7f45f957d,0x65f1d7c15ec97ac5e757,0x855dfd7795dcd7645d55,0x74f5d017315c6570a5c1,0x16f55b996d75b456c25a,0xcd69b5a31674597164d5,0x91d61458155f6579d5d8,0x57255ba5689593561157,0x55599560556955455155,0x3f54c1521546d50c5419,0x4f753c54e2534d4cd52f,0x94af5281491522d47c51,0xd94705185452513143d5,0xdd428508941c5059407,0x50053f24f8d3dd4f153b,0x64e9d3984e2537a4dd13,0x6e4d593504d0533b4cb1,0x31d4c152f64bc12e14b4,0x92ba4ad12a54a592904a,0x527b49b126649812514,0x90923c48d92304885212,0x48311fd47b91df47411c,0x146c91ac467518e45d91,0x67453d14044a1122444d,0x10443d50ef43810da435,0x10c542d90a7426108942,0xd0744195056414104a4,0x11103540bd0204044ff9,0x3fccfe43f30fab3e70f8,0xd3df8f783dc8f633d50f,0x453cb4f273c84f1b3c30,0xf063bdcee83b88ed33b1,0xebe3ae0ea93a44e8239,0xcce643954e4f3900e313,0x840e0137c8de3372cdc5,0x36d8db03684d923630d7,0xd35dcd683564d4a34ecd,0x233450d0e33fccde3360,0xcc9330ccbd3294c96321,0xcc7831a4c513108c3330,0x90c1e3060c092fe8bf42,0xf94bd62ef8baf2e80b91,0x2de4b732d90b552cf4b2,0x52c58b072be0ae92b8ca,0xd42b38abf2ac0aaa2a90,0xa952a3ca892a0ca74299,0x4a5f2964a4a2910a3528,0xbca202844a0227cc9ed2,0x79c9d827249c326d09a5]))) else (if j<9 then (word80 [0x84061010,0x205418406128401040,0xc0c0c10182000c100440,0xd0410000182000000013,0x28200041040000201941,0x11028305000800004108,0x2003c10802060402080,0xc1000110042010208003,0x4005200200820304000,0x20c1844810c44810816,0x8001040208200241400,0x26504040194111004241,0x82022602410d13010801,0x70202008200041c08200,0x204100083022204004,0x22e04040604100b0410,0x2020c041000000200,0xc301048004012,0x80020302000810400002,0x8810000080410280c2,0x810102020703040,0x60682080070429650386,0x160904430b0482218582,0x4110c200b00160020048,0x20110c08110824110808,0x16088611042812088584,0x9858221841841041841,0x4010b03240648084248,0x149022104024110c2012,0x8872408841609044309,0x5822184420104019203,0x240400b040204c902020,0x402038200c0410241008,0x2812040184020c084c20,0x105426100c1165088404,0xb84020b84020b84020b,0x84020b84020b84020b84,0x20b8402daeb6b4da976,0x9fda67693da3767ed9e3,0x672d9b3666d95f651d90,0xb63cd8b7627d863612d8,0x33606d8035fad7af5e5d,0x77f5d9d72b5c4d6fb5b8,0xd6cb5a3d67758ed5ff57,0xd5ab55bd533534d4975,0x16d41f4f8d3cb4ecd39b,0x4e0d36b4d4d33b4c8d30,0xb4bcd2db4a7d263492d2,0x3347dd1df45fd16744ad,0xef435d0bf429d08f414,0xd03b408d00b3f3cfb73d,0xecf633c0cec7399ce4f3,0x7bcd8f35dcd5f351cd2f,0x333cc93315cc1b2eecba,0x32e2cb4f2c4cad72a6ca,0x5f291ca0b273c9b725ec,0x93f249c90f234c87320d,0xc7fb1efc7831dac72f1b,0xcc69319ec663189c5eb1,0x6bc59715fc567153c537,0x147c507132c4b3126c48,0x311ac42f105c3ff0f9c3,0xcf0edc37b0d8c34b0ccc,0x2f70aec2a3099c24f08d,0xc21f081c1cb06cc17705,0x7c123042c0cf024c07b0,0xfc002ffabfd2feebfa2,0xfd9bf4efcdbf1efb8bea,0x6fa3be52f8ebdfef70bd,0x86f5bbd56f46bcdef31b,0xc8af1cbc36f07bbe2ef2,0xbbb2ee6bb5eed1bb0aeb,0x3bab6e95ba3ee89ba0ee,0x74b996e56b942e41b8ca,0xe2cb89ae17b846e02b7f,0x2df6b79ede1b74adccb7,0x1adc0b6eadb4b6bada8b,0x666d8ab5eed75b59ad57,0xb546d4bb4f2d36b4c2d2,0x1b46ed15b43ed09b40ec,0xf4b396cdfb366cd3b312,0xcb5b29aca0b26ac8bb1f,0x2c6db19ec61b14ac4cb0,0xf6c37b07ec19b04ec04a,0xffabefaf82bd1af0abb3,0xae4ab83adaeb53accab2,0x3ac52afcab92ad5ab1aa,0xb7aaa2a99a9e2a69a96a,0xa4ba916a36a89e9fda7b,0xa9dfa7429c1a6ca9a3a6,0x7698ea5b694ca4f6937a,0x4a2919a44e904a3fa8e6,0xa35e8d1a30a8b3a29289,0x5a21a86ea1a2859a14e8,0x32a06a80ba0167ff9fe6,0x7f39fb67de9f3e7c09ee,0xa7b49eba7a89e8a7939e,0x367879de27609d4674b9,0xd1673f9ce67339c6e715,0x9c3e7009bea6f49b966d,0xf9b426ca9b126be9abe6,0xa99a6a69499f2676999e,0x658992663a98d262e987]) else (if j<10 then (word80 [0x54221412,0x105412420c22081010,0xa8442402102c20242070,0x80818140021308818303,0x8280040808024040c082,0xc240388040404081c1,0x98204040e0800704080,0x24006040100030102000,0x101020008100c900080,0x800204040800101020,0x20402000800002000942,0xd4900080008000000,0x4000800100000000,0x80019010680022082,0x40010000001,0x11020000100000000,0x800104001800200000a0,0x41520200040000008000,0x4100000020088101820,0x4020c9010082000000,0x40000000000200881018,0x200051a88201020835,0x48100010002000000010,0x60208000040001a0800d,0x400000000024080a404,0x6a9020601c20202220,0x40048200481048324040,0x80800704009032404440,0x40812060800683410408,0x8241000000000000018,0x20800014108020004000,0x820504108020000b0400,0x800f0704100416083c1,0x20004007020010606,0xc0818101820c1810302,0x640400000000802060c0,0x21004100200801004261,0x28306130400080810002,0x1048240080000008000,0x2c100002020000100001,0x2000010000080010000,0x80010400006080000c3,0x4061808200000000002,0xb0c04188982100810102,0x301040501808302d0c0,0x41c9303800c00016080c,0x30284000030400000080,0xc1020200000101010,0x20010100002024104020,0x85810202000040400103,0x240404080c3000400001,0x40008003041e0800004,0x80000000c10002000,0x41000020200001000008,0x102820010100020,0x5c2c100410002080,0xc3008400000581128203,0xc02100160304c3040c0,0x81810648820002080c04,0x100c1c08200083010400,0x44106820404060800,0x50404080410682000c10,0x2010700083c1000809,0x4103020604860804304,0x982069284000000412,0x182004c1030205218400,0x40208241060c0804104,0x20814861104112c8820,0xb0042060200ac100692b,0xc500020004020810100,0x204044a000900089410,0x30341040000030200041,0xc2020610100100802204,0x100800804180e101c202,0x41000830204040020,0x20004100000440800405,0x480818400840104080a8,0x810082a2040010200080,0x9020040183021002042,0x2040c20212044412080c,0x20204040110206041000,0x3020604000040028004,0x82010408081010003,0x81040020384044401080,0x8088b021604111204200,0x44085810202049010000,0x20201040008101110200,0x8810b021404000009020,0x40018002070304005819,0x120020b4882818101020,0x20004001020810100022,0xb9204000004810024084,0x8100240d0410004002a2,0x840405440810140020,0x490102020680c0030382,0x404080c000c10001040,0x80828004011020000111,0x2120500099410102010,0x244099644000c0110200,0x2240040604440a00140,0x20611042b0500080c10,0x200040000201040,0x90008000818140038440]) else (word80 [0x1020000000004000,0x80050400082000,0x1000000000408000003,0x40000000e080c404080,0x8081002a086410a85020,0x902130424081c1000000,0x20800100,0x82003414100c00588,0x8000005001000002008,0xa104043310260020b50,0x84004e80104846100000,0xc02102c105820b068,0x8100800280084c1a0034,0x408081840408081400,0x42008000041018042a00,0x20104020b00100800d00,0x10948420000983840426,0x8000000000000040000,0x800000000704000,0x102070400002000000,0x400082000c1000608,0x100000800100000000,0x2000000810002000c10,0x608001908200021040,0x801204009020010100,0x24080040408080090,0x30400000001020202040,0x21104000000800004,0xe080070400000000,0x18200040008000040,0x20800000100000820000,0x410082000000010,0x205040000808001000,0x20000504002020033081,0x2410024085412102,0x90424080801040e0808])))))
def g235H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xd52d740fc51070,0x7b20834431c0879827e7,0x3609b0000a08ae00342,0x1020b00000505c250954,0x5c00000062b010a38d24,0x3f4409922c4868e73700,0x391040841cc009802630,0x71149fc436203dc068d0,0x4190b36079546144a412,0xf5acb40e0000000000,0x605a500e7464742c40,0x90f09df7397011104500,0x403f901fc6450000b0,0x288468d03ed0bc000072,0x13907fc462b420f40780,0x592416f425d064034e10,0x45133e7340031c09910,0x3b2514601450bbd145e0,0xfb42a0000e04aa40503,0x50296e643c0000408610,0x1cf09ee2779016904d12,0x8d90600000e015f06f81,0x9500a0231300c109150,0x560826848541ea054e0,0xc1c0a6b065303584bd50,0x1d60698074b096a02530,0x896735b0bd4067e22e00,0xb01b0000101a640162,0x9220c0000722a0000e6,0x1f4390000606c0000b1,0x52e080208f504b000000,0xc0470000c02ea73b00,0x4072000090a7302d88,0x1f80abe4060825244700,0xb14e30300000c09f10,0x9580060000f8490000c0,0x9360206513f0a260a990,0x75000000002081b0b990,0x13d1b44057d001131110,0x630000a0500000428a30,0x29000000000000304f95,0x127007189b2085000000,0x10be3704e038000004,0xbec094f168d03cd0b232,0x1604406738a053f42167,0x9c38a045a10121435e2,0x6e1609202a50aa14a023,0x28e000f06da02bb01e30,0x5bc0973037106e80ac50,0x36b0a060a390660000b4,0x5bf02fb051f40dd21a00,0xa05d5424f27d940200,0x4049a80a726d30b666,0x310a1a69f00a5321132,0x122151c07e649b506ac0,0x27d114b03af07c004eb0,0x70673a50426061841fa0,0x7a0017640850231008c0,0xade05e70b5b088341520,0xd70561024196ca0b100,0x82a80000034fa82994,0xbb10ba20b8b423205824,0x597022809c20ae000030,0x46b08db44140bfe45830,0x8c90b774480000b11a70,0xafa119f08ee04c0000d0,0x8bc4bc8019d06b3034b0,0x5f20181154a09ae11810,0x52000020c08002d08400,0xb80110b45077c03330,0xb6021a0a803695043f1,0x17b055a098c092903210,0x76102ce60a20480000c0,0x78507dc4265204943d80,0x73527050a4680fd04402,0x2d1230839200001010e,0x68129582122960e0f03,0x804067001240011231e,0x200060f136007001d00,0x540d010b030b53020b00,0x3020c00326501022238,0x3030a89010509492d15,0x19010564010d0000020c])
def g235D7 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (word80 [0x35eb2286,0x106dd6350c20bf6e0a18,0x41bdd0e610837aa1cc21,0x6f67458420deae8b084,0x1bdd0d610837aa1ac210,0x4fd76d0420d7ac9a0841,0xb798f410836eb1e82106,0xf561d04209feeca08413,0xf5d9410835eb2282106d,0xe6350420dbac6a0841bd,0x585410833f3a2cb0867d,0x7459610cfae6b2c219f5,0xc5658427fbaac9084ff7,0x3592109fee4b24213f5d,0xa548433eb2ca9085f970,0x952109feecaa4213f5d9,0x548433eb2aa9084fd76d,0xe10cfccba1c219f5974,0x38435eb2687085f970d0,0xe109feeca1c213f5d943,0x8433f32a870867d6550e,0x10d7ac8a1c21b758d438,0x427ebb6850867e65d0a1,0xcfacba1421af5934284,0x2fcb8685084ff7650a10,0x9faeca14219f99542843,0x3eb2a85086bd6450a10d,0xdac4a14217edc1428433,0xeb2aa30867e65d0610cf,0xacba0c21af59341842fc,0xb86830867e6550610cfa,0xcaa0c21af59141842fdb,0x8283086fb7650210bf6e,0xaa0421be59540842fdb9,0xa81086f96350210f7686,0xa0421ee50d408437cb12,0x81087bb4250210f7284a,0x4217e5d1308437cb226,0x1087d9434c210bf2e990,0x421fa50b208427eb96c8,0x884ff7359110dbee6b22,0x21b71cd644427fb92c88,0x84ff7059110df6e0b222,0x177dcd644427eba6c688,0x4fd72d8d109faeda1a21,0xaf593434436fb1e86885,0xf970d0d109feeca1a213,0xf5d9434435eb2286886d,0xd6350d109faebb12213f,0x5d362442eeb9cc4884ff,0x74589109fee6b12213f5,0xda52443b7a94a4885f57,0x1949109faec292216f9d,0x52442deba0a4885dd73,0x14910bf2e0292213f5db,0x42442fab8e84885f970d,0x9109faed21221ebd0a4,0x2442fab8c84884ff7650,0x9109faeca12217edc142,0x4427ebb0848857e75109,0x10afaea21221775cc424,0x42fab8884885f9701091,0x9faed192217d5c63244,0x27ebb264885fb704c910,0xbbae7a82217d5c750442,0xfcbaca0885f97494110d,0xf2c928221be58a504437,0xdb22a0886fb6254110fe,0x442a8221fc48550442fa,0xb8e80885f97590110df2,0xcb202217e5d2404437cb,0x1480887f12190110bf6e,0xaa02217e5d5404437db2,0xa80886f96550110bf6e6,0xa0221bed8d404437cb1a,0x80887bb4350110f7286a,0x221bed89404437cb128,0x887bb4250110f7284a0,0x221fcdc540443f838a80,0x887f24150110fe282a02,0x21fc88540443f890a808,0x84fd7650110beee2a022,0x17e5d630442fcba46088,0x6f9648c110fe28318221,0xfc48630442fcbaa60885,0xf9744c110df2c898221f,0x650d30443ec99260887f,0x1414c110fe242982217e,0x5d320442fcb9e40887e9,0x42c8110fd26590221fc5,0x720443f898e40885f57,0x1c81109faec902217e5d,0x20443f8a0840884ff73,0x590109fee4b20213f5db,0x430435eb2686084ff765,0xc109faeca1821af5914,0x30436eb1a86084fd76d0,0x810d7ac9a10213fdd942,0x427ebb284086bd64508,0x10ddac4a1021ea509404,0x833cb2a81084df735911,0xaf2ea102216e5d02044,0x2ecb9840887e12108110]) else (word80 [0xbfae5a0,0x221bf58b40443dea1680,0x887f521d0110ff2a1a02,0x21fe55240443fca14808,0x87fb7550110ff4eaa022,0x1fe5d540443fc3aa8088,0x7fa6550110ff2caa0221,0xfed5140443fcaa280887,0xfb7350110ff2e6a0221f,0xed4d40443fca9a80887f,0x94350110ff6e4a0221fe,0x9c940443fcb9280887f8,0x7250110ff4c4a0221fe5,0x8940443fda9280887fa5,0x250110ff2a4a0221fe14,0x940443fd21280887f942,0x50110ff464a0221fe4c9,0x40443fdb8a80887f9715,0x110ff642a0221fe4854,0x442ffbaa80885fd7550,0x110dfacaa0221bf59140,0x442ffb9280886fd62501,0x10f7e84a0221ef509404,0x43faa0a80887f5215011,0xff6a0a0221fe5414044,0x3fd2a460887f9548c110,0xff68518221fe50a30443,0xfd2a260887f9544c110f,0xf2a498221fed0930443f,0xca1260887fa64c8110ff,0x2c990221fed0f20443fc,0xa1e40885fd74c8110dfa,0xc990221fb50b20443faa,0xe40887fb40c8110ff28,0x1902217f5d1204437eb2,0x240887ed4248110fea82,0x90221fe501204437eb9a,0xc8086fd7259010dfaeca,0x1821bf591430437ebb28,0x4086fd64508109feeab1,0x6813fdcd62d027fb8ac5,0xa04ff75587409fee6b0e,0x813fdc961d027ebaec4a,0x4fd73d89409fae3b128,0x1bbd8a62502bf3a8c4a0,0x57d7518940bbce631281,0x775cc6250376b10c4a05,0xf67118940beae2312816,0xf5cf42502deba484a06e,0xf6290940bf2e121281ee,0xdc142503dc38284a05fb,0x70509409faebb0a813f5,0xcf615035fa1ec2a06bd4,0x3d85409fae5b0a817b9c,0xa61502f6b94c2a06f761,0x98540bbee6b0a81771cd,0x615037ab08c2a06f7619,0x540bf2e120a817edc14,0x150376b8ac4206f57558,0x440deae4b08813fdd564,0x8827fb9ac9104ff71592,0x209faed2a4417e5c2548,0x827fbb2a9104fd765522,0xcfacaaa4417bdc95488,0x27ebb687106bd64d0e20,0xbf2e1a1c413fdd943882,0x7ebb287106bd6450e20d,0xbac6a1c41af59342882f,0xcb8685106bd6450a20bf,0x6e0a14413f5db41882fc,0xb8683104ff76506209fa,0xeca0c41bd585418837db,0xb281105fb7550220df2c,0xaa0441be58d40883dda1,0xa81107b94350220f7684,0xa0441ee509408837cb0a,0x81104fd71d91209fee6b,0x22413fdc5644827fb82c,0x8906fb70591209fae9b1,0xa413f5c7634827ebb686,0x905ed72d0d20bf2e1a1a,0x413fdd9434827eba6c29,0x4fd76d0520bf2e1a0a4,0x13f5da41483dba0c8290,0x4ff76505209faec20a41,0x775cc41482fcb8082904,0xfd768c520bdae5a02417,0xe5d240482fdbaa80906f,0xb6550120df6c6a0241ee,0xd0d40483dca1a80907eb,0x7250120fd0e4a0241eed,0x940483f521280907e94,0x250120df6c2a02413f5d,0x940482f7b9280907ad42,0x50120d7ee6b2041af5cd,0x640835fb8ac8106bd715,0x90209fee6b20413fdc56,0x40836ebaac6106de7458,0xc20dbae8b18413f5db43,0x833f32e861067d65d0c,0x20d7ac9a1841b758f430,0x827fbb286104fd7650c2,0xcfccaa18419f5954308])) else (if j<3 then (word80 [0x837ebb28,0x2906ff6450520dfac8a0,0xa417fdcd414837fb1a82,0x907bf4350520f7a86a0a,0x41bfd8541483fb30a829,0x7f56150520bfee0a0a4,0x17f5d841482feba46290,0x6fd648c520fea8318a41,0xbf59131482feb8e80907,0xf94190120ff6eaa0241f,0xe5d540483fcaa280907f,0xb7350120ff2e6a0241fe,0x50d40483fdb9280907f9,0x7250120ff6e2a0241fe9,0xc540483fcb8a80907f87,0x150120ff4c2a0241fe58,0x540483fd28a80907f951,0x50120ff482a0241fe505,0x40483fd18a80907f9315,0x120dfac8a0241fb5094,0x482ffb8a80906fd7359,0x20dfae2b20417f5d743,0x837eb2e86106fd7650c,0x20bfeeaa1841bf595430,0x837eb2286107fb7050c2,0xdfaeca0841bf5914108,0x37ebaac9086fd7359210,0xdfae4b2421bf5c564842,0xfeb9ca9085fd7195210d,0xfaecaa421bf59154842f,0xfb9aa9085ff7155210ff,0x2e0aa421bf951638437e,0xaa2c7085fd75d0e10dfa,0xcba1c21bf5d943842ffb,0xaa87086fd6550e10dfac,0x8a1c21fe5c143842feb8,0xe85086fd7650a10dfac8,0xa14217fdc542843fdb82,0x85086ff4258610dfac8a,0x8c21df55151842febae8,0x3086fd65d0610f7aa9a0,0xc217f5cb418437eb1683,0x85ff7550610bfaeaa0c,0x21bf595418437eb22830,0x87be5450610f7aa8a0c2,0x17fdc9418437eb128308,0x7f55150610ff2eaa0421,0xfe55140843fcb9a81087,0xf94350210ff2e4a0421f,0xe50940843fcb8a81087f,0x95150210ff282a0421fe,0x95130843fcaa261085fd,0x7299110dfee6b2221bf5,0xcd644437fb92c8886fe7,0x259110dfae4b2221bf1c,0x9644437fb82c8887df73,0x59110bfee4b2221fedc1,0x64442feb9686886fd765,0xd10dfac8a1a217fdc94,0x3443fcb8286885fd7498,0x910dfac931221bfdd162,0x4437f3a2c4886fd74589,0x10df8e8b1221bfdcd624,0x437eb9ac4885ff755891,0xdfacab12217fdd16244,0x37f322c4886fd6458910,0xbfaed292217f5d252443,0x7fb24a4886fd6494910b,0xfaeca9221bfd91524437,0xeb22a4886ff6354910df,0xac6a92217f5d852442fe,0xba0a4886ff6414910dfa,0xc8292217f5db42442feb,0xae84886ff65d0910dfac,0xba12217f5cf424437fb1,0xe84886fd63d0910dfec5,0xa12217f5c742442feb86,0x84885fd7690910bfae92,0x1221bfd92424437eb248,0x4887ed6290910bfeeca1,0x221bf9d942442febb284,0x886fd7650910bfeeaa12,0x217f5d5424437fb2a848,0x86fd6550910dfec8a122,0x1bf59142443df2a28488,0x7bd5450910bfee6a1221,0xbfd8d424437eb1a84886,0xff6250910fdcc4a1221f,0xb58942443f729284887e,0xd5250910bfee2a1221fd,0x9c542443fab8a84885ff,0x7050910ff6e0a1221fe1,0xc142442febb084885fd7,0x48c910dfac919221fb50,0xa324437eb2a64886fd64,0x4c910bfae9a8221bf593,0x50443beaa6a0887fa549,0x4110ff2a928221fed0a5,0x443fca14a0887fa6454,0x110ff2c8a8221fe58950,0x443fda12a0887f942541,0x10ff264a8221fe5c5504,0x42febae80886fd65d011]) else (word80 [0x20ade157,0x2a485360a46144027e8,0x4ee09c6135026284b609,0x56128024a848208de119,0x22a8442086610902088,0x3fe07d60f601e483ba07,0x5e0e801c8838206de0d7,0x1a0833206460c301788,0x2de05960ad0152829a05,0xe09f0134825a048e08e,0x1168222041e07f00f48,0x1da038e06e00d2819203,0xe05e00b2815a029604f,0x94811a021604000788,0xe201a60300056809e01,0x1601e0032804a006e00b,0x10801600160001bf5d,0x562d037eb9ac5a06fe71,0x58b40dfae2b1681bf5c1,0x62d037f3aac3a06fd755,0x8740dfae6b0e81bf9c96,0x1d037eb92c3a06fd7058,0x740dfaebb1281bf5cf62,0x5037f38ec4a06fd71d89,0x40bfaebb12817f5cf625,0x2feb8ec4a05fd719894,0xbfeeab12817fdcd6250,0x37fb1ac4a06fd6358940,0xbfee2b1281fedc162502,0xfeb88c4a07bd63d0940f,0x7ac5a12817f5c642503d,0xe3b284a07bf6350940f7,0xac6a1281efdc142503de,0xb8284a06ff6350940bfe,0xe0a1281bf9d7615037eb,0xaec2a06fd73d8540dfa8,0x7b0a81bf9cb615037eb9,0x6c2a06fe42d8540dfa85,0xb0a817f5d761502feb9e,0xc2a06fd63d8540f7a87b,0xa817f5cb615037f316c,0x2a06fd62d8540f7a85b0,0xa817f5d6615037fb2cc2,0xa05fd7298540dfec530a,0x81bf58a61503dfa14c2a,0x7bd4298540bfeeab0a8,0x1bfd95615037f32ac2a0,0x6fd6558540bfee6b0a81,0xf7dcd61503ee39ac2a06,0xff6358540dfac6b0a81e,0xfd0d61503dea1ac2a05f,0xf7258540dfec4b0a81bf,0x989615037eb12c2a06fc,0x6258540f7e84b0a81ef5,0x961503fdb82c2a05fd7,0x518540dfaca30a817f5c,0x8615037eb10c2a07bd42,0x18540bfaeb20a81bfd96,0x41502feb9482a06ff629,0x540f7a8520a81bfd8d4,0x1503dea1a82a05ff7250,0x540dfec4a0a81ef50941,0x502ffb8282a06fd75592,0x20dfae6b2441bf5c9648,0x837eb8ac9105fd739522,0xbfae32a441bf5d95488,0x37eb22a9105ff7355220,0xfdee4aa4417fdc554883,0xfcb82a9106fe5458e20d,0xfaa8b1c417f5d7438837,0xeb2e87106fd7650e20bf,0xeeaa1c41bf595438837e,0xb2287105fd71d0a20dfa,0xc8a14417fdc5428837f2,0xa2c3106fd5458620dfe8,0x4b0c41bf50961882feba,0xe83106fd65d0620f7aa9,0xa0c417f5cb418837eb16,0x83106fd7650620bfeeaa,0xc41bf595418837eb228,0x3107be5450620f7aa8a0,0xc417fdc941883fcbaa81,0x107f95450220ff2e6a04,0x41fe50d40883fcb92811,0x7f94250220ff2e2a044,0x1fe50540882feb8cc890,0x6ff7359120dfae6b2241,0xbfdc5644837f38ac8906,0xfd7159120df8e2b2241b,0xfdc164482ffb8ac8907f,0xb7059120bfaeba1a417f,0x5c7434837ebb286905ff,0x7550d20dfac8a1a41fb5,0xc943482ffb8a86905fd7,0x498520dfac930a417fdd,0x1614837f322c2906fd64,0x58520bfaeda0a417f5cf,0x414837fb1e82907bd43d,0x520dfec3a0a417f5c34,0x1482febb482905fd7490,0x520dfec920a41bf59241,0x483fab0c82905ff76505,0x20dfceca0a417f5d9414]))) else (if j<6 then (if j<5 then (word80 [0xa12b2a55,0x64a8e94e1296a51e4a1e,0x942127ca4ea49c693412,0x62a4ba495e929124ea49,0x64916921123ca46e48c6,0x9151220a432484690612,0x8a40647e68fa11eea3c,0xa47868ee11d6a3a64736,0x8e411c0a37646ce8d711,0xa8a34246668ca118ca30,0xa45f68bd1174a2da459e,0x8b1115ca2a6452e8a211,0x3ea26e44c68961124a23,0xa445e889110aa20a43f6,0x87b10eea1ce437e86d10,0xd2a196431685f10b8a16,0xa42be85410a4a13a4256,0x8471086a0fe41de83810,0x6aa0c6417682c1050a09,0x2410e81e1038a06240a6,0x812101ea032405680810,0x8a00a3ff67fc0ff29fd,0xa3f9e7f00fda9fae3f3e,0x7e60fc69f823eee7db0f,0xae9f4a3e867cd0f909f1,0xa3e1e7c10f7e9eee3dc6,0x7b50f649ebe3d667a80f,0x4a9e8a3cfe79c0f329e5,0xa3c8e78e0f109e123c06,0x77d0ef29dda3b9676f0e,0xd69da23b2e7630ebe9d6,0xe3ab67530ea49d3e3a5e,0x7480e889d0a39f673c0e,0x729cd6399e7310e5a9ca,0x639367230e429c7638de,0x7190e2c9c46386e70a0e,0xc9c0a37fe6fc0df09bd,0x637966f00dda9ba63736,0x6e30dbc9b6a36b66d40d,0xa09b2e363e6c40d7c9ae,0xe35be6b40d629ab63556,0x6a80d4a9a8634ee69b0d,0x309a4e347668c0d0e9a0,0xe340667e0cf699e233ae,0x6720cdc99aa332e6620c,0xbc996632a66500c98991,0xe321e63f0c7498d63196,0x6300c5898a6312e6210c,0x3a986230a66110c1c982,0xa303e6040c0297fa2fde,0x5f90bec97ca2f765eb0b,0xd097962f065de0bb6975,0xe2e9e5d00b9897222e36,0x5c40b8096f62dc65b50b,0x6296ba2d5e5a90b4c968,0xa2cfe59c0b2e964a2c6e,0x5890b0895fe2bd65760a,0xde95ae2b365620abc956,0x62aae5520a9a95222a16,0x53f0a7694de298e52d0a,0x4e948a28fe51d0a2c944,0xa286e50b0a10940e2806,0x4fe09f493da27964ef09,0xd6939a270e4dd09b0935,0x626864cc0990931a260e,0x4be097492d625864ad09,0x529296250e49d0932925,0x2248648c090e920a23f6,0x47c08f091d2238646c08,0xd0918e22f645b08ae914,0x2225e449088a910621d6,0x437086690ba215642408,0x40907220c64150822903,0x6204e40608028ff61fde,0x3f807e88fc21f663ea07,0xcc8f861ee63d707a68f3,0x61e4e3c607828ef21dc6,0x3b507608eb21d3e3a307,0x3c8e661ca639007168e1,0xa1c0e37d06f08dce1b76,0x36a06ce8d8a1aee35a06,0xac8d461a66349068a8d0,0x219e6339066a8cc6196e,0x329064a8c8618e631806,0x268c3a184e30506008be,0xe17b62f305dc8ba61726,0x2e005b68b5a16962cf05,0x948b1616062bc05708ad,0x2157e2ac054e8a8e14f6,0x29a052a8a46146628905,0xa8a0613e627904e889c,0x6136e26a04ca898612ee,0x25a04ac8946126e24a04,0x8c890611ee23a046a88c,0x6117622b044e888a10f6,0x21a04308852106e20904,0xc880e0ff61fa03e687b,0xa0f5e1e703c4877a0ede,0x1d903aa87460e661c703,0x8486f60dc61b5036086a,0xe0d361a2033a865a0c86,0x18c030e860a0bf617b02,0xf085ce0b7616a02ca858]) else (word80 [0x30411100,0xc045848444a411170e04,0x46905841612110c04584,0x44840116141110480458,0x444a411170e920444584,0x1216110c104458316011,0x10e903458404a410170c,0x32884290412100888404,0x83a410170c3292884041,0x312100c884c403001312,0xc045848309c11216108,0x8484031012110c404844,0x31512101110584844316,0x12110c50485844412111,0xc444021511100c4420,0x58312081611101408403,0xa4050210104010f0b100,0xc4c4818140c086050210,0x1310184c2a4860990140,0x840411050410104c4890,0x140840613122410111a9,0x2122224101014084054,0x40502100c90402041008,0x10584030502100c505a1,0x84440805030706144414,0x10404080416111310209,0x44440816110c10209444,0x4c125241110502094444,0xc4082511131020944441,0x31205020324189688004,0xc9051201162410201058,0x444c1162411102058443,0x503140c140c222c3011,0x610205890444c1252411,0x13045890444c11624111,0x2058904440116241110,0x201040584c4081016104,0x4141040416c42b10121b,0x10605840d16100c58402,0xa522100c481440317101,0x60c30402161008584020,0x6c31716104c949040410,0x160810584030c2212101,0x10405830816100d948a,0x1841922010c1194004,0x84040d0c060410488840,0x312a4100c10402122410,0xc54904031222100c201,0x8101c406121624109010,0x8850185866506120d944,0x84036500a22410140401,0x96881890612652210104,0x99420184131205021014,0x94484031610084830884,0x41210084e8994404081,0x6100c308860404152210,0xc4c4021510086058444,0x413a265101021944440,0x48006170e0218ac5c480,0x6170e02185cac413010,0x617105c4020816100c20,0x10405841710084c5c403,0x1118120c460458484111,0x8120c906044318110848,0x604431218110c1060443,0x11411612104491045841,0x141160c4904445841211,0x41161010450458402002,0x404161118444858404a4,0x8608405c21710085c402,0x17100ade25ba6b7216dc,0xadaa5b46b6616c4ad7e5,0xae6b5916aaad4a5a7eb4,0xc1690ad1259feb3d1674,0xacde59a6b33165eacae5,0x93eb251642ac7a58d6b1,0x71628ac425866b0a160c,0xac0e5806afe15f6abe65,0x7b6af415e0abb25746ae,0x615c4ab7a56e6adb15ae,0xab525696acf1598ab265,0x636ac41580aaf655d6ab,0x8156aaaca5586aab1552,0xaa96551eaa01538aa665,0x4b6a931520aa36544ea8,0x71506a9fe53eea7914ec,0xa9ce537ea6c14d0a98e5,0x30ea5e14b2a956528ea4,0xe1496a91e521ea41147c,0xa8ee51b6a341462a8b25,0x146a251442a87650cea1,0x71428a846506ea0a140c,0xa80a4ff69fb13eea7ce4,0xf7e9ec13d4a79e4f1e9e,0x13b8a7624ea69d3139e,0xa7324e469c41384a6fe4,0xdde9b9136ca6d24d8e9a,0xf135aa6ae4d4e9a61348,0xa6864cf699d1334a65e4,0xcae9931322a63a4c5e98,0x9130ca60a4bfe97d12f4,0xa5de4b9e97212dca5ae4,0xb4696612c4a57a4ad695])) else (if j<7 then (word80 [0x8380040d,0xc501828004080d08182,0x80608301820c19060c5,0x1888341120a10402190,0xc8441101a10919442410,0x83430901840665240c6,0x41821012085440265100,0xa041821524100c880048,0x38422410c52101d04422,0x12100c88904030724080,0x610188a0594424810622,0x101a0458324228110101,0x89088314062224109204,0x188842481062b1011042,0x12100890884030806081,0x20018319228001103600,0x10313124306110848183,0x804800c1a0024206800,0xc120021208060c904020,0xc060830182410c081c18,0x22241000c24186030981,0x410e045820611088a050,0x424406220818ac281412,0xb0e04188831480060d0e,0x40830280060c1812206,0x890881831401084d0e0,0x840722060e881c1830,0x60708482421207084824,0x20340120c481c2024012,0xc0c0458504050111141,0x140c005040302001310,0x14084c40405030013104,0x80c0458412050111104c,0x4818140c0861612110c2,0x9448444081612111310,0x58403081612111051944,0x43c416100c2058484441,0x51204111050481058445,0x1612110c584844304401,0x40c5010584844512c340,0x1410640c083048512050,0x21010484021210085048,0x1c140c046c410160c342,0x31040412100b104020fc,0x41011104c40212100b08,0x484031240130e1058403,0x1684100e105840303011,0x61210144448404050210,0x12100c04485841216080,0xc0464584120301161012,0x845838c0414444840411,0x24100c40484430510151,0x1104814444041211100c,0x10444031112160c44485,0x8314121116130c505830,0x50212101008484030502,0x131010481408404c2a50,0x41010245048312160818,0x485831012110c4048443,0x15121011104448583141,0x21611103208484040116,0x110c1404443141207050,0x30118045850444141108,0x4584430410160c50489,0x14044461424110c4890,0x44305011115100458443,0x14120503012418084890,0x30417100c5c904030503,0x130c905c4031724100c5,0xc904030417100c505890,0x4441612110c581161211,0xc58484431224110c549,0x4430712080048443121,0x62411100010584441602,0x112414485844314120,0x11611145848443241611,0xd960848404126582101,0x485c4031217100c1608,0x484041217100d9032084,0x4658264101195920840,0x40542121011150a90404,0xc42a41012950848404a,0x542a4101015085440412,0x54210129115084040ca,0x44210104a9508404a504,0x42101043082828064181,0x1920a006046417100d90,0x5c403658264101195920,0x84041217100c485c4034,0x43a41712905c403a417,0x100e905c4031217100c4,0x85c403a440431712905c,0x4030417100d8d0459904,0x64634116119030444040,0xd641610100c045848405,0x11121010044458484030,0x11612128e06905840116,0x120c0c04645841203011,0x610128e0458405111210,0x104516904040c11a4101,0x44904031110120c1454,0x44404120511101290451,0x44040ca4111010484440]) else (if j<8 then (word80 [0x84c4022,0x386084010a4423401214,0x4011312100c401130622,0xc2048443210b0884442,0x440b100c4c4421106084,0xc4818325120822120030,0x122120e1010422804010,0x3430240120818201c322,0x40120d008a0031223400,0xa104011321070c208900,0x4844022800c4a0500312,0x420c0c482421412070c4,0x824183001508004c2121,0x6081609004841900080b,0x219024100106448583,0xc04090c250864302190,0xc24103031209085400,0x2150c080d00483210013,0xc51009038421000c301,0x183190c060c11081831,0x442060c086400306040c,0xd14100140818101c312,0x43060c4d1400313060c0,0xc0500483810516048431,0x30008490830319124280,0x1024115240848501c302,0x2408241821304844c212,0x11084410104041161101,0xc041120708108420704,0x641c2071308441150708,0x441151108541c2132408,0x900420806240c1084224,0x21085048215070840101,0xc3430484101c30212082,0x1820713081c90043072,0x4010c1c2018300013252,0x30c1d150c30724010c1c,0x421343070c1c8c4c381,0x50e048430721040c1c1,0x24080706104c08208060,0x84c1c20301080410a041,0xc4c21304584821916086,0x45822400120c54261108,0x41524110c00490831207,0x84818442084c1a10444,0x784081c902080624071,0x5810782081c90213041,0xe08207820850481c3248,0x81e021031209084818,0x21802190c24329031209,0x8006054315090c0d028,0xc48340044818240a1120,0xc48302120908481c2130,0x91206121454003850013,0xc304820540120c64002,0x19000864485830c04090,0xc2464219000826903031,0x20908551400315090c0c,0xd004831512090c5c004,0xc3120708090048317001,0x40c890020704060c4834,0x20d0464002810ca40c64,0x11700140c12041c34500,0x130d160400381130c0c4,0xd009034504810d160421,0x784000c1c4c2840d0848,0x301c31912800c4824280,0x15120c1c11422240c244,0xc183000d08110420c090,0x82411422084c48403100,0x44809043100b08400824,0x10b0848402a423860c48,0x88210060c50183100490,0x40215060854402142408,0x40902c30804070610101,0x1610040c201058404100,0x44440208160858108072,0x40c108821024220c201c,0x21406080818205438102,0x105c5820e06090c3820e,0x23060c40382080708201,0xc501842402100c14910c,0x400851323120c6458183,0x416060e041058315060,0x8441a9031104100c1088,0x18300130804482080708,0x50881832406020c910c1,0x80840706080c00641085,0x948c30645430c505818,0x30604501858381140818,0x824306020c5c1171609,0xc501830623140c40502,0x622040c1810807060c8,0x81171608500021408400,0x61058205031440010d04,0x8834106220c201c214,0x22060c0e0408314220a0,0x2c2810b086418224051,0xc141822581060c6604,0x941840781060c8a04183,0x2506084c944030725080,0x61088185832206160c60,0x40ad2c5c50c060864301]) else (word80 [0x191408545,0x44340140858504c3121,0x4070c4c1191308544c40,0x3101308504c21213100c,0x14884831211088848201,0x12110c64304831512110,0xc4c8c184842108085058,0x21411082c48211045088,0x8431412070c208448315,0x110850481c3060809005,0x4831204110c88242041,0x4400c48510031211084a,0x9003101208144821210,0x8484021204084828012,0x822004831925120c544,0x84030a80081048403142,0x2120e001080412004830,0xd25085810608220c8848,0x2220108488824022084c,0x849430d4008403c22521])))))
def g235H7 (j : Nat) : Nat := if 8 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (word80 [0x4908a9,0x377d8009b4cc500000e7,0x434807e1c8d372106e00,0xbaa05cecde660104c470,0,0x10fc000000000104d40,0x323780000000,0,0xc0b5202b70000140f9,0x400007814500001010ab,0x8cbd8000000001f07dac,0x212000000000008c3a00,0xc9e82e100001006e4903,0xf83e62635f811470042,0x340ec00000648c5c0919,0x1ebb02e1600d6086ab1,0x3a64201600000d0262a0,0xcca400f4093e40068000,0xb24d00000080e980000,0xc0222000000000781910,0xc8109182eb198d60,0x3ffa0ee8e1ce3a06d400,0x68000000000120060000,0x6b9ba50100,0x22049c21d80,0x1e0,0x7b10102e8231c419e000,0x80e4902cb000018e40,0x8000000000427b1a46f8,0xcd4781db00000602e20,0x7680000b00b5e0f8800,0xe01d600002d05,0xfc89820000000f6c0000,0x1015800000e0adb08ae5,0x3ec1864c6073c000068,0x343001e2000008134612,0x837009e0000000000000,0x31829303f6,0xb01f600a2d0047000000,0x3007a0000059,0x78e00001599d600db004,0xca000000000409500000,0x3818180000607e8,0x2807f713d9206a60,0x80c6c4206901e000,0x1020c800008211b440,0xf240e3902ce407d5802f,0x40177c824ba080800001,0x41e6130512110aee3fb8,0x8fb00000573ae0000394,0xa6f2073e86af0066c000,0x7813b0100fc858,0x3a2000000806f20126d,0xb92660255c03db1186f0,0x37d4019a0000140e3480,0xac00001e874109b18000,0x2011de03be,0xa0400e0d1c0000481080,0x60b060069601a6d0,0x26be0ba0819a00000000,0x6a1e640f0cc2d23257,0x5c081340c2a2045b41ff,0x60ac80000088a6401656,0x8df559927a3400000080,0x77000003843ef4230c02,0x1c00000039e00000a034,0x580d9c000e000004e89a,0xc01f0000001220800214,0xa04a10808b4730415d40,0x31012cf0241010c1041,0x8b4c01000007860c001,0x71091812421810450c91,0xc00500e3ce048182042,0x68b0c00870812c00c,0x20431119830040820812,0x8538611f100604085003,0x2092800180c70095c108,0x30062c20042c10001412,0x13410012ca981102086,0x30816c2042001c0100,0x204a20b3cb0c02000032,0x31c10c200b040081185,0x5c60003cf0002411c014,0x702408e2001010050820,0x404110b10018520030b,0x8200968b0800c72432c,0x20010400c21c30800031,0x424d00014028e14105d,0x28530100724004014710,0x300205200315b0022840,0x450c000510504618d106,0x1041c008518014a14900,0x70170400020010030860,0xc32c70862c414b042000,0x24c0030001c704330004,0x40c60000432401a02800,0x11c0004000042005400,0x410020410800001c314,0x224800000e00200c0040,0x108200200048024a407,0xb04d08700404608200,0x430892081430415400,0x400010c3004048000180]) else (word80 [0x1ba00000,0x602715d1680000000000,0xc026e3901e3187c2,0xfb000002834611166c08,0x94000000000000000000,0x3995c1465a00000,0x520d900000000000,0x1c684044,0x7d139110000182222817,0xa00000a08992010c0000,0x181f9000000000000007,0x8810340cd21030000010,0x2856061200002411a211,0x2ea0019600b780e6192d,0x2f06d800000000000000,0x14424c0000000000,0x2e40e001f8000028,0x1b600000000000000500,0xf600003d44480000500d,0x762260000000000201d8,0xc81d0000000000c,0x55000000a06300000e0,0xb6000000000000000a43,0x7a092b80000d015f0648,0x400000000004301a0a98,0xc0314c03380,0x2080a0000000001c1,0xd69809a150f400000000,0x380f3803af60bf00000,0x582b87406cc037308299,0x21953079600002861558,0x32e92322000000000401,0xb5022286467800002016,0x5b06a0f031c000000000,0x30b1800004040e0,0xa0aec80be00000e0,0x428000000000108a5000,0x2848a309758357,0x4010bfc1784a89700001,0xe0d60814d00000000000,0x480b90000000,0x301088905900000000,0x3407300001400f,0x548f3a8b48a058ec0ba4,0x83c800000000000,0x780456035a0000000,0x182fafc17,0x600000607064061c0000,0x9215a00003d0020,0xd04d800000082bc8,0x3eef01c460bc40000582,0x7b402700000000000000,0x604f8480c248a900000,0,0x409b8000040,0x67800000821880000230,0xec006a480a051049600a,0x60000004bb1820200000,0x40f91c06f80000000016,0x5180000680bb1418e00,0x24188e2041600c2e25,0x81420400000c027af21d,0x8000000000c05c1e0d10,0x404300000f0788e02f0a,0x6c403487008f2103405,0xa15021020816262d7c10,0x1891860000000dc0c121,0x402bde05b101cb0,0x5413380678000058,0x3630000108d330157000,0x3003c5894,0xc0000000000408bb8389,0x18009c0000000000,0x5805400,0x80453c21468246f08,0x8d0032ea14000060931b,0x9a0de541cfb8409a06f8,0x60077014ff80a9100c80,0x10cad8000000001a8,0x720000002bb900000000,0x1c459,0x80928112fa52a2a0056,0x80243841400001c06a98,0x17959088007af20a3841,0xcb9288854337c0330013,0x33203f000000000380dd,0xf13da000000000000000,0x180dc941eae0,0x39dc059ba817d01e9228,0x94406760000000000000,0x1e08840000182a0,0x622bda88ec485a800000,0xbbb40f50000024,0x19a00000000000000173,0xce000004446000000000,0x200a99044200000,0,0x1421e800000000140,0x6bc0000000000000120a,0xf000001900a30481205a,0xc00005bb3fe737a20324,0x78127a5014480dc0,0x782a5b869f20fac00])) else (if j<3 then (word80 [0x80e520f6,0x3a00800001408ac,0x7888100000000000,0x33d0000102247c1,0x6e0000000001e10288cb,0x50a94b41329e0395490f,0x35ea054480f8d0457f,0x8094840e9205b70162c9,0x893000016c47001bf723,0x2ac03fbee6ba02110000,0x68429,0xd116a00001c1b5000000,0x1426240cb35041170,0x14c0000001ad002a7123,0x66e038d893682bfd0000,0x3c03fe814400000,0x62e20086e81fa633188,0x81d419f68122b011aa4,0x4f641a66015cc121ec22,0x8000000000000000000,0x220ca3031000000,0x7a0de40040000018,0x400000913420055f51,0xad00000a087600001421,0x37ab46c063e000009070,0x984170000000003c216b,0x195c07b921048003b28,0x1e0901cc0000240c634b,0xc8205304439800000000,0x9218200003c096301cb,0xc0769c084c00007020da,0x59fa056904a95204600,0x32333501,0x696c3f5c01169267c23f,0x980c22021b72421022b0,0x6a9370c7780000606ea8,0xff9107019912095de0e,0x77800001808350896000,0x50181f40aa0000,0x290511036800001,0x8189e996e3101920d808,0x8d500000505e66adbd01,0x218000000001ce852c07,0xe80000423be000000000,0x743a980264421c8,0x69,0xdc0000000002800d800,0x3c5a58000,0xf03516a21e444f80000,0xe0ea40000000000,0xb4b1254d0,0x448a25cd00ed00000144,0x868099d4057000000000,0x100f7400000000000000,0x2818780000000010,0x4a788a3ac0da403ee20,0xd89486fd03009746d886,0x72848fb92646132ae430,0x415a3035f0000028df0,0x69352e4174000019,0xda05a0ebc05bdc678f40,0xaf988a100001045e8000,0x6a11a4259de22c60449,0xd82373738280f9c018b8,0x91e11439660f78000008,0x307301b560f6420bc520,0x57207820000000002a94,0xf0000000000000000000,0x30026000000000682fea,0x80080fe8000000000d1,0x1d080100000000000144,0x1000000d1af800000000,0x46080000480d600001,0x324bd880830325103a40,0x34ca900000f24d800,0x282d1805d7283,0x38000028260781880000,3,0xc0c15c0cf20489c07c00,0x590efb057c00000c0,0x5b70323f01cfe267e450,0x8a0093000000804c0000,0x806200001e220000001,0x8999a209e00000000000,0x761ff608e64011804,0x41d011324a3f8087600e,0x1c49554151b03f2,0xd255a00a034114800007,0x3206019dc1e38000000,0x10095101e680000104,0xadc0206018a000009409,0xe8229f808180000124c1,0x40942c0efab925392a80,0x2ccd5e01590000184,0x92581bdb8947581a6000,0x404b00000464a00000,0x30226b236364684,0x41f0a040200001e80000,0x1ca181e30000148c9840,0xe40000021017442a8000,0x2022a813c,0x8000090262005e4c5063,0x8041d400aae884000038]) else (word80 [0x82d13c0d,0xbf39dd112bce49a40000,0xc4673a06c300992,0x83b8404a40000081c2d8,0xe4502c408ced8217201,0xb8e40c80225800001811,0x50000000000000049009,0x307400000380db280494,0x61fc20e554198740d700,0x208f3418608175b01,0x6a806901099892b50000,0x1c026d82197908f70118,0x481d7c84f80000e73600,0x241d7290c2740ac80,0x2a000006820900000000,0x3c17d53053f01dc0000,0x408600000,0x1aa22b0,0x454e02ab000000000280,0xc4f8105a115de01f8007,0x90000000000000000000,0x490c45025a0000000000,0x2101378,0x36538190000000000792,0xaee06e60000280230000,0x180dacc1b4212d1,0xb50f800003019b208900,0xcad48f259a0900,0x164143401280000000,0x2410500000302c,0x768181c8a68000000000,0x5305b000000,0x1a0,0xe6fc04c5916500000445,0x980000000000000080ae,0xac1b4e12ac7001fc0d54,0x10394000020,0xf92098c742fc0000342,0xe5823ec05c7e094cc00,0xa683b7107ac0000041bc,0x1a1320000020f50c1e28,0x4c6c0,0x29a7255880c4d446000,0x642f000002d4468000,0,0xb529d8074000005820f0,0x3003a883a5213501,0x2b3804c1c0df58342e13,0x360000200349829ec028,0x6461f784560000000001,0xe0dc4000000000000014,0x24800ce789770000000,0x781f36063b281,0x2c00002806eb05f60000,0x5320c0000000000,0x100cc66,0x68f015b1012fc0d5800,0x699a77207bc6a3e494,0x27833800000000000000,0x1032fae3ec00004,0x14a0000000000000000,0xa70bbc0bf79068800,0x5002d887cc00000206,0x590186088e0000000000,0x105b5e0d4ac16aa3259e,0x4e9e435000003002ce0,0x78680362152c1007a441,0xa0649686067302690000,0x128cc800000000000000,0x200fa80000f05580,0x106cce1,0x14325e0a84182041ca05,0xed41208000000000201d,0x4c045f038a2026760157,0x883480000a7376022b48,0x113c012fc07e246b0511,0x9e800000000040b48000,0x1828ad05a8509d200ea,0x50319000000000181d7e,0x805850721646d8000000,0xb0780822a2c876981,0xe9900fa00002810e6899,0xa4224c80f28cc94e038b,0xb05cae1014000000000b,0x45b00000000004207200,0x40c0000101ccb2b72000,0xe0ac28958b831af246,0x4c007981920000000001,0x3e000001099d00001c,0x908a0199a8406506a300,0x50a11ef982083061ae11,0x28c6ac203264191e04f,0x3206e80000702bb50302,0x40f68c2b0c43e5681640,0x709a0b031c0000088,0xa4801c2120ca00000402,0xf983aa00250000011c7f,0xb02704012a8259dd0949,0x2ea205954046d448af8,0x1a170232409e39cf4800,0xf04fc0000000006820,0x1f0587e042680bfeb909,0x603dc000034140b827f2]))) else (if j<6 then (if j<5 then (word80 [0x4090d103,0xd100001e0acea06cb83e,0xd574392a51ec19500000,0xe,0x636e0000180ec480ef70,0x827407f0000012a88e07,0xa1e22815cde21086e235,0x80000000005407500000,0x40b9c000000000000000,0x42b99071483b10000126,0x5b3000d280c0324e0800,0xea013780000021b2e03e,0x98015fb900605ac44044,0x30,0xd5c82f8401bd00aaa52,0x1248392a00e6a8715919,0x5aa048b0334600040000,0x980e2010ac882a6,0x80a11069340e90e5e280,0x7058400002408b000,0x54080000,0xf21c7c2e08000048255,0xd0174810f1003b8a3240,0x181db0000000,0x18680a902d02b18b94,0x35e8cfe48c4000000000,0x41f40000000001744a,0x1a193c203900001c,0x34cc16c983b07474800,0x2100000000000020,0xabc06800000000000000,0x3820000124649,0x81c0d1263000012468c0,0x1a1cf70536a00f309,0x95f00cf40298c0d06192,0xa00000f045b447985d9d,0x3009f0000000000820ff,0xb9e87725a00001c9356a,0x1c7e014a000034187081,0x56000014105500484307,0x72052280ef35083f82d3,0x80591c0a485545e834a4,0x41c768cf294a479b9200,0x600c14194da1b2304,0x9364271009a000000000,0x1c0afdc12d00000e0722,0x2456e5c2a58295800d5c,0x9dc00000a32f7066442,0x48582118000000000e08,0xffc222bb07e503800000,0x5029c3067200000,0x2098c0,0x301d17047140a7401,0x46982834084ea0d2e806,0xb800003045f207c74d76,0xf03f300001c236c00000,0x30030451b1,0x1b230292000024059880,0x70006424c303ccb6900a,0x7605daa109400006810a,0x701eb20857dc2df0199f,0x60c0000382108000034,0x4e0000304b480000c05,0x62e40f955454a423b060,0xa000000000502af00000,0xc02dd406e908ab00000e,0x28bc0a38000000000c0,0xa30000000000d250a000,0x1800c5831c000000000,0x40bbd12744013daa263,0x1910000000001ae7a80,0xa31840000000,0xb21d400000000,0xd083c000000000,0x6821f00001904d4c4556,0x2878005f200000000058,0x1ef000016018f41d3581,0x7e806de0071000007043,0x400001445fc00001a201,0x18c0000000005c955f,0x1112000000000513d782,0x47200002c05f00000b25,0x2bc1110802900000e466,0xf60f4cc0d28000090598,0xe00400000118b6000000,0x1a3237064c00,0x8678972b05c4000,0x3492900000000000000,0x3c89260148f019000001,0x8225220d6d113da4b04c,0x80acb1478641a0ab8800,0x483fd00001082ee01c,0xe280214043b6cd82c0a6,0x80000003e92002fd1eea,0x100b1404241e6019d30,0x4200000000028957c01,0xae60234e0c0444da0000,0xd000b006fc580868247,0x1604f80000733450,0xad00244000000000d0,0x70fe0c400000421f6e06,0x5aa8de8000000000e010,0xa2418c0000380d9080e8]) else (word80 [0x2e03f850,0x69c2c93f821800000a44,0x80000081dee89221485,0x16077ad02200000c0766,0xc0d900000000002,0x24a780de80000f051200,0x390e9501ce40419480,0xee890d80000421ca0000,0x11081000000000020dff,0x219f904e00000c09c80,0x481c1f3228c0db400,0x1005173692c05d8011,0x46a1cca52920000341bb,0xb827d0018a40b5d00340,0x121c0000038c5b80,0x182661c1daf20,0x6f00000000038083180a,0xd0000000a10c12600000,0x302960,0x100ae640e68000000,0x10e360883880,0xd9204040000000000000,0x1c43ba80390000080835,0xa1800006a06722120a,0xf08000000000c114504,0x460045a6488bb0188601,0xc700b3ec92e000010ee0,0x7904d000004123800003,0x40250223d00000000000,0x1919f000000000000,0x488840000000000000,0xf02e8a0478906f,0x80000102300000000000,0x103aae25f4000000,0xa22f7e0e9dc82b090,0x6c724fc846b588470305,0,0xe,0x11800000145458000000,0x100292d16969bc7242,0x2e000014224f01e7e813,0x500fc141aa5099eb32e1,0x60a0b815a9029900000c,0x8d240000603ff3033b20,0x8b9013aa825dc027f603,0x400000a246c02cda0b1,0xbcc45ab85cb323e00003,0x802e100ca8042c000020,0xa90000000000e2e5000,0x466d800000000,0xa42600000000000000,0,0xc0470000072,0x9c000000000000003a1,0xf4b01a9a00be0895c01d,0x600000e0efc0000581dd,0x27210000000000000000,0x122a2800003206e76,0x21ec6620000000000705,0x4928d280000401b1a03c,0x40086394478000028268,0x5001ce74664,0x87bc0000481fef80ed60,0x3a341180000000000000,0x721b0e25b,0xac110293aae077608734,0xc03e0000000000000034,0x8f1f1154d08900000144,0x61899607438600000000,0x7335a000000000,0xf629452f13c14a7,0xc9304088e2000340cc00,0,0x2019,0x200000c08a8000000000,0x4e4a38017000005,0x24f4205e800000000094,0x38800000000000000000,0x1096f7011,0x1ccf6c00000000000001,0x28b700000110da000000,0x92d00000140,0xe6a083d800000720900e,0x9684cb400ea00000041d,0x8000041055000016256b,0x105eb80bfc045882a9d5,0x9d40297000010e4b290,0x69183864005400002592,0x76123dc027400002017a,0xf035b00001e07164cd4d,0x11d0088720d65409300,0xf0416000000000000,0x643928113e00330000,0x401fe0000080b700000,0x506c9c0e340000000000,0x201373a134f0,0x1d3c0e20000038139000,0x104a065023c11dc222c,0x60000000000041000001,0x68d6fc00500000000000,0x120,0x2aa420080000f04c440d,0x34000000000b0004e058])) else (if j<7 then (word80 [0x4bf02960,0,0x180f,0x3800000000000001e092,0x1813b00000240e4,0x198000024480000010,0x1649213900000e00e340,0x812816f607d360ff0000,0xe010460c9dc0d1,0x800af40b4000003,0x20be421ae00000000000,0x802c800003407c800,0x2a2a06b281a00038,0x22123c49dd4879e83ab,0xe0340c054100cb102a9d,0x727c0992813b0000000,0x4a200000000000a9f000,0x44f6c0000000001000,0x800003c1111a88e00001,0x403f3012ba810b500720,0x14190000007062c00,0xe0650000,0x3c10c80000746fc0000,0x4a895a04bc40140,0x7066e000038,0x1d14834f9134a707e481,0xd9582c000000e09ad493,0x78000000000000000000,0x7016030022a0af509400,0xc0fbc000000,0x506f4000018027000,0xb84fa841f000000000,0x1e0ab4000000000,0x50184000000000000004,0x6c220c4b90658000000,0x5040000480d5106,0x16c0791421d00000222c,0x508ce8000000000e43a6,0x9d9e00000000000,0x2410f22184f22c200,0xc037f825fa079e000,0x30087c8c03e065e2244,0xa019f910eb0000000000,0xd869b041a85,0x1b168302506bb208d800,0x3210e000000000351a,0x900000000018023c0000,0xa724840387ccda0,0x828700000205e1dceb38,0x25b00837a42480000000,0,0x2016000001018c4a366,0xc,0x7504812a0122b213820,0x5c84a258000000000704,0x2f207940000202322065,0x80000100120000000001,0x4e09c000000000d05886,0x84ddc1bb789970000060,0xc5400c3181948413b04a,0x8c11eaa183f05b780eb,0x308c82392780088c07d8,0x14a21b4,0x47728986000000000180,0xa7d824e07247a067f00d,0x3c801710434ca2415031,0x1125692a70062c00005,0xa0d082c00000000000,0x590,0x77166d60000318d72003,0x750447c41ea41c600000,0xf12e9209c49cea800000,0x1a00c400004809d00,0x12843400001925c705,0xbe00002c1479005eb40b,0x120a8400003006de32d7,0x62291493e8000000221a,0x53b84b47888f450f621,0x1c0000011f9c00f2a07,0x67c93f80000207be0000,0x10893902884233b24285,0x8139a0212903cd40a4e4,0x83c00000f84da00002c1,0xcc700b10000000000000,0x3ccc5,0xb0258a081e0000000000,0x4c00000000018d08e0,0x700000408eb0503023,0xd6000000000040143835,0x70000000001400948065,0x1843840000084350,0x8001a88a980000c0,0xb250392919f199a6302,0x3e00002019aa20d32046,0x660c784552d197a90746,0xc0554000000000021b60,0x582e60000140,0x965d04d80000840bc004,0x90c227203e0704c3605c,0xa803a100190000000001,0x4f8120c025c00000c,0x1dce82dd821c80000000,0x18e0000001a]) else (word80 [0xf08700000000007a,0xbdb6224720f240000584,0x4d212bac0d9c00003010,0x70000180e3a817f90384,0x1204ad012e301685,0x31e00003c8500000000,0xa0a408ddf80000000,0xf000,0x60000000001831b603f6,0x2c7fec10d8482d000000,0x11cdfd801fb03874a,0x2740558043700000a27,0xfec932883f5a03d00000,0x220357842c0000180d72,0x1257005b8141ba05f40,0x8180773be00001c1,0x3d624292026d4301a884,0xf61185002e3800c88890,0xc8112707d1225b74d078,0x305ee00000000068,0x121d234e00002817b180,0xa3000016489400000000,0x3083a00000000000000,0x184b8800009,0x56ddc0dbbc1821837464,0x6b8e457c011aa8113f06,0x15e66248869000000000,0x82a800000,2,0xe3dc93c800000000000,0x101fc8000000000000,0x1413680000000000000,0,0x48183301ef8068d8,0xd67303f7507b49013c00,0x3418800000000,0x5c0391007700611c1fd,0x800000000000003c1d08,0x390bf94,0x20d4078d200db8036480]))))
def g235D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x8800c484,0x78890b1012224445880,0xa90c110ca840690c1118,0x8c14858428101242304b,0xe04a16084450a089842,0x2912400216203068858,0x88910b100c0010858911,0x18916084440400216222,0x800a08212203062c1088,0x8582100c2102c1910048,0xb101420c224040818b11,0x102422c4040858800244,0x460290b11100a42c4440,0x844816102212c4440c90,0xb11102002c9088a48b80,0x4405083011010217201,0x84205832200916202841,0x844808100412c4451010,0xb1010216200091118611,0x20196104430a09210101,0x85049080a10c11202043,0x44808111012c4052c10,0x897202a2025880804c17,0x2c4054490b1010222009,0x80a88b100d101304480,0xa040102e2012e4033000,0xb1202446086088610b01,0x222110010b1014100085,0xc80a44016084052c0400,0x43044622582101010008,0x5c80a5c002202020600b,0x885c002202010400c080,0x80172021700442901488,0x2c404b54d9e6ca1619a,0xf15676adb536a86d33e9,0x23430a004f0a73335b99,0x94bd2597294935c92643,0x31db8dcc64229712986b,0x42b611705b8193fedf96,0xf8d7b5bcede16ed4755b,0x9b5c96e146f5b709b08d,0x5469933ed96cc9463931,0x9816bdb5d22ded66cb0,0xd5722ad1524a70523a84,0x13dc9c54d525e92b0921,0x47c233d13e87d43120c9,0x207e73db9e54ef475f3,0x9b1c50de46d035019f8c,0xb863a30c17d8b9a5a42c,0x1159ca98523280936096,0xc486235914085c4051f1,0x8f0473036f1a68c90604,0x2d915f0a544e62581140,0x8343d61c20cc85c02801,0x1e07a834c16208f03681,0x2c044000ffd8940ff989,0x40ff58940ff18940ff90,0x940ff50940ffd8540ff9,0x8540ff58540ff18540ff,0x90540ff50540ff95220f,0xf55220ffd0e20ff50e20,0xffd0a20ff50a20ffd062,0xff50620ff99120ff591,0x20ffd0d20ff50d20ff98,0x520ff58520ffd0520ff9,0x520ff50520ff10520ff,0x8c520ff4c520ffd0120f,0xf50120ffd0c20ff50c20,0xffd0420ff50420ff9521,0xff55210ffd0e10ff50e,0x10ffd0a10ff50a10ff54,0x610ffd0610ff50610ff9,0x9110ff59110ffd0d10ff,0x50d10ff98910ff58910f,0xf94910ff54910ff14910,0xffd0910ff90910ff5091,0xff10910ff8c910ff4c9,0x10ffd4110ff54110ffd0,0x110ff50110ffc8110ff4,0x8110ffd0c10ff50c10ff,0xd0810ff50810bf58b40b,0xf58740bf59240bf58a40,0xbf58640bfd8940efd094,0xef50940bfd8540bf588,0x40bf58440bf59620bf59,0x220bf58e20bf58a20bf5,0x8620fe50220bfd9120bf,0x59120bfd8d20bfd8520f,0xe90120fe50120bf59020,0xbf58c20bf58420bf5961,0xbf59210bf58e10bf58a,0x10bf58610fe50210fe4c,0x210fec8210bfd9110bf5,0x9110bfd8d10bf58d10bf,0xd8910bf58910fe94110f,0xe54110fe90110fe50110,0xfe8c110fe4c110fec811,0xfe08110bf59010bf58c,0x10bf58810eed0240bb98,0x840bb58840bd98440bd5,0x8440af99020af59020b7,0x98c20b758c20bd98420b,0xd584209f996109f59610]) else (word80 [0x84016084,0x490c49088885888c84b1,0x28844510842002c4888e,0x490c10010b111c112828,0x4a002c44212942220040,0x90c492a21a222101d2a2,0x251080a3442508880102,0x44124a8a2c2001081004,0x9454b0d1c2444e021001,0xd868e0a14858632161c,0x14685216222a5229080a,0x56284069521120441424,0x521614a0282910842258,0x88a96124202938a052a4,0x844072684b24222a1485,0x8889152c1429088c5628,0x382950a4224134840b08,0x904062c4454a8e2c3430,0xa00748487485c808049c,0x54b0d1c280910872cb11,0x485c80b11217222454b1,0x12112034142592111494,0x14201216223c54a0e124,0x203158a101a549088100,0x52172021308052172030,0x5868e0a42c3190b0d1a4,0x825878a948a4202958a1,0x1a54844811048a42c21,0x4080924122587889080d,0x2c2c54a21210149c5029,0x52080840832512a24840,0x64a89210122a50709124,0x203958a101c24a892102,0x4a242c4044820b101124,0x40c58411192230d12197,0x2c3a4882082522323868,0x83412c9070c90b082228,0x2290d1a2829031624410,0x485888b1122220585311,0x1216224068890b101222,0x42c40484886242029284]))
def g235H8 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (word80 [0x242aa000020215d89a44,0x84000000000e5094000,0xc15ad51d7c076000000,0xcd95000010081e25,0x76d17e3494f819a00000,0x50ea000000000a261b88,0x2e000000000815c242cb,0xe0,0x174000074100c2700000,0x34254c614380a1b23f34,0xb74848cc3e00000000,0xc04784438049a000000,0,0,0xf0b1000,0x2da8bd20f40000,0xb0c40000000003899ec3,0x6a000009037c00000000,0x2cd73000000,0x41000000000280b,0x2c24b00001406da,0x20000000003924c000,0x38437000000000d0b60,0x94722281400,0x302a500002404c,0x605c0000012870000000,0x7090,0x981cf000000000000008,0x16bf38e101c71096c89f,0xdb2b2b497a0000100b50,0x3915d000,0,0,0x1259c0000701f30252,0x54347c3160000101a600,0xc2c50000,0xe286c0,0x1398400000000140c,0x70000000000000000003,0x34980000340080000000,0x240d800000000000000,0x4f10000000000000000,0xf0593817a00000c0b7,0x807b2d47100000c21bb0,0x8400000000000004208,0xa00a921bdc4823000000,0xd09e00000a2730000,0x1fc106b800000,0,0x204ec,0x9063a89a4f206400,0x14238000010045,0x702eec306000005de180,0x4240000010ef562e5009,0xc12d000000,0,0x76c0000d1b8800000,0x8e2600000000020a,0x100000103900000e06b4,0x109a800000000304,0xf2d020dc1aa000000000,0x1c42700,0xb210c00000000,0x50852459c000000,0x70778000000000000,0x3c14b8,0x2e88e37000000000000,0x14226000000a20d0712,0x86e10000105950000000,0,0xe76d8000000,0xaa5c296000000000504e,0x40000000000000000000,0x4380000310a4000,0,0x38808a899ac5e7000,0x1043ed088902442026c,0x608ae407e0000000,0xd08900000,0x2028b00,0,0x1c,0x2d16a00000a04c4026,0xe00000000000003c1875,0x1235230400500740002,0x17001500073200901000,0x30110210073001324c11,0x255620017237212103,0x232e2042800320013010,0x31035010a080012000,0x21136030112191003004,0x303b050201207e2002a,0x16112030222551711001,0x12602000000304001200,0x7020313232002270300,0x3001160405540210700,0x2323001201020201,0xa012316205021211105,0x318100101020001131,0x30f1310033201110202,0x531310000010009000,0x140021030002002201]) else (word80 [0x701dc000,0x44e6a,0x4c211c53b03b10323000,0xf0038,0x102e08c0000085bdc00,0,0x1c8000000000000010,0x3740000226c000000000,0xc1c9000000,0x90bf8000000605404,0xf94bb000000000000000,0x3497c000014115612,0x3542ccc07a98ec3c2550,0x5a3000,0x2c813000000000,0xb25d4000000,0x5205,0xc00000000040e3f0b540,0x3c9a,0xf00000408b0266041480,0x1401680c848966021,0x6c000000000000000000,0x340c90000000,0x2009c0000000000000,0x81bc4000070,0x68cc2ee8164dc2020000,0x3421a000000000a08390,0x29fa18580000d16b0000,3,0x46758188d4b53027f000,0x19c6400000000000003,0xc82000002830a0000000,0,0x816c000000000100ab20,0x703806ea012c0a7e6078,0xc01d2000f40000000000,0xf67f8000,0xa046400003287400000,0,0x702b0000000003,0x314000000837349c950,0x6160b4800000000348f5,0x2049c0000d02d2e27080,0x5c00000000000000000,0x1883c00001d161000000,0x180505036c000,6,0x9a00000000000000000,0xf275c000010514,0x42eb0000000,0,0x2508c5420e02340000a0,0x8ec00000000000000000,0xc,0x290889bd416700000000,0x3c68b0000000000,0x34106000000000007,0x3855916077c000050a34,0x140,0xc300000000000001c15e,0xb08bc000000000000040,0xc6400000000180cc0000,0x1c,0x2dc00000000000003a1d,0x500001416f0434c0000b,0xa540000000000000000,0xe11204863800c6,0x826b476e1c5dc0000222,0x1a043a40000003199026,0,0xc1ccf0a8c0000e017,0xac051000000000c0bcc0,0x70616411a00000000,0xe76d000000000296ba0,0,0x205ba881500001,0x5c583640000000000000,0,0x388f78441c000070,0xb2800000000042be903a,0x8000000000c449000000,0x2ab4000,0,0x18118506600000000,0x1819c00003,0xc0bf9468aa2720000000,0x909d40000000000000,0x946fc000000000000000,0x1d40000307ade01f0000,0x2409510a7a01fd00003c,0x257928040e2364390000,0xd093000000000000001,0x5851c150000000000a01,0xf4000060014625100000,0,0x22754000020c90951f,0x3c827645e29dc1b0,0x2f0c1e88043c00000000,0x189a600001929c000000,0xa474382790000001d,0x90000000000000000000,0x34e1b000000000000,0x8680000000000])) else (if j<3 then (word80 [0xe066214c,0xc0000f8714416300000,0,0x30203,0x3013400,0,0x146eac,0xaeb051c000000000000,0x3424a209f400000,0x38116e11080000000,0x625f8,0xc13240c2342b90000000,0x399c5000000000,0x84,0x7640000702b400000000,0x89b2300540,0x903bc000,0x19c57f606601e1b,0xaacc058a41880000502,0x40000012b31018600000,0x102b30000000,0,0x2202cc6cd00,0x141cae0c2c00000000,0x30,0xa0f0000149ab00000000,0,0x280f4f16a80000a60,0x6c0000449385033700da,0xd0d2b06f800000000081,0xf3000000000000000000,0x536c40000003c5dd8720,0xc7dd26744c1c0000b031,0x742e260924000000002c,0x3059400c000000000000,0,0x5246c508b86ea620,0x258059a02d8000000000,0x250e50000000,0x2bb0c0c49b700000c200,0x5257406c4000060,0x59810ca000034294e1a8,0x5090661ca504a4c,0x1f000000000e0a24000,0x3410db21080000d,0x24000050a300000000,0x1913e00000000000003,0x1fb802cbc12e8457bc0,0x65000000000000019a8e,0xe00a1418c00,0,0x20,0x5cc90a88000000000000,0x2953810bde42fd5,0x2716042351b3ac0f5800,0x1302d300002857a00000,0x29c,0x1b000000000000010571,0x50,0xbc20034606c1560d3416,0x80000c0b340000000000,0x40096015400000000,0x702440000e02030590b,0x299202d6000035292000,0x2c11c3047e164a00001,0x80d10000282e40000000,0x9049b0071,0x644fc000000000000000,0x4a990410000,0x2c2e652780000000001c,0xd954462426000000000,0x80b05403302649c48be,0x846c0ed50bdbdc65000,0,0xd2450000000,0x7011249ca,0x300700000000034219d0,0x54161b373050bf909b,0x5016120000,0x64078000,0xf03e80000000004c4f9,0xbd40000006580000809,0x840000412280000b01a5,0x8266e08a00000b0c0255,0xff807d40000000000000,0x3406f426d402c6f0,0xc6c000000001428ae494,0x842dd000000000000000,0xf04ac0000d0508000,0x2910,0x606ac0000000,0xa4a08,0x25c0000000,0xc256c0000000000000,0xf0,0x88c00000000000000000,0x1dc5e000000,0xb075c0000815aa499,0x5b055400000000200f61,0xb40000f09380000000,0,0xe00a8000000001c2,0xf900002c0f0000000000]) else (word80 [0xee417c85,0xab0000100e9000000000,0x5fe42b540917d0c000,0x4326000000000a057,0x40000c71a80000000028,0x1ff00000000000000c23,0x2306f6416c7054400005,0xbc8000034acc560e000,0xc18470c0b,0x9d6204209dee01b4a42,0x5ed77940000000000000,0x5420bc03f44364000063,0x6a59d82326d000000000,0x100a5000000,0,0x1c1c00000,0x414130a909dc0000,1,0x49ec0000000008016800,0,0x218500000a3,0x11c0000c29ac00000000,0,0x34cb4149fa020,0xcf06480000000000000d,0x43179634908878018301,0x6c0000d2125cc4e4437c,0x427facdb30000000,0x3c27a,0,0xd00f0056c1021,0x8d2b46082741ee000000,0xa062c0000a1b5c000,0x2c9680,0x1c03e601,0xe40000308d489d100000,0,0x188fa000000000,0xc02e00000215f0000000,0x80af0000000000000,0x20a7c000000,0x62948925,0xc0000000000000000000,0xd05580000000,0,0xa090c00000000000,0x2cac9000000000,0x1122d00000d02d00,0x194ace0b4,0x7c30dc10a8d105125ac0,0x483980650000,0x3120000000000,0xa00dc0000000,0x3c87400000,0x5500000c14a703f400,0x214edb44640000,0x38218000d4000014,0x58800000000000000000,0x20997000000000207b40,0x50a1400000000245a,0xd00000000065adf42a80,0x706578895000,0,0,0xe14e40000000000000,0x80531c06c00000000000,0x34267004be0a089015,0xac264408f90825a21ec0,0x34240c4284000,0x398f40000f0173c0030,0,0x606ec,0x700b0000000003c1,0x8d000000000002a80000,0x180daa05c6c53800,0x28206a964bd015366d,0x40000000000000308140,0x180f200000000,0x716a400000000041d0e,0x56dd437e26400000800,0xc000000000201c141980,0,0xf04a00000,0x250d76521ac05400,0x3023,0x88085e18558476781000,0x14e70c60000,0x2c50d0,0xc270110cd14b,0x680000b38580000b0768,0,0x407738049,0,0x843f0000000007087,0x9de3000000,0x2c84,0xb000000000e277d5644a,0xa6f9d42000000000311,0xc40000c06dc000081430,0,0,0x50f600000000030,0x759c2fc0000041c53069]))) else (if j<6 then (if j<5 then (word80 [0x709de700,0x2820b00003950c0000,0x3c2f4000014020000000,0xc18900000000,3,0x457c0000240d40000000,0x60a84,0xa09ce01307002800,0,0x90774c06a00,0x88aa9c073f25d,0,0x246ff00000000,0,0x41,0x7549580000341f9e2a9d,0xc0ca10ae0c13f0000140,0xcd402660199d29cd5590,0x45a2c000000,0x243d40000902f,0x400000000181c6b093c0,0x1d50100000000,0x247110000301580,0x172000,0,0,0x210f2000031a50,0x3207f10e300000000000,0x1844700000013a0010,0x2c269000000000000000,0x1360000000000387c000,0,0x5087f0265821,0x46d68d117ff40fba20e0,0x15d6b1289400,0xf05800000,0x1869e00000000020,0x39c0000000000000e018,0x80000506e001f8000000,0,0x343170000000000,0xe01900000302,0x4d5dde00000000000000,0x201,0x6a000000000d0b8cc0c8,0x10954000000000000000,0,0x1e6c40000142a6051ce4,0xdc000000000c08281dc,0x9007929db7c097fc0922,0x715ae1dc000000000812,0x3c00004591c0000806e4,0x800c916,0xcd00000000000003c168,0x11091416900,0x1483e000000000127c,0xf004a412c000010,0xf3e417800005010aca0,0x600000c02f609d800000,0x1d165c034090f3000,3,0x5dc80000000000000000,0,0xa6770000000000000000,0x30a070000000000000,0x3d15b00003a02d508d10,0x22e508204ad3b43c3d18,0x45718c0000504040000d,0x105a5000004a1f000,0xa01e8,0,0,0x303fa006600000000000,0,0x289c6000000,0,0x4140801a000000,0x146f8001c00000823,0xed20f4a21f501fa00000,0x52297699800,0x4444,0xa085e8a55900b8000000,0x90c8055fd8075,0x6258dd17f000028,0x183e0a498704407c1456,0xe00000000000002d018e,0x4740000000000000000,0x102bf00000000000000,0xd0794000000000c2,0x56000000000000000000,0xf057c000000000000080,0x2cc82c2a4c10c8260000,0x1d26ff773c000020067c,0x1528080616ff00000000,0,0x2505c000000000000,0,0x328a000000000000,0,0xa0a180000d1,0xb8da589000000000906f,0xc869f000000000000010,0x123000034e5400001cac]) else (word80 [0x81118000000000000,0xe,0x71400000000000000000,0,0x3c1,0xa0c0c049477a80980000,0x102c000,0x53aa,0xc0000000000000d0b240,0x1c48600000000,0x5458dc250a,0x58c618fe000000000000,0,0x142,0x37c21140000000000000,0xc29a90,0x55c82596198c00000000,0x3d2b2000000,0x23a8c000,0x1da8a8,0x9bc00008019d8177000,0xd44f4000000000,0x466100002c0480000000,0xe533d800d000000000,0xf26b000000000202fab4,0x6f8000000002c1ba0000,0,0x3497f0000042e,0xf616500000b064d00221,0x8c0000000000000000,0xc06100000,0xa004c0000305db01,0xb6a7618122a00001044c,0,0x8433800000000,0x40220044a000000,0x1058bc1c,0xbe71a000000000000001,0x180c2fb549580000507,0x4514fe603f0000000000,0xd2800000143150000000,0,0x30050000000,0xf065c00000000,0xc,0x2992177c000000000000,0x40870000001fe8,0x91c0000a22440000000,0x42b000000025800002,0x4153000000000b8a0a12,0x7143af80000000000000,0xa166b80d2b4318000000,0xf0b9489b1f020,0x80000000000000000000,0x3e63,0x93406940de4096800001,0x89a00000000000000000,0x100f900000106b00000,0xe029800005048000,0xd700003c174000000000,0xb49840000b81f1807600,0xb00e,0x40000000000000000014,0x17900000000000003428,0x70000000000000000000,0x30510503,0xb80000000000000b0494,0x4041400004258602,0x1090aec0000000000000,0x2062b81b562,0xe800000000000000067,0xc00005377c0000000000,0,0x823e19dec1,0x49ac51ca000000000a02,0x5352f300003caa4e053c,0,0x70947d0d8000000000,0xc15b441142048a41f2d4,0x152504a0000126bf0000,0x80eb000000000c280a8,0x30c00000000000000000,0x41d3c070cc42ca,0x4e1800f549260599000,0xb499b8010808e5,0xcebd0000000000049000,0xb03fcc2ce726000000,0x30aa300,0x780000000030325b0b6,0x64db261837059b006b00,0x8056842ba3272c000,0x80641c3070,0x1e2cc000000000000,0x1c20f50118000000000,0xc04f800000000000,0x30a60000000001965e,0x64583c1b300000000040,0x1fc0000000000000038f,0x24899000000000000004,0x19100002401100002023,0x3615040000e04dc00000,0x8006000000000927])) else (if j<7 then (word80 [0x8a540,0x14103000,0x311da00000000060354,0x8c441f600001c1,0xa8000000000000000000,0xd25ef4569000000000b4,0x59a909a0000000009415,0x40000000000000000000,0xa04440000c4a42942,0x400000c44b0185d82047,0x46840000a1c300000000,0x34167,0x513c90ba5d4840000000,0,0x814900000000000,0,0x9c67000000000000000,0x6006b817,0x80000000006282400000,0x101c2000,0x2024d00001117680bff,0x89dd0000000000000000,0x141000000242c7,0x6026282a7e028d41ef36,0x60919b4006d000000000,0x1106000000c27c000000,0xd420c930,0xa0000000009495400000,0x1c971602285dc7000,0,0xf022680a272594c3,0xfc669f8322000000000,0x140a0000000000f2,0x7b400000087800000000,0x1887800000e6c0b02740,0,0,0,0x860e3085a530600000,0x425c2d2700000000,0xe80000042bda0570819d,0xc5a78000050,0xc70000000001c09c70c4,0x4000000000000056a000,0x2c06390230c0c,0xb000000000d044800000,0x208,0xa75dd7400e0000000000,0x50896c2130000002,0xdb00002c88100001ce10,0x191bc00000000000,0x10425f02fac8470078,0x80000000000000000000,0x316b8000,0xe0c4d928b6035000000,0x15f7416d3051241b2000,0x9a6f00000000000003,0x40e100002e1740000000,0x1c309,0xa0,0x7400000042c00000000,0x342dab26800000000000,0xc010c000,0,0xe089c0000000,0,0x1c22d0000384,0xee000028074609c402e0,0xc0033c20700000000000,0xd042,0x80000000000000104d64,0x520000141210000351f,0x60000251640000000000,0x30840000028d7cb02,0xe6428300000000000000,0,0x14987000000000,0x25104e006f9297c1,0x7140000b13b5a2d10000,0x2515c40a080000100ec0,0x3283000009041c000,0x306840000c09ec0000d,0x1c0000000015839000,0,0x708d800,0xc680000021398acb,0x2af4030bc04146,0xa260a10955b3c31ef02c,0x5487c324b910e7946f5d,0xd420bb7421d00000000,0,0x7050c0000f0b,0x7f0a03f025c0000401ac,0x80c76c2d40000000,0x4899d819e000000000,0,0x3825d0000,0x1830ed0ab80,0x10ab0000070518000,0xf40750991000000000b,0x25bc2ec000000000e08,0x80000000001c11385800,0]) else (if j<8 then (word80 [0x824b0b3d,0xc2ea00001089200002c6,0xe4000000000000000000,0,0,0xf09dc0,0x18263d0697652,0x203a8000000000000000,0x2804ac24,0x56c29cc206b818200000,0,0x2428ff03380000,0x1c110e7,0x6200000106bc00000000,0x20a1c2c3000002,0xf600001007b20a06465,0xed0af000a80000000000,0x903,0xe0000000000000000000,0x1170000041,0x75e1c22c989000000000,0xc0c000000000000,0x20ad800000000,0x2423f00002c2c8027365,0xc52c029fc2e800000000,0x41a840000000000000f,0x407c0000000035d05c85,0xf8000000000000000003,0x40f7c0addcd9e0000000,0xe098a51a0600a78133,0x35,0xa3f009f0000000000000,0xb0a21c,0x28e0000342d0908e8000,0x350fb0000251bbf,0x10a10293555b681e6000,0,0x40b9c00000000000,0,0x2c1a4000000000a8,0xb80000645d00000705c,0xe42f1000000000000000,0x20b840000b0918000,0xb0a5c00000,0,0,0x33c00000000000,0,0x38c4600,0x4039,0x80000104f40000000000,0xcc99b0594000,0x14990810c00002404d2,0x14c00002680580d6720,0xb449c9b53fc000000000,0x94,0x8ae03884439d0b5c0000,0x140a400,0x2c9f10000000000000,0x2017e00001c,0x27400000025300000000,0xb0be25254c265800000,0x1d10ad4bed4159411,0xcbc2a000000c27211ba4,0x27199c96d0000000,0xd901,0xe068b81c8f00999e8b00,0,0x147080783501c202780,0xa0b78000,0x6053400000000000000,0x40a000000000,0x10ab4,0x81f40000000000000000,0x425b1c29d000000000,0xa2a6b417d224bc000000,0xa51d340470000,0x3418f8421d4,0x22af15bc105100000000,0x141cdc034dc64f0,0x1465fb0c1341e7000,0xc04f0,0x181bc000e800,0x19a8d,0x508340000a08b1026de0,0x7c40000b888800000000,0x3c212000000,0xc0380000000000000,0x3d0e200002c08f0,0x8057000,0x242482760c0000220c2,0x882bb08f0000030ad000,0x7dd011b000000000,0x123e4000094,0x45c0000b05ec00008030,0x681a900002405f816580,0x4026b004,0xe0000000000000000000,0x1417c629,0xd522a200000000010600,0x44a0400000000000,0,0x41e900000924f00]) else (word80 [2,0x84d00002c5afa01e000,0,0x8075400000000351f500,0x1dce0000000000000,0,0,0x2039400000000000000,0xe77,0xa4000000002d0c9208f5,0x42b1b09f8000014a6000,0x1c19b000000000,0x8a1800000000085,0xb8400000000000000000,0xb031042b2627ef8])))))
def g235D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x14308100419114308111,0x64002450c20440064450,0xc2056404009445103081,0x5900091440c108059120,0x51030500970084451030,0x815900091440c2040407,0x585103091058009f96db,0x19508a379506c1e003fe,0x81fe40fea07f103fc41f,0xd20fe107f843fa21fc10])
def g235H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x170000c,0x74f000000000678e0380,0x201ff135610921120,0x17c0000901300009471e,0x4500000000a13b210b1,0x5b651a000000000000d,0x97be24c603a324682101,0x41110190000a249b74b8,0x5706564f183e218f671c,0x33a2458066017f90768,0x62985a100b935b00004,0x21d1140000705eb4449,0x579b00a00000000a0000,0xc006810800000,0xa06d0000a37b0,0xf5560000a00100000,0x996062539,0x2a706cf037000000008,0x14770740000000000000,0x4360000000006,0x44d106a0000000000000,0x94680000605c6,0x54300000000000000001,0x4e000004770000355e0,0x3751604f000000003,0x14207d5129000000000,0x2e00000000d187d002c,0x45d426b0000f0700000a,0x7f00000000913c7740a,0x185242cf041f03900000,0x610a00000000c8750,0xe74d302740596,0x68000000002003902c0,0x21810000f65f71800,0x16700000000e047a1820,0,0x903ca077000082631,0x69d25a601b00000000b,0x26f97a0000e46600003,0x320000000000001670e,0x441351fb05400000000b,0x859a777911f0000702f0,0x21860072000000000,0xb578000000000,0,0xd056800c00001,0x555a03ed06f941e203f7,0x17d0000c37a90820000e,0x87d0000d086700e705d4,0x20c06ba1467665b0852,0x6540346043613941200,0x226cd24d00000,0x6024d031511c400d8,0x542544c0000a2750000b,0x115d12f0000000040182,0x476e739c053321700007,0x7c521650516240813f2,0x464305010798023400f0,0xe45c124f1,0x65ea016504470283427c,0x7425bd74c803d12153,0x26ae8740000208720080,0x444e801d000074056,0x24ba241503b646515129,0x7300002166201100000,0x94290000107a00008,0x90046f679f259f4670,0x275d32480000c404c,0x290000417ea262312ad,0x439e080e005213a011a2,0x2470000507b004be05ff,0x1ce1130000c7760440f,0x12d501a1015b08110300,0x20d50830035146982542,0x1270570000706300000,0x75715565b13ec,0x74e71371184f08402120,0x12440000b24a00000,0x7067e06000000,0x7e00008783105850220,0x2136744500005,0x1000000000000000009,0x66480048961000000006,0x75075010367055b2130,0x7219000000000000b,0x117c2743361544f00000,0x20610000c25260710,0xc064000000000,0x904c8049000001380,0x4200000000301e802b5,0x8690000255f0000542a0,0x74838052000000000,0xf7526470002d0,0x6214434900000,0x604d0000000000006,0x74100000000305a324ed,0x4a326d0fb8706020430,0x50018180020438208040,0x61c6830a5468b0018,0x28100040013e08401080,0x81164818a062c10110,0xc200023030100004050,0xc00418045010404304]) else (word80 [0xa07824100,0x102500006048c2113,0x75ce0400000406e427d0]))
def g235D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g235H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x7317990942,0x2a0005b283823a800000,0x92e0278180000000000,0,0x3a8b00000000604800,0x694d0a6294210002c16a,0x850ab1311118381a0005,0xa98a3209f02800019d91,0xc00a3900000000054280,0x18a042cae347335240,0x2b3888800000000501,0x5448000006c911,0x3800000289212624e880,0xc38c36442830001a2800,0x7aa9a3f98238db4f1,0xa98231156208034a0060])
def g235L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g235D4)
  | 5 => (194,5,5,0,0,11,0,g235D5)
  | 6 => (1106,4,5,0,0,14,0,g235D6)
  | 7 => (807,3,5,0,0,15,0,g235D7)
  | 8 => (136,2,5,0,0,13,0,g235D8)
  | 9 => (10,1,5,0,0,9,0,g235D9)
  | 10 => (1,0,5,0,0,0,0,g235D10)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 5 1 0 g235H5
  | 6 => lookupWord 81 373 8 16 8 4 g235H6
  | 7 => lookupWord 474 3037 6 19 11 4 g235H7
  | 8 => lookupWord 361 3623 4 18 10 4 g235H8
  | 9 => lookupWord 76 491 7 16 8 4 g235H9
  | 10 => lookupWord 15 97 5 12 4 4 g235H10
  | _ => fun _ => none
def g235 : Forest := ⟨235,10,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P4_0 : block g235 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B4 : block g235 4 0 2=true := g235P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_96 : block g235 5 96 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_192 : block g235 5 192 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 194=true := (@block_merge g235 5 0 96 98 g235P5_0 (@block_merge g235 5 96 96 2 g235P5_96 g235P5_192))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_2 : block g235 6 2 52=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_54 : block g235 6 54 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_150 : block g235 6 150 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_246 : block g235 6 246 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_342 : block g235 6 342 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_438 : block g235 6 438 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_534 : block g235 6 534 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_630 : block g235 6 630 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_726 : block g235 6 726 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_822 : block g235 6 822 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_918 : block g235 6 918 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_1014 : block g235 6 1014 92=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 1106=true := (@block_merge g235 6 0 438 668 (@block_merge g235 6 0 150 288 (@block_merge g235 6 0 2 148 g235P6_0 (@block_merge g235 6 2 52 96 g235P6_2 g235P6_54)) (@block_merge g235 6 150 96 192 g235P6_150 (@block_merge g235 6 246 96 96 g235P6_246 g235P6_342))) (@block_merge g235 6 438 288 380 (@block_merge g235 6 438 96 192 g235P6_438 (@block_merge g235 6 534 96 96 g235P6_534 g235P6_630)) (@block_merge g235 6 726 192 188 (@block_merge g235 6 726 96 96 g235P6_726 g235P6_822) (@block_merge g235 6 918 96 92 g235P6_918 g235P6_1014))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_7 : block g235 7 7 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_103 : block g235 7 103 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_199 : block g235 7 199 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_295 : block g235 7 295 45=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_340 : block g235 7 340 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_436 : block g235 7 436 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_532 : block g235 7 532 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_628 : block g235 7 628 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_724 : block g235 7 724 83=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 807=true := (@block_merge g235 7 0 340 467 (@block_merge g235 7 0 103 237 (@block_merge g235 7 0 7 96 g235P7_0 g235P7_7) (@block_merge g235 7 103 96 141 g235P7_103 (@block_merge g235 7 199 96 45 g235P7_199 g235P7_295))) (@block_merge g235 7 340 192 275 (@block_merge g235 7 340 96 96 g235P7_340 g235P7_436) (@block_merge g235 7 532 96 179 g235P7_532 (@block_merge g235 7 628 96 83 g235P7_628 g235P7_724))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_13 : block g235 8 13 51=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_64 : block g235 8 64 72=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 136=true := (@block_merge g235 8 0 13 123 g235P8_0 (@block_merge g235 8 13 51 72 g235P8_13 g235P8_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P9_0 : block g235 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B9 : block g235 9 0 10=true := g235P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P10_0 : block g235 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B10 : block g235 10 0 1=true := g235P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact g235B4
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
  · exact g235B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 11 := lower_forest (g:=g235) (i:=0) (hints:=268435539) (before_sound K171 V171) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K171 11 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V171 low235 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x460a2c88b37e938140,0x7f01fc07f])),(BitVec.ofNat 152 (word80 [0x42022800b32e120144,0xa952a54a952a54a952a5]))),((BitVec.ofNat 152 (word80 [0x88a52a524f047c8110,0x7f0003f80fe03f80])),(BitVec.ofNat 152 (word80 [0x80528104e04208100,0x60c183060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xad7c084005cacee20,0x3f8001fc000000007f])),(BitVec.ofNat 152 (word80 [0x8c5c0840050acce01,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0xd132249f3080be5c80,0x1fc00000000000003f80])),(BitVec.ofNat 152 (word80 [0xd132048f20009e5c83,0x870e1c3870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x14a9996da492c842a0,0xfe00000fffc000])),(BitVec.ofNat 152 (word80 [0x14a8816d0090c84229,0x12244891224489122448]))),((BitVec.ofNat 152 (word80 [0x6154152340210167df,0xe00000fffffff0000000])),(BitVec.ofNat 152 (word80 [0x211014020000012092,0x4081020408102040810]))),((BitVec.ofNat 152 (word80 [0x3f00c2649b8102186f,0xffffff00000000000000])),(BitVec.ofNat 152 (word80 [0x6000260918100006c,0x183060c183060c183060]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(16,0,235,0,11)]
def g251A : List (List Nat) := [[],[113,83]]
def g251D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
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
theorem g251G : graphValid g251 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=268501059) (before_sound K235 V235) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K235 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V235 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 12 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 12 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K251 V251) (4, 0, 251, 0, 12) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_32291

open PEqualNP.Outside.L_meta_32291 in
theorem PEqualNP.Outside.L_meta_32291.window : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), gates.length ≠ 14 → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o window fit _ correct
  exact replaceShort g255R gates o window fit correct
