import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_32748.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_32748
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffeffffffffffff,0xffccfffffffefffffffa,0xfefefefeeeccaa00ffff,0xfffffffffffeffffffff,0xffffffccfffffffeffff,0xfffafefefefeeeccaa00]))
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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


abbrev Bits := BitVec 121
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 121 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 121 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 121 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 121 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 121) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 121) (j : Fin 9) :
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 121) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 121) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 121 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 121) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 121 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 121) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 121) (hq : chartSamples m q = 0) :
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

def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 121) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
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
def lanePlace (v : Nat) (upper : Nat) := 2^122*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^122 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<122 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<122 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<122 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 121) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (122*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^122)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 122*(i+1)-122=122*i := by omega
      have ge : ¬122*(i+1)<122 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 121 = (a==BitVec.allOnes 121) := by
  by_cases h : a=BitVec.allOnes 121
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^121-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^121 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (122*i) =
      (f xs[i]==BitVec.allOnes 121) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^122*u+x+(2^122*v+1)=2^122*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^122 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬122*(i+1)+121<122 := by omega
      have di : 122*(i+1)+121-122=122*i+121 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 122) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (122*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 122) (i:=i) (by simpa using hi) _ ok.2
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 121 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 121
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
    let r := data j
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
private def blockWidth (rs : List (Nat × Nat × Nat × Nat)) : Nat := (rs.map Prod.fst).sum
private def partCheck (g : Forest) (k : Nat) (tags : Nat → Nat) (start n a d : Nat) : Nat → Prop
  | 0 => cells g k start n a 0 d
  | t+1 => polarSeries g k start n (fun j => tags (j+t))=true
private def partitionChecks (g : Forest) (k : Nat) (tags : Nat → Nat) :
    Nat → List (Nat × Nat × Nat × Nat) → Prop
  | _, [] => True
  | start, (n,a,d,t)::rs => partCheck g k tags start n a d t ∧ partitionChecks g k tags (start+n) rs
private theorem partitionSound {g k} (mode : g.mode=true) (tags : Nat → Nat) (start : Nat)
    (rs : List (Nat × Nat × Nat × Nat)) (h : partitionChecks g k tags start rs) :
    CutRow g k start (blockWidth rs) := by
  induction rs generalizing start with
  | nil => exact mixedEmpty g k start
  | cons r rs ih =>
    obtain ⟨n,a,d,t⟩ := r
    obtain ⟨head,tail⟩ := h
    have first : CutRow g k start n := by
      cases t with
      | zero => exact checkedRow (cellsBlock head)
      | succ t => exact polarBlock mode head
    exact joinRow first (ih (start+n) tail)
private def samplePairHigh (hi lo : Nat) : Bits := BitVec.ofNat 121 (word80 [hi,lo])
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



theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

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



set_option maxRecDepth 32000 in
def g255MarkBits := limbs80 #[#[0x7030140204018080200,0x1e0e0682c180b0502410,0x602e160a850261208840,0xf07432170b870361a0c8,0x713094482311084401f0,0xe2e168b0562a098a4502,0x8622b170c0562e160a45,0x8dc6c131a8d06632138b,0x160547038160b02a380a,0x3e1a8f4783b190e87039,0x88431f90882401f8fc7e,0x249045238b0664616114,0x6930964a1f8fc7c320a9,0xc28940624f2793884412,0xe4929950944729948622,0x8aa5b2d164b0572b1547,0x60b2580c0fcb8550c15,0x178e0705d2e960ba5d0c,0x6330988c2602f968bc38,0xd66a349a0d06733194c8,0x9ce471381acde6e369b0,0xc1dcec42271d4b874399,0xe3f1f4f87b33924f4793,0x8831c0e104813a200fe5,0x510871617d0c521c2150,0x2391c8e47235188b4522,0x32255289349245208f47,0x9c4da6534894ca612e96,0x2e97271d4e4724ea5d2c,0x8942a04fa792e974ba5d,0x4aa14ea652a910aa351a,0x1582bd5cad562ad54aa5],#[0x8b459ac964b131aa9609,0x56ea03399570b75b2d56,0xaf578bb44a2574a05cae,0x4e30538c05fa717cbc44,0xc36331588c3612c122bf,0x96c7652e192c36431d42,0x49a2d06833d9cb866b31,0xa2c964d432b4da48b693,0x638b59aa7138add3ab45,0x4d951b616e723935daed,0x5c0df6f375b6dc6736db,0xe1cee672b91c8e37138,0x5cbadd4b4593a5d0e81c,0xef753b9dae95187546ec,0xe6f2783addeea78bc1d6,0xddecf57a2c964b2592c9,0xc2ddb0fa7c3e5f0f87bb,0xd7ebf1701d5c28d60fb5,0x30481c0a03007fa11fcf,0x20f0783415b10280c0a0,0xc361f0e86c32170a84c2,0x512c5631181406206738,0x138940146a25136224a2,0x2aee8ac51dca86c28961,0x68582c8cc6473188bc5a,0xdc70a45029148a4438dc,0x890486411f8dc7a3b1b8,0xf2692c7cd1247748e446,0x6450e9643a572a94ca24,0x47e532e923de44f7914b,0x8743a1d2a83cbe0f2994,0x32914ca453196c924f30],#[0xdd0e1c4926b0e9a4ce5d,0x2661269bcda4931773b9,0xecf2773a644e5913892a,0x3a14628330a04fd913e9,0xd44a3d1a8b445050dc92,0x1b146a4bd9c946a43de8,0xcda9d4da63de974a6c36,0x50542a1519fa82a0a0a7,0x549c4b29689a9d42a53f,0xad56ab55590c8643229b,0x66b13aab4e990f94fd5e,0xdd658f3f7bb21915a9fd,0xdab55aad55ae2827d18a,0x556b0d86c0f94fd7ebd5,0xea0c8b1cfeb5599fbdac,0xc619156acd6ec95663d6,0xb4d96cf68b3d42cd4ab2,0x6cb55aecf56b555aacc8,0xb550a85ba2918b6d4231,0xd2e732b950ae370b7da2,0x32b20904b95daeb73a15,0xabcde14177bbc11614a6,0xcf7635faf97cbedf2f77,0x2a0a0a83556d80bfde58,0x5fafb18c160540a0bed4,0xa75369b5bc25427d8363,0x829fdf6c57c5bcfeeeb7,0x4b25c3e1912c6c2a2513,0x2a152592e270788bcde6,0x4322fac8c5e2990c8644,0xcc663190c864321917d6,0x8bc5e5fb1d54bcaf71b2],#[0x5f0bd6432190c8642f17,0x60f1990beb231f505e3e,0xca5369b93c932317915e,0xcbcb6673398cbe5a7595,0xd5947ce69f2cbbeb2f32,0xb3158ace62b159bbcade,0x1687419fcf67596cba3d,0x89f3ddab77bbe9305a3d,0x97cd36970f6ea232190c,0xb53a87ce9f4d48a43def,0xaf354c86431e91825e31,0x7fe56f9565badf0518a3,0xb7a45f16f3fc14fdff99,0x60b7d7eb96fadd66aef8,0xde7f958c6ca31b1ab6b3,0x86d768f7c0d0a84ffd9a,0x9986e16ce4dbb91f3b69,0x70f7cd0683ba723921fb,0x191bc646ed3f5b8c3237,0x1a293beded8e8944a251,0xa4bd9f30d879a1dc6877,0xf9e06fd417c793c99f49,0xb1c2e167f82688a281f2,0x438750e2283877c50361,0x3df78fc7e33cf03c5e1d,0x9a871d8cc67cbe2fcc6e,0xf506458edcbcc1609794,0xa29c95e7228f64e3b1e8,0xe04e2a0e54614150643b,0xe5c634350d0d430550c0,0xb3e668b4318e6e8b99cc,0x45b3cfc1a0dcec271eed],#[0x3ce271a872e8944d0e87,0xcde70550e1af179c4be7,0x7bcf418d4eb15896fccb,0x8cbbcaded5d1a73e5f2b,0xf2bc3e975387d36c7497,0xadf9f6ccfe06d8ffccbf,0xb732f42c7eae59fecbe6,0x44be2de9363b756ab5a1,0xa5d7eb722b27138e8689,0x4377d8d968797d0bcf0f,0xd3ff9eb7ece56a1c88a5,0x35bf4b27c377452a1bbe,0xeb78a45229db8a67197c,0x3b950a3df6d8d86c4556,0xe0adfddc1542b5507fd4,0xf04fe7f67b3d4bbfded0,0x67acd6ac55aad56a7567,0xfb84a4ef28984de786a3,0x13c7e2f132d96cb6458a,0x15f305825e6cf7982f15,0x4de67f3f9fcfef28acbc,0x5a15073579825e2f39be,0xd96c86468b9fbc5e2f34,0xb2ea150ee542a1bcb1d8,0x65]]
def g255Labels : Array Nat := #[0x180121188940930,0x506000904126820,0x104042305184820,0x283021308863472,0x601460305c03431,0x40020a058682251,0x40042110cc42431,0x200230188e01251,0x180200104904a052,0x48008240248220,0x283060309823442,0x283060189823453,0x283021188863463,0x8001140a4d04132,0x506040b05126820,0xc03007238165063,0x844060381846270,0x1001001049049052,0x1000008049208272,0x506000904126831,0x180140281100961,0x41040241041220,0x844030380c4c260,0x200030188e01261,0x180130380d00951,0x400021118c42472,0x200040209201261,0x180121188940960,0x204005128345021,0x8000140b0d04473,0x280040209281662,0x400060311c02473,0x800042251885063,0x230060b01a3130,0x200030188e01262,0x280042219281662,0x280042209281262,0x200042219281262,0x180160381900950,0x506000904126830,0x104042305184830,0x180121188940951,0x104042305184831,0x180121188940961,0x506000904126841,0x18081140a4d0c164,0x104042305184841,0x104040b05124841,0x48008240248250,0x208001208249052,0x60142110cc43452,0x48008240248240,0x40800a25068a042,0x108021308948841,0x4200a0d02c2220,0x40042110cc42452,0x410301c0c41220,0x108030380d08851,0x283060309823464,0x48010280448240,0x108008a44328841,0x208030380e09042,0x283021188863485,0x60142110cc43463,0x283060381823475,0x8001140a4d04153,0x18081140a4d0c153,0x108008a44328851,0x283021308863484,0x601460305c03453,0x40042110cc42453,0x42040281042230,0x8001140a4d04154,0x506040b05126841,0x208030380e09052,0x1001001049049074,0x108001a0c168831,0x100200108904a074,0x1000008049208284,0x208030380e09041,0x108021308948851,0x208001208249042,0x40042110cc42463,0x8001140a4d04164,0x200040209201281,0x180121308940951,0x8004140b0d04153,0x400060305c02483,0x180121308940961,0x8004140b0d04164,0x506040905126841,0x8004140a4d04164,0x601421118c43453,0x180130380d00961,0x400421118c42453,0x4200a0d02c2230,0x800000824824873,0x104000904124831,0x400421118c42442,0x400060311c02483,0x48008240248241,0x400021118c42483,0x4200a0d02c2231,0x400021118c42474,0x41040241041231,0x506042311186831,0x1808410090e0c453,0x108008a44328872,0x108008944328872,0x180121188940971,0x204005128345032,0x844030380c4c280,0x506040b05126861,0x400021118c42484,0x844060381846281,0x180121308940971,0x204005128345042,0x1001001049049064,0x1000008049208275,0x204042311285042,0xc04040209406273,0xc04060309c06273,0x204040b05225042,0x400040209402272,0x40000a058682273,0x400040209402273,0x18084180c4e0c453,0xc02042251887074,0x104008944324842,0xc0c008a4462e053,0x601160305c03163,0x200030188e01272,0x506042311186842,0x4200a0d02c2271,0x50600190c166841,0x60140a45061370,0x60140a45061380,0x221820120821920,0x108008904328873,0x22021188862130,0x104042311184842,0xa0820120820d10,0xa0820120820d20,0x2830213088c3481,0x283060381883431,0x506000904126842,0x40020a058682263,0x820211888c2431,0x200230188e01263,0x180200104904a064,0x20020120820980,0x20020120820970,0x283060309883451,0x283060189883461,0x2830211888c3471,0x240141a0524140,0x506040b05126842,0x40040241041281,0x820213088c2462,0x240141a0524150,0x41040241041241,0x844030380c4c271,0x200030188e01273,0x8000140b0d04474,0x60a60381820b60,0x4800c260348241,0x208030320e09042,0x80000c064b04174,0x8000180d0e04474,0x60a201a0820b20,0x1828211888c2c31,0x40020884c622253,0x22300e0f03a3130,0x220060b01a2130,0x223005228163170,0x200230188e01253,0x20820120820910,0x100020104900971,0x100020104900972,0x20c20120820d10,0x20c20120820d20,0xc0800104844a064,0x420088c4262241,0x20820120820920,0x8000140b0d04484,0x200040209201273,0x10010301a0c49065,0x223060309823140,0x22300e0f03a3150,0x22300e0f03a3170,0x104040b05124842,0x20400190c265043,0x204005128345043,0x2040031182c5043,0x606005128347043,0x844030380c4c281,0x221821308861960,0x40010280448271,0x22300e0f03a3140,0x42040281042251,0x221820120821930,0x22200e0b03a2160,0x1024005068164150,0x20820120820930,0x800042251885074,0x230060f01a3140,0x221860381821960,0x221821188861960,0x1828211888c2c32,0x220821188860960,0x48008240248251,0x42040281042231,0x500c21118c42c83,0x220060b01a2140,0x400021118c42473,0x40040241041271,0x8000140b0d04485,0x220060b01a2170,0x801040a45825053,0x102c0141a052c130,0x800840a25824853,0x800840a25824864,0x408008a2452a053,0x141840281041a61,0x141860381841a61,0x801040a25825064,0x40800522854a053,0xc0c00e23058e053,0x22021188862140,0x30102110c941972,0x221c21128861d20,0x410301c0941221,0x410301c0c41221,0x20860381820950,0x14022110c940b72,0x60e21128860f20,0x800004024904174,0x20860381820960,0x410301c0c41231,0x301030184d01972,0x221c301a0c21d20,0x180020104900d61,0x14280e0d03c2a41,0x2230050a8163140,0x22005228162160,0x420088c4262261,0x208001208249064,0x48008240248261,0x104040b05124853,0x102c0141a052c150,0x14200e0d03c2241,0x42040241042251,0x8000180d0e04473,0x41040281041251,0x41040281041261,0x208301a0c20930,0x8000140b0d04475,0x220140a0d221373,0x300830188e01a73,0x228130380e09163,0x182860381882c41,0xc03042251887074,0x22300e0b03a3140,0x506008944326842,0x42008a44262261,0x220050a8162160,0x102c00c12032c150,0x4800e0f03c8261,0x204042311285043,0x204040b05225054,0x506008944326852,0x102c0181c062c150,0x40000884c622264,0x22200e0b03a2140,0x2218301a0c21920,0x200040a0d221273,0x410422510c1231,0x208301a0c20920,0x20021128860970,0x200301a0c20970,0x506040b05126863,0x104042311184841,0x18084180c4e0c464,0x104000904124841,0x601460305c03463,0x400460305c02463,0x68108a44268350,0x108001a0c168852,0x104000904124842,0x400421118c42463,0x104000904124852,0x104042311184852,0x506042311186852,0x42040281042241,0x108008a44328862,0x204042311285053,0x108001a0c168862,0x601421118c43474,0x18084140b0d0c464,0x18084180d0e0c475,0x48010280448261,0x400421118c42464,0x104008944324852,0x18084180d0e0c464,0x40800120844a064,0x400421118c42474,0x208001208249063,0x601460311c03464,0x606042311287053,0x846040281046241,0x4200a0d02c2241,0x42040281042240,0x108008a44328863,0x108008a44328883,0x108008a44328873,0x102c00c16032c160,0x506008904326853,0x60140a45061381,0x400021118c42494,0x506000904126863,0x61140281041371,0x40800120844a075,0x22060381822140,0x104042311184853,0x22021188862150,0x102c0141a052c160,0x104042311184863,0x104040b05124863,0x48008240248271,0x208001208249074,0x506000904126852,0x2830211888c3441,0x40800a25068a064,0x108001a0c168863,0x506000904126853,0x820211888c2442,0x410301c0c41241,0x82060381882452,0x108030380d08873,0x283060309883471,0x208030380e09064,0x2830211888c3492,0x2830211888c3452,0x283060381883482,0x2830213088c3492,0x283060381883452,0x820211888c2452,0x240141a0524160,0x2830211888c3442,0x1001001049049086,0x108001a0c168853,0x100200108904a086,0x1000008049208296,0x283060381883441,0x108001a0c168873,0x221860321821930,0x200040209201293,0x840141a0584452,0x400060311c02494,0x840141a0584462,0x506040905126863,0x221860320821930,0x108c0141a058c452,0x6810a0d02c8381,0x204040b05225064,0x846040281046251,0x506008944326863,0x4200a0d02c2251,0x82060381882442,0x60a21128860b10,0x208030380e09063,0x2200e0f03a2140,0x60a21128860b70,0x606040b05227053,0x60a21128860b20,0x1828211888c2c42,0x102c01412052c150,0x102c00412012c150,0x800004024904195,0x8000140b0d04495,0x1828211888c2c52,0x102c00412012c160,0x22300e0f03a3190,0x408008a4462a064,0x223060381823140,0x22060381822150,0x220060b01a2150,0x240181c0624150,0x240181c0624160,0x223060309823160,0x204040b05225053,0x204005128345053,0x221821308861980,0x102c00506816c180,0x844030380c4c291,0x221860121821930,0x22300e0f03a3160,0x42040281042281,0x223060381823170,0x800840a25824895,0x24004120124140,0x223021188863150,0x20821308860970,0x2400c160324160,0x20400190c265054,0x20400190c265064,0x20860321820930,0x204005128345054,0x204005128345094,0x204005128345064,0x2040031182c5054,0x20020120820990,0x204042311285064,0x64204160124350,0x642060b01a4380,0x14280e0f03c2a51,0x64204220124380,0x220050a8162150,0x141840241041a41,0x506040b05126873,0x221821188861980,0x1828213088c2c92,0x24004120124150,0x1828213088c2c82,0x1828211888c2c41,0x500c21118c42c94,0x223005228163180,0x506000914126852,0x844060381846291,0x500821118c42c84,0x506040311106852,0x606001118247053,0x100020104900992,0x2230060b01a3150,0x2040031182c5064,0x606005128347064,0x14280e0d03c2a31,0x221860381821970,0x800840a25824875,0x22300e0b03a3130,0x141840281041a71,0x801040a45825075,0x220050a8162140,0x2218301a0c21930,0x24004120124160,0x14280e0f03c2a91,0x3838211888c3c52,0x180602118984e076,0x14280e0f03c2a81,0x102c00c16032c150,0x800004024904185,0x383860381883c52,0x144240b05124a63,0x1418301c0c41a31,0x2230050a8163190,0x2230050a8163150,0x223060381823150,0x41040a45061230,0x400006034582184,0x420088c4262251,0x2200e0f03a2150,0x1418301c0c41a41,0x141840241041a71,0x142840281042a51,0x108c0181c068c452,0x22300e0f03a3180,0x228130380e09174,0x8000180d0e04485,0x1000008049208286,0x606040b05227064,0x40000a058682284,0x40000884c622284,0xc0c008a4462e075,0x68110280448371,0xc0c00e27078e075,0x41042a550e1231,0x41040a45061241,0x50600190c166863,0x60a21128860b30,0x61140a45061341,0x108c0181c068c462,0x68108a44268371,0x64205128164360,0x208005228349074,0x24005128164160]
def g255Mark (j : Nat) := g255Labels[packedAt g255MarkBits (9*j) 9]?.getD 0
def g255Y : Array (Bits × Bits) := #[((samplePairHigh 0x7c1f07c01c 0x200802403f30339eb9ed),(samplePairHigh 0xe1305400c 0x200800401a10129ea8ad)),((samplePairHigh 0x60f80060 0x428e0d99b04ace1a6799),(samplePairHigh 0x944548c020 0x220599a0080a0a6398)),((samplePairHigh 0x18380000180 0x1001c08d0847b9ff),(samplePairHigh 0x18e931fc080 0x840446b9ff)),((samplePairHigh 0x7c202 0x84f0601e008e0da55fd2),(samplePairHigh 0x180a03a8002 0x80b02008008e0d215752)),((samplePairHigh 0xf80c03 0x70181e000f00e399e27),(samplePairHigh 0x108a2330003 0x400804000e004319c07)),((samplePairHigh 0x3ff003003 0xf801fe0000fff041e000),(samplePairHigh 0x2128a01003 0x9001fa000063e1010000)),((samplePairHigh 0x1fc00003ffc 0x1ffffff000000000a),(samplePairHigh 0x714cc03b70 0x15f35640080000000)),((samplePairHigh 0x3fff 0xfffe00000000007e0034),(samplePairHigh 0x4210042fd8 0x634c0000080000440020)),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12),(1,0,254,0,11),(8,0,247,0,11),(16,0,239,0,11),(32,0,223,0,11),(2,0,253,0,11),(9,0,246,0,10),(12,0,243,0,10),(64,0,191,0,11),(128,0,127,0,11),(0,4,155,96,9),(5,0,250,0,9),(6,0,249,0,9),(17,0,238,0,9),(18,0,237,0,9),(20,0,235,0,9),(36,0,219,0,9),(68,0,187,0,9),(132,0,123,0,9),(0,2,77,176,8),(0,64,162,29,8),(3,0,252,0,8),(10,0,245,0,8),(24,0,231,0,8),(32,4,155,64,8),(33,0,222,0,8),(34,0,221,0,8),(40,0,215,0,8),(48,0,207,0,8),(64,4,155,32,8),(65,0,190,0,8),(72,0,183,0,8),(80,0,175,0,8),(129,0,126,0,8),(130,0,125,0,8),(136,0,119,0,8),(144,0,111,0,8),(160,0,95,0,8),(0,1,146,104,7),(0,8,54,193,7),(0,16,45,194,7),(1,4,154,96,7),(1,64,162,28,7),(4,1,146,104,7),(4,2,73,176,7),(4,64,162,25,7),(8,64,162,21,7),(16,2,77,160,7),(16,64,162,13,7),(19,0,236,0,7),(21,0,234,0,7),(32,2,77,144,7),(52,0,203,0,7),(66,0,189,0,7),(96,0,155,0,7),(96,4,155,0,7),(128,2,77,48,7),(148,0,107,0,7),(192,0,63,0,7),(1,8,54,192,6),(2,4,153,96,6),(2,16,45,192,6),(5,64,162,24,6),(8,1,146,96,6),(9,4,146,96,6),(12,1,146,96,6),(12,64,162,17,6),(16,4,139,96,6),(17,64,162,12,6),(20,64,162,9,6),(24,64,162,5,6),(32,1,146,72,6),(36,1,146,72,6),(37,0,218,0,6),(48,2,77,128,6),(50,0,205,0,6),(64,1,146,40,6),(64,8,54,129,6),(64,16,45,130,6),(68,1,146,40,6),(69,0,186,0,6),(81,0,174,0,6),(88,0,167,0,6),(128,8,54,65,6),(128,16,45,66,6),(134,0,121,0,6),(144,2,77,32,6),(146,0,109,0,6),(160,2,77,16,6),(162,0,93,0,6),(26,0,229,0,5),(35,0,220,0,5),(40,1,146,64,5),(41,4,146,64,5),(42,0,213,0,5),(44,1,146,64,5),(49,0,206,0,5),(66,16,45,128,5),(74,0,181,0,5),(82,0,173,0,5),(85,0,170,0,5),(96,1,146,8,5),(97,0,154,0,5),(97,4,154,0,5),(100,1,146,8,5),(130,16,45,64,5),(131,0,124,0,5),(133,0,122,0,5),(138,0,117,0,5),(145,0,110,0,5),(152,0,103,0,5),(161,0,94,0,5),(168,0,87,0,5),(176,0,77,0,5),(176,2,77,0,5),(178,0,77,0,5),(192,8,54,1,5),(192,16,45,2,5),(200,0,55,0,5),(208,0,47,0,5),(104,1,146,0,4),(104,4,146,0,4),(112,4,139,0,4),(193,8,54,0,4),(194,16,45,0,4),(210,0,45,0,4)]
def g255A : List (List Nat) := [[]]
def g255D7 := limbs80 #[#[0x5d541481655d17150520,0x481745c54154120ec5a9,0x55141581206c1755c551,0x58120551715056048165,0x5d57150560481745c541,0x54560481745c55158120,0x481a759554581205d571,0x55171581205957455160,0x58120e95655c56048174,0x6d6a95d560483b56a575,0x5d570483b7695415c120,0x483b5699755c120ec5a4,0x595745c541ec59464175,0x61954ec9a65d571547b2,0xec99624587553b161f92,0x24587553b46589161d54,0x553b265b9161d54ee996,0x61b9161175ec9a6e4587,0x9da675a9d664f993b7b2,0x3e6f98bda2f58b9a6b9a,0x6355ad3a7378c7e317ac,0x3d58ee2bb68ed6378add,0xf88fd23f28fc2bd8af5a,0xccb0b4b28b2b29b6b297,0xdca990e3974ba96dcb0a,0xfcb924d29d1e29a6d29a,0x5d224ee2a34aa228d392,0xb2b2b64a6ae4a4fe226,0xeb8b93e0aa3d8acae237,0xad3457cb416cb41eb8bd,0xdb0d8b004de4006e249,0x8e0519d34d8d34cfe30e],#[0xc90602e05d4d0584e054,0x2e06c2e069490640e1e1,0x71789c3e17058002e070,0xe773799cbe572791c7e3,0xd7eb757a9d3e9747a1cf,0xc1dfef777b9dbed767b1,0xa7d1e7f3797c9e3f1787,0x400a30619c705d9ebf57,0xa0]]
set_option maxRecDepth 32000 in
def g255D8 := limbs80 #[#[0xea165505205955450520,0x59571505205517150520,0x5d571505205d17150520,0x65574505205957450520,0xe9d95505206a57550520,0x5954154120e959750520,0x5d141541205c54154120,0xe5941541206594154120,0x69d61541205956154120,0x5d171541205d96554120,0xe857454120e917154120,0x5d954545205d15454520,0x55171545205d96454520,0x5d571545205917154520,0x6817554520e517154520,0xe5d76545206817654520,0xe85745512065d6555120,0x28597551206817555120,0x5d39155120e859755120,0x59541581205514158120,0x5d141581205c54158120,0x65d41581205d54158120,0x69d41581206954158120,0xe5d4158120e554158120,0x5c551581205515158120,0x69d51581205d55158120,0xe9d5158120e915158120,0x5d154581205955458120,0x69d54581205d55458120,0xe9d5458120e855458120,0x59571581205517158120,0x5d571581205d17158120],#[0xe957158120e917158120,0xe957458120e857458120,0x69175581206857558120,0xaa575581206a57558120,0xe917558120e857558120,0x6817559120e957658520,0x595415c120551415c120,0x5d9415c1205d5415c120,0x699415c120695415c120,0x551515c120e59415c120,0x5d5515c120591515c120,0x5d5545c120e91515c120,0x5d9615c120e85545c120,0x5d5645c120e95615c120,0xe95645c120e85645c120,0x691755c120685755c120,0xe85765c120699755c120,0xe9d855c120e95765c120,0x5d1545c520e8d965c120,0xea1655c520e55655c520,0x681755c520595745c520,0xe85955d120ea1655d120,0xe91985d120e91965d120,0x651905d520645905d520,0xe85945d520659905d520,0xe45905d920e95965d520,0x683955d920e55905d920,0xe819654d31e896554d31,0xe958759531e899654d31,0x5d96454540595535c531,0x5d571545405917154540,0x59554581405c55158140],#[0xe819654d41e917158140,0xe896555141e899654d41,0x5d97458d41e899655141,0xe958759541e557458d41,0x5d1535c5416839259541,0x5d1635c541595545c541,0xe89655c5415d5635c541,0xe89655d141595745c541,0xe5d7661541e85985d541,0x6917554d435d56454d43,0x5d55458d4368d7555143,0x6917558d43e557458d43,0xe95645cd4368d7559143,0x285985d543651935d543,0xe919661d43e8d9661d43,0xe8986505505d17150550,0xe89865d150e89865c550,0x5d16350d51e1d5450d51,0x5917350d515d96350d51,0xe917655151e5f8750d51,0x5d97458d51e899655151,0xe8d7658d51e1d7658d51,0x551435c551e1d7659151,0x591435c55158d435c551,0xe11435c5515d5435c551,0x5d5635c5515d1635c551,0x681755c5515d5645c551,0x699755c55168d755c551,0xe9176e1151e89965d551,0xe81865cd535d79359153,0x597915cd53e89865cd53,0xe89865d153e81865d153],#[0xe89865d553e81865d553,0xe89965d553e85945d553,0x68f985d953e8d965d553,0xe898660553e818660553,0xe898661153e818661153,0xe4b906195361f9061953,0xe819661d5361f9261953,0xe8d9661d53e899661d53,0xe89865d154e858759554,0x597915d154e95965d154,0xe89965d554e89865d554,0x693985d954e91965d554,0xe858761954e898660554,0x683926195461f9261954,0x6589161d5464c9161d54,0xe899661d542459061d54,0xe959661d54e919661d54,0x69b9161d5465b9161d54,0x61d54505605955450560,0x5d171505605517150560,0xe8d87505605d57150560,0x5d1715456061d5454560,0xe8d87545605d57154560,0x595745516065d6555160,0x5d1545c560e8d8755160,0xe89655c560e55655c560,0xe8d985d560e53845c560,0x696985d560e95985d560,0xe81985d5635d97455163,0xe9d985d563e95985d563,0x69e985d563696985d563,0xe9d985d564e95985d564],#[0x69e985d564696985d564,0xe8193e0965e8183e0965,0xe85945d570e9d9550570,0xe95965d570e89965d570,0x5d15350d715915350d71,0x5d16350d71e115350d71,0x5957450d71e116350d71,0xe899654d71e819654d71,0xe8996551715957455171,0x6839259571e538458d71,0xe89655d171e179259571,0xe89965d571e91965d171,0xe8965e1171e95965d571,0xe8d8661573e9165e1171,0x5db9161574e918661574,0xe8965e057461b9161574,0xe898660175e858460175,0xe858460d75e898660575,0xe898661175e898660d75,0xe57926197561b9161175,0xe179360176e4f8160176,0xe5df1fb8fcc7de3df0fd,0xf9bdcdea6df35f97dcbd,0xe27dd3eb9f54f6e7af3c,0xefa76d1fe8fb3fa9fccf,0x5ee9fd4fda7dd3e69ef4,0x63fafd57e2bb75daacfd,0x5be6dd76e7b6ddb5ecf7,0xf75dbad5d66e9b73ab7d,0xd5deaef176dbb5dda6ec,0xd57dabecdf2ef8f79dbc,0x7de3df1df87fc3edfe2f],#[0x3b797ecbee5ef1fd8fdc,0xcfb67cf3dd9ebcf3e777,0xf4efa6fd2fe7f33f59f9,0xed6deb5f59fa9fd3f69e,0xeb5f3af6d79ebaf5cfad,0x5bdad6d5f69fb3ad93eb,0xde76dbb6bdb3ed7b6bbb,0xbc7ddd6ebb735b8fdbd6,0x6fcb7d5bdadecef4f797,0xfd27e7d73e789fc3fdfc,0xef56fab3d57e9ef4efa5,0x1fd8eebd75b7ad7d69ea,0xe9f72fb8fdbaecdf66bb,0xc6fe2ff0ff7e3bd5ddae,0xf63fa3fcf5e6df2ef937,0xfe75f2df93fc3fda7ecb,0x8faafd37e97f4afa4fd1,0xa7ed1f65fae7d6beb3f5,0xaafcd7e37f15f78fb57d,0xfa3fb1fd1fe57f27f71f,0xfed022e3d3842c574067,0xab289ac574141bf62120,0x5651bb8f4a3dac5d4636,0x76a4612ec4731dcb8dad,0x6949d50ba93081b52390,0xba9582bb7288576e5067,0x752c1676a59645d8b4ce,0x625f645d8bac8bb1719d,0xdc054eba808bfb5301af,0xa814cbb5024432a04326,0x70cd3ae81903ec4110ac,0x81bac6c0370aba870b9b],#[0x91d19cb9fc8bb1379776,0x2de69755896b6ead32ec,0x4cc02ec967de5d445dd9,0xde1aec5b47fd3a6d8d76,0xba01dd37057b76e00574,0x8803ba6e8bf68dd1aec9,0x68d765261aec9c635d93,0x8b9594517caa0a2cd760,0xd2acb89aed75135a2ea2,0x6439713dc2ca2995e5c4,0x4a32e30bb5d06168ba0c,0xb75947966ba0f2539718,0x76b2932dda71b52aca3e,0xc98602592ca04ba59405,0x4aca65a95d82d5aba86a,0xa5d4f95eba9f8f3b6115,0x8b2b9ed96573552ca9ea,0x7a545d52ca89a2595e34,0xaeca3aa5d55f56baab9b,0x658197ab2831afa585d1,0xcb036ed6506cb72c0c96,0xa7073c34e0b95e581b2a,0x6e0f5169c1e47db83945,0x582716cb04eb9650991b,0xb05145960a3c2ca148be,0x60aa8b2c15785942aa3c,0xe267b694512dca8a1479,0x4527bdb898f5b7133cb4,0x89cf7b514bcb4a2995e5,0x170a3742a7869454e6d3,0x2c5165c5846db8b945a7,0x5e47da8ac53b71628f2e],#[0xc6f554188a76a2d236d4,0x83c74e307869c60f7d20,0x4785d46879db8c0f1b71,0x428db8d147971a28b2e3,0xe52b9194a372323ced06,0x572ea3c146d06a29da0c,0x36ed47d17ca8f8d9b71e,0x28da90147952039aca40,0x2eb91fc5b723f36ed07e,0xc2ea3a795d07428da106,0x46dc74a3cb8e945971d3,0x9d88e2dda11b1ef62371,0xbb11cca57238946e4707,0x762397bec472f6588e4f,0xe5484e6b290851b11d8a,0xd491051b1218a36a4251,0xb1228a3684851aa488a2,0x624951aa48aa2d4914fb,0xe09b2bcb132cd76260a3,0xa93d47962837aec502be,0x629d72ec53236d4a46dd,0xc56a55d8a95cba952539,0x8b15cdb15547962b37ae,0x15eb9a62ba8f2c586f5d,0x2f37d745b6f6e8b75cdb,0x6036ed0c0ded317dbda6,0xc2dea098e74b8305776a,0x89bdb1311b36262366d4,0x25930a047a504c8deda1,0x2aee00764dc012c9b60,0x312bb01ca7b8034932e0,0xd256505232ec094365c0],#[0x4372e173aed02f5adb06,0x3ced83af0d30760b970c,0xe6d812879b40fc5f2e1e,0xf943390b686625ee0d0,0x4aec2536ed8d2ded31a5,0x86984477d8881d56510c,0xd309141a611a832c247,0x6a925a8b524b506d848a,0x2ec6b7b580d687c89a94,0x5c4d8f2a81b1419635b7,0xd31b9b17136a632a6c6c,0xb53811f687051e98dea3,0xe27250658e2fe5c1c253,0xc4e846da9cc39b439342,0x9d545a43aa8b4275236,0x63e88b6a807259500a2a,0xc9e9c6193d03cb9ee6d8,0xd3ebcba27d85714fce70,0xa850f94502b2e8a04365,0x739a36ee6aa5d5cc87c8,0xe834ed5cf14cab9e7385,0xcb1acbb927b877243b2a,0xaea95475a132ae928ecd,0x643f28ec9be11d860dab,0xa9bae1d936dc3b0c3b47,0x630dabd10b947693766e,0x9c3a1778fb68f28fe55e,0xad2a2f542e45e071d8bb,0x5a551ea84c8bd555717a,0xa6b8bdd4d717b21328f5,0x1d9682a070d044061a08,0x436907685520cd0a8c19],#[0x1e1ced42c39daf3b23d0,0x7c91e57f843c3070877a,0x18545b6f4c896d69912b,0x2a88c34ed51668daa2e7,0xec11d75d922a6d854655,0xd8234d3b347597648e34,0x8740a6ae881525c50226,0xe824c5d104a0b8a0915,0x1d0730c2a1605764321b,0x3a2041b0478836084a06,0x482df2487585810e86c,0x8ae7c58d2288b1a41116,0x164d3d32c1a5a658582e,0x2ce6f84599836ab2aa55,0x59b4b74b330ed166d3d2,0xb569e8d68d3d02d1a6ba,0x6cd2d32d8c3b65ab4b4c,0xdeb7b25b98760b730ed9,0x351aeca599e1d4861d9a,0xa99e1d5744aa2a459b65,0x4f9ca2a9f194554baa8a,0x39b05406366a7246d15,0xcc748ac7ce4d5930a1ab,0xe6c1700ad9ae579205c,0xd6d3426996584d32eb08,0x75a6854facb0a6be9a12,0xef4b0c31ed616bbd3429,0x1eca1c67d9434a1b5862,0xcba43d178487242e90e5,0x7b28820b4b1243e121e8,0xb67160b6c22a08d8446a,0x50e320ed846579408c84],#[0xc2c4c15b38d02b611a5e,0xb08b93b6914276ce28b7,0x7492086ce30d0a9c5c2d,0xe52ae8d324dd2ba493a3,0x4a5d2da94bc8d7295916,0x94c1cf6c947469928975,0xa9c4be99349754a612da,0x18e8bca31907954ea172,0x2ed3f915dc9f64bd43e5,0x5d27728bc4ee45789fca,0xc843e457e8bc8afa1171,0x8094cb3090f9164a2f22,0xdd94361b42e2c16a5c5,0x286b68c4665c588b6c23,0xc1ded1943bd8b280bb46,0xafeb8b2c6fb4660df62c,0x90f916722f28cd45e459,0xc0f22f8066d19e87ca33,0x45645f2aeb8be571517c,0xa6b8be915947cae2a8f9,0x55437da9aa2fb5a50df4,0x9aa2fd535c5f8a6aa3ed,0x66d236a6aa3f555437ea,0xd83464bb26983b60d80,0x1706a3bf24d075481a42,0x360d575501aa1cd8351a,0x5c1acea90359d5436a87,0xd9b5d31206b86366d665,0x936ca2720d94361db603,0x60e21cecdba39d837513,0xcdc639d838c73b3710e7,0x9b8179207003b60df1ce],#[0x7f2da40fe5b481c20ad,0x6ff5450dfeb2a1bf94d7,0x202a6b84016d208029aa,0x47d4d5380aa287015648,0x8f41ac71d4364e3e0ed8,0x2056ce3839d9c7873b0,0x4088cb481897181b12e3,0x8c1db09121f292144e5a,0x22fa872444e5a4688cb4,0x61cec24c87ca4910d949,0xa0ed849473b3933f7652,0xd25a093c32e1275e50e4,0x10b6927216ce4f0cb8c9,0xb000032d8ca509a594,0xc10807082e812a073028,0x507b839c1a90c4857026,0xc62bf14b09c44a022f10,0xec8f0873036a19c0c345,0x99049c23b915885c4031,0x2de1640ad653b28813b0,0x4d5067432998b4c105dc,0xb39b1c80e146f23711b3,0x28f6e7a93cd9e34ef275,0x2240a9fdcfde7e73eb1f,0x23910286b431a16d0868,0x92648623c91988bb44d2,0xa6a53289774b0a565282,0xca2d510a82d3fe9e14e0,0x7ab9d5b0aa9544a97549,0x3eb17587ac1d5feaf757,0xa7ad1d67eb37597ac9d6,0x6feb775b7ad9d6beb575],#[0x5d7ae9d73eb975c7ae1d,0xd7bebd75e7af1d77ebb7,0x7607b01d7febf75f7af9,0x1d87ec37617b09d83ec1,0x77637b19d8bec57627b1,0x29d93ec97647b21d8fec,0xcd7667b31d97ecb7657b,0xb41d9fecf7677b39d9be,0xed37697b49da3ed17687,0x7b59dabed576a7b51da7,0x3ed976c7b61dafed776b,0xe7b71db7edb76d7b69db,0xbfedf76f7b79dbbedd76,0x717b89dc3ee17707b81d,0xdcbee57727b91dc7ee37,0x7747ba1dcfee77737b99,0x1dd7eeb7757ba9dd3ee9,0xf7777bb9ddbeed7767bb,0xc9de3ef17787bc1ddfee,0xf577a7bd1de7ef37797b,0xbe1defef777b7bd9debe,0xefb77d7be9df3ef977c7,0x7bf9dfbefd77e7bf1df7,0x3f017807c01dffeff77f,0x27c11e07f037817c09e0,0xff077837c19e0bf0578,0x857c29e13f097847c21e,0xe1bf0d7867c31e17f0b7,0x7887c41e1ff0f7877c39,0x1e27f137897c49e23f11,0x778b7c59e2bf1578a7c5,0x69e33f1978c7c61e2ff1],#[0x1d78e7c71e37f1b78d7c,0xc81e3ff1f78f7c79e3bf,0xf237917c89e43f217907,0x7c99e4bf257927c91e47,0x3f297947ca1e4ff27793,0x67cb1e57f2b7957ca9e5,0x5ff2f7977cb9e5bf2d79,0x997cc9e63f317987cc1e,0xe6bf3579a7cd1e67f337,0x79c7ce1e6ff3779b7cd9,0x1e77f3b79d7ce9e73f39,0xf79f7cf9e7bf3d79e7cf,0x9e83f417a07d01e7ff3,0x457a27d11e87f437a17d,0xd21e8ff477a37d19e8bf,0xf4b7a57d29e93f497a47,0x7d39e9bf4d7a67d31e97,0x3f517a87d41e9ff4f7a7,0xa7d51ea7f537a97d49ea,0xaff577ab7d59eabf557a,0xad7d69eb3f597ac7d61e,0xebbf5d7ae7d71eb7f5b7,0x7b07d81ebff5f7af7d79,0x1ec7f637b17d89ec3f61,0x77b37d99ecbf657b27d9,0xa9ed3f697b47da1ecff6,0x6d7b67db1ed7f6b7b57d,0xdc1edff6f7b77db9edbf,0xf737b97dc9ee3f717b87,0x7dd9eebf757ba7dd1ee7,0x3f797bc7de1eeff777bb,0xe7df1ef7f7b7bd7de9ef],#[0xfff7f7bf7df9efbf7d7b,0xc17e09f03f817c07e01e,0xf0bf857c27e11f07f837,0x7c47e21f0ff877c37e19,0x1f17f8b7c57e29f13f89,0xf7c77e39f1bf8d7c67e3,0x49f23f917c87e41f1ff8,0x584e7833058227807036,0x10cc286c6c2fc00ce70,0x52fc15058585c4cc1852,0x24c70c700cc4198c3858,0x1ec17f80e42dc1ec4ac,0x850c4f442850c1d01a95,0x5dc20cd28c6c23c4d856,0x4058d05c2d8c5c40ca00,0x3081874184d3c2610851,0x53410145c320b83aec30,0x2d11856c4459b02380b1,0x52b10b8c10f48c11b00f,0x4a4985d45245285c0152,0x6833c184738307906c84,0x2e07519a1780e60ce80,0xd702c2c88c43912cf099,0xe0c01181701210ff4348,0xd2bc2cd16c1cc4f81ec0,0x9ac12425808c2701b888,0x84ba8a78258d4c14c421,0xca08a297f70c402b320f,0xeff4511933f0d02320eb,0x65c63d0468c075ea0245,0xde98605b32dce2a104,0x2fec3a10b36f8dd0088c],#[0xc8ab1b3c1454e1a04640,0xc64048b3c89c89d02e02,0x526f286b20047c11937e,0x907fe4c8328dbce36044,0x4606e9fc04595bff0825,0xdc0a3da15b3813fe9619,0x84806428372f5d008cc0,0x775ae88a94779ae098e6,0x5f0a142ca15d3f422d9,0x23ee0c7a0d173f484cc8,0xc25f770d49349fd8ee46,0x99800f28231c2d3ba416,0x2800ad9c6101bfa40326,0xc281060cd184797fc013,0x847603786c2019809e08,0x1b3805fc060c00033f4,0x8207bd70142057d93e7c,0x12bc9050607458383ad1,0x704060c5e9da4909c83c,0xa18ab61ad86b61ec3626,0x745920c00027a85a835,0x4f1289dfb8c307b41,0xf98c307a8396127e2080,0x888860c7ba2a424f50b5,0xbd8a249468c71cd231af,0x7b416be2920f93682000,0x19483036fe9a3032ea29,0x9894a3b21c6ca0ac845d,0x9a3a760b1f0885270206,0x9c0800000bfc885da47e]]
def g255H8 := limbs80 #[#[0xa30000400b010001334,0x1e17d00000000000000,0x87ca00ea00004400000,0xd3649200c9ec002b0,0x4e000000450200540,0x43000000000000000,0x4b9a001d46000000000,0x910000000000000,0xe600a000219c0f00000,0xcc0058d9a9a595000,0x8004d5fa7db002200410,0x56c80000e]]
set_option maxRecDepth 32000 in
def g255D9 := limbs80 #[#[0x50110585404415150110,0x44165541105855044164,0x659544417554510e5150,0x5c110e49654419759510,0x441645c1105857044151,0x66176443945c110e1170,0xe11105d985443955d910,0x48195e19105db8444165,0x59541481615052055141,0x505205d1414817150520,0x48185505205d94148175,0x65541481875052061941,0x5412065d414819650520,0x48164541205855048141,0x5d150481715412059550,0x54120645504817654120,0x48197541206595048194,0x551514839754120e5950,0x545205c5514816454520,0x48176545205d55148174,0xe5151481975452065951,0x55120e5d514839654520,0x48175551205d15448165,0x6595448191551205d954,0x55120e45544819755120,0x4814158120e5d5448396,0x59560481545812054560,0x581205d1604817158120,0x48197581206456048175,0x551614839758120e5560,0x58520595614816458520,0x48176585205d56148174],#[0xe5d61483955852065d61,0x591205d9644817559120,0x4839559120e456448197,0x65d654817659520e5d64,0x5c12054570481415c120,0x481645c1205857048154,0x5d970481755c12059570,0x5c12061570481815c120,0x481945c1206457048186,0xe5570481965c12065570,0x5c52055171483965c120,0x481745c5205957148164,0x61571481845c5205d571,0x5c52065971481865c520,0x483955c520e517148198,0x5d974481655d120e5971,0x5d12064574481855d120,0x481985d1206597448195,0xe5974483955d120e4574,0x5d52064575481905d520,0x483915d5206597548194,0x64176483965d520e5175,0x5d920e5176483915d920,0x48394605205d18148395,0xe51854839161520e5d81,0x61920e45864839761520,0x4c79461d20e458748397,0x595434c56450d3155143,0x50d315d9434c57450d31,0x4c56554d31e19434c785,0xe11534c59654d3161153,0x55131611544c79454d31],#[0x4c78655131661544c596,0x5cd614c5535853150d61,0x5953165d654c58759531,0x4c5435c531e49654c598,0x5d1714c5655c53154d71,0x5cd31591734c5755c531,0x4c5855cd31611734c565,0xe15734c7845cd3165973,0x5d131611744c7945cd31,0x4c5985d931e19754c786,0x5d9854c7966113159584,0xe1131e59874c79661531,0x4c595e19315db844c565,0x59151501545454065f86,0x545405d5515017154540,0x50197545406195150176,0x65d5450196551405d554,0x58140551605015158140,0x50175581405c56050165,0x5d964501755914059161,0x5c140661655039559140,0x501615c1405517050151,0x55171503915c14059170,0x5c54059571501645c540,0x503945c5406197150175,0xe4575501985d54061975,0x54d41e5d86501985d940,0x5057454d415cd5350565,0x659535058654d415d953,0x55141e59535059854d41,0x50554585416595450565,0x5d1635055458d415d161],#[0x58d41615635057558d41,0x5079558d4165d6350587,0x65d655058759541e5d63,0x59541e49655079059541,0x505535c541e5d6550793,0x59571505635c54155171,0x5cd415d571505745c541,0x505855cd415957350554,0xe5973505985cd4161973,0x5d54161574505655d141,0x507955d9416617650598,0x5915350d7661541e6176,0x54d435d15350d6554d43,0x50d8754d435d95350d75,0x65d5350d9654d4364553,0x55143e595350f9154d43,0x50d76551435d55450d65,0x65d5450d965514361d54,0x58d435516350f9655143,0x50d8758d435d56350d74,0xe5d6350f9558d4365d63,0x591435d96450d7559143,0x50f955914365d6450d87,0x6616550d8559543e5d64,0x59543e456550f8659543,0x50d545cd43e5d6550f92,0x6157350d655cd4359173,0x5cd436557350d915cd43,0x50f955cd43e457350d96,0x5d97450d655d143e5973,0x5d1436557450d855d143,0x50f965d143e557450d96],#[0x64d7550d865d54361575,0x5d5436617550d945d543,0x50f915d543e197550e98,0x61d7650d865d943e6175,0x5d943e457650d985d943,0x50d546054354d8150f95,0x5cd8150d646054358d81,0x605436158150d7460543,0x50d8761543e558150d87,0x65d8550d966154364585,0x6194361d8650f9661543,0x50d9161d43e5d8650f95,0xe558750d9661d4365587,0xe19436578650f9661d43,0x54171505505954154197,0xe194154186505505d141,0x5855065d615416558550,0x541415c1505d96554398,0x59570541645c15058570,0x5c150e0570541765c150,0x541655c550e457054384,0xe5171541865c5505d171,0x5d15066174541865d150,0x541985d950e457454298,0xe5d865439261950e6176,0x50d515514354597e1950,0x5457350d515914354563,0x5d9435457550d515d143,0x50d51659435458750d51,0x5469850d516614354597,0xe59435478750d51e1143,0x551515d1545479750d51],#[0x5455458d516595454576,0x5d9635457558d515d163,0x58d5165d635458758d51,0x5479458d51e1d6354784,0x65d645457659151e5d63,0x59151e4d645479059151,0x545545c55150d7154797,0x5d571545645c55158d71,0x5c551e1171547835c551,0x545645cd515517354790,0x66173545865cd515d973,0x5cd51e1173546985cd51,0x547965cd51e517354786,0x64d75545905d5515d974,0x5d95164176545965d551,0x547875d9516617654593,0xe5176547935d951e4176,0xe0d51e4986547985d951,0x54d75591535db8454596,0xe456454d985915365d64,0x59153e5d6454f9359153,0x54d87595535d96554f98,0x5d97354d655cd5359173,0x5cd536197354d845cd53,0x54d965cd536517354d91,0xe517354f915cd53e1173,0x5d15364d7454d865d153,0x54f865d153a617454d98,0xe617454f965d153e4574,0x5d5536457554d865d553,0x54d985d9536597554d94,0xe617654f935d953e4576],#[0x605535d58154d7360553,0x54f946055361d8154d86,0x61d8454d86611535d584,0x6195361d8654f9161153,0x54f9261953e458654f90,0x6458754f9761953e5186,0x61d536598754d9461d53,0x54d73e0553e518754f91,0x5d78454d65e115365b81,0xe1d5365f8654d96e1153,0x553925955461d6555196,0x61974551765d15459574,0x5d15464d74551905d154,0x553935d154e457455196,0x64d75551905d55461975,0x5d95466176551965d554,0x5517460154e617655394,0x61d8055186601545d580,0x60d54619815516560554,0x5518660d545d58355174,0xe4186551876195461d83,0x61954e49865539161954,0x5509161d54e5d8655393,0x659875519361d5464187,0xe05545d3815539161d54,0x55196e055464f8155190,0x65b8355174e0d5459783,0x50560595415815450560,0x58175505605d14158171,0x65d41581955056061d41,0x54560e1d415838550560,0x58175545605c55158154],#[0xe1151581975456061d51,0x54560e51515838754560,0x58174551605955458397,0x65d5458187551605d554,0x55160e1d545838455160,0x581545c560e5d5458391,0x5d571581745c56059571,0x5c560e1171581855c560,0x581985d160e557158394,0xe5574583915d160a6174,0x5d56065175581915d560,0x583915d560a617558198,0xe4d875839161d60e5175,0xe156065f8458175e1160,0x5855450d6154d4358597,0x5d1435857350d6159143,0x54d61595535878450d61,0x5858754d615d95358573,0xe0d535869854d6166153,0x5cd61e49655878454d61,0x586985cd616617358576,0xe4575587855cd61e1173,0xe016165380587955d961,0x58595e0d616538358597,0x65f8558594e156165f83,0x551636578758594e1d61,0x58d87551635d55458d74,0xa615458d985516365d54,0x55163e1d5458f8455163,0x58d765d163e5d5458f91,0xe157458e985d16366174,0x5d563e557458f915d163],#[0x58d985d5636517558d91,0xe517558f915d563a6175,0x60563e557658f915d963,0x58f9061563e558158f93,0xe458758f9261563e4585,0xe1163e558758f9361d63,0x58d97e11636578458d75,0x65f8558d94e15635db85,0x5d5646417559195e1d63,0x592985d5646617559193,0xe51875939161d64e4575,0xe01645d7805939561d64,0x59175e0d6464f8159197,0x5db8559197e0d6465783,0xe156464f8559191e1564,0x59595e1d646478759197,0xe49875979161d65e0981,0xe096564f8159594e0165,0x59584e096560f8259576,0x64f8259591e096561f82,0xe0d6565f8259594e0965,0x59591e1d6564f8459594,0x551415c194e1d6564f87,0x505705d5415c16550570,0x5c19650570655415c176,0x591515c15454570e1941,0x54570659515c17554570,0x5c17555170e51515c384,0x661545c1965517064154,0x58570e45545c29855170,0x5c39058570e11615c176,0x5d5645c39858570e5561],#[0x59570e55645c39159170,0x5c1945d570645755c390,0xe55765c3915d97065975,0xe0570e4d865c39061970,0x5c165e117065b815c165,0x65b855c196e117065784,0x50d7154d435c595e1970,0x5c56450d7158d435c554,0x5d5435c57450d7159543,0x50d71659435c59150d71,0x5c78450d71a61435c598,0x595535c56454d71e5543,0x54d715d5535c57454d71,0x5c59854d71659535c591,0xe19535c78454d71a6153,0x55171595545c79454d71,0x5c57458d71659545c574,0xe15635c78458d715d563,0x59171e41645c79458d71,0x5c59059571e55645c793,0xe49655c7855957164d65,0x5d171595745c79459571,0x5c5935d571641755c596,0xe45865c7966017165975,0xe117165b835c565e0d71,0x5cd92e197165b855c565,0x661545cd965517361154,0x55173e19545ce9855173,0x5cf9855173e59545cf91,0xe45645cd98591735d964,0x59573e61645cf9559173,0x5cf9259573e45655cd98],#[0xe55765cf915d973e6165,0x60573619815cd7660573,0x5cd8661173e55815cf94,0x619855cf9561173e4584,0x61973e51855cf9161573,0x5cf9561973e51865cf93,0x597845cd96e057359781,0xe197365b845cd95e1173,0x5d39259574661655d195,0x619805d18560174e6165,0x60d74615835d39560174,0x5d18661574e55835d186,0xe51865d39361974e4585,0xe0574597815d39561974,0x5d165e0d7465b815d193,0x611805d5816017565b83,0x60575e51805d58660175,0x5d58460d75619815d583,0xe59835d79460d7561983,0x61975e45845d58661175,0x5d79361975e49865d790,0x643815d79561975e5186,0x60176e05805d993e0575,0x5db9460576e4d805db85,0x60f815d994e0176e1583,0xe0576643815d985e0576,0x5d994e0d76647835d993,0x643855d993e117664384,0xe157664f855d991e1576,0x3fa3f63ee3de3be1fd94,0xe67de7be7ae77e5fe3fe,0xe9fe7fe7fa7f67ee7ea7],#[0xbf6beebeabdebbeb7eaf,0xbedb6d7ed76cfebfebfa,0xee7edfedf6deedeadded,0xf76f6ef5ef3eefeeeeeb,0xbefbafb6faef9ef7ef7a,0xefeafe6fdefdafcefcaf,0x3bf37f2ff1feffaff6fe,0xff3ff3fb3f73ef3eb3df,0x75ef5df5bf5b757f5774,0x6eb6df6bf67f5ff5fb5f,0x7b76f75f73f6ff6fb6ef,0xb7bf7bb7b77af79f77f7,0x7f77ef7eb7e77df7d77c,0xdf9bf9b797f9778ff7fb,0xfaefadfabfa7f9ff9fb9,0xb9fb7fb7bb6fb5fb3faf,0x3fbfbbf7befbdfbbfbb7,0x7cbfcbbcb7c9fc7bc5fc,0xd37cffcfbcf3cebcdfcd,0x6fd6bd67d5fd57d3fd3b,0x7d9fd97d7fd7bd77d73d,0xdebde7ddfdbfdb7dafda,0x57e3fe3be37dfbdf7def,0xfe97e7fe7be73e6be5fe,0xeefeebedfebfebbeb3e9,0x3bf37f33f2ff1fefbef7,0xff6bf67f5ff57f4ff3ff,0xfabfa7f9ff97f7bf77f6,0xebfe7fe3fd7fcffb7faf,0xed164006f954003ff3f,0xa397602e657502abd650,0x7a403c0ba303db18701],#[0x5a90a2b976096b96508c,0xa60b035a70b437a70ac3,0x711eb96511835a60b837,0x13035a7135579711d559,0x3837a51318fa3130d7a3,0x2357618e5d7518435a51,0x35761925d751888ba71a,0xfa819489a71963576196,0xa61bc8ba71a48ba61985,0x31b88ba71a88ba519c35,0xc67d7406035a51c0d7a,0x3033a110027a41565975,0x35a023835a023435a02,0x35a024835a024435a024,0x576396497538ea965364,0x7661c0ba33c013a13ba2,0x42b40ba3c3c0ba365219,0x2d22d762beb1652bac96,0xe1b9842de51752d67574,0x17a02c803a72adb1852,0x21763f6a5653f007a431,0xda743645754352d973f6,0x964407fa5441b9854407,0x446c13a1469b1854452f,0x6f1b175701257570807a,0xfdb17570475a76f24574,0xc0da076407a474c77a46,0x1d764c80fa0d1007a4d0,0x3a156417a04fe1d76516,0x9282817a07f215767981,0x687417a08690fa28290f,0xb6c0da08e413a18a6117],#[0x6c0da0b5c5fa0b7c5fa0,0x6d5760080ba3e7407a4e,0xef87012c176011716501,0x176039c5760363d76031,0xa404c63a20483ba201d4,0x70443ba2021138702457,0x8b49610881ba7050fb9,0x8b196508b357408b4971,0x8e9a60899f960899d960,0xe9a70899f970899d9708,0x17608ceba408ee16408c,0xa708d9f9708d9d9708ee,0x409a9574098eba708ce9,0x999d9609b1965098eba,0xa4eba40a4eba60999f96,0x2e176090eba1090eba70,0xe9a70919f970919d9709,0x96509ceba109ceba7090,0x9609d9d9609e957609f1,0x70a8eba10a8eba609d9f,0xb0eba40a0eba10a0eba,0xb19fa10b0eba40b0eba1,0x3355411349711119fa40,0x9f95112e165113357411,0xf971119d97110e9a5111,0x541174971114e9a71119,0x71171975114eba411719,0x114e9a71159f971159d9,0x20eba41229574120eba7,0x19f951229575122e1651,0xeba1118eba712ceba512,0xd9711b197511b3574118],#[0xa7118e9a71199f971199,0x5126e165124eba1124eb,0x128eba1128eba51259f9,0x319ea91299da9128eba4,0x349611819fa1130eba11,0x9f951829575183355418,0xf961829576180e9a5181,0xa41871954184e9a61819,0x61859f961869576184eb,0x18ee16418ceba6184e9a,0x8e957518ee16518ceba4,0xceba41a0eba518d9f951,0x1965188eba1188eba41a,0x9a61899f9618a957618b,0x75190eba1190eba6188e,0x11b0eba51919f9519295,0x19a95a419a95a1198eba,0xb4eba41a4eba11a695a6,0xe97a119ceba41b4eba11,0xeba41a8eba11aa97a519,0x154058eba41b8eba11b8,0x54060e7a705b317405b3,0x50559995062917506331,0x557d97056f575056f56,0x657d95064c7a7054c5a7,0x863a805e8176064c7a50,0x3ba707c39a90696d9506,0xba70803ba50803ba906c,0x540c43ba50843ba90783,0x40bd9b940c691740c715,0xbd6f970bd6d970bef57,0xdd6d750dcb3a70bcb1a7],#[0xb3a40cf19a00cc39a70,0xb3a50d43ba90d13b970d,0xba40d839a70e03ba70d4,0xa913d7f9413c39a40e43,0x71415b97140a3a51403a,0x14d5b971443aa9148a3a,0x5839a41583aa914ce7a1,0x4a3a515039a715959761,0x39a515c39a415c3ba515,0xda71c661751c681741c4,0xa51ed7f941d88fa51d08,0x1d463a81cd6f951cc39,0x1e439a41f08fa41d695a,0xf48fa71e4c7a41e4e7a1,0x8b3a51e8e7a11e839a51,0x3aa924ce7a124c8fa71e,0xd7410439a425439a7250,0xa10ec39a71056d751057,0xf281760eef5650ecc7,0xf4c7a40f4b3a10f319a,0x83ba70fc3ba10fc3ba9,0xe7a110039a710839a11,0x3ba11019ba110198a110,0x97616c39a516c39a110c,0x7617039a117039a716d5,0x1168a3a116439a717159,0x17439a11743ba51683ba,0x863a81f839a521439a5,0xc8fa11fc39a1218e7a12,0x39a521c39a121cc7a420,0xba117ca3a1178c7a4210,0x962219d942219d912203],#[0x122839a4230eba62219d,0x238b3a522c39a1234e7a,0x5c39a725839a425839a1,0x39a126039a725c39a12,0x9f9523d9f9123c39a426,0xda0240e9a0240eba523d,0xa024839a524039a42419,0x424839a12499da0248e9,0x26c39a126839a726439a,0x6f015436039a127039a4,0x987973670175364cfa43,0x6d7538b01543895f9736,0xd54341856439ad564392,0x97339e18733a6975342f,0x53742ba4351679733965,0x3b24d7539d4f973749fa,0x5cc7a2358aba135429a5,0x49fa137d4d76380cba13,0x4ba73b853a53b81ba738,0xd76616c16561419a53c4,0x76619716562dc5766263,0x45f1c576629ed6562a3d,0x6054b9760063a25fa857,0x3819a760819a46082ba4,0x457a464463a264063a26,0x49a764855a46484ba764,0x9a465c19a46549ba160c,0x6592285749281ba46601,0x494a697594c5ba3936ad,0x99507949a45ba3955e38,0x81e175982ad659714b95,0x85ba3979cf8796c55a79],#[0x19a99841ba997857a497,0x7a49b05ba39b03fa197c,0xa39c81ba59e455a49b45,0x49e851a59cc53a59c85b,0xb9d0ba19dd0b939d81ba,0xb41fa7bad2995ba64d75,0x52975bcc1fa7bb061a2b,0x794bec41a4bf03ba2bc,0x9a4bf873a5be92176bf5,0x75bd41ba5c2c63a2c281,0x4bdc3ba2bd92975be66d,0xc0051a5be053a5bdc57a,0x3863a2c312176c052176,0x493a1c1041a4c081ba5c,0x41a4c207ba5c148fa2c1,0xd652d729642d01ba4c40,0x65274e7a22d993962d70,0x5278c1a6275f786276f1,0x278c3a5279f785279f58,0x79f787279f58727acd76,0x27976280c3a7278c1a72,0x699527cdba227df78628,0x9a728c59a528d3597285,0x652a1e56529de5652945,0x7292b5762930ba229169,0x290ada7291e787291e58,0xe4dba2298dfa0298afa7,0x1c1762f9c1762ee31762,0x31762e8dba22e9357630,0x1652a5c1762fdc1762f2,0xa22a819a92b055a42b1e,0x930855a4309bd763043b],#[0x31819a531863a231419a,0xcc57a432c63a232819a7,0x453a52c113872cd11872,0x19a930c51a530c3ba22c,0xba433019a7320fb9731c,0xa53341ba43341ba73301,0x5432857443019a53241b,0x442fd65436857443a697,0x42856544285a344285a0,0x85ba33d8e7a243e85a64,0x3ba23dc43a03dc1ba93d,0x9763fc4ba73e053a53e0,0xa23e84ba74581ba94562,0x73e9e1873eaad763eaf7,0x460c7a23ecaba73e8a9a,0x25bd764662976460c7a2,0xc53a5419118742439a04,0x19a3474fb974783ba241,0xb846ee85746eefd546ec,0x756fa69756f669756edf,0x66fe69a36fe69a06fe69,0x671f78466af15466a69a,0x65e187665f784672f154,0x567976656597665e3876,0xe175694aba7664a9a766,0xb9769857a468055a7695,0xa46904ba768c57a468cf,0x2719af876bd67946b055,0x72859a37281ba971863a,0x6849a77204ba771c19a9,0x8aba46aa4d766a41ba77,0xaf876d8b3a26adb7876a],#[0x9a3750b3a274057a476d,0xa5a4419a376049a47504,0x49ec1ba5a481ba7a441b,0x9f90a989edf7849eecd6,0xf106989f1f7849facd64,0x5d3879f49fa59f456a89,0x595a0056a89fc9fa79f,0xaa8a0a3176a0ab565a09,0x76a1de575a1c59a4a1c5,0x7a05cf87a0459a7a1dd5,0xa105ba3a10fe98a0c9ba,0x145ba3a141ba9a1057a4,0x419a7a1819a4a1853a5a,0x5ba3a2dad76a390794a3,0x9a4a304ba7a2c57a4a2c,0xa7a4c1ba5a4c19a5a301,0x7a241ba5a541ba7a501b,0xa5c1ba3a583da3a3ddb8,0xf81ba3a641ba3a601ba3,0x67974c468574c6039a2c,0x7974c4e5575c45f784c4,0x1a7c4a4d75c49f784c4e,0xa5c593395c593195c588,0x2c752995c5c55a5c7083,0xc8855a4c6c57a4c6839a,0x9c59a3c9d2975ca26975,0x3ba2c8c43a0c8c19a9c,0x794cb851a5c9453a5c9,0xd65ca81ba5d0463a2d01,0xa4ce88fa2ce43ba2cae4,0x5cdc57a4d0863a2d0883,0xcd851a3cd839a0cddeb8],#[0xfc7ba5cf48fa2cf451a4,0x1379759d6b9558c3da3c,0x3955a533975a1679559,0x9644a0c3a4494fb975a9,0x9747ecd7647ef17547d7,0x747cc1a747d7b9747d79,0x4867976486f165484c3a,0x80c3a64857b964857996,0xef1a4488afa7481e5874,0xdfa04985ba848dc18748,0xfa7498c3a4498dba2498,0xa5490afa54902da74a42,0x54c57ba449cc3a449de7,0x4c579974c6cd764c6f17,0xc8c3a74c4c1a74c57b97,0x951764d8c3a54c97b954,0x2da54dc2fa54d42da74d,0x165511796452cc3a4520,0xa65117b965127976512f,0x55157b95514c3a6510c1,0x51de585518dba2518c3a,0x25c3a751dc17651c87a7,0x82da5534c3a4528c3a45,0xaba74a9e1874a8aba14a,0xd874b2f1a34acaba14ac,0xa34b8c7a24b857a84b1b,0x54b429a74c02ba74b8c3,0x4bccba14bde3a54b4aba,0xf14d764f183a14bd80a1,0x42ba54ec9fa14e429a74,0xe185538c7a253829a54f,0xfa7541bd7654083a7541],#[0xa354883a153ccba1545b,0x45042da350429a5550c3,0x4f9118750819a850429a,0xc2da350c4da75010397,0x1ba74fc19a850c29a45,0x19a857029a45702da357,0x1a556db7a7555799455c,0xa756453a556419a956c5,0x15642ba45643fa15644b,0x56507a456517a156514a,0x6851a5568fba756503a5,0x42da357419a956849a75,0xfb975b053a55b029a457,0xba05b84ba75b457a45b4,0xa45b85ba35b863a25b86,0x45bc67a15bc19a75c057,0x58429a45842da358457a,0x8829a45882da358819a8,0x81ba55804fa557819a85,0x1ba75e419a55cc19a75c,0x7a15d457a45d01ba55e8,0xa45d85ba35d857a45d46,0x7805379780019a55e057,0x80c63a28086ba08092b9,0xa81ba7855c176850fb97,0x2317679569657b8afa57,0xc1767b5e5657b487a77a,0x5767bd69657bcafa57ad,0xa07a6318679f0ba27993,0x57b087a77a4dba27a4df,0x781697578019a877cafa,0x742fa37742da77815176],#[0x82fa377819a87841ba87,0x19a87d42da37d42da378,0xba97c063a27c06ba07c0,0xa37d819a97d055a47d01,0x77c857a47c819a87d82d,0x7cc23a57c83fa17c84ba,0xdc2da37dc49a77cc55a4,0x86ba08192b9781421a57,0x53a7858fb9781c63a281,0x7a17e89ba178c1ba7860,0xa77e0b3a27e0bba07e0b,0x57f4afa37ecb3a27ec7b,0x7f02da47f819a87f421a,0xfc2da37fc23a57f02fa3,0x51187831198782819a47,0x1ba486419a4838fb9782,0x3a584067a184053a583c,0xa384463a28446ba08445,0x5a822976a6853a58445b,0xa7055a7a81d176a81e17,0x7419a9a841ba9a7057a4,0xc57a4a786ba0a783fa1a,0x19a9a9dad76a9c55a4a7,0xba7aec55a4a9857a4a94,0xa5ab06ba0ab01ba5af01,0x7ab451a5ab44ba7ab053,0xafdd7a3af4fd76af849a,0x19a4ae50b95ae01ba4,0x81ba5d9863a2d941ba4b,0x55a4d2419a8d282da3d2,0xba8d183ba2d1819a9d24,0xa4d1c19a8d2c2da3d2c1],#[0x7d1c3fa1d1c53a5d1c57,0xd3051a5d2055a4d201fa,0x3d2176d3c1da7d302da3,0x819a8d412176d4019a8d,0x63a2d9c2da3d442fa3d3,0x9a8d4d2176d4c1ba5da4,0xa3d483ba2d4843a0d481,0x3d7c2da3d541fa7d482f,0xda82da5d882da4d885ba,0xb92b978b533978b01ba4,0x4fb978bc67a18bc63a28,0x57490c1ba790863a28c,0xd769041ba790d017590d,0x978cd33978c81ba7911b,0x78d467a18d463a28d12b,0x915bd76919e165918fb9,0x8caba58801ba791c53a7,0xaba5885656588c29a38,0xf7a28753176891656589,0x3a787cc7a287e298687a,0xa4898b7a186caba58888,0x7894b3a2894aba489cab,0x8a8aba48a0b3a28a07ba,0xac23a58a42ba48a429a3,0x439a08e419a38ac29a48,0xfb978d867a18d911878e,0x3978e419a38e113928e0,0x918f514918f419a38ed1,0x38f053a58f457a48f517,0x901159390115968f1159,0x115a090019a39011596,0x857a48f915a690115a39],#[0x57a48fc63a28fc53a58f,0xd76b2c1ba5b2853a58fc,0xa5b0c1ba5b381ba7b34f,0x7b1051a5b104ba7b0c53,0xb3cfd76b441ba3b4049a,0x1c19a3b181ba3b49d3a4,0x1ba3b4c19a3b210795b,0x1ba5de867a1db81ba3b5,0x7a1dc41ba5dec63a2de4,0xa0db01ba5df463a2df06,0x7dac2ba4dac3ba2dac39,0xdd53d76dd429a4db41fa,0xdc29a3ddc57a4dd11586,0x51397b541ba7b6029a5d,0x1ba7b64fd76b641ba4b6,0x3a1b6863a7b7063a1b70,0xa1b8063a7b7863a1b74a,0x7b8863a1b8463a7b8063,0xb591392b581ba7b8c1ba,0x981ba4b941ba3b9019a3,0xc63a2e0067a1dfc1ba3b,0x1ba4e401ba4e3c63a2e0,0x586e2463a2e1467a1e10,0xa0e2d6f95e2c63a2e211,0x3e4421a4e3821a3e3839,0xe501ba5e590b85e4d0b9,0x681ba4e6463a2e610785,0x81ba5e701ba5e681ba4e,0x1ba3e801ba4e7c1ba5e7,0x1760881ba3e881ba4e84,0x7511353a10a3516409b5,0x412351a7117517411751],#[0x11b51a51235195123515,0x8351a412b51a112b51a7,0x35164187518618351651,0x39760574d860634d6506,0xd640c739860673965067,0x760c31d750c31d760bf4,0x51c751a00d299760cae5,0x1d299651d299751cb1d6,0x6351a01631d970ea9986,0xdab97363257536355713,0x3d64342a17536eed6536,0x9753a2d97633f057533f,0xa1622a17661325656128,0x65f705655f721655f2a3,0x92b1fa26327165636897,0x229d7592ae96592b3d54,0xdff87921fd8792305759,0x9d7494ddf87926d96592,0x387949f18794b057494a,0x6599ac5659928974991f,0x5b9ec59796ee7a299641,0xbbe7176bba8976b9f056,0x3b21654324176bbe7175,0xf11653ccf3a543a9d754,0x89763d305653d28d763c,0x5636ed61764118b953fe,0x7466a9d746f73d646ef4,0x4672dd7666b117566b2d,0x6b68976677057566f2d6,0x10e3a36c6dfa36be4176,0xe8d75c4f2d64c4641767,0x8965c5a8975c50e3a5c4],#[0x795cb31fa2c7e7165c82,0xa34e32da44cceda0cdd4,0x68997565820e3a655f2d,0x891ea8040bfa689cbfa,0x9b519409b519708b5196,0xf51a609f519609f51960,0x519412351a411751a909,0x1a111b51a912351a4123,0x8518351a512751a11275,0x618b5196183519518351,0x6739a60574d8506351a,0x5f39a806739a60673985,0xcefa7071a197071a1970,0xa197074efa506da17607,0x3970c1a1970c31da60bd,0x760dcefa70c0eda70c1a,0x61c4efa40d31da60cda1,0x1d0efa51c9a3951c8eda,0xee99a81d299a61d29985,0x5a1861eda1851eda1651,0xefa41e0efa41de99a61d,0x176105a1960fb1d650f8,0x960f339a60ef39960eda,0x70fcefa90f71da60f31d,0x160efa1161a1a6101a19,0x69976205a2a9161a1a9,0x5a165215a198205a1962,0xefa9201a186215a18521,0xfa520da19620a9976208,0xa022da196229a196224e,0x822f1fa522cefa422f51,0x248eda1248eda524204a],#[0x60f5a7361a1a4249a1a1,0xe0986340f7a1370f7a73,0xf1863458b9733d899733,0xf9734d1d9734d4797349,0x653b0d3a53a06fa734d1,0x53adc9863a8efa23a589,0x3bcd3a137b05a63546fa,0xf209865f06fa93b51d86,0xdff865f5fd865f60b865,0x6fa75f91d975f975975e,0x9866346da75fd1d975fc,0x8663d756563dcb86635c,0x564e07a26391f8663d1d,0x6591f8664d1d8664d756,0x29a174659a171659a141,0x18997921a59592a0b859,0xff8592cd3a7920d1a792,0x197924d3a592d899592d,0x9794045a993175959316,0x79391d879386da79411d,0x9446fa593447a79391f8,0x4f215494c47a593c6da5,0x97597949a79494e0b849,0xbfa7948bda7949779794,0xf9795d1d9795df17595c,0x8796575759646da795d1,0x495045a79651f879651d,0x955f2a8951f1a8950bfa,0x6847a49586da49606fa4,0x895a7992717599045a49,0xc9759a497a5999cb8599,0xf859a961659a86da59a5],#[0xa899c97a499c45a59a91,0x49acefa29a1caa899dc9,0x9897575989897498845a,0x7045a79891f879891d87,0x4bfa1976c59196cd3a19,0xf3a197df2a8975f1a897,0x7a197da7a197da4a197c,0x859b961659b845a198c4,0x59b045a19bc45a59b91f,0x9e06fa19e06da59b46fa,0xd11e989c11d989c11da9,0x51d989c4f3a19c445a49,0x6fa49c845a19d51e989c,0x7a0ba1ff86b9c6da49cc,0x86bad4576bacefa2ba0f,0x6bb86da5bb497a5ba91f,0xbcc6da6bc9c976bc9f38,0xe671a6bc11f86bcd4576,0x27196bd11f86be54576b,0x46a9bfd45a9bfe71a6bd,0x596c114596c0d1da6c35,0xa5c1497a4c169ba2c154,0x1c1c95a1c1c95a5c1a73,0x2d99541c2545a4c1d45a,0x9a019629e019628b4fa2,0xf43a22ea01962f8e3a42,0xe3a52f4e3a42f601962f,0x1a643207872ce05872cc,0x8543b3d54438f3a6430f,0x343f4fa243cf3a043e09,0x3c98b963d189963d0f3a,0xdce3a33d4bfa73c9f187],#[0xd1d873dcefa23dcf7a03,0x45a73e51d873e447a73d,0xd873fad9763fb05753f8,0xa73f98b973f989973f9f,0x53fdfd853fcd3a73f8d1,0x4046da8401f185400d3a,0x51f974051d97405dd76,0x845a74111d874106fa74,0x45a541447a540c6fa540,0xb9644a897644b0565448,0x96451c976450efa244d8,0x33ecd3a03ec45a545d1f,0x4633ba2460d3a0460d3a,0x2a05874251d87420d3a3,0x45a342c45a042d1d874,0xf1a66ec45a347045a047,0xb846f721546f4f3a66ec,0xa36f8f3a06f8f3a46f60,0x766a038766a0187668f3,0x6728d76670e3a7668e1a,0x6dfd8766ed97666ce3a6,0x8d3a766cd1a766dff876,0x619667d7796679759667,0x5a967d459767dcb8767d,0x876851d8768447a967c4,0x769d1d8769c47a76851f,0x6a047a668845a769d1f8,0xb2c5766b305746b045a6,0x175976b1f3876b1f1876,0xbfa76b0bda76b177976b,0xd976c9dd766c9f1756c8,0x756d06da76c91f976c91],#[0x76d11d876d161766d175,0x6b8bfa46b845a76d11f8,0xcc6fa46c176a96b975a9,0x447a46c597a36c46da46,0x717670f059470c45a46d,0xf96725c976725779670e,0xa371445a672d457672d1,0x36acbfa06ac45a47328f,0x6e11d876e175756e0bfa,0xe575756e445a76e11f87,0x51f876e51d876e561766,0x47a36dedba46d845a76e,0xba473445a36e98ba46dc,0x9673cbfa6739759673a8,0x2740bfa0740bfa673d75,0x744e3a3744bfa37431fa,0x4845a4755cb87755cb87,0xc45a4759cb87759cb877,0xcb94751c99475045a375,0xda4a1ac597a05fd94a21,0xa5a306da4a324195a286,0x5c4561a3a4161a0a406d,0xc50e3a6c44e1a6c47116,0x54efa2c55fd65c70d3a5,0x54796c5d4596c5d6396c,0xe3a3c7847a5c6445a6c7,0x596c828994c827175c78,0x96c99f165c994796c814,0x6c867194c851f96c991d,0xc8daba0c8e71a6c86719,0xb095a5cb28954cb1a3a2,0x6da5cb91f95cb897a5c],#[0x7154cb445a5cc14575cc,0x6a9cb545a9cb497a4cb6,0xa2ca607a2d006da4cbd4,0x5cc447a3cac47a0caf1f,0xcc94575cc845a5cc5457,0xe445a3ccc45a0ccc45a5,0x897a3ce69ba2ce497a0c,0x6fa3d0a07a2d086fa0d0,0x193cddf385cd1a392cd0,0xa3cdda1a0cdda194cdda,0x5cd4f7a0cd5a1a4cdda1,0xcec45a3ce045a0ce1f38,0xf14596cf097a6ced4596,0x69ba2cf497a0cf497a6c,0x979559673a5cf497a3cf,0x5864a11d865ad8b95599,0xa14cf11a648b2da64859,0x54d196a94cd95a94cce3,0x52995865332d96510e3a,0xe0d3a14e305a64ace3a5,0xcd3a54e98aa94e189a94,0x1d86570d3a5549898654,0x996561959655d1f86571,0xa95586da9559f1965558,0x6565f3a55646da956c6f,0x569cba75646fa65651d9,0xdc6fa55c5cba557c6da6,0x6fa55d91da65dd1d965,0x6fa48091d86811756581,0x1967b595867ba01a6850,0xa47b0e3a47a595867be0,0x57d576a977175a9770e3],#[0x7c51f867d51d867d5756,0x2195967c68d767c71165,0xbfa1791f1a685d1d868,0x75967e975967e4bfa479,0x3a37ef1fa27ecbfa47e1,0x7182845a47fcbfa47ef1,0x4831a171831a974829a9,0x8246fa18251d87835a17,0x491d968486da782c6fa4,0x46da684d1d9684c6da68,0x45a7acd9575ac86fa484,0x176a897575a898974a88,0xa7a891f87a891d87a896,0x8a6cbfa1a6cd3a1a6845,0xa75a4a1a75f2a8a6df1a,0xa045a1a8c47a1a75a7a1,0x45a1aa445a5aa11f85a,0x6fa5a964195a924191a9,0xda9ae86fa1ae86da5a98,0xa4ab91e98aa91d98aa91,0x8aad1d98aacf3a1aac45,0xab20fa0ab045a1abd1e9,0xb06fa4ab203a3ab207a2,0x6da4ab5cba7ab1f3a5a,0xa171ad845a7ad5a971ad,0x5a5ac11da4afd1da1afd,0xa1ae445a5adca5a1ac4a,0x1ae46da1ae46da5adc45,0xd694576d691da4ae51da,0x6d4576d6d7565d6d1d86,0x64165d624164d611d86d,0x7a2d946fa5d646fa4d6],#[0x565d151f86d294576d2a,0x85d35fd86d168976d170,0x6d7445a5d4447a5d3a41,0xd794576d791d86d75457,0x511da6da06fa5d711d86,0x45a4d55a184d51a181d,0x4576d851d86d814576d8,0x5a5d586fa4d7d1d86d85,0x54d8d9551d8895a1d5c9,0x8c71fa28c045a4d9189,0x87cd3a087c6fa38c46fa,0x70d3a3888d3a0888d3a3,0x5759689d759689b1d878,0xbfa08a0bfa3894bfa089,0x7a48a0bfa38a31fa28a0,0x708e51d878dc45a38af0,0x39011d878e9a1738e5a1,0xb246fa38fc6fa08fda56,0x306fa1b311da9b246fa1,0x51e98b051d98b051da9b,0x1e98b091d98b0845a3b1,0xfa4b0c6fa3b0e07a2b0d,0xa3b11cba7b0df3a5b0df,0x1b1d1da3b491da0b486d,0xdc11da3b211da0b21895,0xe86fa5dbd1d86dc14576,0x607a2de46fa0de51d65d,0x1d86dcd4576dcc6fa3de,0x183db1a180db06fa5dc9,0x60dd445a3db445a0db5a,0x3dd06fa0dd1a563dd5a5,0xde18950ddd9553dd86fa],#[0xfd1f96df845a3de045a0,0x45a6e051d86e051f96d,0xf3a5e006fa4e0207a2e0,0x7a2e0c6fa0e0c6fa6e09,0x96e11f3a5e0c6fa3e0e0,0x2e1445a6e191d86e191f,0xe1c6fa4e1603a3e1607a,0x2207a2e206fa0e2045a4,0xc45a4e29ffa4e206fa3e,0xeda0e2da390e2da190e2,0x194e2da393e2da193e2c,0x40e2f1f95e2da394e2da,0x4e3045a4e31a143e2da1,0xe397590e3845a3e3447a,0x44bda4e38bda3e397790,0x51d95e5c6da1e486da5e,0x1d94e7d1d91e7c6da1e5,0xdc00011d94e851d93e81,0x6c03b803300264018c00,0xd406e806340590050804,0x580a7c09c80924088407,0xe40e300d940cf40c180b,0x40119010f010300f800e,0x6415b814d01400131c12,0x6419c8189c17f4172816,0x7c1d901ca41bcc1b301a,0x6020d8205c1fd41f4c1e,0x4823c8234c228c21e821,0x5c26ac25fc253424b424,0x482a6c297028bc280427,0xa02e182d782ce02c342b,0x18317830b430082f4c2e],#[0xe0351c3460339432d432,0x183878375c36e0366435,0x3c3bc03b443ac839c439,0xd83f6c3ecc3df43cfc3c,0x8042cc42184140408c3f,0x8c46b045b044e8446c43,0xdc49f4497c4898480847,0x2c4d944d184c7c4bb44a,0xa050f8500c4f504eb44e,0xb85434538852f0523c51,0xfc58105768569455a454,0xac5bf85b605ab059b458,0x285f385ea05dc45d145c,0x6864a863d46264610460,0xe4684c677c66c0660865,0x846c986b746a8069b068,0x84710c70346f606e746d,0xe8743873b872e4723471,0x5077a076b07604755074,0xb87be87b207a14793878,0x6080a47fbc7ebc7ddc7c,0x9884bc83d882c881f881,0xa089bc88e08804869885,0xfc8e448d448c3c8b508a,0x9892b491b490e08fcc8e,0xe096ec9624954c947493,0xf49a7099d8994c989c97,0x509e7c9da09cbc9be49a,0xaca2dca1b8a0d89ff49f,0x50a6a8a5eca550a48ca3,0x58aab4a9b0a8f0a82ca7,0xacaeb0adecad04ac4cab],#[0x3cb338b254b148b08caf,0x54b770b694b5a8b4ccb4,0x78bba0baa0b9f4b968b8,0x6cbf84bed4be48bd48bc,0x58c2acc238c188c110c0,0x3cc6a8c608c4f8c414c3,0xf8ca34c958c898c7fcc7,0x10ce28cd84ccd0cbe4ca,0xb8d204d178d0c0cfd8cf,0x30d66cd5bcd4bcd3b4d2,0x4cda5cd978d8c8d7e4d7,0x14de34dd90dce4dc0cdb,0x9ce204e168e0b4dfe8df,0xcce51ce46ce3b8e31ce2,0x4ce8a0e7dce72ce664e5,0x98ebf4eb68eab4e9f0e9,0x6cefbcef20ee30ed44ec,0x30f368f2c4f1e8f140f0,0xc4f6dcf62cf574f4d0f4,0xacfad4fa2cf994f8b0f7,0x20ff38fe60fd64fc68fb,0xa903ed030d023d011500,0x10831072d0651059904,0x450c610bc10ad509e509,0x9105d0f810e9d0de50d,0x451441136912b111c511,0x7918b917f5170915f515,0x891cbd1bf51b251a3119,0x39214920651f811e591d,0x5125a124e1242d233d22,0x352949289d279d270126,0x52d352ca52c052b1d2a],#[0xcd310d303d2f852ec52e,0x9534e9343d339532cd31,0xed382d379536f5363135,0x753bd53af93a39399538,0xb93f293e8d3ded3d4d3c,0xf5425d418940f140353f,0x5945ad44e9446d43ad42,0xa149014821474d46c546,0x554c914bf54b114a5549,0x7150ad50014f2d4e514d,0xd55439537952c9521951,0xf1576556d155f1556554,0x595b395a4d59a5587d57,0x255f895ebd5e055d255c,0x91631d626d617560f960,0x4d65cd651d64a1641963,0xe169296875677966ed66,0x996cad6bc56b216a9569,0x21707d6f9d6f1d6e556d,0x4573a17301727971b971,0x6d77c576c175b9750574,0x8d7af97a5179ad78fd78,0x397e8d7da97ce57c397b,0x7d81b180ed80657fe97f,0x558499842183c9834582,0xe1882d875586c1860d85,0x418ba18ae58a4d899588,0x898e1d8db18d4d8cd58c,0xb9912590798fe98f418e,0x6194c193e9931d926991,0xb19819976596b1960995,0x1d9b559ab59a05993d98],#[0xdd9e6d9dbd9d359ca19c,0x81a0fda07d9ffd9f459e,0xa1a3f9a35da2d5a205a1,0xcda741a6b5a619a561a4,0x61a99da911a8a5a839a7,0x41ad91ace1ac31ab05aa,0xb5b135b079afe5af29ae,0x59b49db3f9b359b279b1,0xadb7f9b741b675b5e5b5,0xddbb15ba9dba0db965b8,0x9dbed5bdf5bd8dbc81bb,0x2dc261c1c1c0f5c055bf,0xd9c70dc641c555c415c3,0xd1cb29ca65c9bdc8cdc7,0xd9cef1cdd9cd05cc69cb,0x35d291d1bdd11dd079cf,0x71d5b1d4f1d45dd3b9d3,0x1d94dd88dd7d1d711d6,0x39dc99dbe1db29da81da,0xa1dfe9df35de81ddeddd,0xa5e301e285e1ede145e0,0xade615e559e4cde43de3,0x35e8b9e861e7bde739e6,0x39eba9eac1ea0de999e9,0x19ee8dededed5decb9ec,0x61f1a1f135f079efbdef,0x6df4adf401f381f309f2,0x81f7e9f77df6d9f629f5,0x6dfac5fa5df9c5f92df8,0xb9fe39fd85fd01fc6dfb,0xce01d200fa0009ff71fe,0x6605aa0516044a038202],#[0xd60946084607aa06f606,0x9e0cea0c0a0b4a0ab209,0x6e10ba10060f060e460d,0xca1446139e12e2122211,0xb2170e167615e2153a14,0x5a1abe19da193e183217,0x361db21d261c9e1c021b,0xde2106208e1f961ee61e,0xda250a241a235222be21,0x3a294e286e27a626ea25,0x922da62cca2bf22b262a,0x1e318630f230322f7e2e,0x8e34b6341e337e32ba32,0xa3846379236f2364635,0xc23ca23ba23ab239aa39,0xea4146406a3fba3ee63d,0xfe4512441e4336429641,0xe64936488e480e470e45,0xe4c824be64b464a9649,0x7e4faa4eea4e724dc24d,0x7652c25232519a50ee50,0xe65632558e54f2543253,0x25a6a595a58ae579e56,0x6a5dc25d225c665bde5b,0x8e610660525fba5f1a5e,0x6e64b663b26292621e61,0x5267be67166686661665,0xa26b026a7669c268e668,0xa66dee6d466cbe6c326b,0x16709e703a6fd66f426e,0x2a743a7322724671aa71,0x9277da774e76d6760a75],#[0x667ad67a2a79be794e78,0xfe7d5a7cde7c6a7bda7b,0x36807a7fca7efa7e6a7d,0x2683968316828281f281,0xfa86328586850a849a84,0x9a89f6897a886e87ba86,0xe8d868c6e8bb68b168a,0x4a90a28fde8f528eaa8e,0x1a947693d2932e923a91,0x6a97a2970e9622959295,0x3a9aa69a229996990a98,0xa69e1e9d6e9cba9bce9b,0x8aa0caa0429f9a9f129e,0x52a3cea33ea2c6a21ea1,0x16a70aa656a5c2a51aa4,0x7aaa9aa9a2a8faa876a8,0xeaae26ad82ace2ac3aab,0x8eb142b0d2b016af56ae,0xd6b48ab396b2deb25ab1,0x5ab6f6b666b5eeb562b4,0x52ba5ab9e2b91ab836b7,0xfabd72bcfebc82bc06bb,0xd2c02abfaabefebe82bd,0xfec372c2e2c262c1dac0,0x9ec6eac636c56ec48ac3,0xd6ca5ec9aac90ec842c7,0x9ecd0acc8acbe6cb5eca,0xe2d052cf92cf06ce8acd,0xd2d34ed2aad21ad18ad0,0xc6d636d582d4ded44ed3,0xd6d94ad8bad7fed772d6,0x86dcc6dbfadb4eda52d9],#[0x4edf82df32dec6de26dd,0x42e282e1fae182e0e6e0,0xc6e642e5aae4dae3eae3,0x46e9bee8eee81ae792e6,0x4aecbeebeaeb5aeac2ea,0x42ef96eef6ee32ed8eed,0x6af29ef202f182f0faf0,0xf2f65af5c2f4e6f416f3,0x22f97af8d6f832f77ef6,0xaafd4efc3efb7efad2fa,0x8b00eeffeaff5afe7efd,0x1f0407034b02cf024f01,0x8707ef0727064705bb05,0xcf0bf30ad70a0b091708,0x630f130eaf0ddf0d570c,0xdb114710c3103b0fd30f,0xd31433139712f7126b11,0x1b178316db1627156b14,0x571abb1a07195f18cb18,0x831ef71dff1cf31c271b,0x2b22cf22432137208b1f,0x4325c72503245323a723,0x3728a727f3276b271326,0x2f2c2f2b372a9729ef29,0xc730172f2f2e8f2ddf2d,0x1b336332a331ef314f30,0xbb373b366f354f34b734,0x9f3b833a833973389737,0xbb3ffb3f273e1f3d7b3c,0x7343c742ff4277419b40,0x6f46cf463345a7451744,0x7b49f3495b48bf480b47],#[0xe74c634bef4b574adb4a,0xaf4f2b4e934e0f4d434c,0x4b51cf515750d350474f,0xc3547f53ff536b52af52,0xb356fb563f55b3556b54,0x535993592f58b7587357,0x8f5be35ba75b335ad75a,0xc75e5b5dff5d635ceb5c,0xab6117609b602b5f4f5e,0xb7635b631b627f620761,0x13659764ff643763d763,0x37679f66d3666b664b66,0xe76a076987692b687768,0x676dcb6d476c7f6b8b6a,0x8f6ff36f736f2f6eeb6e,0x4372cf726f7207714770,0xdf753b74ab740773c373,0xdb785b77a3770b766f75,0x977aeb7a5f79bf793f78,0x3f7dfb7d637ccb7c1f7b,0x4380bf7ffb7f5b7eab7e,0xc382a38283826381d381,0x6383438323830382e382,0x383e383c383a3838383,0xa3848384638443842384,0x438523850384e384c384,0xe385c385a38583856385,0x83866386438623860385,0x23870386e386c386a386,0xc387a387838763874387,0x6388438823880387e387,0x388e388c388a3888388],#[0xa3898389638943892389,0x438a238a0389e389c389,0xe38ac38aa38a838a638a,0x838b638b438b238b038a,0x238c038be38bc38ba38b,0xc38ca38c838c638c438c,0x638d438d238d038ce38c,0x38de38dc38da38d838d,0xa38e838e638e438e238e,0x438f238f038ee38ec38e,0xe38fc38fa38f838f638f,0x8390639043902390038f,0x23910390e390c390a390,0xc391a391839163914391,0x6392439223920391e391,0x392e392c392a3928392,0xa3938393639343932393,0x439423940393e393c393,0xe394c394a39483946394,0x83956395439523950394,0x23960395e395c395a395,0xc396a396839663964396,0x6397439723970396e396,0x397e397c397a3978397,0xa3988398639843982398,0x439923990398e398c398,0xe399c399a39983996399,0x839a639a439a239a0399,0x239b039ae39ac39aa39a,0xc39ba39b839b639b439b,0x639c439c239c039be39b,0x39ce39cc39ca39c839c],#[0xa39d839d639d439d239d,0x439e239e039de39dc39d,0xe39ec39ea39e839e639e,0x839f639f439f239f039e,0x23a0039fe39fc39fa39f,0xc3a0a3a083a063a043a0,0x63a143a123a103a0e3a0,0x3a1e3a1c3a1a3a183a1,0xa3a283a263a243a223a2,0x43a323a303a2e3a2c3a2,0xe3a3c3a3a3a383a363a3,0x83a463a443a423a403a3,0x23a503a4e3a4c3a4a3a4,0xc3a5a3a583a563a543a5,0x63a643a623a603a5e3a5,0x3a6e3a6c3a6a3a683a6,0xa3a783a763a743a723a7,0x43a823a803a7e3a7c3a7,0xe3a8c3a8a3a883a863a8,0x83a963a943a923a903a8,0x23aa03a9e3a9c3a9a3a9,0xc3aaa3aa83aa63aa43aa,0x63ab43ab23ab03aae3aa,0x3abe3abc3aba3ab83ab,0xa3ac83ac63ac43ac23ac,0x43ad23ad03ace3acc3ac,0xe3adc3ada3ad83ad63ad,0x83ae63ae43ae23ae03ad,0x23af03aee3aec3aea3ae,0xc3afa3af83af63af43af,0x63b043b023b003afe3af,0x3b0e3b0c3b0a3b083b0],#[0xa3b183b163b143b123b1,0x43b223b203b1e3b1c3b1,0xe3b2c3b2a3b283b263b2,0x83b363b343b323b303b2,0x23b403b3e3b3c3b3a3b3,0xc3b4a3b483b463b443b4,0x63b543b523b503b4e3b4,0x3b5e3b5c3b5a3b583b5,0xa3b683b663b643b623b6,0x43b723b703b6e3b6c3b6,0xe3b7c3b7a3b783b763b7,0x83b863b843b823b803b7,0x23b903b8e3b8c3b8a3b8,0xc3b9a3b983b963b943b9,0x63ba43ba23ba03b9e3b9,0x3bae3bac3baa3ba83ba,0xa3bb83bb63bb43bb23bb,0x43bc23bc03bbe3bbc3bb,0xe3bcc3bca3bc83bc63bc,0x83bd63bd43bd23bd03bc,0x23be03bde3bdc3bda3bd,0xc3bea3be83be63be43be,0x63bf43bf23bf03bee3be,0x3bfe3bfc3bfa3bf83bf,0xa3c083c063c043c023c0,0x43c123c103c0e3c0c3c0,0xe3c1c3c1a3c183c163c1,0x83c263c243c223c203c1,0x23c303c2e3c2c3c2a3c2,0xc3c3a3c383c363c343c3,0x63c443c423c403c3e3c3,0x3c4e3c4c3c4a3c483c4],#[0xa3c583c563c543c523c5,0x43c623c603c5e3c5c3c5,0xe3c6c3c6a3c683c663c6,0x83c763c743c723c703c6,0x23c803c7e3c7c3c7a3c7,0xc3c8a3c883c863c843c8,0x63c943c923c903c8e3c8,0x3c9e3c9c3c9a3c983c9,0xa3ca83ca63ca43ca23ca,0x43cb23cb03cae3cac3ca,0xe3cbc3cba3cb83cb63cb,0x83cc63cc43cc23cc03cb,0x23cd03cce3ccc3cca3cc,0xc3cda3cd83cd63cd43cd,0x63ce43ce23ce03cde3cd,0x3cee3cec3cea3ce83ce,0xa3cf83cf63cf43cf23cf,0x43d023d003cfe3cfc3cf,0xe3d0c3d0a3d083d063d0,0x83d163d143d123d103d0,0x23d203d1e3d1c3d1a3d1,0xc3d2a3d283d263d243d2,0x63d343d323d303d2e3d2,0x3d3e3d3c3d3a3d383d3,0xa3d483d463d443d423d4,0x43d523d503d4e3d4c3d4,0xe3d5c3d5a3d583d563d5,0x83d663d643d623d603d5,0x23d703d6e3d6c3d6a3d6,0xc3d7a3d783d763d743d7,0x63d843d823d803d7e3d7,0x3d8e3d8c3d8a3d883d8],#[0xa3d983d963d943d923d9,0x43da23da03d9e3d9c3d9,0xe3dac3daa3da83da63da,0x83db63db43db23db03da,0x23dc03dbe3dbc3dba3db,0xc3dca3dc83dc63dc43dc,0x63dd43dd23dd03dce3dc,0x3dde3ddc3dda3dd83dd,0xa3de83de63de43de23de,0x43df23df03dee3dec3de,0xe3dfc3dfa3df83df63df,0x83e063e043e023e003df,0x23e103e0e3e0c3e0a3e0,0xc3e1a3e183e163e143e1,0x63e243e223e203e1e3e1,0xe0de03e2c3e2a3e283e2,0x811b44589b11a1344e06,0x2ec268671209c22700e0,0x8283de0604ec2e830e58,0x5e1360c25708051a17,0x612814c1704df0ae2015,0xce184980b70a029c202,0x15027058b0de202b0306,0xe0dc0b0280bc6c07c1e4,0x1f0b04305e831850c282,0x192302c03480308e131c,0x21406e0e068f06270598,0x4290240af066886430b8,0x2a2501c03d8610c91419,0x5299a90668816d1810a2,0x83814067011d0ab1c080,0xe3486380401711d060d2],#[0x492145d41d8e4a244421,0x380489a23bc040fc240,0xe108d6832a101d30b311,0x1075227e1980c2363060,0x3b06d81609a2304b0bf8,0x1444dfc4e0313625f070,0xe090d81a45542cc4c26,0x89c030a24846c9181643,0x39852910a19c0c5884a0,0xa1d3402d832d8223884c,0x3c1aa0e5290b51123b10,0x346282160990941219d0,0xf80c23301b11fc21336,0x5be821312264e089f04,0xea2f41b88d0be810c6c1,0x8a8910705925045f0,0x25528b47282c3c6120f2,0xa4af87513c080ac1e4a4,0xe90fa2ec4560051d1a60,0xa708286e19c0262b02a1,0xd90de8d918a2283584c,0xe09e60286aa216a20d05,0x529ca0b2162128948f31,0xc8807459c3446a0221a0,0xe91d08c361dc3b120612,0x7509610c0a80b1126c4b,0x66c2b0c60503f0c81245,0x1e3474421112218642d8,0x947881a280a280c3dd00,0x50224b41292b0b30062,0x84122c100d613c4b20b6,0x15815287143880d001b8],#[0x905414c1214242a151d,0x62c4e43c2248e0020aa2,0x82887a9a42a432d1331c,0xc802340868dd5220cc19,0x9250bf0814070d61b00,0xe9361f42f31687ac869,0x946a8ca5c9752e56539d,0x21c0dbc73a4415c4e8ce,0x9d4607425d45d91b170e,0x2e85c326a3e8dca083e8,0xab47aa2e0691f850648,0x1a4989001602c024eb0e,0x332561d6254b00dd9b8b,0x43a2442b4029208cc9a5,0xfe98c348121c8141413e,0xa01014c17e3601014b2f,0x5af851188405311ccfbd,0xa05efc1000a5ce784819,0x1983f62006577a3e9010,0x7479b9050243661fa405,0x328252adff35d482084a,0x91233053db0923359f5b,0x8910dd72e5224676fbf2,0xd4b00a848727260b520e,0x4a331df7a4c26504a717,0x93296a709f0662779bdb,0x12979bcb8323331ebe27,0x80bcf63bd51a2cfadd06,0xefc34d921ba1fa40519,0xb689109e7b1986c051aa,0xdbe58558121e9ffc4c44,0x467b7f97280ca21223d],#[0x647d3f80d024367c1652,0xbf06823349f9a648f04a,0x7fffdad5a85ca109145f,0x5386ec55356f12304c4d,0x304051018f55c11994ff,0xcaa5f08570144fbe7842,0x84d26e3fe5e00640a21d,0x32e65f20cca5cb80fcc4,0xed666599fc8c8b987d83,0xf20be6667ec38d9997b2,0x63f0909a79d2601014dd,0x534217f2026979e2484f,0x10d87a2868040531be8,0xc2fd1509810c2fd2551,0x2f83896e043235f8da41,0x6d1a702271f9e32b810d,0x4be0e350a41112eef2c2,0x5293cfa6eddb000881,0xc085b7f4400217ce0e08,0xea02183f620065a7e1a4,0xa5860fbb23810caedb3,0xb2bb62469043adfa4438,0x9e09ff6086b1bfc82085,0x21c0530beccc7fb04301,0xe067827fd82184f2a4e,0x1c6cdd0197dfa41e0101,0x55411457c1028eefe22d,0xc5c020850039f0c5d4ee,0xfb7a054458df6f40a5f7,0x5a2ed5d60460380062c8,0x50579d0d92cfc11967da,0x8ba7e736a1508112cffd],#[0x749810b0e6fe08542043,0xfc32a840862fe404d6f7,0x9513a211ff1551010d4,0x10d6c7e8545286b7b47c,0xda637c4702211ff15510,0x48b584e87589ac08d0ff,0xd6ff6d16022204aa09fd,0x9fa5c8ad7465a75ee4a9,0x4610e298a7efd1b50655,0x3c804053f3ec4909e7f5,0x9ff6e1201014cd7f4a4,0xee380988f7176ea04053,0x65e42d483333da0484a5,0x297afb7d61521af40738,0x4e85082054e97f8d4800,0x4002143fed82426653ff,0x812154ffd6ea80906fa6,0xa24243a720a0486c7668,0x443f3a14a8a0c489c767,0xd5b234fbf801e8dc4224,0x22130e99b54670ae722e,0xc272e8ce0ffd32c0d329,0xba1d2edf99409235d536,0x8f35a5119a1b3164d121,0x33f09c9061ff442c2467,0xc1beb420a3406728efa2,0xf48c24698f35a511983f,0x17899732d246aaf861fd,0x9633fdc14a0243062477,0xdc068a0d0818422477bc,0x8ce722ec18b234eb57fe,0x5d40284c42fddab8c246],#[0xa9a129acfec0d804a58,0x8cd17fefcdc1a8932792,0xc339417d72234e4be824,0x490112246f7e66e68512,0x24e4672c224513fda1c5,0x7ff522f1e8646967fff4,0x2244665e187fec61234f,0x1760c591a7dfc5e99e04,0x9085f06f75d69234e739,0x2233ebb142e524362994,0x1bfc478880a2565beb28,0x3d7629dcc486475cc484,0x23321fb0d19129784e48,0xdc227b3041223adffa54,0x83312201bffd2a11999f,0x23e49a6b646947c1d844,0xa33fd41697ca30c235b4,0xfda04946800fefc0aa11,0xe0f32d6d1229048b6847,0x912ef12bd60150910cf,0x518209120ff562af6482,0x9831ebf444a33e3c2dad,0xebfc280494680f86aa11,0x698e12c6b7e302a846c6,0x648209115e16b7e34a84,0x39fc1ea8c10489d6083f,0x895f2e22450860c48d04,0xa4dd0ac7349a24413fd7,0x28c308d2daf92690c591,0x1a44f891601297bf1a5f,0xe05508d49fe5bded1861,0x9e3b114824497d6016ff],#[0x28d05e3f4024a33ebf90,0x3f1ec25189add7f85009,0xe5a9878d2a11a564fb9e,0x62441b2fba6e64608244,0x49a431646957fb089370,0x8d3db53cca30c234b6be,0xb01e3aa3416d66f68c30,0x9e5a7f16e372a09105b6,0x7c4f23094b85fcde1d51,0x31d9a2048546e9ec8ca2,0xd1751483024463b3d121,0xa8d28ff46d64538c393f,0x1f806812213f0cb86236,0x11c23ec8bb4628d30eec,0xf24e3a4702352c7ccdaf,0x48bce9e49f3310469a0,0x5a28d28fb310b8090203,0xfe7f4f83688955ec8bb0,0x64d121583d3d71c08d03,0x8048597ff1544090d6f1,0xfaf744856c0922048ffb,0xe2b42121e1dd123d9090,0xb9fee9c61978012a2df6,0xc8ce60048957801c1242,0x24453f00770090d2f093,0xb050228d1cff078200d0,0x5b8f9bf289b1b1136adf,0x2ae890c5e869dd76208d,0x1ffb28aa435446bb7f90,0x48a0ffd9455baa234c6,0xef2e8cbeede48680ae0,0xb448963d556b60d094f1],#[0x28285792441327475687,0x44c9f43e98a58129d137,0xf0484b7ffe6090d4ec02,0x9012a21f4ae782432bd1,0x79275812204fd0a5e68d,0x4a89be0676d104a6872f,0xfdc84845bfa070984200,0x6c0854443e0dab024323,0x9903dbe10c4cc6fd1ca9,0x12648973f0682676f804,0x3e4286aff68ed04cd1fc,0x979720b6c101447b2cb8,0x266f7afb7e5823920289,0x54c0fa1202856c79ea1,0x8627fcd4050b07914f08,0xce4908428777eee88202,0x826ac7f8a8dd01436bff,0x13424093537fc0913486,0x9338ffdbf70c9223cfc2,0xff62e388182a74e431e0,0xe6826a26efac3640a1d0,0xf7c356640a1a3fcd0093,0xe79e1cc81437bfa88284,0x14497db5bfdc840126b,0xde5024d54fd1e596c4c9,0xe4e937d4050c9e5b7f5a,0x8f8900a945366f424050,0x1864c7fc90394093491d,0xf010374f5488555a2e46,0x490275b81ee903054e8f,0x296677a150fbffdbfc04,0xf0618a7bca385213393e],#[0x340fe78819fe512557f3,0x940402a64c7fc913b41,0x6028573f614a0152b1fb,0xd424ca8fc750142bbfea,0x502482a5dbf5280549d8,0x28054a5c7f08104cec7f,0x9342731c024cd97fd6,0xf9f24e8944cfdcbe122,0x2f1c1a099d5ff3003205,0x62450a1db12ae944ce1,0xe126506973f00933fbe2,0x6a0286d03df501433715,0x64ede1697404153cb07e,0xcf0a90dc7d44140580a2,0x4614c1fe90a444ced71b,0x891ba7a80a19afe46b1d,0xfc111334b47948aa2028,0x1899b2f500c8182a6487,0x214341fcfc3a8a529fd6,0x4ee752c1d854a4e9e15e,0xc910153fdf044a9620e1,0x4f9a5dd240a224f33fea,0x5e628c50d2961f6142a2,0x4050ca7ff0942201534b,0xc090b084a426b17f4682,0x985f866561e544144b7f,0xe30a426a8bfe5032080a,0xfd5570b209ae2030694b,0xcc1f040156c65d0145b3,0xe1484d2b17fe38c04495,0xbef00af0084d05ebf064,0x804268afc08318480426],#[0x3d9f2ae120109abbcabe,0xa9a9359fca2ab32051,0x919445500a9c8ff94455,0x3537fc00113b121357df,0x3e38a91dbfe0489f3121,0x523e26e4e416980a2074,0xd5de55a4251340e87c71,0x392049a521ced3f49024,0x26883bcf32050cd6fa48,0x20e8f204135878057408,0x682690f2af90209a2bf0,0x422c3b089adadf49047,0x14507fa4291133d6dff,0x48c226aa4d07fe8ba911,0x67eeebc1014337fc0913,0xbe822268cb1366a014a6,0x387f39708fa0889a83ca,0xca4101537a4f9c15e214,0x5a6dff89bf81449397ca,0x4be568038a9a27849695,0xf366768cae211e9e6931,0x26ae59f72a53001c430d,0x4d1602890f6f92161a02,0x240974044d549acfe51,0x89a359bef1c050cdff,0xa950ef3dd00a95be55e0,0x50ed5dd20a170e74ed00,0x11050de7fc2ae8220205,0x95e5fc2a91202a737efd,0xa2771017e4e58ae04ed3,0x200f40890e2238a0e282,0xba6b2c0863447d6b0ab5],#[0xa3113467ca30a311347,0x2911fbb0d108b62e7d93,0xf20f08c44d14851f6c2a,0x54c5ebf020ec08c44d6d,0x2fbe40814309fd05a050,0x1fc844286923ddf0850d,0xab202029ac7819826249,0xf02042c8f819826271cc,0x90bc59fe301014deec,0x486ebc34c0252d3fa7f,0xfbbd0e80408727ff3b78,0xa0f000533cf940b66243,0x2d989cf97dd850be48ff,0x5004683d6ea81495ad38,0xb3c00062c337c2849faf,0x4840087a3e774da92e7f,0x55339f5c1b3494476ff,0x8afeca31a810d57de9d4,0x117c6a08000a6e669450,0x422bfc2839f8c48e009,0xa0cffa4d100014ccffc0,0xf8b0819b3fc3cffb8081,0x40204313a356c102183f,0x9fc478490c129fdff77,0x8c1a301021cbf1d09033,0xa1fce96b59b890005453,0xe8290010fafff3c0c210,0x5054d3f89d0101235fc5,0x670c7e4a8019fefece04,0xff416222670ff416222,0x379a128507ff1c380086,0xd59bcc4c2478d100332b],#[0x3f580a29ff83d5080021,0x667e0c0a0ccfc18145ef,0x2fbf570cb667c1700114,0xfc34a11811137e988005,0x2e0b1617e834008be7f8,0x13034b189f32b000a657,0x470fee80052c7ff09555,0xe3800668b8999a20014d,0x8493ec019580053574,0xc8f0d3ff60ec0044438c,0xa2dfe204ceffc211810,0xfc40a2877f1028a1dfc4,0xdd44509172b8c3494b6a,0xdd6b8808d73d40001892,0x214311f57f90138180a8,0x2206f8388008697272b2,0x121d3de3428ffe03bc01,0x58848e400442efc0101b,0x679bfd8c1d400014e2fe,0xfedd30614357f4a69500,0xc13680014fde2c00caaf,0xac86153fe23884cd5781,0x65c5f1448000c5b6ef,0xe89991f6720021739e5,0x245be667266143365f0,0x5415290d4a891f7f84fc,0xdc0f53db888002a3dffc,0xbf2be008c01e7f019332,0xfe30600ccaf1d861410c,0xe79ea285b7c2750021a3,0xd0f80483861367854a0,0x400888e44db53b0344fc],#[0x72e1bb1854ba2727a4da,0x43a6dbd84d5bc5a0e286,0xc8ff845c2014c533bd81,0xb27014d6f83ca1d2021,0x90fb82497c4214251f22,0x3393f6688440866fe481,0x2fdcb81014bde1f17a10,0xfc44e0405363e7c10217,0x20297be3ebc840ce47f,0x8cacffb2b8204349fd57,0x116ff5a61c252d7d7f9c,0x3245c1ca1290c7d63813,0x883e74112df0906df0d2,0x2159f8aea840861f3a0,0x4485cfe1a206557fe0a1,0x40866f2c5103303fcdf1,0xfe7e95c080a5d7fdd50,0xcab104088e7e6e485081,0x412979f679402161f8e,0x1021bbfdb59206683ecf,0x855bfb9714252f11f96a,0x14c2fc521210df57040,0x71dff7020437d99e6141,0x945758004391e47b8252,0xfebc401183d6c00cb8f,0x9cd5cb60010d0d3e6142,0x57061436ef008a11f64c,0xde8600cbde8600cbcfa7,0x15372f3c0b0d17dd0587,0xb4ad3c161a1ff4e8514,0x143ff922426677d14001,0xe353c20120d7e71e0003],#[0x7d7880231be9900085df,0xb0251fb80891fba8019a,0x4d3ebd201187ee0225ef,0x3f003d8216af81e20701,0x95f891e196de2e480454,0xfbbd2002955eba1d2021,0x63fe82204fbbd2002944,0x244ec660d80c5279a1b6,0x7bfc161220865b578435,0xe38fc460c0530da95c23,0x59506667fc9ee6400887,0xcd014b23e0931cc4afe2,0xca832c7c2c8066e3ff3f,0x21aec0ad8d8885377c7,0xcb6177b200a5b78bc447,0x78ad8a052dbc5e223810,0x4359579547d76a9a349f,0x6d0d7f014b8fb7f988e0,0x3c4ad9ff37541da22226,0x5313ff27c680a043b869,0xe77c93814b67d1881044,0x7488205307fbc320334d,0xc1029bbe2788419aa4be,0xfa3b122c4014f3459503,0xfdb9680237e8b28045a1,0x2980a3c42beb1005383,0xd6eb390014c67add6720,0x111864a8f5ddc800a833,0x16c9814a495de0bfc55c,0x4c0a513243f8aa053699,0xd00c49713bd0217499ba,0x8a162b3fcc18043d2f38],#[0x8029e1d1b91eef0021c0,0x5776ef408543e6d9b901,0xd78ded0149cb86cd00c4,0x78073101ffb60822810e,0xe50118c46d2982b2a4ca,0xf0ec6021abfae020cba3,0x219990baac1da02985f3,0x2187ff435328124bf860,0xffa1a9940936dbfc8070,0xde2b02100fad84b014a3,0xdfb4e40a58f720c0419e,0x400c407bb03aa821bea,0xc8149e79bbd86ca55df8,0xf7529dffe90a0296e2bd,0x100fbd88b40a573420c2,0x85d38c32033c0f991803,0x819c050f46195e562394,0xc0cbc8be0e042e7d107a,0x380a5cfc7b02ca99fc3,0x5c0cce8be0e042c1fc2d,0x3e95c0cc1c1b50658fc1,0x5c2257e95064377093bf,0x5f6fc12810d1c341641c,0x2c085bb3bfb5c186029e,0xf6282085f62820848782,0x1fcb1c0ccdfcb1c0cb2f,0xcfcda9c085aedf5c0ca8,0x6a29408683fa3947014a,0xe10d2ac124fbaa1303ff,0x706b845f7f82cc82177f,0xa39ff06bc11e386b8195,0xffc15c0cff3e1050e018],#[0x8118c43383ec580a58b7,0x6fce11ca4835b08bb3e5,0xdf88d014839ff073811c,0x33dcbb84a87c488e522,0x7c4a831d211509e520f5,0x8f3ec11b6bd7c408d86a,0xae9170655faf0a7b8246,0x823a3e917ebc298e048,0x908773a5c703d8680a7f,0x9319ae60223dfe65bb9b,0x29a5f6ea93010ceff87,0xfc2d6b200a673160f571,0xe158680a5ef8f4a8329d,0xfe14e04349c2b0e524df,0x6180540bf3434085d49,0x5343fb78e420dfee0b06,0x9fa6b611eaffe510200e,0x18680a7ddc2650118c5d,0x4be8bf343408693a1874,0xfff21a91824d9f00c701,0x4339bffb04a178060448,0xc4fc7e0ac0864ffa2c08,0xb3d43403149f8fc15810,0x6a0cf93fa32202b1446,0x3aef83062e904245bb1,0x7dd5e002916f93b88aa5,0xd9743a60189058f96552,0x6ea8285a22224e30f8f0,0x4300a727f82a410b8ffe,0xa543fb0bdd49d6f7c927,0xcb1db9af019bcfed1140,0xc0194121a43b2a72c4e0],#[0x52f5fd84800528765,0xfffcc04128004465fa19,0xf0fcb442043a91fa08a8,0x208ecff188ce208110cf,0x69affc9304881a37ae39,0xfd0904acffdf1f26e420,0xffc2c668084089dd4fb5,0xd1034572e2926206857f,0xff8a9e24440d3dfd3309,0x4089978ee77183081131,0xe8a142043e3fe1739688,0x87f7fe009a85121cde4,0x90c10405383fc98aef04,0xdfff686800881a4effb1,0x4c0a129b9f6490b810d,0x7b84824266de8819a0fb,0x1498408718de8d209133,0xff208ca303be0989afd4,0x18b17ffc19f0405341fe,0x9bfe7e5103350eaf3020,0x1f996020297bfb3c4819,0x4f304c4078358a82043a,0x45ff8ee04dc1840897d8,0xa102275f3899b1a81022,0xb28541022a9e8ebe2890,0xc235b8610229dffe19f2,0x6ffd911a9903423ffb3c,0xd0e80408797d18f44086,0xa2066938cf1082433fbb,0x10357becf02042e47f5f,0xaa1d0081129f24e90d68,0x5fef0ed935081a75f4c5],#[0x9134fff4c4caba008113,0x3c4208c8c24feb8ac400,0xf954204340702e240cf3,0x7020435ba32702043436,0xf08244beecca242fbed2,0x860010ddf3f0019708da,0xc01912fc620c0a96dff6,0xa69be8276800a628f,0x6054b7f0204d97fd1184,0x1953e675e06623fd34,0x43d7fba850019cbfc1,0xa54fc7c80021f5f18f90,0xe57f10001899c47e0019,0xf91460033d7e3f490019,0xcafff267bc42b001139f,0xa2508000a9cfff47000c,0xa1c1faac0085abf0651,0x3c7f0400cbefc1fc1881,0x5e8ec002161db8b34004,0xa0de8008687cc6288a1a,0xf86b508527e4b0008557,0x1f3d82357db9bc8019c1,0xaa77fa008bb7ffa008c3,0x2a00eb89abf4811040,0xb048004371fe94620028,0xfc881357df3cca852ef9,0xbfb12380241e5cc88149,0x4c67c08019a735fc408d,0x2ba08218bf847e701003,0xf47002141d5e004273cc,0xcffe002129e5fc80a118,0xe13f305016233ff00108],#[0x471b8402437f0fc0400c,0xfa253b901348e3c2011e,0x5f79d80042ef0ec48d4c,0xa7087720034b3f830008,0xabd9f08a5983801aa4bf,0xa627fdbc2e0080088,0xfc230e102a63bffd0288,0x8643a9e008ea57e022a1,0xffd02020a195ff4080c0,0x10048dfc808816fc0c94,0xa8022c8f3a8023cfc627,0x4f7bf60265fb23a047df,0xc04c97b583a049b9cec0,0x9b3400873c32760293de,0x865e3181e804837a97,0x1dff969000433bff2468,0x32d3c3f0c0a0be1dec0a,0xb4022c8ebb4023c43d80,0x2468fa40466e2c1649f,0xdbf1b04ae029a7e313a4,0x22e1008689f2180000c5,0x93f3beb1480c30551cfb,0x6536eff2b942ae9f4046,0x20435bfe022042d79e00,0x88b1921810153aa13fc2,0x27008cd01e8ba32f1f1b,0xd5292113be9fba466efc,0xe8819a1d1edd50810f6f,0x7575f2720804886ff9e,0x1010b87f3ac694a080a7,0x826247e7f08119b9f571,0xfac09c2f484a395fb84],#[0x10b57fb3ed5158029cff,0x88e1b7d5b041a35daae0,0x14df598302943f588284,0x1a0520c0f5e116facc18,0x94400d535d0d604743d0,0xf4ff812880862ff1e014,0x3199fb40501fe82c444c,0xcca049333f680a0fed01,0xc380086beb3680a521fa,0x20588dfec1e26507ff1,0xe34400cd3d4692280fde,0xf143dc2021cde6045091,0xcd3c01959ff0c04285e7,0x6182a8e7d9b12804317,0x6132966f12ddf9df58a4,0x29e7eb43d80482fb4,0x919b4000a77be47cec22,0x82a5a9f58f0400c5bbed,0x2b10be79d8019a0fb3c1,0x5fbcea1e1005368e02b6,0x240ffeb3164024efc804,0x6890b9859907ef9fe2d0,0xcd6028e7f172831010e7,0x414153e19f945b010d7d,0xfc18141ae2403fc6f970,0x3ae3d008a667e0c0a0cc,0x624068dc69224acf5402,0xf6d121842144657fb7fb,0x8489901ff83218468617,0x2192ffcc4a944000a78f,0x2121c60042601f8e100,0xa1dfc40a2dfe204d0e30],#[0x14b6afc40a2877f1028,0xa5aee3006513fd28a,0xfec212fc68002a02fea8,0x925ba88a128677e028ab,0x808dbac57011befa0002,0xeafee76cc54c088dd6b8,0xf548004340df95910010,0x20010b037fc4c0086875,0x1882549fba40021e137f,0xc83ff80ef0048edc0580,0xefc051433bf014069eec,0xe3300656cffa9b13350c,0x2015c800d5311a5f0470,0x67f081448f100462fedc,0xb3840a6187a30020a1ca,0xace1029afe3ece50a43e,0xff18300665f95f00460f,0x8da75d891887c005871,0x221a3fe30600ccbf2be0,0x4315f8281526bf8a1ed,0xcfdea28019850fc160,0x8a40f893b0292eff2caa,0x9230a250f02c51f5d2b1,0x9f81a1f0090efe55a754,0xc8c8024a5bdeed4302a6,0x1415241e62de7520fff2,0x221cc9890b9f43279fe4,0x257e87810cccfec17282,0xb0286db385932f73d86d,0x2976fff6e2a0294a677,0xfd5a7e8e40aa7f3bda4d,0x212a40377e44e280a633],#[0xa8d083410f51a30fafce,0x2220876b7b04194bff26,0x5ff83a05020d16f9ff16,0x419b4cd8c23039bc0108,0x18aa6f52af4085cc63f5,0x7428fd0940cc67ffa388,0xfc46b81a13fe34540cd2,0xa3842407f8424033237c,0x40658bf53e2a02967e30,0x152a8215d972021034fa,0x5c0860fc672cf7c0d14f,0x36047e362103535bc5c7,0xecd11a160e6ffc621c05,0xf1dea02938ec7a80a4f7,0xa754102978ff6625014b,0xf68e4aa5f14ea82052f8,0xdde2a978e354cd02966e,0x11447fbc164014a8418,0x69ec088afe6c028b4231,0x304018ce7fe2686186a,0xc8ea85d7a3a047d1e267,0xbe66f65491607e3f3354,0xbaa01866a7fc3f940865,0x7fe6452c067f7871d094,0x910fffe5d46938c27449,0x43addfd60465c636290,0xa305080536bffc54e144,0xfd6b02309fe920d4827f,0x87a3bfd8614944044c8,0xf205944044b3fb15c288,0xfe398016901a41ffd1df,0xe1a7d2032869f480ca5],#[0x60bb860c7417fc545101,0x40653fb1097dfb960fd1,0xd81a05207977b09d3c0b,0x99e5dec2733c32fc2723,0x4e33fc00521bfe181042,0x7fb99e002901e4f88821,0x367c6604317f9701e606,0x8ddc120c7e19e00c416,0x867e0470f9705d40675f,0x10a033af840c1c0922b,0x340532f8468e0480f97,0xbff37081683401bbf1a,0x14e025fc6eb397a42aa,0xbcc0a8334dffe110220b,0x84863fb9a3a700102aa2,0xdd5050b44444cfc68518,0x59ce088f3f285b0f1ffc,0x295aa1ed54052af5f414,0x1522f886029a6c0ee460,0xfbd84a010298e3fca135,0xb159e87653c28b370910,0xe04341fce342347e96c4,0x62471287420ceafcd980,0x1d2620b06944e8f1419f,0xee52fe2a8354219514fd,0x50805fa54b1fc535698c,0x8f0b2254e4b210ba5889,0xe145050817d2d289ca11,0xb4ccf3f2a58309141d99,0x217ebc2cc581263f4b34,0x4fcbb160485faf03c581,0x51ed1860152be5d8b024],#[0x37e8b6851b90f976bb8d,0xf0c486321069a1de25c3,0x60224bf86370d4083497,0xa1902aa21e2e28ffa9cc,0xa55b71a202a62a1b5cbc,0x303fa68072550fe7c1cc,0x900a991d50018657f2c4,0x37fdc0662c043f181f6f,0xbfc700a607f9b9c58086,0x3a96f9022800c600cff2,0x3f308c07410e10777e14,0xb68001d989fa185af434,0x37a0bec236f400fc2357,0x13c454bb0907843bbf0a,0xbf9e01f70489e88bbe09,0x17117770489e22eee090,0x4cbd84ebfea2061fbda1,0x1384cdf062433b78c2b3,0xf4aa5698e23d1404cfea,0x9f6ea1602c77708f6dce,0x890e5970b0153cb84510,0x5196eb9170ecb182b522,0xd21cae2a9812b876667f,0x16941d6a417268afded0,0xcd1e0e164bc2aadbe387,0x2b8a6d1deae1303e1548,0x896e6c2acac5f1db3099,0x2bd190f079dbcfb963e1,0xf8f5d8e2a9a4395c5e01,0x7e68e776615d7973b8d8,0x985a21ccc05696cd091f,0x836748e7132d9e1a39dd],#[0xddd0b719057be24ae745,0x4bea3c3fe34183dad4d5,0x243920eb5242d295c3eb,0x5b8d95895252bd195d6a,0x76e2e1005295c263a15c,0xc1b78f48c65c1b5adcd3,0x613c2004d850e4e3d1e5,0x39b34964dfb1a03b2993,0x2c5e5a4ab662b1d0e5f6,0x9cadd4382e2f961d295c,0x6a782eecd0b52fbff819,0x9658e74d17bde2c8a15d,0x7fe3da4407b9ce1adf54,0xde783d3c188c85571912,0x18a9bb92a43125662430,0xef4544b8862e20dedd22,0xc73b34617d5458b27e17,0xf62386274f06d7c7c30c,0x519b678512c4ef5a4ddc,0xd5897bd89f745ca5482c,0x119bc64b17ad8e552a4f,0x2587e392c2ade392c389,0x3e5d4843c8a88d898bca,0x1db61e9d8c65eea57b7,0x1e176a4f2e7102ed4a43,0xe3c519e1b113f5a710ea,0x6d9ec42b586fc9ea512d,0x4d870bf1051008c5e580,0x71eaa92af71eaa91a705,0x2af]]
set_option maxRecDepth 32000 in
def g255H9 := limbs80 #[#[0x840420cc44405000d040,0x400000304100324000c4,0x30028300104400404c00,0x411050c30c1000042082,0xa0430531880052402970,0x1010410000c140b14004,0x811981840060a0041002,0xe600e4670424344070d2,0x4600000680009f84114,0x510c30810007071c0180,0x13932a77800180000,0x540021e685c000000000,0x12800028000000000001,0x7277cc3ac00164326400,0x17e48325cc0007040d9,0xf4a40021c94695ab70c0,0x1aa2935b40028505db2b,0x30045be4753b8001399,0x41c43400059c0022140,0x1300012c50dc0000166c,0x279b1c21f0000068002,0xc00000308a75c0032480,0x36540000bc0036e042,0x7c00031c40000027dc,0x4396f800000347383c0,0x81f5a400156a0b51072b,0x3864028000002534002,0x35017ff58c0005400,0x29e87a6b53831ec00378,0x78003340000002268001,0x20940011ce23888a0,0x13d76845c10235a7c400],#[0x3060c00000104a098001,0xd47a3aa6252212500005,0x5a00000024677773c279,0xe03e61fc54c75125e0e4,0x178b10c00219e65f6473,0x2314f800075457400000,0x28340015f5544001666,0x302786a7200000000,0x22a000068,0xf12095cb3a1817270000,0x15af33f5f80037a83ea7,0x121800149a4866bf24,0x5308c36434976e6a8844,0xf0080028900000000031,0x383800009312f62b18,0x7a3391e839d2f5353190,0x208000052c6dd62c1,0x1f74dc0001750cd0a826,0xac00128814c448001229,0xc000000270a0f929a7,0x5222040000017c84b400,0x180000026a63c934671d,0x1d400036380f4c74f57,0x0,0x14000000000810000000,0x52440030b00002114436,0x2dd78e3340022846ed51,0x264c492074003,0x18042d05d400115c0,0x16e5946186f400000000,0x1c00119a0840000fd510,0x3ee17e1950f00026742],#[0x348069082c00326c40,0x4d2f000000323c003749,0x28586700000003b78,0x1de7f83940033fd31000,0xd000355d69800244e856,0x127e6d80037f44ec0006,0x82b0ac00040804c00120,0x180967c003022030556,0xc5280026f11b11ac0000,0xe23dc00000000148,0x482940001480031d94d4,0xc7d156d5ba0640000016,0x36c00273d4b32ec45a34,0x9400330e09e060112225,0x237a1280000027036108,0x37e945069400000000,0x33692e400363c000000,0x306c0000,0x3335b00017b800000000,0x2277368c00001187302c,0xc38d2a40017307b06ac3,0x1340005ed1e05d150646,0x1c00360800142400211d,0x23c72e00000024463cd3,0x237400387c0031b400,0x672740000014895df760,0x2b724e2780025,0x8404140016a058243000,0x15705c3162,0x80000020a14b80027380,0x59a4076e558a3d138731,0x15fd65a07137e0590cb],#[0x366c2340022d932c0,0x4cb7870387b40003d800,0xec71400057c50d254881,0x1833900030477,0x2a80036032b972c18662,0xcc6606310ec000000001,0x268a4600400032,0x26c74f00004bc00,0x20c0000014a36e8410,0x55900000000003b27900,0xb90d16d65514db54b3a,0x1563986d7da05c4977a7,0x40000000000000033001,0x340c10a35e2c32590d,0x7c0023d75e228f034000,0x3f76c800167a3bd7,0x68400274451a74c0036b,0xfc0031241f8001758001,0x16fc0000003277652fd4,0x53d5242e80038775f33f,0x1f03f66800000116a4aa,0x963788f0a70533f981a6,0x2d582400241b4ad57b42,0x8984b4cd00e5e911a306,0xc00000218847c0007293,0x6b971335507e14515822,0xf80030c701c5c74d0559,0x17e34c00004e400049c2,0x7361a00021a400000,0x3943c0000000002c97bc,0x36062af7a21435874e95,0x1647940001b80016cd86],#[0x2000069e3167400001bd,0x201945400000151c5604,0x8228840000015097d400,0x21d05e4170650003,0x94e33711200f40540000,0x30e800030]]
set_option maxRecDepth 32000 in
def g255D10 := limbs80 #[#[0x55110545105411050110,0x5c110595105911058510,0x611105d9105d5105d110,0xe111061d106191061510,0x50520e1d10e1910e1510,0x58120551205452054120,0x5c120595205912058520,0x5d9205d5205d1205c520,0x61d20619206152060520,0x585315513154d3150d31,0x5cd315c5315953159131,0x611315d9315d5315d131,0xe113161d316193161531,0x54540e1d31e1931e1531,0x59140585405814055140,0x5d5405c5405c14059540,0x61d4061940615405d940,0x58d41585415514154d41,0x5d1415cd415c54159541,0x61941615415d9415d541,0x58d435514354d4361d41,0x5d1435cd435954359143,0x61543605435d9435d543,0xe1543e054361d4361943,0x5855050550e1d43e1943,0x5c5505c1505955059150,0x61150605505d9505d150,0xe1150e055061d5061950,0x5515150d51e1d50e1950,0x5cd515c5515915158d51,0x601515d9515d5515d151,0xe015161d516195160d51],#[0xe1d51e1951e1151e0d51,0x5d1535cd535955359153,0x61153605535d9535d553,0xe1153e055361d5361953,0x5d15459554e1d53e1953,0x60554601545d9545d554,0xe015461d546195460d54,0xe1d54e1954e0d54e0554,0x59560551605456050560,0x605605d5605d1605c560,0xe1160e056061d6061560,0x54d6150d61e1d60e1560,0x5cd61595615916155161,0x615615d9615d5615d161,0xe1161e0d61e016161d61,0x5d16355163e1d61e1561,0x61163605635d9635d563,0xe1163e056361d6361563,0x5d9645d564e1d63e1563,0x6156460d646056460164,0xe0d64e0564e016461d64,0x601655d965e1d64e1564,0x61d656116560d6560565,0xe0d65e0965e0565e0165,0x5457050570e1d65e1165,0x59570591705857055170,0x61170605705d9705d570,0xe1170e05706197061570,0x54d7150d71e1970e1570,0x595715917158d7155171,0x60d71601715d5715d171,0xe1171e0d71e017161971],#[0x5917355173e1971e1571,0x61173605735d97359573,0xe1173e05736197361573,0x5d97459574e1973e1573,0x6157460d746057460174,0xe0d74e0574e017461974,0x6057560175e1974e1574,0xe0175619756117560d75,0xe1975e1175e0d75e0575,0x6117660d766057660176,0xe0d76e0576e017661576,0xfb3ee7bcefe1576e1176,0x7def7ddfb7f5fe7fcfe9,0xf5fe7fbff7fafedfbbf5,0xfeffdfdbf77def7ddfb7,0x7bef5ddfb7f6debfd779,0xf75edfd7f9feffdfbbef,0x7f6bebfcff7fefbdefbb,0xbbf6febfcff7fef7ddfb,0xfe7fbff5fe7fbff5fdff,0x59428099208fffffdff7,0xd970a0be58282d960a2e,0xbe542e9d650b8be5c282,0x7d750d8be5c2e2d970b8,0xbe58367d760d8be5436,0x207935482e48d80b980d,0xe9a5d4ec71742482649e,0xbe09928080e51700b923,0x4c82e491813904602648,0x9b609906f03e45340b92,0x4003d58400f5510002e4,0x18003995003659000d95],#[0x61008e65c005d8700176,0x61c02c565008ee5002f5,0xb97008e65c025f870097,0x76100ef56103bd5440e3,0x8975038ee500e5f84039,0x8ee540e5f8503976140e,0x4c175013055004897603,0x11661c043796010d6580,0x8a564023de40085b870,0x229594085b840216610,0x64d8401a95d8083795,0x8040de44101598028566,0x5c1e159607856541e159,0x9803116180c339203056,0xe50181598049061c1215,0x5960805e5c1817960605,0x5e60141598050565c201,0x17940697e401a3b90068,0x856542217970685e541a,0xc17950705e501c159708,0xa056582415950905e581,0x28ed710a3b58428ed410,0xa3b5d028ed640a3b644,0xc28ed960a3b5d828ed94,0x10bbb5442eed410bbb65,0xd02eed540bbb6442eed7,0x950bbb5d42eed940bbb5,0x54436ed410dbb65c2eed,0xd910dbb60436ed610dbb,0xb61036ed640dbb55036e,0xed850dbb59436ed940db,0xbb65836ed860dbb65436],#[0x6d15409ba5c426e96109,0x98c65826319509b45d02,0x2abd540aba5c42a31970,0xa8c6582abd750a8ce50,0x3033970a8c65c2a3396,0x50c285943033940c2859,0x5c3031970c285d830339,0x750e0ce503881740e0ce,0xe504033960e0ce543881,0x1740b0ce442c3397100c,0xc6582cbd750b2f5942cd,0x33970b0c65c2c33960b0,0xa85d83233950c8ce4432,0xa33910e8ce5c3231970c,0xd0ce583a81760e8ce543,0x3ced900f0c65c34a1760,0x108ce583c33940f0ce44,0x3e3397108ce50423391,0x50f8ce503e33910fbb64,0x5c443394110ce4444339,0x911c8ce50463391118ce,0x65c72a9651cb6550723b,0x9541e8ee447a3b971c8e,0x76147a89751eb65907ad,0xb1541b8ee587a89761e9,0x9e507c17981d2559074,0x25961c2c5d470b1651c,0xd89e54764d871c09e587,0x7849851e0ce487895761,0x2085e448215981f85660,0x8041872005e5c821796,0x52105e44841798200566],#[0x548617912185e5c84179,0x913317e04cc17962185e,0x5d8ccc5653317e10cc3b,0x5943705e60c6916531a2,0x5644de15973705658dc1,0x15973785658de4965378,0x85660d2917632afe48ca,0x81791360ce48d8179834,0x805e5cd817943615e48d,0xda15973805650e015913,0x3885e58da17943685e44,0x14e15963885650e21591,0x55511595541594550ee4,0x95444f84510565d54159,0x97558565556159155a45,0xe1d46458751a8e494615,0x59456056455833925411,0xae4d523b90548565d581,0x53935485e45525f90548,0x856455a17955485e5152,0xa6d7571856555a159456,0x705e61ca6576728ee41c,0xdc159577105d5dc15947,0x730ee41cc6d757205659,0x9de15957785645de6576,0x2738ee41ce159677905d,0x59d0199773995d9ce339,0x967805651e015917806e,0xe41da1b9574a2e41d215,0x5947885645e22b93768e,0x854c4ee1431385655e21,0xa56413b8e4c4ee17313b],#[0xa95944e5b8413966104e,0x43797138d65c4ea57613,0x5215d054e153153850c5,0x5485751516e105459841,0x120de58545b851516614,0x448cd74123359048cd54,0x5120a654485385121461,0x1c4853861214618482b9,0x97120a65c48538712146,0xe504a538412946104a2b,0x18712ad5d44ab565128a,0xae5c4a29971294e1c4a5,0x2b941594e10565184158,0x8ae54565385159461456,0xc4d84130de444c797615,0x61361058159814056604,0x5e17961785e545e15981,0x19856586615951985e5c,0x45a1598148ce48521597,0x61805e50601598169261,0x586815941a05e5c60179,0x9817116185c15971a056,0xe4c622b931885e605c15,0x7971885e546217941894,0x565c6a15951a856506a1,0x17961905e54641794190,0x56586c15951b056506c,0xcd79423355d08cd55423,0x30d65c8ca57623295948,0x92857524b55509237972,0x22ac5948a37962496614,0xc8a2597229361c8ab175],#[0x62589e54964d852589e5,0x14981598240ce4890757,0x932705e409c159826126,0x6189a17972705e589c17,0x7902785e609a15982691,0x5e549e4f942785e4c9e1,0x17932805e40a01797278,0x85650fe17962805e54a0,0xc37903b0565cfe15963f,0xb215d0ecc1543b16e0ce,0x4f84392c550e45b843,0x40056590049754005651,0x8e6498639ac5d0e61597,0x73992e1ce649873992e1,0x4d0215904088e5ce6219,0x97408565902497540856,0xe1cf445863d08e50f215,0x3923e85e60f415983d10,0x5e48fa17903e88e54fa3,0x4b953e85e50fa17933e9,0x564d0415904105e5cfa,0xc17903f0565d04159441,0x185e58fc17943f05e4cf,0x61594418564d0615904,0x5c915957215945c85659,0x15c9564570565d721595,0x55794e0d5e16985713e1,0x616665765985a615e916,0x765d056557415945d05a,0x595604f84580565d7445,0x7845885a61601d965824,0x1e1d6245875887e55629],#[0x65765a07e5d621d97589,0x856417616985a1061d68,0x645765d856557615935d,0x907e5164a392590565d7,0x644787591161d6493855,0x5a8de456a1f97590765d,0xd7815905e0ce496e1698,0x75e115d97815945e0564,0x556c1f945b29e456c159,0x945c0de457067875b07e,0xe457017905c10e1d7027,0xf945c132517017935c16,0x56417a17955c05e51704,0x15955e856517a15935e8,0x85655fa41757e85651fa,0x64f84791d5d1e415967e,0xf05655fc15947f1b5d5e,0xe86d757a1d5d1e815967,0x7f90e19f01b957c0665d,0x9fe15957f8564dfe1590,0x47c92e15ee33927b8565,0x520015938005642001b9,0x947e0de45f8159680056,0x64e0215908086e5df827,0x1532f056560215948085,0x35d0bc4d542f145ccbc5,0x15972f05658bc15952f1,0xb35d0a2cd64288ae44a2,0x2299628ad5d4a2b56528,0x894e1ca25187288ae58a,0xa62b91298ae5ca229972,0x298ae54a6cd7429b3550],#[0x4ac2b97298a65ca69976,0x52b33590accd542b0ae4,0xd8ac2b952b14e14ac518,0x75292c594a42b962b1e5,0x61ca427962909658a4b1,0x797290965ca44f872913,0x965ca895762a09e54a82,0x4f852b93614ae27972a0,0x89e58ae75762b89e54ae,0xa47862a92614aa33922a,0xd85660b049852c05660a,0xbe17972d85e58b617912,0x2c8565cbe15962f85644,0xb215982c9061cb24586,0x72e05e54b817912e05e6,0x5cc015953005644c0179,0x962e85e54ba17912e856,0x658c215953085644c217,0x97547056511c51734705,0xae450c159747056591c4,0xb565430ae510c5384430,0x856451e2b93421e5d90c,0xe159647925d51e496547,0x2a45d90abf92428565d1,0x1223964408e5d0a21974,0x4485661124586448ae4d,0x1183392460ee41181798,0x44615e491817914617e4,0x512015914805e5d18179,0x944685e451a159748056,0x6512215914885e591a17,0x594630ae4d8415964885],#[0x565d8c457663056558c1,0x159163995d97e4f845f0,0x565d8e457663856558e,0x1591640ce49883b9062,0x8565d90457664056519,0x8a1791628ae4d8a9b936,0x6485e558a17946294e4d,0x21415956485651921591,0x6818565a141595850565,0xda161595858564616657,0x76820ce4a08159685905,0x65a18159486056461865,0x591868ae4e127b938285,0x564536159586856521a1,0x15974d856593649654d8,0x135d13815934e0564138,0xa15974e056593849754e,0xe925953a4d744e856453,0x2615974e856593a49754,0x4989e4d2627914989e41,0x9242391491d5d926b165,0x7490865d249176492fe4,0x512a23964a08e4528239,0x984a856612a45864a89e,0xe453217904c8ce493217,0x7974c85e4d3257924c85,0x564d3c15914f056413c1,0x17904d0de453415974f0,0x5e45345b914d1624534,0xe15904f85e593417934d,0x8856593e15934f856453,0x9a15976885655a215916],#[0x690564da415906909e51,0x5a6159769115d9a41595,0x769915d9a61595698564,0x45a815906a0ce499e159,0x976a115d9a815936a056,0xe51a097946587e459615,0x7936805e45a017906809,0x5641aa17956813e51a01,0x15956a8564daa15916a8,0x905da2a15958a856462a,0xc15938b056422c15968a,0xb856462e15968b056562,0x1c15968b905da2e15958,0x8c0de46266576870ce4a,0xa3015938c05646301590,0x48a1de521e1b91878565,0x4e3215918c8564232279,0x916e15e09ae15958c856,0xe09b015976e05651b815,0x5936e85641ba23956c15,0x565dba45766e85651ba1,0x55846f1560dbc31906f0,0x15641bc55876f285d9bc,0xc55946f1564dbc55916f,0xf85645be3b906c9565db,0xc015976f915d9be15946,0x700564dc015917005641,0x5ac1f906b0565dc04576,0x6d88e55b693956b07e4,0x4db657926d85e45b6179,0x907092e55b617946d85e,0x651c215937085645c215],#[0x5968f856523e15918f85,0x56524015939005642401,0x15949085646421596900,0x56424437918e8565a42,0xc1596910564e44159191,0x1856424623958f0ce4a3,0x481594918564e4615919,0x9485652521591948ae4e,0x2541b979289e524a1595,0x59505652541593950564,0x56561594958564656159,0x93960564658159096056,0x6425a339294056565815,0x594968564e5a15919685,0xf5d802fd6400bf5d8001,0xf976013e59004fd6403b,0x986140a3d9601b259406,0xa618702ab5d80a3f9502,0x5a35d8103f97028f65c0,0xc617607985941e61760,0x48f65c0c6387032b5d8,0x14617608185d8186386,0x509bc594263f95050fe5,0x1826f17609bc61426f17,0x740abc5902af18709bc6,0x6582af1760abc6502af1,0x1740c3c55030f1970abc,0xce5c30f3950c3c5d430f,0xf1840e3c59038f1540e3,0x3c61438f1650e3c65038,0x8f1960e3c61838f1950e,0xb3c6442cf174103c6603],#[0x32f1970b3c6582cf1760,0xebc5943af1910ebc5d4,0x83af1860ebc6543af185,0x40f3c6443cf1980ebc65,0x543ef3910fbc6583cf19,0x751cbf5c472fd511cbce,0x5c46efd611ebf5447afd,0x1861bb25d46edd641bbe,0xfe5c6e3d971b9861c6e6,0x3f951d1861474dd541d0,0x375507c3f971d1861c74,0xc61851f235d47cdd641f,0xc376447061861f0fe547,0x76dd971c3765870dd761,0x1f986187e3f911fb75d4,0xc8261762098e44826198,0x1218fe54803f912018e5,0x90ccfd61333f504cc639,0x74313e5c4c4f961313f5,0xe18c461863132594c4dd,0x387311861cc43d963118,0x8e10c6ad64318f65cc46,0x618731ab5d8c63f94319,0x8fe5cc63d973198e1cc6,0xe3f943398e10ce8d7433,0x398e18ce618633b2594c,0xdc3f97350fe50d43f963,0x320fe44c861763718590,0xcc86387321861cc8ad76,0x5340fe44d03f97320f65,0x18d0618634235d8d0c96,0x983418660d03f963418e],#[0x5d8de3f97358fe44d662,0xf91368fe50d23f913498,0x8e50da6391368fe50da3,0xdd74503755140f971501,0xf655406385502b59540,0x23d975018e1d40618750,0x98e1142c95450be5c54,0x42618750b25d5423f945,0x520fe5d423d975098e1d,0x5483f945218e11488d74,0x55218e15488d75522b59,0xd1443f91510fe5d4e3f9,0x87511861d44c97551375,0x661443f97510f65d4463,0xd65528fe454a62985118,0x86614a3f955298e154aa,0x3f9153185d5566298529,0x98a614c6198530fe514c,0x4f9617118e45523f9154,0x118e15c48d757137551c,0xc4638671235d9c43d957,0x7198e11c6c954718f659,0x9c6638671a35d9c63f94,0x472bfe41ca3f96718f65,0x95ca3f947298e11caad6,0x957298e15ca8d7572ab5,0x595dc6164770fe51d43f,0x965720fe45c8fd907218,0xf659c8638672235d9c8c,0x62987218661c83f96720,0x18e15cc8d75730fe45cc,0x6165778fe45d63f9573],#[0x623659d08d947423645d,0xd28f91748fe51d83f917,0x150fe51da3f9176a3e55,0x448e565123e59454f964,0x7123965848e576123965,0xd84ae59412b95904ae59,0x6415b965c4ae59612b95,0x65456e56515b965056e5,0x38613325944ce59615b9,0x8e14506185140f6584c6,0x6187142b5d8503f95141,0xfe5c503d971418e1c50,0xe3f961798e18588d7616,0x998e585e617617985945,0x52f39214985d86661651,0x149861c52ad76148fe50,0x85a3f97148f65c526387,0x618185d8603f961818e1,0x545c3f9417185d868639,0x532318e58643f96190fe,0x58c92f95324be5cc8cf9,0xd7422395cc88f96524be,0x861888c975223259488d,0x6187220fe58883d96221,0x98660883f97220f65c88,0xe618523b75d08edd5423,0x39861c8ead76238fe548,0x94dd54250fe5c8e3d972,0x25235d8943f952518614,0x8a6198250fe58946186,0x622b75d88add9322b764,0x9496dd9325b764096dd9],#[0x92240fe4090dd9625b75,0x61c90ad76240fe4c90f3,0x176270fe5c903d972418,0xfe549a3f93268fe409a6,0x61763f98590fe3f963d8,0x3e590ecf9633b3e50cec,0x4dd6439395cce4e56339,0x90f658e4c97539375d0e,0xe46387391861ce43f963,0x3918660e43f97390f65c,0xe863843a32550e86298,0x73a2b5d8e8c9753a0fe5,0x5ce83d973a18e1ce8618,0x943b98e10eec9543b8fe,0xe18ee61863ba35d8ee3f,0x2983b98660ee3f963b98,0x85d9006164400fe58f86,0xc97639b264ce6c990399,0x8fe4cea3f903ab2658e6,0xa61873aab5d8eac9753a,0xc0fe5cea3d973a98e1ce,0xf2c9903c985d9028d763,0x3d0fe40f4c9963cb264c,0xcfa3f903e8fe50f43f93,0x55c985d17261545c8fe4,0x515ce573573954d5c617,0x955718e155cdd7457375,0x5cd5e3d975718e1d5c3d,0x38457ab5915ee78357b9,0xb5d95ec975578fe515e6,0x3d975798e1d5e618757a,0x98a615e6198578fe5d5e],#[0x63f945998e1166ad6459,0x98fe5566638559ab5956,0x7461545d18a616661985,0x7d2be556c61755d185d1,0xde4f9917918591fa3f96,0x47937551e4e563793954,0x55e4638579235d5e4dd6,0x96790f659e43f95790f6,0x645e662987918661e43f,0xf947998e11e68d7479be,0xf659e6638679b2595e63,0x62987998661e63f96798,0x8fe51ea63847aa35d1ea,0x63f957a98e15ea8d757a,0xa18595fc61647f0fe59f,0xec3f907b0f659e8c9657,0x7b18e15ec8d757b0fe4d,0x5f08d937c23641f03f95,0x7b98595fe8d967c2359,0x51ee3f937bbce49ee3f9,0x967ca364df28d907c8fe,0x54cb43f937e0fe41f88d,0xd542d395ccb4e5632d39,0x8614b4dd742d37590b4d,0x61872d18618b43f952d1,0xb95d8a2e591288fe5cb4,0x2e58728b9658a2e58628,0x9b9614a6e57529b965ca,0xace5652b39644ace5872,0x2b39618ace5952b39614,0x8a4dd762937644a4e596,0x7293761ca4dd96293761],#[0x1ca8dd852a375d4a8dd9,0x852bb7594aedd912bb76,0x658aedd862bb7654aedd,0xf972a9861caa3f912ab7,0x7650b0e5932c0fe44b03,0x63862c18618b0c9852c3,0x18a60b03d982c18660b0,0x661862d8fe44b63f982c,0xd98644b63f972d9861cb,0xb661962d985d8b663912,0x2c98e5cb661972d98e58,0x4ba61872e0fe54b23f91,0x12e98644ba3f952e8fe4,0x58ba63952e98654ba639,0x8445395cd1463962e986,0x5d514c965450fe511461,0x187450fe591461864532,0x85d91c6164470fe5d146,0xe58443395910ce591431,0x396590ce58643396510c,0x8ad7642325d5083f9142,0x20f65d086387421861d0,0xe3f98420f661083f974,0x43b76110ee593438fe45,0x90e618643a35d90ec965,0x843986610e3f964398e1,0x45163f984398a610e3d9,0x8645b25d516c965458fe,0xe5d166187458fe591661,0x991443261d0a6176478f,0x265910c986443265110c,0x3f9444b9e4d123f9144b],#[0xfe61123d9844ab61912,0x86187460fe51183f9146,0x698e5d186391460fe5d1,0x1a3f96468fe511a3f914,0x46986511a63914698645,0x584639646986591a6394,0x45f0fe457c3f97610fe5,0x1d7cad765f325d57cdd7,0x975f0f65d7c63875f186,0xe457e62985f186617c3f,0x1985f8fe557e63855f8f,0xfe458061756398a617e6,0x62986018661803f94600,0xabe45823f97620fe4588,0xa3f95628fe458aaf9560,0x3186120c63956298e458,0xc3f9583186160c3f948,0x850fe5a0c618683235da,0xe043f918118596146164,0x6813259604dd84813964,0x5a043d968118e1a048d7,0x98810f662046198810fe,0xe16063f91818fe620462,0xf98818f662063f958198,0xfe560e6185838fe460e3,0x3f96839861a0e8d76838,0x3ce4a083f91821859616,0x3f98820f662083f9482,0x4235da103f94840fe461,0xa8f91828fe5a1061868,0x84b9e4e123f9184a3e56,0x12c61814b0fe56123f94],#[0x64b325d52cc9654b375d,0x5d2c61874b0fe592c618,0x654b9860d2e61764d8fe,0x5d13061764e186192ec9,0x1864c325d530c9654c37,0xfe5d3061874c0fe59306,0xdd9349b76412661764e8,0x3261d24dd9649b761926,0x8c9864a3264d28c9904a,0xa8fe4d2a3f904ab26592,0x2a3d984aab6192adf944,0x4cbce49323f904c8fe61,0x5323f974c9861d323f93,0x34d186413463974c98e4,0x559a6175689865934619,0x9065185d5a63f97668fe,0x661943f93650fe45943f,0xf97678fe459e62986518,0xfe45a0af9565abe45963,0x63956818e45a03f95680,0xfe56206185881860620,0x23f96881861a208d7688,0xb1861a228d76889860e2,0x243f9589186162461658,0x8b8fe5a24618689235da,0xe1cf392870fe421c6165,0x6898fe621c3d98870fe4,0x561e8f91879861a268d7,0x948a0fe4e283f908a23e,0xe45b23f976c0fe5628df,0xf976d0fe45b43f976c8f,0x8e45b63f916dabe45ac3],#[0x3f948d186123461818d1,0x9860e363f968d1861a34,0x83f948e186123861868d,0xf1861a3a3f968e1861a3,0x3c3f938f3ce4a3c3f908,0x9218e0648cb958f0fe52,0x64a3f959218e16483f91,0x3950f642543f959298e1,0x52546184950f64e54618,0x90950f656546185950f6,0xe164c3f91931864e5461,0x385938fe464e3f959318,0xf6425a3f91940fe564e6,0x3d94968f64e5a3d91968,0x9864e5a619196986425a,0x501651f405d86e619496,0x40e44d3016433c05d8c,0x49019750c05d14301755,0x51406554901855240551,0x5c5019453406454d0197,0x622405d889016471c059,0xd8e5016525405d48f019,0x843a405d0e9019639405,0x65ce901873a40650e901,0x3903d40640f501643bc0,0x595e503933d4064cf50,0x1907bc0615eb016479c,0x406458101862c4064def,0x50193654064195019460,0x140618c501961fc0e541,0xd1018633c0610cf01873,0x50c0660d101963440618],#[0x14901945240611490194,0x552c06454b0191514066,0x59c901867140615c5019,0x96254065495019722406,0x650ef01983a4065ce501,0x1933ac0640eb01963bc0,0xe50f501943d4065ceb0,0x29857c065d5f019457c,0xc0a6167019559c065167,0xb01547ac0659e7019479,0xac0655eb01947ac0611e,0xb101962c40651ef01987,0x43c061d0901644540660,0x517019843c06590f0186,0x75f406457d01756140e4,0xd58701955fc06457f019,0x6583405920d019860405,0x662050196814061a0501,0x17566405960f018581c0,0x59621019865405d59d0,0x1968e40652390165894,0x4064e3d03908f406423d,0x103948f406523d03938f,0x1c200ab002f800a0000,0x8400398019500ae00490,0xd00c000588028d012580,0x20080f4c072c0368019,0x4f802650128408e20435,0xca05bd02c8015880a540,0xd4a0679032f018b80b,0x1de40e94071f037f81b3,0x2a820a40fec07ce03d30],#[0x8047882358115c088d04,0x9b804ce825d0128c091,0x52a0a5d05128280c13c4,0x8016500b05057502b101,0x301017c60bae05c682d,0x65f8325818de0c530619,0x7d06ad834d01a140ce50,0x40e2e0700037501b460d,0x1df00ed1075583a101cb,0xf501f4e0f8107a683c50,0xa8419c208c1025080183,0x896043d021aa10b7084,0x26609088473423021165,0x6c136d099d84bb8253a1,0x299e14830a1c0500427,0x58ac2bf015a50aac0548,0xc805d002df216c10b3e8,0x90c4c0614c303817d40b,0x19ee0cd30658c326218e,0x6541ae00d52069b43448,0x6438801bf90dd106da03,0x876903ac81d2a0e73872,0xf7807ad43cf41e1f0ef6,0x100fe687e5c3eb01f350,0x2210f10678825c40ae20,0x447e220510e18862c429,0xe4c469c2301115d88a18,0x20929048de242c11f108,0x12f0096644ac62528127,0x726136e89a504cd22626,0x98281213ee09ea44ec22,0x452bc291c14690a22450],#[0xaa1c549a2a1514ef0a6b,0xd08adc8566e2b0315690,0xa16410b12c581e2bdd15,0x2d67168f0b3f059aa2ca,0xcd22e2416fb8b6f45b3a,0x205e222ee917590ba2c5,0xc0285fbc2f9f17bc0bd,0x87f0c3486166305c181a,0xd918d78c5d46288311e1,0x2328e192d8c89c640631,0x676e338219a28cc5065a,0x24468c8343b1a098cf7c,0x88d5846a5434f71a5c0d,0x1b338d8b86c1035cc1ac,0x7391b870db9c6d82368e,0x5a37f51be60de806ec83,0x71ca38ab1c440e17470,0xe6f4732e39601c950e42,0x618e9e474a83a1f1cfb0,0x61dbe0ed2876443afb1d,0x3c5e1e128effc77aa3ba,0xa903d141e6c8f2cc7910,0x107c3a3dee1ed90f6287,0xfc5c7d963e971f380f9,0x150ffe87f603f871fa0,0xf9206f102ec8118405a2,0xc41bf20c990584827040,0x8528426f211b9081883b,0xd90866e430a216f10acc,0x91102087cc43b221c890,0x22689125088e6444e221,0x59f22ba915688a684507],#[0x1646412308117688b844,0x88eae472b237d91af08d,0x212c902c47d823d711df,0x971242091b0489e243b9,0xb250f127a89364497d24,0x4b03256e12aa894e24a4,0x7e64bcc25c812da49678,0x7c996a4c85262f930a49,0x135d89a9e4d282683133,0x730138d09c0c4dbe26cc,0x2f278413b849d624e8a2,0xc4fd027ce13dc49e964f,0xa12650722828140809fe,0x5bca2a251142869942d0,0x894854a3dc51c728cb14,0x297d94b40a5425269291,0x3c129cb94db0a6845316,0x6654832a2895040a7de5,0x8aad4553b2a8695378a9,0x59b8ac8e56192af51569,0x9895c0cadaa56b32b459,0x42be495e90aefe57562b,0x58952c3696108b03657f,0x2d659442c8616394b186,0x98b3f059d02cd296620b,0x16b6cb57a5a962d33168,0xdde16e44b6c45b352d87,0x8e2e3717124b84c5bef2,0xc5d302e8197384b96a5c,0xbc265deb2eda17600bab,0xc6cbdd25eac2f3f17940,0x317edcbf285f6e2f9e17],#[0x30399812cc05c60072ff,0x137308498388c18460a0,0x4061eb30db98630c2d06,0xc5aa629831371892cc4,0x8f20c7466372319e18c3,0x51991f4c89a641c31ff1,0xb329e19454c9ca64c232,0x660132f419704cb4c656,0xd80669533399994ccc60,0xecce946726337d19b74c,0x9a0acd00267de33cf19d,0x47e9a36cd1726887342b,0xc034d31a600d2b469243,0x6a5d351c1a84cd3d069,0xd6426afb35659aa98d50,0xf5cd76a6b9535b81ad50,0x29b1a0d8966c2435ff1a,0x36b81b4c8d9e86cab364,0xe48370e9b7c8db7c6d97,0x1c6ee6375c1ba5cdcd66,0x8dfd66fae37ae9bcecde,0xc340e130706a381d9c06,0xd91c608e2a8712a387b1,0xf39319c8ace3f471d338,0x7346398f9cbd4e59c729,0x91874433a081cf30e6fe,0x8eb1075453a7e9d344e,0x9db88ed1876383b049d7,0xbfb1defcef0e77453b8b,0x373c7a9e304f118783e3,0x67a0f3ce49e664f2d679,0xf6247ad73d539e998f49],#[0x6cf7d87ba63dbf1ed40,0xb1f3ccf9767c7c3e269f,0x3efa9f6ccfb0a7d563e8,0xf153f6c9fa74fce67e39,0xa7fd23fd21fdccfe827,0x501668081402da00c900,0x7090330814a4085a039,0x68a0a7d04d4823d4106a,0x41c420d4d064e830341,0x84aa422ea108107c083b,0xb6e858342aba14b909da,0x650d2e865f4317a17cd0,0xa1eb50f0e8740438621b,0x4692226d10ce881443ee,0xd244d622599125688f84,0x68aaf453b2292d140489,0x173e8b6b459da2c1115b,0x1c118708c1545f1a2f09,0xb234b519f88cc7465223,0x4716237d91b9e8d9546a,0xf3b478aa3b851d628e70,0x5e8ffc47eb23e551ed68,0x921e490c2484da41d120,0x47d92394919c48aba44b,0x82a4b652542927849202,0xc49e224e6d26ec933949,0x94cf4a5525189286c940,0xbd695b04ac1a54f929fc,0x652d0896574b21a58652,0xa5de12e6496fb4b6b25a,0xc482615d305497e84bcd,0xb04cb7264e131f698c34],#[0x29a7c4d27a685d33d899,0x37269b634d8ca6bb9357,0x24138d89c374e04a6f89,0x5a75713a589d034e6b27,0x4f20a783d3bc09db04ec,0xf424f8827b493d5a9e75,0x1e9fdd4fdba7e4d3ed69,0xd417ca08f502d280d540,0x86cd4302a1585091a83b,0x64a8a5944dca23250f52,0xd51b8a8d114630a2ed51,0xa48f52222904547d2a3b,0xab2a52f5281a93a14970,0x654c68a60b52eb296a14,0xa9cc54dfea6b45344a99,0x420aa0354faca7a453bb,0x2c547f2a3655148a8705,0xca9e754dcaa60152b8a9,0x55f2aacc5550aa961544,0xfb55772ab8f55ad2acc1,0x12b3955934ac6f56122a,0x57072b7495b2cad5e569,0xf02576a2bac15cdcae48,0x4afd657d62bddd5e72a,0xd6172b0935836ac09d60,0xc6ad6306b15658882c39,0x6b2ca2d6486b21258eda,0x659ceacdb96674b2ff59,0xb4a95a372d1156828b3e,0xb32b55d5a962d3f569ae,0x496ccab6415b052d7356,0x2dd416e54b6ec5b5fada],#[0xc1aae0156fb4b7ad5bbe,0x1a5c77ae2f1712cb8705,0xb9c35ccd2e5e17296b9,0x759aba855d2d2e8bd73f,0xee17722bb695da0aec89,0x42f175785cbc065defae,0x5e98af40179aabcb95e4,0xe2e5effaf71d7b32bd62,0x5abf055f66afa697ca2b,0xd7fdebfbd5fc4afd5d7e,0x50581fcc0c76042300d,0x64b0a4d845ac1f360d03,0xb61dfb0dfd867ec30961,0xc528626a311e98862c3f,0xd36c6456302b16c18ac8,0x318f74c76e639331b918,0x3249591bcc8916425b20,0x539328ad93e8c9ae64ac,0xba65bdb2d0995fecab06,0x4cc966630330ad97f4cb,0x9b4ccd6b6697b33d1998,0xb619d54ce66670e337ad,0x633de19eaccf2d6782b3,0x683db4109a02ecfe267d,0x18b68a4b4459a1d2d0b6,0x74d288692d34845a38ed,0x9a708d35b699ab4bf9a5,0x51d5a898d41069f6b4eb,0xd535599aa56d4e16a55b,0x6b4b35971ac3cd5da6a,0xd7626b9fb5c65addad6c,0xdcd8436bfab5f25af2c],#[0x5db344d9576c7d362a1b,0xb6a55b4d4da3b6d04b67,0xdd7b6dcdb64edae86d61,0xed6e52b71b1b852dbee6,0x4ddf46ee2b7615ba76dc,0xbdeadebd6f4737931bc3,0xfb5bf66df7e6fa6b7c6d,0x638375c138e06a701837,0x711cb87f9c358e16c709,0x38c71a838c29c59ce28b,0xc6e4a3722d3907dc7a0e,0x5cc26e5cb72c3394c1c9,0x9d31cdf6e6b673403994,0x5b3a1b5d05ee7cd73c3b,0xe74c83a515d240e8ea74,0xeac275463a905d418e9c,0x7baebb875c4bad29d5fe,0xd1d976ec7e761dbb019d,0xbb791db50ed77769a3b3,0x7893bb85dd46ee637713,0x977e5bbe69dee0ef3f7,0xaf0a97842bc149e064f0,0xe39af17a78a43c429e1a,0xbb1e56af27b791ebc845,0x83cf05e716f35d7995bc,0x7a61bd229e8a2f42579f,0x5c47ac03d541ea54f4fb,0xf8f6617b233d855ebd2f,0xdee38f6eb7b69bda51ec,0xe181f04cf7d17bcd3dd5,0xb8be4f9f1fef8cc7c46b,0x47d12be7e9f386f9ae7c],#[0xfafb7d663eac1f50afa5,0x79cfb977dc13ed5df658,0xcdf912fc597e1a3f025f,0x3f5e1fa72fd137e6ebf2,0xf37bf8e1fc24fddd7ed6,0x567f963fbedfda8fea97,0xb000f7ff0bfeedff02ff,0x23f00e18056c01c2007,0x8b203df01c480c640536,0xf40c9205d902ae8134c0,0x82414110a07c503a381a,0x5bc82c3415160a1904b7,0xdf06b0833d418f20c070,0xa0f7d078e83ae41c9a0d,0x22fe11150853841241fc,0xdfc261e12a5092584784,0x985474298a145d09f484,0xb8785a842c9615e70ab,0x9d70c8b861b42ffe1779,0xfe1bfd0da986b8c34c61,0x43d421e1d0ebd8742438,0x8534418e204b0fd287cc,0x3288f0c468e229110ed8,0x51338897cc4b3624ef12,0x28c1142a89f3c4eca270,0x5762a3714e48a5cc521e,0x3c59362c3115d58accc5,0x8bb1c5cbe2df716c58b4,0x8858c25c60662fbb17a0,0x6d19798c9e463fa317f1,0x634e91a528d18467e633,0x6dc6368b1b158d6bc6a6],#[0x38c70d2380f1bd68dcf4,0x98e92c73e239911c9c8e,0x1e338ef8477023b111d5,0xe9f1f0a8f6f47aaa3cc7,0x2a402b1fe48fda47e0e3,0x4842a41b520b19042481,0x11c487a24345216f909b,0x51919248bbe457522889,0x5242691f8c8eee46f923,0x4a812513926fc929e48d,0xa424c9b25f592ddc95ae,0x2c9e1a4e6f26ed9362c9,0x9462ca25a509f280c93e,0x9c694c6ca56a525928f4,0xbd2aa09536ca8f653ff2,0xa57a92b9595afcac5655,0xb45659bd2ca59633cb05,0x134b7c25b792d8896a64,0x3978b4bb665d2d2e6097,0x304198034bf465f292f5,0x31731449887cc3226117,0xda6503324d98fc4c7066,0x4ce9a66df33399976cca,0xa67cd26668c7343099f5,0x59ae54d5da6a8b350d9,0x736e29b56cd9ce6c7f36,0x6fe7379c9bbdcdd226e2,0x4e271e938ac9c314e096,0xf4e982742939d79cc7ce,0x9dc44ed52762f3ae29d4,0xca39e38cf0ea781f3bd5,0x1b3d579e9e4f40679a53],#[0xe7cdd3e3b9efa4f6fe7b,0xfdee7e8d3f0b9f634fa5,0x4b5018280393fe09fd84,0xaa0b5d04a681f940cea0,0x427da124507fa838b419,0x7694362a19a50bd28565,0xe898b448ca22250fb68,0xd18aa8bc3458aa2a9d14,0x3b2d1c7a8dbf46a1a332,0x8da42b520ae8fdf47afa,0x34972a49b523e6918948,0x95454a5aa50c5275e934,0xf26973d4b5da58952b6e,0xbd32de98cd4c30a5fd52,0xa6e8536729acb4d2ba67,0xed5a755539a69c654e01,0xb34fa5a7b6d3ce69e0f4,0xea1595077a81fd401e9f,0x487ea3a95196a8a6543d,0xacd4c92a5e952bea9415,0xdaa2755066a7c353a5a9,0x559aaaaad543aa9a5549,0xd21565eab19d57faab9f,0x3aaea55725ab7a55b0aa,0x561c2b07557faabdf55e,0xcc0d650eb20d58d2ac51,0xcbad4956926b41359cca,0x15bc5adcb56d6ab6355a,0xb9e55cadae37d709ab7f,0x86ebbc55d9faeb3d74ba,0x1d7bb6bd835e7faf29d7,0xb003d7f3abf235f4faf9],#[0x120b07758306c1156049,0x6561f6b0dd58622c2a56,0xac64b62e5b14f5898ec4,0x912ec80563c5b1c958d6,0xacd94a2c9cd64b4b240d,0x4b31cd980acba36594b2,0x675cb39559bbecd4d666,0xff6845b403d9f5ecf33,0x6d2a56923b480da326d,0x5aa0ed4916a03b4dd5a6,0x5cadadaed65f6af6b560,0x8eb625db05ad7d76bc0b,0x76d8eb6a0db3e6d98f6c,0xddbb6eb6b73c5b8c2dbc,0xf3adf2b6f6eb79e5bc5a,0x35c226e0b17020b7fcdb,0xb8d55c5dee28d7103b86,0x2ccb947dc99ee41b71dd,0x3173bdb9b65cceee6137,0x2ea2b74d6ba48dd13ae8,0xd826eba9759ebabcdd51,0x7dddb4eed5d766ebb1f5,0xabbe2dde6eeec1772abb,0x78c9bc455e11af01f77e,0x3dd79adbcb8de4eaf20b,0x7af62f7ac6bd42de8a6f,0xdf1fef8677becbdd0ded,0xec1df532fa297cddbe5b,0x5bbf15df7eafb917da9b,0x37f19bf785facefd017e,0xfffd7fd4bfcf5fd9efe8,0x3e301618084c02f600de],#[0xc606f70301814ec091e0,0xc17660aeb04e98240c0f,0x3e8c1d9e0deb06838313,0xcf84b6c23e6114708398,0xb0b9f8597c2b4e147709,0x1bef0d81868fc32ee185,0xce1f9f0f5b8777c3a06,0x6c47be22fb1133884ac4,0x8a03c4e2e263f12c7892,0x65d8af1c558e29d7147b,0x316f18b70c5b462d831,0x62e8317318b90c5c462e,0x5e462f0317718bb0c5d4,0xf0c5f462f8317b18bd0c,0x18c10c6046300317f18b,0x18718c30c61463083183,0x18318b18c50c62463103,0x46320318f18c70c63463,0xc6546328319318c90c64,0xcd0c6646330319718cb0,0xf18cf0c6746338319b18,0x31a318d10c6846340319,0x35031a718d30c6946348,0xb4635831ab18d50c6a46,0xc6c4636031af18d70c6,0x8db0c6d4636831b318d9,0xbb18dd0c6e4637031b71,0x6c1189a27851cb06e031,0x881a8812988a101411a8,0x3160130a82ec14301138,0x861b096158415a85a0f0,0x81a02b0e183e18330bf0],#[0xf0f4270e848e2784e0c0,0x307017014851341bc004,0xc0804e0287314c69c2c2,0x10907c224a4294191849,0x62883522028150834182,0x88180dc5206a0b07c1,0x3414752100907874268a,0x13c9188603683a1b0940,0x742d1a884046090326d8,0xe25ca316623424b7c3a1,0xa8351da391e421224108,0xda08761c07846c9f43a1,0x78146748e190361d12c1,0x34801511c4c870578113,0x91940e02c31e0a224860,0x12098047d1735a1e0011,0x1098b0206138811c3638,0xd1b86f2bd0da07022185,0xf0b445858661f5248df0,0x22284932893402092021,0xa2e0b3494b645a251e84,0x96385f8c6241dc71820b,0x35ccb0c8949cb01190d,0x5445104c43e1e46c1786,0xc669a068829c6b1ea88b,0x3c882c10450830110400,0xf52f2116e2b9624a0063,0x92849e1ec631885a2369,0xb920021ac43695a46709,0x2854400480f01f231703,0x74e9150e4554290fa691,0xa01b74506aa8d354be9],#[0xec2b84406028071fc6ea,0xb5f392c8a5a18d8757bb,0xab4772f843d0e9bb6314,0x2ed04c70d29f7322e9cc,0xfa1c3804995682ff2d07,0xb1cd008bd52eda18b874,0x870384637894873ca314,0x383b04b0119688865e12,0xad04f9225c581430c44f,0x4447197886cb9e2d04b1,0xbe5ae05d39956817cb58,0xfcc4b0475ea7f252411d,0x3195ffd930080761d7a9,0x727020530d1f4f4a4543,0x909f1b77d389002d0cf3,0x9fd6da3450bfdd5054d2,0xc10a8864fe125c11598,0x1d7f507ccc8021271f27,0xf66b99b1475ea7f312c1,0xe90c25127eb3ea104eb,0xf27d486ed231c5fc5140,0x9cfe442c310ad6e598d7,0xf1985572a86e7eed8910,0xdc1b12cd42c766a6321b,0x426e050bdf64961a4d98,0xd200594b0fc5161969f3,0x330b8c5f4aac40e1b3ec,0x57ec990803d0f6e0c4c5,0xf3ecd20459603da90c9e,0x2285ee36ecb2cad6e598,0x5e7eed8406616df998af,0x1985eda84c71fb348016],#[0xecb3251ee7268ed9a0b7,0xb0e0fbaa3442e070e1fd,0x32200150b4ff20128001,0xb5e4998f6d6302346a7f,0x5fd1060016875f1c0188,0x660348b19e0d6c1966b6,0x811a2f3fc86d800ae197,0xf030979fd5c001a855cd,0xe8ef5013522ce07221e1,0xd073d8062321b5c6a951,0x651ce300351c7b7801a8,0x88d7e5e0592ec0fd00b4,0x5da07955041d2cfe6c01,0xf4f8300c4747d1e000b8,0x300351d1f950002a177,0x3024a328fb8d00c4695f,0x71dc07441f71a0188d1c,0xa106ce6fea74c600348,0xb13309e3801a8c5fd813,0x296de80d8c8664f0404e,0x2d14f0f8144a3898052,0x85347ef6cd945142e1ec,0x75fec5688dbd860351c8,0xe00348737f8c41820948,0xa833143b80e886fe480a,0x1152ed4ec9b3259b0d01,0x32144319d1f1d7f2a8,0x5460a961f9e49b3261db,0xb367144030c73162c68f,0x275f6c1a098e1ae5f74b,0x4d7087b36d0c6c327c79,0x85e2b8bff6ba648104c9],#[0x234d0e6832741ac8a5a1,0xcc0a441a198ab7aa1960,0x662b0300d0bc543b3aee,0x7760b680e50145e3f04f,0x7412fafa82b487065dd7,0x74fdadcd66c76286188a,0xb7ecebbbb5220708c731,0xc231c45d32f7eda1ac86,0xd0ced130ff12f0878c01,0x34f5056b0e8faac70b36,0x2fa5da8d049011130cb9,0x5ddd30ec0b0248088b76,0x9cfa8ebf8114c8976af6,0x587078bcba2f66a48148,0xd028313b50016f36cd70,0xb8a23006398befa8ebfc,0xbd1900c91132fb3a5da,0x48204fa7ae0b0dac1c16,0x89627a13e3f397283133,0x286ba1c5e2f28fe31201,0xf1e5230063589b7aa1c6,0x897279948e34d0e4f159,0xc2088aa6ae777a890ba8,0x6d4821a6df0d57321048,0xf4f0795887680c2bf3a3,0xcb8b719d1e454a81b434,0xaa5db3ad8484e5159cff,0xe9ea9c6e6f0562a06da6,0x696bee0f10c420d61d7f,0xa95e744a10a90535e7ff,0x2096a6f7eaccc5481da6,0x30012036baa265ecca56],#[0xb6f77c952cfdff7e6ecc,0xed2c6179bc4431683735,0xdefdcdc15881da53fbf,0xd2826a0fafc24729962d,0xa78705b089e56fea0c28,0x414383786f4798d2096a,0x7429cc406d5cf7330a18,0x30fb38ce62096befe1f6,0xf694f44a10a904b52795,0xa904b516dd9598a90434,0xd1c8a903b4866d2f4645,0x7cf96dd81f24c2d39d7d,0x859c4522e6c537459c3e,0x7a2a40ed3efa45cce379,0x74e8ff114905a647e755,0x5a6178e32f122a99d4fd,0x4408d83e7c9ddfd0b490,0x1081a27bfef6ea2d8218,0x111497027fbe8d8e572e,0x2421081e290ff12466fe,0xd9c6d220589f7d1b1d6a,0x9ae7eacf644334738d04,0x2046acfff606d9222236,0xbc8886680fffb036ce22,0x3b647d15d042497f9fb1,0x6b8fe5e9e8f21a440ed5,0x819a5bf804f6078e2203,0xf4b144cb1e5fd3d95f88,0xff7b427744862046b40f,0x712f6ac080428cce715d,0x440ed45e5ee6f45481da,0x77c952cedfe5e5e8e61a],#[0x1c9d3ae8278a5862f2c2,0x210a587d7c7d90b042ba,0xd6d800cb3154f5f9f26,0x82eb59020a4228dd268a,0xffec0e810220469a7c64,0xff1b9d863200108822c3,0x8256984f80ee81394b2,0x9e15a8c1394dd7a9c98,0x3244e3173391e41470f8,0xc0861806ff1736be4021,0x37e531c0235b39bf7b0a,0x1a5199bffc9508280e34,0xe1f84b09206ed0dfa728,0x3909c463f209c60350cd,0x374554905c3f3ee6f9d1,0x1ad1591ebe42d40d971d,0xf21c28437ea8b8d0931e,0x53e4f1502a1c001e6281,0x8725ac92ffa0500009c3,0x4142a3f468a34006b0e5,0x5e0520000296a47f2af0,0xc2441b2a65a64cc8dfb7,0x4cb6f1dc8b4c20e1fa5,0x8ffe3c910068cedb2791,0xd9e48b65c26e6420a3a5,0x51f3a44724870010b557,0x5838e340351c77d4d621,0x620000216cae3c38a36,0x1c2bc933247ffff1f5e8,0x11a7fb8b9107bd68e215,0xe6ff033109c858b5ec03,0x6006a3abfcdf084001d0],#[0xc4222af3a1f1088cab5c,0xd4367fa521d40a33ceb8,0x814008061a95fb227180,0x1ffc6e8a0c4ad29f6e4d,0x51117cdfad99548ce6,0x1adc82d1a19b38aac380,0x7846430e3e08062327ed,0x6a38e3e080623120f937,0x8c1fc1402b669b9e080,0x6e1ac000786a77dbb857,0xe1e9e1e5c084ac337e8,0xfe9a8018908b7f9a1800,0xf680fb53bd84850ad3b3,0xf9100c46afd3e49d9489,0x13c2538f0f0e8425a1f4,0x8c8fc9f08421618df77e,0x91cb5d3049b2e9f22018,0xb9d3e2801c9133e70921,0x400c47d8e92fe2400214,0x429333f1400d479ff4d,0x3fe9a801890363afe280,0xaf300a452e397c584cbb,0x148a0f776f2a0005438,0x6100999c41f00a451ae6,0x478c3c04800c682ffbde,0xc5874212b0f14cf80623,0x84ac36fdb480311c907,0x315bc8e00c4677e1e1d,0x84f43935f87f31021001,0x9301f1806234b8fc2c60,0xfa27d222159eaed250b6,0xe8b084e145c65c20a85c],#[0xf806230b8cb84150aafe,0x11c2ff704c003394c049,0x341ac7848647df870803,0x9a0804000d0e04fe0062,0x216947e482010858657f,0x59b58d97bfeacf6f1000,0x1995d3755870002a223d,0x558f9a0168cdfd59ad21,0xac7cd00b4647e54000a8,0x14b5d7fdba8a005b3,0x7ccaf13297ae5f4a7068,0xd7b7f9a0d83200136acc,0xa00000288a5c33e806a3,0xb878e200d19f5fdb2414,0xde4ef522f99beb804ca6,0x3322bfd25108485dfe09,0xb800650f5e4998c3ebc9,0x913278d00d4717ff697a,0xee91805a3cec797ef568,0xf25e3d20d185aa08c1cf,0x6890d1d3471d1b3b5b19,0xba744137d806231de062,0x6e02d9a66957a43238f7,0x15b3669c20d0ad9934f5,0x8b19e114c11660e3b062,0x55fc84f4002e1a666018,0x103fd7001a651c4c0311,0x8062289fb80311979039,0xf4fe910cc6303388c3d,0xad8005b34bea08dc6055,0xaeec30150ff400c468fe,0x9067e00622c3ca800150],#[0x6757e0fc30000a1ae41c,0xc4808063145f1bb34811,0xf8dd9a408b3a3f74acb4,0x8c374bf2c02415014692,0xc13feda08a3fbee0b080,0xfda4090719a7feda00a2,0x2c8032690ffaa2029963,0x78d3e0d20459fa5fb720,0xfeda08a2a9bfeda08a3f,0x11668cadfe781502da27,0x62e7fdb41145cffa0348,0x2d14f17883501890100c,0x702c8069a230e7406902,0x51cb8d3e0d20459cadfd,0xd13feda08a2889ff6d04,0x5840461a3dd7f3c0a876,0xa05b447b348016507e40,0x6fc16101185eebe58242,0xf0812031698f669022ca,0x633ec46300d462f690,0xe8da87001ad198ffda92,0xcc18016cd073d806a337,0xe805a328e71801a8e1fe,0x87d00b468fd70289a743,0xbf2f03097607e805a34e,0x210480a02267f3600c46,0x5dfd3e0c0311c9043ff5,0x57c0c00d470ff68c00b6,0xf0c08016cc3ee340311a,0xc7d00b461f71a0188c1f,0xcb3f9b006230ee03a261,0xe0985000c678ff8e8016],#[0xf400f89944f1c00d46af,0x300c45ecf08d44136786,0x5c3d806229e1f0289471,0xece8cc00008c407f00b2,0xdcffd19980001187d7f,0x2e1a7f060062336f618,0xd1b0e3e805a343e0c100,0x60230e3b80e89b03f402,0x9b71a180170ecfcdb401,0xb81a6587f203e0330acf,0xd1006a1577472237feb,0x5e40566f7b43008a141e,0xc808cdef66701142c360,0x90986a4ff705b2770f1a,0xb6dcc804cf98fc6b3074,0x800c2fb8402f0024376d,0x8cddfd34c80099bdc9c0,0xbfe0272013377cc93c80,0x1626332e985c240a1a7,0x358ad1e1ceb57ba9225,0x232f7cc93c808cdbe3c,0x8c20a32d81e5a0c3c6b2,0x113c0390b9e0985b2361,0xf8568d2fc402409c29bf,0x29e622c0b58f0111d704,0x851c468f2228e1a461e6,0xc7012349818e024618d,0x30828cb8722311991e4c,0x985b273f00bc0290ad86,0x20314876eb96018cb9e0,0xb31b75cb00c6537f8c41,0xc83c80acd8ea06838fb3],#[0x1a582b660e41e4046586,0xbbf211d62030205abbe4,0xd72c03197add7edc0359,0xfe14c140a33b7f80cc6d,0xfc9c808ccdd72c031943,0x7026cb1fe566e08d9b30,0x43c7f0c932002676f4ff,0xbc1d005161e382292003,0xd18366f359379244048d,0x4a2fba9c0450a3c3e288,0x6617c40f00a42d87f638,0x6700fd4389ebff726403,0x8449825680fc7951c40e,0x346d3c53e560623a7b76,0x3e45dc2366aba5821052,0xc31a879f9da5a8a91e0,0x7f6c415054ce8fdbf9ac,0xf0685442367bef59192c,0x4ed2e61459a3ca80d183,0xa7fb82d923fb4a541133,0xa32d81e5a0eb48e20232,0x2717c40f00a42b618c20,0x288d18366f359003f503,0x1a41bf113c0390a3c3e,0xb859c7140b45dff004d6,0xbf061141ccc37bc22838,0x140b466ffc4825009b39,0x8202d967c0a05a2cff58,0xefa7d5a0e1039888ff0,0xd300e676a7f3b286014d,0x9c3f4f994300a678d655,0xdbd8a05a347300f46059],#[0xc8c4c973c76094300a68,0x220030d0fc802400386b,0xf1092d7f51032cbef026,0xf0c6832cd4fd1036102f,0x32022666fde9002ca587,0x15bbffd060800c3a7fc3,0x89246fde9002ca06f311,0x440d844edfb37014cd7b,0xc32fb0d22ec69fe2253f,0x64b72619250f02f7034c,0x112139e000057216d264,0x983eb0e010208e185e2d,0xffc3400784006203f7bc,0x7fde9042ca1fbde981d1,0x86d618b38e80fae0e239,0x328a4fcd60428d4347b0,0xd7c028c357b0ca28d5ec,0x91bbffa807480167420,0xe24937c21e1c45927c88,0x20c1c655ee3940146af,0x627c23461313e0ea307f,0x946d6c69461b13c268a3,0x3ed231811430989f0751,0xd0cb038ce8713e0e236,0x924fdc0246b6d1c25afe,0xa30d97c348bb1a7f88,0xc659305f805190835f,0xb1e7e9638f3f331b75cb,0x1aa606020b62f985e988,0xe5deb6ec018694ef8790,0x650fb3f9d3a08049a513,0xd9dbae580632b75cb00c],#[0xbe7cd8151abfe90a6c02,0xf074014586d389002cc3,0x4ff703b237f511a00b36,0x7c1889193ec1ac96c66,0x13b0ca28be2078052146,0xeddeabfa914412921163,0xb37479d7951c41e1a41,0xd330601c7192bff511a0,0xe7e0178052173e12d020,0x8e23462ff08006140d68,0x85959fc002700761809b,0x1a7e44d6e29474f80770,0x2a7fb82d931e0a49c006,0x43f0cce0ad9eb48e2023,0x643b7f87e199c15b39,0xfdab8005b323f47e4660,0xf8f0038cbb85e402d183,0x40c5055a370bc805a347,0x8199c206201a36763fc2,0xf1cbfc61410514b8fdbe,0x28b6413bf906042499f,0xc40456b8fe18bf052101,0xb5ea30348fd2fd0b9440,0x69fe489c2d04040a2d72,0x512b9ff1df3319410909,0x4808061accbffecd388,0xb43d8560470d1f84bd10,0xdbfff201c0a800d0396c,0xffe9f372140e240346da,0x11a425796229405da283,0x60e50248068d5b9f6b14,0x3434be12c2480f3474bf],#[0x4008105afb5fde85cc0d,0xe130101d1b03ed817681,0x5f1d69031494f8fc281a,0x30d4bfd85c0203093a0,0xc8302124f7edda881204,0x4ceb8d7a8c0d23a839f,0xf884000042d7902fa600,0xbeaf5c0800064447b615,0x927e1000049a55e85836,0x10a52ff8a9000ba417f0,0x30880059a55737f18c00,0x1183f9ec800d668f6d3f,0xfaeb8880055a87fc4803,0x52417dbc8800d66ef6f2,0xfee720022913cbf3e800,0x9a487d3e18cd20017695,0x2ffa406130f76bfc1400,0xc99c1027ffd120420a2,0x59f79f9703251986f8c0,0x25133fc11fd6c1a010a,0x280042952ff5d0cc2000,0xed3071c6806a3ec7dc70,0x42d35871c921c002,0xcf34471a01c905ff6214,0x142000ba407fb851001c,0x29a0cfefcc821285ff,0x1affaf990425141ab78c,0xcf16bd806a341fe280ad,0xfa440073387f3459001c,0xda00c2545af60188c5f6,0xcb99980245ad7c78ff2d,0xa956b8c00d47afffda92],#[0x8529ffffdbaa00000085,0xccefcc81c517fd7c6402,0x40073388ffb390004926,0x31bf5d20a0470c5fef00,0x407fb46005b29fb26069,0x7c100c46ce9fd5100063,0x2017692ffc0b981a661c,0xe402017692ffab60500,0x800c709808096d85f6db,0xbfd457f91481652dbb7f,0x51d3f94e814e880ced3a,0x4b75e98015334dcf0403,0x240009b48fc73100010a,0xcb9cd000010b4d61e729,0x5c3eb87c5a0c5c2b7,0xffc211000a34f3703e43,0xb67e86fa791108cf9fe6,0xac2040396b02ffd60800,0x8913e6a0062317f4f195,0x93ca1001cd1b3fe9a801,0x767bd9c54c880058b0fd,0xa53353e49ca44333829b,0xd97c40311aabbf834200,0x4000a34e30fc3a109486,0x9b5008800e5a8be33b36,0x8031234f9100c460ff96,0x4f9900880185ae71fd38,0x852a74f8a0072417fe5,0xffa6a00623ec7cbf8900,0xf1400214999f8a006a3c,0x9346cffa6a006246e2d7,0x14579805a2f570ed1061],#[0xa6edcc88005c345cc029,0xfceb300026871c3e0168,0xa450bf9c6ba00b48a7,0xc675f3cb974009a4cdf7,0x37eda40188f9fdb48800,0x13d0fa67faa4630807e2,0x301f1806233be3f0b182,0x200916ae2f19d210039a,0x98220041698feb7d3c82,0xd19eb2882068cf1ff7a6,0x13f80188dd9eb2882068,0xe100623e7aca20819b38,0xa3ffc69b00400c2d3bf0,0xdb0c0800e67027f00311,0x64feb2e34181001cb517,0x9963e6805a32c7cd00b4,0x8f08002e22bfeddd0029,0x14352e19f40351e58782,0xa003478ffb740d50000,0x8c2276336a802d2175fe,0xb8797835ffa788c10,0x933278d00d4795df8902,0xa460168e3838fe240024,0xead21c5207c2074d13fb,0x9bec0311a30d280c1e80,0x6a200416bdee5d005a38,0xe0eba0a15472ffca92ae,0x5081191da97ff0da0d51,0x332fe8504515bffe309a,0x8a5b8a15929be1c1078e,0xdd21425240016252fff1,0xa00369de392b101a393f],#[0x47d7b360394e74f240e8,0x9a3bd481c1d74142a8e,0x424086927a9045ff8834,0xa43afe85045177fffcc2,0x88868211aadfea08664c,0x8b66bb4409846fff6810,0x414d0ff873ac1d600105,0xaad0a99872b5cbc62810,0x86d7ce1e5720d143d7db,0xc42080643fbfb884100c,0xd7d92590100bb483f3d,0x101cda6bfd4512343968,0xf4a010014a2fc33f96ba,0x2251f90f750d28dfc63,0x931f0207a468fe805958,0xc692cff1e9b91918d879,0x56779ec18a178ccc5e40,0x4d7cfffca681588ce8d4,0x8200d45ee5259903a2,0x3335664d1f9fe8e129a2,0x94880e341bf12380390b,0xc0078983f3401458ff8d,0x953a1951d9cdfd850750,0x1c004a573f23801d208f,0xca29b3aecd4052ae3e29,0x481fd003ac034818fca0,0xf0aa1802c34ea57c11bd,0x2895a635f04410a92af,0x222dde41a8da3fa03456,0x281c4817e2040ae0c6d2,0x5d217c03202d947f781d,0xa347fd583b20dec119],#[0xa376dda409806cf2685f,0x8d262f6e4448d2685f00,0xd7f6941a23a5f3aade80,0x428ac30fef5b4a071207,0x47fa186b0cec313d7a30,0xa14e204cce14d1d60d47,0x5e277eb818a080c2487d,0xc00e1cdff848ea040100,0x20f8de0ad195bbfd5220,0xc4ec38ca3e3e10e200d2,0x5388334881419f80a911,0x800314b98438803489ca,0x21c56cd8ffc8c3690000,0x204ccf02d9f8188e50c4,0x231900040198a2fa4218,0xb5475caba906a3ebfda1,0x6d3a4561e6639fe1c7ad,0x8d1786325d6b23aee45d,0x62937fc05001842b400,0x7fd890130899c96d7b3c,0xbfa1411455caba906a3d,0xbad03491bff9e0d0268e,0xe6dfd0a91186798adc8,0x8011125fff454405331b,0x30a535b34a9ffb0a0e44,0x215279fe1489005862e0,0xa80d0b02693be63db858,0x1802488ffd106822cd3e,0x9974cecd0356818f83fd,0x7e0370052162149188ca,0xf34014598932ae05349e,0x2a8fcc3c3c3231968783],#[0x750885039b56fe1be14,0x2489d9fc4600811233a4,0x1846ca0fcffa90015048,0x2ccf0fcd86a44850fe04,0xbedc5c2165affea0cdd0,0x2e10b2957dba8130cda2,0x94d4fc3db583430d5f6e,0x6086238973f6e383431,0x9e01594e42a3e6ffb0d4,0xeaff3fe4700540289227,0xa3a1f583fc5b3a432b0,0xf5ae106b29ad903ffd54,0x1eda7f8acc486d61eee4,0x8805a1ed903ffd540a1a,0xd2f0fb0a2b4617b7d526,0x4ae849fe08fcb5b0a20,0x265a1e7f1c0021c47b78,0xe6071ae0530f0f2d0c52,0x3655f303d39029a49bff,0x1bbe78e4aa999bfd992a,0x1a031c600144c5d6b08d,0xf11a2ef843c468bafece,0x223cfcaeb58568fbe10,0xfd002a08063589880fd6,0x82942f8c74b0ad1f507,0xb43b7fd810611b35e77a,0x9bb60799e1ed919280c,0x7afe0201c90201535e7d,0xcdffd53880d44200c457,0xde516040b4ccde828551,0x19b67f72e0a091253c35,0x199a9408cd7df0c193c3],#[0x831b7d9b018a4bff2804,0x6f4142a8f3fe10a6a2a4,0x28909e1aef28b0205a66,0x6ccb523501a34fee5c14,0xfc88ae005866fc07495d,0xc8935f4868a3480b0d22,0x89542432b4f3e300d150,0x8a81fb535340f5a20cdd,0x1c5f11380290b2075cc2,0xfd60a51623afe8c52889,0x891a1ff21485a203a885,0xa4855d03e813481063c8,0xfa991fe1651b3e944720,0x4018ba8cc1fc08307196,0x46effea00d16818d0dfb,0xd67910fd8051a443f601,0x5756f409a457f002af00,0x18beea3ecfa51c482921,0xe5e0a91f0fba21451ec0,0xb487d1f49477400a4cc6,0x281b39d3244bf8004c61,0x938804ad6622ffbc34a2,0x2127c4002d9dff830403,0x9b5a9f512bffffd1610,0x80fc1d891080fc1d891,0x424bfb42268447fb5b8d,0xe17ce34009a925fda113,0xcb601f144cdcfc514022,0xd7f81c49c782340091a5,0xe2000022a59e7fcd9468,0xaa1b8f460000454bf7,0x5bf855c1230a8fff9d00],#[0xd42c1fcf50ca049d3,0x1113bd4f251151ffa0,0x50c252195f4eaf900630,0xc2f1ff31641550dcfcd1,0xb5f02305d4917ee353a8,0x8a01170d37ed00000d52,0xb513ad7ec41550d0fd42,0x33c537ea14f2fbe82944,0x2846af5de0d13e424041,0xe204a53037ff4698086,0xf00b18e41828ea1adbb0,0xa0f8960210084c0dfa7,0x538a6840120c6d8ffcad,0x67f9879cc5743b7e56e5,0xdebb1201a004184211fc,0x915d4349846d343c12fe,0x2ed04edf9585a6616f11,0x29f7c90b34857e777469,0x379ca37c69043527e8e0,0x64373e85fb91623ac3f0,0xa0a1041315cfa97f6f15,0x1404290841bf9f678c77,0x24482048bcff39d2578f,0x2798ae8707b42afe405f,0x3e4037882078a055f874,0x69b8403482088ca75c1d,0xf958546516f11e895fcf,0xf0669c81861040f184ed,0x2aff75c3b2123c4e09a3,0x4cf779759272096a8c7c,0xe2bdea25183f785891e2,0x11b15f822b42c703d081],#[0x788efff1f9cda0602188,0x17905a64bec925cb8109,0x434ee4209c87f893bbf6,0x4703d081a2742ea3ff78,0x68fc2c41550ccfc1769,0x268f94d980403482088c,0x60bfc49ddfb42e82d33d,0x891313535275ba0409ca,0xc170825a9e3ebdb4f607,0x2b49c6e342098bfb948d,0xc133a391a9053583f8ad,0xcc44bca2ca8c420e1c83,0x5382e6215f4eb9a0a705,0x3fcd01cab2181fc11cd0,0x32b567368fb2c681a439,0x19df96a488e153ffcd40,0x50600358737f2b0a488a,0xbfd377089041c3b3fe04,0x816249fc137100005438,0xbac42b383fd6629a4c20,0x34029241800698a6fc48,0x9fb3355386001e2269fb,0x3d40996637eae8026617,0xbc916ca5eb64926cb10f,0x4bb00b86a69205e1225e,0x1a32a7080400e6847f0e,0x7a0009c2d3f8f880002a,0x6b443f87b29400d21c18,0xf18e05218be3b7940200,0x89211fcabc1170a8c8d,0xe4ce6c012ad5bdd93f9c,0x63feec992004243f7e1c],#[0xd54fe58a004712003cc5,0x2a15b3fe49f97ab8840a,0x4f9000560ca5b6ee6c02,0x61b3ffa77358a18a11a9,0xfed80388c6ffb64fa827,0x49ff89a461d77dc4a230,0xc94fe61e683b40ea204,0xfff6e578891e682c3da9,0x94b006ace9fd6401a65c,0x12df8cf0c600533d7fe5,0x63473f999c1d0c2000e9,0x84001e224b1ffd924800,0x7e3a9ac02d1c9ca5f249,0xe231b917ff9474018da7,0xf80164a26217e247800c,0x668fcb00029967bfca74,0xdfb480014cd1efd40022,0x1b5c6014c247ac8034ca,0x3e7808d205ff7a0000aa,0x82d6dfb480014cdbbfc,0x9c2d7ffa634b504b00,0x8b72cc0600061a4187a0,0xa5ff62ebc0c1c400b16d,0x65a71fb82350900005bf,0x4e3f7042e2003535b7eb,0x4a52e45bc65800cda2bf,0x1fd42501394b27f212a0,0x5040351f7fcea0806a3b,0x80b1456df318014ccbe7,0xf7cd61940402076ab5f0,0x587ff78f04b320001535,0xca52eb8f96c400132],#[0xca6cf0055297d75e7ec4,0x7d5ff0b08000191035bf,0x28d6333ff4bc001449b,0x80056d99f4e2bf392480,0x4000cb587fa719e70238,0x978810a959ffcab56ce4,0x5ac86398068cf3f5a7de,0x7cda8322ae1a3328c8b6,0xd1d33fff5a9400074697,0xf5a00004c93bfdf1b002,0x89055c3427f2126cbbf1,0x6181fe8c601230aef9b5,0x720c007b42bfec952227,0x6ede88528002f121fcf9,0x2e19bfcde1c1800f6897,0xd103400876907f2c1000,0x71dc8a9bc0162da01cff,0xffe56c860014690e393,0x16d04effe89860087696,0x5a4ba726a5bcad40600b,0xe800a3165cff1261800c,0x2001cb56b93f0834308c,0xf96fd005d243df3e564d,0xfeb4fa22d80085a56f1f,0x96acf3db409d6206694f,0x80014e2f30fe08986003,0xbb4afd2c667fea98d,0x96a4e00145a8b25feab3,0xc7aea908042b4c7ff4c6,0xf8ad4cca910000b45217,0x341f3881c41000618cc7,0x3f6266109500106271ed],#[0x5169c7ae4081a002d35e,0xe1470bb1cbffb2fa00c2,0xd3c6944f800e6857f15d,0x8c5f7f9bbc68a1800c5a,0x569e7fdc4f58a530c002,0xc3002535a71a539cd622,0x440cc0002e11d38ebc0a,0xc00c2567fff9e046b795,0x3ce6600a8d53fdef1d66,0x63e4f9dc0d520bfbf4a4,0xe40c27ccb9513e0039a2,0x9c274c103680076d95ce,0x2227f7df86b340184a8e,0x7402c676747478c6400b,0xfe0131ac00b4d71fc75e,0xabb2e144f800e684ebf9,0x9132b5779eb469380061,0x8021da63fefd3cd309b,0x57f97041470a1ff34ccf,0xd3fac8026cb3cc789445,0xa803a34c7dbef95002d9,0xe247800ce21bf76ff2a0,0x95fe0730ae00b24da217,0x78892a7fbcf00100846,0x126005b3da6f7c920400,0x9de4c78185c0154a2f89,0xc34d7efefca88100856,0x20c9902b4865e5418a80,0x9fcf00c485a44457fe89,0x923198bc1ba08046cf2c,0x65f3e285301152878583,0x7bf5000899e3f2c000a],#[0x34cd57c2d0d00000553b,0xaa197af0b513a3ac80,0x470a1ede04cc94ff7a00,0xbe5f8170068cf8e615d1,0xc28617833e013800d222,0x6011a000622c5ec713cc,0x4604846d12affee95c0,0x9106fe21c1170aefd985,0x2cd1ba54b27f3c031216,0xd8ea66b340a93bc75239,0xea467c590e1a900756ad,0x4bf318054cca78b8cf81,0x1470b4dff885604233f,0xbd6e214f40846817fc32,0xf403c1170f8e62591450,0x47565fe3100029a1916a,0xa6441b357a7e46200053,0x80ab8688fa124d97bf2e,0xffdf029c002a88873525,0xa11470aabdce8b4507f,0xc30143ff1b89128cc0fe,0x8384abb89243f6180a7e,0x333ddc4926ff1d37f426,0x7744a2051694adbdd121,0xb3ffb276409018b4e796,0x806316df0809e4d039a2,0x9d275fe0f461a80c480,0x27fdb429475f1aea7d26,0x96797fca931202033102,0x4c48080cc4679237b481,0x959f009ed20859e5ff2a,0x33e38107eb18d1e9310e],#[0x300069945fff10000054,0x22a59fe07da0188edfc,0x24e8ff80014cbc7d4000,0x1528fff13600c473fc0e,0xb7f0c001a65e3ea00001,0x15433e3813a3fe000532,0x2081400d21c5fff10000,0x1365c7e9800270aeff9,0x34cb5fd2b28056cd5d70,0x30d9ff4000d32e7fd000,0x2f1e016c2509ffd24c15,0xc6767c5ee110c001710,0x7d400000aa5affc11980,0xb6117fff354c00691c,0xc3f3ff81c0000a86178f,0x81a01a8eeff9b108001a,0x1152e1f0300d465f3,0x8a173fe8001a6583e80,0x3fe0c70800470f2c7800,0xfbb4e0230a07e6006235,0x3306acf0feed380542c3,0xfb7fa517182e680ff4ce,0x405510901ff5e3046cf9,0xfee40808c2d3a1c0f829,0xc686cbe0d96818024d20,0xf13d20b47e0ffc330303,0x7696fe7f3502600a34e5,0xc5004cd5cdf9f4456c08,0xf841701cda7bffb34acd,0x8e6f1f841703b688e6f1,0x3009a27aa5aff27f0236,0x841200b442b0d1fde944],#[0x8feb98918289ba1d1f5c,0x315701e1a63ff0feac47,0xf7cfe50080719c36fe79,0xf0f03bd3ff2011405136,0x10ed2de7fb140202768e,0xe1ac0cd9c36e3fcaa010,0x7f9421eaac0156bafdbe,0x36986f8fc20b819b4752,0x59802e1dbf18cf400a08,0x71fe4560a0786987c992,0x321c1a13ede3011c3c3,0x8f665b40d6776ee3916c,0xed02d9d2233feb0299bb,0x6768f9b440661923b697,0xefa52013447f66dc8216,0xc33bece0dca076192338,0x93f874298600be0c7814,0x80d19c02f8118090b4f7,0xa7dca6e001c3b76ffa24,0x821874fff144901a33db,0x5df36f0519d48e087c0a,0x3100e149e782010e150a,0x3295c9578150470e4f3c,0xf916018cd4f9a1028164,0x12b437fe43c8b00d674e,0x12408c01589ecb92704c,0x1592dd28d001c3cb6fa2,0xbf3a43f0442988502923,0xe1dfe160ca290400ab74,0xda9f44e3050213597f2f,0xd012f6fc16014048d21a,0x9050249edb7b8fd41022],#[0x28065aa73fe0bcff8c92,0xd500401b35b7d73f9318,0x7e4d828c023a6acffd18,0xf827d67ac16014048d91,0x6b6ef51f82c028251abb,0x3468ab367879e090a085,0x1443014a2d93e1978b70,0xc48c04ed26f8adf9e80a,0xfae448500cb54478fd6,0xf5d1f521424004a273f5,0xe6f51440400200271a0,0x1fbf4e620080036ee796,0xfbf4b11401434a7ff18c,0x9e12fc9024010046dac1,0xe7c25f9224020125a99a,0xff6e6ea8246008603145,0x14108d24fe14c0470ac,0x160c60a0326c4fa8fc16,0x9d73f580b07120a9ff5d,0x305014b557e58f0460cd,0xffed30a0d19d3c25f926,0x102815c306b1f01c6502,0xd674ef916018cd4f9a,0x6536558064437fe43c8b,0x9ffe726da681ad1cffe0,0x48d26c82e9c15403911,0xe44fc688fa269f3e812,0x456bc391b40b0d3150f1,0x26cf6cd67868a0800c4,0xa7d24e009c3274861edd,0x80a445b849fc600d435b,0xe04d501488573edf026a],#[0xdb7fc6dcc503ad0ae7db,0x80810c3a24913e50150d,0xfc9b32020430fefe4ecc,0x92b1f22122ff0800c47b,0xeb0264a1e5f8f2825c55,0xafc09aa029103d3ff290,0x197c3f620f281d5a558f,0xf54c644ffec41e506acf,0xb98e32045a69204e1234,0x8c43bc9dd4c94202311,0xf841062cf08b77d32508,0x1042cd5df841042cc508,0xe5f87702040861e3df84,0xe10410b346be50820a59,0x494f80796b11039888f7,0x57ec810118583e5e24db,0xc20821666ed5ee081167,0x34cd5f4ed6c1022cf1ef,0xd9a1c0a023686f6fa860,0x20216a6ed5ee081167ef,0xff70414b36629fbd6298,0x1f92e25dc80c03a44a7a,0x4046142be1eadc0b19f,0xfd491100808046a15fb2,0x9c3378f7e10410b3d1,0x6acb5ee08116795dfa03,0xfa86026cfdf5fee08116,0x646b7f086dc0d1a1adf3,0x3df84230cb1efc208216,0x78991ebedcd820459e,0xc36dfca03030056987c8,0x7d83010daa9f749289d5],#[0xa49806e0b26ccf64f8ed,0x46e55940858a2ff54ffa,0x4f0e860138637ff7ccc,0x408b3f7fafe60a0559c,0xca6f0e8601385cff9f15,0xc8360c083690c3fc6026,0xcf51dbcac140ab4772c7,0x7230049abb87dfa85068,0x58c5bb0059a7364fd7e9,0xb3973889ff181ab427fb,0xe44301142e7fe9810408,0x36058b6861fe30136597,0x4181d3477872db7b5306,0xfaa92029102a0dedec9e,0x4498d8074d6b71af1f7d,0xadafe30e302c672e3d6f,0x5042300a31410cbe038c,0xd52004c00c45685e9f40,0x1ebad428095a55fe0778,0x62faf9148530063131f5,0x35f43a4be8962c0196a0,0x8a153f1eb726244e015,0x7897ff4a4188eefe0858,0xbb00b855777ec42600c8,0xd0eaf7e38ec02a18dfe4,0x871407a1f5f53bc38a03,0xf42f9a8a0800c46bea77,0x760150c6ff1c760190b6,0xffd82ede102187573ede,0x514cfc21b7840a61e1,0x140ec34bc6406edaa050,0xc89a60280554e4e1f9ae],#[0xd3c7a9c2890b0596a5bd,0x829d218185fe94848622,0x170e9e3d4e14489a434,0x7664040861d48eeeed16,0x18887e1b32020430f0f8,0x81c02c86b64447d90100,0x6877f0081c02c8677f00,0xff5a105253cac2669c1a,0x53c6ca77c81168d33833,0x45100fc230e8740010a2,0x380008a225f075d89800,0xc7fec092023a56be8c71,0xd1e7c9f58000016a71e3,0xa2801c92b830fc87007a,0xa3c09b3000911333fbf6,0xcd23e04f2680ab4f3fe4,0xb46fff67ed4028a0734d,0x26840626b4adbe818817,0xfed215043a50749d614f,0x576d10bf1aa540f094a6,0xcd1dffcf5e76a400c240,0x178d701cd09d4327d701,0x69a9e770ded2065a1309,0x3094bdfffaf1b509840c,0x8836704c2540be36b441,0x4fc4b16f041109aa042f,0x860e1ca01836a10209ae,0x3e5800ab3a3af8b7001c,0x3485bd4f00806ed11ff5,0x700ae939876f757e0019,0x4385cb80054ce3553bfc,0x3fc7b4bc0aab90000c5b],#[0xc4d23dfb0ff19014925,0xfa7000054345b64eb180,0x933ff843f2000a24d8d,0xb97000a99e4693e7e00d,0x2a488d9a9e98013b4070,0x46ddd481122eee87cf90,0x317c3f01fb6d42440000,0xd7802a950fc82000564,0xa945fa388205ad63e8e2,0xedd2f18e000126acedfe,0xe7e402221b00085890ff,0x6bf2497fc5108400216e,0x27f947fea852001cb504,0xa66be61f6d0e0000544,0x3a88cffc3ba2e1a200,0xa312c0211a75eaf40940,0x67dbc92b00759f3ff0ee,0x192ad13e1b237001644,0x78e31480c94d2ffef88d,0xffabee3003cd13fd6f84,0xb000561f23f5200a3357,0x3076a7a6002ace8f8dd6,0xaf180039203c7e9800ab,0x305ee80d9f0c002ed397,0xacf1f6c270400fb43bb2,0x7c25200ab3c78169e006,0x17f97cc900000196bcfb,0x89979f56500011433,0x1a2272f13e8007a43797,0x5a00ba4f3fdb66200000,0xbfe99918232187fc65fb,0x4015674c62c33e40cb42],#[0x7fc3cb00001687ce057a,0x682fe527ec20b00186ad,0xd4100652b1129e7c003a,0xa66eff54c00559a7d622,0x4664cc007d101877c001,0x351f7fcea0806a3b3fd8,0xf3b86f69032d0be75040,0x2ca5f2e5520888145b0b,0xd512e9502f2bab70784a,0xfe5caec9c21d2d49e56d,0x61fac0e5760a8984b9f3,0x880000862abdb38c02a6,0xd8800164a47feef060a3,0x1fbc4f41000429f97f88,0xe096640002a6bd5bff7f,0x553ff32f840162b6fef1,0x4b45eff5a7fb1000329,0x1ab393f8c50b05852c0,0x11a08000662fbff0ba96,0x30c080e3148fffc5302c,0xea19e300f9a0de5f4416,0x941fefe1b100018d01f8,0xa356fb9ffcc580028,0x47100129ad38afce492,0x33739100032d6de9c57e,0xd7737a5e2042a567ffe9,0x5b367fc0bb64001eb44f,0xf00389000d21eb35e601,0x17688ff6246a8078d1c,0xb1da46008ed31ae3b0f0,0x9a4ebfc1f2100dd2ab8e,0x2beca03255d5ffc50071],#[0xd9fe378e7a404c255ff9,0x5dae3f1ff5b440007469,0x29a13db2e15c0d5800,0x9e462000534279afe310,0xffe9435ca494005dad3e,0xd1c6d7ebe5f3d010295d,0x4f1be9c0434bb7f1b002,0x70b367a5ffffa00058a8,0x1484c40018e2ebed5b7d,0xe9b5ca0042b493f8c5a8,0xac3c7fd041201a3387fa,0xfa4a036588f2fc8b4100,0xa5d7e92aa3a8c86bce48,0xe08c5274be6e625628b,0x32951fe164e4002da3cd,0xf4c265977ffaf7d30000,0x5430bd594000450d9fc,0xcafa00003092eff18000,0x32540fcdb000001d0f3,0xbecc4e1390a77f9f8c4,0xed315fba4bc000ad3,0xe34a27c0073475f4a09c,0x87ffe6ef1a28600216b0,0x7ffdc4f58a530c0028c5,0xa1ffa81dcc418001489e,0x4a6b4e3af3b2180051a,0xb857fa71d7815860,0x283fffe3811ade551033,0xd0095a07ef78eb360061,0x84875e7402e6720a438f,0x680074d712e544f800e6,0xd668030955fe9c57c103],#[0x1fd8f3998058d03efbf0,0x800a9ae3f8ebce8058cf,0xf001cd01fd7f3fc02635,0x9f7c3acd00612aa5c289,0x3df3e997ccf080059a97,0x3218bffcbe66144010ed,0xf3ca18a1c2ebe7045820,0x80b23dbcbf97800521b5,0x86870c5f800561b7023b,0x197800561a1c317e0015,0x34cd2f3e9e00158607e,0xff8f2c0000ca1eb0ef80,0xca1c3e1df000699a9,0x70808401d9aa9ff8f2c0,0x66bee83785c06cb0b1c0,0x8f0b40311c3ff3d30022,0x2152abfc302e00319c7f,0x60fd82a348fab18c1af0,0xc75f18000050d51c61a6,0x9b7d25a00013692f97f,0x94d75f01ea05400026d4,0x552ebe9c75e0440200,0x389c2800cb5e5dc446e8,0x4386a40215aa3ffff9a8,0xe1f04ba70000f6233950,0xa2600570c590e3300d19,0xa9afb9738c02a6687c1,0xca557fba79025b000,0x16a5a012ad5bfe5dd0f7,0xc354011400f223be1ef4,0xc9567fec48d500f1a3d,0x6680000cb51ff8011ff8],#[0x6603e4b00195a6bfcb48,0x849c2dfc003f0b80d965,0xb9fe09d00039b483f974,0x4c1530d2f22611430a9f,0x34f3f25005142d09ffd2,0x8078d01fefd04b960029,0x58d0100f5a13feba0865,0x5fe5eb4600000cb567fe,0x6cb1b8e038404200ecd5,0xecc8c1330b7d848f85c0,0x16678ff413c00599c1,0xcffc982d00cd9e3fd04f,0x82007da11dc0ca534d86,0xfb307b2003da03ffa378,0x11b46be1de980b2183f,0xdada19a11a83fed9d9e5,0xd31e305010ed3dfe1a53,0x4e1c9b86308503ad01ed,0x63e0087923d47c79aa80,0xadb0f6fc5f94076d138c,0xa43b17fff735818a0295,0x4db220330d047c730441,0x215a752628e882a86574,0xff423348ef42f2f39384,0x90eb8ee2c18050d32349,0x5038ce587ac7718c0576,0x8f8f351980721c9bd780,0xfd28086690f8ec1052cc,0x774100a028dae3f6f662,0x3fc039ef7415b4317fff,0x12051690d1677ba0eda1,0xe2c3c240c2d28ddc793e],#[0x10c42787e68410b32378,0xce89042d1afd44d8ec08,0xcb552fd0482335c7fe93,0x9897b3b9620030edf44,0x9b25ad6540b33cb8d027,0x10dce0670f1f23fee04d,0xe5f04dd9998259a91f55,0x44efffd1ba8b03ab4b7f,0xa154463cb05b58201588,0x3d95418d8655dd795bab,0x43db77c5e5040861d1fc,0x31a06b323f468162a00f,0xc80c668f088404acd1dc,0x319f3d22e4063367a45,0x243b0250ac4a07fc4972,0x99f3b00c580769add68f,0xa50052d587ca7b300652,0x64042092d6debf9fe039,0x2089841d1b2bffd92980,0x9010824b5f7c537ffb67,0xb71e20016aafff64a601,0x7e0c0c1029888b07f97e,0x120670fb7696a1a9306a,0x849df03d065159fc9b02,0xfb7696a1a93702042782,0x3d085199fc9b03860670,0x101987a43f841850abf0,0x38f40df20e480596eae8,0xd9283fbed45d04042d3,0x801604c35081cff03592,0x18bb92962a97bfe1e2e,0x6440a619c6ff36880cc3],#[0x91884aead00294b4f09b,0x819f87e433bc9da14012,0x51741010b487c70410b2,0xa351fc4e848874aefefb,0x431c9d28f5b602903092,0xf4001c20180a28b93dc9,0x608290830a0cedc8fa62,0x4ffe82742986effff09d,0x13be33e7a13d5a1452e8,0xee215ff68364a13806b,0xfcf1042cd852393d9502,0x228a81fe3a84821674f6,0x60ffa005ee05da37faa8,0x2ae02b0c0ff999af00d8,0x6216f39eea032975fe4a,0xf0c349e9e35f8264440e,0x4f441d2d163911152191,0x87f7fc420120361a8bdc,0x5351323a3fc58180480e,0x8fd4cc9ee47ea6a4fbe8,0x86273ecfff50408b3dc,0x18403e225f3efe08c810,0x1440875a1095afcd9ae0,0x861f1fe2c44633b0cbff,0x447e2043112d2be4c040,0x2e3ff24d04042d32f524,0x64a11ff6dbe062065a03,0x331ebc4afffcc0a69051,0x5b1bffe5644088070d,0x1b44a785ba173f8d6188,0x4665a20dfe5918406440,0x2c210093140e2c5457db],#[0x3abc620016ae7fe8cc20,0x477b169a00435c7bff5c,0xb9dc53a50006d344bfa3,0xc282b90e4935e0b809b2,0x1683be85c92000da61fd,0x4647f9593a7f606020c3,0x5c1f0c901586aea864c9,0x8808c2dbc7a55c03219,0xc2967dfeaa08a2c3fc0,0xb9259258808c427f2c02,0xb3fe2a4e014fff1d27c6,0x20b819345782e026ca45,0x6870f84c9805a1dbff51,0x909e2092b7e909e134,0x7bca89e34bf919944fdd,0x538a9d55d562a472e4,0xef5a2947c03e593c2f02,0x936ad9e777aad14a3cea,0x7e354a51021880fd8bb,0x166a68fb1793a808ed38,0x6a4186887fc7ea3cc020,0x8bb25a591538947564f3,0x4844500d304162195e99,0xd1efc9e722842bbd1c78,0x25698da1a3ee1f4985c0,0x272b32ad294c3b27c7df,0xbfc8886a7e0ab480d386,0x368b656c6aa10aaabc68,0x990742a1bbf0420f6c2e,0x313df823792d2a339395,0x830acff549a2be40a2ca,0xd50cfa120843c2cc5ed4],#[0x794039004bda4ea1452b,0x10caf403507a8ca16022,0x81b29d244323e72dfa81,0xa44a2905618300ea8860,0xba85a627408597e92560,0xa726979188c3d1892a4b,0x8cc32bf0863bfc6230e8,0x4e571cd6230c035adf91,0x77fc84a70329231062a,0xbff274c65a29d42a2308,0x84222bf761e385333792,0xeb8f0442d840e5b09d5,0x170eafc218efaa84302,0xffec206b40adfeef7bb0,0x180609f0f53a10fdc10a,0x5a27118f76cac0d9a151,0x6ec02a154fee01f8084c,0x179856ef44618083f2]]
set_option maxRecDepth 32000 in
def g255H10 := limbs80 #[#[0x1200080304030a050301,0x170b0c0603030029070d,0x5340208041900020001,0x10000f080501040106,0xb28500300011d0b07,0x9000315050507003200,0x23050f0c090000090c00,0x100104010009020303,0x316161f017700220322,0x700090e1112130e0400,0x8001c10060a1a050204,0x10408010005230201,0xb1f0a11001f01280200,0xa04030001012a160201,0x40803010c1814102201,0x45000200011800052b24,0x40a010b370200080000,0x2f0641091f040d100401,0x800051c04000a060507,0xe050203232a19090610,0x1061802020b0f000001,0x3010e192109091308,0xc172101000709000a00,0x150c810e1c4b25200118,0x190606020200071b01,0xb0d00000002032901,0xb2d0461030103000e31,0xd01080a031a01173728,0x2062b010c0c6b000201,0x4e0003121e0f00153315,0x2000110020d031a1e08,0x611083b4e0f1c0d0917],#[0x3f02272a290014060138,0x3729002d001e033b0204,0x205000c4200900183c19,0x42070e0b000f0d052a04,0x625ad0000270b18032d,0x6066110000c060000,0xf063c05090d062d0701,0x46170279070b030313,0x510a100d1b2b19180001,0x311010400082328003b,0x1180017175f01011c13,0x600051a190b03002608,0x441a03122c065d0a1e00,0xc0400110b0015000000,0x110e00001c06241e1d56,0x30007510302020d05,0x240305094501207a001f,0xa6d181a043523010601,0x10228150d180c1c2315,0xe3922714011b2082042b,0x8334e8dfc000479c51a8,0xb40403fb26a1ee360cc6,0x8c083dc013b091574,0xcf9bc11b45b8a3a40efc,0xd09a53f9407a20602164,0xc23015c0d4513cc0d541,0x33b5a50eda7851113127,0x482799c9a477839e5e0c,0x324798f274e5a382e393,0x205d4e77151fd40a8c59,0xbc4dc250d9bc566fdc24,0xf91951e0d3d12955cc43],#[0x16138d00b450c49903,0xcbc4108e9b345cfa8395,0x5e29145e13254b664a78,0x84e7d81353b45000958e,0xca216fc48755e598b,0xe85344425c9f77549d74,0x1361564147473836e0,0x43bc5634a106f3199800,0x960000028d18881d0721,0xd71cd528b211000215ec,0x20a25dc83a101,0x5f6000115a9a0120f000,0xe391570e5cd421fb19e5,0x8200e5014598000c11b4,0x1cfb688476b5d64d0705,0x6f654e21ef8ce3463,0x6a3bd1e095510be65830,0xd6134450000a0116af89,0x60787ea2384cb40005fb,0x5600001a200004e550a8,0x60b032459d88000176c5,0x87386520e633528ace7b,0x1eb08ecb9800002502e0,0x1c230000369600005a40,0x33468c38000c0535d017,0x1359ab1276189e3919c0,0xd012f736000268d80dc,0x487c66da00015d850d78,0xd88022500002a3c36724,0xad10bb00013b9de68000,0x2c546000079643202a11,0xb07e96f12618ebf78d9e],#[0x51fc00000000b0595,0x7041c76150000000cc80,0x70000000544c0005ca01,0x27320000000000345,0x6124cb055b1798000,0xd51ee00000524f115890,0xb1a3c5fd381cd5000011,0x2f3832a49e5b4,0xa2132963b8fb665e8de0,0x6dd5400004095d9c6315,0x53352fd8cd512ac53852,0x20801283ea74291237ed,0x9c3018f054aad147228d,0x711a17a11a8000370b40,0x5ba8d1c000532e55308e,0x8f8f28000060e521c4e6,0xe1b3652500032da9a842,0x44b8000144116308497b,0xed006852f56d54d4f35f,0x7d4ba52d0000000261f8,0x40004fac000d6b100843,0x2ba00027a91b067611ef,0x23cdc92c88c20000ca1e,0x44e2b71e55e94c583dc7,0x935d753405f564066454,0x580600cad23ba8fc113d,0xde619d77a1f787cc10cd,0x842156440008a5b0418b,0x7c0c92f319cdbf34a5c3,0xf8d3600244f024690340,0x8c21a09b416565891a91,0x9aa40ff0cb91db9af248],#[0x6b925754da4e29786655,0x4f71f9f91650d9ce0621,0x8000000320700b966d13,0x28b00031984f6,0xf0c8d00008a33088ca40,0xf872c498d8687c2de310,0x1d30568cb367da529469,0x3cd34bde1c3571b5f2e4,0xfc6a2d96c0000000000c,0x41ae09600020a5c1,0x1fd00000009de8399000,0x46032d6d900030c00003,0xf000000041d800051701,0x9b7f6475d6846b88a802,0xac8000c804000095560b,0x1684c3680008b0c000d,0x10ed0000000000000000,0x51b0000519caa36fe179,0xe1419a2d700000000001,0x245d37129ced55fddf82,0x8ed51901e6f2994c0e29,0x3ee5b000d03f500036ff,0xda50900016d617ca2521,0x56fa81b4730d8f92df13,0x686db0d14c4033540d3f,0x7e0bba7588ddb29f9e77,0x19a52242202c416df2b3,0x1b8647288da16dd4bc6b,0x45a1a600026350358282,0x7400011bf3e59a9755ed,0x57979bd1055c5c418a85,0x2d29daa2ddd1383778e7],#[0x9d432766b1ffc67809be,0x9000000000005f900032,0x85600004ea34e48bfc2a,0xa9210000004f30d8e11e,0xae3d48a691ecd6e71c28,0x92ac12414df82280000a,0x4961fc4000000000000a,0xe20000000cdb36ca0000,0x7c168585000217c038a2,0x133100022ec481046,0x46000098f53d2427d22e,0x2197866f2cbc,0x92ad00006be53b057e00,0x72d12823949c2b5144fe,0xe84cea262d1db1840e11,0x5c8a400000037b290a11,0x8f5669803d4000cf4d26,0xfc82605c9c537488650b,0xf489ddb728600032719,0xf6010000000042c2a781,0x49f41bf48f886759add6,0x1741227161a33355914d,0x8149e3b1d4f25bbda4d3,0x1dfc06c4c8b1e60c5201,0xe701670fe10dc46e109d,0xf143400001b294837cc5,0x8000df8500e8ced3c8d5,0x7d9d25677d02a160d80,0xf6012b3db00024ce57c6,0x6d08260fdefc000c7e72,0xce1476c57b466ac0db75,0x3da2bcd88e3b243e3307],#[0xcd47c0a0e2374ac27118,0x16c00c9f3628c9a48640,0x3c5de1a80711e909957c,0x1a95c9388c7562189001,0xd5a996305b9006e00002,0x12c774b89424c19ae14d,0x1e53614b503e7a0520bc,0x13175db3360900020104,0x40004fa12bbc75a0a993,0x76741400000001224841,0x1773645008d5700001,0x655cd73d5e021c405a40,0xfdb0c3440553a50c60c,0x1a23e200000008b635ec,0x3e588051565c0c8d5fdd,0xc2cfc9d7082454e58e1b,0x7cb000137a59880001d0,0x33545400056cf08d5421,0x14e3521f9f3a58dd1b85,0xc9e06918e7c03256c458,0x166ce08b0598038433f,0x780000000180d24b7d02,0x66750001132000164cd4,0x18bc1be1ec11bb003,0x1bc8bc55d0000,0xc0000000030a30a00000,0x3745d7f06bb000009,0x8de621df164c24480000,0x26108c6c68ad9c00005,0x2775e7d44d84d800000,0x43780f7493863b413000,0x9d8d940000c442980003],#[0x3cfcc0009244000dfdc6,0xdd975a052a400052140b,0xc1a4f9497f1a4516743e,0x40000000180a00000005,0x77bad6565308828000c8,0x6824ea934c51506d8c48,0xcf88f56259ccd6a4da2e,0x7cd68000541247d5f501,0xa5e7184314605e0075d,0x1181cd92380,0x965e2310,0xd3c51d48b5842c00,0x3a24fdc1480787429000,0x84f9768000202cc547,0x5148614807c00000000,0x85bc0000000000058800,0x1ed677400017a1,0x437db8cd214a5f8c0000,0x8cf21ffdf8813342,0x567000031d9160000986,0xcf246c510cd77b9a8f,0xa000227a000141f5ce40,0x4c2400018720b,0x77662dd22c0004ad47d3,0xba5a3000244bcc723051,0x801807b00024415e,0x4ed12dc000d67267a000,0xa6861c000136c71d9fd8,0x61e28000000310807675,0x4cf90a40f190b29f9a5b,0xc114ab4b143de9dac23f,0x17104c780de0fd02ea5],#[0x30c000241cc97000000,0x40b82f93b7a045725000,0xfe863d815955424d8345,0x5000079480714b200017,0xdaa20a600014b,0xe6185b0890000003,0x742148add03c06d71240,0x5131ddc279e98e51df09,0x58bddc51c3451158a1c6,0xa3c0c4002c5ce6f84e49,0xb5db813ac34d4f8cbe84,0xde3c0005a68147467815,0xdc4474dd012fb49f93fe,0x5b3f253ff130c6b85e20,0x9778499e461c06800044,0xd0e11528b787b145c,0x13e5cac8e8,0xd750000150800000000,0xd6d55840b2915f000000,0x114000c6487388800000,0x1a38c00000000000000d,0x5a1885b724540c00097,0x506133055f4593000,0x37141400009d00009950,0x593dc3bb000268500023,0xcf5e5921a0d176414f40,0xe952c50ec3a388255b2,0x820afc9780fc817335b1,0x80005ddf665d29a0ea80,0x38200027cf00001eb8d9,0x536608fe041566402c,0x9c2ac1b90000705cbe00],#[0x921c00051b1134000306,0xad80004ac9470d5d443c,0x747dd14a20c4d72225b4,0x275055670b54e1e27c86,0x54a000353d574e3ff000,0x8103073c21054000c6ff,0x9b727ec00011bc00020,0xcbd13e654386e6d52400,0x316c43814c0d2f842f,0x9100084546039ba14af0,0xd1590002060046d7d2d9,0x314900000009eb,0xfcc0ac0001eb40001c88,0xdc2c72cc977c00089073,0x17e24270b5440d46c677,0x9380000000067e030641,0x880005fec6ed45a00398,0x400002797d100021d18a,0x7c1000000000000000db,0x59000263f0000000474a,0x7271d35af672f18a92,0x9744021000000,0x148ccf400000000000,0x9400017a528e8c180000,0x6789904531f97ed1ea5e,0x776d2b774a9910000db9,0x4a724e049ae565d16a,0x500026f9000218687c80,0x59b369bd58b20dc9b218,0xd7b2b1e03f6724fbf21e,0xb24398392729026950c8,0xc6324d595dada7a4b004],#[0x8718d261b44ed0ec5f5,0x3708b40001ad40009c08,0xe00024f2d11b43f822c1,0xd901747ca7920c09a03e,0xa1f76356dc000543c000,0x54fd35d443c4991,0x149d415f6310c842eb00,0x33251e77eb0001119882,0x6b512b1e9cba24620337,0x80000663000157602d83,0x41c2809afc0fd40134b,0x8f921c1b244e983612ef,0x3484947c3a016195780,0x165fc2860648e0f62800,0x103553a2c2113f75c5cd,0x45dc58000021ba1f1b,0xcdd552b00027fd00000,0x9cb633da4b45e5fa800,0xf353d600000004d24000,0xbf58c000364d024d5415,0x25bdcc5a75e00000008a,0x2638a6f015c3740009e8,0xa720386f70000157cbcb,0x700a272ed31c5bf00010,0x1bae6cb000018d1c5e1c,0xfe45614dab557130e596,0x2c6695b8057fcdcd3399,0x407cf911b64bd731259,0x1ac18186ad47283d91e9,0xe0992b66e000002216bf,0x59d93df503f4d052373,0xd5166711520000d4b800],#[0x5bc40c47d645f19ed6dd,0x14808c3c1ddc9513009,0xe62959685f3506800000,0x4c819245778b063cb9f7,0x429c0e6c8099a67e5608,0x4dc3d590975630405971,0x5a570b988f06ec4e197f,0x20f6b007f011c57b8000,0x493c3dfc1393df712435,0x624c1d800002027506e0,0x3139700000563d806085,0xa08ea547bc1df35c8e42,0x35e6c78e2400000030,0xdd907798505689c20269,0x7d717b00001e2488f5f4,0x11f03311541f975aad,0x49a8b474bf00,0x31a9ba82bf9adc000000,0xa500007690ae27521290,0xbc64705e0000000109b1,0x5bf75749385253cfc642,0xf42c79c4f41bd79f5cd,0xb5512dae756ac60a2899,0xc000c44843292ed65716,0x6ae902767d43a4535880,0xde62543156027f5183,0x742b87410a5000000000,0xd2cc0009d3754bc2b41a,0x35ffdedd802d4c8651,0xd2d800000000000,0xb50799740000a1472b00,0x6674d3f70c00026261f7],#[0x2e8e580000f3656e48af,0xac9281619bec000df1e4,0xde8d1e4000371c9eb339,0x20844d23518411c73f,0x30191f5427b00005a90,0x19f14c953bb7c400,0xeb0114329c058000000,0x14f09251550cb18,0x1130466053c0001f580,0x3695d6605b000000,0x22ed0ca23cf03c8000,0x2652240ed28184bc0000,0x10aa00000005a713e9c9,0x15a75cf817c000000,0x60000000000000009724,0x1598400000004ac1cb03,0x85f47d9000259e404470,0x358000850c2c4c700653,0xb76ba000000058e2070d,0xb73a00000009d9b53444,0x67f9ee64249fe8000d56,0x79000012514a73424cda,0x7033c000508950a5b185,0x4ecc13f1d1a38b17f85a,0xa8077500035ea,0x30b84c355540f7561e0,0x206a07c10ac009800000,0x531000328d000356d000,0x44871b065d61c0000000,0x75ea000000033fd8eb47,0x4dd000007da1b0000349,0xd0c040c88b3ab1cdf36e],#[0x527575c1d31500000004,0x26688fee10a56a27bc53,0x59d5a5d0010003792000,0x1dc6246de948d0614f61,0x232b8bf000000021,0x732524482e2e9c89800,0xb4435900021bd5270092,0x15c100014ae00015be9,0xc9c000048ce81300,0x6d3000219c46b56b3000,0x7ec25d59900000000001,0xc0762681843471a01324,0x5038000993e7b4000154,0xfcd50046dd3be557145d,0xf30f4855410edbb84129,0x26608df07f844a1251d3,0x2f15eef43000000008fb,0xccdcd759400e02200001,0xc5b080254440456572d4,0xc7784f500006f5000262,0x21bdfa107888085ab,0xa456b8f307e906ae4da0,0x1938f4778317bc4ef04,0x6e9d01a4ea5549608000,0x8183ed42d9f9d1065d21,0x7102263ad93b5ce58894,0x6a8000e0203b800023c,0xec060a00000000174000,0x228ac9201d745ae0098,0xf72a1b4219610537b300,0x60d8f84000126c0bd9dc,0xf2c0a41098da37950797],#[0x719d0000866978886a76,0x4a4d4bc1dbf0f100027a,0x7400087f800089915f7,0x7c2f0db9f34d885c793c,0x15e3c10b419111c1dc96,0x4aa94b95aad1c8835,0x4f510000081c80009890,0x844519400032b9893c5,0xd37364212a04ded6e372,0x65615089b93ce07d00d5,0xd0bf9e40000044c7088,0x8000900641e445c7fc59,0x1d7c000119000000f,0xd54f8d69900032dc0000,0x313fb26d9b5054d0d024,0x48f659d4705cc940908,0xe8a0d2ca9a3335847310,0x1244300026368abb471d,0xe344000132400021c1db,0x571ddf32355ea87ee018,0xee13e962b123939e8740,0xfd8752db139a2be00ea0,0x361796d123245ea1a,0xcaa044912460e00012d3,0x17ab95ef5c485fa16ec,0x246d40c333dc7162d000,0x7c800012e58e3e37993a,0x73000368fdc5053e4125,0xb038e6db03e400093190,0x9d3c0b40000000000130,0x6cf00a12540000001800,0xef56c545c0980e703a74],#[0x75c55e1151111e0000cd,0xf910800014a90c7d47,0xa19f6119fd70f48a0535,0x78e9778edbbd05484af4,0xd08c1e387b47c357ea36,0x26a7591a7e00000648,0xe4000000171b5b8f2e70,0x707ccbf8403dc3400085,0x2c9801e7519cf16b680b,0x4b44895c29e0718b0001,0x116c0005aab056ce6c1,0x224082de2a5000000,0x5ab2ce53ac358ceb0000,0xcc213d7ae2bd000320e8,0x4000151c1041f2752d89,0xd0d9799d66d7a6de4,0xae095a4175a832464c60,0x13868623b8df53]]
set_option maxRecDepth 32000 in
def g255D11 := limbs80 #[#[0x5455050d415013148110,0x5c165591635856055153,0xdfeffbed765d5745cd71,0xffbfdfeffafdfeff7fbf,0x8273ae0175802ea807ff,0x551052e00a54014a0003,0x58500f080161012b082,0x8058700f0c0161803c28,0x8861610c2a21850423c3,0xba061640c2a81860430b,0xc2861750c2ca1861030,0x74b00e1870c30c185d83,0x862c28d5641aaa83a5c0,0x10c3c09a97030b0e3161,0x61cc3c318586322ca61e,0x359543c22878150f0e61,0xf1e05e3c3a858750f0aa,0xcf25d9e3c2bc97578f08,0xa62650c52b88a56110f0,0xb0a21e1042c209973132,0xb0e21e1842c30878510,0x22aa8495c492b0907871,0x38b0e4161882c291574,0x843a2a871e0cf2b89c78,0x58738f0c71618e8ba9c7,0xcd6458f06b1e0163c39c,0xacd7658f0ab359563c22,0xa4078380f0101e1d62c3,0xc340785812eb01e1204b,0xcb9959632b2a651e04a3,0xa2c2955742aac855550a,0xca2c39478628b0c51e14],#[0x9503c22197340f0281e1,0x61d03c320586422ea845,0x1e1583c23078160f0e81,0x11e0623c3b058761aecc,0x91e1a24bb4478588f09,0xca955d123c1a478148f0,0xb0e91e1922c3251754a2,0x8f06d1e05a3c03478748,0x90f0ed161da6bb347856,0x690f0b21e0e43c0c8780,0x8270f02e1e01c3c34897,0x58771aece1e11c3c1ba3,0xc78398f0331e0263c3b8,0xd0781a0f0141e1a63c24,0x202d5400f0b41e1283c1,0xc282d7505aca0b5d016b,0x6a88ed8705b0c0b5d816,0x76ba8ed651dae23b5847,0x4d6b89ad6135a826b5d8,0xd8d6c21ad7435ac86b60,0x54556a0aad8735b0c6b5,0xb5d156aa2ad8155ae2ab,0xfb61d56c2aad7555b08a,0x8fb605f6b0bed517da82,0xafb595f6c23ed647daa,0xae82b59056aa0ad867db,0x5b0a2b5d456b28ad8415,0x25aa64b61c56c30ad761,0x625aea4b59496b992d63,0x733dac67b50cf6c01ed7,0xd843dae87b590f6c19ed,0xed805db0e7b618f6bb1e],#[0xaed735daa6bb50d77c02,0x22ed745daa8bbe0d76c1,0xc2aed855daeabbe1176c,0x6a1c2d8085f0ebb61d77,0x16aa42d8385ac70b54e1,0xa16c2c2d6585b090b592,0x14b6ba96d652db025b61,0x60516c396d862daec5b6,0xb5d916c222d7445ac88b,0xcb55196c0b2d8745b0c8,0xecb61596bab2d8465ae8,0x91b59236aa46d818db0,0xb009b61a36c2c6d658db,0xdb0c9b5d936c1a6d814d,0x6db06db605b6c036d874,0x195b012b61db6c2b6d75,0x8695b0b2b59656c1cad8,0xd8475b06eb605d6c03ad,0xed839db033b60276c3ba,0xd2f80a5b014b61a76c24,0x252f83a5b074be0696c0,0x2f85a5b0b4be1296c,0x1f6034004f006d006e,0x1201f60386063c0b1813,0xca017702c1051409741,0xb088610181e6839006aa,0xce05710a7013e025d847,0x1b04344064f0c2c17742,0x30f801e283ab07260dee,0x8088cc114421d041d880,0x28084e689a312d625084,0x215c82aec5400a571456],#[0xf90bcb172c2dbc59c8b1,0x33786578c8018a230945,0xe1bac36806ba0d3f1a26,0x760ec01d1839787198df,0x3ffc7e78f901eb03c647,0xa21a442bc84690682070,0x791da234a46108a1110,0x4c3496f92aa24f049089,0xc27f64f589d393742680,0x7f14ca29345188a20141,0x57a4ae095902ad254d4a,0xe2dac5a98b40163d2c2c,0xf197ba2f125d84b9616f,0x632cc4b186e307c6058b,0x6335065f8ca6991f31ea,0x551a8034ac68a4cff99d,0x6decda51b1e35e86b28d,0x338d27118e0d9bdc3764,0xb11d413a1a7364e5b1c9,0x78e8f049dde3b647640e,0x83e187bb4f599e853cca,0x71fed3f867e60fb59f3,0x83dd064a09440c680e10,0xd43e286dd0c5a15b424e,0x92a2f5455c89fd128a21,0x910120623c9472a8d4d1,0xf4ae294b527724b14902,0x66a68d4c9c98852f0a59,0x9fc13e1277e4e729bf13,0xa5276a3f145aa87e506e,0x4f2a5d545ca7b54d4296,0xae915bbab485620ab8d5],#[0x8597eb1d56222c1a579c,0xfdadbf5b16b56d68e2ce,0xbc997752eb65cecb8ed6,0xc60cec0d17f6afa45eb2,0xe4b18962b6c465871b0a,0xcb6994b32516446c7e18,0xd674acde19aab3346614,0x5db48b68b8d0b59ff33d,0xd7c9ae1b57b6a6ad3a5a,0xb6e3edb8db4e36666c4a,0x2f38366ff2deb9bc1b74,0xe6d5cb8392971d4e289c,0xb75e2eb15d403a3773e2,0x373c427822ef19dc33b3,0xf721ec03d3c79e6f2b9e,0xf7dfcfb01f453e4d7c1a,0x2f40237fe8fee5fc73f3,0x6320ab411081c702a20,0xd85810a1a121c21783a9,0x43c286f10d2e18cc2e,0x13e6265c49d88d911122,0xf8bf5171a2cb45668a59,0xc4a27118583602331462,0x5431c90783426111186,0x481a11094383742c2209,0x6c60441085e060323080,0xc07c12040f0644616848,0xf340202a56178a8942e2,0x835240e81c0d030cc704,0xc621d0c02d4100858ac2,0xa021c748f4642605349c,0x33a89348e05468eab790],#[0x4b28a95489c26c88a459,0xe11b370f5469f4dc34ae,0x44200f190312f1691c7c,0xb1e4f1178a800ca36090,0x19086c926f3b9b640543,0x14f79fa0a42649131ebf,0xc088a33cf7e7ac04592,0x7349ab675683acc1fe1,0x978e96e04e932b35f516,0xff5019481be3aa02947c,0xa42f1307fe037489f112,0x7db9dc12259a17e35013,0x8389597f622001598873,0x27f0260015983407cffd,0xacc14cf267bc80d96,0x2785fff224821253fb01,0x881297c1bff919250094,0xfe56091025613f8eb02c,0xa2f8067f218856893c6f,0x2a04b1fc0bffd6402404,0xfcc0046095001e3fe050,0x13e15fd2014cd0b9e17f,0x200500955fe84021198,0xcabf0640219a27f04fff,0x8668c27f9f0441182547,0x5fd1010ad19f0afd0900,0x4851b8fe14419d273e01,0xf5e40003a40dbc7da42f,0x40a52f7ee14000c24cf,0x38f5001229796c7af40,0xa10b1acf400184adff37,0x7407a9123e5715010984],#[0xc2947ffdc00313cc58d,0x4762e000692d757ec500,0xa12b5fc5000723effe0,0xafffb000e27af9cf33b8,0x90003239a03e7dfc1d0a,0x647b3f3e9029285fc,0x73fe5c7f770142573f1a,0x8e0d7407a913f59000e4,0x6140020526ff26003138,0x40a49ff2c00627df8d,0xa41ff830062798c0f81,0x638f080c51f7e299fa81,0xa8b076913d574360ed20,0x40a4af1bd6883b489e97,0x2dff97825285d0ca3f40,0x3704c5073aedcee0a12b,0x13980b73ff61025677bf,0x25ccf7905095dffe2a07,0x57851723dbdfdc826283,0x4c8fbaff1d2100c90bcc,0x2b7f9aa104c8fbfe6490,0x50d2953ffb63e2e48021,0xe4b2408010d534105c78,0x5498f1609501367ef4a,0x2c12a026ce3ffc28e420,0x3e6441499bd3db08111e,0xa1a43962b96575c10428,0x525affe1270042a249cf,0xd820a4c3ff9f8011a100,0x40224efbf4228201126f,0xaffbe0ec0329dd7e8450,0x50a693bd7d202043224d],#[0x9e3ad291429a4af19ca4,0x3af5018ad78cd2ac0348,0x691bf6b49560a69277a5,0x6c715013679e163f62c2,0x1798905268f064821457,0xa249f0920a4c7d6db081,0x6f7f04294affe1870142,0x4aa50fe0bf20842a4c5e,0x89f8042152471c13c288,0xc88002527df600a4a17c,0x4a8cff40084a2fedf,0x530dfec0039452f7d8,0xf2201c4fbf9fb1370a00,0x8007941ca7fa0000955f,0x1069332a35d01ea413fe,0xa4ffee00389d7c1e2a02,0xf7d8010945f7f7310184,0x880713dc3b9bc40612bb,0x7139be6760000955ff9,0x73017cfbf83b155ffd80,0x5fc6800391c7f92000e4,0xef601c4ab473f9002948,0x407a90bfac8007239d3b,0xe27df820003238c18d7,0x13dbcff0c0a4a0fff2c0,0x36faea084a8e7ffc1807,0xa55beba8212a3c7c8829,0x55b87c0c3a949b4dc100,0x1b818a62c3e70f704029,0xa99bfb02202a3c7f26,0x8e80405479ffe8345402,0x1799a8cd1cf99312936f],#[0xa8fe4302931f32625264,0xf7aa024aec7f37faa1d8,0xb9a09a45fea8149a3f90,0x44212a3d9f120a4c16ce,0x6018aa7d790202a3cfac,0x49a7e703202a39e68fe1,0x568923e89a8cd20c9989,0xe64c97094003ffe58111,0x306920ac933fc88883a8,0x483a8f43a0fa8682b5e3,0x414987e648425479ff72,0x80a8e3f324212a393d2,0x8927e867e5854291f18c,0x9185a85d23798f912a00,0x9084495c7be2543c4811,0x69f1ea26406489f538c5,0xc70540194aefe04800b6,0x219a1be98a002d9b4f98,0x9faa8a80312139568349,0x22000a358886b8faa648,0x65abfaa19223f843c814,0x2005a6b516fa3e2f9234,0x718a4015d2635f9e8e62,0x1b9ff9c7878200692f7c,0xd2d55c26d8a014ad,0x7d7c44003920bfcbc900,0xaa62f7be3f95200652b,0x5420245357d5e7a83480,0x935d62627d237bdde7c8,0x593063aeec7b2800a14d,0xaf02951f7be3ec120000,0xf755d67da20048a665c7],#[0x2dd207bcf85fb140a292,0xfd67193003294bc8d6a8,0xad2fbe710a360245347b,0xf23cd6d7f7c1568060a6,0xee0ad001029ab5aae3c4,0x8d76466400814d1ebfaa,0x535bd038a6805f342f9f,0x4b2953f7df0fca050028,0x5b1b8af481cff811c7a0,0x9a23e7f97c1400ca56f5,0x1453177aafd232150142,0xdcab53a44fd1fb621250,0xefdfcb9094001853262f,0xe475c759e11e010050a6,0xdf4f60840e9330faaee9,0x10a6475e46b1215e913f,0xa269fce2f01851bf67c,0xc06144ffc7f40c610ca0,0x53601ea3ea01a907cf8b,0xc28dfeffd0a3ca25010,0x6b34b1d28030937f71b8,0xe485ebe35843200289,0x9581d790017490a2b3f5,0x486aad3f15662404769,0x860404769cd3c2d58028,0xfafc31a00454a5f7dfd5,0x834252ff5e67241f2445,0xaf29641424e9ebf93c05,0xf9fe3e49012a82d13721,0x178f73d7c812211689b3,0x933c7fdc79022882513,0x44c008c94d59a5ca5905],#[0xf9f13864010923f2e3ea,0xc2e1333da3a45102f685,0xf4d0a2f481f823fc8d02,0x207ff3e008d082252967,0xe2438854cc32d1f83831,0x10608d2cc9e017c16292,0x6001b81925cff8fc0cd0,0x305155f0706a40ffe7f6,0xc9cd076064e5ceb62153,0x1a6094bf7c668e7a0ec0,0x5a26c0c9da588c56a015,0x774a0b19d42df8631724,0xc2c479087d7385c90dc9,0x3856fbab21548dec67fa,0x1327cfdfd8cd214182d1,0x8b44d1eff9e272205825,0xab2164858fdcf9dc8884,0x1347ebeb46403a44ac0f,0x8817b42e5f6393200a27,0xbee6c1051b89dde91cb2,0x1ffcf81392078495cf99,0xc1080574a9df5e0a2547,0x30b6139f44017291f583,0x612cbff81472400000,0x13fc3007140ffe8abc80,0xc262f1ff706e14000ba6,0x2c2581ffff314f80000,0xeca00285337fd2c44484,0x81800000c2d73fe3ebd1,0x7ff87aa8000612abfc3c,0x6cdfafdf95ed10028531,0x2ed619ffeccc62400018],#[0x9803522b5fa34b400000,0xff83dc15a002053562e3,0x3ffa8f6466400814d5e7,0xa6efe7ef0f24000d258e,0x58a763fd78df940a0058,0xe9fc8006a45c3f3e900,0x30b5d7e1108151002c35,0xa16caff2ae0150000,0x30d65f8f0831408,0xa7d084014298daff21a9,0xa34a14000030d73fdff2,0x83ff82d52800059a6b5f,0x801b40fe723d75041152,0xe1aba8208a979e1e9948,0x9f5fcdd042484aa66ff9,0x67fe284100900420066d,0x8a6380a1a6923b820215,0x8499a5fb8387c91d9603,0x224802a62f5cfde98e82,0x2068e0d095bfffeff36d,0x8ad69789f242f481fa5e,0x8801b4775fe0e8b10040,0x7232c44208a99dfdc834,0xf75b0ac43218a9a17ffe,0x620746a765edb6040a1f,0x8c72102c34e7ffa88192,0xb1214c780f87691df08,0x8aff30f66210a740e3b1,0x4890408cd8a73407c3b4,0x811459001a547ffa3030,0xfe91b04980408cd7bfff,0x264b00e52cacf6c08155],#[0x43447b47e4ee0d8a4ffe,0x31f5f4337018ab578f15,0xdc1a94af1e31c64506e9,0x1568d7d8aa1e241d1fc9,0x578a842a4c79e1ccdc1c,0xb24c7c7e8e78462ad18c,0x578f1fc4c81]]
set_option maxRecDepth 32000 in
def g255H11 := limbs80 #[#[0x4006800a002060020001,0x20202040c0001a140820,0x4005002008a127418618,0x806040860a04001060,0x15060c00300182820010,0x44620e92040400200000,0x410908101890c1420,0xd8502040870200006,0x1c48d042048a020c2030,0x3000a30084000c08000,0x19508047030414201060,0x2100028600041020209,0x214480001e1410820281,0xc003060400283362028,0x82828324442000a20285,0xca8302345191200b801,0x8186005488a02181820a,0x184020c215020c203000,0x32001020a080020258,0x8a4003026418836000,0xa2c006021c38a100658,0x2043802054a170814101,0x381090e081110a382111,0x49080e08010022420100,0x7021008682107800c0a4,0x910a54f0636050081c2c,0x10ea80807e284030a000,0xc040871e0c400120410,0x82098d000808e0a30081,0x1018a1000082067c0062,0x85822e041860c6c40200,0x1011028005161c026001],#[0xa2000020398002811c20,0x262820b0c041000a3c1,0x2240830404505001430,0xa2c2161a04004702c585,0x8702122000102040914,0x8102023c101080411500,0x38d04000860000480641,0x140c0a00a00e140c3c,0x40224289009000200787,0x223d24a10002cc0a0000,0x14087141c3890e19182,0x15ec000af9c2741040,0xbd85f50620c97b040000,0x23ba000000000149a,0x199e611a3ac000000000,0xbe946de200035a800197,0x965b4d008003f6461f79,0xd8012b62f762593e4de7,0x87e5cfa04eee0000de08,0x7cf8000000a57882e,0x20d2d4e000225e2e0000,0xfb35761b78273000000,0x137900055d02b000,0x5b9000000002800000,0x175a00000046a80000,0xa6800000009f70000,0x8000001381d38000010c,0x56b3f68c2bfa2,0xd8000000f58000000000,0xd000000000013f6fad00,0xaad0e4001d4d3be00031,0x7be00000073cba427175],#[0x94980000014d3dfee1cb,0xfb0e0000006a1d858000,0x320d77a6ce33468a,0xfa00000000010c400,0x47d400000000000,0x62e43532ad95923c0000,0x51b0000075b32557fad7,0x9568a4814c499,0x861000,0x8eeddcc8c4e0b7475800,0x31541603861c00098558,0x7b8000000000000115c7,0x1f190002f500002660,0xb3159abb0200000015b4,0xe25d0a500037ac85a000,0xa029775960ed2f2934b2,0x232a0a00003a20000bb,0x8b000000132c99e00,0xbe468688ae851b3f99e0,0x691bb73128000000cc21,0x9b6000092fd430000001,0x899994680001c1f000,0x60000d8198000042a800,0x5a0000bc0ed8000bc6d5,0xd10000000000eb380032,0x34805cee860517003bfa,0x74c001ef26922842,0x57d377d6ea00027f00fa,0x5ab8ec54610b737b2c4e,0xe2891a228ee4,0x141f58000000a220001a,0x8a80580000003c8f4686],#[0xa3ac5000343df590000,0x1ce68dcb248003dea,0x48e068a31f4b262e2934,0x28584000442574810de9,0x1f9dbc1cd257e51f1a9a,0x87344049f82232002f8a,0x24d8cd832b7decf2dc38,0x4e1aec14286934b5b012,0x516f6d38170000c8eb92,0x33d78496ccd30f6e22b6,0x38ec4dcf7530c31a092,0x87b59fbf507e261cb2e8,0x740000f2ad3509018adb,0x6f080000001b90006,0x281a0000000000000,0x19b10005c54000000000,0x197c0014743bfa34400,0x740000005e578a600000,0x6b800000112c161e0eb6,0x34ec6deb87fd0d0a39f,0x93100000000002338000,0x2eb8e6f682e967b3dca2,0x79dc000000000000,0x9e3a9330000000032000,0xf50002e1417110f0005e,0x354c10148f5a72aa5d13,0x3a6bc9c,0xaa5c00b5e72d085b4000,0x9f7ac22ea8f619979c50,0xae5f4e0003b9510,0xb64fc22d8f178b200000,0x20c4d580356516ab79bb],#[0xc7a5941b68ea3782119f,0x2aa81ab5af29bb290001,0x1744db9ac9300353ef97,0xf222b28000000936800,0x2f290550005195210ce,0x386060001ded8c6acb00,0x51400000042e883a6d7a,0xac20001184001ef0f00a,0x3d5000184b35219c0001,0x617d000000000140f000,0x3febb9b13fac5dc754af,0x116bc000193f27800009,0xa27c2ce01c2565ab84ba,0xe83f2d84fb8f11,0xc76a32b0be0c33a3e31c,0x3168936b7e0000994000,0xcef28003ac2117c20800,0x2d291019953,0xa10e7f3af3302ea00000,0x353b8e94cb0001b6af,0x5e726a7cf359b0,0x1102,0x6f32914000000,0x4e70000000b8c0a1000,0x8c30a8b18002d0200000,0x572a3c001d1e49a0003b,0x2984c8cda1d02a,0x242e1ac00098a47c4,0xb4b40005ee5a08000d36,0x4000007fd346003af7a4,0xccc876311bd8000000ac,0x75b1b15659433949d655],#[0x12400111a64d41ec0017,0xd3f000000000124b0003,0x30380003bb00011c0e6c,0x62db0000f1fe15a6f759,0x7b27d6c00000008c071,0x69dc000000296177000,0x9255be7dcb86904bd931,0xf84561a4beb46f,0xd4a161c7a5f38000,0x3b3ba81d1257e8001e99,0x30005859a340000b9ac4,0x97090b8f3172cb800081,0xb699080003043b981387,0x43134f9e49b87e788301,0xef86af64fb7a48cb0987,0xb5525829bbbc480017de,0x7e956be3a4c53,0x1d76000721800,0xa92a015fd94000000003,0x63a00004680012,0xf15e320002df5c069890,0xa01b8ef,0xbaa00000057ed5a8000,0xdb348000000000955000,0xc67f944f0003d5800090,0x1b0001581bb4bd300062,0x2a764cee1adafc001c,0x4fb0da80011563a90000,0x14d22531000001aec000,0x443e673c0000530,0x70003315cdf000640800,0xdb5752b1e79c001bae37],#[0xa10de83d53640358957b,0x4d9e7a8f81c0c9006deb,0x9a6041dec2b0c7a,0x39dc000000000259378d,0x9000000157688ebd1000,0x10e600000034a856,0xef6000000000095c00,0xe0c00039e00000023380,0x793b26e3d76d90000,0xc648001e6b79da54315e,0x34d271a066cc7e45f6bb,0x6241400069724b00031c,0x125cac81068001b473c,0x3ca0d800156400000000,0x53c00007de7b1eda420a,0x12fb6647919,0xc00000000019e0000000,0x2876dbd85562bf87647,0xb80000000004ce4000c4,0x870a1392a7c0d4300023,0x7bf97c89e0a9a2c8000c,0x9ed61c539000e000cf16,0x5dae7c80000000c4faff,0x8cfa000196369a000000,0xe91b828d5f98904bdc56,0x540000004c6400173874,0x5e8002698e2d0006b03f,0xcb80002d680038381b7d,0x83feddb8c10e3d59dc87,0xeb9000686e61d143,0xf9719c89e3a000000000,0x230698dd33b27c001ba],#[0x7400000032edd2931100,0x298000a500007ce6950f,0xba88001e9e00095b2,0xc68800000000b0000056,0x58a33f20006e3,0x31aee09618fb3b6b800,0x3800045400021895bd00,0x708000452ec100000012,0x19ac5c23e38000000a,0x3999b48a988000,0xcedb3ead40000b09,0x7000000000080c71cd60,0xd4001e94000076254f21,0xfce86e8438d9a00011,0x3f16b95ab5742cd120,0x11ae4440000000000,0xd8e8000a7f12ef514000,0xe000899ce4738b253c06,0xf0000afae61038000046,0xa0ecd0000001a516106f,0x6d000005ef0898000a,0x347906d7f80007cc0000,0x54e000273e9240000001,0xf86c590d40000,0xe3c3c495b0000000000,0xba7c00054580002f400,0x2517a8038bc9a3176b38,0x6df88b7539f08994001b,0xa2090ea7bbbf00008407,0x211000000011d4290000,0xfc2130d768f1b0f26000,0x33fb87a86d1c1057001],#[0xc800400023fce7f92b00,0xc586b4ab900037285,0x80a000000000327b8210,0x29115440002d0f627dd8,0x19cd312800166fafa,0x7e60eaadd26ef314,0x5e84923e1b50001c0a00,0x7f54473a3d7bee7c37b0,0x36ba574460000002e0e3,0x6b74a6000299615d2831,0x7a9c0f375fd208003414,0x34f9f31c5286403bc33b,0x6c0cc000b4273d80036a,0x23800000166082,0x2f6be701200000000000,0xadc00000043f7cdd65a9,0x6a5b83d2ea0004694d96,0xb95847b0001620076000,0x10000002aba000b8fde4,0x44000000b2b80000009a,0x47917199ef000006db5b,0x35388e76fd464c638b55,0x3a0498c001c89f879,0xb53cd39bb50004d6e3a2,0x6d3acca2d5110f8f2341,0x897b80010f32764e6f04,0x780003d4800034a000e1,0x96200000000020,0x1f2f00000000002cc0,0x6d07a15395cff0004ff8,0x2ba230d0000000ca8d83,0xd57909207e20e5a5e000],#[0x6f0318374860000001ae,0xa60006846e2200000073,0x89986e0002c4e9f8bfad,0x2ce364ec3a4,0x7a53d1e161d4000,0x1a805457958b19c06e46,0x99b84000b6300031fc00,0x3746823d5c000d01e0,0x908001dc918fe39ebf00,0xcb2000000655c00199a8,0x2338ab80001778bc6,0x1f4c0200004a58c1c4a5,0x215300000006a9935800,0x4c000a15bd45e81f6175,0x1346b98ab12c1a89cb17,0xc0d175624b6e9bb7316f,0xbc38b3000241081073a4,0x4e1424000effeed1224,0xbcd1373a551b2a52149,0xc16a000000000034b400,0x2588fb05bb6dcfdbe5fd,0x5059d2dee2afb17030,0x15399937e3dc91b7e0,0x34940000006b20,0x8f0a84fdab0003874000,0x23a4ed6304bcadb50d2c,0x33824a600010f8000d3,0x9d0000001d0e40200000,0x30e2ea55c5359b5f0b,0x656f1fc0003570,0x80007557820000001e04,0x12580002457a88000db0],#[0x8945c000000000000000,0x46d32131085e4e299,0x66c4100015f1fda884c0,0x1eacb58b8dc2763ed2,0x1e0c000000000731c,0x3922000eca800297a000,0x65573d30000fa3ca93ba,0xdc000000000231571b24,0x5f81baf3e66df0003e,0xdb40,0xb29aa240000005210,0x30f0032000000000c000,0x600038827248f945c000,0x3e8ce118510003b7,0x46000d1b42630ccafd00,0x13d4001e8400000019,0x5e964200014720220000,0xdffa9d2caa0000412583,0x1f4000276ada8909,0xb99a53955e71b000177,0x1918000000000000,0xa400025a000000000000,0x2600012720000000001c,0x8300003e40ed3d2e1197,0xa9ed136a77147018fbd5,0x4162d515a9255,0x78001b1e000000000000,0x4a00030d800245000027,0xcd53e31d8d8244618715,0x5b4000000577c35705e9,0x27b00030a897f0005660,0x1e400000000003726000],#[0x3d6000000045d7b8800,0x140000000000003b0a00,0xf04a20002de600000057,0x160c13a450648a501384,0x9c70007b7000174d58e7,0x8002ef614fdb48000000,0x400000043740005404f0,0x2cf605ba992f40002b5,0x7c000ed80001820000b1,0x1d84eba07a06d3cd8c1b,0xe972e020f2fe42b4ebe1,0x75a0b62629027273b,0x2b1a77351eb44db75426,0xeb9e0002504000860800,0x8ad8e0000000000001bc,0xc800058e36760000001a,0x1c180002ce0ecc0008,0xc7700041240000000000,0xe5c51f969e0b1000342d,0xa40b05b74800dc5abc2b,0x12bed3865a27f78d,0x12845c8000ef33a700,0xf95ce8f565539b44a400,0x93848843c53d25437162,0xabf156ddd82024da78bc,0x80004d5d4a94df49346a,0xf00063c3e7a000000442,0x640004a955aea68c2e89,0x545400000000038,0x13750882ade6500,0x15e00000000000,0xcfa17b20000000f6c000],#[0x8b90a2abd767ee0008d4,0xe3e59cfe5c293b744a92,0x9b48577bd4678259c4c5,0x36c83f400043b74b02,0xb09482e20800000111e0,0x26efe1a3fdcb3ea101df,0xacbdc92ca0f3aa644e75,0xbc38a477566a6d7869e,0x110b8df551000339800,0xad00076ff12800000000,0x88f1591c6233765e4b71,0x68d7138db0000dafb134,0xbbb5d7a69fb55789864,0x5ab8f418c7b6696f,0x6575f3792d3854f4d74f,0xb36b85e4800000099336,0x3e906eef4100060933,0x2813336f48f6a3cc0000,0x5d00000007068001,0x7e86000c7ae0c8001452,0x160e80029b31e300002f,0x84a9b20e6bf0,0x6e6e44e8c000f3044580,0xa38000000b2dacbc001b,0x4449fa2674000c4b3161,0x3a6c001493000040fa93,0x907219966e8c95ce000,0x98078000b01000039000,0x124300000000000009f,0x5810000000caca2d40,0xce5c2700000009cb6650,0x138c0000000000002],#[0x7228eb0000247565a000,0xf25d0000001233b45616,0x2ecbf6719,0x9027c3274200000000,0xec729600091f8003df40,0xcf99f75e800034bfbbd,0x32fc0011b854c0002c67,0x3b5c9ef0000000000636,0x539b58a000348000365,0x66000ee0f93636600000,0x213a31d46000fbf74341,0xa2c89016e6afad8537c0,0x11e9c48bc88003,0xb6c580a1ccb0d32ee000,0xdb3a7e0000ad6a8ea5a,0x2e13eab2cfa64400000,0xde000000269e00000000,0x81ca9922d00000000000,0xa21711d37b72e38c4d33,0x3b0d3bed232fa824f053,0x451800026388bc0008bf,0x101f3dfd02f839d3a7c1,0x1d58292800268250987,0xa916e0000cd75832d240,0x2e25a8c0002,0x4d8306a000a4efd40,0x800000000004a8001adf,0x9000000000013fcdf4d2,0xd69e3c43e0aab9c41916,0xa94154e380019321fdac,0x81a02b2576171318001a,0x1e8883cc3c000396d],#[0x80028500000c61b54624,0x95178a49c51b5419c33,0x23cc77ba548000127800,0x173246c746f7ec70c095,0xcbd7263d200000047cb6,0x7880000002d640006aa8,0xf7780000000000000000,0x8000e3c00000000019ae,0x25cfcd23320000006ac,0x359a000245d08bee400,0x54542800000000000000,0xb9409997b00026c80014,0x4710002f58000000503c,0x9644001b3fce40000d31,0x4cc20004b3e49c5a5a68,0x44058980001418003a9,0x792d25635d20f3fa7500,0xfb3b83d5e000bb600035,0x780c3b1d2fc7b1f20004,0xc0580037d868b8e967a1,0x30c92b1163cc17396f9b,0xf0003874aac2b00fe1de,0xad74b7000358879f1b,0x60003205b9a00000000,0xc6d9cacc2b7,0xf880002de167000061b0,0x323a7900000000000001,0xd64c2618003dcc000f65,0x2b690001ce773e45c815,0x1b1fb97172c7940e778,0xa1da0001e3ea3491bc0,0x6366c5df935e49778bf6],#[0x25f3e4a0000000002,0x269c00000002440d8899,0x804434c000a18e4c800,0x5dd0003ca400000,0x6ccb7f23741b5a742d80,0x18c4c4dd7301467635,0x122ce390,0x4c6a601c906af9884000,0xa0000000003992000c3d,0x3a2200094680039f,0xadaab000235000000000,0x150042000009,0xf03802371e4c4001be20,0x90cd47d5e68efcd79283,0x40005fc8613d8194e000,0x800057640000adb992b4,0x1aca203e3568000000aa,0xf687b057944a5f400060,0x55540a0005b8f568124b,0xf1c0001edb983ae14284,0x800143e744ab80268000,0xd8f8cb3ba18001334d23,0xadbeceb7c7e88d89f20f,0x2ec3360001814000b1,0x7f3e6ba6600011e00000,0xe6e23dffb5d9,0x517e5b0d3e0003c20000,0x311ea8000000000,0x4c08000001a03614800,0x743afabae4b800000000,0x7cddf00019efdb3dd019,0xb2e1d4aad00000006bc5],#[0xd2a0000002bc6aced2b3,0xd731ec3c840000002245,0x13e3a04005d5ba227747,0xa0703071e6d000670800,0x7693301e595f081,0x5d0001822000374fbd00,0x1cc5309800130c5273]]
def g255D12 := limbs80 #[#[0xe1582a8540a20483fffb,0x54ea1d71ac3546a0d31a,0xabad65ae9592aa573ac7,0x17a4d8f42d0760e8015d,0x3aed8b16b328493a0670,0x2c24058f4fcef2744cff,0x284840201c30341c4c44,0xd070b108f0c869880058,0x29b92100e118f8d8b910,0xb81dba93c083f022841,0x1fdc40a10fec10a10ffa,0x313bfbe105087f790142,0x4ca01ef34041ca0fc240,0x2ff4000a507cb500e50b,0xa2ff4200528bf900814a,0x507fc0840a517f320014,0xa0ff92800e507fe0c00e,0x1cffea881ca0ffca289c,0x358a0]]
set_option maxRecDepth 32000 in
def g255H12 := limbs80 #[#[0x40c18026197020070180,0x81938c1010a14106061,0xe0002003a502009830a,0x190c6043422005037c0,0x2106833008ad00200,0x334080da1044f8f1a082,0x12183050614404081408,0xbaf765832000000013ab,0x90d92408a732d0000012,0xdbc24c0043e0000015c4,0x2971000043555193c14,0xf00069852ecf80051f00,0x6e6a76001420800009,0x62720917979e751e90cc,0x300088ba6e4966328000,0x1f30e81e915169c35602,0x82261479a33962688009,0x40007b20b8fe6a037979,0xa000d5719a26ae54191a,0xbfd4e3ae29e4a66c5452,0x18ba41800e1a0ac312,0x6901191006a7bc400486,0xd37d0dcd0400e9f8b18b,0x542d8a500155092fddbc,0xcd1f31710040e4f0abf,0x2780011eabe000cba8b,0x4c0016b000097ae40000,0x3861e01d4dd91f706ce9,0x745000a3000650421,0x4e9922b1123a6d296000,0x480019480046dd11ce64,0x145c006f5c0c82c002],#[0xd53001276e240025572b,0xffa3e1ec2200240c6b58,0x86000c26896491250011,0x14525d13d1b2976,0x908d229a48e2642b8d1a,0x62001324075ec8b737b2,0x14a48ed828be85f1c4,0x3656f20d0a786fa2849e,0x321b5de36cab8fb5b400,0x56001b1fa47108862dca,0x1d4c9846abb000003288,0xfca97262126f1ce04ce8,0x44000fe0014e00000019,0x5ecf01ae001548000e34,0xea4cce000a200093a002,0x3e140011d0a323a09206,0x1faa10715972,0x18d7669a4f41df9214f0,0x862ab486abfc6649c92c,0x91a82e3a4266301899c,0x420011054da87c8a3008,0x5f943856b098532cc8db,0xc9f89826144d97f0b63b,0xc0062c20f41b4f8009d,0xa0412d2a002056dd1975,0x44206d1a802000626001,0x19a60022d00028200000,0xfa0e1ab0000318ab7ee0,0x6690000e3c002996604,0x62aa15a67c219aeb5001,0xc8000000009d44e64596,0xf800000000000dced2e1],#[0x2a555400000cca001570,0xea88006d5000c600020f,0xd0cd8d2a428b621]]
def g255D13 (j : Nat) := if j=0 then 0x910142030c007ff else 0
def g255H13 := limbs80 #[#[0x500a000c01c800089807,0x480804d015330f93c406,0x4f3b1a1a0ab9eb]]
def g255L : Nat → Packing
  | 7 => (45,6,7,1835037,85,9,4099,g255D7)
  | 8 => (550,5,7,12517674,137,13,4230,g255D8)
  | 9 => (2070,4,7,14025635,138,16,1480,g255D9)
  | 10 => (1977,3,7,4260142,121,17,4397,g255D10)
  | 11 => (344,2,7,786453,69,15,4223,g255D11)
  | 12 => (21,1,7,131073,16,10,4129,g255D12)
  | 13 => (1,0,7,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupShort 11 113 4 8 6 0 g255H8
  | 9 => lookupShort 137 821 6 12 10 0 g255H9
  | 10 => lookupShort 517 2549 8 14 12 0 g255H10
  | 11 => lookupShort 494 2927 7 13 11 0 g255H11
  | 12 => lookupShort 86 431 7 11 9 0 g255H12
  | 13 => lookupShort 5 29 4 7 5 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sample10 : CutRow g255 10 270 48 := by
  apply partitionSound rfl (fun _ => 0) 270 [(48,9,3,0)]
  simp only [partitionChecks,partCheck,cells,boxes,and_true]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sample11 : CutRow g255 11 275 48 := by
  apply partitionSound rfl (fun _ => 0) 275 [(48,10,3,0)]
  simp only [partitionChecks,partCheck,cells,boxes,and_true]
  repeat' apply And.intro
  all_goals decide +kernel
end PEqualNP.Outside.L_meta_32748
