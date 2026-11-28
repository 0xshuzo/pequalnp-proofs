import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_35692.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_35692
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffafffffffeffffffee,0xfefefefeeeccaa00ffff,0xffffffffffffffffffff,0xfffffffafffffffeffff,0xffeefefefefeeeccaa00]))
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
    let width := ow % 32
    let delta := (ow/32)%32
    let span := ow/1024
    let head := if span=0 then 0 else ((num+span-1)/span)*width
    let pairs := if span=0 then off+num*width else off+head+num*delta
    let pointer := if span=0 then packedAt data (off+i*width) width else
      packedAt data (off+(i/span)*width) width + packedAt data (off+head+i*delta) delta
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+pointer
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

private def countBits64 (x : Nat) : Nat :=
  let a := x - ((x >>> 1) &&& 0x5555555555555555)
  let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  ((c * 0x0101010101010101) >>> 56) &&& 127

private def wavePosition (data : Nat → Nat) (pw : Nat) :
    List (Nat × Nat) → Nat → Nat → Nat × Nat
  | [], pos, label => (pos,label)
  | (offset,zeros)::tail, pos, label =>
    let start := offset+(pos/64)*(64+pw)
    let bits := packedAt data start 64
    let n := pos % 64
    let rank := packedAt data (start+64) pw + countBits64 (bits &&& ((1 <<< n)-1))
    if bits.testBit n then wavePosition data pw tail (zeros+rank) (2*label+1)
    else wavePosition data pw tail (pos-rank) (2*label)

private def indexWave (width maxKind pw tail iw aw : Nat) (levels : List (Nat × Nat))
    (ranges : Array (Nat × Nat)) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % width
  let t := h/width
  let b := width+t % width
  let t2 := t/width
  let c := 2*width+t2 % width
  let pick := (packedAt data (2*a) 2 + packedAt data (2*b) 2 + packedAt data (2*c) 2) % 3
  let v := if pick=0 then a else if pick=1 then b else c
  if packedAt data (6*width+v) 1 != (t2/width) % 2 then none else
    let z := wavePosition data pw levels v 0
    let bounds := ranges[z.2]?.getD (0,0)
    let i := z.1-bounds.1
    if z.2 < maxKind then some (bounds.2+i,0)
    else if z.2=maxKind then
      let val := packedAt data (tail+i*(iw+aw)) (iw+aw)
      some (val &&& ((1 <<< iw)-1),val >>> iw)
    else none



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
private def groupWidth (rs : List (Nat × Nat × Nat)) : Nat := (rs.map Prod.fst).sum

private def groupProof (g : Forest) (k : Nat) : Nat → List (Nat × Nat × Nat) → Prop
  | _, [] => True
  | start, (n,a,d)::rs => cells g k start n a 0 d ∧ groupProof g k (start+n) rs

private theorem groupBlock {g k} (start : Nat) (rs : List (Nat × Nat × Nat))
    (h : groupProof g k start rs) : block g k start (groupWidth rs) = true := by
  induction rs generalizing start with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨n,a,d⟩ := r
    exact block_merge (cellsBlock h.1) (ih (start+n) h.2)

def smallCircuit : Circuit := ⟨[⟨.or,[5,6]⟩,⟨.or,[0,2]⟩,⟨.or,[3,4]⟩,⟨.or,[3,8]⟩,⟨.or,[4,8]⟩,⟨.or,[0,7]⟩,⟨.or,[1,7]⟩,⟨.or,[5,7]⟩,⟨.and,[14,12]⟩,⟨.and,[15,9]⟩,⟨.and,[13,11]⟩,⟨.and,[6,10]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low9 : Lower true (varsX 9) (graphGoal 9) 1 := by
  have q := @lower_count true (vars 9) (graphGoal 9) (proper_of _ (by decide +kernel)) (graphPairs 9 3) (by decide +kernel)
  exact q
def K9 := extendKnown [] 1 [(18,[16,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V9 : Known true K9 := extend_ok (m:=9) baseKnown low9 (by decide +kernel)
private def selectedPanel (n : Nat) (data : Nat → Nat) : Array (Bits × Bits) := Id.run do
  let part := fun (j : Nat) =>
    let off := n*j
    let base := off/80
    let word := data base ||| (data (base+1) <<< 80) ||| (data (base+2) <<< 160)
    let x := (word >>> (off % 80)) &&& ((1 <<< n)-1)
    let y := if x.testBit 0 then x + ((1 <<< 152)-(1 <<< n)) else x
    BitVec.ofNat 152 y
  return ((List.range 9).map fun j => (part (2*j), part (2*j+1))).toArray

def g73Y := selectedPanel 6 (limbs80 #[#[0x3c0000004b300000014f,0xa]])
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
theorem sample73 : block g73 3 0 1=true := by
  apply groupBlock 0 [(1,3,3)]
  simp only [groupProof,cells,boxes,and_true]
  repeat' apply And.intro
  all_goals decide +kernel

def g223Y := selectedPanel 108 (limbs80 #[#[0x3e10821a185c0e95adbe,0x440694241cf510202,0x2657ce74100874a00802,0xa5001dc021141001af12,0x6211430006c122613ce2,0x2a766ed2846e3cc,0x766ed42e8c0000c207e0,0xe95effe0000e0842002a,0x18041e305d3878b742,0x830192050a109e30603f,0x7f3909e1568940000000,0x181c003e007e03f61c0,0x8040401121806c31043,0x4311c3180,0x0,0x0,0x7ffc081ff80000000,0x804900009ea41fe01fc,0x41820000021500086950,0x1fffff80000fe0000,0xf19000a40000000604fe,0x6a1000ab5]])
def g223C : List ColumnInfo := [(4,0,219,0,10),(0,4,91,128,9),(1,0,222,0,9),(2,0,221,0,9),(8,0,215,0,9),(16,0,207,0,9),(6,0,217,0,8),(18,0,205,0,8),(20,0,203,0,8),(64,0,159,0,8),(128,0,91,0,8),(128,4,91,0,8),(0,2,141,80,7),(5,0,218,0,7),(9,0,214,0,7),(12,0,211,0,7),(68,0,155,0,7),(1,4,90,128,6),(2,4,89,128,6),(3,0,220,0,6),(4,2,137,80,6),(8,4,83,128,6),(10,0,213,0,6),(16,2,141,64,6),(16,4,75,128,6),(17,0,206,0,6),(24,0,199,0,6),(64,2,141,16,6),(66,0,157,0,6),(7,0,216,0,5),(9,4,82,128,5),(11,0,212,0,5),(13,0,210,0,5),(18,4,73,128,5),(19,0,204,0,5),(21,0,202,0,5),(28,0,195,0,5),(65,0,158,0,5),(68,2,137,16,5),(72,0,151,0,5),(80,0,141,0,5),(80,2,141,0,5),(129,0,90,0,5),(129,4,90,0,5),(130,0,89,0,5),(130,4,89,0,5),(136,0,83,0,5),(136,4,83,0,5),(144,0,75,0,5),(144,4,75,0,5),(15,0,208,0,4),(23,0,200,0,4),(25,0,198,0,4),(69,0,154,0,4),(73,0,150,0,4),(76,0,147,0,4),(84,0,137,0,4),(84,2,137,0,4),(137,0,82,0,4),(137,4,82,0,4),(146,4,73,0,4),(5,8,18,192,3)]
def g223A : List (List Nat) := [[],[48]]
set_option maxRecDepth 32000 in
def g223D5 := limbs80 #[#[0x585504c195dcf6254110,0x4c17454f625413059153,0x54f625413065553d8950,0x5513064b9061d544c198,0x6a587d8b514c192e4587,0x617624c1a961d54d8930,0x501a961f54d893069f94,0x595645414029d6558550,0x5414025d9459550500a7,0x29d95d89505015350f62,0xd8950500a565f6254140,0x50197d4f625414028d98,0xdcf625414065773d8950,0x5814025d905955450198,0x29d6555161500a759554,0x55362500a761554d8940,0x503a066175d894029587,0xe4575d8940e85985d762,0xd89506a39054f6254198,0x61f915d36254187e4554,0x61f6254393e4185d8950,0x5439364587d895065093,0xe4d87d895024f9061f62,0xd89506879361f6254194,0x6839459554585a4e4d87,0x61564585a0e518655161,0x584a8640755956168394,0xe4d8059561682981d565,0x5c3515d39060f62d4075,0x6459061f62d47a066362,0x61d54d89a0e517555362,0xd89a0e518755362e4590],#[0xe45545c36268197e0554,0x5c3626a39155170d8998,0xe8198d5170d8a98e4554,0x60175d89a0e51855d362,0xd8984e4d805d762e4d81,0xc1ea0f307328d90e1175,0x72d2952c98e34b1958b1,0x951c68c743aa1cce1668,0x2958cac2d54aa8d478a3,0x31dc52e0d705b24d90eb,0x985c52c71634b0e5871c,0xda0bba5146d2af82750b,0x13b3ad26ccf03ba85d28,0xbab016eb60fb3e0b2d86,0x4e35d015db16516cd512,0xeec6407bad06ecf24bb3,0xcd83bb19986cd749b908,0x73a36d0ec6d4bb34966,0xbb3d45ece945b3343ecf,0x1e8ded2574a3b82ec093,0x42ec0773a3c4aece73bb,0xec083bb3cdbe9397fa44,0x8577a7449ecf055b0b02,0x4db4b0eecde49b340c2d,0xb371ce8ef55b3a9d28f7,0x1196cd61fb3a08ecdd3b,0x1660e4bb3012edc383b7,0xc0a79a381a6ccb89940a,0x23fb085be92265b3302e,0xbb37dde83b75a48e0660,0x1002000899738eecf43,0x850120400e0300a02006],#[0x896238861f8731ac6216,0x4dd344c62f8b62b8a627,0x51d4550d414fd3d4ed39,0x55d5554d5153d4d52d49,0x5a16658d6157d5d56d59,0xdeb789da749c96f5b56a,0xe2b88e1b84e0b80dfb7c,0x3f43d475c4d0290e3b8c,0xd84d07bc5dc,0x80004010100000000000,0x180,0x643484,0x0,0x28200016420000000000,0x4000003a8201]]
set_option maxRecDepth 32000 in
def g223D6 := limbs80 #[#[0x54f625411054d8254110,0x66362541106576254110,0x5977354110dcf6254110,0xe416354d1064f6254510,0x66153d891060d53d8910,0xa5d85d8910e4183d8910,0xa1d5350d2061773d8910,0xdd55350d20a5d5350d20,0xa5d5450d20a1d5450d20,0xa1d8550d20dd55450d20,0xe418550d20a5d8550d20,0x6628550d20e458550d20,0x6177350d205537350d20,0x6177550d20a177350d20,0xe458454d20e418454d20,0x6138054d205538054d20,0xa1f8054d206538054d20,0xdd78054d20dd38054d20,0x60f8155120e418355120,0xa1f815512064f8155120,0xdd78155120a5f8155120,0x54d5254130e4554dcd20,0x59153541305515354130,0x5d153541305955354130,0x61953541306115354130,0x591615413054d6154130,0x5d161541305956154130,0x5956354130e0d6154130,0x61963541305d16354130,0x5d164541305956454130,0x99574541306497454130,0xe4d825413054d8254130],#[0x5d3625413054f6254130,0x657625413064f6254130,0xe0f62541306636254130,0x5956455130a617454930,0x66176551306497455130,0xe4187551306498755130,0x5955458130e458755130,0x55163581305d15458130,0x5d563581305d16358130,0x5d56558130d516358130,0x597545813058f5158130,0x591545853064f5458130,0x5d154585305955458530,0x21565585305d16458530,0x64165585305d56558530,0x597545853065d6558530,0x65f84595306435458530,0xa15825d130615825d130,0x611825d530e41815d530,0x60b805d530e41825d530,0xd8980d453066176d4530,0x64362d453061f62d4530,0x66176d513066362d4530,0x5d154d893059580d5130,0x61554d893061154d8930,0x66154d893061d54d8930,0x61174d8930e4554d8930,0x66174d893061574d8930,0x66175d8930e5574d8930,0xe5175d8930e4175d8930,0x5d180d893055180d8930,0xd5180d89305d580d8930],#[0x64185d8930e5584d8930,0xe5185d893065d85d8930,0x61754d8930e5d85d8930,0x64354d893061f54d8930,0x5d56550d4066354d8930,0x54d43541406497550d40,0x595435414058d4354140,0x50d52541409954354140,0xdd9535414058d5354140,0x50d61541405955454140,0x595615414054d6154140,0xe116154140dcd6154140,0xe4d64541405956454140,0x5d9655414025d6554140,0x50d72541406516554140,0x255765414054d7254140,0x54d825414050d8254140,0x24d8654140e518254140,0x5db53541405935354140,0x54f625414050f6254140,0x65362541405536254140,0x65f62541406576254140,0xd4f62541406636254140,0xe136254140dcf6254140,0x59773541405937354140,0xe1d435494061b7354140,0xe416354d405956354d40,0xe418254d4061d8254d40,0x5938054d4058f8054d40,0x25d6555140a1f8054d40,0x64165551405d96555140,0x59781551402557655140],#[0x58d43581405978355140,0x59554581405954358140,0xe4d5458140e455458140,0x25d6558140dd56358140,0x9d565581405d56558140,0x65353581405975358140,0x59773581405537358140,0x59553585405954358540,0x5955458540e415358540,0x5d564585406595458540,0x655645854064d6458540,0x25d6558540dd56458540,0x64165585405d56558540,0xa5d655854065d6558540,0x5537358540e517558540,0x59773585405937358540,0x25d65591405538058d40,0x9d565591405d56559140,0x25576595405978359140,0x21d845954021d8059540,0xe458759540e418759540,0x65275595406427559540,0x60d825d54065d535c940,0x60b815d540e51825d540,0xe1b815d54061b815d540,0x59564d4d40614855d940,0x59180d4d405d965d4d40,0x59584d4d4059580d4d40,0x61d43d89405d543d8940,0x60d53d8940dd543d8940,0x61d53d894061553d8940,0xe4153d894066153d8940],#[0x61554d8940e5d53d8940,0x66154d894061d54d8940,0xe4d54d8940e4554d8940,0x61d75d894066173d8940,0xe4575d894066175d8940,0xe5175d8940e4d75d8940,0x55180d894050d80d8940,0x65580d89405d580d8940,0xa5580d89409d580d8940,0xdcd80d8940d4d80d8940,0x5d583d8940dd580d8940,0xe4183d8940dd583d8940,0x64d84d89405d584d8940,0x9d584d894065584d8940,0xdd584d8940a5584d8940,0xe5584d8940e4d84d8940,0x64185d894025d85d8940,0xa5d85d894065d85d8940,0xe5d85d8940e4d85d8940,0x64d87d894025587d8940,0xa5587d894065587d8940,0xe5587d8940e4d87d8940,0x61e75d894061675d8940,0x65275d894064275d8940,0x61753d894061353d8940,0x64353d894061f53d8940,0x66353d894065353d8940,0x61373d894055373d8940,0x66373d894061773d8940,0x59554dcd4066375d8940,0x65f625455059564dcd40,0x5db815515065b8054d50],#[0x65953581505955358150,0xdd15458150dcd5358150,0xdd16358150e455458150,0x65165581506456558150,0x5977358150e457458150,0xe0f73581506537358150,0x597835815064f7458150,0xe4153585506538358150,0xa5d645855065d6458550,0x64d65585502616558550,0xe4165585506516558550,0x65b53585505957458550,0x59773585505937358550,0xe0f73585506537358550,0x643835855064f7458550,0xe416558d50a5f8358550,0x643835915064f7458d50,0x65f625c550e0f8059550,0x5d3835c950e41735c950,0x610835d9505db815d150,0xe0d815d95020d815d950,0x20f805d950e41815d950,0x647835d950613835d950,0xe43835d950653835d950,0x61d53d895061553d8950,0x61d54d8950e4153d8950,0xdd154d895066154d8950,0x66173d8950e4554d8950,0x66174d895061d74d8950,0x54d80d8950e4574d8950,0x5d180d895055180d8950,0x65180d895064580d8950],#[0xdcd80d8950d4d80d8950,0xe4d80d8950dd180d8950,0x65d84d8950dd183d8950,0xe4d84d8950a5d84d8950,0xe5d84d8950e5584d8950,0x64d85d895064585d8950,0xe4185d895065185d8950,0x24d87d8950e4d85d8950,0x64d87d895064587d8950,0xe4187d895065187d8950,0xe4d87d8950e4587d8950,0x61f53d8950e5187d8950,0x61373d895066353d8950,0x65373d895061773d8950,0x61f74d895066373d8950,0x66374d895064f74d8950,0x65f62dc55060f62dc550,0x61164dcd5066362dc550,0x61182dcd50e4d64dcd50,0x65d80d8951e4584dcd50,0x64f62dc151a5d80d8951,0x64f80591546416559154,0x593715c1546438459554,0xe1b715c15460b715c154,0x643845d954e05805d954,0x59183dc154e4d64dc154,0x61980dc554e4164dc554,0xe05805516064186dc554,0x65f815516061f8155160,0x6438355160a1f8155160,0xe43835d560e0f8059560,0xe4d80d5160e4187d4560],#[0x61154dcd60e4187d5160,0x64354dcd60e4d54dcd60,0x64165551616416455161,0x6418655161e516555161,0xe518559161e518655161,0xa6075595616407559561,0x24d80595611d58059561,0x1d78059561e4d8059561,0x6438459561e138059561,0x59580d516164165d5161,0x64186d5161e4d80d5161,0x643845956459583dc161,0xe0d715c165643845d564,0x24d80dd1655d3835c165,0x595735875064d6558750,0xe517358f5064d7658750,0x5d383593505d38058f50,0x60d73d8b5064f625c750,0x66173d8b5061573d8b50,0x61174d8b50e5173d8b50,0x66174d8b5061574d8b50,0x5d183d8b50e4574d8b50,0x65d84d8b50e4183d8b50,0x64d85d8b50e4d84d8b50,0x64d87d8b5065185d8b50,0xe5187d8b50e4d87d8b50,0x643625c3516417658751,0xe0f625c351663625c351,0x65d80d8b51605805db51,0x64187d8b51e4d80d8b51,0x6417455362e4187d8b51,0x6417555362e417455362],#[0xe058055362e517555362,0xe4187553626418755362,0xe518755362e458755362,0x64f80553625d38055362,0x5d3815536265f8055362,0x61f81553625d78155362,0x65f81553626438155362,0x661545c362641545c362,0xe15545c362a61545c362,0xe4d545c362e45545c362,0x615815c362e61545c362,0xa15845c362615845c362,0xe4d855c362e41855c362,0x652855c362642855c362,0x643545c362662855c362,0x553835c362663545c362,0x657835c362653835c362,0x615805d362d53835c362,0xe45855d362a15805d362,0x662855d362e51855d362,0x657805d36264f805d362,0x24d805d762643855d362,0x611805d762605805d762,0xe4d805d762e05805d762,0x613805d762607805d762,0x64f805d762647805d762,0xe07805d762653805d762,0xe13805d762e0f805d762,0x64175d5362643845d762,0x65d80d53625d580d5362,0x64187d5362e4d80d5362,0x787386f85fe4187d5362],#[0x8db87e87d87b87a87987,0x6793d8fa8f98f38eb8e7,0xd9a799d97a97997396b9,0x9f29ea9da9d69c79b59a,0x73a6da6ba67a5ba3b9f8,0xda9da7ca7aa79a76a75a,0xadaad9ad3acbab6ab5aa,0x17b0faf8af2aeaae9ae3,0xcb36b35b2db27b1eb1db,0xb5ab56b53b4db4bb47b3,0x8eb8db87b72b71b69b63,0x4bc6bb4bacb9cb96b95b,0xc72c6dc6bc67c5bc3dbd,0x9dc8fc7ac79c76c75c73,0x6cd2ccbcb6cb5cadc9ec,0xcf2ceace9ce6cdacd9cd,0x36d2dd1ed1dd17d0fcf8,0x2d6ad69d63d5ad52d4ed,0xd9cd96d95d8ed8dd78d7,0x17e0fde2dd2dcadb4dac,0x6e53e4be36e2de1ee1de,0xe72e6ae69e63e5ae59e5,0xc9ec6ea6e9ce96e8ee78,0x6f15f0ef0dee8ed2ecae,0xf52f49f46f2cf26f1cf1,0xc4fc2f94f8cf86f61f54,0xe8df602e8e1e02e8e38f,0x8d08046a1ea66e4d8002,0x796666040046a10902e,0x9f5924d937665c4005e8,0xd24e8df92fe8d710ee81,0x47e820984650ad615955],#[0xe594cb94dd17c80594b5,0x6a0f837e8ce247e90ef7,0x856787618896c660af22,0xcf36c6512133e90ef25e,0x5c15aa5cca15944e8761,0x18d614f806e9c6c71595,0xa4594961ee800606e922,0x2e923014e8df55826059,0x650405da1c1d3c691512,0x8d9d06e8d3a4d68dcf85,0x11022e8d187165c5f24e,0x4a3ee9051466901a3469,0xf916147aa95cc9e1f298,0x6e8e295ae4e2e2869c7,0x75d8f797594f56961572,0xe9c370668d2599595b78,0x9c736de4d817525cbda3,0x4327b5d0425d6621206e,0x490669dee1de8c03ae59,0x263611ce70595df3ee8d,0x22e904a905d601696617,0x6e802506ea476a159543,0xe922c12e8da128e81273,0xa0dd27e86230e6812522,0x20d36e841fa2e8ddd232,0xcaae594365e6484b5de8,0x71ce94a927e820a8168d,0x8d6157561595bb1b6a4a,0xe61c87316a17206e8e08,0x69195696152e5d645fb5,0x4c81b054c9328e947d5a,0x5153e69c4f81e8dca6d6],#[0x840b6a10598e8d4d27e8,0xe7265c5522691862468d,0x72595c327e863177654a,0x8e920a0f6995e2768c27,0x25c9c3a69cc920e9522a,0x8d9a16e8dd786e4ca075,0xc000e6940a85660402fe,0x7a226a10b06e8e2a85e4,0x64b681c65ae122f5d61d,0xe6a46922692245d61d7,0xb6a51bac5948c3ce945a,0x68c9a20e959044e8c050,0x8dcc39e905c0668d9644,0x60f3568c6922e94754d6,0xda80e4d5f986189013e8,0x222e9d1aa96882f25e85,0x7765ca76d60cff14e81e,0x26a06f70595a435e8d0f,0x68d8d34e811906e92332,0x94c53769ce38ee8d970e,0x20f8565445a4e9c957e5,0xfb82650d95ee9cac14e8,0x865615055ee821e24e8d,0x37e8cbc24e8d71a0e90d,0xfe85470e6918d31e818c,0x6820022e92326ce81034,0x8c4432e8cf922e918541,0x3260595d422e95371de,0x345a6518f7165c58aa5d,0xc14e8e1d24e8e3d06e8e,0x6464dbc31e957f2869c7,0xee80773ae90530d6a176],#[0xa621227e8cef5d65e0c5,0x193b06e94776764d625d,0x538815955d24e8cb6876,0xcf69e4d8d0b68d1f066a,0xd0d6a0742869c6971e5c,0x1168cee7be422b5d6820,0x6e51d927e861f0669d24,0x69193346811c14e821e5,0x940d4ee8d4991e817128,0x47524e8d2272658b1436,0x7d06e921c25e8cf057e5,0x73ee8ccd5ae51e336e85,0x28682364f681cc0ce8d7,0x8e8d0e2869023a75d02c,0x6822228682179edcd7b2,0xa4fda1e90c828e808228,0xdf624e8e15a129cc306e,0x710e8db14ce90c806e8,0x917681c95da5c16575d2,0x7729c0224e8d0855e552,0x265c4d25e8d665e660ae,0x65cad8de9502985954b7,0x161200ea4f20ee819c77,0xe0381594605c6516b5de,0x827e85eb70595600668,0x64b691cf5ee81e55a28d,0x36e841ea1e9c9812e8df,0x8e80615ae4d903868ce5,0x69c2d0be8d0324aa58f0,0x8e388568c4336e802644,0xd08af54c9d3c68cd606e,0x740668d2b81aa1ca06e8],#[0xc57e91e927e85a50ee81,0x2769e0127e820b6d28ca,0xa65ca881595480b6a530,0xe820d226921187595e17,0x81a220e960f9361d0427,0x4657661363ae8cc80ee,0xcaad594c47e654c22868,0x556e51688d295027265c,0xad680d12168ce7a45943,0x8594b84b6905b6d66045,0xe4603a129c984ae8daa9,0x806d5ea5c1506ea5385d,0xde424e8d90416941008e,0xa10e681884f68d558ee8,0x303aa56857e9d0385e4c,0x36e850e77294ab0e6808,0x1e823a3ee945028e8192,0x654182468d2611682269,0x84180e68124776540478,0xd4908e80683fe81deabe,0xa85ea1c1c06e9539a3e8,0xd28e81915ae8de584654,0x7e59499615954e69660a,0x9e81d32869d1054e59b5,0x68df35ae4e2c5d645fc9,0x8d9f57660fa1168dfe06,0x51e5565c85875d8c006e,0x3e0669e3ca0e84e257dd,0x82269d1ca95d03e85e50,0x24e8d730669d87736515,0xee44150ee81063c698dd,0xe8e1f8a595e081594d06],#[0x95427be4e1803ea56724,0xc0122e91ed0e69517a35,0x8e28681a8a0594598564,0x506e907928e806269e81,0x5ee0df527e8462286823,0x66a51661595bf2ce8dd1,0xe8cf427e8592206940b0,0x50a125e8db60b6912438,0xd1608ea4b224e8c0c84e,0x2f5e61d2e8a5d8f62468,0x66de819584654af8fe18,0x9a6188c06e9628066a1e,0xd6150b36e842024e8d85,0xe9cd23de8d5053e842c8,0x95957265c3a0e6a51073,0x5a024e8d928de91e85a6,0x6a276a10927e862d066a,0x693e52045a68595066a4,0x95dcd7b2268d1d6c660a,0x969c5ba0594dd1d6a445,0x65c4722e9202a15d8923,0xa5843568c7f24e8d996f,0xdf628e8108a4e84c8066,0x88ae5903206e8da25a28,0x3a3e8c537d595b406e9c,0x54658f10b691259524d9,0x1595449d6810134e8103,0x594b05565d2c5e61d338,0x81c806e822749e8019a1,0x4a63ce9cd514e81f62b6,0x8b25e8d3f09e95798465,0x6ce90ac57e91089b618],#[0x58260dc12e8e0f62651d,0x4682141c6a4a812e8d63,0x6a10a29e85e024e8e381,0x90145a28e1ea0e9cd106,0x4072be91c724e8d28226,0xbfad59094812a1ca8059,0x61c6a4a624e8e02a05d8,0x13e861b8a5d86e5e6106,0x7660f822e9d015de8508,0x5d51e5ea1c2434e8d0d5,0x95085ae4d94146a4ae57,0x225de863495e8c7e06e,0xe906691f215e8dca286a,0x143e8dff20e944a5b24c,0x15681cb77e94aba5dd4c,0xce8cd324e8d9aa55d04f,0x65c5795e819528e81e53,0x11ce5de460214e81a973,0xd095ae51958b2a0d363e,0x1722e8de755e56175d61,0x469660a7066a4860ee80,0x3ce915056e51696b6610,0xc68ca224e8de53268cb3,0x6a100a25955b06691951,0x8caa5d61c7446e8c8a06,0x4df066a0787e658a41be,0xdb60e55d6a3594387165,0x460261565ee81085ce41,0x5c20d6aae68c34336a10,0xbe91c528e823b1b6a401,0x5d63c066a62255615e64,0x1dce346811b93e851855],#[0x14694dd50c06ea532632,0x839be188b945d07c4ce9,0xc5d661095ae85950669c,0x1be94ab4f681cf45e943,0x3e41cd28e807728e81f9,0xe81f1726580588e1cb48,0xa61f20e959224e8d7828,0x4af4068cbb5be4ce9066,0x8741e94483de8cda1c6a,0x824e8da706e8e1e69614,0x87595b335e80fb4be90d,0x468d20146821328e8065,0xe846524e8d38556150a2,0x15095ae5cfb7a6504127,0xc5d07ea5b87a65ca6906,0xff22e8e0614692188364,0xa34e950c3de8df46c610,0x725954a226a0fa14e921,0x8615765e66041a75d88b,0xe856e34691122668ce66,0x850d286812906e91e525,0x9bd06e96205d6142a9fe,0xc077e9c4342684be64e5,0xa53e84300ae8dac5c24d,0x20e952d69e819833e851,0x1595618de9d0128e9d0f,0x681528d29d0124e8e166,0xa441226912992e8cf94f,0x1239e8cd8a15d4c2146,0xd80ce8d7950e80d4226a,0xf69615336de8c44892a0,0x34e811a7a650ae7b5d03],#[0x66a47269614ff25e856c,0xe94de2768c298ee8d9a0,0x4d9351e844f0e6a5123c,0x2136ae50a372654cd95e,0x81a7dd88b8d6146f066a,0x85ae8e1e91e819728691,0x22e91905ea1c1533e851,0x76153c0d6a17a5f595ab,0xe858c4fe8153af54ca08,0x8d3e8ee8d718c6183830,0xcfca15943b20ea2391ae,0xe77465c5473e545a55e5,0x714e9caa5e6812501aa4,0x55655385761d2f20e950,0xe6588d5be4df887595c1,0x590d012e8e1e77654417,0x8c3d0ee80095e6086482,0xc9b5c24ce8a4e805c446,0x10a15d88d27e86343ae8,0x815954f6ce550d20696,0x945d50c44e9c2e5a64da,0x269d1b08e8049935d201,0xe918a14e8cab9c615042,0x90aa28e812850e80d52e,0xd325d685fc06e9d08846,0x454fe815480e8d4124e8,0x7ad594933e68cc73e68d,0xa029cd15765c7028e906,0x8e8190226a1365c24dbe,0x69c808564ca70ee81082,0x9d350b6a10b5ee81f606,0x18a21e916d3e69c5206e],#[0xed5da1c16346911131e8,0x228e81a7805945628e80,0x6d660405a28e385d6a21,0xfe805e6f5d8eba75d02d,0x68c9f18e8dd127e85283,0x9183a1e9cc32ce8dd544,0x23725e8db885654400e6,0x3b5d6a02a48e84195765,0x722e91085ae8e3824e8e,0x70595c22ee9502576553,0xfdd5ce0668e3e2868237,0xe957e81e4d553b68ce17,0x919597e1892346950c31,0x1258ce9c390ee80fe5ae,0x142aea1d272658a55769,0x20b6a51c4f691552468c,0x206952339e94da2869d1,0xbe4db082e80d24de8dc5,0x68c1106e9cfe8664ca65,0x8dd82d6a05212e8e3846,0x17031e818b79e920d0ae,0x11686157a79e522531e8,0x40b6951e066a52d0e6a5,0x96e850e2fe8d972868d1,0xfe81dc5565d311168200,0x6952a5d649a65ee9c444,0x9df055e950854659af06,0xca997594b987595a320e,0x876de4d93076a5ba1ce8,0xa8164d5514e80ec0e681,0x22e94f926e81675d6602,0x5aa5cf4de8dd2a429c95],#[0x680e30669dfa5761d051,0x1c6b1be8c02556159b4c,0x54c28e80796c610b75e6,0x286c611335ce5ca37259,0xe34e910e286a4222768c,0xe6a0ff5ae8d08a05d4c,0x4e8ca5af54ca62268205,0xe518f28e907e2ae95c74,0xa4ad0e6a47fad690955a,0xe0f22e91a773654de1b6,0xac555d607a55d4c124e8,0x65a65195a65d0336de8c,0x41e95fd74e596f276852,0xf6182f41e91ff20e9602,0xe850327e856535e80088,0x8e3936e847c14e9c436b,0xd3d06e8de9656150b43e,0x7b2868d82a2e8d5912e8,0xc5daa212066908455614,0x31e8197af54c8f36e857,0xbe8219875d4e497594e0,0xaa4e65ea1cb76d24d937,0x5624a35d82e6f595b208,0xf5765d3028e804a55e,0x13a1594cc066a599246a,0x7086a4ba93e920b20694,0x556159e7729caa3d68cd,0xf1d5ce286a07a2869422,0x6a17281e81574c690c97,0x546322e91735a6122f0e,0x60e576519934e910f55e,0x3422e8d021de8cac7ce4],#[0xb5268c8e39694dba4e9c,0x25e8db919e8dac4f6805,0x5615340d6a109a659096,0x595ad5e680846c551176,0x90212ce8dc784650a7a0,0x11306e919c0ce8d08286,0xcc466900e066a5329455,0x15ee11645e5d1ec4b691,0x7b65c40a95d0402869d1,0x8e801b94e910e2868d93,0x5d8ea646605431e81ef2,0x4d8d4be95c48761c4772,0xac316918d3168d8d696,0x5a7c6821277e9caa1ce9,0x9885955b5761d3471595,0xad594975d6484c5ee807,0x4e8cb18d615365565c71,0x68dfc3e68cc6576521f4,0x152f22e9128066a07b06,0x175a95d02b066a5f7656,0x135ae8df60969589226a,0xe73658598fe9c3128695,0x4468c91576606f47e91a,0xc660a84ee8d4044e982f,0x5032306dc0000be91086,0xb1927488b01d1c60112,0x32546f10733c88dc731a,0x1f67158965d1d5df51d9,0x787a60897cb9ddf7225b,0xa7fa8b79d3e606930a36,0xa846a14ec66280bc2800,0x3512853fdeee970b316e],#[0x96bb55a6d1675329548a,0xc8441200d4e6f197eb6d,0x13f9c8c659289245a250,0x4eb6db4586b556a85329,0xe8f3a994aa451a8942a0,0x12876270f85c1c00afd3,0x57a992c8e431f8dc6029,0x14823f1cedf6bb3d8ebf,0x1000b0d66a349994aa39,0xc8c44b218d85c200c040,0x9b2d7eb757a9d3e97429,0x29145606fb79badc6db6,0x200c0401000b2d3e833,0x8d4622d14890401c0c05,0x36994c25d2c53691449c,0x9f4da4f1f8bc3e0eea71,0x49208e462270c0401000,0x5aa54ea551a853a964a2,0x5600f8783a1c0d15ead5,0xc0401000acd468b3190c,0x22d14894421d0c050200,0xb8562913894401c8d46,0xa0cfe7b3b9ccde6b3258,0xd058240e04010008b43,0x4aa34f2712e15098441e,0xe56eb358abd5aab54a9d,0x20009bcbe430c823d5da,0x98bc56271187c3110060,0xf2d9489c4a230fc76371,0x289419faf576b79acc65,0x62b1186c1000a04da5d2,0x512813c98cb6532590c6],#[0x3599cc65f2cd56a34da4,0xaa4ee571885409f4ea6f,0x5926110782f1387c2e00,0x6eaf4fa5d1e80389a4c2,0x31fcf677385b2d164afd,0xf05812009f4c6531c8a4,0x33598ca8461f0d85c260,0xec257299369345a0cf67,0x6732e8f45a02f375b7da,0x1288239188a42000a4d0,0x5024110803c1c0d05a29,0xf777b9db0d063ae160a8,0x1c00a0ce63f1787c1dfe,0xece6672f93c882d12858,0x1b6d8ab2552893492419,0x69f4ca451686401e6eb7,0xc36168401000b0d5a9d4,0x53291419c0c259289247,0xbadc6db68b2572b154a8,0xa4d06733194c66230179,0x50200e050200c0401000,0xa4ca612e964a249a0cb0,0x963b1586c15faf074369,0x285c1000b0d668d3596c,0xd4aa24de672e130762d1,0x6e36ab358abd5aab54a9,0x277339347a2d0c823cdd,0xec58200c0401000ac54,0x4ba3d0e7f399a8b85426,0xdf6bb3d8ebf5babd4e9f,0x10009ecba3d1687401e6,0x9cbe57249046a270c040],#[0x9aad469b49a28fe77379,0xf803e1e0e87036194bb5,0x43211068240093c7e2f0,0xd1a7f3b9bcc052251087,0x3d1ccd164b0566ab51a6,0xa7d1e7f3797c9e27047e,0x5d29128843a190781000,0x8cbe5b2993c893d9ccd6,0xaa29027d3b9ccde6b339,0xe0501800b155297439dc,0x83d1c8ce52220f058240,0x2e16cb217eb757a9d2c8,0x261289044613017cbc5d,0x8dc5e270f8501000a74e,0x4a231087c3397ca8471f,0xe96db4d88bc5a2b1489c,0x2800a3cfe6f2084401e2,0x80b05024100703014070,0xf2d95ca64c241047a391,0x8c429f6f3743719cc65,0xe270f85c1e00a9cda5d2,0xd1e843b9bcc04f238fc5,0xbb5c2d462af56aad4fa5,0xac522733193c7e2f067e,0x75331248232108401000,0x98c45e2d158a44e25108,0xc653218cc4602f072b75,0x68701c00bb59abd4da14,0xe431f8ec6e301447a351,0x2d968b2582b355a792c8,0xa6d2e9346a130178ba5c,0x11066240e0401000a34f],#[0x52a752a8d3f9dcd45b26,0xfa793a9c4da65b0d76b3,0x10009c4c2511f8bc3e04,0x8cb64f238fc642a0c040,0xeac9549948a250273359,0x38b43a0cf875b8db6d35,0x430140802200a0ce6632,0xd2c843e1d0d8642e1207,0xc01f0eb71b6da6c35b29,0xb056297439b4ba4d1e84,0x5f2791c72311185c1000,0x6aad4ea551a853b9bcce,0x2e06fb79badb2d164af5,0x60901e009fcde5f2789c,0xc0981f04652c12482351,0x3c3789b118128101392f,0x387711e0ec102370e81,0x8060b60481d878080500,0xa080c81a78ab1060b01f,0x3a0a85d0f807c2bc0047,0x4f02e17413c1ec7d0871,0x404e0401af80b8a2248,0x3cb2aa564ae14b0c027,0x250cc0581e8ee0121834,0x2c8df87024e2dc220d23,0xc3b4743181d08d8081ad,0x806a8026c42f07b82505,0x9a1da24474cae13f1664,0x846a20e80706038a4c8,0x905a182004811365d843,0x782815132b1f0054bd85,0x61c260e8b683acbc0941],#[0xc1054009208520115101,0xf09d0c8c6c5c8e53260a,0x414c1082ea8e075a2501,0x1e9c20be4b83e4b8270,0x10601a687ee848e5a200,0xf08205bc169a147cf,0x180807b02,0x60556840000000001484,0x41000000d6c34c0f5a19,0xf68501000027ae083009,0x36100b2100000d58a683,0x1606880e85010d84,0x6370402ac20000000000,0xe041d208000003ec0f58,0x123835b0db02014,0x4e84021742,0x6005b0804ae0805bba08,0x99c10000004e82c,0x4491d1002d0403181000,0xf4849e58a870,0x590800,0x17b038e04ae876823d21,0x1c6c5,0xec4d1000000002020000,0x6e080000060356340400,0x5bc1c180005,0x4078d080000000001b81,0xdc167dde830000000000,0xa648200000000000000b,0xd4197c41000000002381,0xc1c100b21374823ba1,0x1010000000000],#[0xc64822d84000000,0x6820100b210,0xc8400035040000000,0xd750c0000000000000,0x6c8a18,0xe08011c080000062e080,0xa7429742014c0c3d,0x558634c4,0x6ac40000015b08000,0x9080400020d08064e080,0x6200070280804a089d09,0x66e0800000279,0x2020000008f6410,0x34706c8400000002908,0xf9031eae0e30828d8400,0x45840000026e251301c,0x11c0c9a1000000da0800,0x40400008e84000,0xcb0800006c20001b41,0xeb0806df82907161,0x1068718100000000,0x28748200a42000000000,0xb774146c2016420184da,0x1b5d08000003016ba100,0x6c2000001000000c33d4,0x1dd080000000001,0x24d0800059c08,0x581000066efa0c000000,0xdd0d2123cd4401168403,0x1dc08000190803,0xb080000023ed04995880,0xc862e84c8402d418],#[0x75e0e90600000148400,0xc61048e0400000290800,0x403a7040000000002922,0x704024e8758100000040,0x3b,0x1a5421803c704022e840,0x3a1e703fb820b7d,0x458402361000000,0x1616201e0800000000,0xed0a98100e604dc08000,0xb2166efa0c0290cdd0e,0xb61000000000000000,0x6820000808002f0400,0x8000000055d0806dc288,0x30c0800004f07ad0d90,0x2504,0x1ac0ed06992080000000,0x356207028742000,0x11b080190cb038e040,0x1a420000000,0x40000000000b61370200,0x80006fc8400000001568,0xa3435b08000000059d0,0x3610000000d86d81000,0xa70200010c0f1ba88000,0x30100000000008db62,0x42000000018c90514ad1,0x2012f88286040002361a,0xa8200000000000000c74,0x234c5ef8410f88401,0x200000001a8201cc0804,0x80301924d14b0200b74],#[0xc4010000000de0db03ac,0x6840000000000000234,0x99080004d8944000001,0x80180ed0400000000029,0x13360,0x6b8100c604024a1000,0xe08000000b1b3189e151,0x3504024a,0x2d840036100001e9080,0x1484c85b61000000000,0x54a300e60402181c702,0x93a100000000bb420196,0xa4396100770233c10000,0x6830e040000003610000,0x100001de08066e84c85,0x8782000000f742ce0401,0xc0c989a28c02cd092f04,0x107430e04d,0x2e84c782c0400b782000,0x1cf05809af0400000003,0x3de0f6c25b08061d080,0x14c0b381efc62000,0xad84016820000000,0x8283c1004ba100000000,0x8400001d904000000012,0xb424e040117832e0402c,0x1ac08000005b0200b41a,0x10000000000ab4200000,0x2504000002000196,0x6420001161002f5880,0x49e08000007b020000,0x6072c20000006f641521],#[0xe080000046c2b410000e,0x3241730280800013814d,0x5478352b100000000007,0x2d04000002ae86682ce0,0x268200000035d430080,0x9604c86cd08000000d04,0xd84000002ee8403b6100,0xd410000cba1000000a,0xd20800000000007a4200,0x35c1050e04000000021,0x6d068d080190804]]
def g223H6 := limbs80 #[#[0xa00824188121512161,0x82600011619020059152,0x63c89b002210110912a9,0xd55146e4802cc8184867,0x90001342221189020002,0x680000205565001a,0x2084001809004040180,0xbbc59cb8100000000000,0xa2c0b2a6b5bcaa]]
set_option maxRecDepth 32000 in
def g223D7 := limbs80 #[#[0x541104c950441754c910,0x441655411058d5044153,0xd8950441865411060950,0x5451058d514437354110,0x4438354510dcd5144362,0x619534416354d10e1951,0x59510e01634417558d10,0x443865d510e0d7544287,0x60f6244175d891054f62,0xdcd10dcf6244185d8910,0x48186dcd106177344165,0x615434815450d2054d43,0x50d20a1d434828550d20,0x4815354520dd54348373,0x605534815454d20dcd51,0x54d20a1d534818454d20,0x4838054d20dd55348374,0xdd554482875512060d54,0xd4d2060f514838155120,0x48154dcd2060f5448184,0x5d5424c185dd12061773,0x54130545504c14254130,0x4c1545413054d504c152,0x591504c1635413058550,0x541305d1504c16554130,0x4c18454130609504c181,0x995504c2615413061950,0x54530e0d504c36254130,0x4c36254530619514c161,0x5d1524c15454930e1951,0x55130595544c16455130,0x4c182551305d9544c174],#[0x995544c1875513061954,0x58130e19544c38155130,0x4c16358130551604c151,0x5d5604c1745813059560,0x58530d51604c35158130,0x4c16458530551614c085,0x5d5614c1745853059561,0x58530a15614c18558530,0x4c17459130595644c354,0x5d5654c3855913061d64,0x5953061d654c18059530,0x4c38759530e11654c381,0x615744c1825d13059574,0x5d130995744c1865d130,0x4c3865d130e15744c285,0x611754c1825d53060575,0x5d530e01754c1865d530,0x4c17598530e19754c384,0x5db514c161d453061265,0xd453061b514c180d4530,0x4c176d5130597544c362,0x553624c186d513060354,0xd89305d7624c174d8930,0x4c185d8930613624c180,0x5d5435016550d40d5362,0x50d40995435017650d40,0x5037650d40dd54350275,0x54d50501525414050d50,0x54140585505015454140,0x50165541405915050163,0x6095050176541405c950,0x54140995505018654140],#[0x5037354140d895050353,0x50d525038454140dd950,0x549405cd525015354940,0x5037554940dcd5250175,0x58d535038754940e0d52,0x54d40595535016454d40,0x5018254d405d95350175,0x995535018754d4061953,0x54d40dd5535028754d40,0x5038654d40e015350376,0x5d9545016555140e1d53,0x5514060d545018255140,0x5038155140dd95450186,0x50d605038655140e0d54,0x58140551605015358140,0x50175581405956050163,0xa1560502755814061560,0x58140dcd605035358140,0x501535854050d6150375,0x59561501645854055161,0x585405d5615017358540,0x5015458d40dd56150373,0x61d635017558d4059563,0x59140e01635037558d40,0x50183591405d56450165,0xa1564502755914061564,0x59140e0d645037559140,0x501755954021d6550385,0x6116550180595405d965,0x595409d5655018759540,0x5038359540dd56550287,0x54d72501435c940e1d65],#[0x5c9405cd72501545c940,0x503535c9409d57250175,0x5d975502755cd405d573,0x5d54060d75501825d540,0x503835d540e057550186,0x21576503865d540e1175,0x5d94061576501835d940,0x503855d940e0d7650285,0x61e6550183995405d665,0x9d54060275501769d540,0x50164d4d4061e7550184,0x6035350176d4d4059753,0xd4d4061b5350184d4d40,0x50143d8940ddb5350187,0x5cf6250154d894054f62,0xd89406036250175d8940,0x50185d89406136250183,0xd4f6250275d894061f62,0xdcd40dd76250373d8940,0x50165dcd405937350154,0x9977350186dcd4061773,0x509506177650186dd540,0x54362545505d95154153,0x595535415454d50dcd52,0x54d505d9535417454d50,0x54165551505915454380,0xdd15454186551505d954,0x58150545605438155150,0x54163581505516054153,0x5cd60541715815059560,0x58150605605417458150,0x5437158150d4d6054184],#[0xe0d605437458150dcd60,0x5855054d615438458150,0x54173585505956154164,0xdcd6154353585505d161,0x58550e0d615437458550,0x5417358d505956354387,0xa1d635418758d505d963,0x59150595645437458d50,0x54187591506016454174,0xe15645438359150a1d64,0x59550605655438759150,0x54376595506116554183,0x54d715438359550e0165,0x5c5505c971541655c550,0x541535c950d897154176,0x5d172541735c95055172,0x5c950e0d72543735c950,0x541655d1505d17354384,0xe0574542655d1505d974,0x5d95060576540835d950,0x543805d9506117654183,0xe1176543835d950e0576,0xd4d50593535415398550,0x54153d895061b5354176,0x5d36254173d895055362,0xd895060f6254180d8950,0x54187d89506176254184,0xdd36254373d8950d4f62,0xdc5505db7154163dc550,0x54154dcd50d8b7154186,0x5d37354165dcd5059373,0xdcd5060b7354181dcd50],#[0x54176dd15061b7354184,0x6137654186dd15060f74,0xd8951e01765478058551,0x54561dc1516176254580,0xd8b7054586dc15160f70,0xdd15260f7054980dd951,0x55180591545956455180,0xe11655518059554e0164,0x5c15459570551645c154,0x551825c1545d97055172,0xe0176551805d954dc570,0xdc154e1176553815d954,0x55186dc15460f7055164,0x5db7155165dc55459371,0xdd95461b7155180dc554,0x583735456061d5158180,0x595545838754560e0d51,0x55160601545817455160,0x5837555160a1d5458187,0xe1d545838355160e0554,0x59560d51635815458d60,0x581845956060d6558181,0x595715838359560e0165,0x5d16059574581755c560,0x583805d5609d57458175,0x61275581809d560e0d75,0xd456058f51581879d560,0x58187d456061b5158180,0x6035458165d5160dcf51,0xd516061b5458183d5160,0x58165dcd605537358187,0xd537358185dcd6061373],#[0x5516159154585801d561,0x58580591616195458565,0x21d65584755956161564,0x59561611655858059561,0x587805d561e116558780,0x6035458565d516160275,0xdc1615977058586d5161,0x59185dc16160f7058575,0x59570593845956460165,0x5d5649d570591755c164,0x591879d564e117559381,0x6037559185dc16460f70,0x5c1655c570594835c165,0x597835c165dc57059574,0x6077059574dc1655c770,0xdc1656137059583dc165,0x59774dc165dcf7059771,0xe0d7099580dd16560371,0x587505cd61d416558750,0xd417358f5059563d4176,0x61d63d417658f505d163,0x5935059564d438058f50,0xd4187593505d964d4174,0x61165d418359750e0d64,0x5cf50d8971d41635c750,0xd41825cf5059573d4164,0xe1973d43845cf5061973,0x5db50e0574d41655d350,0xd43845db50e0d76d4183,0x60f62d4174d8b505cf62,0xd8b5061762d4184d8b50,0xd45615c3515d961d4587],#[0xe0d70d47625c35161970,0xd8b51e0176d45805db51,0xd51805975461f62d4580,0xe0d70d51865c35459570,0x55362e0176d51805db54,0xd8980553625d554d8974,0xe0554d8b805536261d54,0x5c36260570d89545c362,0xd8a855c36261570d8984,0xe1170d8b835c362d5170,0x5d36260174d8b855c362,0xd8b805d362a1574d8985,0x60575d89805d762e1574,0x5d762e0175d89845d762,0xd8975d5362e1175d8b81,0x798ef1cd87d536260354,0x9bf36e5fc7f8fd1f63dc,0x73ea7ccf79e73be76ceb,0xceb7d6babf4fe7f4fd9f,0xc6d7eafb5eebd579aef5,0xdb5b5f6b6cfd9eb3b672,0xbbb575eeb5cfb7d6f6db,0xdd7b6f5deabcf77aeedd,0x8fefe5fabf37daf9df2b,0x73be76ce79bf35e5fcb7,0xf69dd1f9fb3ee7bcf59e,0xbed7badf5b6afd5ba7f4,0xdb7b6b6bed6da7b3f65e,0xdbcf776eddd7bab6f6dd,0x7b8ef17e1fbf37d6f9de,0x9f73de6fcdb97f2de3fc,0x75deb7d67abf56e9fd2f],#[0x3edddb7b5f69ecfd8faf,0x1de37be77aef3ddbbaf7,0xe9bcf79df39e5fcb78ff,0x7e37bcf6ded7d77adf59,0x1fdcfb5f5bea7d2f9df3,0x6fe9fcbf67eafd3f9bf,0x7206420600e4d9c1f652,0x8e4e510b260dd0265e6,0x8e4e6b6a5d4de685d8a4,0x6619e45e419c9754c461,0xcd29106604889594a103,0x8819654c3a036625645d,0x490364e7903661a34560,0x4685d4d33f6124e0465a,0x6add4de41e4d9c1ae443,0x8e4c004b595f745dd02c,0x642061ae4502446090b1,0x943d03661280a6612621,0x13036e4c4310e4d98895,0x4f036624e56e183b0366,0x675d4df03e552d10e42,0x1e4e2e685d84044a5c3,0x754c3d3f5d52b1ae464e,0x6426c24e52053d61d949,0x955f3f61d244de52031b,0x25b036427b03e5035675,0x4d785502210e419b03e4,0xd9654c43036566e22e4d,0x85594a3455d52984594d,0x3652709354c9d10e4033,0xdd52b446465b10660ab0,0x52731b6426d24e54de3f],#[0x8dd216595e655963a166,0x2d875943e08e4d9b2465,0x1e4df49654c3803e4d,0x55e0d7c68595563f6113,0xe403116e527710e5198,0x5d83b566183b03662731,0x1c301b65c482d6544872,0x55803e5c9432e50a744a,0x5666596342b64c474b59,0x803e427e05e40711b642,0x365e664a5960f1ae466,0xa65e673d615284465e67,0xe412a32650ab26e4e081,0x95ca44dd4303d6149110,0x5cd6c5d05c226594a655,0x1789e415b3f61d268459,0xc4124d9c4b5955710e40,0x166502f5c551294220d8,0xf61090086619d58d4d98,0x590e2685d45d036626d3,0x566f3f5d26668595556a,0x2674b596382265953036,0x7036526e45a1c2c7a5d,0x85c50d29046590b2d654,0x58e419b16e527245dd19,0x3e4c36655d8c616e5108,0xe466503e519c56e0d530,0x5263036527921a620644,0xe7601e4cf86c5d45c16e,0x928d590a14160e4d18e4,0x20365674445d667455d0,0x3fe5265536152616e426],#[0x3e4e521be417e1ae457f,0x5d4922d654ab036624d0,0x159f0ae4d2b0fe443245,0x59e6a5d06467596313d6,0x670fe441f03642753d61,0x503e4d9c0366131745d6,0x3d5d666036602310640b,0xe5263036619f10e401f,0xe552b84e520285594d17,0x164e0de4d9c67595600a,0xd2c45dd42c1be426b3d6,0x483d5d67d1be407e03e5,0xa3664c481864c2b9654c,0x186542203e4dba8758d4,0xb65cab3d61d9d4f6183e,0xdd529675d4651ae45281,0x6091725d03b0364e7445,0x2521ae46783d6164d036,0xea036626c49595bd03e5,0xf01e4dfa03e51b9655d4,0x4461e6745dcd988c58cc,0x3660901ae467210e5529,0xe58565854d9803e42650,0x44566e65c6463e419b06,0xcca06e4db812e606347e,0x46136416e9158c5a40e5,0xb35e4cd17ddd8a00665a,0x955909f51e42033a660a,0x764ccb0666137306589f,0x65c6a7bdd41e86e51691,0x521946612767bdd5241d,0x24d1de45a41164cb6176],#[0x4d7c5d8cc06e4e2d4661,0xb1e6422a7b5d2648b651,0x77e425d1964cc2985503,0x6641bb06e4dcc95594ae,0x594db1ee505f9158d4a8,0x5a2446a1671466624d8e,0x88146a604f8bdd97550e,0x5246614906be58eb1e65,0xf1de45af719945240618,0x915505c17e4ceb07659d,0x7e41d146a1c281465a19,0xe18973864c616354d294,0x44978a5955947dd5dd40,0x4c77be51281ce5d257ce,0x893e596468be4d4d7125,0xd38e4cd51ce427819e4d,0x3ce19071e64106835d03,0x3dcd984761ddd59e5251,0xe414635e50d529e59506,0x5cef13651422e655a313,0x4e246e427b2ae51be176,0x65466426546a14761d65,0xd3ee54f89954cab6ee5c,0x4665d9a64e4e0051595d,0x65526e06e55360665cc4,0x6108f8b595568b595524,0x1d1c1ee407f15e5e5c5d,0x9cb066590c1c65c4c406,0x9f4ce15e91264e0c4664,0x246e4e7912e45da4661d,0x82e403747e45aa1164d8,0xce509139e45283e6150f],#[0x6159738e4ca8865d4ea1,0x11086fdd98c7ce51cf59,0x2688ae1d5b6e5d4657be,0xa81ce4d281ce4c1646a6,0x13a6413c06e4db635e50,0x15e551846614761ee584,0xce56697c550e215e55da,0x6183e8be18a4435d2241,0x592206e4da2466067691,0x1c63ae419430e417206e,0xd39e550ab3ce197a17e5,0xb8be454d35654cf6fe5c,0x5961d9d356589d7ce44e,0xc65d2e2fe453e1264c0d,0xe41e6296594a695d8511,0xd04362608587ddd14b52,0xcdc52e41f9715d499825,0x2f7ce50e163551981de5,0xd596152519e4cf81c65d,0x6e4dd21de46354c5963,0xbe455086594e46124ca8,0x649aa985903b77594413,0x59190664d1430640bf46,0x1e483e40846b5946c13e,0xb71c6513d2fe457329e4,0x4596159e46e4d9c88594,0x3e61534066508328e45e,0x665a5f1c65d7b3ee15eb,0x590dc122606313660d70,0x121a07e4df91ce4d028e,0xdac80e0d8c5fe18a05ee,0xa07b5d04e8a6515b19e4],#[0xf635509282e02767d5d8,0x19e4da68b5955112e45e,0xc650fc1e64cad466491b,0xe423e4665c933ae4c050,0x4dda38e4c4438e4c4230,0x9c033e51085964e5119e,0xab46dd52a286420b4ee1,0x54660db77be526382dcc,0x34e50681c65da39e550a,0xde4ce1176511246609a8,0xe42453ee15123ee61151,0x608c06661f51964cf31e,0x62919e4e5530e4171066,0xff48e406d63648c31de4,0x240611fb6b5d4ea14659,0x5f550e913e41f4715953,0x611a56de4d651e65155,0x618418b595501c65d044,0xe768b5943d525941148,0x58e48dd91f306514246e,0x444661d970ce50f84364,0xd306517547e190b3be44,0x1ee425e0664d0e40650f,0x9651e58b64d4d1ee4080,0xe4e153964c0a7d5d89d2,0xd88d286586a816090b27,0x49848e18ac17e5533485,0xa671e50f43ee1cb917e5,0x45f610c34665e5a30e54,0x13e41a213e40be5de11c,0x9e4d7a52e0de55be0d75,0x61df106e4e1e1964d681],#[0x40095fe50a82ae51713c,0xcf71d65c6235640993be,0x3262609871de447f4021,0x848dcdf27d5d03c71995,0x1364161596159486594b,0xce4cca47646599f50ca1,0x6413751e0e086f595550,0x51d399e41941ce54761e,0x3b926415a8ae4e300ce,0xed1c6526ca1e0c3d805d,0x98e0c9f6ee5cdf35e40,0x13e51ee47e180b47619d,0xc591c581e467828e5604,0x5d08f6be523b1de458b7,0x5d5a066522f8b6594a7b,0xe7b6485228642076ea,0x109854c3d4c6199138e4,0x3925943d515961351e42,0x7ee4e6b92640df3c5961,0xc6625646a5db21465174,0x595424665db211661971,0x454b636419a17e523c5b,0xd2595594a01ee5c403be,0xa2466149143e0dd44661,0x534650627e614228b594,0x9164c5d1c64db79954c0,0x6e0dc2466087d6158cc3,0xe4db4116609535e589d4,0x10ab7ce453206e51ab1d,0x1168ee106499648029ee,0x66636042c86e51d713e4,0x66607946612790ee4d],#[0xc64dbd466609086595c,0x6189735e54a306e60e6,0xe118e0c660ee1ee41094,0x4d1581649d035650d643,0xee176507a62e066415e,0xa73a64cab1d64ce33564,0x543e4df434658cc1de45,0x1c654b398e0c0213640c,0x95d8f911e559a46e0679,0x655708a2615b9158c606,0x54ab8b5954b13660d609,0x3b2ce4e5c9ae41593a6,0x52485d88873e4d929861,0xc955509f06e4daf46e4e,0x39e45955f618a017e546,0x7e4e0806e51fe1c66268,0xe1cb777594ac3ae40b02,0xd8b9596519b6f25cd343,0xc9d1ee407d3be443c695,0x67465d24f8b5954a9ce0,0xb06e4dfa336502062642,0x8b5940339e457f066524,0x6e0e561e6407a1765c50,0x6541147e450e6fdd4d24,0x50b31d6590b28e4e0813,0xcd0466552d59e459b7b5,0x27116602013641de9158,0xf6d5d96450e59ed3ae40,0x31e4c9752e41f3336512,0xd60cc851616043a6412e,0x5d2381c65c954761c585,0x459c83e40675d6612648],#[0x9d3635502c0666168466,0xdc3a65cab436118e07e5,0x19fe10a175642638a594,0x6e5955f40e50f8466167,0x3e51c45260de517e5897,0x6417b46e425b47e45b83,0x6134436518e0665dd53a,0x4900ee4cf817e5852066,0x5f4ce19c16f5d45d1ce5,0x48618ac46606798a595,0x35e549d1c6602306e601,0x66159f7ddd4cf1166125,0x5954f122615d29658d74,0x522706e593546646798b,0xc91e641eb9954c9e17e,0x38596159f476065835e4,0x82dcc07926406506e4d,0x77e419246e459c405d92,0x26484112e4485405d91a,0xe4e1f06e59aa46e427e8,0x45fb1c65530596152806,0x8d51ee424079e4c981de,0x77336510406e611e29e5,0x869dd94469254f51de44,0x1ce4cb21c6542a81e466,0x66601a63d509206e4cf8,0x5d1986b5d8960c660ef0,0x5c79c54c9d7d550ac63,0x5523c619343ce19c347e,0x9c1964cc13ce58f830e5,0x431e4c985b994c36024d,0x7125cc635640ef06e613],#[0x6661ff61e0dec6120d8c,0xe4dc6475d9877d590ac0,0x621148e4237136606119,0x52d12e4e001e65c6151e,0x1c475d45863d4d2946e5,0x146e0d79116612f06e54,0x7ea1c1d176590d46e1cb,0xde41cf17e5cc69e50ca5,0x6412c11e41b3a154c3d1,0x459b06651675d6112763,0x71406153361e4ca8596,0x8f516420b1765c9606e5,0x946e4d2da054c384661c,0x1d6450f8659543176507,0xae4190925903d4661e64,0xe4d261ee407817e52219,0x52251c6466c30e4ca433,0x2151ee545e61e0d8c17e,0x4246614231c6427325e5,0x113e40f813e41ab9854c,0x57e0d771365175296586,0x9e58f43764c204760db4,0x660d85b5948d176549c6,0xd9509954ca509a618613,0x1613e61c5113e60d06fd,0xeb1366060996489f3b64,0x548610816de4e3614659,0x8e5d4de8a64d5b82dcc0,0x664cfd1c6541911e5d9a,0x5940e11e519b30e589f0,0x95bd1c64e6d5d64d2b88,0xc07136515782dd02c4e5],#[0x6347e44f82e6553c3a64,0xc8e654de6b5953388e4d,0x8b5943f52e18a460e4d9,0x76190b06e54f81c64d31,0x6590b09e556c46e12764,0x112f6264858885956412,0x608715d49613640735d6,0x885f590c31c6519e8add,0xc95640c68add60a19a61,0x985cc9f48e40f894594c,0x69d4ea63dd19834e44ed,0xe41fa7de50d45b619428,0x54f1466427b1ce427713,0x42c6e594663e995aa0c6,0xea0c650c530e4c046364,0x7a0e0c3806e421c6b25c,0x46d526e4625c189e550a,0xce10e21ce5cff1ce4d7f,0xd4ca71de4dd0865d8c67,0x45aa17e51451ce4e7699,0x1d10664db16b5d8c61de,0xfb066551346614195ee5,0x11ee407115e4cf406661,0x17641c96354d9834e50e,0x765ddd066518e38e4c06,0xe44f43064d753e595cb4,0x5802475d94815654fa76,0x2b1de59d03c595fd30e,0x3c06e5d211de41ce1c65,0x98a214654c5956140e52,0x1d659c51c65029985944,0x66619e2f6556219e4cba],#[0x5d4f16fe58d43a640954,0x60916ddd98e1ee4ca640,0x80850e19ed4661d95466,0xff06e5c551c64c2e1e65,0xa1ce4d08a054c483ae40,0x63608c3462552d35e40c,0xd5512a4e6191c19e4e45,0xe1619695d46511e4e505,0x5c4b1c65c4e1ce524d3e,0xf43e61c571e6422b06e,0x291ee41103a641a32ae5,0xd805d0498ae515b635d5,0x1ce42651ee424a596119,0xb5d52406e52286e5d464,0x64cf08ae420e0ee4d6c7,0x184a7b6489748e41fa17,0xdae2ae54c76e5915f51e,0x949de45268e6420106e4,0xd5b60d751e641125961d,0x665a579e50ca70c6590,0x9e519b8f640ea13640fc,0x590637ee4e764ce16175,0x1d5b28e54644c595de8e,0x11e5160e044324e2e8a2,0x5955949d06e4e2e0666,0x852e19ec46a5c188ee52,0x1ce507e3ae4ca7635cd9,0x9e4c1a33e4d0029e4d4d,0x651378ae42023a650481,0x4cf895650a4986183b17,0x46b5258df27b6493243e,0x3b77e54a65459520695d],#[0xe485d91947e0dc5805d8,0x34e449769595a5805d03,0xf594a39954ca786595bc,0x64e6614e58f499d4cab8,0x5c6e5d9d52b1de451111,0x4ea4ce198446e117e066,0xa3164c9a06e5c896bdd,0x8be415b15654c062e0c,0x6364094475d90b77e5c4,0x1e4c4547e4629a0e0c48,0x5945e46612445d5d52b6,0x11c2525955817659326f,0xe322a650f943dd2247be,0x8e3c61c6b9e6489d6e64,0x219e4de85fe189d80e41,0x61e41ed1e641ff11e55b,0x665279066581328e5208,0x61d9652618a27ba5c1e4,0x95c54665d2c5be417646,0xd9e4320d894760dd0765,0x285fe14d106e4df44661,0xf5de110835e50d433e51,0x35e4ca32fe45407fe0d5,0x1e509461e022006e4e29,0xe46729b5501d1de46181,0x418a7d5d03f1ee5cd581,0xe0462645b25b618aa1ee,0x8e466485677dd8aa28e4,0xf47641d11ce527661e41,0x82e409169e54f55be189,0x6a1cbc30e41924625d2c,0x64c307725ca406661234],#[0x52477ba1c1e43e118862,0xde543e0d894665e50066,0x2c116619e9024e082964,0xe48e40563be40dc1e642,0x4761c8613e40bd39e444,0x3658c311661963be4159,0x615301da5d6180dcd4a1,0xd417466166a1ee5ca446,0xc4d3ae402d4665e7d465,0x9d5a5958798dcd4a0665,0xe17e4cc746a5d9a95994,0x75e427c11e4d9b0665d6,0xe25cdf14658fb35650d8,0x640fd51e12084664d9c6,0x955d51e120a11e549313,0x248ae14651c64da38a5,0xa19e4da51c65cff3ae4,0xa40591cb95590aa1ee41,0x4e594f111e4e5a465d52,0x16608a35650d77c5d058,0x60d258ae4d5b63649191,0x561361e0d5588e4e3360,0xd4113e41d3236517412e,0x281ee4255176516d19e4,0x813e591f3c6191e46615,0x9c58c9d2ce4d4115e54f,0x658aa0c6609a8a5955c,0x1d60806661a58be41d73,0x1d278a1d60a15e55078a,0x41581609c529e41e2466,0xfa466119e46a1c2d5961,0x61c6602a06e60bb0ee4d],#[0x77e414106a60f35f610f,0x36102c636552915e55c6,0xa5c1d06e523743e0d8d6,0x12093c619a009655627e,0xd1129658d67be12788ee,0xf71e5248466159e19e4,0x829658d01264db013e40,0x3ae40bc8f650d311e4c1,0x324cf892e02085f650c3,0xe5c45915ccd207e59da4,0x943e1d6580b71e54c748,0x25346e06767ce1066915,0xcd11660153e615376ee4,0x446e0e7906660c254594,0x1de5c6835658a019e4d3,0x1dcc0a11e4db24660e71,0xd4ca50c6421b11e4e7d8,0x94d013e4df75d61d2699,0x8a4466490c1c64d9f8b5,0x531c65d3c1e64d568b5d,0x86060c15635cd2906660,0x1c64e7946a5d2c466612,0x56421648640744661d2f,0x612687ce110b92e415b2,0x600746e142313641d67b,0xdca25e58eb6f594d93a6,0x6ea154c4639e457d17e4,0x548e40714665c944c595,0x15e5e3f69596423ae412,0x259557a0e401d0c658cd,0xe52654821cf663e419c5,0x14954661c8a35e40ec7b],#[0xc603e595aa40e146c596,0x2b5f5911f1e65cd61e65,0x325658ef1d64d605da55,0x11e4d2c40dd4f18b5d4d,0x660da31e654d95161208,0xe626877994ac5d615264,0x52521d65c6940dd8cd1c,0x5836e642531d65c63466,0x6a15e558b1964ce81de4,0xd75e426380e4c5f86595,0x3ae401f46dd1990665e3,0xc6427a985943b43e518e,0x65c9a06e4d1769595fb1,0x189d12e4e0d79e4c9717,0x4e614e4cf57c5d0635f6,0x342e6557b1e65c5b1de4,0x1ee4077826426846614,0x6e65cdf336512e6464e0,0x6e561348a1cc31964d0f,0x61c9539e442839e448f0,0x12795121e0a52e18a846,0x5b4660e7659e4e5146e,0xe08b6454d4760d0b7d5d,0xe06e55fd2ce4da628e45,0x9ee10a56f5d8a40c64cc,0xa5915981e443411e5d2c,0xe467930e413f7be51028,0xd9871765cee1de462646,0xd2c6fdd9751ee418947d,0x5a11e552d1e64cda46e5,0x952594e91de54668e5d1,0x83e44d43b6406246e527],#[0xce466b6ee4e3213e40e7,0xe4e581e65cd847e05c61,0x4d9b13e41ae775d8aa19,0x9681de4e1214e596c59e,0x6148640fd3ae40281465,0x2864e0a5b6189f0665d,0x8b9d4d3956509f6f5d84,0xcdd8cc6160c7028e4209,0x655db47e0e54475d6137,0x4d2d8be416319e4d1e15,0xe59136416f73e4da611e,0x9f29e41e364641dd0664,0x84661d28116608f775d8,0x126598740dd92086595d,0x66619f34e44eb5be18aa,0x618ae066587b62e441f4,0x427c13e4df28b595495f,0xcaf7b5513046e0d08756,0x1b7b64262695d4e55de1,0xf5d6512c0ee4e2e06e58,0x94e51ce7ddd89d695955,0x3d88883a6408a82dcc9e,0xe4d791ce567146616696,0x453946a1c1f3a660481c,0x44169595687cdd4db47e,0x8525658ee11661957799,0xa5e618cc06658c519e4d,0x77e406f19e4e5e51e0e0,0x6a5c1f29e58d4356409a,0x5ccff466519c6e594e24,0x514da1e0c463c6188c7e,0x90b86594509854c398be],#[0x463e401f25e51e26260,0xf69dd9848f550d28be18,0x39e442659e117c3a6412,0xee110b0664c14356549d,0x5d66459611941ce4e715,0x407206e4d1b29658d875,0x42546662686fdd4d3136,0x221c65180516120a1c65,0xe48e5ca838e40b746649,0x7725c04865951c35658a,0xce4d925d6552b4ce1978,0xe40ca46660345d611972,0x1c5451618864ce15e75f,0xdf48f594d16ea5cdf466,0xd1516420329e4cd30ee4,0xc77dd89f8e64cde9fe44,0x8a595dd35e54cf11e4d9,0xde4dfc46e52523a64104,0x64d7519e4d6c17e51116,0xd4db47606597bdd19513,0x5429658604661d2e7c5,0x396f5d4d21e64d8c7b5d,0xb07e4df39864c4006e4d,0xce504b8b5954e1ee418,0x324df450e1a2473e4d41,0xe41d146e42659de441e4,0x16682ce4d4006e59b51d,0x4cf6fdd14c8a5946a46e,0x6a9858c029858c9f7d5d,0xc47dd948465d1813b640,0x116619f51e420b4661cb,0x260c303be419046a166a],#[0x60da01ce42636f5d4d36,0x5d913e41da19e4d0a43,0xc501c65c8f465d49364e,0xc6466427e0664e614061,0x11c64cb4116612771e5c,0x665c733b640698b5946,0x6e5c8e1c65c8a6f59556,0x60d9663645985d615240,0x15967e24e761c6427b60,0x20a3ce198506e546d596,0x933c6191847a1ddd2865,0xe0664d8f29e594e5be41,0x9a54ca115654128a6420,0x1d505c405d23d1e65cd7,0xe544f43e4dfa596148f9,0x1188825d03a1d65d611c,0x4ca0e0c0143e0d5f436,0x5f30658021565cf93a64,0x9485d91f99e413a1d651,0x639d5293c619f515e558,0x660d08636502c0665c59,0x6152f81e452817e51894,0x5ca45a5954807659d659,0xcea1ce4e6819e523477e,0x1d6de598e466425b6be5,0x113654e91c65421695d9,0x8a595603c5961d7b5510,0x9e4e603c6188719e4e2e,0x619325964d9b59615951,0x19c54c595f819e4da140,0xc43865849825d04847e,0x7263a552943e0e230c65],#[0x117e516c5d61d241ce42,0x6e4e144664d2d1c64e4,0xe5965f30659423864c60,0x595ff1e6407977594083,0x5448066547c516421069,0x5024664e526e65d5a3a6,0x2819e4d458e650df81e4,0x4695963530e417311661,0xc641bf17e5932695d8f,0x8dd4c3066607a86e5239,0x658587bdd4af0c64cf24,0x41df695d88b3be445b12,0x9357be527282dcca7136,0x5590e4e08825cca54664,0xc5b594c33c6181a8b595,0x3ae413a8e590e00665cf,0xf550c31e658ac17e510a,0xe566a06661a017651dc5,0xe088b595d93064ca91c,0x94748e41f412e4455516,0xdd5d6119511e4d9a1765,0x45ee44ca82e426b47a5d,0x3ae504346e5c944661d9,0x6e41bb4324dfa11661a3,0xe4cd40665c7212659488,0x51065b5951f06650741e,0x12506e4e3c8a59561176,0xf19e4d8b1e6518c5d61,0xc1c652795121e0812e4e,0x28e420551645f35e60cc,0x465de115e506f1365942,0x6525163651987ce11c81],#[0xd270664dc706e561d59,0xbc47e0d0b7edd41d606,0xc343e0e211de46225d61,0x9146596d9e50c9e485d4,0xee4dd37b5d4af30640f,0x6e601a0ee4dda13651ec,0xe44d4645848806e51f00,0x183b06e5cbd176589b3b,0x5477ea142217e5ced616,0x2e8be416938e4c457159,0xc7d550d91ce526b59615,0x43e4e3739e4597126580,0xe65c65466107e46611a9,0xe4e430665dde06e591b6,0x5c5d405d8cd0664e4c73,0x8588020d8c8a594636fe,0x3077254a61ee4111475d,0x7636491f9e50cab8a64e,0x8f594cf34e41cd066608,0xc64e569de45001765c99,0x654fe83dcca111e519c1,0x4dbe47e45af3e595ad33,0xc2f2a641bf1de50672ce,0x58b5945b3e61c8b1c64,0x94664e7906660e81de45,0x48e18418be41f6616184,0x6189b81e457f43e458e,0x5956b06e59cb47260e14,0x58828b59554915cd4c8b,0x85219e4d3b2ae55bc066,0xe128658631c64d0340e1,0x206e607546e519c29641],#[0x71594528b594d88a6420,0xc650fd30e55517b5d4fe,0xa552d0c6611c39e441f0,0xd4df4320d8d06660fb46,0x16328e50653c5da3d8a5,0x314765c5819e4dfb29e4,0x46fe4165116612e46615,0x1e65c3f9954c0712e4e1,0xc6626d43e4e2e406122c,0xe4dea7ce11c53e61d1d1,0x455023a0000436558e19,0xed10cb10a86087906460,0x91716f814eb12e910d50,0x16b1fec1ec11d341b221,0x7c02689253a23ff22b02,0xe0a2c972b602a2e28d12,0x4943356320530ee2fa52,0xb2e39ac383a36d335a63,0x18440463ed63daa3c643,0x83a46f445a2444042e04,0xe124ce24bad4a7449494,0x467532351e550ba4f894,0xaf059a6587a572755e55,0x174601f5eaf5d505c445,0x80b66ab655a63f062e36,0xef76da66c5a6b0769656,0x52a741972cd719870356,0xb2679ec78bf779776527,0x1a680457f107dd17c6a7,0x80b86928513840882d98,0xeb28d4c8bed8ac889408,0x4df93a2927291148fe38],#[0xb919a3b98d8978a95ff9,0x1dba0959f8c9e469cf59,0x550a800a5ada47aa308a,0x8657132458ec330a91e0,0x4008c0085df6761bc681,0x504b900390c52a8881a8,0x38090007e1e06d5955b5,0x2c448f5368be28885188,0x500b000749a7635694fd,0x5d4e51a400d62b4831b8,0x3a06000841ea7159c5dd,0x3c478ff384c12948b184,0x4b06c0078dc363175561,0x5e4f5163c4da2d48c1b4,0x4206c00819e272dac621,0x36480f6360b1288861a4,0x3c068007e1d36a980595,0x554ad03398c22ac8015c,0x4d0a400795c969d875d9,0x6150d1e404e732c9f1c0,0x37070007f5dd709a660d,0x434710738cc62988e180,0x4008c00765be64582585,0x454990639cbc2807c164,0x580e8007b5ce6a97d599,0x60511223e8c82bc971c0,0x53084007ede06dda0601,0x3b470fd364c3294831b8,0x45080007c1c669180549,0x424810337ccb27c811a4,0x3b070007c1d36a57e5a5,0x113cce4330b02287114c],#[0x18030005fd6252d3c491,0xb52709021076194440bc,0x250600046d093bce7348,0xde348c627c911c8480cc,0x1b02c00585534c4f83b0,0xb82ac8f1e86715c440e0,0x2605c004991938cd631c,0xbd2aca02547f1483e0d8,0x21058004e51e42cf236c,0xb829c9020c7418c4d0d0,0x2806400479033b8df32c,0xda2d09b23c77160470cc,0x270580051d2c485133e0,0xce300ad23c821bc59110,0x3306000475063bce4358,0xc52e4aa2708e1f85f13c,0x320780040cf43b0d9334,0xe334cc32a8921f069110,0x1d038005352a45d063c4,0xc527c902006d17c430b4,0x2b070004890e3e4e9384,0xc22c49a21c6d178450e4,0x26034004a51c441003a8,0xf136cc32c49c22c620fc,0x2e060005512c45d013e4,0xe9370d02d0851c05d118,0x2d0580063d6451d13400,0xd52dc9922870174480f0,0x29044004d12c4550d3f4,0xa62687a1945d154400c4,0x1802000430f638cce2c8,0xd12d09e2086e1483d0b8],#[0x21020004f521441043d0,0xb82b09421c73160410b8,0x3707c004a51a448fd34c,0xa725c8b1f46d1685210c,0x1c02000404f43a0db2e0,0xbb290891e4651583d0a0,0x2b074004590e3c8e3310,0xcb2f098240761644f0f0,0x26034005413945cfb378,0xdf340b9284781a060100,0x370bc005393a489043ac,0x153dcd4314a621c70114,0x220440058d4b4f9334ad,0xbe28c9521477198500e8,0x2705c00495193d4ed358,0xba2987918058114390c4,0x2004c00479063e4e8340,0xb025c841cc581343f0bc,0x2405400450ff3b4d62f4,0xd629092220781a4510ec,0x3d0300056d454850c3fc,0xd2308a72647619c5a138,0x3607c004b920424f2398,0xdb334b928c7e1a45b110,0x1f0380051d3647d063b8,0xca2d4a52547917c410e4,0x2404000531284510337c,0xc72e89f25c8c1b0500bc,0x3c0740051925458f1378,0xe3354b7274871cc63134,0x1c044005193a49911400,0xc72c09a22c7b1a04b0b0],#[0x1f04c00491073d8dd354,0xb6270901ec6c154490c8,0x3208c003dce9368d22f8,0xb72989e2247119856128,0x2c05000451023b0e230c,0xd42e0a8244831a0530ec,0x1c040004991b428f839c,0xc02e0ac25c7b15c470c0,0x2e07400485093e8ec350,0xab240881c46918455104,0x2f05c004590e3bcd8304,0xeb31cb4280841e46914c,0x2e0540056d3f4c1123ec,0xae26c871dc621684c0f4,0x28044004710f40ce12f8,0xab254881e47116c470c0,0x2103c00474fe3a8d4300,0xc52dcab28c9b1c04c0d4,0x25030004b91e444f736c,0xd8328bc2b07f1b0530f4,0x35054004a51c438ef38c,0xf7348c32a48d17856120,0x27034005bd514c12543c,0xbd2a8861d869170440bc,0x2f05800499073ece3334,0xf4374c42b4961d85f11c,0x250600051d3f499153f4,0xc12a8911e469164430d0,0x30070004750d3d0e6358,0xe9324b22747d1a45311c,0x1d0300050931485113f0,0xb9280881f0621583f0b0],#[0x2405c005213c47cef360,0x91224791b8621183b0cc,0x2903c00410ec2fcac284,0xda2cca82687a1a452118,0x1d0440053128471103c8,0xd8308a5204721703f0c8,0x2d054005753e4690b3b8,0xce2e0a12407b1cc48100,0x460b40050914410f6378,0xf2368bf2b8a125080184,0x1d05400561314750f3f8,0xa425c7f1b8621343e0cc,0x27044003e0e7364d12f4,0xee358c32ac881b8550f8,0x2d07400569424b11b428,0xd12cca62406d1484a108,0x35060004d91f40cf6398,0xcc2d8a22347619c5c120,0x2405000521294510a3a8,0xcf2f0a02287e17c470dc,0x36078005352144cfa3a8,0x23420e332cb323878150,0x320640060d7858552505,0xdc310b828c881a85611c,0x10020004e51b414ef390,0xc82e4861e85d1282a078,0x3709c004f12a41cf6380,0xcc300a924c7c1bc64150,0x2b05c0050518424ff3ac,0xd331ca82688c1cc5e10c,0x2a044004a11440cf0388,0xde338b526c841a05d108],#[0x1b030005052a4790b3f8,0xbd2a89d1f4711a440098,0x1b038004a10e3fcf3384,0xc32d09c21c7316c3c0b0,0x1f020004c112428f1384,0xb225c801e05c110370bc,0x2906c003eceb37cd731c,0xc52b8962387a16c500ec,0x2a04c00465023a4e1334,0xc02e0a023c771804b0e8,0x1f038004b91240cf7360,0xbf2d0a722c761a44c0bc,0x2d04c00459023b8de350,0xc72b8a323c6a1544d0e4,0x2905000438f838cdb34c,0xbb2ac9b23c7117c480f4,0x2d058004911541cf7344,0xca2c8992207417c520f4,0x23030004d5263eced364,0xc92cc9e23876144490e8,0x2f08000545454d9223a4,0xd12e4a4270861ac4e0dc,0x31070004b91a3f0f0388,0xcd2b8a1234801cc57120,0x1a0200047d083f0f0384,0xdd330a5214641503f0d0,0x1e038005493a49d173f0,0xb22688a1bc5e148450b8,0x2702c004550d3c8ea314,0xbd2a49821c7a1b0480cc,0x170200048d103d4e9328,0xb4268841f05d13c3e09c],#[0x28070003fcf2398da328,0xeb31ca726c8c1dc62120,0x470bc0058935479123ec,0xff384cb2e8a822c73164,0x1d044005895250932470,0xbf2dc911c456138380ac,0x2503c004890b3b8dc338,0xe8354b728c851b457100,0x1f04000591564d9233e4,0x9e2207d1c061158460dc,0x3003c0043d02370c72dc,0xd12f8ab270861b851118,0x15034004fd2b43d03398,0xdf328b325c831744d0b8,0x2f0680054134491053c0,0xc32d0a32588a1d05812c,0x1603000489093f4ed36c,0xc1248871f06e178450d0,0x2b05000469073c4e0354,0xec354bb2bc98208500fc,0x2e07c00539364b917400,0xc52d8991e862134450e8,0x1a03400489113e4ea36c,0xd02cca4218771744f0c8,0x24054004b5133f8ef38c,0xcf2dca8240881c85f124,0x2604000441003d0e5374,0xf836cc8274801a0540f0,0x2404c0059d5b52140478,0xbb2b4971fc6f188530ec,0x34088004a90c3f4e7340,0xd730cb22989621862128],#[0x1a02c0052d3645d093a8,0xcc2d8981f46214c3f0bc,0x2806c00525414a4fc3a4,0xda308ab244891c8670fc,0x3104800559454a9143ec,0xde300af24c7b1bc63134,0x2a05c005013448d0f3dc,0xb329c941f06b17c4d0e8,0x17020004d91a3d4de334,0xa52346f170440e82c090,0x30070003b0d8324bd2c4,0xbe2c8a2258871dc4d0ec,0x26040004a118408f2350,0xbd2c4972147517c510f0,0x1d0200046511400e6328,0xd02e4b1274911a04b0a4,0x2a04800511384a5173bc,0xc12e49e2587b1bc5910c,0x1302c0047d0f3d0dc350,0xa6240811a85a1383e098,0x9e040000782f00cb2d8,0xc392c29045c4d2d4b704,0xb095c020419b1018009,0x4b0e4a00ec132f41033,0x80d102a609c5078c3e2c,0x252b8770ac026428607,0x8022435b14050298b06f,0x403100e0c2c2c2882409,0x150ac4109d09612cb08f,0x2ce1031d1f8572fc4200,0x434068b2a44430813300,0x36b1e8962987a1c9ba08],#[0x8320d190b884c108cd14,0x1b04147c0449068ca845,0x20c24c1d0d44c1d891a5,0xd8060d2350ef0d4150c,0x8c2141c0e6024128ae24,0x849108e71d2b16e490ee,0x8363455c34c5a140f102,0x189060a6141704a09813,0x68130c98ad8c14342f15,0x800b5450d0370bd29268,0x970ea108624c91fc2416,0xe88d234330e500240e0,0x4f45c4aa044511b05436,0x4a0f4c6b246f82149a0c,0x90c21b21c916a8d41f,0x4046a29621311083c167,0x7940d000594c22008472,0x67b294684a07d27c7158,0x32c40533341486e1f1e0,0xb132054c0d0844e0007c,0xa0214484b46d0cd428bc,0x832a1ee53c82a577e2f2,0x32dd0221390ee9a3c654,0x36019fdc570a12bdf3f0,0x589ae1a5df89844c0e9e,0x2d834834e005c7c19969,0xbe3528e38a4191bd0499,0xa4a78b7b709ef722d848,0xb0428586687c199cb039,0xd8baa084b039ca13dffb,0xe2aa3cbe3b08aae98a0e,0xb82419558b4f15c286fb],#[0x8dea4bf00cd4fa23832d,0xc27a2e019854b6c9b050,0x4e3a142c78ca9065cd90,0x509346d0dc05282dc103,0x9f24c8101f0a327e082,0x9f6a3973cd068bbc106,0x57e7ee143e11eb945074,0x96dea083d00f200a4e70,0x8654bc5b08d7190c10a,0x64e76aa0285b3b889da,0xa73bea8052ba0e0a3ca9,0xe3f8680199bedc2024cd,0xe5b0a6f5ed2105d55838,0x6f74dd24b65b066da0,0x70f3a52948cff9920085,0xb1b7f6a006515818fde1,0xecd030a5ec81832a45b,0x3cc03d8fb5d7d0306687,0xe2de8430b5ed84b70748,0xf41a9ca93466b7a0213d,0x439db025dfca022abc3,0x97dc570a135ff35b9940,0x9ad374be264d34b1a602,0x86c98f6f504255f40008,0x985d0a5f12b7c0660edd,0x142ef7b714810dd8f92c,0x294d8b0fd098e8d9a06,0x77a3d00f200a4fba0889,0x17cd572f690cc0d12d94,0x1982141e5141c8536986,0x6d40a3970653410b2f5b,0x1b38d385b8458b7b7077],#[0x378142be0cc672a4d1b8,0xb8305184f25df0d369d1,0xb4410b2713c977c2ab05,0xc196c29a48e8fa1716f9,0x25a5f3f709ed3141a24f,0x1043778e387019a63cc2,0xf144050b9ec18f5e67f8,0x15127e0cb614bada0c96,0x8474f15c284c7e217f02,0x83cb751e6901f00d210b,0xd333142d3b78284e7a2d,0x733ed065184c6e1a497f,0xe3060219b8e3fb0e0339,0xa3a2c3d8cdf7d20d9a3,0x84f4e8e9fb8b010b76d4,0x62fbb552129f4303843,0x7722d841754106ab7b7,0x51d96c1fbc3f41d06963,0xf8dfc6c0339be4ae9861,0x2947e93b81095ebac71,0xf42ae610e481836a91cf,0xfcd0652b32de8c9fa043,0x706ac5c60e7286b84599,0xe45b090d5b628086e760,0x7a9010fd06946d3a317e,0x6dbd46aa534c50b068f4,0x35f390a3c3fb4a6054b3,0x56e139dbc1427b8ae142,0x28fe00ae619efb512b34,0x11bde3a14247f6d7132e,0xd70f80ddb40022278e50,0xc0ae61754fa0e1b78284],#[0x70a1c0be4c6a7a7452e1,0x84c3bf82b885f558f820,0xc0ae610df7d20c82d1e7,0xb80cd32de8bd8b80a121,0xdbb6850aefa020c3f62c,0x42d3c570a1f3ed400ca0,0x430384741c12b17483f5,0x5fa148f0a2b7d28a129f,0xdd849b87925ad70f9e06,0xd486fc5af0c0431981a2,0x4c052b38215f09971a53,0xb7b51484e760707875a3,0xc61dfd200cb5768ec2a4,0x72ec8043007e8ac910d2,0x4d1d3b550142d81c10bc,0x546682179fbca2847b2a,0xb6f9100a0219d07048c,0xa443f4051c347f42a9,0x7471b4e8e9e2ca0fab38,0x5a687b199c9c346986ec,0xf41139e8b60c1b38d3e8,0x98cb83179d0b1464e076,0x97148a30bb94474883d0,0x3d209ac6d15909811e04,0x98116c263c157b386427,0xc944a58f8a32f9431d90,0x8bc88ba62f726a0c026,0xa1a296705cc0f586a6a7,0xb9b0ce84adc38d556b0,0xc0a361b21b2197cd5319,0x8e032a3fece024412220,0x3a16025794151a6c3187],#[0x43a1ce4c5a838fc7b838,0x622d3942a3271412ed43,0x2f5ac28681a0fb81b845,0xc718c1f258c265863aff,0x8286e33820013a187039,0x8548580fd23446fcd644,0xe84483ad44a7ac0518f0,0x5e05d1026e883a7d0437,0xa9c67079a58a90dbd50,0x1af459618b42bd42c7ca,0x15381c5182d368723c12,0x83360f941dbc02839b25,0x8e31609c1521b3430e82,0xa4198169e2223d9103a3,0xca7f0190b49e5c066e64,0x1b47683a429b093f4283,0x129e54a8f67828f34100,0x68d6835c1899fe82c34d,0xf6c201db097062ab812,0xbd5718352974461f0918,0x4874f3470e3ba0ef73b0,0x87b61e3a1e45d8109b08,0x2dd415908018145a1ed,0xb3287f76fc5186c31684,0x197762c6d98d042b46c4,0xa707dd5107a78889be82,0xd8a22c46fa82cd872e86,0x6361834297fec1108dd,0xa31f241c96b44f7420e,0x221523381d94299087db,0x945b28401cf71f06d72f,0x8918f920cce865ea0a6c],#[0x19d22f2384199086c370,0xa9e0add0a28fcc52e704,0xa2e850cda2461f0ecd85,0x1c7e658c6837116584c0,0xe95142d3463e4842fa13,0x44de908d83045e2367ed,0x2479a0800006c1a2d3c4,0x8f628b4fec19050bf45a,0xb173b0a2c2a263c4a213,0x1050eadd82f650447e28,0x341b21f7d2283b7b5381,0x42ea2c043d7062ebb545,0xb7a872da511bf5c18bf1,0x8381bbaf453615159081,0x36f5041b4b628bd51190,0x8503cc8a8c6d2cba3070,0x70c9c2002ba1278b0e95,0x4001e84c6c3c107d4100,0x1939c1040001af082364,0xa8fe728cc08c083ff00,0x10052126ce0ab8317382,0x5068fc824703cf5416c2,0x8345afc5907a9304ef97,0xe0ce735c846bbf5f518d,0xef62d64978315e0ea0d0,0x7445d18b2c35acc6400c,0x44ab0e77b123f0c833ac,0xf408336bce083b21d3c4,0x6d545ae04011ab05de30,0x7036421e84c6f6113e8e,0x436431b0d1d0a5362004,0x872c2e35e9e6932e8407],#[0x2302d498200ccb16586c,0x36d3051684be84c757aa,0xa3009df8a23704507438,0x8c00decaa0d1c091844f,0x571e13c0aaab854714e1,0x8df5b1d787019002c4ec,0xd7062a34217678854800,0xb50084a6ef883dd710a2,0x5079618bfd4497668bdf,0x659fa584c7d320e1d0,0x27fd4527a2a6aaa51ba1,0x4ed3931ca0dc228ef6c7,0x6921e20b4f1111b9fc06,0x184721be38a184f4523,0x9c718d12fc6092c34302,0x3dc0d21ba084c0134b87,0x6c5146d2f187577444a9,0xe5109960745d61602012,0xa8a4f228866853b42779,0xbb839b0a0f066bb43d32,0x5e883d098e9d1d41c303,0x7bc2643cf1fd810800f3,0xb118100203438357ca8b,0xbbe4441431ec0f08023b,0xfadee8b5ea82c6882b7,0xec949066d3c444ab0bf0,0xb0cda11d221a0e7262ef,0x777628e3133c9683a431,0xfc90f004f84341018be1,0xd82ac9bc29b2510f684b,0x9444fe410470637702ad,0x876e9890183a1eb43a79],#[0xbff0220a15ddbc118468,0x5124a470cdf45a2cb0b,0x5526cc67321223c1385f,0x10e912d06c8747835fff,0x707ed1c51a6c34fe615a,0x94f45f7aa88c0b1f60aa,0xaac64cbb02128e84b61c,0xd2cd166c3b2070bb614c,0xb67b17c57451b742d866,0xa93c2d3c444ae0c5ec0,0x296045d5051a6263e145,0x61eb1832002394107116,0x5a15dd0dbe4d41eb9410,0x64ec98949241a2f74416,0xa2f76e0a9304e0babc2,0x6ab094865d60b6509df6,0x40739330fee86a8d166,0x3df9686341513fd0600c,0x6427b81e3cde0d524c44,0x7b1ee24537d148347d4c,0x5d093f50573c103e0254,0xd1b17d6c667d510e421e,0xe1e1e3454d1d30236965,0xf00ec84c096650e78887,0x380c8b7c6a28f610980b,0xcf9a23a4517425dd89bc,0x624fa9318006c3d7728a,0x62c4f870194bf800c918,0x56434bb30ab831181375,0x883302113c10b810bb94,0x96448e04003e98800c6f,0x894e058a367cd207a131],#[0xa9a9c26032742605a788,0xebfa8cc0a30c4002f582,0xeff51246c4c47c1005b7,0x7a94570898f128b88e0b,0xab1c302cf25a0e788860,0xc3e960ace0028f550b1b,0xfb582a43b5424e98a23,0x6d097e221cbac1190cce,0xca891f7020dcf0310a92,0xc0a7f031ae4a18018171,0x52a3d49822d63c2b845a,0x605c6705ad2086684a79,0x102afe8300ab85440000,0xf8321173a263954527cd,0x227ad0c2e704a0c00835,0x42e97c101d1002d269e2,0x7625c94367d098340547,0x7f921979141ea7195234,0x1c5e4251dc225e0e4515,0xb430e1d83223c14c7785,0xace855bb04005b0dda1b,0x17db34907435ad8b5260,0x4416586c84df86f184cb,0xc097a2002bf54523c167,0x59618b420067d510f6a1,0x6c1a2c6882072c171f34,0x2d0eb03b2007e8fda208,0x244299e8a2a6c82cf18a,0x80001cfec028052fbf30,0xe6e5ba8c58b822d84c0,0x5643d382bc07341264fa,0x8635fa10f06d70a65378],#[0x24e9c356c086b43045f2,0x8c843026030c0c303338,0x86cf0020f2c21b0cbc8,0x6b030fa0947900b0c79,0xd18f920d9fabfa126430,0x2b4df89642dc2244fe18,0xcb0410948769da29192c,0x9b838b08b81a3c40a8f5,0x15a09dc1d123f2080286,0xeeac5876250549e38396,0xcc0a1663099fc827ba1,0x1198345ce7f507da4bb3,0xa25bc4a263c4a219ca6,0x36888b9d127f8183215e,0x1100207168b98250617,0x443020055e7615848e7e,0x859d15da1b844341d3c4,0x9c6707a78889a3838743,0x34d860d08df905075a8a,0x23465a3f702f7434e338,0x5f6b511811173a2a4982,0x98d9a3059ce484cb2d10,0x5da24a6c45871f6c990c,0x6c84017a850b83bb835,0xb21cb7b445a5881c092f,0x1960e07cf0840dde1283,0x250c17728a970b94253,0xc86c864b333474ffc222,0x8360200ce07ac25a558c,0x4e08051d0d2110340bd7,0xa5ff5811050d4ea0a90e,0x41fae930770880280be8],#[0x657e018c17a2302e7c3c,0x5e9c470b485361ea6d1c,0xac850f1cea30f426314,0x566855c98b6e75e9a90c,0x4ef97283cb099de0ac8,0x168d2f7444a922d0a3cd,0xf3122a5e345ecdc16580,0x7604253f0641427b81da,0x8b4f11134d5455c18b91,0x820013c6c54014a015c1,0x1631704973688b7828fb,0x190d03839b0a4eae16c2,0x28c9821a3bb1781fc936,0x1d1d63e064862b41d8da,0xb542da0c5869460acc1e,0xf9e1b2101ddc227a0107,0x8b30cb2e033279314303,0x301bb3a88036f087031e,0x8763e1e0981530e0ae11,0x4025d60a7c0489161cc,0xfa41471895d50585e1d6,0x3c788c1e5f8434bb3442,0x131d85b46f66a925d3a8,0x62f12cba3cfc0638eec5,0x42a1bbc2cc718d76851c,0x15bb054382c6b60a395,0x8227d3d2b092f9320c00,0x70e144b7d0f51d5851e6,0xe3bdb1e9907c1e587770,0xa28d85470f4b066932e0,0xfcd11b81a428e3055c18,0x147c7451411c16ea10c6],#[0x5bb0480c0ee8061f1e10,0x3a930527fd4457db6a8d,0x846bd4a28ba1dd087038,0x79c146cf3415908b0e95,0xe31c5d0e654c64cd2c59,0x5851f4cfb44e1bb61ce3,0xee709a788893636251e,0x3d4998e31dd6bf09524a,0xa90f6570b4f11114f42c,0x3e8028f1ece41bdf41ec,0xa8e90fdc8a2e342b3426,0x411cd4709a1f0c686870,0x76d052c2634410381274,0x77a5456426c182d26c94,0x8ca39f110cccf8260200,0xc09361000096c4e0daf6,0x8e77d474fa09d2738a10,0x7022cbf400aae21f504,0xd2c22e9089fc82e84363,0xe7242662ba1a708c1ecf,0x21cdc1bbf5f5199d0e70,0xba945f15d141d6a2da0d,0x2808bec149ff42a3d419,0xc65742effc0882859b4,0x27d164531ba2365828e5,0x79b0a6c3debb6347e416,0xb049b0c5a1b2173d1894,0xda133f9043908725e1f6,0xe84b8c9a788881c3c635,0x6720eae15177a9e32521,0xefb9630977424bb3c277,0xa840b9b446055c18bac2],#[0xc1283a428e04c0b1ecc9,0x14218100499ba066a979,0xead005240762cb0bbe37,0x51f8283b845a831eb169,0x4201d0c61886834c0ed0,0x5608dea0bb497091860c,0x12fc34193dc0a7f031f3,0x1a7b360c801aeca8363a,0x4028e8738e31807dd015,0xa1806b24bc1e9e2226d0,0xe8492f046e08a0c7cd,0x630964e3e6886e84c840,0x83252147241470c5cc0b,0x30b4f11100034d89bf81,0x8adee506010c90401134,0x6b6831d6b62270396ce,0x5169c4a247e410cd0a37,0x93c2008bcea25ea129ea,0x20c1c0990906bf06480,0xb429da14303929e891f7,0x14d05dfb0106f6155a39,0x28260396125bfe83660c,0x16a4c16a4c178e0a024e,0x10cc8788c9834fac43da,0x2459fa00c2f38a080076,0xb21ed3931b01d498,0xf3bec9b24bf505364a2,0x211290ea4c12b7609725,0x742604e62d4d1ec6843d,0xefdcb8642d638c667425,0xaa233ea88e914b030743,0x5849c5054382f7f28a4f],#[0xb8ec779e1d4982478414,0xfb02b9287768795c7082,0x2670370892e5d442c52,0xa000e07ba131a1c2a23,0xe08bc880e0e8a102bf4b,0x9110e7ec194637c51125,0x5ae07bad8b5f57f6dac0,0x3cd087e9c03233f90460,0x379e0ecb99d4727fa880,0xaf8d6356ec10011db44c,0x52676151ea0e6c31c62,0x4d928b7e261106685a93,0x46836e0d1062e04ee751,0x12bf40184ab0ae4a1e58,0x5a70a8ac86c86e116a4c,0x90f0947075f31005d9d4,0x641450eac245d0cf110e,0x88b14bd1f456856fd380,0x882e865f3841b7d8eb64,0x550bb618b431bfd8499d,0x7188c0b2c2a73288bc8a,0x189cf0a884e87df0ac1f,0xcf0020c035b6c4c10a5d,0x81f20a0d80adc8a14600,0xcc0b5638a45203ca08c0,0x161033438ba11ef05683,0x11fbea083302bbe42947,0x3a9456382ee0403506bf,0x800ef72a51fb02b3c17,0x85c15fa10fdcb18317d2,0x544add47a83d61b21d41,0x41237d6c6cb88898660],#[0x3f0264d41db432f082e7,0x8fcc2cb42c38d40ea48d,0x95ff58122192ecd1590c,0x2bfabd5a4286098ecd19,0x85122cf907bd217a09e1,0x108f052362f380c51a1f,0x363c0e519d2b2347866d,0x4e8ace84bc8a37067c44,0xa945161d604c0a30c435,0x90d9b89212dfd2c18045,0xc51b0c5a10022279cb6,0x6bf11a9f0a2ab81cd1a7,0x7728b5a1bc1cb8705ae0,0xfbda96187a131ab5f041,0x18ab8314e6b908b0f105,0xd84eeec537c6908652c6,0x7062f00e0a90b61661f0,0x19ba1170303e785ee068,0x5c2d62e0a90e586e1152,0x2e970a919d1043743038,0xf38210e9155b144b41eb,0xc734ecea3a43161515ba,0xc55c18bdc0f1d1441e84,0xcc0919ba707ed3828ee,0x872d8d09955c60adf2d6,0xe09dd3cca309c6610045,0x9707c670407d02ad5242,0x91783049a2ce38c6eb7,0xe928f610916d666193a2,0xa3f208da60831b0688ee,0x1a2463e483eb0bdab951,0x2510381daa12d04c086c],#[0x3f80c66050b831c3131e,0x782848ea51a022060e05,0x214041b0cce0c9dd20cb,0x4878ce0b1e09a036ac35,0x2e4a24c44377ba086a85,0xc783a9304d0de8ad260b,0x8e0c2a2151c783be221d,0xd603d17b3130660411c1,0x63002ae74407b2896650,0x68d0e77d93647ba1af8d,0x8f4f11129870401486c8,0xd45708bafb354737f06a,0x6a84daf0c7ee068d0b1d,0x3a8e4f4a8a2c33414d87,0xa8e2d08a6fd07db0b1d1,0x706224fe0327b8123c16,0x36ee141d5e28ae11590d,0xce896349ee055bb05474,0x400cfe4166362f02e880,0x13610f0963a702f7a94,0x48742274227426040e04,0x928697e545b655103e70,0x2162959d05f07a78888b,0x10be7ebea386504972ea,0x9040068356ec253e7a00,0xc7762cb7bb82a4d4187,0x859c0e9e22247286355e,0x6c3b645107a131c2e0e5,0x343b6f511dcda247e417,0x194ae6680292ae4f9a3f,0xc444ab22893a624d7870,0x1cba1a9c1eb81300a4d3],#[0x1ec398887c93059742b2,0xa6aa24fd9e0c85b0cae2,0xa107f4145a1a421e84c7,0x20f5ab1418381e338293,0xf07f31d13da985474f55,0xd8fd9c0910d5c18912cd,0x74f01228d04003d098c,0x80839e38d81997f921ed,0xf7f289bfe06300ec3ac6,0x6f130b9f2fbd09d086c6,0x6c2b142368ab07142d10,0xf7d1483e3f02d47d5b12,0xe0f45be88c08c0a5fa82,0x3b0667d0d51c71889f6c,0xa0dc7868ce0a1e960e1c,0x86e86b8310c17a25da16,0x90c259e0981372c55c18,0x4e854f104198125362d9,0x368cef2a82d4877928b,0xd8402ac22e0402550a6f,0xd0b1476ea0a56ea0d01e,0x9c098159098169e22279,0x23ee041ed7989179e209,0xfe6048851e10a90f19c1,0xa839b82605368717045f,0x7045742b71ff5199f545,0x87e382a7d7f5185d08b1,0xa28d866c9448f4412fd0,0xabeb2638e18a8e87ee4,0x829e1e31831e8c1ad04c,0x9812fa10c035f6080007,0x8ba173f9a0c85a8fe032],#[0xe151000e2a19817bf770,0x54fec19050bb7cc128e8,0xfd8d22321840c5c0846c,0x10b9ea0e860b0a386277,0x19e4b41990b3f9052f54,0x263000f8460134f11140,0xf19c166e0dbdd8830f4,0x436b82a63745dc588018,0xfb4171a108e0c7b3836,0x471895bb051b83]]
set_option maxRecDepth 32000 in
def g223H7 := limbs80 #[#[0x20090268865a524280,0x58810004005800059190,0x4429065aa12680128010,0x8250241921a058465069,0x11548a168055a510010a,0xa660a11a000a8206091,0x682208201402a4289122,0x50a54429224868292292,0x2860541a6498a1848a91,0x2646800a6822581a0110,0x105850a0141409844144,0x22092884481521929504,0x8415402a05241850102a,0x485450099995aa060094,0x5011002925010480a442,0x9100960a20121908a029,0x85029865a4a804844900,0xa6852a481446800a8281,0xa8192054055469651294,0x1922858442810094922a,0x469a624152158aa5640,0x489041502414a22a0aa,0x60428558884444198564,0x48168899920a00001292,0x888a12896a00202a112a,0x5a82110a5188580160,0x28212528a25624268126,0x8201088181a11a2a4148,0x8a94558a414505604501,0x84250540800006201090,0x5a2089149285126986a5,0x15201852208524a80500],#[0x81692a46849180041948,0xaa2208a004116050850,0x522261144218829a0484,0x82482412626529841480,0x9122626945908882559,0x2441651808a000a48100,0x2620480001a892a59182,0x20e49f1a21a068000219,0x1c3004fc4baa8780970,0x637e097864a2b810c852,0x120500de4499c670f235,0xe135b3664707644981d2,0x3701acdac8f5161b1051,0x49c0bd622d15aa9a306a,0x50948405de8a442dc471,0x4d2a84793c8e9c92d221,0x9f72c26b3309395208e4,0x30d8a21cde3dd210fc6,0xe32f4ce81e94207218,0x20ac98d594a28cd411b,0xd5c4659c17477d06dc3c,0x6b30e08b426ca0a5dd01,0x423111545207c0218220,0x2c5ebc01e28e05773b48,0xc20f52b4a0fcac258bfe,0xc129e8505260e3240186,0x62802908e59219ec1838,0xef117a3301000ca7a390,0xc18822a1a83e01600020,0x819a0a18896a30ea805c,0x44bc2bb08a27b812aa05,0x309806468f040927cf8],#[0x501ec6400960d4446b94,0x20612001406703a28b06,0xe2000a408aa82c16ca41,0xa823985ca9a430b6000c,0x268a20033116e0bab14e,0x35b014c81d3027a9e082,0xf4910535d0fe0a00295b,0x22018a4c0008a14400c4,0x9fa42ed8e384ac25164,0xcf05420099aec27694e4,0xc424106eb42468159604,0x19384a19158082cb8d2,0x904c07c0ff51f269a620,0xbbac12b0150f5edbe033,0xecf06308320d203a959,0xa7c6d56100043154817,0x90a40d24c3c5409b0443,0x17e8a1dc0369a0802b80,0xfffffd188000030e0561,0xffffffe003ffffffffff,0xbfefffff081fffffffff,0xfffffffff880ffffffff,0xffffffffffc5f7ffffff,0xfffffffffffe3fbfffff,0xffffeffffbfff27dffff,0xffffffffffffff97efff,0xfffffffffffffffcde7f,0x9ffffffffffdf3ffe7f3,0x79ffffffffffffffff47,0xd5cfffffffffffdffffa,0xfebe3fffffffffffffff,0xfff670ffffffffffffff],#[0xffffb77fffeffffffeff,0xd0fa99dafc7ab1ffffff,0x8f4f03afb0f6160cf48c,0x186b2dd98164d5eb4597,0xf5922854942d167c175b,0x26938dc2a7a274ac4132,0xf567003bfeb31a05af19,0x4a80862776f3790e37f0,0x7ce851cae987e24ab3d3,0x36afd0d6c48265e5,0xfb592be8f4bc7fb0f3b0,0xba519737a65ede510a4d,0x5b0fa01d4cbc7c9f5f60,0xc375fc54dbbca29fdeed,0xeb4527d85bdf687ccbd7,0x84399adcefe0d93af733,0x5589721a454ad8f77127,0xf5d04735416a39b1bc0e,0x360a37759b8bc4ef5517,0x6f476c0cd7466ccf68d5,0xebc719a330a94d5bcff4,0x561a5d7a26273ff590ae,0xaa6b32263e2acb7c879a,0x234d2f9758b5bd079263,0x3538cf0fc274de09c3aa,0x7d7c5cd25897b9c85923,0xce9c90f9eb58459e359b,0x62895aaef7dd0f1734bc,0x9a7b7ad974ed77bc26fc,0xbe6ade732f578b7c14b6,0x3e13dedcfde968ff47eb,0x50c93c0550aa2e76b379],#[0xf4d8771cfb0752f817ce,0x5b41c8244644f5b8e764,0xe7dbe2854eecb4eb34c3,0xa1b96e16b03733c3c529,0xac26cc8bf18e2c5a8add,0x949cba307627cc6e9f8f,0xf6a21b672b40881d073b,0xa5fdc367499fc15d3315,0x9dd2aa503aeb08f025fa,0xdbf36aa821e5ac45d3b6,0xbbfcedcbccf60c21e250,0x663c5725bdbc5eda519e,0x7b4df1746ee9e592beea,0xc9a83d3653af95b26cc5,0x56203e7b99710f4f4188,0x262ebcc1942fab6afe63,0x55a2d13996764fdd9bd2,0x11fb54514d0b90bc]]
set_option maxRecDepth 32000 in
def g223D8 := limbs80 #[#[0x54510541104c9104c510,0x58d105851054d1054910,0xd89105d9105d51059510,0x5452050d20dd910dcd10,0xd4d20d45205512054d20,0xdd520dd120dcd20d5120,0x54930545305413050930,0x59130585305813055130,0x985305d5305d13059530,0xd8930d5130d453099530,0x54d40549405414050d40,0x58d40585405814055140,0x5cd405c9405954059140,0x9d540995405d9405d540,0xdd540dcd40d8940d4d40,0x549505455050950dd940,0x58550581505515054d50,0x5c550595505915058d50,0x5d9505d1505cd505c950,0xd8950d4d509955098550,0xdd950dd150dcd50dc550,0xd89515d9515955158551,0xdc15255152dd951dc151,0x5c1545955459154dd152,0xdd954dc554dc1545d954,0x5956058d605516054560,0x9d5605d5605d1605c560,0xdd160dcd60d5160d4560,0x59161551611d561dd560,0x9d5615d5615c16159561,0x5c16459564dc161d5161,0xdd564dc1649d5645d564],#[0xdc1655d1655c5655c165,0x5d2655c265dd165dc565,0x5935058f505875050b50,0x5d3505cf505c75059750,0x58751d8b50987505db50,0x59754d8b515db515c351,0x5c362553625db545c354,0x9de6fd53625d7625d362,0xbaedfb6ebfaf67f9f67b,0xbf6fcbeefabe6f7bbeed,0xdbf6bd7f5bcff3dbfefe,0xe3f7fdfb7ddef79ddf73,0xefbbdedbafeb79fe7b9d,0xfafdff7bddf6fd6f3fbf,0xfebf9fdff6fcfeffbbed,0x8727896589ffbfdff3fb,0x2b84760f81346b730e09,0x9c8965780d866209845b,0x809d09879a0f81870b80,0x1785730984170985150b,0x8f89657295647237815a,0x802771826237819a0f81,0x1d85928b757451769339,0x4f3b80108965438d6542,0x849d39804f1586720987,0x9805c0c87720983170b,0x9a09879e098415098316,0x87391d854f8875745975,0x37811129847103845609,0x9c098796b1531995642e,0x803959759e7172620b85,0xb849b1784740d816f39],#[0x9b158678977473258439,0x631d07834b61749a0b85,0xf87720b839b0f81609d,0x5b53760609851685655d,0x80715376540987920983,0x47817c5f764051768941,0x7d91656d3d850ba16579,0x6530e36203c5432a2d84,0xbd650275739213839499,0x4b11853a2f83304b808a,0x834ba5652d1183507f80,0x55657e75549b11857913,0x88cd432d7b73435d7640,0x750f7b744377734f7573,0x5d65613d854f5d655277,0x9138731a38474798062,0x878ba565427975231383,0x49806b11877d79819511,0x6275819d118731a16543,0x871f7f732dbd53294586,0x796158c5540e49802411,0x393d81137d751d3f850e,0x850d4b852d7775117773,0x3f830fe5521975752711,0x3477541513844b76859b,0x806c4986296775301383,0x7573323d874fee611949,0x1b1186587f7602478076,0x83197b752e21864e3f84,0x7582983d8427777539db,0x44768711916565c55432,0x7312bf534211833c1287],#[0xed61197762507b813477,0x56b7534fa5651d7d7419,0x811c3f81106776281380,0x6f834b75879a75859b47,0x82777510d963194b8040,0x832a4b834275809c4781,0x19866ca780677b73063f,0x62118652c54332118059,0x741013806065741f7976,0x55768a2d862cb5534f77,0x2711873779741e11846e,0x80466c834b1383867574,0x75849b77809d75849d4b,0x91b96562c9542e138694,0x846075541565543a7973,0x11863a478603bd652967,0x6e19866da5634219867d,0x73021383909165455565,0xa16443e57229a776427f,0x4213872b757247bd6519,0x853977732ab55348bd53,0x11808411873623838c3d,0x28118651118361498037,0x8057e381115776466575,0xe5821911856ee582023d,0x7949803649802676870e,0x853013833511863b1183,0x758222c9432e3f84102f,0x421187243d8492458078,0x74485576203f872a7f74,0xad652c49802577750b77,0x8d75751b758252118353],#[0x805449806d6575307762,0x75753913842247816547,0x3477733f75859c796194,0x542d2f8481d5530e6784,0x5d752019866b11876ccd,0x2977849d65748b11837e,0x8311757492c5822ccd54,0x1b83677575185d65513f,0x79a3807412874577730b,0x752d2d8436bb534c7975,0xbf804633836a91658a7f,0x837573485e655277733d,0x860c1184531385211184,0x118085e7801011853c11,0x2a4b802f33834b3d8392,0x655d7773484b84427575,0x7973895d764e11847099,0x2c1380993d850e7b7303,0x534c1180633f809aae65,0x11876d4980385f764eb9,0x3b3d830ba180735d7531,0x83759165435576441183,0x75819b77730479752e47,0x57458077458579e36200,0x8698bb534377744f3d85,0x11871c758234a1847413,0xb3d809e768710118451,0x845e5e65511187207573,0x49861913868e75725faf,0x5d118726b75348118725,0x54397f80224b86292f80,0x777413cb842e3d834fc5],#[0x367762945576311b866a,0x715fbd53025d65985d75,0xb7533dbe65194783067b,0x271187382f84347d741d,0x828e75822155768b3d85,0xa08774d953193d844f75,0x8ea18573cd4329118352,0x7524a18074e542195d65,0x3d8312c5542ae582295d,0x46767532b5533d796562,0x80957b81606d738a9376,0x65646113830a3f844813,0x2d65762811876bb95343,0x812ce76229a1652e7d75,0x75825133838055656fcb,0x2967744177743f2f862c,0x83482f847c11878acd64,0x47814a79751ea5632d3f,0x9a77549b7b73757b734c,0x53292d8437e55229e381,0x11856fc964622f845ebf,0x207986623d8314478141,0x8294138634be65291387,0x458071e532024b802b75,0x2c11807f65643a757501,0x762c9b847a1186506576,0x7d761991658b21834d67,0x9c677528138535138609,0x809d118358a1641e7685,0x13839875744811838375,0x2113862245837911857e,0x750be762022383461386],#[0x65741ced612975741b75,0x61e13203cf842911850c,0x8486bf804077750e1186,0x13848e4b86194b806a13,0x34c543392d8438916544,0x87391384907b76034781,0xa1651e7575327d76293d,0x295d658f556579e76219,0x832c7f734275759a7f76,0x7762587f73293d80962f,0x9d77752a7b732e757250,0x841377730f3d83397781,0xb5533f4b80074783033d,0x34837180c1655f57764b,0x7631e9530f8181538383,0xd2853081765181752fa9,0x8c83756482653ae95339,0x652bf5752d817652c183,0xd17628e9541b818535c1,0x4a4f8647d1805df1752e,0x808281814be97539f381,0xdd632b4d8650f1851e4f,0x80e9824a4f838b817449,0x752b81650cd164338171,0x83844bdf834b81751f83,0x454d836d837364f55342,0x852df5541d838390d174,0x8375654d8383e97448f5,0x82c3848cf78329f1541e,0x5466817649d27528d374,0xf58419c2652b837183ab,0x3d3845f83738381761a],#[0x733ef56302f56419f163,0x4f83354f805581763883,0x6cf58442a965074f872b,0x752deb5332df836aa963,0xd1853081737bf58302f6,0x22827569818151f58619,0x654ac174408175078186,0x815451f56529826521c2,0x31838720ab807a4f805e,0x6551f2851e8175338387,0x4f830881764a81751a81,0x7b4f837b8176344f8731,0x86054f835f4d836c8275,0x4d8638ab866ac381464f,0x31818694c3834681871c,0x8335c1848ca96564f580,0x4f8765f55119c3838c83,0x95f7532d817569837483,0x86294d86268380608180,0x4f8545818486f38165f7,0x284d87454d872b4f861c,0x6225d164414d816bd265,0x4d8605f7806a4d807deb,0x37818634e9544881751e,0x645f8287314f87454d86,0xf6852dc38097e9752ad1,0x414f844b4f8568e9734f,0x850ec16549d1642bc165,0xc1533ee9530b83736cea,0x5281872b8380954d8084,0x85354f83314d876c8165,0x81653af7804b4f836482],#[0x53f1611ac1744ef7541d,0x841ed165288373808184,0xf783024d8625f3817cf3,0x33f173434f857bc27531,0x8365e98311df8380d154,0x4f8634e9822b8176374f,0x34dd732bf373434f846a,0x8390e98205f57342e982,0x4d8453eb624781833581,0x4281638d4d862b4f8446,0x8738818099e9743ff773,0x837531e9825f8174804d,0x1c4f876481834b817380,0x8480e984104d861a4d86,0xc15343c16538d3847c4f,0x44a95466f551424d8085,0x8698e9532af17443a976,0xc18346c1651cc1844681,0x4ff5611981752b4f864a,0x8483dd7344eb6250e953,0x81878ba9846781844b83,0x83d17528f16125817641,0x76478175688187658184,0x4d8744f56329e9732a83,0x80f58602f5811983834b,0x534cf1532e818085ab86,0xeb5427837641a96569f1,0x32f3851ec1654781762b,0x8621dc8380c16505e953,0xf5532dc16440f7860281,0x404d8765818720818745,0x851eeb621a4f81208176],#[0xe97247817633d1842bf0,0x5081761c837444d27530,0x8422f1841e4d83368163,0x4d8651817625d3845e81,0x834f834a83814bf38343,0x8183818451f573298174,0x818731c16540e9809a83,0x90f15343f1734c4f8343,0x7343a96545e9533d8184,0xd18330f3734c4f838083,0x26828521f77442f56519,0x7638f38134d17465c165,0x4f816a838634dd630583,0x2fa96364eb5339837347,0x807c838535f7802bdd73,0x83849083763ef553294f,0x994d873681735fe95427,0x8764c176404f851e8380,0x4f861aeb623ed1641c4d,0x4b4f8346f38743d38460,0x814281763e4f8060dc83,0xe9521af38182e9544ff5,0x2cf5806581765fa9657b,0x73394f8420a96544d176,0xa98074a9656583762be9,0xe8165214d872fc1644e,0x53478176504f8535e985,0x81748ac1654a81868ec1,0x45f3811ca9807ac2651c,0x832cf171648171838287,0x82872bf3541e808708d1,0x85817347f08743c1653e],#[0x805e81871f8085358380,0x4f865feb744ff57629c3,0x2c83546e4f8743f57142,0x8367f55419818521d186,0xd1753081648e4d8337ab,0x1c83752fc15440817531,0x6550d18431827533e982,0x818652f5511df57442c1,0x6ed16438f58629828708,0x8652e9733d8374808154,0x4d8424c18097a9652f4d,0x4ff5804581751cf78046,0x851fab84674d846beb73,0x4f83454f862bf1732e4f,0x36f554424d8641808731,0x7531a98167817520c175,0xf5732d4f8347818334c1,0x5e8186514f8334c16552,0x652cf77142a96568c180,0x8383834d81244d876dd1,0x7bf58020817626d1542f,0x542bc384464f80818175,0xa9651e4d8483ea7539d1,0x51f37443c18146d38434,0x74514d8451ab8167c165,0x81812281848ef7708081,0x10816451f7511d828765,0x764e818383a9651fe981,0x81764783764aab8074c1,0x83eb733df583294f8569,0x8367e954104d87318181,0x818060e9744fe9723ea9],#[0x850257012f00004f834b,0x5a0829071505df04c003,0x250def0ccf0ba70a7e09,0xea13c712a3117e10520f,0xb519951863173615ff14,0xa11f7c1e661d3d1bed1a,0x82255d242822ed21c520,0x472b1c29e728ea27a826,0xb830892fb92ea22d622c,0x853662354b342b32cc31,0x843c4f3b4a3a0d38cd37,0x564237410f3ffa3ebc3d,0x3d4818471045d3448e43,0xb54d8f4c864b784a5649,0x3f532e520450fd4fbf4e,0xf858bd577e567c556454,0xef5dee5cd95bd75ae059,0x1a62d761c860c55fb85e,0xc9689167606635652564,0x436e346d1c6c0b6adf69,0x3740672cc719570716f,0x42790e780c7719761375,0x107ee47daf7c897b5b7a,0x558422832d821c811580,0xbe89978891879d866585,0xe83e008e048cf98be18a,0xa12c440083349648a2f8,0xc3890c46007e38178973,0x4a9411605a0084391929,0x168923813044008b3dda,0x3c178903a13446008036,0x77b516a943a9344a008d],#[0x88bb18e9d389485800,0x3a0088ba98495399284c,0x1842007d3817496330e4,0xf104320080b79829f381,0x73e15864007e3756a8f2,0xe8c3693840008539d8aa,0x962913a148480081b556,0xbb18ea03a13c3e0087b7,0x80b65668e33120480084,0x7ab416c993c92c4000,0x40007e369889a3b1244a,0x3444008bba9849c38930,0xf8d0280086bb192a03d9,0xb371203400863756a922,0x8c339004000843998e9,0x58c89339144000883b57,0x3c19caa40178640091bd,0x7b3615c88338f0360089,0x7e389788b330f43a00,0x3e0083b81809e3b1444c,0x44500084b91608532108,0x412854008dbfda2a93b1,0x3a1444e00883a5548a3,0xca03b13c4a0084b997ea,0x1889f3b1305000813a18,0x34d5a8a3410c38008a3d,0x873a18e9d3c148420070,0x7f371809f3f14c4400,0x46007b33d56852d11c40,0x4062008fbcd989a3a94c,0xa0d026007b3154897351,0xd3f15c60006026d0a702],#[0x891359304e008337d769,0x5beb4409384c00793516,0x34158872d0cc2a009541,0x7db4d56862e90442007e,0x7ab5146802d9284800,0x4e008b3918e99351384c,0x1c68008c3c198a33f954,0x890034008c3b590a13b1,0xd3814c5800723296c923,0xc97381385600823896e8,0x98499411605400863cd7,0x341448933114420088ba,0x823a58e9c3b944600078,0x7d34966963a1345400,0x600082b79487e309043e,0x14420090c05aeb04698c,0xfc3a008c3f1aaa13b1,0x439130440071ae138823,0xe963c9486c007fb796a9,0x16888300e852007ab3d4,0x3818c9a399344a007fb6,0x73b3140752a8b8300078,0x7bb6d6496389205600,0x5c0075335588a3291c3e,0x1842008cbbd9aa93e130,0xc0a8220073315448c331,0x32e8fc46007eb655e7f2,0xe8934124560076b35467,0x14c8a391546e00813495,0x3294882318e44e0079b2,0x85b5566893291c40006f,0x82ba17c963691c4200],#[0x3200652ad1467268b444,0xcc32006b2d14689308d4,0xd0360069aa0fa6d268,0xc3a9344e00753194a813,0xc813891c3c0073b39508,0x1467c3392c5000522651,0x2f53a7c2f8d82a00762f,0x74af94a823590c50006b,0x89bad6e8f361445800,0x4200732f12e6f2a8e454,0x10460079b5962963e948,0x915c46008538d7091349,0x5368e44a00893d5a49d3,0xea03a1344a0089bcdaea,0x9a8a64115c500082b6d7,0xaf52472270cc3a0088be,0x7cb614e82300fc320077,0x73b0d50843593c4600,0x520084b919aa53a95c4e,0x404200823958ea73f93c,0x21444c008438da0a33e1,0x6330dc2c00883c190a74,0x8a3795450006e2e1428,0x94489338f8460073b194,0x2e1207934114440073af,0x6bb295887369284a006d,0x8bbd9a0aa3f1947400,0x4c0079b497293369385a,0x24480088bb9a29739938,0xd93854007e36d8094381,0xe3115c500085379729c3,0x483329184c00813856a8],#[0x52e7b308e446006eaf53,0x31942892f1084c0071b0,0x71b496e953b158660076,0x8b3a990ac3e11c4a00,0x4c0074b295e943911c56,0xf05a0092c0da4a83d944,0x99344e0071b154883308,0xc3a92450007033d5e943,0x943c92c5c007fbad869,0x9407a2d8f82e0079b316,0xb215289310e8220076b2,0x8038d7c9c38108360072,0x25c3865882965d2f05c0,0x820ca38da88c00df1316,0x98b8024a268340c0b0d,0x39105031258ab842b04b,0xb83a0933092090e864a6,0x41c0722d023418508090,0x30a84a29011c274021e1,0xf145902c232712131d86,0xf028022d8205d1a8ce1,0x1a8d9a5365041d2821c7,0x22350188c1b494501474,0x6330e5480b972bc18b8,0x56393445804310aca2d4,0x52147000158696e904cc,0x2f1c820de1f238f0650,0x870932e40cceb1988822,0x93e10161ba7cda680901,0x64090449c07cb44c1489,0x46241e4b27c484a63e4e,0x67c4fa1414d1c1c5eb00],#[0x5800419bbcbf0080330b,0xbac6b101a044e06e123e,0xe984b28d7c5e1611f3fe,0xfac259a7cc750308e14,0x38d2b8e16d4d3ea42847,0x94349eb8228bdc21a42d,0x81957c9eb8234bf51400,0x34862fa7dd04019e34e9,0x83a7fd140c34301907a9,0xe530336d4aaac23829a3,0x4a419db0dfab424cf9f6,0x6942e7d474800ce1f768,0xb82383cc6580a1a1dde8,0x2e934b28358a38499c9e,0xfec98041981ab2e384cf,0x11de2e3e844cb2d3d65a,0x966aff5d0965945e06e,0xad0142cf3d704580ff5d,0xb0e20664f2e5d2899ade,0x61e1f871334f03822c7c,0xf4483347fe991d200347,0x83dd612cd33b9a8b1c78,0x387d7425981efc961a15,0xc117be5c00cb5f11f992,0xd182e126694537073cf5,0x632c0a0cc0fecc51810d,0x8da1d064d21818c2bc20,0xca83ef20856f39fc0019,0x41981a7daa13b961c40c,0xf09669853d7047ae5800,0xdb354346d6d20ca9d8b8,0x8584786fd5a126677f00],#[0x320fac0114f7020f697,0xc08797e48106043674a,0xc0472f3c7a265d7d6174,0xc79402679f1c1117a9d5,0x3f8404746dcb14227f8,0x6fe1b133f71fe0500cd3,0xdf40c0a38fd990197b20,0x22077fa0a066d9cff008,0x7c284508fe0150665fa8,0xc8b01980cff5e7000930,0x7b0c065cf1c4d7a66ecb,0xde34a000342f70b4023d,0x3ecc0050b0c3da810bdf,0x4efc8819250489e61437,0x24cfbfc8a011986f27e8,0x500cfbafc408b502fab4,0x93009a79eb822e7d3c35,0xbf120642ffec4c00cc7f,0x5a08408613ff16616120,0x9bc91819d6f7d7411a1f,0x28fac011634da9065cfc,0x87841e2c11543470c103,0x190f38184d4fb4c4b080,0x8d5a71b62000d1c1fe8,0x198d461e670a197fee2a,0x81935af53850b1937c50,0x87d3c9532ed7b522c7b4,0x810bdf850324734f2ab2,0x41a16504b92f0a8fe640,0xf1365b7f518c285361e4,0xeac15d432c77e822c62d,0xff9045eebfc018019c08],#[0x4042decb84aa3fa045c3,0x1214b84472e1267f747a,0xc404367f000832da2c34,0x6a28650bffa04647f200,0xd38f220655bd01b55693,0xb14356997f3227f818,0x6dc486ca7fe333283925,0x3e12cc3e4eae023d3077,0x81960bfe91440cf14b5,0xb24e4a860fa53819636e,0xbe850ac9fff520033da4,0xd1d03377ef5e501991b5,0x292126cc243c96821123,0x754ce14345bff0229bd0,0xd7eca19fa71a6401a219,0x4000678ec3eb0966e068,0xfc0c60c3bfa042c700ff,0xc0020cd8f50c320d43e7,0xb48066cec14e984b3d72,0xf709032c77fbe644fe3d,0x40ca9faa00cbd6e0c71,0xf22804736ed5ac90b95f,0xec000d18fb1111010d3c,0xaeacc3fbc1411b3e34cb,0xea1008f6e0985089a5b9,0xc62fb4047ee14a41966b,0x2003437dbd66a554001a,0x67ce1fb518c99c3bd781,0xefc28000d105ffc0480,0x2e934b283c22d4204347,0x5825b7b2f30034fa90c1,0x31cfea8008d4fd863424],#[0x1883f940ca73f0096ba0,0x19ab6e440ca047560aea,0x985e14e080868ff4110,0xdf3e0642c3dc065bfb09,0x1edcade6010c9faa00cb,0x82ffb4a000346e399901,0x66668bae1123f4028066,0x203337d4e800cc019ffa,0x3377f91489943ff0a7,0x7d89081fe448328461fd,0xabee2a45ef8e2488cd62,0xc230ff8890469ff0008,0x3c81819f67e1608d3e79,0x8f0dfea910400d219f,0xd03850b0c1d02117f14a,0xfd19996b9472a7ccd2fe,0xa599a3b6faa370034d47,0x64c519a589fa1eaab1f,0xcb2280679ce05046ae15,0x46bff100997fc4811734,0x1aa5d144a126bf840,0xe703bd0d0a1ef9e1eddd,0x6242e05e4cc1fb241066,0xce1f0dc81960bfe4d206,0x48581ba41091ae32c69c,0x541931c1f87420bc746c,0xff2690330ffc82011eb8,0x525ec486841f050d0b05,0x7fa49046b0b1fd0a1610,0x670f0ce9065bd97096,0xfa26602fc75065e4fbce,0x84b347d5dc5019e3ad32],#[0x65765a7b90848760f75,0xc114bcbfe08e267efe26,0x544808fbe3e52411e781,0xc7ed000658a76a41957f,0x9749a59100827af48423,0x875c1b042870fe13032,0x6c8ffb31329a0569c50a,0x32dbcbc12123ff882006,0x48497b7e0950bdfe7b00,0x4367dcb028941a25f82c,0x2327e4481979881f540,0xb85290659f19045dfaa0,0xa1fc6822f4611ff8019f,0x35890c2790d5fc880142,0x7e41944e7a81847376ec,0xb4c80ccb9fab00120238,0x7259a50e3f8c6411a3e,0x746851c2cfa6a308c4f9,0x936021638437f4000683,0xa9c0cbda61e0848cfeec,0xeb82353d2dd982121ebe,0x1fa78820067b49820c29,0xf803713447dea0195008,0x98474c0abef05046ae67,0x7bc804cbff1208b89bba,0xbfaa2404779b814cc848,0x5d0adfebe94700ce500c,0x20230474afc06627eb1c,0x6e9e41065df49011a4e3,0x7f9844242f538f22066,0x446deb6142fbe3029b85,0x1d49dfc9508334bd4c08],#[0x3f22064561162843383c,0x157b93d7047a7ec31a12,0x73f7f007012519be431a,0x837c860bff9f05080921,0xe4c4ca0fb88ef42a05f8,0x21240569f934001a513f,0xf2dbea31a14bf2206433,0xdbf54202160bfbe2400c,0xaba1ade4243057f0a832,0x46d2abf423057f0a832,0xb8e6028667f40835f812,0xfdaa30214dd1a1470a8d,0xa1bed419134b735d59a9,0xa05078a81ba1425ff0c0,0xe8fe6602104f9e3408e6,0xd7b8481969e6f1676010,0xb9366090adff86a42033,0x3477f503207cc63d0335,0xd7b0f58c99c3bfc02200,0xaef583b0850e395c045c,0xe05e4cd6ea9009e2143b,0x61419c2b877e89067242,0x2080660afe15065ac3d5,0xeb5008e2727ae08e5f5f,0x3700d2cfee8f4d0abf1,0x5ff206667bf047d4b7e9,0xee54a153f9f510133b42,0x24400a193f34480cd657,0x61f26111bf7e908cbcfb,0xbfa39421021f0bc0a906,0x5e6b3234855f7828234,0x33afd6001197e2044778],#[0x16687cc4024427cfe700,0xba7ae661f58022afc641,0xd920ca9ff1984019923d,0xe46868e109c7b4034572,0x1b12137f904023c30821,0x78a9023ebc9c8c085e7d,0xb831c1797d224001a57e,0xa07a0674697067f767af,0x86ef6b71d4819f893,0xfe714010b7900965fb04,0xe3e04d2173c7135e9995,0xfff2c1163ee7f00cccf8,0x84e7c420424ffc058236,0xfc50067f7c041b3fd480,0x2c31019b5e044a13bfdd,0xf81213c67de9a8003477,0x53ff199947f188804733,0x57ef31a103ff9d560336,0x203377fd40132ee07045,0x8804853c7a908cdf0fe2,0xadee0c8bfed40234f01f,0x8e3ffc90008eb9fc8114,0x9008d0374821378b2b80,0x6424f83257c00032affd,0x4961caec01a9829d25a6,0xa7ec53417acf2806662f,0x9a121bf5f1a01a232e01,0x71fe0500cddaff49d100,0xdef645402140dfea4237,0x230fef7022c17fc9280c,0xfa265449c77424e7fc00,0x80cddfbed64b02684ae3],#[0xcf8d38e3800688fcfc20,0x132f7f5032553f26c066,0x9f8aaca1f040646fd791,0xd5f45128477c9404266,0x1e740067ce9406446582,0x3e140065ee14a7033047,0xd4fa8c085e6dc1b30a18,0xccc3ff4004547fd71a10,0x4242e1bc4811d3e382e9,0x1b17e73c0c600d3067c4,0x20116ba7a060330d05dd,0x8580ff5d09661b02afc,0x4f99b57fc4011adf2104,0x740f166e850f02d728e5,0x7fa759c4123583e0a1a1,0xa0f1608aa17b4cbe1197,0x4cc9e69e5a65ac78e54c,0x42dbe14f810b9df0edc,0x1103c7d110099fdd926c,0x230953e1956426058bae,0x23238ddb2b85afe090f,0x899e5e5a4c524308be2,0xc42d50856fa193bfd79a,0x53630d91bffa85233303,0xabf10672470fac7a1033,0x41153fd0a9a4cd3ef208,0xe408dd5a7f120c99c63c,0x6ef904647d18840854b7,0x84f1660423725f90199,0x308329e3e609b5cd213,0xfe0c08b3f7f1234d2457,0x20428b3fbf6008de143a],#[0x8b9fe849eee0ef468ff0,0xe5f44065d1f08201d249,0x2c69b86559abd61cccbd,0xa0862ff400042f27a6a3,0x2a264b0d95a5ed9032cf,0x5a17e2088a80622f592b,0x383ec904085ac8bd0044,0xf2c7b403357b99fc649b,0xe6050ec492d4de846cc5,0x8b343a28a5e1c305947,0xff120134914b3920cf8e,0x8f187a2c3b1df7b10c3f,0x3e760456346ff12ed236,0x3032ed7d8b45440f0d91,0x5b859976f7fe1e468f49,0x80c1490ee741a40d0fda,0x1b277f1a608682369e32,0x60ebc018c7f0008b49e6,0xed391869ebbe411ade4f,0xdb4bb8574bc30042bbe4,0xa2a78d39860cd7491eb0,0xa940665aeba411b6bec5,0x213bd02445996e10d3b6,0x5c64eef5e6d12169f420,0x8f2021430e5f830239ca,0x5fd0860b4e7e4080cbce,0x2cb5e89a14a238d305b6,0x66ef61c0019836ad6,0xcd238fa84066920be36,0x186c91ffc4100330ff51,0xc3654ff864123189a69b,0xe1088bcd1a48c00d893c],#[0x2917ac95967a8823a30f,0x1ef025a4f30d927f0842,0xcc1e9e62250cf5d6a0c8,0x56b020fc00881c03c2a0,0xb992cb89d4e103f34206,0xbf06483f41107f104403,0x33529f01118863c2246d,0x9fe9d072b19c3ffa7235,0xcc164cf3c50445f2208b,0x8ef8019b5f4101081f8d,0x42798ca1336cca1a11e3,0xe9e1dc4019a760462bd2,0x2473fd211330f4f8c008,0x780158a14d1f4c9a39e1,0x9e61b22bc01063c70446,0x67bfc4d9ab4de8306cf4,0x210232020066034605ee,0x2847464fc64568665ffd,0x4106636ac103fec41ef1,0x2280198689f0022407da,0x3610bc848bd8599460fe,0xa9da38fa4c211b351957,0x1273a1a11b8b5c1acb65,0x80472f04f228033ad741,0x988c1338fc6844dcffe0,0x89d5d7615987e821927,0x8722ccdffd429199b7aa,0xec9336f9f6408da45659,0x876bec5a31efb825efad,0x3c70286692a39fe90899,0x1582c9a01fe283021477,0x2aa044ecdf30c1983f1a],#[0x9d1b40cd9f9031caf142,0x35fb065995ed0c010bde,0xc6a208e8c41d2b25668e,0x3c10033939d9b1bb0a1,0xe8194ff2012adc6111be,0x91ed20642366751c7b70,0x810b58f4206553c89474,0x500a71b43cd16161d320,0x82679f26047429077bf3,0x4420655aff0f22a798ac,0x8822b7ffee82c40b437f,0x81822d09e101f0019d7c,0xa48c9439b33a9129ffc0,0xe9f020810bb5f62d153f,0x9a4bff1a1582c9a24610,0xf830349a0bd7f8dcc264,0x5af3860651dc68458e35,0x11cb8e805acc9fe85986,0x2d1ce006482147fb0f1a,0x2064938c808d9d97072a,0x2435812b6f96f62668f2,0xa34ff42ca133afa803b1,0x2be31008edff8500019,0x9deb088b337a6e18518d,0x4fd1032459a2a31be488,0x132b348f23c411771843,0x19772303e91cf1081093,0xf87d509fbfb35000b268,0x2a3d6be6820cd231844b,0xf8d56173c60d1655e6d3,0x8486ffc34d2333e34,0xa34bcb0655f90008ccf8],#[0x22575a83227eedee1333,0x1fe40251e28672471f84,0x2aef6c6e5242fc23d423,0xbfc29b86559c1c505114,0x9fd6c5085a49687f9991,0x42c4ad63d616716a85,0x6c0d0d0f188008557f51,0xca0a67c2fd5859989a7b,0x40840d5bfa2066cff0e1,0xab1eb81170df1845a7d8,0x6692ad8fec5089e1324c,0x91debe02800cf3d4c288,0x96c49e8dab86dce26134,0x66846d14c9d94485ba24,0x38c92302f9a0685aed4d,0x4646cfd8035050e87ce2,0x82366e7c420424fc88b8,0x65490673fcce0262faae,0x8ceb3f18046afe09025e,0x8454ce9a0654ffe04115,0x279e4f37a1239e12481e,0x1a4661fc310333163ff4,0xf900973f20631a9f38ec,0xc0cbcf83c6142dfd0487,0x1042354b4ab5519db86b,0x5ae5a8810c7f9009771f,0xa00c83d5044ef8a50196,0xa578a11bbfa21164cd9f,0xd96aba0ae3313c598108,0xb10b1cf0904c0cdf1262,0x3a9c183c40b309afd101,0xa1cb56010b1f1f620659],#[0x4183301e30883e0fe411,0x61933280d103c3648ad3,0xaffda440823a1a92be5c,0xa481be82237c07a00067,0x216bfa0540669cf9b1d5,0x58b4772a7e627b716180,0xb91032a8d85c64e92449,0xa14d7800334bc04084ad,0x8c3659e28222bf600010,0x72224c2c37d3640cd14d,0xc49ec50a0ff141810a4c,0x640823a1a97e11ea11b1,0x523e408ebd62845affd8,0x50b8dcc164cc318e8451,0x808c177e26651ddfc6f9,0xcc89dbf4ab94ce3e5af,0xa3c80850ccf800084afc,0xe47c008d1c6bf06cb373,0x725ea9967f1e20d2a903,0x8cf5e7204066ae7a0323,0x7e7c0821450d9cc6b896,0x7f1c54b00671fba5f454,0xa841997e3e1061d21016,0x8109de201e2c0ced2fc,0xd800851fda8866921df8,0xb2f010210b9e03596dcd,0x3ef860a078c21c1e30e8,0xdc5c30a22cf0f5881094,0x11019a05f439e23e408,0x1665f8d044b0b920cbfc,0xc0460bdf8811a3bdbe31,0x3c0190bfd8111665fc41],#[0xd9f853f819997fe0111b,0x23a19a3fe4440cb7d504,0xc5e850f4c9e8c485c2fc,0xfc0134fc4c074601bea4,0x39d9de411c478f722dfd,0xc90198f8237b01aa2cd8,0x230222d2bd81d0a346dc,0xa8ebffc1182b19e3bfc1,0x142c2864fe08019768da,0x8118af49078e9b2647ec,0x27d37a159672af20649d,0xa10646c3b4c93d77c823,0xb3b6715e91f4e3cd22c7,0x10f9c5645243bf998810,0x807e10006753d9c67292,0xea0088b44f42e33c4915,0x4917e08ef3fd40270fdb,0xf928608ea0176fd9f2b3,0xcb17ff90456e7d801967,0xcef6039fe60117ba7080,0x215b5ae33066ced85194,0x8d0893fa08046b7aaa91,0x6528914c236f0992651f,0x56903297d57411b36f48,0xf24106637e412892868f,0x8432851d7e950cd23865,0x99c68eae86121bad8a7f,0x8091df260642fafcc28c,0x1181166f00228f9faa55,0xd01dff98c0a1ab0c9917,0x98479e30875fc4082182,0x3aa0084f7fe041cfec85],#[0x7f8d6d0ccd59661c8b35,0xdff0c28c99b5007e6c27,0x5ac43465e5e1019a9847,0x1a55197b883a5245369b,0xa14bd0a2c9dd5281944f,0xb800334a91845a79a0f2,0x800868b71ef3b659dbdb,0xc426149a9d2f84b7d999,0x3f800453ff14136bf8]]
set_option maxRecDepth 32000 in
def g223H8 := limbs80 #[#[0x128028aa042188288218,0x804842102419048429,0x262100a01842a02066a4,0x20452828806549120a59,0x62468182228018816081,0x62859162a86490641151,0x60011400050a84802644,0x58004950492520064000,0x60941010a94182261020,0xaa025446881109805861,0x21881160458000906494,0x120548000202560051a8,0x180088a80400194aa,0x1a9698840a049882a800,0x2080141880244a918608,0x24480828908195906085,0x5002a5882282a008001,0x9925a01000a82520489,0x24281022a22020262802,0x40200540060262521201,0x24880021091261846489,0x50888210014006a48a18,0x21a299650a51209142,0x854a28a081a051aa8861,0x42220962040921985260,0x1509084005989908110a,0x81014551400940000100,0x6608a615880406151101,0x5448044a14062a840918,0xa21a8098648292015258,0x40464189995a55228584,0x28228109124856865414],#[0x466289120a2200889,0x415821502844058902a9,0x220825040244a4086424,0x29621a88656900990956,0x16625621269844982056,0x11190a64692400281108,0x24521a25006422481102,0x816248402004452881a,0x10a6006a296808400980,0x99a6221a010602a82218,0x1454801860a12a512501,0x4428941444101484041a,0x6290846554a846155881,0x496045a2a89810980a00,0xa614690498848590442a,0x842a6406a2811214a00,0x94501940169620428894,0x168429582a25210a490,0x81084010185409210080,0x9806a08804124524889a,0x29202016826000910181,0x410a1154802028028a49,0x21284418208409522156,0x4205a9861401108088a9,0x5182200a01401a05590,0x8062626010408645a86,0x806a4a908616508561a9,0x94020a009118481a08a0,0xaa05905122280a8a59a1,0x6241416420506510a52,0x86284040a16a2854124,0xa410120561a812928114],#[0x61450020421a8151aa,0x609015a8848a14591a5,0x52698218080a01205091,0x1050298619846285a808,0x94146a52800a28965981,0x8499468892a692010015,0x58928159a202080a1108,0x506800906a404006899,0x281540822850591a4559,0x2206460894890022a198,0x6024024826502182a686,0x21a6684a921084928005,0x40510829110a216a12a2,0x5635840024920661040,0x682b818990e430ce913e,0x904ed84b2c838db4b0ac,0x330bc3c19c40897a653b,0xd9022404f23f28034193,0x49d913fcec066c4c0737,0x7883f96231c090bd1391,0xb83405782460b9892c1,0xd9e097264540280127d5,0x984b2027e485830e33ae,0x35f366ae18c0dd8548f4,0x43c523dc84575a3e5c0b,0x94ac88973146f55444a,0x42e04d2ac938a06f1403,0x6252f6b5b342904191bc,0x6490ba138270f102c624,0x49ca7867981423e4a03b,0x1bca4210148c332980c0,0xb26683c30b5f088d5808],#[0x618a0872f7d706906ba1,0x1e2b1378655cce74c57f,0x856ac172080c04764240,0x2b92a93805240e6749c4,0xa08192bcec78018890a3,0x5882a08944df80383120,0x4e6208878b0b10681010,0xfc5e68219b24e2231884,0x4a3d00134a4051d16487,0x6408ceb72331b9691da0,0x52d99f6d07289c5a2874,0x318c6a024c69b690442,0x75bdd020294c04498ff8,0x43f17125743b18a62b97,0xa1044c100c327118a8b4,0x217cc806087a45e22e05,0xc96310baa82759c0aa0c,0x258006400a198029e4ca,0x691cb792e4c41ffd6129,0xe4060d63be55a011865e,0x200421821240d7ca9d34,0x16000014440000101100,0x209090400200a000a51,0x4221010000001644278,0x1454160c080240004,0x10100002409202a010,0xa400020200000003608,0x10054800004e080603e0,0xf0005800180140768043,0x5c911014012000003004,0x66182080c4012008200,0x20712280002380020008],#[0x8007ad04800004084062,0x40860a042021200000,0xa02308e4000430002a00,0x8002096410d8022c000,0x11080a5260042241e8,0x40e20110b30080000008,0x195404000b80a0120110,0x9092220800c598648104,0xe4050900020d51104405,0x130000000f00e3408085,0x880000f829800f100011,0xa100000080800fa2184,0xa00890a0019404109000,0x9029128000000010ee0,0x501000100010529111d0,0x4040400000b04322125,0x3b5600000a4200041513,0x147002a0201850034511,0x11551064709100d30060,0x1166300120020024020,0x10516f40a06c81290204,0xc10017e40000c0610a00,0x9088189444100c18b08,0x8b090019882700000042,0xc082001a30008400016,0x95048801ae0029c9002,0x4b9406001ba12000022,0x18a322cc801c50004204,0x2a08404201d1150048,0x4040002618101e300480,0x4c04b001200221ec8480,0xe00098549008401f70c2],#[0x41921028200040820510,0x8808a08000002a002136,0x90000000420201562220,0xfbffbd7fffffff7f22,0x3bf7ffb7ffffffd7ff0,0xb076ef7fffffdfffbfbf,0xff0b1bd5ffffff7f777f,0xfff0e8fffffeffffdfff,0xffef126dffffffbffebf,0xefefd162f7eff7fdffff,0xfede5f19dffffdeffeff,0xfffedff1d7ffbfdfbfff,0xffffe7fb20fdfddff7ef,0xdf3ef9bbf248feffbffe,0xf97fffb77f282fffbffb,0xff7fefdbfed2b8dfffff,0xfbfffbefffff2f1cfff7,0xfffffffffff7d328e7f7,0x9ffffeffffffff362fff,0xbffbfffefefbfef3a0fb,0xdfffbfb7fbf7ffff3dc7,0xffbfffbfffff7fefb415,0x8af7ffedffffffffff44,0x4c73ff79ffffffdff7f4,0x7500fffffffffffffeed,0xfe53dffffafe7d67fbe7,0xfff571fffff3ffffffff,0xeab75aeff7fbffbfffbf,0xddd7f5eafbffffffddf3,0xf7fdfb620ffffff7ffbf,0xffffdff65ab7fefbff6f,0x7effbfd7691dfffffffb],#[0xf7dfffbde6ceffffffff,0xffffff7ff5709fffffff,0xfffbffffbff744ffff7f,0xdf7ffffffffb780fffef,0xe7fefb7fbafff7bdffdf,0xffdfffefff9fdf7f9f7f,0xffbfffffffffffb830bf,0xdfbff7fffdbffaff86af,0x10003ef7be7fffeaf8a8,0xb00000000000000008e,0x90b00000000000000009,0x90b0000000000000000,0x90b000000000000000,0x90b00000000000000,0x90b0000000000000,0x90b000000000000,0x90b00000000000,0xfffffff90b0000000000,0xffffffff000fffffffdf,0xff7ffffff03ffffffffb,0x7fffffffff07ebffffff,0xbc000000,0xe300000,0xe30000,0xe3000,0xe300,0xe30,0x300000000000000000e3,0xe300000000000000000e,0xe3a8000081500000000,0x10ea309200c401041a39,0xea0fb124103a04280122],#[0x93010a11a8e4924c8014,0x6401216006013010a0a,0x5a1413190432450d8a4,0x2881144514c3290958,0xfc4054315a02652e0c88,0x4e10821016b032084324,0x4a003913618060404841,0x18011044d18f4800a00,0x18a4108a0e119f83c11d,0x1008058108081b243160,0x8000600080b21c5e6a2,0x61c1aed08222011d5ccc,0x124221c080040cc1e300,0x20039000030e05061f60,0x2281b01a74a0e015c204,0x291a0c0d8084806c0021,0x2391f6100290022c7a22,0x24e8002031014900001,0x882580501d118012c520,0x102268ba28a4200c295c,0xb22227e400804541009c,0x8b81028b18880374440c,0x84462029f640a5414404,0x10010002b19041b01423,0x801388942c32040c204a,0x8200867a02cd56800432,0x40600a00032df9005009,0x2ac040490032ef084086,0x2000292ca622fb08000,0x4c105250e44003079227,0xc040484416108431a82a,0x894249c932c38],#[0x59c0a87ea4820ce333c0,0x8bfcb5f60ec4987d6cf4,0x9dcb6e49ebeddbbf0b46,0x1ab99ed822e68dd6f1ac,0xe42977d85e6ce58f78eb,0x86c7db7d939c21e07b7a,0xdd43d3ea44a0ad05ef6b,0xd2ed2fb1a80785dba68e,0x6eddebbbb42a5cbedb3e,0xab51868e1085ab13dc7c,0xdd9a33f84d27e67f46da,0xa181fd8f87ff75d39f0e,0x1b7cbe38daf54b84ee5b,0xb74b47c7eafda5daafe9,0x48db78dc9e5abbf0bc61,0xfea18e6aa3d5297de3c8,0x959ad1a749ebc3bda493,0xb2d55f09abcc4c920f13,0xbf01a02b53dd1cb09828,0x862d42e7cbdfaa6bd28a,0x9cb52992ba5828b3584c,0x3bc4b4f9a09dff3e9a29,0xc01cf48f6a86990d22bd,0x6ce30bd9a67ae28389ba,0xde1ff4aa3c805ed6ed5f,0xf70b6dcac8aca96d30b2,0xade05e16a5ee19a21c30,0x98a4c36f1db4e826ce9e,0xaea98dd3ceca835911b8,0x12d3fdbaea0a6f98b974,0x3e4ae02bcdbf1cddaf3c,0xaccb56c938fce74a91a1],#[0x87b63aa9d11d0ec8d8b9,0x7b5c94ef03f298ceb93d,0x84f80493388880f9efb9,0xbaf3dca5ba4adaee3b01,0x284dc06aa2a1690cef28,0xed2e89f19b92eb5ca4a2,0x2c86fc2ea9f866927ded,0x8e0abffc2dbddaa5c238,0xa14aa188ecd8c10839ee,0x20a69c4faa4a7bd9da1f,0x2d1eac8e4b8fdba9831f,0x923e9b8b3b7291e986ec,0x3bcf1a8f997ca2881b0f,0x58feeb8922bceec7a32b,0xb32f26e9dafbd769c790,0xd7a38e39945cb3b3c92d,0x983fab3bd5ae9e7fd4fa,0xf33f5d8c5e5398aed1eb,0x12ee2f6f8a3b2cb4ccb4,0xaab7cd0bf7ae5caec1ce,0x941d06c6c9b1a17dda93,0xade14e0fa24b82b67c57,0x1f4c932a53af5a99887b,0xf8282a882bc5f769e1a3,0xcd1486bdeba0ed00de4,0xe865a9dcbad8285cc5ef,0xbc2d89d9692fdaeb21b9,0xebfdb6b858a3fc8ada9,0x4e979ee876a75a6a8cf9,0xbfe9fa999b7b87ec18e5,0xa7a63f48a068a0d7a8c6,0x6d0b8cadeeb5fb8db009],#[0xad3e41b66d72a26ef794,0x2bdb0c0eb6f8f5b58c34,0xcd98d02bfb80dd56921e,0xd69db8943ca0f1084e93,0x93f2acc1d13ce5978903,0xcf0da0ff05ebfd598858,0xdc8db4f4fc81eb3b949e,0x73e51abfec6e5cd66b7e,0x5d10d86a84821a29eae8,0xb79e6ba6bcc9e3a915d6,0x9bcd582ff3a878cbde31,0x3e2d8e5993b6ead0d2ab,0x802b169a48f9e8ce3fef,0xdcf1cdf28c7c14efd9c3,0x3af68ade099caf44e03a,0xa4f94dac3a81ed8d03de,0x3ee81f85f7de88aa8a46,0xd9fde52c82caada2c518,0xb95a8ae5ebef811c9ea1,0xfcb5acda980a55b15842,0x7d60cc7e5bdb2ac4f49e,0xc04e8de1ca418efd7df5,0xa6e929feccfa42e57a93,0x5872e8f9dea2bc6ddc1e,0xb50c16d50a61f89cd9df,0x2bd4dea2867895bc8cce,0xe9b68f4b99a6db2fd48f,0xc0fac9aba8b796baf9c3,0x9af]]
set_option maxRecDepth 32000 in
def g223D9 := limbs80 #[#[0x55152545505013048110,0xd5351d42655956458560,0xf7efefeff7b7fbedef62,0x74806e8135913ffff7f7,0x374306ea11dc4e1b8181,0x8d65482eb005c201b984,0x85d721c2a20754424b83,0x992560212ec27d886fa8,0xbb3e354496e0a45954ba,0x2a8021616bec42559484,0x10aa259541c2c2225d45,0x8b03aa5f54096eaa84c4,0xc805b8ae5501baa44754,0x55024b8b1f62292ea374,0x8584a4bb0cb705bec447,0xd25cdafb1019431aaa64,0x6425d40cb20df530aaca,0xe272dd885bb14974696e,0xec4e25d050b091d54846,0x12ec02dd86eaa19d4213,0x63aa6125d18eb911d521,0x4846ea985d530b0b8970,0x75196e05754805b8a1f5,0xb75442e89750c31b824b,0x1d426c4c24458d1130b4,0x2d964396ea9599485b98,0x29c973016e092dcc65ba,0xb00dd42212ec525c5ab3,0xea90cb76396ec025d9b2,0xf0b0809707c4c225594e,0x8913aa4b74422ca825d8,0xc0f2b008b71246e8925d],#[0xdcd10b824976716ea02d,0x7d89a5ba111654aacaf2,0x7ad5052a80a1611bae47,0x24a9d554aa0a974452ec,0xea8a54c15bb12b73252e,0x6e24a54c74aa12976254,0x52c64a54494b2929715d,0x252eaaa9d474baa29630,0x1254ca2a591b4b82e974,0x653d6a28a5c154aa2296,0x951452c22a59054a9929,0xe965052ec3a594b5328e,0x12965152e64adc574ba8,0xa2e971452e63a58c75ba,0xb28eb531d2e07add174b,0x5b82eb51152a22ad5114,0x421008900052c84a58db,0x320f0e386362ad110864,0xd8e8a6b6314969ca464a,0xee53827c92d08de4271e,0x7a5acacf463a2fd56e8a,0xef8273f41ec0eda7303,0x515e7a933594f48122ef,0xf79bb845a16bff56ca74,0x658c9406484a00629701,0x67e9007194a80637a740,0x9a9004d625805a767c06,0x7806e8e9005b7880071,0xb8062788005f88a40637,0x40739c900516e4c06c9c,0x688488066766406f98c,0x6a9ea805a8084069969c],#[0x97868067868005e768c0,0x64540586c58055628805,0x6c0689c9c055766c058,0x9c07ea29805a767c04c7,0x40708c8c06a886c06084,0x5b6c6807caa9807098c,0x7a8c80059888c06f9478,0x79c7c066704806b84880,0x80b4072968405b686007,0x9716928f84370e970589,0x628482023312898e5213,0x8a1a16571d0894766c18,0x2082187145a4a0e8a39,0x142679063e1c050a8607,0x4f36d210644c2e903532,0x27391846b8983c308068,0x23dba8809054720ab451,0xbb48d14f8413281f5489,0x1980b2afa8e1011c7ac6,0xaac8170ba22c7c0a454e,0x1f751011e3e0a0996b9e,0xefc020099cff35974285,0x315b87022669f1800460,0x1f09a7e39a091a710062,0x3e8088471fd49540915b,0x8c567204f7bf4409e6,0x6a71157f0067a4069f83,0x238ff022008e7e7904a8,0x2839d3bbe414cf8da2c,0xefc422ef9040463fe85c,0xc0a6710062313e8813a9,0x844791f8012473cfce24],#[0x44701b7e21680240f07a,0x8c6a2473afa0203e9066,0xef004247befc18138dff,0x14d6b70273e3e44a3f,0xee45e09e7e120118f4ce,0xce7f8e682479e3d6d411,0xd7f5c00513ff81018824,0xf2018fe9f8013ce30588,0x10133d6f00e7f486f050,0x3b400338f1ab08239fff,0xf8c0011eb6e0104ccdcb,0xe7c6251cefc08828254c,0x365fc8291a7f3dc2231,0x1c6211217f8010467bf2,0xff20808c391ac048fbfb,0x4e7f9baa6141ee52c938,0x11d7e7e0c023dfb3cc0,0xcbba543df80291567e41,0xf5d80fb1ac011abc6008,0x9fcc0042338fe07c0231,0x904d5a7709a79f63008e,0x467f7006198ac708d7de,0xe20a27fe118236fd7b84,0xf70cc050bf804011ccfa,0xd88023967dc0efa780c7,0xf1fe90801983e0c0c9ba,0x7ff7009182035e7c9804,0xff220455f401cf5e1099,0x63aff8009207f5880469,0x35974283f7a4131e901e,0x827bdc404fbbd04118ff,0x7c0a0019aee9c253bcc9],#[0x66feecc0a2fddd78014c,0xeb204fbad7022bf6b00f,0x10d00ccf480c1f060648,0x263ce2027ba48f84e9f,0x6a61230f1982823dff81,0x3000490d3ee4044cf3fc,0xbc38299f1c1108d042fe,0x2a34e0709ef71013dbeb,0x400245c93026b7d77438,0xd0411cdbf6998295e3f1,0xcae208475f51c608d3a3,0xf2ec6705669be1f0015c,0xb98c26dfb6a92e4825d8,0xd3ff70014dbff828145,0xbc7dedc42ca777fc60a,0xf32b85411e7d2ce10241,0xd626014dc98813d6b204,0x8ee3c82739bd0ed02abf,0x87ffe800a297ddfe620a,0x828384e520531f881c14,0xf7b48660acf480f1f303,0x51e76729053667290504,0x277f7003effd74880282,0x4120f6f480a2f99e04,0x88484701975f4046fcc6,0x827a5f67f2620af67768,0xe965b04a385d08514e13,0x9830275f6b8084240e67,0x55e82a2ebec087d3c06b,0x551f3038287b70045bf7,0x22df5de1c14d3389f870,0x490bcfbdf10aa6797601],#[0x79987a41]]
set_option maxRecDepth 32000 in
def g223H9 := limbs80 #[#[0x104491842251450018,0x448a10688a0108861014,0x18a2504a049a00084595,0x6960018200851880a052,0x850942628a858a4082,0xa84500899500444902,0x1219a40482a8a0816a14,0x2111424619045085044,0x40081204296010806028,0x221420a164082620890,0xa4a4404a084040840806,0x10154a40012a0919486,0x1424548025a400a61809,0x59996115064240448898,0x51a95928a1422494108a,0x59200122541218484195,0x45066999666054084548,0x9400062aa65a04480201,0x59064805145411480194,0x800591860a1486941229,0x66010042090412848954,0x4220914884a86188a26a,0x2094048845954219159,0x80144612581265129581,0x59a02098910210921090,0x2502012005aa486a5650,0xa1215a15895180110940,0x8089499604486549052,0x2a9a05215a1409680a82,0x468609964091068a041,0x20280a6241a221818024,0x9000161a45856a868508],#[0x282a4a01624980498201,0x8905168a214801510141,0x91280080158045a12422,0x45a496192822212162a2,0xa0082810004552948188,0xa966221991a16128402,0x4002a002489454042541,0x92804819059a80a491a,0x286224416a405415500,0x49c2a870248492222241,0xd0d0a82fea3e39f0cc65,0x842819a98653061506a6,0x5068748771447cb42009,0xf539e9a0c9f201623590,0xe13907920148b6a9f2c8,0x2a8b38a03a41e97c18cd,0x437524eead1df0d222a1,0xcb248240c011c082c89,0x881e806d000d937032e8,0x101000e8e288386d0221,0x99114764d9b10a0201fe,0x78f414e0880494ae0c04,0x26efb09c18200084508,0x405e2620b682c80aeb1c,0x6b59cb14422ef821ac4e,0xc911903f040412c80f36,0x81809927c90411875a6e,0xb5ecac3929132441899b,0x9b2b4c63e48ca9641205,0x88a0c32700eb1d630124,0x860100008186104233,0x1200080aa00882000000],#[0x80044042028210830102,0xf99045084005aa710013,0xc502648120128060000,0x407d0ac0262058020042,0x4d10002043045c484,0x4002d83801800050004,0x4818c045000800100,0x20d010d205102422004,0x100d000730080400000,0x5509100003d40000e084,0x8820a00182121130800,0xa02a404001221040c0,0x1801002000909c61001,0xa8200121041a2c53a028,0x40102880a2062002c008,0x408c0001020300017f9,0xa93842002040881110cd,0x38a04090041309050386,0x1e200028f0c01009908,0x100ff8134004440000aa,0x10048580804010004428,0x3000a44f050080212088,0xedcf3f23e28050888430,0xcf0b6ec80096a5fff709,0xfae8cec7c15e3ebffef3,0x774a0827c215f77243de,0x877377699550ff41baa3,0x1affcbfffe2709cf9f3d,0xc6327fe46ef6f8623fae,0xd3b773874dc5dbe3cbb4,0x7e760b6f63fbad152353,0x4cd5156fe4e1567e7942],#[0x6389d7fa8d8bdf7f2b8b,0xd36e3fcd2a7b45127476,0x369d9f177681d24ba79f,0x51fcff3b51a0262fd3ed,0x8bbfe883dda9d735c1bb,0x29fadd490f798a1d13fb,0xf3bbefaa70de4e9e267f,0xf7b5fbfb14c78d8979cf,0xd4769054a0b0c27ddd4b,0x3dbdbee7dbd5ddd3c17c,0xfee0b0ccd37a,0x19c0000,0xd0c00,0x6860,0x18000000000000000343,0x3fffbdfff37ffcbb9a,0xb06d9dfffeedff6df7fe,0xff86cf7fefef7f17fbff,0xfffc517bfedfafffd95f,0x73bfc363efdfedbfffdf,0xbfffff225feeafbfedff,0xfffffff146fff7ff7f7f,0x3d34c17dfff5bff,0x6f40000000,0x38a000000,0x1c500000,0xe28000,0xd4a03686090188071440,0x98c3387b27887df038c5,0xd07ce7de9c1a509471da,0x868a11e4b43d866c988f,0xa46c493f00050869827c],#[0xdaa4de16f49c90ab0775,0x40d93690028240906521,0x1989ca039684529925da,0xfcc65380b94813ad18,0x183a10eab54d3e893709,0x8d8740255690c896ca02,0x333485b89aba70eb0348,0xc9b7fee34c160405682f,0x3ab616573b21d46adf99,0xebb7dc7e2385e42d08d9,0xd0fd3a9d5b32846bb694,0xed0c8da5a33c55ce9b9e,0x2d575e2527f28c32c343,0x5d132fd47bf736f6fcf4,0x4fb74d74de5e3e0ac1bd,0x6e87b6cd15364afd1d07,0xb766c1373a7e5c4d7754,0xd2b19ad3c64e0e173a6a,0xafdbc2d4f65cf136f177,0xba7f42effc4f7abaffc8,0x8e78ff3f79aca0e71bf0,0x23f36d535271bd26d1dd,0xce4a7329f0755e8d16c2,0xec83a9a9647d853f9272,0xe17be116028bb2aa885b,0x357ea667b3db733e754c,0x3ba635a0f12f53e629cf,0x9e949d564f6add3e0302,0x5ca8fd0f9cdf09f70023,0xc29bee896fdd6f437a9f,0x1bd205d46af733a1bd43,0xf2284b98351f305ed697],#[0xeea1b1fc7b57e0fa015,0xf7bc5532ec44e3923ebb,0x590d48e2ffdda9f882c0,0x95d6b2a4f097d9aa4e71,0xcfb30de1e95eaef3fa9a,0xebef83e659d69756aaff,0xad94c45b93b6798c5943,0x47aa715ae54e1b37596b,0xa2f5e7465b5f9f75ee4e,0xb2825d64cf13c6a54e43,0xfac0738c0fde3cedcfde,0xd2d54b47f02a472fe191,0xe82a558eb2e44df4b1d2,0xef2d3a2a8677eeb0626c,0x111ff4c53ba43e03d14e,0x77f0068985144e3d6c6d,0xb0d51a8bdf6b94e7a951,0x8fcb95f29a16edaed75c,0x49af523a3be80fcdebf2,0xc2ddce7ffeaa539feb84,0x7b1fa74f6e454f7054b5,0x63095c5f75147b44a5a5,0x7d58d3bba59d83fed3]]
def g223D10 := limbs80 #[#[0x52142661561120fffdfb,0xb509509409309103621,0x964b54954961b5195196,0xcc24a1a0982200a65965,0xcd647057535d8aaa481d,0x8b8426044da6970d74aa,0x314004038a6c082971c3,0xb8118a95a30e04766471,0xfa2067f18144053f2032,0x87f0e41df4b010792123,0xea227070101c03bfc580,0xfde0042a00e5fd001407,0xf000275401cff500143f,0xe801d0035f]]
def g223H10 := limbs80 #[#[0xa20040a1582a4408a060,0xa5126aa00482248545,0xaa52a854248a01018288,0x5400140055860a112211,0x28024200504085a6684,0x26568200280825245240,0x22a181010200a2858044,0x82084260290410268008,0x8c5c425e5c8a528805aa,0x6c7d951da6292759b84,0xf2aed59249d8cf018200,0x14484504012633f40988,0x62004280108368ad108,0x4241000000040400,0x9b0000343e0984090800,0x10c00130320411081c16,0x7a00082c832d01353888,0x4300000000000005001,0x510012f3450ecab1a6e6,0xf16207db050f98a63548,0x8dfb371c8306b6655ba2,0x1b856e8a37bb5af,0xfe00000000,0xfffef7fffdfa10000000,0xbbffffbfebfff005fffb,0x1e3beff,0x7982c6eb64f9ee000ea0,0x4c5d99e54f5d3961991e,0x6cbb0000000000001f07,0x521b96cf52a7f159acb6,0xdc2f4f6e9be02cd5cc66,0x1dc48af1b0ad60b7918c],#[0x52e87d4e4b74a2d26675,0xb4d93b0e3f2b29b8dae3,0x5ee596fdec42b3a09c6d,0xce60eafb7daca2a11e86,0x2f846ef3f77aa6422703,0x68755]]
def g223D11 (j : Nat) := if j=0 then 0x162043802ff else 0
def g223H11 := limbs80 #[#[0x501000026a80009c41c0,0x792c691034a8c420000c,0xf50c000eb00cd00e0004,0x29006a009309000048c,0x4008b4e000]]
def g223L : Nat → Packing
  | 5 => (70,6,6,2359356,102,10,1032,g223D5)
  | 6 => (1001,5,6,11600447,138,33070,1173,g223D6)
  | 7 => (1933,4,6,10617471,138,16720,1284,g223D7)
  | 8 => (1016,3,6,4063391,104,8496,1192,g223D8)
  | 9 => (190,2,6,720913,69,4333,1100,g223D9)
  | 10 => (20,1,6,196609,32,9,1050,g223D10)
  | 11 => (1,0,6,0,0,0,0,g223D11)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 6 => indexWave 36 1 7 608 7 1 [(324,81),(466,97)] #[(0,0),(97,0),(70,0)] g223H6
  | 7 => indexWave 527 2 11 8493 10 1 [(4743,1001),(6618,299)] #[(0,0),(299,11),(11,0),(1289,0)] g223H7
  | 8 => indexWave 1036 3 12 20496 11 1 [(9324,2546),(13048,793),(16772,2268)] #[(0,0),(2268,4),(566,231),(2495,0),(4,0)] g223H8
  | 9 => indexWave 554 3 11 10836 10 1 [(4986,1361),(6936,827),(8886,864)] #[(0,0),(864,73),(374,526),(1317,0),(73,0)] g223H9
  | 10 => indexWave 111 3 9 2313 8 1 [(999,264),(1437,201),(1875,138)] #[(0,0),(138,11),(80,132),(259,0),(11,0)] g223H10
  | 11 => lookupShort 6 41 6 8 5 1 g223H11
  | _ => fun _ => none
def g223 : Forest := ⟨223,11,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sample223 : block g223 8 526 32=true := by
  apply groupBlock 526 [(32,9,3)]
  simp only [groupProof,cells,boxes,and_true]
  repeat' apply And.intro
  all_goals decide +kernel

def g255Y := selectedPanel 98 (limbs80 #[#[0x10180426991b37f3d46,0xa2004c34b100f978,0x2664ff9ca25060a00400,0x7a72097028082490089b,0xd9a2262012c000280811,0x1000e0315c40873a1cb,0x1804571001ce872f2404,0x604707c3e75174e1e400,0x1b0c9044c007a24704c2,0x16f000d409009108011c,0x802780703807807fc0,0x940140801e00e8004b40,0xfc007ff8000181804d80,0xd7e00004040070438007,0x606211c10a001fb000,0x3f807c0007ffff80000,0x1c0010af7d0014000000,0xf8000000000038081590,0x7fff,0xa02034ba6000]])
def g255C : List ColumnInfo := [(32,0,223,0,12),(1,0,254,0,11),(2,0,253,0,11),(4,0,251,0,11),(8,0,247,0,11),(16,0,239,0,11),(128,0,127,0,11),(0,4,91,160,10),(10,0,245,0,10),(18,0,237,0,10),(64,0,191,0,10),(3,0,252,0,9),(6,0,249,0,9),(9,0,246,0,9),(12,0,243,0,9),(17,0,238,0,9),(20,0,235,0,9),(32,4,91,128,9),(33,0,222,0,9),(66,0,189,0,9),(68,0,187,0,9),(80,0,175,0,9),(128,4,91,32,9),(132,0,123,0,9),(0,2,141,112,8),(5,0,250,0,8),(11,0,244,0,8),(19,0,236,0,8),(24,0,231,0,8),(65,0,190,0,8),(96,0,159,0,8),(129,0,126,0,8),(130,0,125,0,8),(136,0,119,0,8),(144,0,111,0,8),(0,8,54,193,7),(0,16,45,194,7),(1,4,90,160,7),(4,2,137,112,7),(8,4,83,160,7),(16,2,141,96,7),(16,4,75,160,7),(26,0,229,0,7),(64,2,141,48,7),(72,0,183,0,7),(82,0,173,0,7),(84,0,171,0,7),(137,0,118,0,7),(146,0,109,0,7),(192,0,63,0,7),(1,8,54,192,6),(2,16,45,192,6),(9,4,82,160,6),(13,0,242,0,6),(20,2,137,96,6),(21,0,234,0,6),(25,0,230,0,6),(28,0,227,0,6),(64,8,54,129,6),(64,16,45,130,6),(67,0,188,0,6),(68,2,137,48,6),(73,0,182,0,6),(74,0,181,0,6),(76,0,179,0,6),(80,2,141,32,6),(81,0,174,0,6),(88,0,167,0,6),(128,8,54,65,6),(128,16,45,66,6),(65,8,54,128,5),(75,0,180,0,5),(84,2,137,32,5),(89,0,166,0,5),(92,0,163,0,5),(129,8,54,64,5),(130,16,45,64,5),(138,0,117,0,5),(145,0,110,0,5),(152,0,103,0,5),(162,4,89,0,5),(192,8,54,1,5),(192,16,45,2,5),(200,0,55,0,5),(208,0,47,0,5),(153,0,102,0,4),(154,0,101,0,4),(193,0,54,0,4),(193,8,54,0,4),(194,0,45,0,4),(194,16,45,0,4),(201,0,54,0,4),(210,0,45,0,4),(212,0,43,0,4)]
def g255A : List (List Nat) := [[]]
def g255D6 := limbs80 #[#[0xca176e53b068f645c520,0x1c]]
set_option maxRecDepth 32000 in
def g255D7 := limbs80 #[#[0x5d143481965d97350d20,0x481765cf9058d2065976,0xe8d74591206cd765d164,0x5c120ecda958570481b0,0xecda758d70483b35d963,0x65970483a3685965c120,0x481b169f615c1206c7a3,0x5d1435c520e516350d71,0x5c5206997650d71481a6,0xecd7658d71481ba5d163,0x58d71483a4e51635c520,0x48176e81635c5205d3a0,0xe81635c520653a058d71,0x5c520e53a058d7148196,0x6cda759171481b35d964,0xd9171483b068d765c520,0x483b068f645c520e51a3,0x68f645cd20659a0e4d71,0x581305d1635c5604c3b0,0x6a5635c5604c1a658d71,0x5d1644c1b35d97158130,0x4c1b85d974591306c176,0x5d9645c5306c17658d71,0x5c5306e176591714c1b0,0x6a1a45d9714c1a368176,0xd91714c1a8e59765c530,0x4c39468f645c530e51a0,0x5d971581405db94d9171,0x5c5406c1765cd63501b3,0x6c17659171501b05d963,0x5d971500b3681765c540,0x581b461d7358d60ecda0],#[0x69d635c160ec1875cd63,0x5c160ecd76e0d70583b3,0xe538350d71583b35db93,0x5d971581a468d765c560,0x583b35db835c56068fa0,0x6879061d60e51a3e1171,0x50d716c7a0e4d8758393,0xe8da05d9635c78458f90,0x5d9645c5b0e538458d71,0x5c5b05d984591716c3a4,0xe91965d1716c3a465d64,0x5d9716c1a5219765c5b0,0x690a3641765c5b0aa486,0x641765c7a3645905d971,0x5c486e8d905d971e8da1,0xe8d905d971693a364176,0x5d9716d3a3641765c5b1,0xe1ba064d765c5b8e8d90,0x64f645c7b068d7660171,0x5c5b05db84d9171e13a0,0x68176e11716c197e1364,0x61f616c3a45db845c7b3,0x658dd63658cd7a364590,0xdac56a759d96725979a5,0xace2b36acd6b34ac96b1,0xf8ab78adcab68ad96b3c,0x96d36b4cad2db4aabe8a,0x6f2abc96e36b8d6e27b5,0x32ac79afa4bce2f32bcc,0x78cd9733ccce3335cccb,0x6d8f353cd4b73e8cf8b3,0xe4b78e5dce3734dcb372],#[0xcd3b2ceca7b25e8b79e8,0x93d32f497b68ed93b38e,0x281f870ff24fc87e25f8,0x803405972942ec68438b,0xf871132ec7053892877,0x312aec105b812a130874,0x80002f8704b780048f80,0x9368b91f8878078718c7,0x80cb88d9c2ecec878931,0x88098b68b5ff88299b68,0x7b813dd2ec649f805e0b,0xea2986bc678d2cbf9348,0xed4493881ce786a0e388,0x2768f0878939d2ec41b2,0xd5870d409f8038d7874d,0x88cdaf69587f80e0eb88,0x7f2d403787561aecdceb,0xbc3f869cdf8688ef80c9,0x93158b6684a788262f86,0x22ec2e2f487503883c4b,0x914b68e5eaec54e78696,0x800dcaeca95769219b66,0xbf886d9366bcf78708ff,0x513f6d25eb8849676821,0x971d178059f348c0af88,0x576925f348c55b486017,0xfde72c99eaec4d9368b1,0xecf9c350ad6f28686388,0x6b88d1daeca4678d3202,0xf572ed00678d391f887c,0x2c60378710f787482788,0x574950878755676815a7],#[0x450b8818678d359b688d,0x8ce0d2001ef2c49ff28,0x9767cb7d432203ac618a,0x4e53f6cacd0f01105f7b,0x5212016a8c170bd31801,0x828406080801869c172c,0x801220385674a8800f5,0x25474a880109b2e4c788,0x1464bc64a9113017a23,0xa74a8d014244070c0e0d,0x2e1bb66ad18f012a0384,0x4a0c012a1365c7cb8f01,0x7b03781028fe022bd6ab,0xfe0fe813841822d049c0,0xb12bd85580f217c0350,0x4bd009274439582107fc,0xc100b00c1382c282c020,0x88a8c214a0f0e7843c19,0x4a12603785782f220a1f,0x9a04286d41343fb04029,0xc120069080690ae10a90,0xc020100c6c207f8481f,0x2d0632628858980805e8,0x11c31430359310000,0x6d04000268200000000,0x60400000000016834c08,0x2011610000d41000000b,0x588000dfa44ee1880268,0x800034090100001703d8,0x800000001793113818b0,0x403bab100000055851c0,0x10e09dc0b38140],#[0x16e0400029c0ed040000,0x13e4c60164200012820]]
def g255H7 (j : Nat) := if j=0 then 0x1 else 0
set_option maxRecDepth 32000 in
def g255D8 := limbs80 #[#[0x5d96350d205d16350d20,0x5917350d205d96450d20,0x6597350d205d97350d20,0x6597450d205d97450d20,0x6a57650d206597650d20,0x5d97358d20e819650d20,0x5d97458d20e517358d20,0x6a57458d2068d7458d20,0xe8d9758d20e8d7658d20,0x5d39058d205cf9058d20,0x5d974591205db9058d20,0xe8d745912068d7459120,0x68d975912068d7659120,0x591435c12058d435c120,0x5d9435c1205cd435c120,0x6a5615c120645615c120,0x5d9635c1205cd635c120,0xe91635c12069d635c120,0x651645c1205d9645c120,0xd91735c1206a5645c120,0x68d765c120685765c120,0x5d9915c120e8d765c120,0x699915c120659915c120,0x659945c1205d9945c120,0x685965c120699945c120,0x69f615c120e8d965c120,0x68f645c1206a7615c120,0x6a7645c12069f645c120,0x591435c52058d435c520,0x5d9435c5205d1435c520,0x659435c52064d435c520,0xe51435c520699435c520],#[0x5d1635c520ea5435c520,0x64d635c5205d9635c520,0x659635c520651635c520,0xe51635c5206a5635c520,0xe91635c520e81635c520,0x5d1645c520ea5635c520,0x651645c5205d9645c520,0x659745c52069d645c520,0x699745c52068d745c520,0x259765c520e51745c520,0x685765c5202a5765c520,0xe59765c52068d765c520,0x5d1935c520e8d765c520,0xe8d965c5205d9935c520,0x68e965c520e91965c520,0x68f645c5206a7635c520,0x65b935c520e53645c520,0x5db945c520683935c520,0xe8d765cd205d9645cd20,0x6a7645cd2068f645cd20,0x683935d12068d765d120,0x68f945d920e81935d920,0x68597d85206a571d8520,0x5d16358130e8193d9120,0x61163581305d96358130,0x58d715813065d6358130,0x5d971581305d17158130,0x69171581306117158130,0x6a571581306997158130,0xea57158130e917158130,0x5d9735813058d7258130,0x65d73581306117358130],#[0x61174581305d97458130,0x691765813068d7658130,0x6117458d305d97458d30,0x6917658d306817658d30,0x68176591305d97459130,0x6a587591306a17659130,0x611635c1305d9635c130,0x611645c1305d9645c130,0x611735c130591735c130,0xd91735c130619735c130,0x68d765c130619765c130,0x5db645c130691765c130,0x694965c53068f645c130,0x5d9635c5305d1635c530,0x651635c530611635c530,0xe51635c530659635c530,0x5d1645c530e81635c530,0x611645c5305d9645c530,0x6a5645c530651645c530,0x659745c530611745c530,0x259765c530e51745c530,0x681765c530619765c530,0x691765c53068d765c530,0xe59765c5306a1765c530,0x5d9945c530659865c530,0x683645c5305db645c530,0xe53645c53068f645c530,0x5d9645cd305db945c530,0x619765cd30611645cd30,0x691765cd30681765cd30,0x683645cd305db645cd30,0x6a1765d130681765d130],#[0xe8d985d930661945d930,0x6a587d91306a3945d930,0x5d993d91305d990d9130,0x5d97350d405d96350d40,0x6597650d406197650d40,0x5cd435814058d4358140,0x5cd63581405d94358140,0x50d715814065d6358140,0x5d9715814058d7158140,0x50d7258140e917158140,0x65d73581405d97358140,0xe8d74581405d97458140,0x68d765814061d7658140,0x5d97358d4028d9758140,0x6817658d405d97458d40,0x681765914061d7659140,0x58d435c14068d7659140,0x5d9435c1405cd435c140,0x5d9645c1405d9635c140,0x68d765c140619765c140,0x5d9435c54058d435c540,0xe51635c5405d9635c540,0x69d645c5405d9645c540,0x659745c540619745c540,0x699745c54068d745c540,0x681765c540619765c540,0x6a1765c54068d765c540,0x5d9645cd405d1935c540,0x619765d140681765cd40,0x68d765d140681765d140,0x28d905d9405db935d140,0xe817458d43e8d905d940],#[0x61d765914361d7658d43,0x619765d143619765cd43,0x5d163e01435db905d143,0x69d63e01435d963e0143,0x59173e01435d964e0143,0x5d974e01435d973e0143,0x5d97358d605d38350d60,0x6918758d6061d7358d60,0xe8d8758d60e818758d60,0x5cf9058d60e8d9758d60,0xe0d435c16058d435c160,0x5d9635c160e4d435c160,0xe11735c16069d635c160,0x68d765c160685765c160,0x5d9915c160e8d765c160,0x693835c1605db835c160,0x5db935c16068f845c160,0x687945c160693935c160,0xe0d435c56058d435c560,0x5d1635c560e51435c560,0x661635c560659635c560,0x681745c560e81635c560,0xaa1745c5606a1745c560,0x661765c5602a5765c560,0x68d765c560685765c560,0xe81765c560691765c560,0x5d9815c560e8d765c560,0x661835c5605d9835c560,0x60d905c5605d9905c560,0xe8d905c560e4d905c560,0x5d3835c5605d9935c560,0x653835c5605db835c560],#[0xe4f835c560693835c560,0x68f845c560e53835c560,0x683935c560e53845c560,0x691765cd605db945c560,0xe8d765cd60e81765cd60,0xe81875cd60691875cd60,0x68f845cd60e8d875cd60,0xe81765d16068d765d160,0xe81985d160e8d905d160,0x683935d160e8d985d160,0x64f905d960651935d960,0x6509361d60687905d960,0xe819161d60e4d9161d60,0xe919161d60e8d9161d60,0xe8d9461d60e819461d60,0x6479061d6024f9061d60,0xe4f9061d606879061d60,0x6879361d606539361d60,0xe839361d606939361d60,0x65174e0d605d974e0d60,0xe8d76e0d60e8d74e0d60,0x691765cd63681765cd63,0x683845cd63e81765cd63,0x693905cd635db905cd63,0xe8d765d163681765d163,0x68f905d163e81935d163,0x5d973e0163e4d905d963,0x65174e016365173e0163,0x68d765d164681765d164,0xe8d765d164e81765d164,0xe81935d164e8d905d164,0x68f905d1645db905d164],#[0x683945d964683935d164,0xe597350d706839461d64,0xe8198585705938350d70,0xe517358d70e8d9858570,0xe817658d706917658d70,0xe8d9758d70e8d7658d70,0x68d76591706839458d70,0xe819859170e817659170,0x64f905d970651935d970,0xe4d9161970e817660570,0x6479061970e819161970,0x6539361970e4f9061970,0x69393619706879361970,0x68597d8570e839361970,0x65164e0d705d964e0d70,0x68364e0d70e8d76e0d70,0x68d95219716819521971,0xe116350d715d96350d71,0x5d96450d71e916350d71,0x6197450d7169d6450d71,0x6817450d716597450d71,0xe597450d716997450d71,0x68d7650d716597650d71,0xaa57650d716a57650d71,0x5939050d7158f9050d71,0x5db9050d715d39050d71,0xe139050d7161b9050d71,0x68d7458d716609858d71,0xaa57458d716a57458d71,0x6917658d716817658d71,0xe817658d71a617658d71,0x5d98358d71e8d7658d71],#[0x5db8458d71e818358d71,0x5d39058d71e538458d71,0x6139058d715db9058d71,0x6939058d7161b9058d71,0x6839458d71e139058d71,0x68d74591716817459171,0x68d76591716817659171,0xe8d7659171e817659171,0x5d98459171e917659171,0x68d97591716819759171,0xe8d9759171e819759171,0xe81865d171e919759171,0x659905d171e8d865d171,0x659935d171e8d905d171,0xe81965d171e81935d171,0xe91965d171e8d965d171,0x68f845d171683845d171,0x680865d97169b845d171,0x694865d97168c865d971,0x219905d971aa4865d971,0x645905d97128d905d971,0x685905d97164d905d971,0xe4d905d971691905d971,0x219935d971e8d905d971,0xe19935d971651935d971,0x683865d971e81935d971,0x64f905d97168f865d971,0x683935d97168f905d971,0x683945d971e1b935d971,0xe4d43601715d14360171,0x68d76601715d96360171,0x5db8360171e8d7660171],#[0x5db9060d715db9360171,0x68f90619716817661171,0xe8394619716839361971,0x68176d8d71e8f9461971,0x68176d917168197d8d71,0xe1190d917168d76d9171,0xe8193d9171e1193d9171,0x5db84d917168197d9171,0x60d63e017165f84d9171,0xea563e017164d63e0171,0x5d993e01715d983e0171,0x5d990e0d7161993e0171,0x68176e117161990e0d71,0xe9176e117168d76e1171,0xe8d76591736817659173,0xe8193d9173e4d905d973,0x68f64e017365164e0173,0x6839461974683945d974,0xe4d81601766509360176,0x6539360176e4d9160176,0x69393601766879360176,0x5d96350f205d16350f20,0x5917350f205d96450f20,0x5d97450f205d97350f20,0xe517358f205d97358f20,0x5d9745932068d7458f20,0xe8d745932068d7459320,0x591435c72058d435c720,0x5d9435c7205d1435c720,0x5d9635c7205d1635c720,0x5d1645c720e91635c720,0x69d645c7205d9645c720],#[0x699745c72068d745c720,0xe8d765c72068d765c720,0x6459061f61681875c761,0xe3f51f78f3c5f61fb0f7,0x69bacdb66cf33d97bcb9,0x9e75d3a79becdea6f337,0xf89f94fba7db3ea9f4cf,0x5d6adb53da7bd39e7f33,0x5baadbd5faafb577abb5,0xd7cabdb5eaaf4d79eb7d,0xd63db1bd8bebf55f6af9,0xf59f6cef676b3ad9b6c7,0xed6edb73dafad6f6b6b3,0x975cb6e53727b8edc66d,0xe71737b9b5cd6e6372fb,0xbb35d96e7d73db9e5ce6,0x6ee7772bb6ddb2ed5769,0xdbd35df2ef5779bbc5dd,0xaafd37e5bde5eeaf677a,0x2fc7be3d71cf7f2bf65f,0x5b72bb93ec9ee4f326f9,0x9bacdbe5fb2fb97acbae,0xe7eb3f19f6cf6e79f37d,0xba76d36e8fb47ba37d17,0x6eb9f57dab7d5b6abf4f,0x5db2dd95ec9f63baf6d7,0x9c6cdf66db35d99ecbf6,0x6bbb3ed9eecf3675b39d,0xdb76db76d9b69db36d97,0xb6f3b78dbb6dd76e9b72,0x5ddd6edb75dba6dbe6de,0xbf7f1bf2df66fab7d3be],#[0xb7e5b71db87dc3de1bf0,0x4b7a57d27e7b73b79cfc,0xd37e9b74d7a67d32e97f,0x7597a7dd3de9e74eba73,0xdd76ebaf5cbadbd69eb3,0x37797b75db6ed6f6a7b4,0x5fe2ef16f89fbe5de9ef,0x1f78f7c79e37f1b78d7c,0xd69ea6f36f9b3ccde65f,0xf93fc9be4bf23f72fadb,0x7e5df2df967cafe55f29,0x8f9b7cd7e69f33f997cc,0x97ec5f61f9e7cebe73f3,0x74fb8fdb3ed5f69fb37d,0xeb3f53fa6fd2fe93ef1f,0x90f9b514ffc3fb8fda7,0xd26d93c66a5d923602ec,0x35d84822b6629905b414,0x60028d3b624492d80a69,0x21196cb9968d5d8d7157,0x832ed12c28366291f1a8,0x2e91b2d3967fcf8d417,0xb079017d9bf2ec5d8008,0xa603ece23762ec01823,0x104f6711235a638c955d,0x417670029da03e2eec10,0xdcc1208ae9ef5034c0e2,0x1875f2ed06009b784c39,0xfbe5741cd2cbb1661f6c,0xf2bb140de5d89c342ecb,0x5d81b59b2c850d3b4249,0xcd19f5a82c92cbb28af1],#[0xbdb4bb17005ec06b76ae,0x6be9a1525b66998e1b81,0x768e69b5a7684f6d4110,0xa55c3bdb364f05d86021,0xa64eecda923f6086803b,0x7b2ed1b283a6070d8bb2,0x9b377ca0dbc6eb361cc5,0xc926426cdd03f3504702,0x2d1977077a71a60e83ed,0x92fb04c896d83deec5da,0xfd81724b6d1330637449,0xce094d766d3275a43cdb,0x33021b079881da20446e,0x97acb804df5d9150bf60,0xed04f3cb2c3103bb30d,0x6690ad3868004fda0d85,0x495e6bb1a4f05d84d61f,0xe2fed0b92336654b7976,0x5f609833976048d2bb2d,0x7641534d235a8069c8d2,0x154daed1024e74c1d369,0xe6d2ec84be5b026dc3d8,0x29763fc85da35895e982,0xd99f27e5d99f3ef509e2,0xa3805766f1251a60ec5d,0xf1fda44f463d99b09c69,0x48bb09030ed0aa6faec3,0xed1ac4a2ec24821b3799,0x972f197319e6ba1a0be,0xa51ebb0ccc165a2e25b6,0x2fec1025eb2f16109b42,0x76c7abc7b4091a4cb09a],#[0x73343dd9c10915d89818,0xca9c69c602876828b0d9,0x1a37048305768c512d83,0xbb3609bfd9a3c9ce9a38,0xb3841eecdd223368df01,0x4d007666111fb345d7cb,0xbc57609411d9be67c5d9,0xd39941cec1ac4a2ec2f,0xcde75eb2d17803b322d5,0xb3ac99742200ba078466,0xcd8bb31850eda38592ec,0x5d8b459f306db717623,0xec3119ba3914fad41449,0x838cbd244ae46109a522,0x49ced23f0f766fc87bb3,0xe76cd711bb36e839db3a,0xb31d522bb17ac165c010,0xa0e466cdef4634c74be5,0x22376703a25b379401dc,0x1bb36ec9edb9c230eccf,0xbb22654ecc216d30c639,0x86e7430e6537bb34f986,0xf90bb672ca1db074745d,0x1adb894db618e905360e,0x5d9446fb0e382c9863f0,0x8dc90bb4731d2c20e6db,0x19bc4c37e7c5da210eb6,0x7c5d968652e8d8063b01,0xaec091afa685cafd80ac,0x408060dc152c5e585a7b,0x981d6ddb135b4cd9a83a,0x177666f073b674c8dd9b],#[0x7a685039dcc1418ec05f,0x31c4426d1e73e2ecb69f,0xd076b68d131d764e937d,0x9a5765cdb8c3998426c1,0xcbb4170a58ccf7b2ec21,0xe8276daec519ad767257,0xd215db0151b4c398c0e6,0x582cb008326d12d76aec,0x86106f25f609892db02a,0xec9d929b314d64bb440e,0x4303ed830608ec1f44b2,0x52ec0f00e36cd7b6976,0x8f66733dfb3084fcbb24,0xb35e16ecb8e2ee5d8cb1,0x84cb561cc435952fe103,0x74db4c71285a32ac2fd9,0x718638d2cd1a667e6a09,0xd995cf35d8cf1a3668cb,0x5fa5a730de143b418c67,0xf1ad7671c1adb8806eaa,0x3bda3a617ecc1f0c7601,0x6dc395f2ecd8a47b3460,0x6f02d3868040bd801250,0x88d0bb300346e0930576,0xc25da120c7602eb95863,0x760789b9a66c8fabb280,0x52a564c39927fea0f629,0xd8476dd14612ecd80fdb,0x5eb2c033dbb38ede6d81,0x9a82003bda3a4f05da37,0xb47810ecd8145aed1a9f,0xa760b2f159f1a82dd28b],#[0x2cd765d887da2341dee5,0x6da1a233ece4480ac80e,0x9ccc18f684a2c997321e,0xf0b49961812abb0468d6,0x15d83c433eccf505760,0x66cde335d52fe2c99822,0xe81c2c9765dcfed41429,0x87cdcd238632ed8a6802,0x228ec00709f682f1a576,0xeb66eb3f17612139d20b,0x760e164bb33a7fe98a60,0xa5ea0ecc220d768b1bd9,0x41276004151b309c8dd9,0x15b7029e1da098b26190,0xca3dc13ed04676aec740,0x8521fb6af3ac99642cdf,0x216db7328deca3dccc65,0xdad3b406b5da0d76ae89,0x6c1e74a34d1c8cfb34b0,0xe51bb1768a8e0bb0d24b,0x392abb06a7d5d9433fb4,0xe5610904af4c15a73b41,0x36c2937fb0438a1da0aa,0x45612ad303a7e5d91f28,0x82c35d91627766d5197a,0x6d2ec42b0576031bcbb2,0x7b019c03dd36c146c017,0xa47cf6ecc4259b2e8301,0xef2176897a40867b9e1d,0xad9971f9eebb034426d1,0xcb0968b5d8171776081,0xd2410ef60d4243b0791e],#[0x1190bb44c1dcbb1c250e,0x594ba3f690e8dba0736e,0xe5da1148360f220da71c,0x6e3705fb30d121c33dcd,0x7b8fbd41d4ed6cda502b,0xdc5d88104574f39bc98,0x33083a05fb30dca3da05,0x761cc85db3941ded1b87,0x7200eccc34b2ec953e5,0x3362ec9136976611e0bb,0x53a6169c8ba24ac65d81,0xba090546dc1a70aec3b2,0xcca08f68ab119b06f948,0x58bfb040148d8866d165,0x7edabde9dec0ed0eb60d,0x658c71976677075b0758,0x69c129b315dbebb11abc,0xe1c4da27ccd658a87ff6,0xfb6cc8e29b60ef913b35,0xb28fb06fb3301aeca1fc,0x635c4bb27e4c6c1cf38,0xb20f6c1de53b4855937b,0x7fb6668a3ba35e10bd32,0x1b0745fbd9898a968cdf,0x99acf4658a187b4c39bd,0x85797660abe8b3731ead,0x933b67ad44ca3dc78e8d,0xadb364a569a40793660a,0x583a87f5239a05a82b59,0x7d40b9426846da2e9046,0x54ad9c7eefecd7881f66,0xced137103690f0a5b381],#[0x289215bb3864b1d989e3,0x14524d22d4486d14985f,0xe9868d8e8774868413b4,0xab6832c47940e1e9ca24,0x94105febb2729eecced2,0x2cac8e19ea2ff6094413,0xc6472cfea5da373858da,0xa9a420859d82c836ecd2,0xda054fae19e87fb6093a,0xa2710f60f82efb055d4c,0xd3eb9626ce2d23ea23ed,0x59d832e2cec1637af688,0x5d8b53d328350ebb043c,0x8dd2c3b307c98da268f4,0x2daada028fd6ce3e4bb4,0x876a0b54bf0cfb0ddb45,0x7690c0a5b66d49bd828e,0x627ca7d99e2fde58425d,0x569ee921a87b5239be97,0x70766ce1dc9480dffcb1,0xda32f954d1912e2e19fd,0x41e8ba619b566f68cda8,0x583c726ca325b448502d,0xbd5b339612d8856b9e91,0xda46071659da87f4c39,0xccec1cf6cb1a89a47a1f,0xa63fdb03a9bac39c0f46,0x9c7d99b053ed0a71ab68,0x7691bd66b6708289a47b,0xec5208db4449ead81b89,0x3dd09d32b50fe90737a2,0x2e3618e77ff523abd5b0],#[0xc726acb35866c9a6c336,0xb45957ed9afc86e91583,0xa9e8e5d97d66f08e18f5,0x671b0c4b01fba55c9ad9,0x81b4439abd3058f45d92,0xd9858ebe512524368b63,0x13d7172c55123b3871b3,0xe98bb40b621db03ce7e5,0xd4c20f8b9ed16307b66e,0xed078243610e9df94811,0x62e2c1b40c94cd205263,0xc4ead22aae2618b656f6,0x3dec157837483a25da44,0xb66272ebb491591c3388,0x47a1f1d981af56d0e452,0x6216ed16026760ddb3d9,0x1cb68b4a7da33e8bddb0,0x1a4584ebd32a2986d11c,0x8030fd6d23b22760bc9e,0x4e29b670dbfd984ccbdd,0xb2ba3689ada2384dec1,0x8da37a3aed95f4bf46e6,0xcc24553484314db086c9,0x94ab7a411c4bdb2befe6,0x1e4bb02c64ecc2d2e768,0x86583f24368c5013ba89,0x2cff0f7b058dfebb0eed,0x89562ca0905aec1fd647,0x8e68d7a6c76830ae7a4,0x62c669935b36399ad842,0xb3731f4bb13a9868d4f8,0x38235eccbf3bf0906933],#[0x97135057a95a4159e9da,0xfdb34e171db2c4996dc9,0xd21b2ace50b477966bc3,0x9f23b92902193b30c152,0xbc35960e55a520b697e1,0x10599e677e520333f74a,0x6d1ee7d766e6121b05c6,0x80f9c5947c945d1bd6a2,0x68f0d232d076cc415776,0x21ec1d31bf60a521ba45,0xf6627185b60fd24bb2e4,0x450c73d991492e8d7052,0xea4dec1886470cfaa1f9,0x7db6846097b6655ffd30,0xf942cd1cbb2f84c6c1f8,0xb088c86d1c429f60e5ab,0x2849348b618fb41e5fab,0x2ebb485960d206505ed0,0x7d8354fde5a4316760cc,0xd16356f282fa89b87b8a,0xb815bb06dc43d9bb226e,0x5e9da28d032ccfa24766,0x6e0db7d36693963b314,0x48af1c59677047db2c6e,0x5e058d8aca53ecdca443,0x69e6ce1b7eaec23a39a3,0x766b30b7b0064b5d9a5,0x76509c4c31629e6c21b7,0x250feecc2452b751d389,0x57f36810a79a43d0b9da,0xdba461852d8384d3658b,0xda23c926d16c5df60b11],#[0x8582cf60341c7a3749c6,0x483db375cadd9c04fde5,0x90bb391046d83a51746f,0x6c0a27ef2d210adb4045,0xb1367b30bdc6c39b2ff,0xb89ada290986911b1ef6,0xdd618fb2eb680833d947,0x3683924ba3871bbd99bc,0x6999abb36aff6c51d6a,0xd6d8ed06d58f2c2427bb,0x1cf6cb127ba486491d82,0x5a4909c0c390e296c206,0x33dc216d1ed39f4d1329,0x2c1376914085b375145c,0x18bb40c5fbcb0ac56ecd,0x8d9c1ea56905838b28f7,0xcd7a4274caea95ba105e,0x75ae3a656032da0b6446,0x177c9ab2d4eccce7a2ec,0x9690dd7c2ed192c59612,0x683fb89862b447db450a,0x39c43d9ba5076ce3a683,0x276e915822360bda7da4,0xd72c5629da33cd11d1ab,0xb3739ffd826a396d1117,0x12af86d00b717309b131,0x43af4cc2bedb320146d2,0x4bb388d09d32b025ec15,0xd396aade905b44726ac8,0x1637130c7a165b40a93c,0x1c3da41cddeda1b63bed,0x2ed226826ed19871b0e4],#[0x6cddf29b6c5414fb47ad,0xb103db0760edd244c53,0xddc0da2ea23ed9641676,0x985d9506eb70443edb02,0x7491294fb47a479da160,0x68e12fc33dc2dec00f3b,0xc085e995c7eb6821411b,0x3c746a8bd1b083cf1c9a,0xd761e9a1d99aa71651f7,0x811061ed03d53348153f,0xf86b708d8411760fdead,0x8fb68a51051ab89f690,0x8d9896f46d0ea7137051,0xc1cd4174cad887b076e0,0xf6b217671546d21744ce,0xdf4da136206d18b6470c,0xdec16407b6ced1dba464,0x60ccbf5b3131eada1a83,0x625ded991015ed0a5167,0xa67aa5577a2ece1135b4,0x170cff21ba4895f6da0f,0xb411557db03e23ed9627,0x862fee982b4c3488e187,0x67db606d8b1b466961d1,0xebb37f1cec3150b0ecc2,0xd88645fed8794bb46e63,0xc641cf6cb23e9b328960,0x2430b337d63ca090f8ec,0x4ad30a073e99520db70b,0xe19ee69b2c5219db4305,0x719c23b33cd10d22c2fa,0x7099db3d8f25da347936],#[0x46ce3d4bf0cfb83db67,0x746ae0a7b4718c1da13d,0x211feda0ea78e8d8f44,0x1c4c6c1f12fb6c3dbedb,0x867666fb2796649f0bb0,0x7b06e045d8320a2690ac,0xa1fb04ed0631d3688808,0x6e7a366e89cfa6561aec,0x1c9a4644a7da16cc46d1,0x4d8bdc356d19e2c3682c,0xe0ea7030c5d9c5a37514,0xa7b46d042d83aae26,0x1ae82ab8412055e05800,0x71b30309c55e09571010,0xc31408252845388010ee,0x72e4d9f99ae30c25b48a,0xe46ac87850421f253bf6,0xb52a3c51de9d3d2ea247,0xc78584daf355c08b3395,0xb722adea5b16b4bc6694,0x913fea7d2ef46ddd63a6,0x2036348453f875909760,0x29b45331260f4acc931d,0x4b51eba25341be7d44eb,0x5806aa0d482a7cf4d3e9,0xdb419654ec3f579cadd1,0x29dd7fb969706adb85ac,0x864307fe01ebf2b7ba6f,0x8c96f90331a862cec46f,0x35e7cdce499a8f2ffe55,0xb05b5b0eac1d3f7a4e74,0xddf6dbbd77146db6d9ab],#[0xc6f2e5e459c60f866703,0xdc8fb39f5a6ea2dd0db9,0x165a12003c9f788aefb3,0x6ce85417802750a6f2e1,0x233d26621380254f662a,0xf6b2ad0c6016002710b7,0xd1074aa10a5b178022cf,0x2670773aa4ea5d178028,0x8023cec63aa8f4551580,0x1780262f86c2c0f0450f,0x5815802a92d7b30d2a69,0xee501b002a11274aa504,0xf8bc3f10002510369a90,0x42e8fe5618001f2cd581,0x966294fa57178026f167,0x3207d2f92e581b0024cf,0x2a11f76b311c6718802a,0x24b086eaf5185b1080,0x17802d73284b4d307216,0x831b0023ee561a78f257,0x106110802df277635966,0x810e5017802811d75b29,0x6208c43d1200254ff672,0x36c2bd18540f001fcc85,0x70063a9cfa54160026d0,0x2810c793112261198027,0x801fad65ca4cde480f00,0xe0025d0a6e30d305c16,0x711a002a319742b10a50,0xc6d1b802ff4c8d35d64,0x74e643110024aff6caf5,0x42c0e2541b80218e565a],#[0x5ba3cdc4e16002810d7,0x4e560a24ca3d128021ce,0x26b076caa11054128021,0x80248ff712e50a531780,0x11802750263a7cc84110,0x59158026d0666270ee49,0x16541380281207caf10a,0xf53068180029f1274add,0x1278ee400b8028f267fa,0x1652a506511700234ec6,0x91671afd0a601380226f,0x28714793293a69160029,0x248f566298f8561580,0x1300220f068268d8490b,0x681f0023d0768a84f654,0x105d1800262f75eab11c,0x8ce63c0d802c520702e1,0x5ad51c580d8023b07692,0x7fb20f85318002a1267,0xf0867274ee5d14002bf3,0x2610e7a2f51a6c1c0024,0x801187532170842b0b80,0x1780196ac46174882f07,0x490f801ece6622c51c65,0xc63911801aaac499e0b0,0xc094360800176aa449dc,0x31a892301200148993e1,0x43694072250580162a04,0x912f1186a240c8013a8,0x112742e8f84c13058015,0x800f65e2b0f8662b0580,0xf80140863a18ca44a0d],#[0x4a1180140883a9547a30,0xb03c0d0017ca04920cc2,0xf0d43d0c00138853e9b8,0xd188963c1500178aa4a1,0xd311186c21070017e903,0xc8d359688e3008801468,0x13089371506619068014,0x1368c371988c350d80,0x4001248439950882707,0x28088014a953e12c6e27,0x5a1c0780188953c1607e,0x648c2b0b800fc6f2d94c,0xe144722e0a8013472351,0xd4c1a09e350d800e6642,0x271319187c1e088018ab,0x13e8834168742306000f,0x110703092874220b80,0x4000c6561e0d0361004,0x1a040014482349607c24,0x681e088012c843e15460,0x2c74210c80122792d930,0x594c741a040012e85389,0x1218e462290a0011a7a3,0x4873612872230a000be5,0x12672321387624050013,0x801568b3414074260b00,0xa8015a93429d8a23810,0x2d110014c903f17c8a28,0x8a2c0d00130793393878,0x8c9e38070014c973c15c,0x1184902a0d0015ca63f9,0x2280e0541f0b80188a24],#[0xa9e449a486290b800d46,0x13e8e3e96ca63a0e8016,0x800f8743613c7e2f0b80,0xd800e6672b110782309,0x300a8014c8f3b968842b,0x90300c80118723014886,0x6080380f00144843698c,0xa8f8581b080011c7e319,0xb419889831088010e6f2,0x26f33944782d0c0016c9,0x172933795c9e2e040010,0x8012a853998c923a0d00,0xd8013c883918484280b,0x23058015289341607c26,0xf80fc0001407e3597468,0xc082585178182902c028,0xaec202201000fbc25c0e,0x80e85644a8523c28110c,0x83810bc0dc2820fc1ec2,0x8f4081898385002be442,0x70b02a05094a9c201605,0x5804e01902af42ec4092,0x108ef838ce5c241140f8,0x64a860bc1b0b02282dfc,0xc3ac27435c460b0c2054,0xb4170430ed44483f440,0xf410159c2855e4b61058,0x1dcc500ad07c0ee84417,0x3a43f8460ac186c30918,0x8c5500f00f82219118ec,0x29912106907c5001409d,0x2743ac514c386e8220e8],#[0xcc260fcc464258404ad4,0x61b068c28230e1817a8a,0x281d2c1502586f8150f8,0x10eec1c8a81f05db03f8,0xc6950607bc309f00305f,0x490fc104190286808a20,0x50c218990118143acae8,0xc502130400698998080e,0x250eccad0b48eb80a879,0xb8128c28eec1244c1274,0x699821c0f02e42b0f949,0x820c004a11d4a9cac0d0,0x82400984ee05e1108ae1,0xc0587b4ad06e8b44530a,0xfa4ed41503c8c109bc3d,0x88c502d822c294694220,0x8b14570201810c1c04c0,0x25c3001a4a021c18b4b1,0x1c4c311144e444b04a1,0x44911a502c460d44998c,0x3c87ac4843307b8a6c4d,0x24410ae8af0488e0a144,0x87c8418690e604205921,0x130234200c280b44504e,0x302cc0142b87c85c1e5c,0x8a02489101270fa85c85,0x189618e91da94124f835,0x187e430009410908479c,0xe1142115c1d04119645,0xe844c8a786bc441b2184,0x8a18d12c311798d34302,0x10864a4a91008f94a509],#[0x99c6c09c0682b09801e9,0x841583113c0384b8b24,0x82827b46e0ec4c4c9b45,0xe505f09c82204e056033,0x983606b00a210c089881,0x13343fc2a82147a1e042,0x9d430050852cb041d47d,0xb0a1c915118aa86950b4,0x9c510584b830d6007cc4,0xb342c8698140da10a840,0x58ad4294ed4691644458,0x8490d81b613604a07e0c,0x9c8e384411c5844a40aa,0x701446d41d0d61b50dd8,0x4570ecc111c214490318,0x2c4330c049d81d8ea8fd,0x205480d1428506268518,0x94649d05105405b03027,0x358124c301344b059058,0xa82c9402d21d2c024511,0x103c1005c210c4290686,0x33bfec2142184140f06b,0x5c36014c979d1b066605,0x336be067e202192e02,0x10c3fedc6280901fd69,0x4307f4a480cc0f71793b,0x191d6b502911fc3a3d40,0x2948fe38e0522aea336,0xe5fedeb860067b3d5880,0xc4fb0148cff7c89b0010,0x9a900014f6399e113100,0x111ffeb30600677babfa],#[0x22a3cc64c5e6f345d401,0xcaff3268014ba22efe01,0x62e654814a1c76fa8019,0x84410b2e5464fec010e2,0xff20085d3c242052689e,0xa1c6a2979b16d042a3e5,0x2258403168751a608062,0x7a014a7602dc9814a9be,0x1e902a31f9a2042057b1,0x91f6f0e042b980071e02,0x4e9e08393f3be8100029,0x3f66808647f0e8f5010c,0xb9de43d029bbd018e502,0xa3b3f87228a19602a003,0x4433e415640a523f180,0x2102160f2bec8052cfe0,0x60014a487f4408527b7e,0x35d02932f28d4697b5fb,0x7014db753803000537df,0x401480df1c99004bebf4,0x29c003f8fba005329bdf,0xfabb682174e8f48c99e0,0xcc81480029cafc4028e5,0x436dfe70010805375dd,0x2fbc35f6029f9f5c1ecc,0x3220862bf85e100a523d,0x11dffa34cd801a25f1ee,0x8bbf8048c414abe44e01,0x4b905e44402950e35168,0xc3a5f0202944f73fb801,0xfe58c0404419f7776aa4,0xa8a7f0e6404283c1fe],#[0xcae42030d0f2657ef064,0xeb341066ff5666022043,0xfeef1c60122d768e2042,0xc5b8029580f83c320432,0xf80052167fa80198cffc,0x93b62070eaf6f128cca9,0xa6c734c084d69a010,0x3c052e3f1020ecf43980,0x99814b5fa8f032a563ef,0x2052c1f82a814937d467,0x3743f100a79b1bab,0x1c63009303e001000628,0x18b659a295c84061e8fc,0x445e02000c49dfc94020,0x926603300310cfd5d80a,0x89fcd2c0010d97fd1002,0x40af0602323fc174a821,0x71e980cadf7f8e99b003,0x313695fd0f00c000544,0x75ffb41280014f83858c,0x1e00d6043abeac8810a0,0x3c08c04305f8e00a467e,0x3125f2c54481008837f8,0x7c397ba97411133d55c0,0x21580a637c2604243c,0xc02469f45cb88029a0fc,0x29f5780058637ff4b8,0xcb25c500a69bfd470120,0x8030f8ff4c1a4014cf7,0x4e7308ae7e4406029797,0xff4429010c8f57a80216,0x243fffd6484003001126],#[0x878e62060d4fb75b9005,0x2948ffa7b08000a65bf,0xa57f460400053b9ab87e,0xe7961e0086b397ec0a4d,0x5f0108328ef72180624b,0x2865c5bc194cd0d0c149,0xccf7a010f014f155f803,0xa44014c17fb2cb0052b9,0x8f0c84030005501f5cff,0xa4b7abfd0280868bfe74,0x3c3001118615109f0a00,0xdb8b95020408bb7fe6ad,0xdc582108b9f006502bf1,0x520006948cde55005430,0xc00b6729e02a12fdc800,0x1528010e0fe440840bdc,0x500029f1f9a2042009f9,0x80fdcbc700c5037bcdde,0xeb4afda000a62a75e032,0x96a9fda400a5f9e26109,0xf8044042d3f5f57a8021,0x18f5fd382212584a0e9f,0xea2b06537cb48042a7c8,0x9a77c011649de8080a58,0xfa0d40a50b7bb1ff0c02,0xf2ae7102986f786a3c24,0x84f7ffd1a00a40870b8b,0xa59b87118052b31fd60,0x1f6345c4d043f1d1d1e0,0x2aa7f6052d9f5f925a96,0xe064d042e3b1b9b042cd,0x47b0030edfc1e8008547],#[0x53f3ebab330110220,0xa664ebc01958ff808242,0xbbb9d40430517e625000,0x49810f37ff09ef014a2f,0xb2e4fbd304a516bf5f8,0xa693f93580a00a6d1e93,0x2c6d8e0c8011dc996bc0,0x4dde3460188aff86ae04,0x28d13ffa206553c1f40a,0x21aba7db00337067a,0x21b5fb280d010dcf070,0x57e1747014e0f8bfa67,0x9cb063afcb7f840cd878,0x77a75832e0e16200018a,0x43c38b041bafa8080625,0x877684043fbb3c5e95e0,0xf7a05399ee7500a457e3,0xb11e10062dda58a144,0x180a557ffaccc0440870,0x9d1ff7f50e7021c4f9a4,0xad805419ff4263508802,0x1540f3c0a41becc8c923,0xa601cf43f8430cb015,0xf278c906821e8e2f6000,0xffcc07c821cdc9801088,0xa611de8782cf6014c0fd,0x251cdccd172e200a755e,0x7c981494e2e66042e19a,0xfc26032a7fcaac833196,0x9696972821d13d640ca1,0x2fbfc086e080bf402979,0xc89c02e085e5e6b0b1cc],#[0xf885f5c3410fdf08e832,0x2a2ab381462bc5845f7,0x99dc010f47a300dab501,0x4029b56f27410aaffddc,0x14a6fd10c109876bc183,0xc233b37ac109c7f67210,0xd24c0851de08061ea81d,0x483014b83ea0a00c457c,0x90052357f18003325fe0,0x170b71608503daa2216f,0x3fee011c0876dbe30065,0x790840a4db3a840a4f7d,0xce4552085c70681410b7,0x2100a6c9f86204018b,0x83dc08673f2c0a3dbfce,0x4305fec5b7014a8368f,0xdff2d86f810d0abc3b21,0x675081495bd89c8a0317,0x560438da1f3c42814db,0x9a3cfa782703343ffd4e,0x6f002129cf48010b8672,0x953840187abc002c356,0xffaa3f24180a711bd9c1,0xfdcc00446a0de0006229,0x2ff23d00840299dfbadc,0x72f2410937fd03020294,0x9e5878021a3f50600668,0xe5500014d852f280a427,0x62a5fe7256100014f064,0x3eed6a2053fac472c300,0xb8219ef85628052a5819,0xa6abf45a400a5f2347a9],#[0x95300053f1e37f900100,0x424bfe03c08533b1fd2,0x8537d22e90a04393d9a,0xa7e41e589d04313a2ec0,0xf2f180437dabd5496000,0x6010db66150380053791,0xd99f37cc482029ede520,0xf7668086efeb1448033a,0xa52fdad51e18006937af,0x1df976e065bbff0d2f80,0x524dfcb85a95048015,0x9fc023222e482112fce8,0x6a9fb81006251cea2def,0x4e4605239c1b9fd0280a,0xf01000313bf0c90195ad,0x4c2029e1f6e6e1a08671,0x77fb110a021a8ffa4ed1,0x762a529c0532b451e084,0x485f68061c3f211010b9,0x18b1b5b8032cdfe6180a,0x9d5fbb34042e0e4720e0,0xd2b00337dcad8e1b941a,0x82108fc32f24a080a7cf,0xfa7fb45b00029804ff5,0x2e6982525bffd30e2401,0x92180029f0fe4a800297,0xc1d6fdca0805341ff077,0xa8d718048b5d513a0062,0xfef546b021e1fa78084d,0x20216efe474c053014f8,0xa49bf2b9b014b4ffc02,0x850fb99fc019a4a9e4c],#[0x432fe3f56011d1fb4a8,0x2d6cf98e021c1fe9a99a,0x100f9be6b1805303c505,0x3b9cef1fd814aa47f102,0x9fe000c96f4fec80c004,0x4803a66b018909b1c109,0x8cbb83e1104345f40581,0x1a1f9088085ebf844014,0x5d1986029b5abfc68702,0xa89b88051a1c6a2b3ff,0x4fca021a8f77146ad404,0xaa7e01923f5060066822,0x3e28ffb00a0501111e62,0x9b38147939fa58040005,0xd6b4052e91bc5c5c0530,0xb80629df7b8180a5ebc9,0x543b9b567042cae436c,0x29cc05471eaf02618904,0x710438e018a039d9f5b2,0x31bb7a601874e1820cf,0x751ea0010e02b7e71e08,0xa8408722aff927014baf,0x40fa0536989446ffd5ca,0x3695029e9c3041f9fbc6,0x9ba65e0d90438007dff3,0x8a2806087abffc825490,0x9d7e36019114029dde8e,0x7fbc04404322fb080018,0xc0e906531f25c1c00c54,0x465780aadba5ea2052c7,0xba818008702efed84ee5,0x86a7ff344420437bfff],#[0x1882fe970420b83c90d6,0xc8bfb4001814d43c2060,0x298eabff00a45de3b0a,0xafb0832c053bdfab9228,0x53a1c6a2cbc24347c7d,0x93f600043e9fa490d704,0x3ac080a637c260423beb,0x617dfe9ed06000a7fbea,0xbc04261b34fd05085bc2,0xf171c4a294382c3b544b,0x6584f7228b788401303d,0x63260ae30e130f2d0f4f,0x518007d9fd92a591eb61,0x4b0d20b2664261e5ff04,0xe292a4e2a653f9798829,0x5ee242568cfe20b136ff,0x2dd0e660229c71958a5f,0x2654859db121879381e1,0xa9c50a771d87ae0744ff,0xeee95171d4a2aabc210e,0x168806e359e1eef8c230,0xf869ae091f93b5b2851b,0xe87507a3c3bbe308c3c2,0x7ba46f862b3f16622918,0x8980b1e6228e506eead1,0xd0c2941b0280e785abc2,0x38b2f8fa8e17ac7d871b,0x6c3c4c04178379e1c8e8,0x285f920f77f61379b109,0x7b5845b0e859f0b34ce1,0x315c1d16f10afbc34858,0x783bbfb0b2e5d0b133dd],#[0xec36f42636cfc2014863,0x59c0a39a09ee35134e5f,0xbd0a2a4201b8854786c0,0xc4cb8ea98676e7ea300d,0x801de5676de2a564e11,0x4605c0f1647c379e1b6f,0x4165e0dc07c4a3b80f89,0x70fc31b010987b311843,0xcdc484562e858489ddc2,0x867928b9701320e243f,0xf644a3e6075c0889fd19,0xc68bc4611af82d59b11e,0x2361d163c3141c6728a1,0x131c8c46141c4a200a34,0x127608a5fb17b415237a,0x5f625148c461107c3d78,0x3301d0b47d6de852670c,0xe17dd4a29b4261f0a3f9,0x5f4b4cab38ba6c515805,0xdf12184362e606ac4a28,0xe623020a5a1ee2a395c1,0x8a319e0c52b45c29d15d,0xe33c2f1f86b4ee171d9d,0xc63c50d9ee249f106b0,0x58b3426a74dc4642b416,0x1cb42d1c538a034ae246,0x77de1bae278958b341b0,0xc9145d46b460073ab318,0x400ba355c36173026e04,0x6c361e1c99909876b835,0x8d8a7909ac24bd180001,0x94cc715efc60a041317b],#[0x318ef05984780185c3a1,0x4d30d670984b42e89bc4,0xc62430362e477128ca7c,0x52467872c3c686d706e7,0xc2a342df0c40137ce026,0x2a5f12bd416efec2e5b2,0x6e6f2b1002d3c30df84c,0x7c4c784ce482ea58800,0x25d163810060277e544c,0x700a0f1b81e2251cd076,0x9e368b0c1df8b3bbcc28,0xf069ed920c008e24ea54,0xef9a300dc42a3c35a0a4,0x2b1990baf16100730377,0xa6c3fbb7658726568b23,0x39b08012ced12ad26b61,0x6cfec2c3a19da4c2a43f,0xa4200018e0766230a721,0xa3ab0e5609c4008b41c2,0xbc76105d9b51806477d0,0x87099ee2e8f0eaccb064,0x5a5f08062fd18553607b,0x39a2a433ff10d5274774,0x92f060c94471f08009f9,0x4735090607086c5a2ab0,0xd26121d092ece131f93b,0x472b101783467683002d,0x40267046be1c7d82f109,0x4453acc2c9cf14c3c8f8,0x8a75ce143482c343f4df,0xf3028080007b9a0bbd1,0xb1c0a69b12ef0109865b],#[0x712ef8835870de1e8ee8,0xd578901cb432250d6399,0x818a568bbc3131c4a2e2,0xc1d3f28980a32c59a139,0x93662309ce3a276d82d1,0x32187b3454587119e38a,0xc232a7458be504c3a1eb,0x3033686ef315c14853a1,0xf0a39a0b8e545199a717,0x94703d5e141c6228e4b,0xc45ba37bb288e3e13bef,0xbe13702c0412af05c333,0x6b092f4675f0acfc30a5,0x3af4e836e18a633ce200,0x76e00cc3c5e59161987c,0xbe02d916206c3f684c91,0x4a7b6483949824b3b44d,0x788c2a0f0803d8df496a,0x78baac29aa6868d6e868,0xa32105e00621327ec098,0x100e38944a17e483113f,0x8000187c342e385cc0d2,0x8290d79cc2ce189b4e31,0x5c72a221bc23c3fbfe2b,0x64c7f0836f4263ab854,0x3d9a718047a258c08fc5,0x45bcf5161c6f06fbc381,0x34ba1c3a1c9c3c2e3894,0x214894360200012fd508,0xd0787a96200bded614f,0x9ee863b847165bab5199,0xb23a2f46437b85b3fb0],#[0x43de0a83c3a7128956af,0x85361d7032310c9bb971,0x9616477128f27f2c220f,0xb827137a131c1d0a21dd,0x944e74be51a5fda24065,0x20040e438a2f446a3d38,0x89ee85b3987130121bdc,0x1be1bef0b01cdc1cac13,0x198cae11773dc587ea8b,0xb4770230ee783dbe9d96,0x613d1d4269b14445dfb8,0xbe991623c655e2d986c2,0x446e065f3053b09853a2,0x1ae0693e100028e8b0c5,0xfadc79718017e385480,0x4ca483e4494a475e2c20,0x3c3b68978a1a20a6f9c0,0x297428887e16b81b442a,0xc7128a9382712dd09d7c,0xf6e00cc319a8f095783,0x8586c28792080a3a23de,0x1ef8886870980c3724e2,0x3d45875381a6c343a198,0x58961e1ec7c636020183,0x461843624d87b713994,0x1b7a1449a6c4fbe4]]
def g255H8 := limbs80 #[#[0x220014102081802a1862,0x54242061a6161402008,0x62a01686106010119524,0x50c2180614f8444a02a5,0x2d310f3616044a01244,0x1040d790510080020d,0x801ec04508607410809,0x52b7e3e0000000000000,0xfff77de01ffaffbffeff,0xfe6bffffffdfb,0xe00000000]]
set_option maxRecDepth 32000 in
def g255D9 := limbs80 #[#[0x581105d9604417158110,0x481985d9106197144197,0x5cd434816450d2058d43,0x50d205d9434817450d20,0x4838350d2065d4348196,0x65d614839650d20e1943,0x58d205d1634817358d20,0x4829858d2065d6348176,0xe51634839058d20e1963,0x591205d9644817459120,0x481615c12050d7048197,0x5cd70481645c12058d70,0x5c12064570481765c120,0x482965c1206597048194,0xd9170483635c120d8570,0x5c52050d71480965c520,0x481745c5205917148163,0x65171481935c5205d971,0x5c520a5971481965c520,0x483935c520d917148363,0x59173483965c520e5171,0x5d120d9173481765cd20,0x481965d12064d7448176,0x64576483965d120e4d74,0x5d920e4d76481935d920,0x48171d852064e7648394,0x65f6448193d912065f61,0x5813065b8448196e0d20,0x4c1715813058d604c142,0x5d1604c173581305c960,0x58130611604c17658130,0x4c2765813065d604c192],#[0x611634c17658d305d163,0x58d309d9634c19758d30,0x4c176591305d1644c390,0x65d644c1875913061164,0x5c130591704c1635c130,0x4c1845c1305d9704c173,0x259714c3645c13061970,0x5c530591714c1635c530,0x4c1845c5305d9714c174,0x659714c1945c53061971,0x5c530d91714c2965c530,0x4c1645c93058d724c394,0x591734c1865c93061172,0x5cd30611734c1765cd30,0x4c1765d130d91734c186,0xe59744c1985d13061174,0x5d930641764c1865d930,0x4c1985d930651764c193,0x65d844c3985d930e5176,0x61930649864c39661130,0x4c39461930e41864c197,0x643644c187d91305db64,0x50d406193250193d9130,0x5017650d405cd4350163,0x659435018750d4061943,0x58140e59435019750d40,0x501715814058d6050143,0x5d16050173581405c960,0x5814061d605017658140,0x5017358d4065d6050192,0x61d635017658d405d163,0x59140e61635019758d40],#[0x501975914061d6450176,0x59170501635c14050d70,0x5c1405d970501735c140,0x501435c5406597050186,0x5d171501645c54058d71,0x5c54061971501765c540,0x501965c54064d7150190,0x50d72503945c54066171,0x5cd4059173501865c940,0x501865d1405d97450176,0xe4d74501965d14064d74,0x5d94061976503965d140,0x501935d9406417650187,0xe6176503935d94066176,0x6194065d865019261940,0x5019661d4064d8750393,0x5d16350f9661d40e4d87,0x58d4361d6350d7658d43,0x50d7659143e516350d97,0x5917350d975914361d64,0x5cd436197350d765cd43,0x50d765d143e197350d96,0x6597450d905d14361974,0x5d143e417450f865d143,0x50d875d9436197650f96,0xa617650d985d94364d76,0x61943e617650f905d943,0x50f906194365d8650d87,0x6598750d9061d43e5186,0xe0143e598750f9061d43,0x50d73e01435938050d63,0x65f8050d76e01435d380],#[0x50d6058d4358197e1943,0x5817650d605d14358173,0xe0d435819750d6061d43,0x58d605d1635817358d60,0x5819758d6061d6358176,0x58d70581435c160e4163,0x5c1605d970581735c160,0x581845c16060d7058181,0xd8d70581945c16064570,0x5c160e1170583835c160,0x583945c160e4d7058391,0x5d171581635c56050d71,0x5c56060571581765c560,0x581905c5606117158183,0x65971581945c56064d71,0x5c560a6171581985c560,0x583835c560e057158363,0xe5171583935c560e1171,0x5c96050d72583985c560,0x581765cd60e117258383,0x66173581875cd6060d73,0x5d1605d974583845cd60,0x581935d1606417458184,0xe4d74582985d16066174,0x5d96064576583985d160,0x583905d9606517658193,0x61d815817660560e4d76,0x61d6061d845816360960,0x5819361d606458758093,0xe45875839061d6065187,0xd8d60e51875839361d60,0x58174e0d6065f8158187],#[0x65f8358194e0d605db83,0x61d6165f8458193e1160,0x58f9461d61e458758790,0x6517358d845cd635d973,0x5cd63e417358f845cd63,0x58d845d1635d97458f94,0x6617458d935d16364174,0x5d163e417458e985d163,0x58d945d9636417658f98,0x5cd8058f935d963e4176,0x61d636518758d9061d63,0x58f9461d63e4d8758f90,0x5db8058d74e01635cf80,0xe116365f8058d94e0163,0x591765d16465f8458d90,0xe4174591935d16464174,0x5d96464176593935d164,0x593935d964e417659193,0x64d875919061d64e5176,0x61d64e4d875939061d64,0x5c16450d7058d435c394,0x641435c17650d705cd43,0x50d70e0d435c19850d70,0x5c19858570605615c396,0x641635c17658d705cd63,0x59170e51635c19758d70,0x5c19859170611645c176,0x64d765c1915d970d9173,0x5d970e41765c1945d970,0x5c186605705d9815c393,0x619845c1766117065981,0x61970645865c19661170],#[0x5c39361970e41865c194,0x643635c198d857065f61,0xd9170e0f635c198d8d70,0x5c197d917064f645c190,0x5db835c164e0d7066364,0xe0d7065b835c194e0d70,0x5c59021971647845c364,0x58d435c5952197164c86,0x50d715d1435c56450d71,0x5c58650d7160d435c576,0x661435c59650d7164143,0x50d71e41435c78450d71,0x5c49858d71e61435c796,0x60d635c57658d715d163,0x58d71619635c58458d71,0x5c59858d71651635c590,0xe41635c78458d71a6163,0x59171e61635c79458d71,0x5c584591715d9645c574,0x619745c5985917165d64,0x5d17164d745c5905d171,0x5c4865d971e11745c596,0x645765c5905d97126176,0x5d971651765c5935d971,0x5c7915d971e41765c786,0x50d805c7945d971e4d76,0x601715d1805c56360171,0x5c78360171619805c576,0x5d9835c57460d71e4d80,0x61171e41835c58660d71,0x5c79161971e41865c576,0x64e865c79461971e4d86],#[0xd8d71643635c576d8d71,0x5c576d9171663635c597,0x65f645c593d917164364,0xe0171e13645c598d9171,0x5c583e01715db805c563,0x65b805c593e017161b80,0xe0d7161b835c763e0171,0x5c576e117165b835c590,0x65b845c593e117164384,0x50d7264f865c590e1971,0x5cd7659173e51635cb96,0x641765cd985917361164,0x5d973e41765cd945d973,0x5cf93619735d9845cf93,0x65f645cd93d917364364,0xe0173593805cd98d9173,0x5cd96e0173653805cd76,0x64d765d1905d974d9380,0x5d974e4d765d3905d974,0x5d186601745d9805d394,0x619835d17660d74e4d80,0x61974e41865d39060d74,0x5d176e0174e51865d393,0x643835d196e017464f80,0xe1974643865d196e0d74,0x5d9816017624d805d993,0xe05805d9946017664580,0x60d76e4d805db8360176,0x5d981e0176e41835d984,0x64f805d991e017660f80,0xe0d76643835d994e0176,0xc8193e1176643845d994],#[0x5cd43c816450f2058d43,0x50f205d943c817450f20,0xc819758720e5943c8197,0x5d963c817458f205cd63,0x59320e5163c819758f20,0xc8197593205d964c8174,0x59171c81635c72050d71,0x5c7205d971c81745c720,0xc81645cf20e4d71c8196,0x64d74c81765d3205d973,0x5d320e4d74c81965d320,0xc81935db2064576c8396,0x5cd63d83945db20e4d76,0x5c7605d971d81635c760,0xd81985c76061d71d8183,0x61d71d85835cf60e4d71,0x61f6164187d85985c761,0xd919061f6364176d8d91,0xe4183d91935db6464176,0x61f64e4187d919061f64,0x6fe5fe5f63fe3de3bf93,0xf27ee7ea7de7be7b67ae,0x6afe9fe9f67fe7fa7f67,0xbfabf6be6bdebd6bbebb,0xf6cf2cdecd6cb6c76bfe,0x6ddeddadd6dbedb6cfac,0xebedfedfadf6deedeade,0x76f66efeefaef6edeeda,0x6fbefbafb6faefa6f9ef,0xfe2fdefdafd6fcefcafc,0xf6ffaff6ff2feefeafe6,0xf3fb3f73df3bf2ff1ff1],#[0x5774ff4fb4f74df4bf3f,0xf75ef5e75df5db5bf5b7,0xf6eb6df6db6bf5ff5fb5,0x7b77af79f7776ff6fb6e,0xdf7db7d77cf7cb7bf7bb,0xb7f77f37ef7eb7e77e37,0x9b78ff8fb8f78df8bf7f,0xb79ff9fb9f79df9db9bf,0x7b9faffafbadfadbabfa,0xbf3bdfbdbbd7bbfbbbbb,0xbfcbbcb7cafc9fbfbbf7,0xfcebce7cdfcdbcd7ccfc,0xd9bd97cffcfbcf7cf3ce,0xbfdbbdb7db3dafda7d9f,0xbde7ddfddbdd7dcfdcbd,0xe9fe9bdfbdf7df3defde,0xd7ed3ecfebfebbeb7eaf,0x7ef3eefeebee7edfedbe,0xfa7f9ff9bf97f8fefbef,0xcbfc7fbbfb7fb3faffab,0xbfe7fe3fdbfd7fd3fcff,0x6da579071a4793ff3fe,0x817600075a37907da079,0x9760580da772ded87282,0xa34447ba0574b9a01658,0x74a94976804dba49a887,0x6f1fd861895ba477481a,0x51e1873714976819c5a2,0x1e5769f89da70ac8ba48,0x9fa40b55974725e57658,0x9a40a27976074a1a7090,0xa90755b947d9e186390d],#[0x7421f5862dc8ba47882b,0xc081a07a89fa60b1e58,0xe25ba476c89a678cdba4,0xca3a30829d74995e9879,0x6197139e9764b5e5879d,0x1a147275769985ea80a1,0x76975eb867c959978243,0x480c2ba011895a718265,0x269e5861e2517635c1fa,0x3c89a078c4fa44a2e163,0xe9d7499e797609885a74,0x91746fded76465497675,0x5765d407a3012598676a,0xa479e79760794d7646de,0x799cbba712c07a36b88b,0x4808ba62dc43a700c9da,0x8149967094d766be83a0,0xde9861ac07a36d5e5863,0xa1a7095699711041a74a,0xd766c949768169f949a0,0x7343ceda30a265760414,0x67615b947c41ba49726d,0x7dca1a709c9da70cd497,0xb40da77640fa77514b96,0xc9fa49a44fa49f295732,0x2ba010e797609e198712,0x58678de18630c2ba0028,0x9712c81a0790b9a3151f,0x379003a4011e9769e981,0x4c03a4939599670481a,0x5e9d740ac82a97902ba0,0xa6d76138f3a308d83934],#[0x5a00a259762da6ba373,0x97673e517637c93a3799,0xa4752198412df5841aa6,0x394d4b967c9ed862c41f,0x12ded87141e58715807a,0x7085a745e1186824b9a7,0x9b1730581ba403e11867,0x8a7605889a72daa5742e,0x5760ad05a00d14576899,0xa477e75760c9fd8418a7,0x378e75760aa9f940b08b,0x4625d762beb57307489a,0x66d761814576589ed76,0x48ba6706fd63131ed870,0x557698a597670029a00f,0x57306e5d7627c57a34a2,0x7470e9d740a4a1a709ab,0x69a407a333521766ee91,0x6fd4576585ed8618e779,0x25e1872a8cda50a26976,0x15b96706817613259768,0x89a770275760ce817649,0x9761a1e9764b1e9862e0,0x960b5417660255760626,0x37aa59767709fa69a274,0x76757699de58736081a,0x5941765fc4fa4a00a1a7,0x2817627155a76f829a70,0x839712d4d76472a57427,0x5766c5eb867de77960b5,0x7646807a32109da70c9e,0x43adcba103d07a00a94d],#[0x5e0afa067837a081a17a,0x64e7a0316cda30812976,0x809a8216a3a49b821a72,0x87867b5d793493057616,0xba3880bfa6365cf8405a,0xa310853a40112f945689,0x82ed33a45405ba321c2d,0x1df4d930a851a73ec63a,0x6a7d7604427a359e7176,0xd0ba60b823a43b9bd971,0xe3a42ec5ba369d33a394,0xda606e73a387171747e4,0x848182da705e85767c10,0x407d6d760f45aa9529a7,0x774a9a71c685a1482cd6,0xae857649437a07fd73a0,0x61a882867a035284961,0x1d7641e61a05f1f17655,0x1763f053a452e018740a,0xa43c5a7947bd51766ce0,0x391045a73bc35a672421,0x8eeab8473436a97c1339,0x380ba94149ba365821a3,0xc3ba04a2e97601925972,0x43a427035a47ec35a475,0x5a847ea9947342fa306b,0xa01c1a19701b5ba01a20,0x5b8e1a62d131963f115,0xb972a970b256403025a,0x46e574406f17426dc996,0x6318413c65a453a8ba14,0x919743531945d4f5a30e],#[0x3a461c35a37ec0ba03b9,0xa327c65a819845a74e05,0x60aec364188aba07a0e7,0x8206a847d31a45430d9,0x420987142ada030ecfa4,0x6c9760d065a3539b7940,0x1874d435a076425a33c,0x7867ad2fa43b90da909e,0xa328d0da907b37940a68,0x450437a0866a176021bc,0x4740ba095009a73d0b7a,0x6463a34a261766328576,0xf2574956fba30498d969,0x9a90ae1586250ada743,0x9a833973947997393799,0xa96e839a919851a82500,0x90345ba3a0461a81a409,0x40a23a0202c1971382da,0x91b7a304cf5a30567176,0x5a19602027a367261863,0x61a34b61fa3556157617,0xba3259757646c09a0624,0xa35c459a81dee5a33722,0x8059bf936aec9a39a45b,0x45509a30c6c976995cea,0x99358684a89a14468976,0x459a38b437a084cada71,0xfa004ec1732b971767e,0x7a637411a9674c5a4511,0xa318cc7a64585ba33da1,0x35cc3a64a205a81aec1,0x812c1a718037a0750d7a],#[0x1453a434685a448285a0,0xa2f941b271765bc25a32,0xc17343e2d862d051a062,0x7a366334a40c10da705a,0xa339173a377671761556,0x3b10ba39a809a7a1e99,0x755d7631e47a01b447a,0xe80ba4211b59695d0fa4,0xa298624e05a82e2a3a40,0x21a332287a3480d5a724,0x5763ed2ba633663a4668,0xa3444aba077cafa067e1,0x78402fa902525768acaf,0x7800ba08a3057612ca9a,0xdeaba478ad5a047caba3,0x415a64c1c9960be29841,0x61a89f6617616d338492,0x3a4992ada42c423a32b0,0xa712e3f83438e7a42cda,0x35f289a743e8576758fd,0x5fa857675c09a05d263a,0x4c67a034415a6500b7a6,0x65a8187396406e85767,0x9a94e2a9742d45ba301,0xd741a3059712d3187240,0x7614421a43c28796482b,0x72693ba01f9a4947ee21,0x7d6a9a4709917623da99,0xaebba39b461a819d7176,0x1b9a06f551764fd87935,0x85a381109a30a1aba02b,0x564725c9960d42fa602e],#[0xa36f0a9a71a4bda45b9a,0x60b8ffa32ccdfa3061d5,0x7bd2d963f525768f6c97,0xf4f5a60319f9624c36a9,0xdf1768b45ba352c53a44,0x389873c0ba094a897644,0xfa31240ba04000ba82a2,0x76955f18729835a98402,0x333689a444685769f6f9,0x8ce3d8712c2da79845ba,0xf42da7038aba07a55396,0x533a3212a9742ec27a34,0xcfa1080e1a419cf5a795,0xba067273a05756576586,0x84133016347719632703,0x4184f9a31c1bf9353a45,0x4528ba3444aba378a318,0x604ba6336848679a8976,0xc37a077837a080cffa01,0x9ba03805ba35352d8631,0x1765a421a631d3194540,0xa40fec9a30b4aba079d5,0x38223f9353b05a712cdf,0x1c6c974998c1a675437a,0x943ba065199a36fa8576,0x4afa04d10da90734d639,0x9a90cacd7608a296464,0xba67836591070e1a0721,0xa387ab97601ec9769aca,0x683929982350ba699427,0x901f18723445a867437a,0xb409a95da05861a80ba0],#[0x2fba397c53a61f571a16,0x13a089f517305abd761a,0x3a63b22fa4a0a0ba04d8,0x98798e3a471909a30d5f,0x601d09a69af356499570,0x5b92976a1e1fa3549b59,0x64c1a64c00ba49467387,0xae5a4360e7a428c5ba03,0x15a65a8a9a37b90fa608,0x7a438439a066437a383c,0xa377abca379ac17363cd,0x96d853a32ae03875cc37,0x3799d943b4dfa602009a,0x48da08ca05a39ed9fa3,0x971a07b935867e6a9a07,0xba493e05761b037a982,0x3a6262bda3708fba34a0,0xa037463a0845a5962f82,0x34393194528f9a319c53,0xb409a8666857682b056,0x1c2fa4982cba40b6cba3,0xe01761e463a683133939,0x2da69c6857647b0d960c,0x1a0809a7947f56596634,0xa4122879873aa9867057,0x640c5ba03855d972500b,0x8f99d9736caba377e617,0xb409a454305631280ba3,0x6018742285762d4a9a07,0x9d9624ce3a449cb5a061,0x176291cd9608899a0889,0xa3a1021a433a717659a7],#[0x33c2e97695a85744785b,0x1e835a0729f9763f425a,0x8f7a30482da796e3fa0,0xda78472459a038cffa30,0x1d763e809a03e4fba073,0x1a92512fa433427a089a,0xa00aac18344065a34642,0x71c59a34e0aba678767,0x76d0da309c4ba03ac37a,0x9463a41b6017664685a0,0xe85a073917a349067a41,0x5d763a425a458409a93b,0xd96250bfa3a1463a37cd,0x9873809a3544d7a339d7,0x618171947a023a493a84,0xa50fa01013591a06c17,0x4863a82f1319715f3564,0x685767404ba65359d972,0xe5a726b256401d33a36d,0x9a058109a90ccc7a0428,0xa08ec35a67e4a9a07b85,0x376cbfa3a0c61a44b021,0x56289764ec39a743685a,0xc153968da71764d52976,0x8bfa3429bfa0540dfa40,0xbfa06b171a381d8d7611,0xc93538a9a0796d5a02e1,0xa386263a05f2c164189b,0x40ac25a35a5a78481437,0x5ec35a47e409a45cb359,0xff1ba047809a73480ba0,0x305734345ba322b2ba46],#[0x2d863a50fa108c59a603,0x7a14804ba65c50fa6085,0xa0500e7a03185ba33ce8,0x655867a6191a4947f439,0x4dd37867e45ba3245297,0xf0c7a05085ba61e427a3,0x861a34a421a03a8e3a42,0x85761a6ad642c2a9a376,0x5a726d09a69968976186,0xa36b937867d533a33b8c,0x982a2964031299817027,0x38039a446e87a376c35a,0xf1517666530a394e99a4,0x4d5a736e17a62ae29643,0x25a91ed35984b909a60d,0x574014b7a43ae05a09fc,0x841802da996453a461b2,0x73d437a085a03a36de3d,0x1c6c9760a5339352c21a,0x8f29632d23d8413861a8,0x839a3511719378263a45,0x2d7326a617630467a32c,0xba379ac9a30b009a98a7,0xa30d8c3a6750b7a4608a,0x7684ba63b80ba929d09,0x955bba06f6c17343aa9a,0x4ecba39a4aba0785b597,0x28786799f9761f42fa40,0x72a9736c9760bc61a67d,0x1a4574c7a328285a4739,0xa47d6ed86702297441e7,0x657dbfa016017a659c35],#[0x2690ba4999a7947ecbfa,0x75759765dcd96086f176,0xa23a042ec1a01e1b7949,0x897619909a60a6ab941a,0x3a493a717662e0b84442,0xa661caba47985ba32245,0x60b2897644a85764844b,0x543057326c67a0532c99,0xacda707673a358e3fa0,0x9a93f823a44a1f1863,0x53a459c23a4650aba47a,0x9747bc2da90257176724,0xa41bdf1871710ba90aaa,0x49c4ba8a180ba394ce3,0x8a573947a049a63bd17a,0xa1cda70585ba3415f176,0x535a154d8d7698684867,0xf1764e26176296a9a670,0x5867d4fda3198f9a31c5,0xa03a125973f88fa46793,0x3481cf860584ba8a1451,0xc0aba61aa89a344685a,0xb461a84b9b5970150ba1,0x827a33ba87961aca9a47,0x9ba0576bba30e099a488,0x5861ad717675d2d97254,0xa40c063a3836098618e0,0x984515a01c435a47f737,0x8b67d769b0c7a050537a,0xb53398291c9969ac09a9,0x1aba0260fda716845a78,0x21a63a453a43cd0ba30c],#[0x9a3359b7a39818793520,0x97146b9760400ba68f40,0x608687a076c09a864939,0x13509a90a40ba090acd7,0x2c99a367687a073b0563,0x261a35f287867384ba65,0x37a06f5a3960228ba04d,0xfa342e617666f3794994,0x76832a9741a409a72221,0x829971a3775859740605,0x3392d97174e3a62d12b9,0x673a34d18d7605c39a0,0xcada0674ada72b8bda74,0x5a81a827a3650ffa314,0x796634dfa398a897665e,0xa73e834a97c02da39c96,0x63c925768fd99a06f859,0x500ba333453a43dc4ba,0x205ba32100ba68ac59a3,0xc67a0536eba498e71764,0xf1a4283516306c67a034,0x19682c5ba36197196786,0xa0821c9960d286987397,0x1541517689687a473837,0x5cd33a36b809a903531a,0x9c5ba342d25766e059a4,0x1f9872502da90e515a01,0x618737067a052f196349,0x7a0260f7a39822984156,0xa32c68ba04e5398723ce,0x4352857648d71a9734af,0x81d2d945da857676053a],#[0xa4a9a37ae2ba438571a0,0x61fa6364ada36874d930,0xa9762d1539668d71747d,0xb834744ba6012ad762b6,0x9712e997624d358683a3,0x672137967d0a5a70e5bd,0x930b7a65f4bfa3604e1a,0x117196780a9a776453a4,0x8d7a3399339353d91935,0xa9762f909a60d02da30f,0x5a813c09a3623256495e,0x769c6ab9447ecb960b46,0x34312d8725db9637256d,0x8ce3a471dcfa004d87a,0xd5717683aeba406753a3,0xe23a6284bfa35b051a73,0xa976722c9740b9b79695,0x9a07b2c8a90b68798482,0x762bac176139bb937bca,0x73e929963f899a762e89,0x4950fa606c09a03c5319,0x2ebfa3799379875463a8,0x85ba394d3ba033705a21,0x33a1542a176961a7a471,0x176582bda31adbf93439,0xa66e0e3a4746f9760167,0x62dc27a394ce5a62b40b,0xc05ba364063a32f6a99,0xf6cd7607685764bd0ba4,0xdc9a911287a448135989,0xf5a701421a0601679387,0x7a63745ba41eac9a10b4],#[0x946d88da38c863a61b0b,0x32e9539688da1979592d,0x36ec9a60b0dfa40f3414,0x28bfa35ac35a67d6e576,0x88fa48bdc9a111467a02,0x47a33285ba34f40ba61f,0x5a446133a31f859a81ec,0x9669a39841a053a49106,0x70190da90952f863a553,0x97809a83c00ba48b0dda,0xe571a970aa98447e7d76,0xa8ba06685ba35c285a39,0xcba49a409a85a5339452,0x5a01aecf6407c8fa48ba,0x6463437a971039a04fed,0x182e61765fb05a314299,0x829aba428da19696205a,0x500ba45e461a88423983,0x177a0661f1765d92d945,0x71765d45ba352609862c,0x1765f67d760e63b934b2,0x7405a3c9353863a39f26,0x73628ba065a8576749cd,0x85ec17365e8ba0482718,0x3acda4080e3a471037a0,0x845a74f9359683009a92,0xbfa0362a9a32dd29765e,0xfa483409a94facd7606c,0x93685a7a37f9f1861f22,0x41ae85a0802a9a42e175,0x2b4bfa342e01765d4aba,0x32d574130c7a64563186],#[0x53a0396a97447535987,0x73a365813a36d063a0a0,0x7a438971768485ba3552,0x944b42da39da03a34d8d,0x328e7176579f1766da2f,0x6af3994078c5a1510ffa,0x6d3ba0212c9a39a039a4,0x1318492409a84fc51a81,0x1861e171937980ba394,0x9a49a451a44f8ada4686,0xa05742fa412039a064ac,0x385e05744b059a741e71,0x336897627b2b846fc37a,0x25bfa314d917643530a3,0xc25a35a82fa311c09a3a,0x31a654017a64a00ba817,0x1a02a8dfa69615196639,0xa050f4d630a533a3336f,0x6488e3a47528976458c7,0x2a42da60f571a37ba857,0x5d0ba60a705a015809a7,0x92f961f6aba4852b9769,0x37940cc9ba379aed962d,0x9760d453a6259f3a632b,0x9320661768743ba04f6c,0x34a287867a00ba455dbd,0x41285967098d9602427a,0x1ec9760a909a90a95197,0xb5a361605879f5b7960,0xba46e44ba332453a434,0xd632b6a9967052fa0570,0xa71ec37a6849b99382b2],#[0x33102fa39905ba351c99,0x149a79475837a385453a,0xb445a75a05ba3350ffa3,0x40ba63fc0ba8418e7a62,0x5ba36927186381679465,0x57412c9ba38ba7187420,0xa63b930a36d605767d30,0x81568ba444571947992b,0xaae576248c5a743459a,0xd685764bb19a10050ba4,0x2897643cfda01ec2da49,0xcda1081bfa328c4ba420,0x3a82d759631312d948a6,0x747159fa4368b7a46046,0x79640ba3565717475ea9,0x368d1a519c5ba3a216d9,0x44e1a32f863a81bcd7a4,0xc0ba68ff0193478fba37,0xaba078835a07f009a81f,0xfa408ca9a71c0e7a4288,0xa9550e3a44a011a76650,0x308263a44e445a76e809,0x7a6a9a62dc61a81c2cfa,0x684ba634435a0760aba3,0x423a037a63a48702fa69,0xcba10b467a328453a63f,0x5a351037a071809a421a,0xa36c27d760dd0ba90a4c,0x40b68576499759727933,0x57e1d7615c65a06eac9a,0x59f1873ada3969627176,0x809a333e61764e9ce980],#[0x71947b671761edcb960b,0x59848059a66440ba36d5,0xa69a0dfa49c171937ae8,0x635425a48912d973eec9,0x34435a07f5a99432c09a,0x69339454311760585ba3,0x8afa0680bda05ba31872,0xa3a403c51a45a0dda795,0x7a04780ba39045ba33dd,0x7643a85768422fa48451,0x70584ba661abda373689,0x22d679789017a64f5cd9,0xfb056314971a077465a7,0xc59a05cca9a47ace1a62,0x9a723193a043021a35f,0x9a30cd2d9816dcd76058,0xa0214c7a0431f1766e90,0x9481bd7343451a362839,0x7f809a63e329932d284a,0x3c9ba387e1d87405a7a0,0xf414327009a917a89761,0x617659125981f035a072,0x987249a3a406ac9740aa,0xa457463a07e22d841a62,0x613061a056d15a04ba73,0x26c0ba3124dfa49ced57,0x312d87265919726e2187,0x601871582da41043ba04,0x9a0a2827a36d463a32e,0x5762422d867202fa9964,0xa40b867a021d6d970258,0x619229743e971947ad0b],#[0x6b069a454321a029a097,0x71d1969bc6ba3619c194,0x8b1a08c595a4515dfa06,0x73a4132d9a07360da48a,0x3a61311ba074519a61cb,0xa398c69a81d227a65377,0x410069a34ccb1a468b15,0x171db8475dd3a3069d19,0x706ba061ceba35f625a8,0x635862fe41841ce8fa08,0x63a32cd3da49471d961c,0x9768286ba34f53da38fb,0xa062640a35353fa3336d,0x3009d1a306a0da46dc69,0x6a469a4922db961af63a,0xe53d849251fa06a8eba4,0x5c1a1925d9a47d53da46,0xd1960ef55a3045dfa04f,0xda108edda418e8d764f1,0x9647913a30f1c1a46b36,0x59f6da608643a352f1d,0x331afa037997a66506ba,0x93d84945afa32b1ad94,0xe4d84134c9a4515c1942,0x4fa069119a91a637a32a,0xda696371834928da0872,0xa332c3da08eb1d9847b3,0x46886ba3351d1a904763,0x52ceba4911dfa065179a,0x68b1a38c13d94540cba6,0x91da1538b1a48868da36,0x69a44cb15a497f1f9847],#[0xfa0535c3939113f93618,0x941a24998489d1949d11,0x4479d9961bb23a051b5f,0x1a11da45393d9820f1d9,0x997994885c1a49275f96,0x371a9130eba331ad9947,0x60a332dd9a37ef21a414,0x3a38bad1a40e2d9a168f,0x9447ad3a30eb09a3424b,0x37cb73a9130cba05b31f,0x85225a45dd03a3696dba,0x2d1760ecc9a0612d9a0,0x1dfa328e8da058c6ba33,0xd1a39bad9a17983da68e,0x793605dd9153979768d6,0xa49b4eba4695dd916ad9,0x382dc1a4540cba6536d1,0x9273fa40fcc9a45b6d9a,0xf64fa0535d986725c194,0x60d8733235841d197a64,0xdda01f30ba360721a042,0x18490e49961b5d98675e,0x8682ad9a847ed9a32e24,0x366b08a3606258633249,0x52f09a415919a37ee8fa,0xea8da34e4eba4915c393,0xaf5a429869a6356d9a37,0xc18492649861ca4d9153,0xd949468da465901a45cd,0xa332a41a45428da44d13,0x58f09634c747944760f,0x6051fa34ecb3a08be8fa],#[0x3119a07f5c3a3670cba3,0x249944b03da08693d945,0xb3a0881c194541afa465,0xda83086ba41dad9a37c8,0xa086d1fa06a2439352e0,0x41bccba66a5799487c3d,0x1f33da3061d19410747a,0x7b3fa40f2d1769bec5a3,0xd7b938ba4393912b3a46,0xd9a41af5d961a227a652,0x5945b51da46af71a6132,0xa41bd3da455d1ba41bd9,0x452e258620edda030b44,0x2813d8492ec7a3798eba,0x519594515c1a154321a3,0x4cba060b15a4049c3a36,0xdb8679a43a351e43a353,0x99682b479475ab1a430a,0x632fec7a38b93d98331d,0x61a64fa328637a452f31,0x52edb867a0e9a38ef1d9,0xf75d941a179768e24fa0,0x5db8675f3da602103a34,0x3d8493e419452b69960a,0x1a4105d1a41043da68d5,0xa48928d76594c9a360d1,0x38c3494327625a455501,0x4c53d9635763a328d799,0xc1959360641849264383,0x9d98475dc39391519a91,0x95945086ba0929799468,0x163276d9a61aad9a3851],#[0xa05fa49861b8eba62ff2,0x664ed99179a4b961b4eb,0x1d6d9761ba4b944b31fa,0x5dd9332f15a30646ba6,0x11fa052d79a4885dd942,0xd9a07eadda32c643a369,0x9960a903a36a347942d6,0x966913d9493f6ba30c36,0x4798cba6918eba039e27,0x58eb1a330d3d93622d9a,0xd28f9668ed9947a28d98,0xf6b960ab69940a86ba38,0x3a059b6fa608595945a,0x1a399225a829b6da408d,0x9467d95a45b5959360dd,0x61a9c19490ce9a08ed79,0x1c53d868e11fa0696d99,0xa53d868d6d9761cb4794,0x64194542d9a347d1fa06,0xe9a62fef7a4505c3936a,0x1a997979938bac4a38b8,0xa362345941a60d8720dd,0x4541d9a383e0da44d869,0x69e35a63f53d949353da,0x8b6b940aa41a154243a3,0x709a3171c1a16b33da39,0xd9a9735dda414d19a91c,0x1a30e9d9961ca4b9848a,0xa3622f5a32ab71a4132d,0x81f2c5a41e36da60893d,0x28f17a30660da38f20da,0x1c3da38e5c3a34f5dda3],#[0x625a442f21a01724fa05,0x37a4910cba691643a352,0x3a64571f964786ba08de,0xa34e6dfa068f55a397b2,0x81352066801b8000028f,0x67282cb41337081a0336,0x1d09c0846d620140e820,0x11b5b0cd90608a2d2c15,0x467d219a8ffe079ac39d,0xb8a52b327c31317c9286,0x80c3e65ece2de29638ca,0x9c584dc946b41340d194,0x51f500f46677583a4c,0xe7465a225ad0cc683894,0xa9bc64c4ca577d25d68f,0x561aa8335280a87cd3da,0xb516f4eb4a758a5ab875,0x3b1da58850c1495f1dae,0x6b2034e2da152cdcd655,0x5777111b7da9b91ed963,0xaaf23a7784baefdd108e,0x60358fea27db9be1bdea,0x44b21bf50afc83f34132,0xc84723a332316c889fa4,0x4944149972483522198f,0x32f098574bafa595b2a9,0xb513b4c9c97cdd5a6a2d,0xce8d1d444ca106cff2e7,0x544869e054cf7a575d22,0x30aa2a14699463886200,0x66176d6b404af153ccd8,0xaba989fe661322f85000],#[0x59354d051cc32f6382c8,0x2d09aa14699343988400,0x635715773cc7703bacd2,0x2dc99a1c7112e3506200,0x60b6452f36c7b0bbbad5,0xafaa3236759603d8a000,0x6376e55332c70ff37ed1,0xac693204691423304c00,0x5a54eccb1fc24f4390c8,0xa68819bc5a8fc2985600,0x5c54ccab12bf4de32ab0,0x2faa5228711543606c00,0x67b8158d524cf10be2d5,0xabe971f86b9403707400,0x5f16552735c6d023a6c5,0x2968c9d8590fe3106800,0x5a94f4f324416ea35abb,0xb2caca3e7195e4588e00,0x6236ed673d4a711bece8,0xb22a92306b13e3188400,0x6e9a463170d3532432e5,0x2e69b21a6812e2e86600,0x60f6ed634accf0ebacd5,0x2bc921fc641363184a00,0x5834c4e526438fcb8cc7,0xad29c20a659363686800,0x5ef5cd2b2e454f9b8ac7,0x2d8a11fa6791c2985400,0x5cd575012844d003b2d2,0xaf89ea0e769624188c00,0x62977575424b70cbeee0,0x2ac989ca6092e3784e00],#[0x5a957d232f436eeb5ec9,0x2bc94a005d1202d06400,0x5b753ce527428f9b7ec8,0xa72831c45c1262905600,0x5cd60d2136c68ff394c2,0xa70849b4589002804a00,0x60966d192ec56f6b68b7,0x2da951e86592e3087400,0x5df60d3135c8d0537cbf,0xa3c7c98e4e0ee2585200,0x53534c8908bc6daaf29d,0xa3c7d1a6569083087200,0x5cb544e524450f8344ae,0xa7e819b6581062804600,0x5f96ad1929c5cfb37ebf,0xada9b2246a11c2984200,0x60d6553f39480fcba4c9,0x2b0931de5890c2c05600,0x5d7594eb23c53013b0d2,0xa868a9de5990c2e85800,0x5e95d5032a40ceab46ba,0x256811ac5f9262a85c00,0x5172442cf3b8ed2af8aa,0xaeea7242731443385c00,0x5b35b4eb1f426f9bb4d6,0x25e7f9b25711c3485800,0x5dd605252d470f9b32b9,0x2cc9f2005e1122a85000,0x5eb67d2d32c5efeb8acd,0x2a0959ea6c9663f08400,0x5a949cc3163f2e6b64bd,0x2b8989f6611403286400],#[0x5c1584e722436ff38ec9,0xac6959f26714c3886e00,0x5a95050122c34f839cd3,0xadc9a9f46412e3186c00,0x5a957d0b29c2af5380c9,0xafca6248791784706400,0x5e95bcfd2a44ef8b9acc,0x28e8d1d6609062d85200,0x51f36479153e6df31ab2,0xa4a7e1ac5a1122f85c00,0x54b3cc8b0bbb0d52f6ac,0xa8e939e8661362d07400,0x5b151cf928452f839cc5,0xa9c94a066d1182e85400,0x5433f4a517c10edb58ba,0x34abda68731403706800,0x6958d5cb5a4c3143feed,0xa7e8c1d86110a2903a00,0x54b3f4a316bf6ef34ebc,0x27a879be5b11a2a05400,0x5c759d0122438f337ebb,0x26a77980491022504200,0x64b6ed653c48d04ba0bc,0x2a28d1d45a90e2b84e00,0x6136c51528430f0b7ac0,0x2827f9a6570f62f87000,0x5b7584f119c1aeb334b7,0x2cc9a9f2619283205200,0x56d4ecd119c1ee8b74d2,0x24c7f19a500f62906000,0x5192b45b043aadb312a9,0xafca724e839a04389c00],#[0x60369d4b3f4ab14be0dd,0xa96971e6651262d05800,0x5c54dce32141ceeb60bf,0x30caca60759603408400,0x5f363d3139c7d063ccdf,0x2b8981ec6511a2f04400,0x5c55e4f31fc24f635cc1,0x2b4921f6651403887e00,0x5d54a4df1b404edb38c0,0xa4e831a0560fe2e06200,0x55141cb718414f5364bb,0x2dc9f20a679202e06200,0x5c76552538491043aed4,0xace961e8689483e87400,0x6116b5633dca50c3aed0,0x2b09821e6e9283004800,0x6296451128448fdb8ec4,0xad09b216679403408400,0x5c95fd213245cfe398ce,0x266801924c8d42684000,0x5fb5fcf520c0aefb54b2,0x30aa2a346c93a4287600,0x66d7ad7b40cb114bbed6,0xad6a2a226793c3906800,0x5c35dd052dc6b033dad7,0xa487b1a0541062b87600,0x5693f47501b96d6b06ae,0xb0eab2246e1563706800,0x6296e5673e47b06bccdb,0x2848e1d05810c3186200,0x6195f53935c70fdb96c4,0xab4941f66212c2d85000],#[0x60768d4b3947f023b4d0,0x26c8a1ca6093e2f06800,0x53937477053bcdbb0cab,0xa7e819ba550f62a05a00,0x5453947103bb2d3b12b2,0x25a841c85b1182e04200,0x52d2ec5f0c3d2d8b18ae,0xa6e889ce609303308800,0x5c95a4f921c20edb5eb7,0x2e69ba0c6a9623b08400,0x5f56352732c630b3c8ce,0xa6c841b4539223707e00,0x5553ec9904bb6dd31aae,0xa567d180498dc2405000,0x50f2ac4cffbb4d9b08b2,0xb1caba446c9362d87000,0x63b75d81474b510be0d8,0x2ba9da146f1282d04c00,0x59b4ccd318c22f0b5cc0,0x2be889cc5f1142905a00,0x6336fd4d33448fc392c8,0xb32aa2486995c3787600,0x63b7957d454b3113f6e6,0xab49c20c6d9423787800,0x6016fd573545ef7b46bd,0xad69ca2c649202e85000,0x5c756d1930434f9b86cd,0x2da9f9e45d9142e85400,0x5e95e4fd2545b01b98d1,0x2a295a126d12e3206400,0x5bf51cdb19c06e9b46bd,0xaf0a6a507a1723b06e00],#[0x5e1685553b4810439ad3,0xa50891b45290e2e83e00,0x5ab4c4df143eae332aaf,0x29c942106b0f82a85e00,0x5d15ed112e458f7350ba,0xac4962046d1242d87200,0x5d35a51931467023a4d5,0x2c0962146c1303106c00,0x5b54ccd11bc1ef135cc2,0x274861ec6d1504305c00,0x58f4c4c91b426ec33ab7,0x2d0969f65b9103186600,0x5e76052533477093bacf,0xaa88e9d86112a3687800,0x55f47ccd2141cf3b94c8,0xa90909c66190c2f07600,0x5513946105bcae0328b9,0xa4e7a1a0551123306e00,0x5393346506bcade342b5,0x2bc971b6579062e87600,0x5b74f4cf1cc14f034ac4,0x290911fe6793c3386c00,0x5ad57d091f41ce3b44bb,0xab29aa086b9082d87000,0x4cb23c4902bbee434cc3,0xa0e7398e508f62985a00,0x3e6ed37ad0af8b5a9a96,0x9c460942418c41d03200,0x42af1388cb2daa924c84,0x1c06694c490ec2685c00,0x404e5b6ec62c2a123a83,0x1ac601463f8b82205600],#[0x3dce3342bf2ac9d2427a,0x1d25f940430c82105c00,0x3fcf2380ce2e6a5a5a89,0x9ee6613c440d82284000,0x3c4e1b3cbdac2a7a6087,0x9b4601363c8c82283a00,0x3a2d9320bc2aa9822278,0x9da6995e450d42705600,0x459093e6e2b26af28290,0xa1c76976510f82c86a00,0x420f035cc8ae4aaa7490,0x9f0671704e9083105400,0x432f5b90d931cb2a788b,0x1b65f9283b0b81f04200,0x372caaeaada989523882,0x1f66d956438da2084200,0x402f538ad2b0aae2808e,0x1f26793a3c0981c83a00,0x4710cbeadfb40bfab298,0x9f46c95c460ca1f02800,0x410f739ed5308aea748f,0x1ea6913e418b21b83000,0x43af7b94d330eb02848a,0x9dc651463d8aa1f04e00,0x41cf4392cc2f0ad2748c,0x9f067150428ba1e03e00,0x426f4ba4cbadaa826488,0x1c060140440d22484000,0x404f1b84d2ae6aa26281,0xa107296c4a0dc2784200,0x422f8394ddb38be2a898,0x1c2611203c0b61c04000],#[0x3cee135ac72daa0a3484,0x1b46192c3c8c41e04200,0x3dee3322b8a9a94a2c7b,0xa04709884d0e22285000,0x402ee384d1b04b8a9695,0x1985611e390a61d84400,0xf00dd336baaa69b22076,0x14828831d0c16380f83,0x90cad8606562384616d1,0x83d81056e11c082f0820,0x823092255c1e08e0d223,0x507c07c51386e0601ec2,0x11a0742b8792a00dc2e1,0x12d4b018d2c2828441f7,0x1002103a2c011584088,0xa82c138c201dc1d23be1,0x8292cc5ac3a950614588,0xaf45443984b06a23c0e,0x216ccb18a0a82b083e84,0x7d0b41543a0a023689b1,0x44c30f0ba1d8a8a142a8,0x4385e14c22c20928615,0x2126108c441ae121541d,0x1b05b07a0f1628c02778,0x8634185aa1f0c506f052,0x78149306cc270485d186,0xe09d504c3607c22a28e2,0x9415787d8a149441c580,0xe1b4041c10f02a290910,0xa12205a07838262068c1,0x3cce11c8434241e301c3,0x4222223e4b382084306c],#[0xbec292281e930150229,0xd60965841e019128bc92,0x2664c2c994a3a2ec9080,0xc0a1e60d51e03d0593ec,0x20c50d72c00485286246,0xa02609e87282242276a8,0x185144bc4458243504d4,0x463a565060b450c15109,0x4482ca91320250e41886,0xa0c08c980e9240511686,0xa11141a74158ee048850,0x1330521289919836618,0x426c4dc508560ec8311,0x3861e43408d2801b4be2,0x28e9004da16c0ce18509,0x5194a22061308210b404,0x19ac26220a1b606428e5,0x2841462681a8d04f0921,0x31f82a852b0b2ea1c449,0x811f8a7864488251e017,0x64d130b11e8ed0da0882,0x8f80b27063456d8a8034,0x28593a27e458ba904236,0x29020659148552602281,0x280cdc009e61425d5138,0x4184b14424d64fc4d947,0x9470c4e1f64014e05237,0x83515417183507931c2,0x9d1700125804091ea0d4,0xc61018d0014234094992,0xe4150ba97e2e20483201,0xaa8e7f01caa8043c8792],#[0x955008701efdcdc03ca8,0x2239fee5da4021dcaf83,0xfe47400d28f7eb294900,0xc073ccfaa980a82fa789,0x8ad80447df8f9380a54b,0xfb4dd1d63001134a3c18,0x21021663f79ef0090aff,0x87eef9fe7ccc03418dfe,0xe506006b37ff9a9df100,0xdf92524005467f968393,0x440443b17cbb04281d9a,0x23a37f0801a45c3ccaf0,0x2043edeb41b9a40a68ff,0xbfc29a0202989e4cd0ec,0x27db00688dac1fb00672,0x85f7343a004087a2f94,0x5087f4d72033e3fc7934,0x9ea3d7608008a0f8c206,0xa008467c1bf810b8e9ff,0x80044a8d7ffc18048778,0xc6aa400d0ef06ef8a85f,0x7001106f87610216a5f,0xfcf5e2ec1021c9fe0cc5,0xe6b1804ad7543da410ca,0x8be2fe7ce78804428ddf,0xde90014d807d98222043,0x220891c2d0ec029b4e22,0xb088089b7ffa102f0200,0x197e05a02921c3ffacb1,0xd3a00cc2abfe40d00811,0x8011063577b9a40a6ced,0x7f60d55019c9fc0ef324],#[0xace178f538370b100557,0xe250ee8217de192da021,0x8002263f9f71ed910034,0xfeabd00029b5cb69ba12,0x3329fd4ecf041014f27,0xcd1f5a600a00d05f9670,0x799916c20439077fd120,0xcfec951bc305c0089c,0xc8cb434e00119dc9b3e4,0x87d7543da410c2f93f18,0xef1f001116ffbdb10000,0x852fe703880068c7fb34,0xd9d6dd3c05383f54bf40,0x88c37064e03d510215af,0xa004421f4b1ac896080a,0xdcc2078010dae7e9bf0b,0x21d1fc6db011c0600229,0xee981001114fbe0c4970,0xfe5ea86a88008817ff16,0x237400113c07aa2042bb,0x329bfd2a80110cc3fb6c,0x7d010d860fba8080a6d2,0x10110f7a2101484fd449,0x62272021b9fba527fc1,0x1032a3ffef85688087f7,0x50810deead3c004307c6,0x880ed3e4019a1f928,0xe12bb80408717fe86887,0x8202170e509162014c2f,0x814a23996901880ffe1,0xf36fb8345000882bc6eb,0xc37c0080a40767c42042],#[0x7e19d019e5ff8b4f0010,0xe042fdff12860c053521,0xe4693f16fe801ab98ff2,0xcc758043ebaa1ed2086c,0xbfdcaf8395444044d3ce,0x957d7579005688400458,0x10e2f8bf9b95ef1008,0xa23954440445bfead420,0x53e79dbaa47a7200d5cf,0xb231c05359cef2309000,0x43f3f80e5102011142df,0x4c587302189e4cd0ec20,0xbbd11bd2286a0054ca,0xed6600227bcb4a41801a,0x25e126006a77ffaac07,0x1100044443e020cadfcb,0xe1c0ed910034fbff15db,0x801104c7ef9782021fbf,0xdfc5a0005333fad87d43,0x400d257858034c05329a,0xfdd4f90066a466fe87f,0xe9e4c00344b9be086801,0x98008b2fe9c680067a97,0xe09b80a630bd3f5a610c,0x5309c4f8b2a014c67c0,0x57d3a840852bfe521f68,0xf800435bfee32ba2c087,0xdb89901743001150f8a2,0x6404319fc6a8d1c0536b,0x761021ebf480c84fdc66,0xba307971f001104f2668,0xf9ed20874cff6169033a],#[0x40d1ee68761021a5275,0x39bd1cfc085cfc35fdb6,0xc46002246f9b2c842c05,0x6fd07d4400341b8dbfd4,0xc54d20c00d3d0fdd0066,0x54dbd7e517ca0004417e,0x226af505234b98b000,0xf22802151f57f6280ee5,0x11022241ffa1cd2012bd,0x9d9e082029c1e9e5f4a2,0xd9de5d1118008953fa,0x92808577db9bef845811,0xbf021d9d9fa88810c0f7,0x14e41fa74019b5d46b1,0x38d4420294effd500841,0x34008a6fd6d3c680069f,0xd042002271feca605426,0xd473cb04c337ffde32,0xfe215c10f16f89e136f4,0xfe8a85fa0180089669df,0x8917e2c88e9c002225,0x8dc0204433abf80405f0,0x21218a143001162fe129,0xff1b029c14004503fc1f,0x8a8f790637e001a4de0f,0x4053fbda1f8beba01800,0xa5b3f8801a3091f81980,0x74420292de0e801021b3,0xd100a5f7ea87a6b010fe,0x88ff23a47ac801a6ae46,0x80501108f2f3322d8408,0x5038bd130215dff6185e],#[0x6380a7af6874268ed803,0x551fe9c910d2d1b7ada4,0x22b02fc7d4af808c004,0x8008627b022ff7864aff,0x471021a30dc190deac1f,0xb2086aba9a8402955ca6,0x2219f0b0810baf9fd85,0xb92000a787efff84c221,0x11147f525400a5a3e55c,0xf9546042f3d534c9a08,0x5004397c61c385d160d3,0x3fc5ee1332043fb2663c,0x27a021338b67a7aa0347,0x89010a6ffc6150810dcf,0xee8410a5e3ff74141bc5,0xc0345bd1e4c9002191ed,0xfc2c231c053a7c9836b7,0x180219dcddf82c086a82,0x7fe281e8a302225f9b75,0x4900433dffe290000a60,0x223dcc5f0085a7fe6b,0xb8f1f500067870f68440,0x5c010d2578acc9990223,0x7fc647380804423ede2e,0x8cad208088cd57e60668,0xa40066ae4d1c1951fff8,0x58034cbff4c10215bff2,0x2b522d68225baf6fe284,0x1134ff1b3800435bff99,0x8802969f3a7ff8c06478,0x996ebbd520a0088f3d70,0x7ef440cd5ec5b89f9006],#[0xbef30021a6793400c46e,0x7500a5aa7915212068d1,0xd3e483cb16601a9efb80,0xc0044f9de0bee182029,0xc3ca141130ffff4f4e06,0xa7e94217c501a198b445,0x3de88838bf8381386080,0x82280a8c76c646490022,0x4164089203645fcae34a,0x22f864806080a70f87a7,0xf2a76420006a87e12021,0x48043f3e49f202143cff,0xe3f869e0010fafe7ea85,0x10e8d803537fe54c0cb8,0x408a26eddc810adfc314,0xf9006675dff96caa4915,0x2d82162ab2aa40a52e14,0x8ff5eccde42b1022b94b,0xff5c2044575fcee0a3df,0x98c08619e30228b0032f,0xfe02908746c01abdf89b,0x534367edb007934008ac,0xa4cfbb41924f43a05000,0xaa737c7e88115c7d6c36,0x19acf248c4000a6472de,0x7e284e4400220bfc0ef8,0xd840002289e8f82c0855,0xd5f0f076066579bf613c,0x120002992ff084436014,0x8347a4fedb04086bbc2f,0x888f119832a7f06f9504,0x99c281989fcf93860500],#[0xf4824b3913ff449021fb,0x4a4f47c16042a133ff4b,0x48d6cf5704893ff50b01,0x5006567ff6f356f10004,0xbb032c22c7d8810ddfec,0x22ddab0383db043d7e8,0xa02a6df9fe4dad9c04a0,0xad82043f52bfd481161a,0xf0e1ed0880004438df8f,0x7f2021268b43105e0014,0xc9021700e8ed31010fe7,0x31bed47090242044fbb2,0x34acfd444086e9768503,0x7ec41803413fe585c604,0x79c010d15fe03a0662a5,0x34f45bffe4006767ee7,0x2ad30202a53f41b5bc84,0x92997a14404455d8f486,0x2989fc9f018ed8008987,0x1c3c830067b3f2a62040,0x8783f4c5ea0c20c05466,0x7231404403ff88c88a40,0x3bffccf5102069c7b7e2,0x9dbe20010edf4e008198,0x52f7ff68ac5103443fe,0x1c9d4124440887bdd27c,0xa6a3d317b4aea4022a,0x229cfd5e444830202a0f,0x2a19ffff81494584240,0x77fa7a0a2cfa4a834b04,0xcae280a5aff94500033d,0x800046d7f82bb440d197],#[0x40a5d792ae9fe1c81390,0x38033a76edc0cbc5c93c,0x34066c7b4aa442b77a71,0xb57ce3b43a05307f4c1,0x480351deee28f5679081,0xde2b1440d21c3e3dbd8c,0x5293f82602010c1edff,0xa89063e800d247f6a642,0x54eaed010e954e670484,0x22202209f8378c0218dd,0x32c7f92910332bfed51a,0x42cb50f12021b3b7f30,0xa4c7a733810b0f0f63,0x5f9754820c080a88a2f1,0x8ce7cbccac9676400453,0x29cdd5f5fa2138617100,0x94fca028fef171030800,0x5598c6a087cdbfb60019,0x4f307fecbc72f02211ff,0xcfdb41962bc3df884803,0xf896029a9936702010d5,0x2185d58f24810d56d29,0xd42fc677c10bce72c13,0x404001125db869b9e0c0,0xdf2c00400150efe9f9ba,0x6893a8ed76c1411187fa,0x7e4800a4efcbfc188300,0x1b63d17fac32400d2f,0x9e2d42e7c6587c6a2440,0xa445878fa42210218d86,0x8c089143e1fea00218d7,0x611d8800456bee06d7b0],#[0x5045ed1b1c1130fe14f6,0xdad820440a54f6042c3e,0x10089cfe090819a5274c,0x9e92e80429bf65df5048,0xe77f2340af2808402a6,0x3b3c4204373dbfb6c381,0x6c800441317dae408636,0x219decdc4042b3f93e2d,0x2df93205810caf142280,0xf915340665ff53d50012,0x1108dbd71078100044b7,0xb7952c087a6a658d4764,0xd7d72f4ee490001b15f1,0x9019b08fd9cbdb021c3f,0x203248dfd044854fefac,0x8f04436bebe4580cfdfe,0x2f80cd0088a7fbac0af5,0xa840860d443ca0cc8f8e,0x904d7ad9e0008747845,0x457f8c571419c46281f1,0x61205243f82aed95c004,0x420439dfa9cea814a47e,0x35bf64544010d687fa48,0xbb99014da7f89a30c05,0x3f8f8d5422c84022fe23,0x160111d8f51f00067178,0xe58534d901a40efc41f1,0xb178219bfca3b4066a87,0xa8044c2aa38208587ac4,0x756966014a6e5d992a65,0x66a7d51890086eda0c6f,0x146eb4dd554bdf836100],#[0x2607dbed81989f11fa02,0x4010c87f86d47007e2d4,0x6adcfd15680a617ebe41,0xa0dfeffc5ce86b490022,0x68cfa4ecdff4d1088dab,0x5e660818223bf8a36220,0x2a5ffd04864c0044539f,0x402259e243edf13b6d02,0xff514800cfefd58e485c,0xd69a00438b8be6502153,0x8113d9bfd51810c6ff04,0xfff7a4023d7bb50328fd,0x1154ffed06525021c2,0x6f9f10210de3c302b722,0xb53140cf8e2c3112010e,0x933be1c30ed0600d41f3,0xa03307c61032c1c5237a,0x40862cfda88198a83fe7,0x1e876434008987f83430,0x610239de766c042a3fbd,0xa9f60fd7adee2e2939c,0xbfa08c17e619a3589eb8,0x43143cb2d6718034e54,0x67e493dd20ce4f86ba22,0x3e401989f7b2e5492044,0xd80530bc3e5410218b85,0x3aad78f4b034291bf096,0x227df951925884000229,0x9aac047f7a3f9ac60d90,0xc0a503fb13ac380a655f,0xbfc4af090e04408045cc,0x181014d9fe5518428343],#[0x857c32c700043a5ff8de,0xb680cd29b259e681808,0x45626e4f6ea22044565,0xf2800d4af0f858e313c4,0xf8b91550810fd22fec92,0x69bba0da397532082161,0x77de881983c2fc21a200,0xba467811001f6fa00336,0x952c08697b0b064fdc2,0xb04383fc2eb00008717f,0x6f0c1cc208727f894f05,0x522bff6f37480800226c,0xd547e22c0014d87953a0,0xaea00221db7c3d880043,0x440bfd8c1086c7970f,0xff328c08736af749c88,0x4c00d3ed3497402181d9,0x7ff54ad20043b74869ca,0xbf741d7e5d074bf4068c,0x850600d1ad1fdb008503,0xc4fe5243ca0400898e1c,0x42000114f736146a014,0xc79f359408777fe8c98e,0x10e1f2f3e25591034f3f,0xbfaa69419882fe5d3808,0x5a579010f0ebb5a28218,0x4523f27f48982043eb96,0x4904292effa21c812280,0x45000a520b9382105fe9,0x308110d6293850294efd,0x87d1e406c35797d905d,0x5f8788408747fba2bf9c],#[0x430317f1e251010fcb2,0xa0fe421b00a6a7112ce8,0x860810fdf759fe95067f,0x2b523f84e00053f3e766,0x146d274b7c373c90029e,0x7c08fa83fd4440868303,0x2a30f2aa70052afac62,0x4c924087fbdcc7929082,0x50085cd3e3e0019b9fd9,0x301f87702c7081150278,0x2bd023b39ffd945e068a,0x61221f1e23f3b339b461,0x9270e3f42068dffb7751,0x2c4085b7db482a3021c3,0x620febda7ce280a69766,0xca4cbf5ddc2010e2f4,0x3b3c7569dcac10f5f8e1,0x5f17b04085a0f48e7283,0x1c0351392ceeddc00221,0x445908408a2e7ed585a7,0x10fcf889c4085c6af9cd,0xbdd341042fbe8e12058,0xa010dcffedfdb6088044,0x2193ff62567034539a5c,0x85dec6c22a3d06e200,0x1d993fcd11010d0e9ff3,0xda84004443f2365e8802,0xd9949000a6acc8fdd56f,0xf778f303397eabb065f3,0xbc00d1d3a11a8006287f,0x66d393fa40295b0cbed,0x70512bea682337f8c5ed],#[0x80874af89d1033dce797,0x1a23d2d406547cdb454c,0xb2fe551010cc5f1e5000,0x19cdf8b8a540820044e,0x7faa0e080087287f404c,0x1d258087368272c00861,0xd7e4f12312002201fafa,0x72e133080089ef120065,0x214dfe0e850810ccff1,0xd57e6b5080029919bea0,0xbf86dd22001153e28b08,0x7f8159f38c108114ccda,0x5ec63fc01a55fa02084d,0x9b1021bbfc15f03374b5,0x50810e8f3372021498d1,0x9f9958a2b02995ff8406,0x35d02010fdf2e6980336,0xc0371bf1d9660086c64f,0x810b9d3e3e9aa39a62c,0x2c0a466267b0214dfd98,0x52e087589e47808f67dd,0x89cf0797e04363f633c9,0xdebc0c042e3fa80a1021,0xabf55c420919dbf98194,0x98f022d067633cbc109,0x563c814e1ff83714760d,0x49fe45e10003479a391c,0x460bfdc0f6c04230011,0x81150f06bd9855011000,0x1c8085a7b89f864e8520,0x42ab6ffaac40021f5e8d,0xd39f9722806687c8160],#[0x22c60022fb2ed9fe9148,0x52c2c10defe0f37c5cb0,0x4313cf07ccc3021ddff4,0x35f765e043e3f89d0660,0x2b9c09810e33c604587a,0xd5237d306c2021c9ff,0xe09302295bfd6821ed06,0x7af2066b7f30a840861b,0x10d8feae3ef6c0044772,0xda753300053dbc8aa398,0xffe8f5303427e401936d,0x3c4d160cf5752201499c,0x4850810e237f6202173f,0x864ce3ee5819d1febc,0x553f304950029e5dba78,0x5f8722066bbcb6c2052a,0x7d4c0cf37fafc8780908,0xd97e267a149004447f88,0xcc98f45fc23a1122006,0xb0e429ed000692af86c4,0x3d6100029dbe419d819b,0xcf5f442e64801a60fa17,0x61f871810b5fff2654c0,0xa7efa6c980333561d019,0xa0863d0275f250ea2180,0x49f1c41c881a09fd6d8a,0x44db9840a7bb8708011,0xc640235d97c777ecc240,0x40220dff007b2e6326a2,0x41802e20543327ea4fb0,0x223ef80ec2400a6fbb05,0xec362086c7877e9d0c10],#[0x3fdb1b5d2524e0045531,0x8947cc4042dbca96042b,0x78f84c19c0efc9d96021,0x680876e481f8c819f3cb,0xefd1fb22010c08bfa995,0xf56068e6cd534b608110,0x7bb2c182840044952bd9,0x25755940884e9f900655,0x53f4312868fa00356bf0,0x4ec201190753e15ce540,0x3534e04383fc4a36af03,0x5a021f8fa68009a5d7ed,0x46be2b31011d5fff6511,0xa4949fe2050810f048cb,0x120c595ba010d37e3cc0,0x400431bfd1c380118081,0x8983c492840a5e41ecc,0xd6e10088860f1b436a80,0x50153cf37ad04293e08e,0x244201a48f9fea408b0d,0x189987f04c019a3dffcb,0x53aff640fc11cc4d7800,0x6a2981a02f81d0906040,0x810f8b61d1c0021d3ff1,0x8c616020442bf278948c,0x88e18faa28005303ff8,0x63ced58c5f2797bb7700,0x8a58e549e12580542711,0xfc76fca4810e2ff51010,0xfb82223d7d31628021c5,0x219dfd22f8617100895,0x856625ffa10dff2ba0b],#[0x21acfba58149efc774c,0x43f2dd81c0535bf9a323,0x76e0240086b9ed2f00c4,0x46043432749ae9000885,0x1e0043af3d3046b7c34e,0x33737f04019a9e5c84,0xd9fa781a70a0880d7dfa,0xce010408cc4a5d7ca021,0x718c0402239fb6bd9e49,0xcbb8f941c84204543ffb,0x822e73fd2306a006907f,0x84c19edec920042cc7fb,0xd5074be38202a33cb78f,0xa74bfc2110d80536d,0x4f47712010c97ca13949,0x5c76c9019a5fd2ed010b,0x1158603413cd8a18010c,0x33bd4becdc9ae010c196,0x447bf91ce8010ca50de,0xdd24000a737b3951a182,0x6006acfc039103379f52,0x68e972832470f9fbb91,0x9ea808c0878ff95f1a32,0xe4d02185fe2033810cce,0x391fce31c620532bc337,0xfe998401993874f2c803,0x33bfbf2b8ca1788408a0,0x813290008a6786a6e404,0x8aa4de1c02141fc302,0x2100a717eac6cec17b10,0x8156c450054c5fc2fc20,0x810c4fecf5008553d6cb],#[0xf5fd2c0240220d93f1e1,0xb23196122d761e082179,0x82001a6cf59a4b640a6d,0xc582aaf4042f7b7ab4,0xaf07fad8204356f88700,0x6947e650212bafe77051,0xfa03067cffd3840700b0,0xcfe930c3b418035276fb,0xb3838008817f0952c086,0x81996f950c202969ffd6,0x6ab7fce9940862cfda8,0x734c0198ba7e836b7d24,0x5e0014f2ece1b44086c9,0x3ef00c24c035d8642f70,0x918068c7976602143f8c,0x5c8e252a12b00a8aefc1,0x9e0010f158fd52fa0533,0xb0219dffab8c085872c2,0x8777d7831042d3a7e6e0,0xa27c60290dfe09ad3400,0x991dd12880891f940452,0x121021c07eb180622397,0x76f1e54c1801a69f97c8,0x2a1234408c0e5f840329,0xd0c1022b1fff587b236,0xfc9a1d502181fe70efca,0xd36d0195bcb7657833d3,0xdf91c194d37fd90010d1,0xa8084eb7fe5c98801a0b,0xb46596f2425d60157ef9,0x88e7ebec6a99d0110e7b,0x1ffda045c76639b45840],#[0x37e04db02955fa780085,0x25c945810aaf7712010b,0xf6200068c6faa6fc301a,0xa0068efe2c08a0cfdf5e,0xe4dfaf300089ef7afdf2,0x14e57f90768000534bf2,0x3618e02988fbd094d820,0x8697ac446f7c002266fd,0xf4f43140537a4fedb040,0x48cf3854bfd0b4006a1b,0x220dfa1408414a860f8,0x43765a58e5f25df8020,0xd1eb189a4088b41f0544,0xaafff9755bbd4102279f,0xf108bc8086c7a733810,0xde9939080a782bffb84f,0x4497ff283beb600694b8,0x7547014d2e3cf5d00480,0x9b97b53948004489ff1b,0x1995f866ea894c088b7,0xaf75f1090204477d364c,0xd2db6a3021db23fca0cb,0xa51ff819418e3d008507,0x801a7dc5d78992200225,0xcf149d61022e39c8d3d4,0xdcf548bd82043f3fd6e8,0x21d3d57c8019a40e7b08,0x90b841022b58ed66240,0xa4ffe52171810f4fd75,0x1907c8d102199f3f9b01,0x61702261f71d5d984022,0x4b121a802aa5b3073606],#[0x99e2074d022b6f38cf69,0x9f8f0a726902241f54dd,0x2ec102215d85c008507e,0x1167febe4b0297de0bb6,0xd80014befd5f8d652001,0x21d9fe6c7b0c0860b89,0xedc15528344ba3f15482,0x741021d6febea020298b,0x51ffc718364087776eeb,0xc1d0c00218ec0ff01029,0x97df0620ed765c010b4f,0x51d5ffdab60296abf101,0x83427c710722068c3ac0,0xfd6b5a22043e7edc5114,0x3810f8d522be04021ddf,0x2858218002a7db3dccf,0x508ddea47768087e399f,0xc4f650604053d71d9cf8,0x8a1b2fc528cf20539df,0xc101514fea9727200180,0x7c7e001034610277f446,0x22b5f77abf338804437,0xe0c2567ffe8b1d815d84,0x6a8fffae5158a20693,0x35e1014b9f9fc365f683,0x67790fe0d26a800899b6,0xfc0a1232043d4b1f0806,0xaed0ff1e7122f3481b15,0xa84b983347c217e9b067,0x8883dba80aa0000a82f,0xced20006a776e6e82104,0xddffd5644810dd6fff13],#[0x95702225ff081840021,0x6c97a792806777ffc400,0x9cb1400d997bd412b00a,0xbfd224a75043c14a5d2f,0xb50ca00115ea7ab8042c,0x4dc303c1001512fcbda3,0xbfe4c8440866ec7b190e,0xf7e5e8810acc44f7042f,0x8d810bcfd04c97700088,0xdc088a3fd0038352abd6,0x337be0c41bbfeb4aa9a,0xc41d43f4823a7f5ff20,0x19f6c8c65848f5f29c0,0x9c3c210d806a8fc97d80,0x4ff8203357fc7680ca8c,0xc92089004427f8c0c891,0x2251d5bab98400445beb,0x5001a41ffcf501935088,0x3e8e7ad680a5efe9e932,0x34604053abffa5412004,0x6f66527208011327d5ff,0x508043daee1a222021e5,0x45e4915108113af733ff,0xc19e1f0e1150810eeff8,0xcdd264f6021b3cb78f84,0xdd7f6920678782bb810a,0x43832eafc0adc8c089cf,0xfc20001985fece2900e0,0x2033e25fc09d88004457,0xeef1f376e4086468ffe0,0x3ed98832d99fc56a0810,0xf9066408857e0e034215],#[0x85f78307001008763b93,0xf02cd373002a71f2d980,0xfc3e840b828008900cfe,0x140044b27f96f4b03393,0xf66d112408733bf943d4,0x1e6065c7d50704004393,0x17fbb51bb08080022c3f,0x211d1f2ff5b04086b7,0x110e37b3ec0b021f7bfd,0xa7fa2067a7f54b265978,0xce8db8a2e0a00223ac5,0xbff76492029a3f586d40,0x39b4fd5cc477290008a7,0x3f98086e7fff248d0004,0xd12f0672532d402261a7,0x5d92400874f8fcbab440,0x9303431fa8998052ebae,0xa60319ffd089ff790c,0x9cfa7fc085bbf136bb5,0x4032a1fdcca01ed3202a,0x434410dcd55fe0ca1d78,0xd70819728fe504627af0,0x2a481a35e446506021fb,0x2029452ad1f824378ee1,0x3e3ef60761021d6fe331,0x3b301021a9fd992b4204,0x787b11e8764340089278,0xcff04840cc5fc8bca206,0x7c43800062b11bccd8a4,0x7680ca1b69deb7841a2b,0x2d3abe59259aa04457fc,0x347adb15410b0f233204],#[0x10c8e0e1ca82043e1ddf,0xbe38311805313d9fa888,0x1021c3fb4193c3200697,0xf4f6c0c60022510656e3,0x59868044053e401975c5,0x197fea2b960126d36af6,0xdc5fa924086d7cb28b02,0x3571fbdd0a03e31b4195,0x27b48001a05faf905004,0xfb6f00348d77c0029239,0x18ec61b10eda62d7b69d,0x800441aacde68010d5a6,0x44adbc604627259ddbb,0xbe60423bfe1179245442,0xd8033abc1c2740010eea,0x77419ab285b4066ed483,0x7a0222e73cbb8288fe58,0x3151b98002a09c8304b6,0x1a016859378219afa3,0xf899350405327ebf8648,0x40539be1dc8d0c102232,0x4179094043c9fe052040,0x1aaa6bf042620000544b,0x444087aff48fe9d24880,0xfe7f1b1090088c7983db,0xe40a2c0532ce7ccc236b,0x81118a34db8c408763f,0x5f8f24810bcffe1b7921,0x1e285fe85c25210002a6,0x531e5d925162f826a202,0xe155aa052d1fc5c381c0,0x720686421f37e0010ec7],#[0xcffa351080a62dbce195,0xcee60ed710eb8002a2,0xab1f78d1fe654f2edfb2,0xa0086aa76f94d240d19d,0xc45ff53d5001235fd758,0x975f91e47833dce0129e,0xdcf58208446fc0391033,0xe4e0cc0451b078839810,0x627e9ff28019dd828f2e,0x3a7d24086064ab6ec043,0x678c08dddc7c820cc2fe,0xaeb9fba146d918cb0908,0xb3e001108fcc6a08086,0x4ad45c2cc40043f3bb1e,0x2eed3a117f97fcf53780,0xa3729066f7f00312010d,0x58df100a4aeb9fba1467,0xbd14029b59bf95440432,0x21d5e0478a00087b3dc2,0x8fd1d82131fffe480c30,0x11397e4990844360150,0x80e5404523e5474ea030,0x77a159a087e7f9bcd560,0x842dbfe3eb1440d0ef2,0xfe67988b20005463f648,0x8920447be456580021fe,0x7e4e24284087d7f4eef0,0xc4c2a94a3ee9e0e50682,0x43d617537dfe0d0b78a,0xbf43d8a935ff9802df8,0xd5a206aa3d9e039000a6,0x66abc0149822b36a7e45],#[0x674af1f20006747fee5,0x5263f3b81085ff140afa,0xa62ffd9402019d6f1f95,0xef6a300342981f23ec00,0x45d1400447ce9116186d,0x4431faf9ce80532bf89,0xc2f11c2044fb5f4e2284,0x465178fd9200436bff91,0xafffb288cc810edfa271,0xcb2810b6fdbd3dc9410e,0x2080aa6610f09010d0fe,0x4b00219affc508a09a50,0x8f6d368bb3103513f575,0xd90080431bf5f65fc086,0x6cfcd0a701084004573c,0x1014fdf49e78679ac00d,0xc9238982212f7b2ff0c,0xd84002233f90ca65f66e,0x4cbcc2fa5010eee6c1d9,0xc0a4898a8511fdb90151,0x17ff38b6aa000da20187,0x2a63f10d22981a33fd83,0x48043ddf9a06e31a1000,0x9c514f29403463f4c967,0xbf24b648087c9933b018,0x1008793a54370005353f,0x7dbf52884087b7f19898,0x9fd15033c967bd000a53,0x68663c5ffa17400880f0,0x5c174c05316b8fdeed00,0x431dde433b908014e17b,0x3ed25b3e029b9d61ee80],#[0x330fd4d411b73b958461,0x13010511405527fcde30,0xc49070445c05459fa1b2,0x227eccfa82650805395f,0x804383f8ebc78734d0,0x4087c1bc9f424bd7cd9,0x14def57e7410bcd331b8,0x73f54801a4aff9001410,0x22c8fdcb8d501014f1cf,0x4232df165ae9f25ad28,0x68bab62f68c02991fa3b,0xd2bf3400482fe9a62600,0xfccd4085ce18c935e068,0xc17f0641c11d00c05483,0xa23afcc0cb1fe65de40c,0x746180a7cfff0e2ea141,0x81a3c457e4a086d3fc2c,0x5fd6550810c01fce14ca,0x4900034e2d460ea0021d,0x5a79a9d0c1022fbfa4b6,0xd1ee6303e404303e8c9,0x7fcb0f0216bfafbd0fa0,0x400429b479121a000886,0x177381a27d4a08beeefc,0x7cb6f92406002243ff93,0xb4066c3bf28343040884,0x8743faf8e69029ab285,0xd6c32c002995eb7ec064,0x587dbe4f76c440011267,0xceee24dc255e2fcc080a,0x527f3c6204287f14000c,0x7bba409014defc774c08],#[0x51440d11fca299f40cf8,0xb73d06d6c3300d49ffba,0xb1440d31d53b7f100034,0x21e4fab86d481fdffda2,0x6d1810151efffb374250,0xecbcdd858408973fe82f,0x1cdf6a3d84a82044c3ff,0xa8c32021713727751102,0xe3bbd819f5c999fc0435,0x28800440991caa0901e1,0xfd3e8e9c0021c9ffb244,0x87e6df6ee08b02205,0x28d9a7880085f707a51a,0xe5fcc01ad7c02254fca0,0x19b1a084088dcf1b08a0,0x5c0a3a61d1c002181fff,0x3491fdeb925b029b8a,0x18111184b1943f3c764a,0xca8b06a20692736fe5d6,0x1304367edc581141a33f,0x4a747037b0029a1fe220,0x66766fd5cb4eaad8011,0xf27bbd62281105fe1b20,0xd833cbffec2052821f5f,0x8574d8a582163e10bf4,0x40f38940a4046f81fb8c,0xfe18111010ecfff593b9,0xb6f44c4542cf6e68230b,0x77e58630043abf8f3010,0x1cf4b777889a9980455b,0x4204303fe8d145b02011,0x250bc94ca60431bf1fb0],#[0xe917a60675c06bfc5544,0xb6088ee9f78ba68034b7,0x43cf18cb08defe243c40,0xe600022886fe1c1d980,0x99bb4720216dffdd22b9,0xe67ad340a6cff6824019,0xc77671f06b508822f691,0x7a14e029852ade68243a,0x1435bc9e5f0c086d3c5,0x85cff682401981fc1b8c,0xfa70cf500068d7307c00,0x10010f57fa93480014c1,0x427fec6b7033cbffb7b8,0x540801139ffe1c49d303,0x789fc2cc00d0ef8fe245,0x7f06e30810f072ec0520,0x2e558810c2ff510109e0,0x5103463fe9ed880043c3,0x4068af15ebe066efee94,0x11bcfc1be0cfdfd14c32,0x449bc786284e4400229,0xf1d10033ebdb8a1e3348,0xce221b087940801195e1,0x942043901f8b509cfffe,0x319c8483c5408b6ff101,0xbd98ee010f277d907204,0x8c08866a9b718810e4fa,0xc2150200449bffab844a,0x160810da3f80211a0a97,0x33f3ff27290404393f65,0xba6dd4801a738f58fbd8,0x408783f021306014d19e],#[0x10c9f5ebe065f7343a00,0x2b1a170208937fa09020,0x9d5fd514284087d7fbbf,0x8c7014d87c903d9b5202,0x72ffca454004499ffc74,0x2042b7ff05441d81a113,0x4329e76e280a507fad8,0xcdfca3159033d3dacc48,0xf8a980a89b958dc96014,0xf8b00401405395f6f582,0xc40852d3f0cab9033fdf,0x410c4f37266408697991,0x84ffc45e110346b0641c,0xd0000542b2ff12498808,0x963e615800887be4e846,0xf4ecf9282160d4a1470f,0x19e500cd0cbfc5590010,0x10cf1811935e3f480cd1,0x9f2abf1d542044462a19,0x22950c1f0919dbf98196,0xbf028e9bffa8d796800d,0x471726bc4167800226c4,0x100b5f7c20528fcacf60,0x32e39b64ce04353eaa22,0x62919c3b02085c8ffdb0,0xb8bf8110020044d503e8,0x4325fbc6f13b014d0b,0xbfddf6a030034da137d4,0x6cec60cd2ffa90430218,0x2975fcef0512d1d8a84a,0x5ff6111c2043b4a3ff03,0x2230f135b282830202a6],#[0x52ce34545a78508d5570,0x66f60f0c8085e3677140,0x9f31acb0700d2ddb26b0,0x953033c3e3b737e0010e,0xbf07aa017000884ffc9,0x33e3ee13010b0fc24042,0xaffab79a824765e5b040,0x1ffa99f9c38f212c0045,0xf9e1419a6ff5f90f0122,0xfcf06e811277bb8a3afe,0xc821dbfca3b406614902,0x425ee7b00014b8e84c64,0xa84029dde50e6102004,0x810e1e99003299ff9474,0x6fb0e940533bcbf92dd1,0x2043c59227d10080a781,0xcc3e3c069067f7c58358,0xd4f8c2e042c67fde027,0x3cb89820431bff904381,0x38704000a9f7e3810429,0xe796f1f09833a5fc7ee0,0x10c2fff57dc2a3186044,0x52ebca1d8085d7c9d508,0xf1774b4e043a9f186940,0xff4c10217df3e2d4263f,0x7baa87ea06934080464b,0xc08043fbcd2481821bdc,0x71467b3c108aa4855c76,0x11bd09c7f5128d33e7ce,0x848388f71a904ec513bf,0xc6668dee5ec7526be504,0x4d3ff0ea593a8de4a432],#[0xffa1145262c6fa090ac5,0x81fe58d0aa6137f45201,0x2331383e3427ce25f619,0xcd8d47f3897d8799f73c,0xa47068772899a4df211d,0x45915ce7b08ef53d47ee,0x23f2429e4d84f0d34278,0xc9ef6b84adc44f6183cc,0xa642aaf0c7b0d8fde1a8,0x6e2c352cbf37a0c9ebcf,0xb8f9f732145e4f41c1f0,0x13df75088d174decc435,0x28d3a95cf53d0ac4253,0x18d460eb5fcc824359f3,0xef7f9068b888c8cc413e,0x7662a9c82d9989a6704,0xb09a413b1446781e84d2,0xb94246a573fb1947e713,0x9fd3609ef39e9225281e,0x733d4d49f7e0406422a2,0x85239ec20237c8f0d4b9,0xf914c84a747c19093b09,0xae651e3dd04ad1fe83d7,0xeb66389dec67ca090c26,0x8522ae3b8826241d4f51,0xe3dc2ade55c1a93cf868,0xc0a8c309f019b52119fb,0x1805fed708afd05afd82,0xf282425b9bd0663ec2ee,0xbad5db8586ec1f41a175,0xb2148d2c6a377c2d060b,0x6520beaebf1a17de7413],#[0xe1b31d5c03a452552b7a,0x9ea44dc4bec35774d061,0xc2683b94f03f948f7c21,0x587c720a0ce1a6c6a227,0x32424092e131b897f0ea,0xe3079eb15de2e8a3264f,0x1852dae91cd207452020,0xff972b12a1b2ebe651b,0x28f0d157e3296453bd46,0x400bfdae1019b0557e83,0xa3e31f3e4d0607b0619a,0x4149c3229b0d168b9e10,0x5b198557d871a91ad2f5,0x368e776f161dadd71987,0x4ea4baa756b1d4a17b9,0x226de46e1eb9c9c1f847,0xce29eb755e4603f03835,0x1a106f85c46091a9aa37,0xc8b0065379bbe68e46ff,0x2192ddd7dd68ea6d3e37,0x341ceede2c3c7f613603,0xf4bba0842530fec87cf9,0x55f55cca4426d2fda473,0x6aa99c6038556e053bd2,0xecc48ff2c68493f28c0b,0x79f9a3f65dd069a13c20,0x654cb7e0ca34ef7d6c96,0x3f9785312c365f98128c,0x343ebe5f11090b2d9c12,0x7de3bbe32ab57e2d5e9e,0x52ed48884bb560e38fcc,0xfca4abf419477789b053],#[0xf1a141b7fe99d0a7754b,0x77cd17d13a2bd20bfaab,0x1fc0ae40c86a7eb8d909,0x8f14d713876b9cf0f313,0xf3e9d07961e351f973e6,0xa32b33d24894bf792351,0x27858fbfc10485bb815,0x863f343f79232d216455,0x4defc9290e6e6130cbf2,0x161c0f00fb0c5ddd7a11,0xc0717983c394252acfa3,0xa5dbb5b4d54ae48d4895,0x18cbdd089b897d87e1c,0xfb104b3ee8fec2c5f29,0xf96251e407e351c4e830,0x9c1dd03a2030b562d221,0x62d739383ab92651f3d4,0x78be520da01c23bd2e37,0x71a176ddd7dd68ea6725,0xe5f630efad19a717d9ab,0x24af77ac85d7fb404242,0x1121f2ebe6518b1b2ce1,0xa313f265aa4a7db92bfb,0xd36c12dfb0455201ddc5,0x9727aeab0a0dbfcc4442,0x4aafe2254205e067dea4,0x9484e3d0484930115b33,0x4421748aee9a0c0ddd98,0x788325d205fd419ea4fa,0x850a7db2102f6ce6b481,0xd93baf98f8fd451a2f41,0x52ab52eeed027869dfba],#[0x71823894d7702b470795,0x2fe5451fb860cd841bf7,0x2a6cfcc3870d9ab71a1b,0x6a4b9f6f987e7edc19e9,0x6bd8b461e568a413e033,0xca46bf894cd24ec9748,0xb0b16668b27e610dff54,0x2627a4c3a764293f8665,0xc3297c8844ae9247dcda,0x33328dc5266386966f44,0xc507657e8427bdae13af,0xa4e9d29986000004de13,0x9a8e35139921e4ebd2c6,0xe824209c9168e69bfe51,0xc92c6a46da6b586c4271,0xe2ec3094a578c2e7525d,0x8b47938a13c3decc7125,0xf4e8845a573aef51ede4,0x4b84af3936f730156210,0xfc3612964bb46899a5f1,0x4c0f0d4a9b897d86d789,0x850baa330e55563b0e2e,0x8d9fe8c8477c2d095b19,0x593517c04c3432f89508,0xd87d971d3878f7f83a13,0x64265579a8d86c1e6871,0x77a3f4215ee44a317570,0x7f3393c35293aecba101,0x921274f0c857be53d46b,0x2411e2fac0c8633655e6,0xd2721ffbd7a166e5f25d,0x1a8d8ea757ee14c8ae6e],#[0x8685f34320271b0f203f,0xdecc428bc71ba108cd7e,0xa92b6330baf33328d174,0xad6f709ea147477724b1,0x11ddc5a3fb84c3047129,0xd204a47cf86d7eb40f62,0xee34275f586b4f52bdf9,0x84a49bc5106e985c3203,0x284f0f013c9d14934dfd,0x293af4b1a909baac1e4e,0xcd5584a5cb8de51b1bba,0x26c3d75e68358728967f,0xd225dda065243582b1e0,0x70cd3227f7a3225bb726,0x62e03f8338512a7ccf4,0xd19467b96c60989cf527,0x1feb215d77b93992194f,0x3bc6c983173651d2f39a,0x77c8dfe342d8df412120,0x90bcaf070c85d4ba97c3,0xc1b9fd8ca327bfe3426f,0x2479a8c2fc0f0d486c22,0xaeb1eee2f0a1f264e84f,0x341d9c5328d20be851e7,0x7661684bd8435c317af,0x8f0a4b7dea413d5f45a4,0x7a13480b848de1cd9da2,0x16c0e4bbc6d199e0]]
set_option maxRecDepth 32000 in
def g255H9 := limbs80 #[#[0x41048440005480200426,0x1a069088289028801a00,0x56811448446a265a8168,0x1140a056062000606551,0x2189164004a19a18409a,0x418086a0655020901152,0x228004049200a9a0149,0x28006405425996920409,0x10069668580408080040,0x410941848112621665a0,0x19406202490190118221,0x58888952004240948120,0x58490180a4124a1864,0x11008000424802914,0x84806442981a91482419,0xa28058500801a01248a0,0x9200010210266509001,0x86a68856845480156009,0x4001412a56844281005,0x52280505400481646010,0x88644214a60a91a05028,0xa460a6540a4869190982,0xaa015a8446998400866a,0x489142545980a8028081,0x600a8a01a88608a5268a,0x4909528000a5a4120002,0x210285545122a9252188,0xa08622a0940296124600,0x969052aa4964882090a,0xb0e440841c37081aa861,0xf983a8d099113a8d0caa,0xa7693cecdf93ce5ba2c1],#[0x7eb391f4af1808830909,0xa8136e430a30a9ade374,0xb4711083d85b5002d12e,0x12056b496e60b2ed34be,0xe5ae144e523fe0ff106b,0x82400a1418585ade90b6,0x17006e39836caca7aaa0,0x5704a78bc04287101a8e,0x887fa2901a3cdba0ac1,0xf8eb13e8063eb1b6e0c0,0x4211cc42156429980ca5,0x3c9b728b148489654407,0x92100b081470000861,0x80700020000003000000,0x440c0800808480008,0x20b03481480c80002000,0x6ae20221000000080404,0x80b11415100000520088,0x20584820e12218a83088,0xa5908870096084000220,0x40908810805601001c00,0x22d46880098329280830,0x302080801c900609,0x421202888602110801bb,0x200100e2040000890000,0x8041c18180010004e27,0x5a0140428880000002a0,0xbc01aa00080081442416,0x64040821240a400d000,0x2a350000000000220080,0x516000da6db44185460f,0x699881d5cc2e2fed1a7d],#[0x8f9414204a4af899ef9e,0xb381a5e18f3d37b3df19,0xe797e2271113e4bba496,0xc5f813ea98aaec79acf7,0xa4ec175b524696854da5,0xe36cf43511963cf46af1,0x81ad06b0a8ac2289198,0xa9ed66f58274669325e9,0x5c47f7e4bb2ab6aca659,0x92c3d5e177ead94d45bc,0xb8b7fcf9ff01c71abd32,0xf0dca68ddd19ec8b8b9,0x810000000000000000,0x40800000000000000,0x2040000000000000,0xfffff902000000000000,0xffffdfe003bfbfffffff,0xffffffff07bfffffffff,0xfffffffff87cfffff7ff,0xffefffffffc5dfffffff,0x7ffffffffffe3effffbf,0xfffffffffffff273ffff,0x1781ff,0xda80,0xa00000000000000006d4,0xb5000000000000000036,0xda80000000000000001,0x6d4000000000000000,0x36a00000000000000,0x1b50000000000000,0xda800000000000,0x6d40000000000],#[0x36a000000000,0x1b500000000]]
set_option maxRecDepth 32000 in
def g255D10 := limbs80 #[#[0x5c9105c5105851058110,0x2192061d10619105d910,0x5912058d205852050d20,0x5d1205cd205c5205c120,0xd8d20d85209d9205d920,0xe1120e0d20e0520d9120,0x589305813050930e1920,0x5c5305c1305913058d30,0x5d9305d1305cd305c930,0xd89309d9306193061130,0x5814050d404c940d9130,0x5c1405914058d4058940,0x5d1405cd405c9405c540,0x58d4361d40619405d940,0x5d9435d1435cd4359143,0xe014361d436194360143,0x509604c960e1d43e1943,0x5c5605c16058d6050d60,0x5d9605d1605cd605c960,0x6116060d606096060560,0xe0560d8d609d96061d60,0x5c561e1d60e1160e0d60,0x5d9635d1635cd6361d61,0x9d96361d636116360163,0x5d164e1d63e1163e0163,0x5857050d7061d645d964,0x5d9705cd705917058d70,0xa1970619706117060570,0xe0570d9170d8d70d8570,0x21971e1970e1170e0d70,0x5d1715917158d7150d71,0x6117160d71601715d971],#[0xd9171d8d71a197161971,0xe1971e1171e0d71e0171,0x5d9735917358d7250d72,0xd9173a19736197361173,0x5d974e1973e1173e0173,0xe01746197460d7460174,0x6057660176e1974e0d74,0xe0576e01766117660d76,0x50f2060e76e1176e0d76,0x5c7205932058f2058720,0x58f605db205d3205cf20,0x60f605db605cf605c760,0x61f61603615c76161f60,0x61f63603635db6360f62,0x61f6460f64603645db64,0xb6febfd7d9ff3f67bcef,0xeefd5f7beb7bef6ddfbb,0x5fe7fcfb7feff5fdbf97,0xf37e5fbff7f6fddefbbf,0x9eefddbb7f6de7fcfb9e,0x6debfbff7eefbdefbd77,0xfaff3fbff7def7ddfb7f,0x7fbff6febfcff7feefdb,0x3fffffdff7fe7fbff5fe,0x98d22e94e7576ac3abb2,0xe86079764648ba069b5d,0x5730c08cbc18b64ddd02,0x26c3d600e5160e90cf89,0xd8f641dd02e8f0259477,0xe083b2aee75767941c23,0x290077867c04c8ba8465,0x7900a4abb0604e51f04f],#[0x44b98f1d5da0c272cf63,0xd1361ec4e2ecb2757682,0xde922ed4e81747a3abb3,0xc63491760d03c9a80465,0xd760074b186975cd815a,0x6c84c9461ced62ec6eb,0x81f5da3d3aecfe9d7678,0xd44ab0c760d93554ebb1,0x277659872e74ca068664,0x5766031c0a38a65ca81f,0x7cc1d8ce5164672c725,0x2a764df162e756439479,0xe8c572900bd761a0dcba,0xed3039961628c391b658,0xf907c3ebb349f5d91ca2,0x6cb4216e5194b308449,0xd0e64c1c8720f0567660,0x2008f20960f90653ebb2,0xec344391802abb2ab325,0x7972b20c83bb858c797c,0x76a1862764dedc720384,0x6b65ce8ca30e080d988f,0x184bac67e8d763975b18,0x282043967e2fc1b88364,0xf845907cbd786e416c77,0x43ca499461cd192e94c5,0x58c64c9942ec8c558634,0xc14b30c7463837d64ba0,0xecc251769106cbb003e5,0xf863907cbdd03e4540aa,0x46b9b30e644601b2c2a5,0x2996187883270e9976a7],#[0xa5d32ec1a6790252bc3a,0x26f80d96171ccb898365,0xb949614cb9c18618093f,0xccbd58a65cb8832d082,0x411e41b88f2e342b943d,0xa14772d469d76854cbb5,0xec1cb5761321ca401861,0xd967546bb10bae4c3532,0x4ebb3e8ee58208b204e0,0x1861c04c30cfa439602,0x34cf20a0dd63787ab88,0x20be0f982347c3acba59,0x1988332c20f1760eb433,0x42bb1d10e41e4732f4a4,0x8a7261f0632e38857633,0xaa48327080d90873ebb3,0xc6880f9724314c238ee5,0xf90ba07cb1f0e65c5162,0x15c9b18ae58e972c7580,0x383e50941b30443b9708,0xc681f21665576ba74cb5,0xc634e9960d76cb061165,0x5976819c9b727651f1c2,0x74b8892f58d18c7088e1,0x5bb59030aaed6c0d9318,0xae41b28ac0d94765fc82,0xecf20d90a006ca0b155d,0x1838428bb483b650313a,0x4eba3e9961c693b22f86,0x3e4d40832702c5632a,0xcfcb70c741b97ab06ca5,0xe74a41987975cb068365],#[0xd74471dca05285d879b2,0x1ccbd310e51f4832cf09,0x3658fc572c662b9063,0xd481b30deed630c06c82,0xed146198b119c9c69561,0x5903022c8390e65c28fa,0x4ebb3f03e42dcaaed5ef,0xf83e41601f28a00f982d,0x1e18ae86e15977230c30,0x271c5f83662dc39c10e6,0x5907066a19803660a063,0x50bb17b85cc681f27604,0x391641bc8726fa59743f,0x35eb208ec9640831c1a,0x270619974575cb53bad9,0x9763874b8849165cac83,0x21c9c003659d01b2d30a,0x118e19f4772e140d9356,0x4308f288cef630c07c85,0xe65441908229c3adbbd8,0xd939974ca53b760de18a,0x23c9a3036608c632e6e0,0xeb760de4faece4b1761c,0x288f208a0d947407c81,0xec1e31938f1dc98811e4,0x1908506ca2a03660d132,0x64b251afd8d1942e65e4,0x98e64c5c432a4e0d983b,0x707326220f962406cb3,0x293ce964a707c85d9761,0xf935e0ccba92d9d8281b,0x30c33f03661c4672e385],#[0xf8ce5cdc83210e0d9826,0x87cfaec9441968630c33,0x2e540d94622fc1a1275d,0xb93a75eb195a75d80857,0x31c33f16618cda2865ee,0x50364c5c63264e59872a,0xd4132ed5265872b1dc9d,0x207c0f905e06c8cf1724,0x1841f75ca068ee58341f,0x2fc9a827641eddac2186,0xd06e42d53aed0c439678,0xddd72c68e399708074c2,0x287a6186842abb2a1064,0xd871c0acbb82d5d850b7,0x6c9d0baa5835b2e6145,0xcad5d82c732e16e943a7,0xd501b30e05b945846bb2,0x2116e963a76eb18f8365,0x193861ccb0a83660742f,0x1dca550365180bf06104,0xc31590e4a2ecea0d909f,0xd01b22ac6587002cc39,0x222051767430c8d983e6,0xd949230cc562c9d87077,0x1dcbd196610746720b20,0x883661c8732f462b949b,0xdf4532c545176970acbb,0x2830e9430d3ebb249860,0x3875e1dcbd2b450cac73,0x33c22317e0d10ab0f565,0xa17618841b2d220d9062,0xdac37275c41987807c85],#[0x22f839971277b20605e4,0xf963620cb4283641053f,0x74c9d3836609d1ae6d00,0x38e65c2483210c0f9335,0x5199b08f4b9868375ca5,0xec5ca1734633c1a311e4,0x187ad1dc98790e420152,0x6cb9840365d54c2e3645,0xe83e5cd5d2e3489d741f,0xd2c6726a0bb634721cb3,0x266615978f66b23c06e4,0xd764758b9a28e6505857,0x1cc98a11641c4cb08349,0xb83e5818c30d0c0d939e,0xcfd3f0cf861981f1ccb0,0xc4cb9867a20cc3d175c,0x5978e68b2179164098ab,0x6cba003642859f08f01,0x5a75da101b2130cf9480,0xcd95728c845902851c83,0x2630cd643074c98683e4,0xd867b774b063d5c46873,0x20cb80ace4d6d6aed4a9,0xcba258341b272e0f973d,0x28ca2ed085587454eba3,0x20fc41908115cb15325d,0xf900a5fc82290e415c87,0x5ebb15b3e120c1b315ae,0x80e65a8cab0c4617978d,0x84faecd03b91aa67ca1,0xc5e41988206cba99761,0x1932806ca480ae40e8cb],#[0x6cb483b644313b20f83,0xe186611d1f27160f9725,0xc20c722b0d1742b4fca3,0xc87e0d961628c3a4b6e0,0xd964106cbb098618c0b2,0x21ca3f106420c6727340,0x303660101f28bc619830,0xab4a2ece647962f5abb5,0x30f215976f07cc021f5d,0xf875b07c9b2ad5d82887,0x30c1d60365060732f487,0x40366239eae2560d9176,0xd6cbb0c72c974086cb18,0x2c1e5f87374ecb3d8ce4,0xd747e2ec39b8ee5a9c77,0x1dca52b1e50dc7727529,0x403644601f30d059862a,0x1e5e53014fd90661ccb0,0x20c8e5733c78cb54be26,0x998726acb199a608f183,0x72ca2ca95d8c94f28d64,0x53fe4141e3235469834d,0x11c932ccc69986653b23,0x2ed069849e78c88812e6,0x5741c52bb369a648914b,0x60c3a29a65cf5e32820e,0x39a60e51cf26bcd5741d,0xd814f21164b916e7dc9a,0xe6c0fb638472b1c41a65,0x5643172c31c92e4201ca,0x7ec915bc65e8cd70c10d,0x2a961cec9726a0fd904a],#[0xc74d722a069980434cb9,0x28a0d5744424cba29265,0x9973578c9d51ad924097,0x73c9c69ae58d8d3073c6,0x592e60ec972c106b849a,0xf98320b6e593237e991,0xc32f9987924cc2492e4,0x9964734c859bce1028d3,0x7dcc23be641e4d7266cf,0x3058d34d30940fd732b,0x1298326c8a5907c7ec90,0x2666fd944634c3a79aa6,0x9634734c24d3958c81ab,0x25cb111265ca0d32ec2f,0x99265d11cf2734698631,0xa5f730f249984a34b92,0x3076d5922a60ca2db559,0x9988f34c3a2b965cdc93,0x78b25435618e8d327764,0x83f641a09728bc6990bb,0x39cae65a4b968824cc3,0x3346b903e72b210bc59,0x5735c25c8441a61d38d7,0x79c9d53064ee1f3268ee,0xd1266228d70686c1914b,0xc41f7283e698620354c2,0x306869641625c9cb3ce4,0xb909c72b9a2bf50d18d3,0x34cbdd3958c20972d284,0xdbcd9058d330b4a57694,0x535fae834d5903a354c1,0xc83c4b939d72c1a492e4],#[0xb966c35c224bce5041fe,0x53c9b5b05d911f328f24,0x4bee41e5e32f4ac19245,0xd814aec924b948d34c31,0x2936e7935034c3119a61,0x5762a25c84a9a64195af,0x34c9a8305d981f2868ed,0x33961cdde72954f29808,0x1a4d3246af1930f7ec22,0x28a0f9867834c0cf3561,0xb905a52bb4aa9e522cd3,0x7dca23bf5c86897269a4,0x21a65281fae4004b9666,0xd0c9330d2fb961f61c9b,0xed18a7979c354c043058,0x5766c6aba16bc652a94a,0x7ccb183ee19e5ab26c6a,0x1296522dcb08b26b839a,0x1e5cac632fd814634cc1,0x21364b949a7cc0b3bea6,0x3860a61c8323c64ea497,0x34ca2f1a61ca1ab0914f,0x51a61134972728f3640e,0x9314b22d6fd971a6acb9,0xc83ee5971c7eb197b05d,0x9834735ca2f1ae4d95f6,0x7cb20fbee4df5e2ec10f,0x51aa6029f72c8ed5943b,0x1609728144990a178bb0,0x30b4c3914b34c34a9ae4,0xb905e34cc11b964cec93,0x73b210be6511c9721126],#[0xd295d889830c76d59434,0x2e1e72354c176456acb1,0x2912f1740a7cc223b064,0xd914635c9a83ee4e0097,0x6ac8319a642dde32c1af,0x9ae127093293c698603,0x178d720ca4b949c34c85,0x2cdac3945b60bb2e12e4,0x7845935b23a12e4cd097,0x60ba22bc65c20d322a0e,0xa1a5d8fc93211e69984a,0x8c9720b669868c34b23,0xc920fb908034c21012e5,0x174a57cc0a3926619cd2,0x7eb20f3f5d868972696f,0x51a64cd94b26d64b946e,0xe79f708f2d5873835c20,0x86faf9633060bb141264,0x3944b60bb2712e51a1f2,0x52bb333c59059fb2434c,0x312e5a554b2126fd9023,0xa5182ecbaf391106ab23,0x2f1af9933034c9d81a61,0x5766860bb2792e61694f,0x34c1263e6507cd3207ca,0x53c64c418326964b909d,0xd68d3233cd7949625cc2,0x213ed5845a34cbd7b964,0x5844a34c3111a64e78d3,0x7ccb3c1a652794f20f8d,0x71a61d75f2c6fae5921c,0x894932d1069963673c9b],#[0xe784b90967ea10d1a64,0x990a034c38ebe6587cd3,0x52b2353e6611dcac6cc4,0xf2961d24d32c7cc1761d,0xd0d728a0c1766125cb1,0x2696f984797ecb803f64,0x9919e24cbb092e454187,0x34c9d0bf60d1982ec5a4,0x429651ac93308efb93ac,0x8ac93294069875c6ab20,0xc10c3905b34cb923f5c,0x993a160cbd5bf58d19e7,0x7cb900b924d40d30e7a4,0xcb550cb0d72c7ca59393,0x179cb2c726987617cc33,0xec486993657dc83f1a64,0x976607cc882395d870d2,0x7dca3cb5590c8932e5a6,0xd1a619b1832896697454,0xd31f2c70869983b25c9c,0x4b84b934a7ccc3c1a61,0x1970a60cba29a61cb4d3,0x6aa198b058d21cae688f,0x41a661a1f12c3e499760,0x820d2e8c04b903b35c22,0x2c1e6b844260c85a9265,0x7939324c9b9296422de3,0x7d4b0f9a60e68972d18a,0xf92e4669aae878a7916b,0x24cd30c6469841b24c84,0x289a69849c78bb51a9e4,0xd962f34c3a21ae0d2097],#[0x60c9d73559221fb2e56f,0x3e641e1ff20dc69819a,0xcc4d30cdae4939a34c85,0x33501984a80c844c058,0x1849a80c8cd4050d2203,0x80ca2840645ba0321110,0x6406588a03293501849c,0x8203269501834881cb3,0x28dd01905a80c99a4059,0x1966c80c8a8406616a03,0x80cb36c06508e02e4990,0xd20ba806080001018448,0xa029d023ec1e42182611,0x7247ec41e63ae6353c2f,0x6c6720612c5b4454e04e,0xda84e47f0a793c73766d,0x8aa3e89dfe97c291d28b,0x92c258bc18b5c6af6ca9,0x96e164dbd4d5eccf14c8,0xd50098f9f0f398ede0e7,0xc320551a9513e90da507,0x3d41a53b0f34a32d9326,0x3761f55b6754f74eab48,0x63816d7b4f75656e7568,0x1a2659c0595458f1188,0x38bea94899b8550de1e8,0x16c55d45cbd16bece6b,0xa8949e864948418a6128,0x1504d721c26f136cc62,0xfca6230731524109c138,0x17557947cad143dadca,0x2ab126e7e1964d0dc200],#[0x175d6b3a48713c16e6b,0x9c8c1e0621303c89c0a0,0x16ed3d3cc8d02b82bfa,0xd49e22471180480d21b0,0x1564f52644af0b70cd2,0xb6959f66815a3f8ae150,0x163d252a434f3362c12,0x22b4a668b1b0508c4180,0x15bd2332c7106bd6de3,0xba929e8611503a8840a0,0x150d1b34481023b0d12,0xd4a0a2674170408ac130,0x152ce923c30f1b78cca,0x8ecf2da9c21e6b12e268,0x1a9e276dd4b2fc4efe3,0x6a9a527f99a510ca1b8,0x16a53741cc7133d2dbb,0x56b8a8e83994468d0190,0x18c5cd5bd0533c52f9b,0x3eb925877982478c81e0,0x180d854c4c31cc10eb3,0xcaba647d1944b8b61c0,0x184db9574ed213eedbb,0xce98a086594a3f0aa188,0x162d112cc44fe38aca2,0x14ae2747f9b4580d0250,0x1685393146304bcae3b,0x6cbea7c7b196458a6190,0x181dbb59cf324430f3b,0xe49c2146814238890140,0x16654d36c8105b9acca,0xca1a22691463f0b4148],#[0x15750725c5d02bbed8b,0xeaa2326f962440b2140,0x15c5092fc6709bdadeb,0xf6a7a487d19e478b6158,0x15fd273047f00394d0a,0x68c52a68a1c2520e0198,0x1ace5575d432fc5af43,0x20b3284831b6548ce168,0x16fd773dc89053bcd7b,0x10af2627795a3f0bc130,0x15e53d36477093b4d7b,0x40b7290899b6538e21a8,0x17355337c9d123dcebb,0x26b527a7f1904b8d6198,0x15a53b39c9109bbada3,0xbc9a2127096c430ca160,0x153ce724444fb38cc6a,0xe69d2026e184488b6178,0x163d252c452f8b80cd2,0x16ae26a879964b0c21a8,0x17a59345cb5143fce03,0xc49da2c7315e450c6190,0x174d733ec8d02b86ca2,0x3eb12708399a4a0ba1b0,0x17656f46cbb143f2e4b,0x8ac8a9e8a9c85e90c210,0x17bd8b524e124436f6b,0x2ab52547c18c470be198,0x1815ad564eb213e6e43,0x72b4a8c891be540f81d0,0x19b6036553f32436f8b,0xd6a022271962428b61a8],#[0x16b51f2dc2af437ac8a,0xeea2a2a78962428b21c0,0x14fce325c40fc3a2d2a,0x20b025a7f99e470b4160,0x16e55542cad0cbf4e4b,0x42b42947e98a4c0b8160,0x17bd8d44cc51d428edb,0xae92a126b9423c8a0158,0x1514d921c30f2b5cbf2,0x22a7a607b990428c0148,0x17b58b42cb3183d8e13,0x66be286841b8508d01a8,0x1935ed5fd1f2dc56f2b,0x86c9ac6951d05c8f41c0,0x1b364d75d6d424b70b3,0x22b125078972448b61a0,0x162d2735c8d0c3cada3,0x60bea6e7f994530d01b0,0x176d7b3f4a3113eceeb,0x5ec3a908a1d85c8da180,0x1915cd58cfb1ec26ec3,0x8e921cc639423e0a6118,0x1524eb24c3cf5b6ec0a,0x32ada46739904f0ea1c8,0x184dc7584f528406e93,0x60ca29c8e9ae4e8d8198,0x19c5f763d0728440f7b,0x7ec529a909d2550dc188,0x1a564d6d5513847904b,0x4ab62768b1b4518de1a8,0x1885c15b5191c40eecb,0x4abea72801a24d8ba198],#[0x18ddbd58cdb1cc24eab,0x30b0a78831a4500de198,0x1885c7534c113bf4e13,0x1ab0a5e8218c4e0da190,0x1865a14b4bf183ecddb,0x2a522671982448b2130,0x17758541cd31d3e8deb,0x5cb8a5c7e986488d21e8,0x183da357ce11f41ef5b,0x70c3a98819a8520e21e0,0x189d9d4dcd91ec20f03,0xe4a724a79196490e6200,0x1725553947cfab86d0a,0xce9da12739704389a110,0x17bd614349b133d6d7a,0x7cbaa888a9be560fe208,0x1a7e4b75d6d38c6afbb,0x28b4266829944a8ec1f8,0x15dd1f32c7910bdcddb,0xac24e7817e460ae170,0x17155b34460ff3acd43,0x32b4286891c260926248,0x19e5fb5a4f124bfeea3,0x7cb6a948b1c24f0bc170,0x1935db5ad092642af33,0x2ac2688219c500be188,0x17c58746ca10ebc0d6b,0x52baaa6809ac4e0b6148,0x1925cf49cd91d41cedb,0x66bea7c861c6568c8150,0x1845ab5250327c42f3b,0xd89fa20731723d0a0128],#[0x63c1f0130452ffba2cea,0xc4ab118b52d80d11840,0x3bc0c2dc205ec30b024d,0x448b41140e0cc1a2acb0,0x7cc2856c4928c0c2b448,0x3e5106410b0e29309848,0x5820f0b418a218030100,0x3a21c28cae0783a3a0e0,0x2811a100a8764e12d42c,0x270784943c3f41110502,0x5f42328224264521a879,0xa9058154a0814a826234,0x614412c560407960418,0x1a43a130680f8a0b5c30,0x2a408971010c2d87a276,0x4c29e0a009041b142216,0xba1d0161c03281908898,0x5fc4a1483d2e13913008,0x3e250284e8782ba38912,0x3310a089044485a9222a,0x381491b1861fc402d8ba,0xfc1008562605f186034,0x26cbc06479621b86a42c,0xc27992816080281a243,0x430527c966270cd2080a,0x1c4f8aa2c9174707282a,0x544c01c04514269825da,0x304f40d8540aa1305248,0x5a0d0124712255d26542,0x3a170201fb1c52037010,0x4372b003542e4bb44c86,0xaa4f85ec57104a4ff0f3],#[0x4aa00d01810d7c659601,0x15ca8d5164804407a178,0xe2a00d06a99f2cd80022,0x289034463c10654fe721,0x81116fc5a9c0854fe251,0x7fc642006807fc604a60,0xe94611a2ffd8ae20909c,0x71500436fbc4ee809038,0x19d0068df80ba0239bfc,0xe09f5ffe30254a1a3c16,0x1500674e5e50033567b9,0x49a943dfc176034f76e0,0x2556f87a0446df80b200,0x2820ce2fa7c86042a20,0x19d3f8944a240d09edc,0x234a59d941273f6697c4,0x13cc90344a2f67658002,0xa5d01236fd4ba02457ac,0x80908f8642792010fb7e,0xece39b73010089dbf52e,0xe40043ab07d3b92010e8,0x318fa9638a83403f4751,0x696f4f93536d300d,0xfa4f14050006aaffa105,0x3d400d43dcd2e34024e7,0x3ede24648012a3e9e809,0xe3cb8c20901fd79b2c83,0x672fff4b707110006ad,0xd47ff5a201213bc397c0,0xcf02c03383f8f5c27021,0x341f5fd75396c04bef8f,0xec7951c012bdd9c14204],#[0x1129dfef65f0c00d339,0x35bb98137bfdc5995210,0x6acfff4a000033dbb981,0xe601100dfa71f4f12a00,0xf8916280035fbfb2a94,0x9c20b80001aa3d091be3,0x3f48325344d3c80860fe,0x6763021883d7ba5019cb,0xc1001ab7c0eec01218cf,0x60fd62f380087af39b8a,0x3677fc720f4422000d,0xa1e00261786d19738221,0xff9bd6200685d78c7ef1,0xf399a006aea74c883377,0x897ff6008804307f87b0,0x61a001a5bfe05d7e2006,0xa0087adb97a40cd9fd04,0xa821c3861f028b60ed12,0x688ffe1a9019a1034d96,0xebe38a8021c3218dbea0,0x5d7c01b80a55f4b01155,0xd08e2cbe2ea2120e0011,0x21c6b5e8ae10495f1ea4,0x85152f506787e1262200,0xe7dab0024adcfdf3108f,0x3e72006787761b20851e,0xc225410dc601b02913bc,0x488fff96468067453,0x342afcfa30471fffe34,0xfe25c99a01a3be562b40,0x800354ebc54a9ae02557,0x90690d000d65feb61008],#[0x67e0ff5f262683477b4b,0x3fe928c8043b6adb6010,0xc8400d4cfb788540043d,0xae3dd56804aaff86a83e,0x4d9dfca1d6a290035cf7,0x82fc3de514801a4f9dc0,0x7baa8c0c0861c7d21804,0x1f398c11b3a762b40034,0x8f29880341bd3e39c086,0xc9c608520ffeb060668c,0x47a120df1fdf6c812516,0xed501810fafe2cf24043,0x822e7e1448ea006917d8,0x341a9f674a2010fbe1,0xedef6ea100696fee70a8,0x25ffc31f84c500006bce,0x5f7603397f6c25d0000d,0x3cf818ffce530025b69f,0x244f0f3a032aafaeb482,0x5cc0cd4fec4000086ae4,0x30334ffde04d6824165e,0x9b69e0db6301a5bf1df8,0xc601810c1f5fe0a820cf,0xa601991fc3138c086a7f,0x195b80d6569034277ed,0x6068e97c3480cd1fc73,0x6b7ecbaa00d01ff91f22,0x433400d10501f4fb067,0x401b3d1459b4c021fbf8,0x50036a7fe7db6dd67843,0x4c000d509f5f25b53c71,0x9d3304900886f3ffc275],#[0x21e2f15cf808fefd,0x707f1eb984043f3ff008,0xa1ffc8400d05dae58806,0x7c0c0d59e15896419cbe,0xe5478573380d991ff754,0xd410c7e31180025e37e5,0x629240d9995334a62000,0x3be38c7240cf5d26cbc1,0x6c400d14fe0898021022,0xd7f17b0c7940044a7f55,0xe59900043cbc3a550086,0xf28033347fe5c80cccf8,0xd19f2fca3900cf9c3e,0xf752309810edf9fcac84,0x89e79b6105da52044d3,0x1e7c604e4fc06e142080,0x8be5e3fc8400d2bce089,0xa67100d081fe15c8019c,0xcddd7fc7871103427fab,0x3f984004081ae3a2e040,0x8986ab7a310856044f49,0x46106607fd9654104900,0xb1ffedde02c8012d3ebb,0x6927e1845cb1be09008,0x9dcda001aab24f2e5256,0x59a8043bb6bc076ff986,0x43c0dfddb9c08697fb82,0x7a5de7810c0fe3448020,0xc066369f813630000890,0x43b27fb605066efc382,0xbe7abb1810d8fc140242,0x206bef18fe9cca110353],#[0xc95419d36fffe92ac84c,0x1c3e1fb528ca034d6bfb,0xa4a392068f7c9c42a002,0x15600d2dff09c80cddf1,0x1a950c3c80086cff766f,0x44100d35f865ff574704,0xf5ffea2e20025473c67e,0x487d90801a57e7d18232,0xcf1ddbb514801a73ff0,0xf03dc2541119a37fc0b0,0xba4081a1bda6ea0cc0f0,0x22bbfdb02e8c0cedc07,0x38a801b45eb2fb4c7860,0x6afb400d101ff122da9e,0xce5ffcd5a4cd00d2c9ff,0xcb1edc0033a7f8137000,0x3e110010f165e6100a5c,0xba1a019e7fd49a11a123,0xf200019b7ebcb4823b7f,0x10d4fd855404ba0882f,0xee3f416c181a41ffca10,0xd9f000cf6fc8830a086c,0x8c1ffc63f80881a23f2e,0xfcdb082960444fc0fc20,0x4c100d34c583e03021b5,0x5e1acd0801a13febfd3c,0x377ffc132a9c01ed40d8,0x1141ca099a00db279882,0x72032c3d378f410cdffa,0x2c7f0d189bfa00694ff9,0x53bf84d49010c5fd8083,0xe5f046ef0f5d84bb4003],#[0x38fc22419b7fbe4411a0,0xa290034e4732cd3481a7,0x1f42c433400d3dffb740,0x12bfc202567efda020cd,0xde1a001a67ffa608a3f6,0xfc8c9b041240225bfe94,0x540800d7c5dcffe019b5,0xf9b17560d4dffc7f8374,0xbcff323114d04baafa69,0x80c0012a5d40966a010e,0x43b7a57e9a3033ef7f5,0x5823888c06b078704c86,0x30c0856cffc0b819a39f,0xe157e08e38f75011b5fd,0xbfd35d40cd9e55c0caa3,0x41c0819dbe3f4e7b819e,0x407f1af4974420d35fd7,0x5b1ad0411101a6388803,0x2801a1df33e8042cbeac,0x304b4524001af3fed22c,0x40cf59379dbe44069efc,0xe4d2c524001a93fdce85,0x6a9154111b8179882467,0x344537c8402979f373,0x85aacb560662ed84ba2,0x8987d1ee22010d6e790c,0x8c804383fc0881ae4020,0xbe63f230c100d64ffab2,0xc50034609cf9000868fd,0x17033c6bf5800ccddfa1,0x6c8400d29fc60646af97,0x879bb59250d4b5fc369],#[0x3c674200906e92d9fb9c,0x4402183a279ff480ce,0x91021a9ef890010ccffb,0x3dcea05978806af7e8aa,0x1810ebc7ffa10e88012c,0xbbc68808408827a7fc60,0x82a02177d0b7cf0012a1,0x1ee12a086bd3ce827e7e,0x8a57400d1bf7a1604784,0x8697c9f415010cd9ff,0x4038728950043e3ed12a,0x13d59035f3e09d7a4004,0x9b4f79a94052d72edc05,0xdbaf130c0866cffc3101,0xdffa60032e476fd98033,0x7fe8a001a12bcbcf00cd,0x27a691863f68006accfe,0x76fb94140069a4de3042,0x17dce04343d8c4f00436,0x6a872fd6222010f4e7,0x7569201111ff6f303445,0x13c73b7be44100d46db8,0x6c8400d41ebf8f64301a,0x8afd36420069ef85ff4a,0xc0b00d19de9483033f7,0xfb0a0e01ed000d89fb6b,0x8008ae70fd38e7021d9b,0x65d8201b3dfb0b931806,0x6a78e2c06a0fdb38e76d,0x195dfea345c04307fd53,0xd4d9e1fbc40674e5c08,0xbb030035e72ac8beb60c],#[0xbfb15874010eded3e1f4,0x8fbb01a94ef0238024c,0x2019e3e79d0195bcdb4f,0x88a8341bff28266fa947,0x22036f414d419c9bce5,0x550800069b7f8accc124,0x7ad33c9699c4035e7fdb,0x66afba6132e96b8423e,0x9e1271d8c20220bed44d,0x9e38405001a09dbfa09e,0x4577ffc132b9d6d40d5,0x92040cf827d310359508,0x8c0854efff880198a3fc,0x8220c0fc55304313fa5,0xc59798402951c190c217,0x867900496ff0e9944033,0x8568006a8f9dc0997fce,0xbfee6a556804acfe74e0,0x281109faf9a468a400d5,0xff101000043cb0abe191,0xb034b75be6817c903523,0xa13f9e48066cc3c33071,0x5f65880688fd21a4b041,0x8882e81a5eba0337f97,0xb1819531ffe200668c7f,0xd61f1db982a2003507c,0x9521022325d65116fc0c,0x46fe898021021e5fe441,0xf8800cd3ffe30a28b809,0x1a03fb8433400d0df7f,0x87a069806a6ffd7c8310,0x66f6bff190043378699],#[0xa011c3e58c0cbdfef4c0,0x30dde11c04204445e33f,0x79a0019dba231627e00d,0x9eba03367fe1880cc9fc,0x604352efc91968c80022,0x7e1eab4c950443bf05ac,0x1fe548840d1df4420657,0xc9b0606637827e7810c5,0xf862033377a7a720662f,0x6006a0f4f8db180ced9f,0x1b7a0a6a0d11f4f98860,0xdf3a010b0f97051010c4,0x5ae801a304a7d8004341,0x86cef26c1819d93ff5,0x3c73f312c833e3938bb5,0xe65000ce6ffcf6895004,0x5f44c0066b68c09c3ff4,0x3b01ae7d6bf5f94c0095,0x99bc3f240335667b0573,0xdf44d28f1068afe40881,0xa6a0d18ff70100a00111,0xa18ef15b76006a0f093c,0xb2483317fa0887fa01a1,0x12193fe5c33400d0d9fe,0xf16f7da001a22fbedad6,0xa006c5f3ff8484002557,0x961020668fe2db5b38e2,0xfc1b1810d9f2ca0019a3,0x40d78fe0e82480087766,0xfff1003307d2a14b610a,0x860339bfb8d041810e98,0xde5fa1508206b4ff86cb],#[0x4400d32f944a8021b22,0x3724fe8c8021f3fe10ec,0x1d2ca091f703c88000a6,0xd0254010f1ef1100669a,0x470fcf6e54106777e6f,0x682ffc1480cdbf7856,0x6fff90a2021929afe568,0x357762ff6dbfc5400d5,0x45200694ffeff0082c41,0xc24eb9205c044b7f7cc3,0x9dc044c57e89a2003403,0x11158000441bf4cd2668,0x16000690e3b7280cd4fc,0xd77ff9103003487c38e4,0x101271fd20160d100880,0x12cfa3dce042aefc3f5e,0x62d021416ffd8cb85601,0x60680fcf6e541067a7f6,0xfbea73b00034e61f00a0,0xf2e4066828ef6d31068e,0x3407ebfa642801a1a3f,0xdfb2af003527ed4d034c,0xffe740140800d401c7ff,0x47efff14a32400d39ff,0x964f0adcfb0340fbf4a3,0x8a0022938865fd7a2106,0xf315680069c7c5c7a6b3,0xf90c08628f9d760662cb,0xc042eebfac4241219abd,0x2eff5b814300257babc5,0x77eb7bee8804aee94a03,0xfb3f018006877a6c3021],#[0xd09802453e8888804327,0x25bf2d5397a001a77ffc,0xd68a210685fe3f574401,0xfbd69cfe4b9a001ae3f7,0xd17ac400d25fe6108019,0x280036b3a2136a0862f9,0x8e7021c3ff853f4c9104,0xf87c877ac80d22eafd3,0x98fad80121a3ff2e4066,0xd54c9cc0f54c0402277,0x8228035e7e80dc02200,0x29a6abc810c9e9ae09f,0x62e60684782c113c8411,0x27b278bd006043c43e5f,0x50691e21a81b72f30805,0x9feb0d14801a6bf6a7fc,0x6219c06c6cffc310198a,0x3d397560d31fe71ced69,0x43b77f68fb066ea75d,0xff9590801a2deefea990,0xd0d97843b012034943,0x7afcd440199bfe9da4cd,0x7e4f9c24123be4a34006,0xf2200866cbc31c0901a3,0xc0cf0f781e4a821fdfdb,0x19f7394840486fe2140,0xdef9aa030219ba679c8,0x3c6696201afc8fe1e781,0x6eebc43548069efff953,0x23031e3fc8230558008b,0xc0f1f0d53330111ba2b0,0x2167be5e1012775d4608],#[0x76800a802246aafce741,0x1a019fde82a02169ff22,0xa6fc8a7ac181a13ffaa7,0xfda30cc19a62690aec04,0xd432f60cd9c43d20199b,0xffc40065efdb08ec0cd1,0x9e480670fa7e481819fb,0x25010cefa6621810d5e3,0x5747ff9ad030345bf40f,0x9008706ffd83d36ad003,0xb5d8ade8f408687f5651,0x85668cd4c7ec597dd700,0x21f3008722c2640d4509,0x1a6f3b7c1312df921e10,0x817542497ffe61d14800,0x92403427fd0a819571fa,0xfffd42755000d25f8df1,0xe723021c1c5cf1302183,0x717e9bc7e90c13146f7,0xbe38880444fbc47d4012,0xe5ec38a0a0590369bf61,0xb7fe2022279c98456f2f,0x5ede5004c70035320a62,0x4c2123b0e03d0a9820d4,0x1300481e87eae0475ce2,0xa2f00c1b98b52035cf85,0x1c22180d0bad0a7fc004,0xc56011fbfbdd40033a72,0xd2ae0474bfa9800240f3,0x1a3d237c38ee20881f3,0x80492c71964efe8651ac,0xeba775d611d7f8d667c],#[0x2b8bc6c0d1ae26769341,0x4307d7916e16068effc,0x25676c2a9c19a9f451d4,0x3496680d23fde7f09600,0x889f8f99b02387f8ca,0xd1e7e42023b29f925208,0x303405c2f5e2477f9604,0x69738e94401313869cf0,0xe890852022a7ae00230c,0xcf99fd56b6e0685032f0,0x2cd884103597a578920,0x4048ae76fb51b347ffb4,0x4ec192848408a1bce7e5,0x880d0dfe2bf206067d7e,0xff96d28e043a7d53f697,0x100356f7523bfc004ac7,0xd6e44b080898ff514d52,0x1d04447fa4120033c3e9,0x3a8864202219fcd4ea94,0x21c8c17fe79060442bf9,0x719bc4506b47d1078010,0xf03fcbca0019cbffcba8,0xd2a001a1d041f9af0021,0xe4fff4108c0021fbdb0,0x4fe412810dcfd1b81081,0x2647d7e8920ca0348a,0x244c40d63ff7fcc83e18,0xc91f9d7a8087efe59431,0xd49ffec205ae004835,0xd8d88fa126a9e19535d0,0x376143dc90c17a821e73,0x481163ffc6b1b98d0e80],#[0x755a011fdf2c40d78d69,0x480d215ef14f810340fe,0xf64e1b96c1a42b1e0def,0x5682af6943e5001145a7,0x409810f5eee013e02c0d,0xa0865e70308090cfe6d1,0xe5fd9f423021a1e9d48a,0x403021e7ebbef67a0412,0xd53f6978040d26d5ff4f,0xf798198780bd36682527,0xa881a21fc36900810f5a,0x28f7bfe2500901dfeabd,0x4ade07aad0474e05fb03,0x11feb541960febe34000,0xc0e6043e7ffd21aa440d,0x7fe998d556200d52f9a1,0x9660291834a7cf6b032e,0x8b8f6f95364200698d3,0xc3021e1d9f6a7a580204,0xe56fbb09810d8fe0c00,0x7033f52b3d40034726f2,0x61a0d1e4402183bfd57b,0x25021b71e39fae690882,0x87d4bf77e901a1dfe866,0x28b64044c91f9d5c4043,0xadd711698008cc7f7241,0x283fc7d711008707f680,0xebd506c604383fc14204,0x1223fbe3849b0c00353b,0x3514aabad419e7dfa490,0xb7998d9b3fc825d5a200,0x86ff2c8189bf2806a2f4],#[0x9181f84aeff454e12206,0x6f247e7b1090113b4e71,0xe31008ceeaf5c1b1810e,0xab6047cedf5b4200689f,0x22001988b867c0cc3ff4,0x88b0a4044d7f4b027afd,0x2606aafe59a0cb0ff8c7,0xc9f6d1001a5bfc63ab36,0x606897f829bb80087af2,0xa63e964002487f4fa0a0,0xea9cb1819e5f5a2e6221,0x110df9716efd7400d35f,0xc980001a7d2fecfba118,0x2457bd148819c3fc3ef,0x89dbc2c08d3a9e957,0x9ae3e0c088b4157b4a5a,0x13ede1411868006bb6dc,0x620033b3e9f254840022,0x5504491786006eaffe5f,0x34f79cbdbaccdd1cbe,0x5d53689810f1fead9314,0xb4a7b01295e126c085b4,0xe044679f1c0680069980,0x2fff3a808637f974d85c,0x45d07aa7f865400d36f,0xb860ce0e76dbfd2c0102,0x7f8198c586013683cf2c,0x44093606a3a6c8271ffc,0x6ac7836bf203447ff9cf,0x9aea4808707f9b191c08,0xbfb93e8deb4c00454bf1,0xa4044863c8f91030349],#[0x7cdec08408777e869a4d,0x4ec00d72c9cd8284087c,0xffe5089801ab99299f9a,0x6e2e2d0cc40402273ee,0x3e80091698de6cd01811,0x3cbff8c131480d2bc46,0x8e0b03707ff2f511a01a,0xc946800d2dfd9b803595,0x881fd818423e84ace70,0xcf32c0087f55e0e266a0,0xfa4125629442081b65c8,0x2328081aa9381aa598bf,0xc59fe34e94068cff1fd2,0xaa043d4bfe79524540d3,0xf927a85400442bf9585b,0x11dabfa0e0de6801a95,0x88e87eb5a200344c7515,0x4afc00946ff1db300dc0,0x43e01ffe41810cbf3a8,0xa9a1e05406e86be10544,0x7ef5e880486f7d250fe2,0xf2f0a0067887e1b58198,0xc71c01293fdb8a065c0f,0x261ffcb2e005339ec6,0x6fa82c0d0bfd3f989f64,0x81abbf3da26003417f8f,0x319c30036d7970aa7104,0x3383fc142042c048b957,0xcb75b4003537fd3a0000,0xd0034b7f10c6066effc2,0xb6a719f1c026f47ec10c,0x891ff5d60002408f7e],#[0xfbeb8c0cfee4fa01b624,0x6aa60fe1e41810f9f8,0xd817460672ffe241a880,0x98252ff1acfd10093dfe,0xd32c08c20440fd7a8007,0x9e98001a76b7d100914f,0x1034a1cdfb10093dfe16,0x5beec260435787a4b9a0,0x4a0d82eed9a349800889,0xe2e002597fd5db5080a2,0x66ff1b8186861ff6bf9c,0x800092df2ae8c874040d,0x61478782348268c7fc73,0xf5980902fc7b244021b4,0xddf8741a67b400354e80,0x20cdc4c08797fda61810,0xd4100ad5565920821a5d,0x477e1ea7328006abbffd,0x2040cecff63ba5006044,0xa475d8b8a2306aefdb97,0xd594b7e9c37ba034,0xcbec63120931fff3c91d,0xd345d1001a0f1fccc028,0xd020959fd542c000d09f,0x3477f19cccb3ffc2d78,0x6be01950034e7ed0d201,0x81128fa57c4841022038,0xa46400110aa7c3ea2c09,0xfcbc5322206006c67f91,0x71e84c1f5b7d8d819d38,0x218194a5839c0290455,0xfe213200102211cfc692],#[0x2428dff014581302269,0x3436dc3810332f5fc8ad,0x6edbe80d2158fc6b810,0x6aacbe8b1b80343117f,0x2200355065ffe1c148b4,0xf5beb68006a8ff39f82c,0xb7440ce3efd4e08c566f,0x2243ff5a1a020686fc9b,0xf38804eaffa45c458520,0xce9fcbb913600349f,0xff8683e8d81a43ffbf45,0x9043effb0b43ab812b03,0x8f5f9fc300acd6abfdc9,0x2f0c00da9ed8a7c0819e,0x4a8b5f01323dbe8aac92,0x1202ddb02e8c0d0bd5ef,0x93f38994001a27e054c0,0x5ecec60430b4fdce2021,0x8000949e1c428181a1df,0xf414190c5206cdfadbfb,0xd52ffa589f1810f91ff,0xe22010e1ff194be44080,0x1e425f5bfe66407faf8,0x43aafef91047d03f981c,0xeff39a011e5f24ccd000,0xebd02960248dafc4023e,0xfffe420067b7f33a09d7,0x3f2d08ce0a0660022c83,0x82a02524bc3a20ab0349,0xc315b10300354fd7fa13,0x1199ecc7d0a63381131f,0x444bec11ca0865f7110],#[0xa484cc10eeffddc02000,0xfccca355f9f424125de2,0x92bfe7433c8024f5bd,0xc447ba08880dc86bce04,0x9f5c23ae0d000d55f46c,0x20048af6ffa7620000d3,0x5468fc14ddc00444fbba,0x505108c01b10f050d66a,0x1143d0fd5c08f9fe65d7,0x1a001aed055ed2862300,0x2f6dc1cc0862f8378662,0xa78808757ed66e71010f,0xf9fd57a0001a0dff8ed,0x101a8401b850f82e9101,0x7d5ad6fa034d68be5421,0x36bffb27ab420006a42f,0x9a001b273326a3c8a421,0xd6d86b03417ff4ac42d0,0x213c30c0f6a0206a0fd3,0x4bd7f1300471fbd7a201,0x6804a0ff5e6fc68b880d,0x12a7ae00230febf49d5,0x83810340258ff143e0f0,0x4a973332ec821a7ff9,0xbf03e908090bd731fd08,0x21d90a0069367dde0052,0xaf01d7efbe942002507d,0xe794021a7ffc04008eed,0xd3084b1cc47e50049c0b,0x51dffe90c1237aff1111,0xa6922440d13f1fab6047,0x10eeff86911a821e3ff],#[0xfa1cff00012850f82ca1,0xab819f1f479e41810fbd,0x8012557d75a411fbd49,0x871e87eae0471ce7f8,0x651de88882219f4e4120,0x474fed494323a881b01f,0x7894086dff63aaf44025,0xfe1f4904004420d88f62,0xffffdd2025671501b3a9,0xdf26f21347fc0bb90494,0xca4202487fa4166801a2,0x3840d03f5ba10479c7f9,0xf6db8d25e001a43fb5ab,0xb214006ddf67c95c0911,0xcb854981a23e12dfc512,0x116067e3a7025001138d,0xe0136dddfea16204a818,0x7308800d93f11dc433d0,0x9ea77e5bcb02baf35f16,0x1e51ac01ab3fc7e90801,0xfda526b83981b3b3e1f6,0x81a71f4739917410ed9f,0xdb1e7796d96bd1c1b997,0xa5bff18a5b78725e58c0,0xdffcd681819c0ffbd650,0xf48069dc188007fd7094,0x49fdbbcfe0672efe538c,0x3600d4bfc78df2ac2095,0xadc9c8c3021f3f209b0a,0xfe02067179c947b9043c,0x7ffe73a1151501aab1f4,0xd40081104b3f88060437],#[0x23c1f26810c05323f6c8,0x865fd24340242f30b84,0x3c7cd8284087e7c2655c,0xc0686b7f87df93100348,0x9069bc30035b17ed4f60,0x1a33ff9f9ea000688f26,0x5cfe581397e74d79480,0xa011e42021e7d6f88009,0x135943f3384f52606b47,0xf86303353f190348d081,0xc3ca5d000450881bdbf5,0x4337021d83b69065a979,0x4a903f81403021f1f9c9,0xfe181e0152ffceb25c00,0x5440cf237ba6f060439e,0x6a523c0016082070aaeb,0xff424c242800896f9d7,0x800930e611f82db80113,0x9fed287c850034ecd5f8,0x213e5f1c14b5848580db,0x43835785378934b69caa,0x31a357061a638ee2d08b,0xa3a29caa21be69a5a1c0,0x4697797aa344d087d558,0x5f6015e183f0a5b1d50b,0x83595bfda3e364a67e23,0xe21f52eed200a30f1d83,0xa5978eed4cd6f09a0c0e,0xbee48251ee195e6a2a70,0xe38eb1c54491d50264b4,0x2d2cbe79312121804f07,0x6e0f1f0e8d4cf90db1a1],#[0x484289a10fefcda8f4b8,0xaa9b3d79afc91c5a1de,0x5a1bfc7764466bb5269a,0x62514a30c9fc5e85fda1,0x14e]]
set_option maxRecDepth 32000 in
def g255H10 := limbs80 #[#[0x4222a4061024100045a4,0x40242814a4004090404a,0x6485012021406518420,0x49151442485891a69115,0xa0866652000a84840126,0x101920a4810458541048,0x919212a1650000244aa,0x1208801068688111980,0x8406408298818162658,0x4219098020410561055a,0x40a59842920808518081,0x22aa82a40aa9aa085061,0xa25a00208282a10601a1,0x98a041822884024a5008,0x5088906091a95440054,0x444804a4041050224505,0x94024050648908552950,0xa0a2018a15004a60210,0x90280584029508816292,0x55446051910560046580,0x59152448105905206619,0x28084a46045144066261,0x84068499456146105109,0x84652814a9101a092550,0x90965104149541510190,0x9800802a54a000552150,0x58992055946862a0148,0x2869542299a050220255,0x21849848508159201401,0x484a140212805496128a,0x806089080005a14890a1,0xa65100501a610545891],#[0x20404180a24188020a0,0x82988246069400692056,0x54098806441615100a41,0x5a099261802100111250,0x21448404284099260882,0x40088015244044018892,0x80080202480509518945,0x11002a5800a09169a00,0x80864062669049111420,0x180024620a5294481061,0x21416444569284044066,0x21414502504690909a11,0x820082a000516a604495,0x80298512484645959196,0x20a990844216110006a,0x41100260281408018550,0x46564aa00085608089a0,0x512880050646620a0284,0x52005611915a2a6041a1,0x190520810a02a5488500,0x84929264088282a02241,0x160a8148299666106a42,0x44811262410290220a16,0x821808448190455a944,0x820208182a9a94510a50,0x8193111d060514d81885,0xf45730e4f500b050852a,0x2b521a206844e35e0fb1,0x48500d8c08a892bd2c00,0xef87fc1c1c454500c89,0xfba8b567f469a140c8f3,0xf93020251a2c264b7a09],#[0x6324c4aa4254203b6162,0x38845d22ab858c9960cc,0xd66aa75fea1259c015dd,0x4cb354ec80949104440e,0x830589dbe7d4d2870f4d,0x8032a25182143c2221b6,0x1307806b095a86e00325,0x2f2e0b314a65c40e9b,0x9e318405e042ea260524,0x8ec2e79059b2b24f1c5,0x94adb2a087d84a82ba5c,0xa180440999a1f44aa60,0x489108696a18608433c7,0x1b832a015e09110551c,0x11665ad7ca62306400f0,0xfabc0ac4503352b18207,0x4c849040c08608dedc5e,0xbe761883724827043018,0x45e2de93f278ac2382a2,0xd196061c280780d60e15,0xebf7065551b25900d48,0x9005a5c41e2484849326,0xc400000d0080100c084,0x1001000590600100c124,0x981800b80040014040,0x44000ec928484010,0x2420400015940840204,0x4812244181988204003,0x201030400281e0800001,0x18100101a80023c4b012,0x61810242042402a80988,0x2003280808400308200],#[0x4009020010040036800,0x8865840010000283a81,0x218608000020000003e4,0x7a800050200000000044,0x4a001801900688301184,0x510060040004228e800,0x856888201034800019c,0xb605d02002a434188001,0x811063e0024018002900,0x209006aa0e018000c448,0x12468071c10a0a000081,0x295087728008002000,0xd20807c6122188400,0x9012549883f51020640,0x1208007c108b41080928,0x88402518100938401008,0x2420201025099b13100,0xc4612162068d0a104a02,0x3020019213000a710d0,0x58110000000000b1a01,0x2b0040040103008b7a0,0x98000602c00501280ba8,0x58d000c0800a041040bf,0xcb00004a064c0009210c,0x8003aff7ffeffdfbf7d8,0xf81befffff7fbfffffdf,0xf7839fef3ffff7ffdfff,0xfff8577dfffef7fcffdf,0xbdfb873ffffffaf7afaf,0xfff7f8905fefefbfffff,0xfffea78acffff77fbfef,0xffffdff8ca7e7ffe5f9f],#[0xefedfbef0e4ffa97ffff,0xffffffdff901ff777fff,0xf7ffffefff91d7dffbff,0xc7f7f3ff7bf93bffebef,0x77ffe9ffbf7f9593efff,0xedfbed7f2f77f9747ffb,0xffffff57fffffd1907ff,0x7ffefbfffbf6fff9aaf7,0xfdffeffffffbdfff9c7f,0x2fdfbfffffffefffe9e4,0x20fffdffdbeeffff9e20,0xa3c7fffffef4dffcfd7a,0xfa57a8ffdfbffffeff7f,0xbfa736f5fff7fff6ffd7,0xbfda8f7e7fefffffffff,0xfdfeaad7bfdfffffaffa,0xffffeac95fff3defeffb,0xfbe9efae4dfdfff7febf,0xfebbdfbb01f7ffee9f93,0x3f6fb1aff7efffff,0x33700000000,0x33d8000000,0x33d800000,0x33d80000,0x33d8000,0x33d800,0xfffffffefffffffb3d80,0xfffff7ffffffffff8007,0xf7fff7fffffefffff81f,0x5e7fffffffffffffff83,0x87e7fffffffffffffff8,0xf89e7fffffffffffffff],#[0xff8be7ffffffffffffff,0xfff8de7fffffffffffff,0xffff8fe7ffffffffffff,0x8300091e023fffffffff,0x4680813a00840000482,0x83413e8840034600,0x2dac01c1144804c02214,0xc0004aa4214a00001580,0x1800405401522107821,0x245e1c042115a9a10aa,0x188407a2d161c0242,0x9361006200d4216a310c,0x9c202580883000173004,0x1cb02004881004017b00,0x41022010081210401819,0xd1401000b052012d2188,0x94874020205010810018,0x19a0023c0104a10c8021,0xd1a1193c0062e9c93309,0xda1ad8c0208c02911010,0x4941b541020042008200,0x49289bb100210d009900,0x130121c254930020290a,0x1040009cb85890116121,0x4201811d40808153a41,0xea2c44049db202004000,0x3209c481df18110820,0x8340ac00501e80560488,0x1f0000002]]
set_option maxRecDepth 32000 in
def g255D11 := limbs80 #[#[0x58143509404c93048110,0x5cd725c5705916358961,0xd8f62d8760c82765d974,0xfdfefeff7fdf6ffb7f64,0xbae21ffffeff7fbfebf9,0x692e8d0616cf3885e719,0x430b01885c02eb8cc976,0x8678f0cc95cc22c1d956,0x7873cac21161cd3b1847,0x6b8068f0811e1d48bb60,0x9e5640ccec195ce72430,0x9aa5710d4e27ae0da3c1,0xc05d54320f00d161d6cb,0x3b20697140f08a1e0202,0x86bb4078488b078a5c69,0x1b3b085176a4ae331e05,0x19a3c1c478088b072ae1,0x58c28bb28586222c74ae,0x1e1cc3c08697115306d9,0x1e1182c0551633b2c66,0x2435d9a3c03d97330f07,0x749e1826b9b0780352e,0x286d49d954c23478608b,0x56c8da591a3c02a971ad,0x3a4ec7161c82c0585874,0x424ac731618d6b808781,0x7100b082161d42c3d557,0x57458b0e0a219a2c04a9,0x136338f0d0a601b6b001,0xdeb6368b0f495d022c30,0xad7020f0871e0d82c3,0xc33696102ac841e11f6b],#[0x8bb2cd767cf021959274,0x52a1cc587c0b0e71e19a,0x272b0cc58714aec11618,0xcc43c1847818a2ec795d,0x5c4f54336d7038f0c665,0xb58093c20678309aecca,0x2950c2aba19176bd2c6d,0x82c608d8a1865769b2c6,0x11cd9199c22b187362c,0x2ec0c508f8b197163267,0x630d0c58439b20b1647e,0x6e3087c5d058c31b1436,0x30e2c81c60958bb2b186,0x73262e44c59078c03716,0x17246308ac608f8c2471,0xb1713e2c40c61d58ba2b,0xb1818e3067c58d98bb1,0x1c71743e3006c591d8b1,0x4333184663027c58898c,0x8c047382562e40c50859,0xf8c23f1733e3010c5d85,0x998bb13363662644c50c,0x91993b0b1213e2e74c61,0xe1d58b90b1633e2647c5,0xc50dd8b0b33818e50cfc,0xec60598c39f1763e2e47,0x42cd8598c1c31867e2c6,0xac50d39c2473838e6c,0xa609880019b23f380563,0xc43e0e642f489441b984,0x8331e126de18e2586937,0xe62ce8aa427ee959a30e],#[0x93decebdb80cd50b270b,0x94012fb491d1a1c3df03,0x1068010d712d9105b210,0xc2589800ef66acd1e6f2,0x6a2308c01016f2e1326,0x1266d24090010c72aed2,0xb3d386b240a0011a7ab1,0x81b3948772b094011b7a,0x237eb696084328d40127,0x12c833554a792888001,0xb0012d7fb553474258ac,0x5074011d79b3d62862e8,0xa300cc011776af11c672,0x8692608001347d389828,0x150892709c00ff6c2c11,0x33d587a2b0e400fd71b2,0x78b0136752a898011679,0x4702e91e672409c011e,0x12c82b21306b2188c01,0xe4014691bb9768b2f8c0,0x988c013d863897084308,0x22788c014081b655a7e2,0x68c340a00150903957c8,0x16c8a348d801568f3997,0xbf5a09f328e801458639,0x7db51406c2486c014c8b,0x207830d2c641e0640128,0x1478c3a588a2328bc01,0x603164442307802a8a4,0x4a512a89c30570896436,0x142c1a281617852121d2,0x5850c870451509c0c403],#[0xc948749a283f8840e241,0x82c1a841843410210781,0x411621502418ac123e00,0x451018050787c4c3105,0x4ca002cbe3a04019012f,0xf087172994a1651208b0,0xa0451c3b271512010070,0xc1d168650e12118509c1,0x744269fee7842313c468,0xa7f85141319ee7884b7e,0xfea345090bf7e4e82024,0x2e278469fa8ed210903d,0x9e73e1b001240e3c269d,0x23aec6f02347fd159101,0xfdc084e61f4130ce2078,0x40812375c0de06002599,0xcbc58515fe1cb028d15e,0x6360c23775eb02081a0e,0x30e7ce88461c5f8c011d,0xd285039f3a2119456f02,0x7f500475ee3a804733f0,0xd8480ce3ffe09201200f,0x700b0a7632a6242447a7,0x3cfb5008f5ee7f00517a,0x92c3e7e40a3be55c40cc,0xa1e008094bc0e7f1a004,0xdb48424c8af30c123757,0xe0d429d03fe7604715fc,0x70fe840249e4e1302883,0x461485ffe2314a0491fc,0x28024c8af20409179bb9,0xfc1297fdba408fbfe97a],#[0xb048b07f82142fc05c80,0x2547cf81880ce178ff18,0x2ffe140281fc0fc0102c,0xf23a1ba802519fae0428,0xe8e046535e4785804a5f,0x7c06024af93c810024a9,0xe01520663fcb74051946,0x945ffc404ebcec011bb,0x4686fd00122758a1cc28,0x7cf016012a7e864f0012,0x740238fe1549e341276e,0x8240678a4e4708f3f63,0xffa280242934bc2337fc,0xc0e54012f57fb0504755,0x346eefcb85091bffa37,0x1ef81e8a0096d1c2bb09,0xc0c004a53be34628499f,0x2c0aa3ef1a8a0cebfd68,0xd40239f59384d770fdc,0xc3400945f14d00033aff,0x78014049336e2138c4e7,0xbc8e064122cbcb04eb5e,0xd0f0a025281c9f0c0095,0x68a1323f0c545067d82b,0xe1f7a302004b5c8eb514,0x60460048df9e0002024e,0xa8503fee49838c012e7d,0xceb023412eb39096f9a1,0x518519fc04680671a8fe,0xe4b04e967e68950926ee,0xbfc16808f86fc2011ee,0x71fe041a08f38d0c2809],#[0x8ebdfc0d011efa7f802,0xfffa43468b04b82bf758,0x9a67a38118fc2a613af,0xd6cd20024bf07810187e,0x613ac7e12c8e8421327f,0x20d049dcdcaa048b2f1,0xfd804f12f3a211d7f2bf,0x238908481d714a0470fc,0xaa0804983fee540a47fe,0x1e720238581f0232ff15,0x8e685012b7bc1b209187,0x1084a19fe68d1424afd2,0x118d7e5de814af3fcdb0,0x8161227220c232898f8,0x832091b3f344ac1257e0,0xdef021487fe0a014ef5d,0x56f34211b2fe24c231cc,0x57c3c98819ce66f7810a,0xe060025af51eb4300248,0x34161f0e20665fff5c0d,0xffc05c1f824567cf1640,0x1ac1019c7e0ff2a4024e,0x1a632fd119201a33f4,0xf1f03d0800955fa60420,0x68af2040913e38341197,0xbc202a18ffffb9845825,0x88100254e7c35047b9ed,0x40cf37c40060248f8f55,0x7debfd760c82497f8bb2,0x499f869428afe6526206,0xe6f670024cffe8c58102,0xd2020d01fed2848819f2],#[0x280264ff1cc5008f5d9c,0xf13f83dc28d1fff14b42,0xa999e7f710489cf86a08,0xd640c825affae2828004,0x137bfa5510332f9ffdc,0x5d018009527cfd0f6092,0xe36a0122fb43c0853bf5,0x9b7ff9fa096a8201307b,0x2dd7c411281a2bdea881,0xa22241084c58b9f0c009,0x661fafbe5ba0804b0bff,0xff58f3c35009515f4ae0,0x11a211bbf52d0720034e,0x73c90347720d7d1033ef,0x9ce85d5d1bf440ccd696,0xc71ac081412ade7e2ec1,0x240dffd744f460096bf,0xf8535048001aa7fd4123,0x8480cfbeb5c654804a0f,0x6600484a32f109abd07e,0x11678ee443460973e7fe,0x282367e3ec8480cf2b78,0x1a567f9c6244012b7f0a,0xbfd089811db8a17f1090,0x3c420819d71aeafda090,0xa4fbf71014187e0943f,0xdf3f3707c81263fde708,0x8a9429092d1d8bb18068,0x420125738be405012a7f,0x696f32e1a880d135b1f,0xac80801aeb8fe900122,0x1440cd3ea95023d7bf50],#[0x160905ff2648101a021f,0xc0091be742046dfff839,0x81a329e5584819c7be30,0xaf187050]]
set_option maxRecDepth 32000 in
def g255H11 := limbs80 #[#[0xa401220a41042469a824,0x24240289014100508866,0x80a2090608021102421,0x50060128458180868640,0x4510189220a44a915a81,0x10010a00046010140498,0xa9426208221581294,0x9a9a04548400492aa64,0x58842510880a46469006,0x90611064100465955640,0x182002410584a05186,0x409820a410595214401a,0xa682409124412468520a,0x28100228152166aa225,0x1584125a8848464a9020,0x942951a08400488a8528,0x24106206840002685951,0x4248a15049200a214a80,0x541a401088450280500a,0x2a149291482246420a49,0xa822124098a119816995,0x25002809555205620045,0x192060019a2152504495,0x1a909060825a61a8a94a,0x18161408a10100485094,0x92282282048142410158,0x60194544861aa8242a2a,0x2020110209a828a18658,0x96a5501a49a6a6892468,0x22610881891400a8800,0x58a02484588688980228,0x291265a62a01a1180498],#[0x8129a02608a61120958a,0x30101456016230bce824,0x673328a31af83ad0018,0x24c42602d200fae90d29,0x12a88b66a629372d4488,0xd0814552f46a1a350ade,0x2821780440d34e441a02,0x1402ed571af4908fec3c,0x88b1cd4848bf0244112,0x856208c289b81ac1255,0xff8513014a898025398c,0x5ef2e4f0468a40fc0f04,0xc04d66370472d6bdc024,0xaa00cbe848a040246085,0x4b872c5c3e4364c17147,0x22482a37ec793da1e0c2,0x24b0415d478816636886,0x120046802402e8fed348,0x120880038088000820,0x42000000160298000d0,0x44190482101692b00006,0x50004006010104010db0,0x20028088000c400114,0xa048102402800740a00,0x108001818181404150b,0x104e09008800001027a8,0xc300280080109408016d,0x7008084101204761020c,0x83f60002982200600908,0x3022e004a00000480081,0x80212800001b30008020,0x529089e0222402004822],#[0x20860054a911008c0215,0x71481002ec0060052044,0x9260040018c008000036,0x4e00042080d200c90081,0x580a30080006f0500020,0x461ef041144a3a000000,0xf70a4ca58a47d000ddee,0x3a009202cae1fe81efa0,0xc32d1508b55b8ca01f35,0xde92921bd2b3dcb4c169,0x985c5541b76f1661490e,0x5bc114646ccf40450d8,0x28340b8d8ed744916d74,0xc281decc67151383352e,0x37cd10be582bc268a8b3,0x374a68939123466552c1,0x8a12f9450f078039c52b,0x4e37b4942c04d8af0ba0,0x44d64a24617caa5424f5,0x85318e9dd8cdb0d285b,0x37821c64d46d7bfa61,0x3ac5684,0x1ed000,0xf680,0xa00000000000000007b4,0xffffbfffffffffff3d,0xc1ffffbffaf78fdfeff8,0xfe1dbeffffffefffdfff,0xfff167ffefbffffe7fff,0xfefe8effbffffffffbff,0xffeff896ffdf7ffeffff,0xffffef65a3eff7bfff7b],#[0xfdffefff343ffffffffb,0xfffff3fff9defffffffe,0xffffffffffd0dfffffff,0xfffffffffffe967fffff,0xfffffffffffff533ffff,0x2541000050ad9fff,0x10200000080000118c84,0xc0000000000880000c88,0x28000000000000000064,0x194060000200000804c3,0x8cbc000000000000000,0x80065e10000000000000,0x3310000001000104]]
def g255D12 := limbs80 #[#[0x8338ab89900907fffbfb,0xcb85b04b04a049849048,0xb14a14994b8db0cb0c90,0x24b9db1cb1ca1cb95b14,0x88300053b4bb4ba5b24b,0x81f06b9704d1023209c1,0x2ba0d8320b72bca52588,0xa53b434d52cc8b103fcf,0x11070c282d030177db35,0x603080d120f10262a12,0x40183a1e1a16045e150a,0xe1af04c44380a2e201c,0x850e8c04367f6020d7cc,0x514b30a141afc81efa02,0x79cc0eff60e60a3c9228,0x286045fe2804e697b412,0x79f2004e7f6020149203,0x2f3e01d7e00d7e7a004f,0x1c3fe6020527f40f014,0x9b26040afcd04a9019a9,0x23c026ff0c88052fd901,0x18f407]]
def g255H12 := limbs80 #[#[0x981510a0680410880a,0x4641a4480018088604a,0x2250259686602a042104,0xa191a056a10080101552,0x2a9a8469042580140155,0x40a16498450808a112a,0x91951420a29880642600,0xaeb041d1a4400a80648,0x90610ab40829905dc317,0x8dc544084840630ae81c,0x8af878b0884a466d2084,0x3081020800804a0078,0xa02a3800080a491000,0x2002e01a0c280404002b,0x40808914631301040422,0xd4e26a19800000e0e280,0x6853a58000401546a9d8,0x73c84325ac36853010a0,0x117b4078918bc30d840,0x2400000,0x7fffffdfffffffe59000,0xbffffafdbfffefffc01f,0x3c800000000001fffd8f,0x8a0000000000000000,0x11400000000000000]]
def g255D13 (j : Nat) := if j=0 then 0xc0c08910006ff else 0
def g255H13 := limbs80 #[#[0xa7c445e98500260af,0x44780d9eecc4ebac0000,0x891a01220806d026b0d3,0x4600b93f8c72]]
def g255L : Nat → Packing
  | 6 => (1,7,7,0,0,0,0,g255D6)
  | 7 => (103,6,7,4587607,119,8427,1070,g255D7)
  | 8 => (961,5,7,17957446,154,8495,1496,g255D8)
  | 9 => (1871,4,7,14484107,138,16721,1434,g255D9)
  | 10 => (1086,3,7,4260028,120,16720,1263,g255D10)
  | 11 => (235,2,7,851993,69,8494,1131,g255D11)
  | 12 => (29,1,7,196609,32,10,1057,g255D12)
  | 13 => (1,0,7,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 2 0 2 0 0 g255H7
  | 8 => indexWave 45 2 8 837 7 0 [(405,103),(621,16)] #[(0,0),(16,16),(0,0),(103,0)] g255H8
  | 9 => indexWave 392 3 11 7803 10 0 [(3528,961),(4953,660),(6378,739)] #[(0,0),(739,8),(223,445),(0,0),(8,0)] g255H9
  | 10 => indexWave 763 4 12 15075 11 0 [(6867,1871),(9603,630),(12339,1286)] #[(0,0),(1286,4),(4,212),(1912,1494),(0,0),(1494,0)] g255H10
  | 11 => indexWave 442 4 11 8703 11 0 [(3978,1086),(5553,833),(7128,505)] #[(0,0),(505,39),(39,593),(1299,1059),(0,0),(1059,0)] g255H11
  | 12 => indexWave 99 3 9 1986 8 0 [(891,235),(1256,208),(1621,159)] #[(0,0),(159,8),(70,146),(0,0),(8,0)] g255H12
  | 13 => lookupShort 7 37 4 7 5 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sample255 : block g255 9 1494 32=true := by
  apply groupBlock 1494 [(32,10,3)]
  simp only [groupProof,cells,boxes,and_true]
  repeat' apply And.intro
  all_goals decide +kernel

end PEqualNP.Outside.L_meta_35692
