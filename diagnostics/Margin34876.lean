import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_34876.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_34876
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfefefffffffefffffefc,0xfffefffaeeeeaa00ffff,0xffffffffffffffffffff,0xfffffefefffffffeffff,0xfefcfffefffaeeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[1,2]⟩,⟨.or,[4,9]⟩,⟨.or,[0,5]⟩,⟨.or,[0,1]⟩,⟨.or,[6,12]⟩,⟨.or,[3,7]⟩,⟨.or,[4,7]⟩,⟨.or,[6,7]⟩,⟨.and,[14,11]⟩,⟨.and,[5,8]⟩,⟨.and,[16,10]⟩,⟨.and,[15,13]⟩,⟨.or,[17,18]⟩,⟨.or,[21,19]⟩,⟨.or,[22,20]⟩], 23⟩

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
def K41 := extendKnown [] 4 [(41,[]),(82,[16,67,101]),(145,[67,117,101]),(146,[16,67,117,101]),(161,[83,67,116,100]),(164,[32,16,83,67,116,100]),(194,[16,99,67,117]),(208,[64,16,33,99,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
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
theorem g27G : graphValid g27 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K41 V41) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K41 4 [(27,[]),(51,[83]),(89,[64,49,33,98,82]),(113,[64,81,33,99]),(139,[116,84,101]),(170,[80,32,116,100]),(184,[112,49,32,65,81,98]),(201,[112,49,33,98,64,82,84]),(232,[112,49,32,97,84,65,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V41 low27 (by decide +kernel)
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
theorem g45G : graphValid g45 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 5 := lower_forest (g:=g45) (i:=0) (hints:=1283) (before_sound K27 V27) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K27 5 [(45,[]),(57,[48,66,80]),(83,[16,32,99,67,84]),(150,[16,67,117,101]),(153,[64,50,114,32,80,101]),(166,[32,16,83,67,116,100]),(172,[32,16,49,113,65,100]),(178,[16,82,67,50,115,99]),(180,[32,16,65,83,115,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V27 low45 (by decide +kernel)
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
theorem g147G : graphValid g147 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low147 : Lower true (varsX 147) (graphGoal 147) 5 := lower_forest (g:=g147) (i:=0) (hints:=68) (before_sound K45 V45) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K147 := extendKnown K45 5 [(147,[]),(165,[33,84]),(169,[48,113,33,32,64,84]),(177,[64,81,33,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V147 : Known true K147 := extend_ok (m:=147) V45 low147 (by decide +kernel)
def g210Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g210C : List ColumnInfo := [(2,0,208,0,4),(16,0,194,0,4),(64,0,146,0,4),(128,0,82,0,4)]
def g210A : List (List Nat) := [[],[118],[100],[100,116],[116,100],[116],[65],[65,118],[65,97],[65,97,113],[65,113,97],[65,113],[97,65],[97,65,116],[97],[97,113],[97,116],[97,116,65],[113,65,100],[113,65],[113,97],[113],[113,100,65],[113,100]]
def g210D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g210D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g210H4 (j : Nat) := if j=0 then 0x20b else 0
def g210D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g210H5 := limbs80 #[#[0x2700000000027000,0x1c1000000000c2f1000,0x1440000002c00000000,0x10c00000]]
def g210D6 (j : Nat) := if j=0 then 0x3904f else 0
def g210H6 := limbs80 #[#[0xa255123a000000018000,0x1a40000001]]
def g210L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g210D3)
  | 4 => (3,2,2,0,0,5,0,g210D4)
  | 5 => (1,1,2,0,0,0,0,g210D5)
  | 6 => (1,0,2,0,0,0,0,g210D6)
  | _ => emptyPacking
def g210I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g210H4
  | 5 => lookupWord 2 31 0 9 2 3 g210H5
  | 6 => lookupWord 1 17 0 9 0 5 g210H6
  | _ => fun _ => none
def g210 : Forest := ⟨210,6,fun i => g210Y[i]?.getD (0,0),g210C,g210A,g210L,g210I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210P3_0 : block g210 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g210B3 : block g210 3 0 2=true := g210P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210P4_0 : block g210 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g210B4 : block g210 4 0 3=true := g210P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210P5_0 : block g210 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g210B5 : block g210 5 0 1=true := g210P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210P6_0 : block g210 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g210B6 : block g210 6 0 1=true := g210P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210T : checkedTables g210 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g210 0 0 0 = true)
  · exact (rfl : block g210 1 0 0 = true)
  · exact (rfl : block g210 2 0 0 = true)
  · exact g210B3
  · exact g210B4
  · exact g210B5
  · exact g210B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g210G : graphValid g210 (boundsBefore K147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low210 : Lower true (varsX 210) (graphGoal 210) 7 := lower_forest (g:=g210) (i:=0) (hints:=285278272) (before_sound K147 V147) g210G g210T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K210 := extendKnown K147 7 [(210,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V210 : Known true K210 := extend_ok (m:=210) V147 low210 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf007ff0ffffff007ff,0xff87ffffd45c460f83ff])),(BitVec.ofNat 152 (word80 [0xa0500a201000a05014,0x1100082401806108421]))),((BitVec.ofNat 152 (word80 [0xfff8000ff87ffff801,0xfff87fc05373b2007c00])),(BitVec.ofNat 152 (word80 [0xc0622c40a122c46258,0x8a012108527132b5ad6b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x280b002c20b008060,0x2c220a00a541186318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb04c08b044c090481,0x30004c100d06c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc07000c00700e0701,0xc04470211aa6018c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,2,41,16,5),(2,0,57,0,5),(8,0,51,0,4),(16,2,41,0,4),(32,0,27,0,4)]
def g59A : List (List Nat) := [[],[83]]
def g59D4 (j : Nat) := if j=0 then 0x4fd5120 else 0
def g59D5 := limbs80 #[#[0x480e140fd42fe20fd20,0x4088]]
def g59H5 (j : Nat) := if j=0 then 0x20 else 0
def g59D6 (j : Nat) := if j=0 then 0x18989f else 0
def g59H6 := limbs80 #[#[0x6e900000000000000,0x0,0x600200000000,0xc80000000000000]]
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g59H5
  | 6 => lookupWord 1 43 0 7 2 1 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 1=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 3=true := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K210) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=67) (before_sound K210 V210) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K210 7 [(59,[]),(91,[64,49,101]),(115,[64,81,49,99]),(121,[97,33]),(186,[112,49,32,84,98]),(203,[112,49,64,101,84]),(234,[112,49,32,84,100,66]),(248,[112,49,32,65,81,97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V210 low59 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fffff0fff003ffc,0x3ffffffc587e73000fff])),(BitVec.ofNat 152 (word80 [0x90a02802220a228828,0x88202080180e13249249]))),((BitVec.ofNat 152 (word80 [0xfff003ffffffffc000,0x3ff0ffc289a9ddfc0000])),(BitVec.ofNat 152 (word80 [0x4c2b05400ac0302b1,0x142090a00a9d91c71c7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc000fffffffff,0xc000fffd77e88a03f03f])),(BitVec.ofNat 152 (word80 [0x100c11844304410c0,0x11844201616088492492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffff,0xffff00012697f403ffc0])),(BitVec.ofNat 152 (word80 [0x260b026088c0882300,0x22008c10069164924924]))),((BitVec.ofNat 152 (word80 [0xfffffffff000000000,0x39d530dfc0000])),(BitVec.ofNat 152 (word80 [0x380c03800f00f03c02,0x3c08f0219d5204e38e38]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(0,2,41,64,5)]
def g107A : List (List Nat) := [[],[83],[97],[97,83],[48],[48,80],[48,97],[48,97,80],[80,48],[80],[80,97,48],[80,97]]
def g107D5 (j : Nat) := if j=0 then 0x3f else 0
def g107L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g107D5)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,5,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 1=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact (rfl : block g107 4 0 0 = true)
  · exact g107B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 6 := lower_forest (g:=g107) (i:=0) (hints:=16777315) (before_sound K59 V59) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K59 6 [(107,[]),(122,[16,48,32,66,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V59 low107 (by decide +kernel)
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
theorem g155P4_0 : block g155 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B4 : block g155 4 0 1=true := g155P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_0 : block g155 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B5 : block g155 5 0 1=true := g155P5_0
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
  · exact g155B4
  · exact g155B5
  · exact g155B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 7 := lower_forest (g:=g155) (i:=0) (hints:=67) (before_sound K107 V107) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K107 7 [(155,[]),(171,[112,49,64,84]),(217,[97,33,82]),(233,[112,49,33,98,64,82,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V107 low155 (by decide +kernel)
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
theorem g173G : graphValid g173 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K155 V155) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K155 7 [(179,[33,83,67,116]),(185,[112,50,66,80]),(241,[64,82,99,32,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V155 low173 (by decide +kernel)
def g182Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g182C : List ColumnInfo := [(2,0,180,0,5),(4,0,178,0,5),(16,0,166,0,5),(32,0,150,0,5),(18,0,164,0,4),(36,0,146,0,4)]
def g182A : List (List Nat) := [[],[82],[33,84],[33,65,81],[65],[65,82],[81,33,66],[81,66]]
def g182D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g182D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g182H5 := limbs80 #[#[0x0,0x1000000000000000900,0x88400000c20000]]
def g182D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g182H6 := limbs80 #[#[0xc0000000000000000089,0x4020000000000003c045,0x22170,0x18400,0x319f0c000000000,0xc0000000000000000000,0xc4,0x0,0x30700,0x0,0x1c60000000,0x0,0x0,0x6200000111c240000,0x0,0xf1400000000000000,0x5]]
def g182D7 (j : Nat) := if j=0 then 0x1605f else 0
def g182H7 := limbs80 #[#[0x58a500000004,0x20000358ba0062400000,0x391240000764000,0x2c200850000]]
def g182L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g182D4)
  | 5 => (10,2,3,0,0,7,0,g182D5)
  | 6 => (3,1,3,0,0,6,0,g182D6)
  | 7 => (1,0,3,0,0,0,0,g182D7)
  | _ => emptyPacking
def g182I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 29 0 8 2 2 g182H5
  | 6 => lookupWord 4 137 2 10 4 2 g182H6
  | 7 => lookupWord 3 31 1 9 2 3 g182H7
  | _ => fun _ => none
def g182 : Forest := ⟨182,7,fun i => g182Y[i]?.getD (0,0),g182C,g182A,g182L,g182I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P4_0 : block g182 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B4 : block g182 4 0 3=true := g182P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P5_0 : block g182 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P5_1 : block g182 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B5 : block g182 5 0 10=true := (@block_merge g182 5 0 1 9 g182P5_0 g182P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P6_0 : block g182 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B6 : block g182 6 0 3=true := g182P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P7_0 : block g182 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B7 : block g182 7 0 1=true := g182P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182T : checkedTables g182 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g182 0 0 0 = true)
  · exact (rfl : block g182 1 0 0 = true)
  · exact (rfl : block g182 2 0 0 = true)
  · exact (rfl : block g182 3 0 0 = true)
  · exact g182B4
  · exact g182B5
  · exact g182B6
  · exact g182B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182G : graphValid g182 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low182 : Lower true (varsX 182) (graphGoal 182) 8 := lower_forest (g:=g182) (i:=0) (hints:=270599488) (before_sound K173 V173) g182G g182T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K182 := extendKnown K173 8 [(227,[32,16,84,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V182 : Known true K182 := extend_ok (m:=182) V173 low182 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe3fc03fc3f8ffe0,0x1fc7e7f1f53c000f000f])),(BitVec.ofNat 152 (word80 [0x4a1492929289120949,0x42905224353c55555555]))),((BitVec.ofNat 152 (word80 [0xff003fffc003ff1fff,0xe007fffe127b00f00ff0])),(BitVec.ofNat 152 (word80 [0xc1903030310204181,0x83208040807b11111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3ffffffc001fff,0xfff807ffc5a10f00f0ff])),(BitVec.ofNat 152 (word80 [0x102004040400400202,0x4010080000022222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0000000001fff,0xfffff8003bc8f000ff00])),(BitVec.ofNat 152 (word80 [0x604018181821848c0c,0x80203093b8044444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808020202002001010,0x10040400000088888888]))),(0x0,0x0)]
def g211C : List ColumnInfo := [(1,0,210,0,7)]
def g211A : List (List Nat) := [[],[116],[97],[97,116]]
def g211D7 (j : Nat) := if j=0 then 0x3f else 0
def g211L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g211D7)
  | _ => emptyPacking
def g211I (_ _ : Nat) : Option (Nat × Nat) := none
def g211 : Forest := ⟨211,7,fun i => g211Y[i]?.getD (0,0),g211C,g211A,g211L,g211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P7_0 : block g211 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B7 : block g211 7 0 1=true := g211P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211T : checkedTables g211 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g211 0 0 0 = true)
  · exact (rfl : block g211 1 0 0 = true)
  · exact (rfl : block g211 2 0 0 = true)
  · exact (rfl : block g211 3 0 0 = true)
  · exact (rfl : block g211 4 0 0 = true)
  · exact (rfl : block g211 5 0 0 = true)
  · exact (rfl : block g211 6 0 0 = true)
  · exact g211B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211G : graphValid g211 (boundsBefore K182) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low211 : Lower true (varsX 211) (graphGoal 211) 8 := lower_forest (g:=g211) (i:=0) (hints:=16777284) (before_sound K182 V182) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K211 := extendKnown K182 8 [(211,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V182 low211 (by decide +kernel)
def g242Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe1ff00ff0ff87ffc0,0x7fff8fffdcb91000f0ff])),(BitVec.ofNat 152 (word80 [0x244121202209100489,0x20920084c8901111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff000fff87fff,0x80fff1ffb31f200f0f0f])),(BitVec.ofNat 152 (word80 [0x488240414412010902,0x14120410311602222222]))),((BitVec.ofNat 152 (word80 [0x1fffffff00007fff,0xff0001fc0c1ef0f00000])),(BitVec.ofNat 152 (word80 [0x710b8585805c222e0c,0x185c48a10c1ef7777777]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060860443010,0x206000c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080080004020,0x40800100000008888888]))),(0x0,0x0)]
def g242C : List ColumnInfo := [(32,0,210,0,7)]
def g242A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97]]
def g242D7 (j : Nat) := if j=0 then 0x3f else 0
def g242L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g242D7)
  | _ => emptyPacking
def g242I (_ _ : Nat) : Option (Nat × Nat) := none
def g242 : Forest := ⟨242,7,fun i => g242Y[i]?.getD (0,0),g242C,g242A,g242L,g242I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g242P7_0 : block g242 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g242B7 : block g242 7 0 1=true := g242P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g242T : checkedTables g242 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g242 0 0 0 = true)
  · exact (rfl : block g242 1 0 0 = true)
  · exact (rfl : block g242 2 0 0 = true)
  · exact (rfl : block g242 3 0 0 = true)
  · exact (rfl : block g242 4 0 0 = true)
  · exact (rfl : block g242 5 0 0 = true)
  · exact (rfl : block g242 6 0 0 = true)
  · exact g242B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g242G : graphValid g242 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low242 : Lower true (varsX 242) (graphGoal 242) 8 := lower_forest (g:=g242) (i:=0) (hints:=292618304) (before_sound K211 V211) g242G g242T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K242 := extendKnown K211 8 [(242,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V242 : Known true K242 := extend_ok (m:=242) V211 low242 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffc1fffffc82a38,0xf320cf000000ff00ffff])),(BitVec.ofNat 152 (word80 [0xa2008402010080210,0xd000ce21212121212121]))),((BitVec.ofNat 152 (word80 [0xffffe0fff81bd724,0x86d14200ff0000ff0000])),(BitVec.ofNat 152 (word80 [0x2c045002042089c324,0x650420b0b0b0b0b0b0b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000000ffffef6123,0x3c84390000ff000000ff])),(BitVec.ofNat 152 (word80 [0x304160844140072121,0x24843146464646464646]))),((BitVec.ofNat 152 (word80 [0xffffffff00002012c1,0x65fb34ff000000ffff00])),(BitVec.ofNat 152 (word80 [0x400980000981201081,0x21a31014141414141414]))),((BitVec.ofNat 152 (word80 [0x245d5e,0xb16d00000ffff000000])),(BitVec.ofNat 152 (word80 [0x808e01088e02205c4e,0xb120098989898989898]))),((BitVec.ofNat 152 (word80 [0x13a4dd,0x980e26ffff0000000000])),(BitVec.ofNat 152 (word80 [0xf00210f004122458,0x980c24e0e0e0e0e0e0e0]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(2,0,121,0,7),(8,0,115,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,2,41,80,6),(0,8,82,33,6),(0,32,82,9,6),(0,64,41,18,6),(16,0,107,0,6),(1,8,82,32,5),(1,32,82,8,5),(2,64,41,16,5),(8,32,82,1,5),(16,2,41,64,5),(16,64,41,2,5),(40,0,83,0,5),(66,0,57,0,5),(9,0,82,0,4),(9,32,82,0,4)]
def g123A : List (List Nat) := [[],[83],[97],[97,83],[64,49,101],[64,49,97,81],[64,81,49,99],[64,81,99]]
def g123D5 (j : Nat) := if j=0 then 0x30fdd7644c520 else 0
def g123D6 := limbs80 #[#[0x35fb2662906bf644c520,0x9faed98c41afd915148,0x2801028c189438]]
def g123H6 (j : Nat) := if j=0 then 0x9 else 0
def g123D7 := limbs80 #[#[0xd58430afd91209f59610,0x4c520bf58e30bf58e20b,0xc620ff54520ffcc520ff,0x600ff50951ff54620ffc,0xa57177ab69628f2f8f43,0x244c780309103891a1d1,0x910384060208a1850410,0x4286442a3841051c2868,0x40c2840a12020104844,0x785430020a808]]
def g123H7 := limbs80 #[#[0xc40004000,0x1240023f800000,0x6100000,0x510]]
def g123D8 := limbs80 #[#[0xc30ff107f483fc21fd10,0x1fd51fe90ff8c3fa61f,0x1ed13e8a37950782a0c0,0x4b0ca34914284a8cb24d,0x81c48e004a1c28e01521,0x28d2481c20400ca34920,0x460e038a3491a38a180e,0x8a140d1423232cd2]]
def g123H8 := limbs80 #[#[0x10a0006a1eb7e00,0x10500000000000e44,0x170000000000000000,0x87d85018000000000000,0x10200000000c06e09233,0x29bb1000,0x146644a25a1,0x3000040000]]
def g123D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g123H9 := limbs80 #[#[0x882,0x9000000000004e188600,0x40e000000000000038,0x1d3000000000,0x1d000000000000000000,0xc41010007e000,0x2a70000,0x382000,0xe0c0000000160800,0x0,0xd200000086e000000000,0x50bc0800000129546000,0x1a86e1106d0a80,0x6930000000]]
def g123L : Nat → Packing
  | 5 => (1,4,5,0,0,0,0,g123D5)
  | 6 => (4,3,5,0,0,6,0,g123D6)
  | 7 => (11,2,5,0,0,9,0,g123D7)
  | 8 => (9,1,5,0,0,9,0,g123D8)
  | 9 => (1,0,5,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g123H6
  | 7 => lookupWord 1 29 0 9 2 3 g123H7
  | 8 => lookupWord 5 53 3 11 4 3 g123H8
  | 9 => lookupWord 6 97 2 11 4 3 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 1=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 4=true := g123P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_3 : block g123 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_5 : block g123 7 5 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 11=true := (@block_merge g123 7 0 3 8 g123P7_0 (@block_merge g123 7 3 2 6 g123P7_3 g123P7_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 9=true := g123P8_0
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
  · exact (rfl : block g123 4 0 0 = true)
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K242) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=16777283) (before_sound K242 V242) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K242 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V242 low123 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffff62ae,0xa02d1a00000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x28028008400040220a,0x20011201041041041041]))),((BitVec.ofNat 152 (word80 [0xfc003fffe0ffe02d42,0xa6e2f08003f00003f000])),(BitVec.ofNat 152 (word80 [0x304b04500210822502,0xa4e2d00b2cb2cb2cb2cb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd84,0x995842c000003f00003f])),(BitVec.ofNat 152 (word80 [0x420c21608485001c84,0x895840e69a69a69a69a6]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156a9c0fc000003ffc0])),(BitVec.ofNat 152 (word80 [0x809009800026048045,0x1142994514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e010838088161,0x10a08c18618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300300210c0104890,0x4a000060820820820820]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(1,0,186,0,7),(2,0,185,0,7),(8,0,179,0,7),(16,0,171,0,7),(32,0,155,0,7),(128,0,59,0,7),(0,2,41,144,6),(0,8,146,33,6),(1,8,146,32,5),(9,0,178,0,5),(10,0,177,0,5),(16,2,41,128,5),(18,0,169,0,5),(32,8,146,1,5),(34,0,153,0,5),(128,2,41,16,5),(17,0,170,0,4),(26,0,161,0,4),(33,0,146,0,4),(33,8,146,0,4),(41,0,146,0,4),(48,0,139,0,4),(144,0,41,0,4),(144,2,41,0,4),(146,0,41,0,4),(160,0,27,0,4)]
def g187A : List (List Nat) := [[],[112,49,84]]
def g187D5 := limbs80 #[#[0x50d504c3ccdd15454110,0x4c2d66154354130f1954,0xd915354130e596454d50,0xd8940f195350d5050396,0xb6785230602b9e0553,0x50400]]
def g187D6 := limbs80 #[#[0x3e8a1a60887615254110,0xeb2a6a8261dc5515044,0x43f8ba260884ed75d894,0x20fe6e8a8221fc5d1504,0x4c3eca1aa0985f77154d,0x130ef2a8a8261f6dcd50,0x34c37db22a0986f96454,0xd30dbacaa1a61e75514,0x434c2eebaa86986df655,0x54d30dbac8a9a6177dd5,0x5644c27ebb2a8986df64,0x3595309faebb22613fdd,0xd1654c36fb9aca985df7,0x43541409fae9b2a613fd,0xdd150503bca9aa0a07b9,0xd53d8940ddec498a81ee,0xfdd543503cea9a86a06e,0xfd74d8d509fceca1aa16,0x5a0d0160027ebaec0a1c,0xfa3b0de360ca2d08e1e0,0x8a5f1665613a49116400,0x1a851f6781da7119e661,0x92a126e9825a932468c2,0x10404c5c317130aaea62,0x7c0099c005c364670017,0x4c16213084821918840,0x84c1130508000044c10,0x5c00217045c110431713,0x81c1808044001411704,0x605c40317100800702,0x1040130401513081c082,0x4207020800007098426],#[0x18]]
def g187H6 := limbs80 #[#[0x500000000e00088003a3,0x2000000f40000007b00c,0x510000000026a37]]
def g187D7 := limbs80 #[#[0x954910fc54110fc4c110,0xd8940f994b10f994910f,0x5110fd50d10bfd9110bb,0x310fd50f10fdd9110fd5,0x30f750d30fe54130fd55,0xbfd9130bf59130f754d,0xfe54140bfd9530bf5953,0xfd8143bfd8d50ef50d40,0x55130ff54d20ff54520b,0xc540ff59530ff59130ff,0xd50ff50d50ff54d40ff4,0xff58143ffd8d50ff58,0x1dc2f8470730be12c148,0x738cf16e2b45188b102,0xc984ad256ea392f22e3e,0x104057d4ee9cc37d6c4c,0xc98841716464788bb10a,0x50b845c985931082e210,0x6cb8f0c40f0064b00886,0xe4c2265c20e0a00b823c,0xc226602488a40b803c62,0x164c6211930886946304,0xa1320827805c42a50841,0x8281264062a421860a04,0x2e405201c202305c6281,0x161464c78c949861c202,0xa4c6801c2022e295291a,0x890e1890e18328182812,0x4880844906325c990110,0xb121210c0c190425c32a,0x7088212e197265438484,0xa9220351201801]]
def g187H7 := limbs80 #[#[0x1010880344,0x0,0x145c0000000000,0xb92000000005060000,0x40400000000000d44000,0x70100000000000,0x3c94460000000000000,0x0,0x1a78,0x14a80000000000,0x2480000000,0x0,0x24a0a000000000000000,0xf0006840000000000000,0x71000000000000003e,0x0,0x680004394f43c9b,0x6647093720531ae00000,0x1a,0x73800000000000000,0xc000b800000000000000,0x83c0040,0x3c0000000c8c000000,0x80000000000000000000,0x2380009fb4,0x0,0x0,0x31a,0x20000000000000000000,0xa583000000000a44f,0x0,0x4140008309d02200000],#[0x1600000000d2c0000000,0x21fa,0x40058900000000000386,0x181,0x0,0x462000000000]]
def g187D8 := limbs80 #[#[0xd30fe907f443ee21f510,0x83fd31fe90ff543fa81f,0xde51210a82a007f50ffa,0x42220171b5580b15121c,0x402cf1e422204060606,0x6220b009951349104222,0x85060a58e14c74039648,0x28d2c81248e13e220500,0xc936280b38f1a480f444,0x54496084b88d0]]
def g187H8 := limbs80 #[#[0xc0323812002712042,0x4800035650a994dab1a1,0xd807e83256871c02014,0x4433514751f03a0032b0,0x7723f080032e00281000,0x2e728cb3912f0854121,0x8dbd5001f1c088000000,0x20121543f26699000b45,0x4f2cf62c44c03,0x25f0c00418ebf820c280,0x2956]]
def g187D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g187H9 := limbs80 #[#[0x736000001d5000001000,0x73c1400000000000,0xd8000010300000,0x6e40000000000000000,0x9f100048000000001710,0x18100000000000001a94,0x1c6d50000000000000,0x5e000000000000006900]]
def g187L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g187D5)
  | 6 => (38,3,5,0,0,10,0,g187D6)
  | 7 => (34,2,5,0,0,11,0,g187D7)
  | 8 => (11,1,5,0,0,9,0,g187D8)
  | 9 => (1,0,5,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 29 2 8 3 1 g187H6
  | 7 => lookupWord 13 271 2 11 6 1 g187H7
  | 8 => lookupWord 13 67 6 11 6 1 g187H8
  | 9 => lookupWord 4 71 0 9 4 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 7=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_1 : block g187 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_5 : block g187 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 38=true := (@block_merge g187 6 0 1 37 g187P6_0 (@block_merge g187 6 1 4 33 g187P6_1 g187P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_6 : block g187 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_23 : block g187 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 34=true := (@block_merge g187 7 0 6 28 g187P7_0 (@block_merge g187 7 6 17 11 g187P7_6 g187P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_2 : block g187 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 11=true := (@block_merge g187 8 0 2 9 g187P8_0 g187P8_2)
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
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=67) (before_sound K123 V123) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K123 10 [(187,[]),(249,[112,49,33,98,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V123 low187 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffff72ce,0xb0ac1200000fc0000fff])),(BitVec.ofNat 152 (word80 [0x28428408401040324a,0x20a01209249249249249]))),((BitVec.ofNat 152 (word80 [0xfc003fffe0ffe02d22,0xa663708003f000fff000])),(BitVec.ofNat 152 (word80 [0x300b00500200822402,0xa44350030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd85,0x995842c000000000003f])),(BitVec.ofNat 152 (word80 [0x428c296084a5008d85,0x995840f6db6db6db6db6]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804c,0x6156a9c0fc003f03ffc0])),(BitVec.ofNat 152 (word80 [0x801001800006040004,0x1142984104104104104]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e010838089160,0x18a08418618618618618]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300300210c0104891,0x42000060820820820820]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(0,8,210,1,8),(8,0,211,0,8),(1,8,210,0,7),(2,0,217,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(66,0,153,0,5),(18,0,201,0,4),(80,0,139,0,4),(130,0,89,0,4),(192,0,27,0,4)]
def g219A : List (List Nat) := [[],[116],[97],[97,116]]
def g219D5 := limbs80 #[#[0x50d414c7a55954350531,0x4c7655d54350531e9765,0x5d55350531f155454d41,0x54531f155450d514c755,0xe576454d514c6d561543,0x5d9544c6d5e115354531,0xc032d1d371595318f781,0xa0d49d2213c6ca0d141,0x808402000]]
def g219D6 := limbs80 #[#[0x7aaa9aa298f954350531,0x1faaa6a0a632fdd1654c,0xc77ab2a8298fb5545053,0x31beaeaa0a63bdd95414,0x4c77bb22a298fd543545,0xd31dbecaa1a63b759543,0x34c7aeaa2a698fd77154,0x4d31dbec8a9a63b75915,0x644c67ebb2a898ddf745,0x595319faebb22633fdd5,0x5654c6dfba2ca98df771,0x459531d78e8b2a63bddc,0xd3654c67fba2ca98ebf7,0x74585539feeca9a833f5,0xe4b110027eba6c2a9dbf,0xd72ac4fa65187f39194b,0xc822706803cdccd9662f,0xcadeabf59a9d1a813396,0x1710d0d27217884e41c4,0x801010a08504402071e0,0x60430220108080141ac0,0x100802016c0f0040c60d,0x38f00f18100180005040,0x1a839]]
def g219H6 := limbs80 #[#[0x0,0x0,0x10100000a0c0000000,0x24000,0x89,0x2c50000000000,0x0,0x2c800000,0xa84000000000000,0x0,0x0,0x0,0x0,0x0,0x100,0x226000000000000000,0x5800000000,0x0,0x0,0x0,0x6000000000000000,0x0,0x0,0x2d000000000000000000,0x0,0x0,0xd7002540000000000,0x0,0x0,0xd1c00,0x0,0x0],#[0x0,0x0,0x3c2003e900000,0x91000000000000000000,0x0,0x3280000000]]
def g219D7 := limbs80 #[#[0x750d31fd54531fd50531,0xd9131bf59131f754d31f,0x8553bfd9531bf59531bf,0x531ff59131ff55131bfd,0x53ff58553ff54d41ff59,0x360a81f84e09000ffd85,0x799bc679865d14a4b0fc,0x80f25a4188c729071616,0x8f2586248c44c958c728,0x881492241b11f21c8c44,0x810a2235859321d5c76c,0x2c80a4d714e6c86156c8,0x5050718a2155842481c3,0x4c5288564c704c71a34,0x1a4c7]]
def g219H7 := limbs80 #[#[0x648e0010,0x0,0x0,0xe4000000000000,0x4000000006c800102400,0x39c0031,0x3070004600019b0,0x0,0x54e0004400000000,0xe960000051c0000000,0xa80a8a34000000,0x0,0x2e00000000000,0x4160,0x143c,0x10000000059500000000,0x5740,0x70a000000000000,0x71c0000024ab26,0x1ca80068400000,0x6340,0x181000000000000,0x0,0x25480000,0x0,0x0,0x98a00000000000e5c00,0xc0000021100110c0000,0x18c00000000000000004,0x118a670b52c001,0x0,0x0],#[0xc3b88c00705000000004,0x183]]
def g219D8 := limbs80 #[#[0x879aa407f54ffa83fd31,0x90c3b469238d145aa324,0x11accc4]]
def g219H8 := limbs80 #[#[0x5202eb98000009a08020,0xf08008c107d4f3308c00,0xe82c6728000038e0012d,0xd000040784001d0a3003,0x32ec500314003c9435a8]]
def g219D9 (j : Nat) := if j=0 then 0x1654321bf else 0
def g219H9 := limbs80 #[#[0x8102d89c0000001000,0x840000]]
def g219L : Nat → Packing
  | 5 => (11,4,4,0,0,7,0,g219D5)
  | 6 => (30,3,4,0,0,9,0,g219D6)
  | 7 => (15,2,4,0,0,10,0,g219D7)
  | 8 => (3,1,4,0,0,7,0,g219D8)
  | 9 => (1,0,4,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 307 0 10 4 2 g219H6
  | 7 => lookupWord 11 239 2 11 5 2 g219H7
  | 8 => lookupWord 6 37 5 10 4 2 g219H8
  | 9 => lookupWord 1 17 0 8 2 2 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 11=true := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_3 : block g219 6 3 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 30=true := (@block_merge g219 6 0 3 27 g219P6_0 g219P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_9 : block g219 7 9 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 15=true := (@block_merge g219 7 0 9 6 g219P7_0 g219P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 3=true := g219P8_0
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
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=16777283) (before_sound K187 V187) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K187 10 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V187 low219 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff83ffffffff74828,0x84baec000007f0003fff])),(BitVec.ofNat 152 (word80 [0x105082080104070820,0x886c12244891224489]))),((BitVec.ofNat 152 (word80 [0x3ffc1ffe029e0c,0x11cdd30003f80fe00000])),(BitVec.ofNat 152 (word80 [0x56100504048228c0c,0x14dc20e1c3870e1c387]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0ca,0xa3210b000000001fc07f])),(BitVec.ofNat 152 (word80 [0x21802460921008d08a,0xa32101a54a952a54a952]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f6,0x491ab201fc00001fff80])),(BitVec.ofNat 152 (word80 [0x460008800460402454,0x40129248912244891224]))),((BitVec.ofNat 152 (word80 [0x93711,0xa28774fe00000fe00000])),(BitVec.ofNat 152 (word80 [0x78020f010780893211,0x82823470e1c3870e1c38]))),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x800430021801004102,0x3c000181020408102040]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(8,0,227,0,8),(1,0,234,0,7),(2,0,233,0,7),(32,0,203,0,7),(64,0,171,0,7),(0,2,41,192,6),(0,8,194,33,6),(0,64,41,130,6),(128,0,107,0,6),(1,8,194,32,5),(2,64,41,128,5),(32,8,194,1,5),(66,0,169,0,5),(128,2,41,64,5),(128,64,41,2,5),(33,0,194,0,4),(33,8,194,0,4),(130,0,41,0,4),(130,64,41,0,4)]
def g235A : List (List Nat) := [[],[97],[80],[80,97]]
def g235D5 := limbs80 #[#[0xd8b514c32bdd36254530,0x308ed87]]
def g235D6 := limbs80 #[#[0x276baec4987595354130,0xfb6e6a8261f654d504c,0xc377b12a2986ef625053,0x30bf2e1a8a616fdd1514,0x4c27ebb6a2986ef62d45,0xd50bf6e0a9aa1bedc165,0xb0027fb9ac1a8f7b7054,0xc632c1448c3f1c0c4441,0xf142207803c687401e4d,0x68811004238040306071,0x81a882030707002a40,0x201100780402060]]
def g235H6 (j : Nat) := if j=0 then 0x24 else 0
def g235D7 := limbs80 #[#[0xb54b50db54950bbd8930,0x58b51afd9151bb58b50d,0x9530fe54130bfd8d10bb,0xd50df54d50fb54950bf5,0x51bf58f50bfd8d50dfd4,0xff54530ff50530bf583,0xff58d50ff54d50ffd453,0x881198520a400ffd8d50,0xdd7681775712c40cda2a,0x711bf6e2aae829662281,0xc83b10d202e4c50c3411,0x843e01a2c11a2c31a402,0x8234595931c210246c7,0xb0101a3c5c02080a1f26,0xc08e08a386900c385080,0x80c3c709838118d1c70d,0x42071c34807803850808,0x450600c0a2a107925608,0x141808078e920c022145,0x82012020160104031215]]
def g235H7 := limbs80 #[#[0x32700002002870053e,0x2cea80ce28000022b,0x31641811cbb24cd05606,0x89600000c0000100]]
def g235D8 := limbs80 #[#[0xf50fea87f4c3fa21ed52,0x685400ffa8ff547fa83f,0x2238d4069c439c8c0481,0x489020308a90180d1e40,0x92388e04d80720714182,0xa30a180c3460ce060345,0x12a48022071238458121,0x8e]]
def g235H8 := limbs80 #[#[0x8912692d48800a907017,0xd0fc3487510910b04000,0xe00163f8b000c3341d80,0x10005c90004c30974291,0x8a00080400000000b02a,0xc29828b189d01b]]
def g235D9 (j : Nat) := if j=0 then 0x41882017f else 0
def g235H9 := limbs80 #[#[0x12000000000000013e0,0xc4c00000000001030000,0x308000000000000000f2,0x118019100000004e,0x132000048800,0x184000000000da000,0x1ce00006]]
def g235L : Nat → Packing
  | 5 => (2,4,5,0,0,3,0,g235D5)
  | 6 => (14,3,5,0,0,9,0,g235D6)
  | 7 => (21,2,5,0,0,10,0,g235D7)
  | 8 => (8,1,5,0,0,9,0,g235D8)
  | 9 => (1,0,5,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 5 1 0 g235H6
  | 7 => lookupWord 5 29 4 10 4 2 g235H7
  | 8 => lookupWord 7 41 4 11 5 2 g235H8
  | 9 => lookupWord 3 59 2 9 3 2 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 2=true := g235P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_2 : block g235 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 14=true := (@block_merge g235 6 0 2 12 g235P6_0 g235P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_6 : block g235 7 6 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_15 : block g235 7 15 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 21=true := (@block_merge g235 7 0 6 15 g235P7_0 (@block_merge g235 7 6 9 6 g235P7_6 g235P7_15))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_1 : block g235 8 1 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 8=true := (@block_merge g235 8 0 1 7 g235P8_0 g235P8_1)
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
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=16777315) (before_sound K219 V219) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K219 10 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V219 low235 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ffffffff878166,0xec12f000000fc003f03f])),(BitVec.ofNat 152 (word80 [0x44510a208081100144,0xe4027249249249249249]))),((BitVec.ofNat 152 (word80 [0xfff800ffc3fff83588,0x9c8d500003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x80604c010812013480,0x8c0550c30c30c30c30c3]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0003ffffda3c,0x91312000fc003f000fff])),(BitVec.ofNat 152 (word80 [0x80100a1024000a38,0x11100104104104104104]))),((BitVec.ofNat 152 (word80 [0xfffffffffc0000462b,0x2b87903f00000003f000])),(BitVec.ofNat 152 (word80 [0x902604c013822462b,0xb858596596596596596]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe03807021c0444104,0x62e88618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400800200000000,0x820820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,8),(16,0,227,0,8),(32,0,211,0,8),(2,0,241,0,7),(64,0,179,0,7),(128,0,115,0,7),(66,0,177,0,5),(130,0,113,0,4),(192,0,51,0,4)]
def g243A : List (List Nat) := [[],[97]]
def g243D6 := limbs80 #[#[0xe5c1243e237355454541,0x5]]
def g243D7 := limbs80 #[#[0xf55151bf59541fd54541,0x42a00ff59151bfd9151d,0xc31187cb0571186ae8a5,0x481c5cb05318c82071b2,0x81c60d4cb0c471]]
def g243H7 (j : Nat) := if j=0 then 0xd0 else 0
def g243D8 := limbs80 #[#[0xa3942261a403faa3fd41,0x1e851ca111c]]
def g243H8 := limbs80 #[#[0x113418000000,0x93000000003000000000,0xa200]]
def g243D9 (j : Nat) := if j=0 then 0x5432011bf else 0
def g243H9 (j : Nat) := if j=0 then 0xa4000f else 0
def g243L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g243D6)
  | 7 => (5,2,4,0,0,8,0,g243D7)
  | 8 => (2,1,4,0,0,6,0,g243D8)
  | 9 => (1,0,4,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g243H7
  | 8 => lookupWord 1 23 0 8 3 1 g243H8
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
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := lower_forest (g:=g243) (i:=0) (hints:=16777284) (before_sound K235 V235) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K235 10 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g250Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffc1ffff602cc,0x14eee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060084,0x4ce80a142850a14285]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc003ffffffe02942a,0x33d9d300000000003f80])),(BitVec.ofNat 152 (word80 [0x324b2450120822942a,0x33c941a74e9d3a74e9d3]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf8c9,0x81210b0003f80fe0007f])),(BitVec.ofNat 152 (word80 [0x400c01608090098849,0x12102142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x491ab201fc0000003f80])),(BitVec.ofNat 152 (word80 [0x8090098004e04820d5,0x4012b258b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803710,0x82821060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801004002,0x3c000581020408102040]))),(0x0,0x0)]
def g250C : List ColumnInfo := [(0,8,210,32,8),(8,0,242,0,8),(2,0,248,0,7),(16,0,234,0,7),(32,8,210,0,7),(64,0,186,0,7),(128,0,122,0,6),(18,0,232,0,4),(66,0,184,0,4),(80,0,170,0,4)]
def g250A : List (List Nat) := [[],[100],[65],[65,97],[97,65],[97]]
def g250D4 (j : Nat) := if j=0 then 0x1a2b6460b5454120 else 0
def g250D5 := limbs80 #[#[0x50940483aa5954250120,0x483ca5515250120eab65,0x5915254120d697554940,0x54120e6b64549504839a,0xb6982d51504835add152,0x5d9544838ed935454120,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x8d01d345ca0d141c032e,0x6080002836294c]]
def g250H5 (j : Nat) := if j=0 then 0x7a4 else 0
def g250D6 := limbs80 #[#[0x3b4a92a0907a94250120,0xfd2a4a02412fdd16548,0x837db2a80906f9655012,0x20fd6e4a8241fa549504,0x483bdaa2a09077954541,0x120df6c8a8241be59150,0x44833eb2aa8905fb7454,0x51209feecaa2413f5d95,0x544835fb26a8905f970d,0x591209faedaa2419f597,0x1654827ebaec8904ff75,0x59520b7ee8b2a417edc,0xd1654835e3a2ca906fb7,0x70995209fee8b2a41afd,0x5d3654827ebb4ca905f9,0xb7054950bf6e0a92a13f,0xfd93525433fb22a4a877,0xbf7458950afae9a92a19,0x3fdd162d427eba6c4a85,0x78a8431e4d85f258a401,0x5610fb7aba1b6d564309,0x75a2b74ea0cee5d288dc,0xee46ef5da1cde3b037bb,0x8178f047085f3f6ba9c,0x82141100f1e0106e88e1,0x810000608205c7806102,0x800c1c4080141c60801,0x400e0e2043820700400a,0x8604002005041020050,0x35040000a6]]
def g250H6 := limbs80 #[#[0xb1e16a1488000433100b,0xd1800019a012082a7cb8,0x80a800280958c8800000,0x9c007b0a0f6240000062,0xc3000000c9b41ba3850c,0x80079320b45000000001,0x488426000c8]]
def g250D7 := limbs80 #[#[0xf59120fe54120fe50120,0xd9520bf59520bfd9120b,0x8950dfd4950df54950bf,0x120ff55120bf58b50bfd,0x20ff59520ff59120ffd5,0xff58950ff54950ff995,0x90ba2585a0c000ffd895,0xc9ce691865a144481023,0xb1c158c79aa528ba107,0x638b4242c461f48c6207,0x4186c55d07149207c465,0x4e2105c741c4c478e217,0x53d62d051e2d131851b4,0x51c61858871054c6d04c,0x88710920789516245019,0xf1c064e21624501c4195,0x60930c75530]]
def g250H7 := limbs80 #[#[0x830c001380000f045900,0x2089843438aa018b1010,0xb0248cd685103e909c98,0x9f623284190a15f0ee81,0x2681a000000000083264,0x1f868694800000000000,0x832d11c8300070978450,0x40b303d89b810e8b7265,0x3848a1b900a27c83d,0x1123901033f513a16000,0xe0000000000c02800304,0x2781a000310c00000094,0x7591000000030bf1160,0x8e14d268000000c627,0x3060001a030000003,0x8000000000308c891285,0x6884400090361ea2,0xa9600521841a600]]
def g250D8 := limbs80 #[#[0x79aa407fd43faa1fd20,0xa0d135662a0d131ea315,0x1acc46]]
def g250H8 := limbs80 #[#[0x40f00000000060a00044,0x921000000,0x4270000000000,0xd0b00000000000090300,0x101000000009a6b,0x52f0000000000000000,0x54030500,0x31907000000000000000,0x8d0d00004756a0000009,0x70cb2,0x0,0x0,0xb0600000000000000000,0x430187000000000000,0x4000900c100000000000,0xe0452900000062,0x802,0x3410000000009110,0xb0880ec2600]]
def g250D9 (j : Nat) := if j=0 then 0x1532417f else 0
def g250H9 := limbs80 #[#[0x3d432007100000709b2,0x3d262888]]
def g250L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g250D4)
  | 5 => (13,4,4,0,0,7,0,g250D5)
  | 6 => (39,3,4,0,0,9,0,g250D6)
  | 7 => (18,2,4,0,0,10,0,g250D7)
  | 8 => (3,1,4,0,0,7,0,g250D8)
  | 9 => (1,0,4,0,0,0,0,g250D9)
  | _ => emptyPacking
def g250I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 6 0 2 g250H5
  | 6 => lookupWord 7 47 4 11 4 3 g250H6
  | 7 => lookupWord 18 101 6 13 6 3 g250H7
  | 8 => lookupWord 8 127 1 12 5 3 g250H8
  | 9 => lookupWord 2 13 1 9 2 3 g250H9
  | _ => fun _ => none
def g250 : Forest := ⟨250,9,fun i => g250Y[i]?.getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P4_0 : block g250 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B4 : block g250 4 0 1=true := g250P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P5_0 : block g250 5 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B5 : block g250 5 0 13=true := g250P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_0 : block g250 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_3 : block g250 6 3 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B6 : block g250 6 0 39=true := (@block_merge g250 6 0 3 36 g250P6_0 g250P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_0 : block g250 7 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_10 : block g250 7 10 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B7 : block g250 7 0 18=true := (@block_merge g250 7 0 10 8 g250P7_0 g250P7_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P8_0 : block g250 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B8 : block g250 8 0 3=true := g250P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P9_0 : block g250 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B9 : block g250 9 0 1=true := g250P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250T : checkedTables g250 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g250 0 0 0 = true)
  · exact (rfl : block g250 1 0 0 = true)
  · exact (rfl : block g250 2 0 0 = true)
  · exact (rfl : block g250 3 0 0 = true)
  · exact g250B4
  · exact g250B5
  · exact g250B6
  · exact g250B7
  · exact g250B8
  · exact g250B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low250 : Lower true (varsX 250) (graphGoal 250) 10 := lower_forest (g:=g250) (i:=0) (hints:=288444480) (before_sound K243 V243) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K243 10 [(250,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V250 : Known true K250 := extend_ok (m:=250) V243 low250 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ff0000001ff,0x7fffe200383270bcfe])),(BitVec.ofNat 152 (word80 [0x108844221108844221,0x10884422001812301466]))),((BitVec.ofNat 152 (word80 [0x3fe00007fc0000,0xff80000020d0c1b3734c])),(BitVec.ofNat 152 (word80 [0x582c160b0582c160b,0x582c16020504091714c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe00,0x3fec46e10dcc438f])),(BitVec.ofNat 152 (word80 [0xa351a8d46a351a8d46,0xa351a8cc46e10dc44388]))),((BitVec.ofNat 152 (word80 [0x7fc0000ff8000000,0xffffc00087060e0f83f0])),(BitVec.ofNat 152 (word80 [0xa05028140a0502814,0xa0502808202040e8280]))),((BitVec.ofNat 152 (word80 [0xff800000000003ffff,0x10f807f00ffc01])),(BitVec.ofNat 152 (word80 [0x4c26130984c2613098,0x4c261310a806e00ba801]))),((BitVec.ofNat 152 (word80 [0xffffc0000,0x1f0007fff00001])),(BitVec.ofNat 152 (word80 [0x70381c0e070381c0e0,0x70381c160005bb600001]))),((BitVec.ofNat 152 (word80 [0xfffffffff000000000,0x1ffff800000000])),(BitVec.ofNat 152 (word80 [0x804020100804020100,0x8040200955a000000000]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(2,0,249,0,10),(8,0,243,0,10),(16,0,235,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,10),(0,8,210,33,9),(1,8,210,32,8),(9,0,242,0,8),(24,0,227,0,8),(32,8,210,1,8),(40,0,211,0,8),(0,2,41,208,7),(0,32,82,137,7),(0,64,41,146,7),(3,0,248,0,7),(10,0,241,0,7),(17,0,234,0,7),(18,0,233,0,7),(33,0,210,0,7),(33,8,210,0,7),(34,0,217,0,7),(41,0,210,0,7),(48,0,203,0,7),(65,0,186,0,7),(66,0,185,0,7),(72,0,179,0,7),(80,0,171,0,7),(96,0,155,0,7),(130,0,121,0,7),(136,0,115,0,7),(160,0,91,0,7),(192,0,59,0,7),(1,32,82,136,6),(2,8,208,33,6),(2,64,41,144,6),(8,32,82,129,6),(16,2,41,192,6),(16,8,194,33,6),(16,64,41,130,6),(64,2,41,144,6),(128,2,41,80,6),(128,8,82,33,6),(128,32,82,9,6),(128,64,41,18,6),(129,0,122,0,6),(144,0,107,0,6),(18,64,41,128,5),(80,2,41,128,5),(82,0,169,0,5),(98,0,153,0,5),(129,32,82,8,5),(130,64,41,16,5),(144,2,41,64,5),(144,64,41,2,5),(192,2,41,16,5),(194,0,57,0,5),(19,0,232,0,4),(35,0,208,0,4),(35,8,208,0,4),(49,0,194,0,4),(49,8,194,0,4),(50,0,201,0,4),(67,0,184,0,4),(90,0,161,0,4),(106,0,145,0,4),(146,0,41,0,4),(146,64,41,0,4),(161,0,82,0,4),(161,8,82,0,4),(208,2,41,0,4),(210,0,41,0,4)]
def g251A : List (List Nat) := [[],[97]]
def g251D6 := limbs80 #[#[0x61b16e95746456358130,0x4c362dd2ee8c8ac6b02,0xac0a0665ba56519158d6,0x3158140fc22c8a9aa298,0x22a2b028158eed598591,0x56350d60502b4dd9b30b,0xca322b1ac0a05e1bb568,0x1953dc9514c540cc774a,0x3c32a7b92a298a81e516,0x5459654f7254531503ca,0xea8f2ca9ee4a8a62a07,0xa81b5169953dc9514c54,0x31503e22b2ac7b92a298,0x8a62a074c59658f72545,0x9614c540f0cb0cb2ee4a,0xb92c298a81f1159553dc,0x8f7258531502e62db2a7,0xab1ee4b0a62a078c5855,0xe5563dc9614c540f18f0,0x63daac7b92c298a81d31,0x7865855977258531502e,0x4093cf62d42cbb9262a0,0x8a81a59297a161b724c5,0x551503c32b2f07b92c2a,0xb0aa2a0746565e4f7258,0x1f7454560f42acbc1a86,0x641f0c84c01077ecda9e,0x3cf876381a8ae441f0e0,0x93318cc05d2d15c9b4aa,0x14060606f075391bcd86,0x42836000400008c08200,0x242820014810400002],#[0x1f020400000000000000]]
set_option maxRecDepth 16000 in
def g251D7 := limbs80 #[#[0x61442cd9a3dd16358110,0x898158130b3568f7458d,0x2e4d62605604c3acb835,0x502e5ba56456358130db,0x614c540f5154f7254531,0x9586dc931503cc563dc9,0x3c6565dc96154540a5be,0x4c560f9154d625453158,0x8758951582a6fa561d62,0xd9636438150d60ab3e8d,0x531cae59190e05435832,0xe05764c7e456454d6254,0x65dcd4358551c5d21590,0xf235937350d62547c55,0xd30443ed18458d614c11,0x58d3158110f365d98458,0xb4e11634c560443ed184,0x443eb3845913158110f,0xd6358110f366117358d6,0xe11645cd60443cdb845c,0x43cbb845937358110f2e,0x458110bae68f84591604,0x78459160443cb975e116,0xb558654d514c520f2edd,0xc520dd56595354531483,0x354531483e556558d514,0x586595514c520db56596,0x20f955955358531483a7,0x8531482ed5a654d614c5,0x558d614c520eb5615635,0xdb5e556358531483ad78,0x31482ed7a558d614c520],#[0x61654c520e9d61565585,0xd25791619314823f7a16,0x483a7565e0d6154520cd,0x4158130d9d5979358551,0x5d64505604c36db9758d,0x26f9a6e5d4158130daee,0x58130fb2e0d62545604c,0x43545604c3e996450d51,0xd97458d5158130bb6699,0x130f36dd163545604c3c,0x5c5604c3cb9745915158,0x6450d7158130fb2e0d62,0xdb6e59435c5604c3e99,0x5604c2ed9a650d715813,0xe0d7158130f365d1635c,0x2e5d1645c5604c36db96,0x4c34fb965d17158130f,0xf7158130f3661163dc56,0xe1164dc5604c3cdb8458,0xc3ad98458d8158130f2e,0x158130eb6e1163605604,0x19158d604c36d964e4d8,0xcdb746456358130f365d,0x8130db66519158d604c3,0x158d604c3cd974e45635,0x994e456358130f36dd39,0x30eb5e1d63585414c36d,0xd9414c2adda6e1d63505,0x550d6154530a3f69b875,0xf355d163585514c3e556,0x514c3cd77458d6154530,0xd16154530f1d59574585],#[0x76197458d514c3c7565d,0x4c38dd86dd16354530e3,0x7454530a77e8d875d151,0xd1635c5614c30ff96e19,0x2b5fa561d4358530f355,0x58530f355d39158d614c,0x7458d614c3cd774e4563,0xdf85dd16358530e37e15,0x530bb6e819458d614c38,0x50d714c297fa561d7458,0x865d1635c530e37e1976,0xe37e1b935d9714c38df,0x5634c2d5fa56457650d3,0xdd18158d30d57e557460,0xd7e5584605634c355f95,0x64c335f95e0d815d930c,0x1815d930d57e57836057,0xe5784605764c317f9561,0x3f51535453158140c5f,0x158140fb458d514c5605,0xd814c560503eb1645453,0xeb1646053158140fb458,0x8140fa6591534c560503,0x34c560503ed3a158d315,0x9a458d3158140fa6e116,0x40db6655634c560503e9,0xc5605036db9558d31581,0x55913158140dae655644,0xdae661644c5605036bb9,0x605036bb985913158140,0x6131581409dee95984c5,0xe69b984c5605026fba66],#[0x503e996350d51581409b,0x5158140de6e4d4354560,0x939354560502eb9a650d,0x2ebba35915158140dae5,0x58140dae661645456050,0x98545605036bb9859151,0xfba666151581409f6e8d,0x1409be69b98545605026,0x605605036db9358d8158,0x64e4d8158140eae59183,0xeae61564605605036b9,0xd605036bb95591815814,0x58d4358140fa66856350,0xae6519158d60503e9ba1,0x502e7ba56456358140d,0x58358140dae6539158d6,0x58f72545315036b964e4,0x3d6565dc9514c540f71,0x14c540e7961b72545315,0xb72545315039e786dc95,0x5e796dc9514c540d7965,0xc540b7969b7254531503,0x354531503f156454d514,0x58654d514c540f555d95,0x40ed5e195354531503b5,0x45315037559654d514c5,0x558d514c540dd5e59535,0xdb56596354531503e556,0x31503a7586595514c540,0xc9614c540f7154f72585,0x96177258531503ce565d,0x5039e785dc9614c540e7],#[0x614c540d79e577258531,0x995358531503e556554d,0x3e95a458d614c540bb56,0x4c540eb5615635853150,0x6358531503ad78558d61,0xd7a558d614c540db5e55,0x540f3569d6358531502e,0xdc931503a7585595614c,0x8654f724c540e7361953,0xd7365953dc9315039cf,0x931503dc7a158f724c54,0x58f724c540f3359563dc,0x73e1563dc9315039cd85,0x1502dcfa558f724c540e,0x7724c540e3b61965dc93,0x65985dc9315029eda859,0x29efa6617724c540c7b,0x24c540c7b65b85dc9315,0x586dc9315029eda6e177,0xd6fa561b724c540b79e8,0xc540e79e8586dc931502,0x6dc93150396ca561b724,0xfa561b724c540e5be958,0x40a7b69786dc9315029e,0x19315023f7a1661654c5,0x3dc96154540cdd257916,0xe79e0f7258551503ce56,0x515035e793dc96154540,0xd6154540fa558d43585,0xd5954358551503b97835,0x503a7565e0d6154540f8,0x7254540d9d5979358551],#[0xa163dc9515038ed8658f,0x31ed96e0f7254540a7be,0x54540a7b69b83dc95150,0x86dc9515029efa361b72,0x9d8658d4354540a7b68f,0x540e675db8350d51503a,0x50d51502b9da6e0d4354,0xa35db8354540ae7e8d86,0xf39e8563dc9615029df,0x9615038ef8558f725854,0x60f7258540b3be9563dc,0x5be9583dc961502de7a1,0x15038ed65e0f7258540b,0x77258540a7b69783dc96,0xe856350d615029eda3e1,0x3a9f8558d4358540fa5,0x3dc940b5be959158f725,0x59158d435025eda5e456,0x33f956118158d40bc7e9,0xc560c5f61f9560563503,0x354531583e556454d514,0x57458d714c560f55dd15,0x60f35dd1635c531583cd,0x9131582edba0651634c5,0x561d744c560a9fe95875,0xa5fe9587dd13158297fa,0x315821fda9e1f744c560,0xcd6254560a5fe9598dd1,0x75938350d51583acf83d,0x5831de97e0d4354560ea,0x6454560c7765383dcd51,0x8d875d151582adfa361d],#[0x29dfa361f7454560a77e,0x5456087f6a787dd15158,0x73589715829dfa366374,0xdda3dd3835c560eb3e0d,0xd60b9be95915cd625829,0x60563582e5fa56456350,0x956118158d60d97e5773,0xdaee8193dd16458327f,0xf745831df9360d81dd16,0x54d4254531a5fe959160,0xd561953509514c7d5576,0x14c7e556558d4254531e,0x54254531eb5619635095,0xe816454d514c7c757659,0xc7e556554d4258531bd5,0x258531bb569953509614,0x563509614c7cd57558d4,0xad78558d4258531f35dd,0x8531bb5e9563509614c7,0x58d614c7c7575595425,0x7a46416358531db56519,0x31bb5e819458d614c6ed,0xd9424c65f7a165d65509,0x5e0d4258551d5d257915,0xdb558f9050d61547a756,0x4354767565e414358551,0x937350d51e375d963e01,0x5e8563e0143586d9fa05,0x5878df7558f8050d61eb,0x8158d61bb56839158d43,0x959158f7050f6d7a3643,0xeb5fa56058058d43b57e],#[0x5c163d57e57835c57058,0x905d17158f17f95e1171,0xfba05d180dc563c5fe17,0xa7ee81846037158e9,0x5702340e405d01e0084,0x42ac14109004141bc0d5,0xd10e081c3cc1d10d205f,0xec55829114409cc4b023,0xfd17a0b945ac2cd1620a,0xc5462430f1830c0c6002,0x3271920c8463c31b18c0,0xd5c69c3451980cb4654,0x83b71d40e6470836f1b3,0x510d48583f91f50f8479,0x604a124011dc8d045322,0x8e14349fc4e326a12e49,0xad45612a314f4a6852b2,0x2dc16bcb585a32c715cc,0x4c0c5fd2fa17acbc45c1,0x531e18b4c48621309182,0x4ce466332d1944c9c64,0xbd3571a7cd2c6933421a,0xbccdc86db3661b24d8c6,0x74d3a21cece4c71137e1,0x1ee4f487953bd1daceac,0xc8073ff1fd4fd87e33ea,0xa21e50c884f42020ad02,0x948c145c22d515889744,0x8623dd1d08df46e234d1,0x29093f49b24b524891b4,0x4bc25bd2cc95d4ad255d,0x53989c34d42665314981],#[0xd50a282d4109ff4f8275,0x1d488a3b51928a5440a1,0x6b534297d4aca5352529,0xa55518a8954329f54f4a,0xac555e2ab5548aa154f2,0x2c35614b0157c2bbd5c0,0x4b4359d2c9562cb13588,0x12dfd6ecb6d5b22d6d6a,0x58ba95d02e45710b855c,0x32fad7acbc75df2ed57,0x8ccc5d6273115878c276,0x6543295938c936453205,0xd9d4ce166c3325980cb1,0x9690345da1cd0567e33c,0x95aacd4d6a234eda58d2,0xa16cc363db0cd7d6ba35,0x78dbb4dcb6e136cdb54d,0xe2570e384dbfcdf56f63,0x396dca4e4972038ddc5c,0x20b84179e5ce0e6d735,0xee1007bc00430f10ef01,0x303750302ea1503614c3,0x28fe0803610113606854,0xac1d217c01a0f204530f,0x1b07486f04683f00c811,0x486f04f00685c811ae18,0x15152060aac541204b07,0xdb454328fd06e83e81d,0xd8188f01e80da151ba14,0xc85623fa0c07b6046a17,0x6e0da05b03e015951c85,0x82614037a19e143a8f58],#[0x2c69254321a30ff82d84,0x411e50d6087847821408,0x60878212822e12e08060,0xd0444d435e10311350d,0x48060844cc35821e0845,0xf0108c34110e04018178,0x4000008504439e142006,0x850,0x2204088150d0220260c,0xa6136043d81076040d82,0x6054342206d8150d0c63,0xf60621944c3d8150d0b,0x810100863810a018ed81,0x822218a19611e0b6048d,0x80439434300005439435,0xe09821e08114310e042,0x83037825811443817845,0x14418e05235604248d60,0x4b8504308850c3901ae,0x2b814060863ae16800e1,0x4098118e3840ae04c34,0x1a481b00826100001026,0xc09206838440d0503414,0xe4101a80d4810ec1e,0x9c21e09034500d040101,0x120d040181d000427943,0x40d08d8208a3410083c,0x28181e84040dba042020,0x2080da8482a1206c0010,0x985040181e15080b08b8,0x260416009830bc1060c2,0xf50e094341d816000800],#[0x10301450f10e0d434150,0x41a0010e1040d6144384,0x490ed810c438110e0785,0x10ed8120010862854281,0x1410ed810c0504382814,0xe1040960e80043841048,0x50e04438110e07854110,0x301441010e0cc126042,0xe143a0050f08c1160641,0x441450e7810d051439,0x43980030085043ae158,0x505214149304090d0485,0x8817150b21410120c148,0x81085f0209c0a205c543,0xc081f0207c081f0207c0,0xd86052181000085f020b,0x817000bc081f0207a0c1,0xf705f0260e13c098382c,0x90350044f0207c08160,0x4100a141f0260e09c1dc,0x106e18128604028306a0,0x786040d0704000a141e8,0xa14100a78a4c200a4c1,0x248504003c081f020400,0x9206c004f0207037c08,0x8307c081f02a0e0b037c,0x3083f0208000003a0412,0xb4002f020545440dc08,0x7a041b8304a18100d07c,0x837c08278304000029e0,0xb0007c081785040f0205,0x4442a8817000dc1dc082],#[0x888378214069c5503620,0x424d03620c309340d70,0x34541d82d150b400128d,0x607454100f0050030011,0x542d0004000d040d8103,0x150400c0102d150760b4,0x1c18040d8100d040d81d,0x8000d062381b0006818,0xb6301d8c076301205d8c,0x1d8c04e570042205d8c0,0x301d8c076301d8c07630,0x4230e06804e002d8c076,0x1d8c07a301e8c0484083,0x4920101a80d6010e034,0xd04a38140f050341295,0x20be8482d040701819,0x38100e04]]
def g251H7 := limbs80 #[#[0x5e90018b446c008d092,0x40570a3d5cdcdcc52c57,0x4c00002c3003d276000d,0x2bf1c4400001ae16c003,0x58ef11159d3b077ea8c4,0x26b28b64bb0b002195ab,0x28d8234f0]]
set_option maxRecDepth 16000 in
def g251D8 := limbs80 #[#[0xb0a60887e450d414c110,0x21cd97658d30443da2c6,0x514154110fa8a9a62a82,0x443ce2cab0aa0887cc5,0x8b1a62b0221ee1624c56,0xac0887ac5914158110f6,0xce97358960443dc2c5c0,0x6258110e75b9ac4b0221,0x439d6eab12c08873a5d5,0xa2c8b0221cd97358d604,0x2887555d5534c510e5cb,0x57358d614439aaecb1a6,0x58d10e3abaacab0a21cd,0x3bf26c3aca8845fe5587,0xe2b0261ce962dc5604c2,0x86b658f8158130e6cb1e,0x450d604c3d9706b12c09,0x130b6ccb286b0261e996,0x6e8b1ac0987365d16358,0xb02616db9458d604c39b,0xa658d4358140e5cba2c8,0x9160502d732ca1ac0a07,0x1b75c82e6b12c16bb935,0x7c02a298f3558d61dc13,0xa63f4553589514c76aaa,0x5d95354531fa2a9cc4a8,0x514c7aaeeca9aa298f55,0xabc32a6a8a63b558654d,0x1aa298f955956354531d,0x3c7576595514c75ab0cb,0x55358531d6ab1f00b0a6,0x4c6dab2ca9ac298f9559],#[0xba2c6b0a63cd57458d61,0xc298f355d56358531e6b,0xd78558d614c79aeeab1a,0x558531b6bcaac6b0a63a,0x795ae8b22c498f1d5d56,0xb0eb22634ef965d5624c,0x98c7de4587595318bfca,0x6350d615072e90bc0aec,0x8541f1ab2aa8b0a83e95,0x5ac9b9ac4a0f1d5d5655,0x8b1283cad75591625079,0xf1d59561dc151e57baac,0xe0d615478eacbb9ac2a8,0x62e3ab2ee8b0aa3a7565,0x28c1ac8b16ab5938150d,0xa2c717f956077058ed5f,0x450d614c110a76cb505b,0xd30442fe728b0a60887f,0xfccb228698221f995450,0xa1a60887765d5434c110,0x21dd97650d30443bb6ea,0x19434c110eedbb286982,0x4437b70ca1a60886f66,0xdcb286982217d99650d3,0x260885f6e4d864c110be,0xef1644c5604437b726c3,0x6258110f74c1ac4b0221,0x43dd30ab12c0887bae0d,0x1a86b0221eeb85589604,0x887ae5914358110f6cb,0xb8358d60442df32ca1ac,0x58110e7dba2c6b0221ed],#[0x9f2c9b9ac08873e59173,0xc8b0221eb96455160443,0x87aee116458110b7dc9a,0x5591604439f2eab22c08,0x510afcc9ee8b0221cfb7,0xee8b1ac2887b558d4358,0xb0a21e7565551614439e,0x3d5977458510afac9ee8,0x8d434427eb27c22c2887,0xaefc9aeaa1a21cdd765,0x7ba2c68867ddd38154d1,0xa214fd96dd163442bbb2,0xe5983dd1108fecc6e8b1,0x764423fb27c22ea8847f,0xaaa9aa298a411fd93e11,0x3262907b558d614c520f,0x1e7565585514826ff2ac,0x14158130f6cb1a82b026,0x4c3dd2c4a8ac0987ae59,0xb12e2b0261ed96354560,0xc0987b658d7158130f74,0xf964dc5604c2df72cb8a,0x158130f74b1302b0261c,0x37b706c0ac0987b658d8,0x702b02617db93605604c,0x987b658f8158130f74b1,0x9158d604c3db322b1ac0,0x8130f6cba2c6b0261edb,0xb708b1ac0987b6611635,0x6b0261ed99458d604c3d,0x7ae5d16458130f6dca2c,0x585414c3d7708b22c098],#[0x30dcfc2a86a0a61ed563,0x20c3a829847fe5d86505,0x8a61ed563585514c27f7,0x76196354530f3ab2ac2a,0x1514c27f321c22a2986b,0x9efc9b0ea8a611fd97e1,0xb8ac2984f764f8754530,0x61ed79158d614c3daac6,0xd16358530e6eba2c6b0a,0x14c35bf0ab1ac298737d,0xecbf08b0a613f990e116,0xac2984f7e4d87585308f,0x3dd93e1d614c26ff2ac3,0x765c530d6fc32c6b8a61,0xc2f3f22b22869863fe19,0x82eca1a617db905d9434,0x6986f66138058d30eedc,0xb90611634c2ebf2ac0ac,0x591309eec9f02b22617d,0x7f720c3ac89847f65f81,0xbb2613f990e1d644c2,0x8776e0f805d930dedc1f,0x5605764c2bbf26c0aec9,0x140afdc8308bb26157f9,0x2c898ac0a07b658d3158,0xb0281eb96454560503d7,0xaee116358140f5cb2302,0xd60503d7328b1ac0a07,0xbdcc9f08b0281eb9646,0x6a8a62a0779dc9514c54,0xa81de77258531503eaaa,0x54f724c540f6ab1ac298],#[0x31503b9ac7b9262a0773,0xf7c2ee498a819ed85dc9,0x9262a067b61b724c540c,0x15ed96dc9315033df0db,0x961545409bfcab0c98a8,0x503ceacab0aa2a0779dc,0xc36e4a8a819ef83dc951,0xa2a067be1b7254540cf6,0x9f8350d51502bdb2db92,0x258540e76b1ee4b0a81b,0x39dacbb92c2a067be0f7,0xa86b0a819ef85dc96150,0xa057be4563dc940f4eb1,0x6254531582b7b27c22ec,0xc560faaa9aa298ac1ee5,0xcac4b8a62b07b558d514,0x498ac1ed5635c531583d,0x6bb615624c560f66a9ac,0x589315835df0ab1262b0,0x60d77c3ac498ac1aed87,0xab1a62b07b5e45634c5,0x8ac1adf8558d315835bb,0xfe59874c5609bfcab0e9,0xd415825fb2dc3a62b04b,0xb5fc9ac8a0ac1abd64e0,0xb12a2b06afe156450560,0xc1aed87589515835df06,0xf7354560d77c3ac4a8a,0x15827bf26c3aa2b0677e,0xecb70ea8ac12ff9661d5,0x2e2b073b5cd625c56097,0xaef83589715839dee6b1],#[0x625c560e76baac4b8ac1,0x835df0ab12e2b073bdd5,0x1ac6b8ac1cdf7358d715,0x2b073b5cd62dc560d6fc,0xd8558b715835db06b16e,0x58960f75c82e6b12c1ae,0xddb23b9ac4b05bbe4573,0x2a1ac13f990e0543582,0x6af5938150d60d6eb1f,0x7e05435825fb2dc0a86b,0xd60f6dc82c6a1ac11fd9,0x309c02c6b07b6dcf8058,0xb1ac16f994e01635835f,0xb76477358d60b3fcab02,0x173582df720c22c6b05,0xb5ec8ee8b22c1af964e,0x6a12a298daf64f745916,0xa63f5553589514c7eaaa,0x5915354531f72b22c4a8,0x614c7daac6a12c298fd5,0x6ac92c6b0a63ed59058d,0xb28498fb56516358531f,0x3ecd6454d624c6aff2ab,0x56458931e76baac8b126,0x4c6fab21c0ac698f3bdd,0xc86eaaa26397f75e0154,0xec98cfd643815d931abe,0xf56358770506beb21c0a,0x4dc141e7ab2ac3b8283c,0x63ff26c36e0a0d6fe4d6,0xf00b0a83af563e016150,0xa8c7fe4186dcd41cfbb9],#[0x6550961547ceaca992c2,0x8551f6ab1a86b0aa3e75,0xeacaa1ac2a8f75dcd435,0x6b12a35df935d932547c,0xfab5914358951ee7b9a8,0x58d435479dac9b9ac4a8,0x51aeec86e6a1aa3cdd76,0x2db9a86a8f675937350d,0x1aa35df935d943546bbb,0x758d43dc1618fec870eb,0x1435863ff26c26e0b0f3,0xf6bc8ac6a1ac3add63e0,0xc02c6b0f37dd56350d61,0xc36f590e0563586dbf26,0x43815cd61b7aca702b1a,0x458addf26c0ac8b14fd6,0x7c8b06b22c56ef956056,0x6e2a1e7758d80dc543b7,0x75f956056350f37ac8c0,0x815d9439dec8702b2287,0x8eaff2ab8ae0b1c7f643,0x2ae8b8ac797f855c9715,0x6b24ef64f845c164cbfc,0x184585304423ff20c0ee,0x4c110fecc2a8698221ff,0xfb308b1a60887f661943,0xc8982217fb9855130443,0x85fe661644c110fdcc22,0x561130442ff730b22608,0x110efdbab0898221df97,0x2ecc2260886fe615844c,0x98221dfb7661130443bf],#[0xfee51854c110dfcc3308,0x1930443fb726c3260885,0xdfcca30c982217fb946,0x898ac0886fee51864c11,0x221ff3844c560443fe30,0xe116358110f7cc22c6b0,0x60443bf308b9ac0887be,0xfcc26e6b0221dfb845cd,0x1ac08877ee137358110e,0x1bf98460d60443df2c8c,0x56458110dfdc2306b022,0x443bf2eac22c0887be61,0xc2b08b0221dfb7561160,0xc0885fe64f8458110dfc,0xfb75e1160443bf2ebc22,0x3dd110dfcc2f08b0221d,0x33fb2cc1ee88867f6558,0xaa298a41fd5635453148,0x906fd619514c520fbab2,0x5358531482feb2ca8a62,0xc520f7ab2ac298a41fd5,0xef0ab0a62906fd615614,0x698a417f795585314837,0x7f5e45634c520deec32a,0x58d31483dbacab1a6290,0x20defc2ac698a41bdd85,0xcb2a62905f7e55634c5,0x8a413fd98595314835fb,0xde45864c5209fecb70a9,0x931482eff2ac3262905f,0xdbe4ab0c98a41bf79161,0xc3262906dfe55864c520],#[0x41ef563585514827ff2a,0x4d6154520dfbc1ac2a8a,0x14835fb0cb1aa2905fde,0xecb706a8a413ff9858d5,0xac2904ffe4d86545209f,0xaff8558d61483def22b1,0x8358520b7fcaac6b0a41,0x82eff2ac1ac2905fde45,0xaf06b0a41afd65e0d614,0x6904ff64f85585209fec,0xd95e0563482eff2ac0ac,0x58130bfdcba82b02613f,0xfb706a8ac0987f650d51,0xa2b0261ef964545604c3,0x877edd15158130efcba2,0x35c5604c3fb286b8ac09,0x130f7cb22e2b0261fdb8,0x309b8ac09877e5d17158,0xb0261dfb84dc5604c3bf,0xfe6118158130f7cb2302,0x85414c37f708c0ac0986,0xfcebaa86a0a61bf7875,0xeb2282986f7e1d635053,0xa619ff875d5414c377f0,0xe1d76505309ffcbb0aa0,0x414c33f930bb2829867f,0xffcbb0ca0a619fe985d9,0xaa2984ff65b87505309,0x1df574585514c3faa86b,0x14354530efbba2c2a8a6,0x4c3bbaeca1aa2987e759,0xc3286a8a61ddf7650d51],#[0xa2986f7e194354530dee,0xdf9650d514c2fbb2ca1a,0x354530deec3a86a8a617,0x3bbae8b1aa2986f7e1d4,0x2c8a8a61ddf7458d514c,0x9857f65d6454530edeba,0x875d1514c33fb0eba2a2,0x4530cfec32e8a8a619ff,0xff2cba2a29867fe19745,0x8a8a619fd86dd1514c2b,0x57f65b7454530cffc36e,0x5d9514c27fb2fc22a298,0x30eefc9aeca8a617df93,0x29bb2a29857fe5176545,0xa61fd5435c5614c2bfb,0x75954358530efaba2e2b,0xd614c37bf0aa1ac2987b,0xdefc3a86b0a61bdd8750,0xb1ac2987b75d16358530,0x619fd875d1614c3dbb28,0x957458530cffc3ae8b0a,0x14c33ff0aba2c29873f5,0xfc2ee8b0a61cfd65dd16,0xae2984ff65f8458530cf,0xddd7550d714c3f3ac8a1,0x435c530defc2a86b8a61,0xc37bf0ca1ae2987775d9,0xa2c6b8a617dd9650d714,0x29876f5d1645c530eeeb,0xf97591714c2bfb2eb22e,0x5c530cffc2ae8b8a615f,0x3faebc22e29867fe1974],#[0xecb8a61ddf935d9714c3,0x87f6e417650d30affca2,0x15d9434c2fbf22bb2869,0xd30eefc8aeca1a61ddd9,0xae8c0ac6987f65d38058,0xb1a61ddf74605634c3bb,0x775d38158d30deec2302,0x5634c3bbee9c0ac6987,0x9fecbf02b2261bdd84e,0x2bb2e89877ee41765d13,0x261fdb83e01764c2bff2,0xe13805d930dfcc2700bb,0x764c37bf06c0aec986fe,0xbfcab02bb2617df93605,0x22ec986f7e0f815d930b,0x1df984e01764c2ff720c,0xd815d930efdc2700bb26,0x4c33fb08c0aec98777e0,0xc1f02bb2619ff8460576,0xec9867f613815d930eef,0xf1514c5605033ff09c0a,0x158140ff8c0a62b0281f,0x3f770898ac0a07f654d3,0xa62b02817f9954c56050,0xa05fe6613158140bfdca,0x4354560502ff73098ac0,0x8140f7cb1aa2b0281fb9,0x7708a8ac0a05fee4d515,0x2b02817f99854560503f,0x7be58d8158140bfdcc2a,0x605605037f306c0ac0a0,0x40dfcc2b02b02817fb93],#[0x22b1ac0a05fee5581581,0x281efb9158d60503df3,0x558d514c540bfdc8b06b,0x531503f6ac8a8a62a07f,0xefabb2a298a81f756554,0xa8a62a06fd619514c540,0x817f596545315037ef0c,0x4d614c540bfbcb2a298a,0x1503deacab0a62a07f55,0xbc2ac298a81bf5855853,0x262a05fde55614c540df,0xded85dc931503bdacbb9,0x534c540ef6c36e498a81,0x3bbaeca9a62a07e7591,0x32a698a81bdd8654d315,0x2a07f5e45634c540defc,0xd6558d31503f3b28b1a6,0x4c540deec2ac698a81ed,0xfbf2ab1a62a06f7e1563,0xc898a81ddd9758d31502,0x6efe15644c540ddec2a,0x8595315035fb0cb2a62a,0x540cfebb30a98a813fd9,0xaedc2a62a04ffe59854c,0x98a813fd96e15315033f,0xfde45864c540edfca2ec,0x1931502eff2ac3262a05,0xdbe4ab0c98a81bf7916,0xac3262a06dfe55864c54,0xa813fd95e19315027ff2,0x58d6154540fdaa1ac2a8,0x515037ef06b0aa2a07bd],#[0xf6b1ee4a8a817f793585,0x92a2a077b60f7254540e,0x1f9d6350d51503bdb0db,0x94354540edebb286a8a8,0x50377f0ca1aa2a06ef61,0xcb286a8a817bd9650d51,0xa2a06bf6196354540bdf,0xbd64e0d515027ff30b1a,0x354540cfebb706a8a81b,0x2f7f26b22a2a04ff65b8,0x2eca8a815ff935d95150,0xa04ffe4d8654540edfca,0x83dc9615027fb27c32a2,0x8540ef6c2ee4b0a81ded,0x7f0aa1ac2a07af595435,0x6b0a81ef79158d615037,0x6bfe156358540f5eca2c,0x58d61502dff2ab1ac2a0,0x40bfbc8b06b0a81cfd97,0xcbc1ac2a05dfe5583585,0xa813fd95e0d615035fa,0xb64563dc9409fec9f0ab,0xd43503bdf22b1ee4a077,0xfcfc8ac6a1a81f9d9158,0xc0ac6a06ef6118158d40,0x819fd8760563502eff2a,0x1f8158d40ddec2702b1a,0x350377b29c0ac6a067f6,0xecbf02b1a813fd95e056,0xa62b07bd591514c560cf,0xef5645c531583beee8a8,0x714c560efaba2e298ac1],#[0x83dbac8a9a62b077ddd1,0xa2c698ac1ddf7454d315,0x2b07b7dd1634c560f6eb,0xf7459131583dbb28b1a6,0x4c560d7ec2ac898ac1eb,0x5fb0eb2262b06bfe1564,0xe898ac1aff8759131583,0x67fe1d744c560cfec3a,0x7dd1315833fb0fba262b,0x560efac8ee898ac19ff8,0xf0bba262b067f617744c,0x98ac19fd98dd1315833f,0xbb5cd6254560cff4c6e8,0xd51583ddee6b12a2b07,0xdefc1a86a8ac1edd635,0xca1aa2b07af591435456,0xac15fe9750d51582dfb2,0xe0f7354560f6fb9ac6a8,0x51582bfb29b9aa2b06f7,0xffba706a8ac1afd64e0d,0x22a2b05bfe4d6454560c,0x1afd8759151583d7ee8b,0xd7454560d7fc3ac8a8ac,0x5833ff0eba2a2b067f61,0xc3ee8a8ac19fd87dd151,0xa2b057f64f7454560cff,0xfe98dd1515833fb31ba2,0x25c560f76b9ac4b8ac19,0x39fae8b1ae2b07bb5d56,0xae6b8ac1cff7458d7158,0xb073f591735c560defc1,0x74e0d715835fac9c1ae2],#[0xc560cffba706b8ac19fd,0xff0ab22e2b073f5d5645,0x8b8ac19ff855d1715835,0x67fe17745c560afec9ee,0x5cd62583ddb22b9ac4b0,0x60f6ec8ac6a1ac1eef91,0xe9c02c6b07b7e456350d,0x1ac1efb74e0163583df2,0xf6118158d60f6fb9b02b,0x563583dbee7c0ac6b06b,0xf7cb2700b9ac1afd84e0,0xc02e6b077e5d3805cd60,0xc177f9560573583bf6e9,0x93815cd60b7fcb302b9a,0x35833fae9c0ae6b06bf5,0xdc8307ba2c19ff74e057,0xee8b067f60d81dd160df,0x9fd8560774582bff26c0,0x83dd160affcab03ba2c1,0x833fb22c1ee8b057fe45,0x1a84a8a639ff9160f745,0x298fdd5954254531feab,0x586509514c7beaeca12a,0x58531bfbc82c8a8a63bf,0xdeacaa12c298ff554d42,0x84b0a63df575509614c7,0x8efde154258531efbbaa,0x158d424c7bbaeca9a849,0x931f6eb2ac6a1263fd79,0xeeab1a8498f775d56350,0xa12637df9558d424c7bb,0x7f65d6550931e7ebb2ca],#[0xd9424c6bfb2dbaa8498d,0x1bbfcaaeca12637f7915,0xabb28498f7de45765093,0x263d7f955d9424c7af92,0xe416454d31affcaaeca1,0x634c77bb08c02c698df7,0xefc8308b1a637df94601,0x2c898defe518059131b,0x39ff75e01644c73faebc,0xd4258551f7ab1a84b0aa,0x546fef20a1ac2a8efde0,0xcbac6a12a3cfd7658d42,0xc4a8d7fe4d7650951aff,0xdf7360143547ddb26b22,0x50d51deeb1f00a1aa3d,0x73faedc0286a8eef5938,0x700a1aa39ff76e014354,0xa8f7761b7350d519fecb,0x9061943546f7f20b2286,0xcd519fec870ca1aa33ff,0x7f28c02c8a8d7fe4164d,0x6b22a33fd93e0164546f,0xfbde4563509619fec870,0x58d425879feeab1a84b0,0x61bfbc8ae6a12c36ff95,0xcbb9a84b0ddfe5573509,0x12c35fd95dcd425879fa,0xf5978050d61afec9eeaa,0xd435873feebc0286b0eb,0xf6fc9b00b1ac3edd9058,0xc02c6b0ebf6118058d61,0x856ff9061163586dff28],#[0x578158d42bbfcab02b1a,0x50fbbb22b1ee0a1cff6,0xec0b00b1a87ddf9158f7,0xac6a1ef7e058058d43de,0xddf835c57058efbb21c0,0x715c163cffc22e2b82c7,0x8f3ff09b8ae0b1f77e0f,0x82e8b8ac77fb905d1705,0x2b1ef7e4d80dc563affc,0xf905d37158f3fae8c06e,0xdc563cfec2301b8ac75f,0x3fb28c06e2b1d7fe5180,0x9b8ac79ff946037158f,0xcd007a00320000affc83,0xf301ab0179013c010a00,0xf802c602890257022501,0x6b041803c50388033502,0xd305a10559050604b304,0x5106fe06b60679062605,0xda08a8084a080207a407,0x9ce0991095f091708,0x260ae90ab70a6f0a3d0a,0x570c1a0bd20b950b580b,0xf60db90d5b0d1e0cc00c,0x3d0f000ec30e700e330d,0xa5106810150fc20f640f,0xb511831151110910e210,0xe6129e1282124511fd11,0x3813fb13a8136b131812,0x951542150514c8147514,0xfd16c0166d162515dd15,0x65182817e01782174516],#[0xd81985193218c9189718,0x2a1af81a9a1a471a1519,0xf51c971c2e1bdb1b7d1b,0x3c1de91dac1d6f1d271c,0x361f041ed21eab1e791e,0xb4204b20191fc61f5d1f,0xf0217c213f212320e620,0x79230522b22275224321,0x2e24f1247d242a23cc23,0xe3267a264825df258c25,0xf028b3283427b5274c26,0x582a0529d329a1294328,0x472b202aee2aa62a8a2a,0x832c3b2bdd2bab2b6e2b,0x222db92d5b2d342ccb2c,0x532f2c2f052eb22e5f2e,0xb0307330362ff92fa62f,0x4f31fc31a9314b310e30,0xb7336f331132c9328c32,0x77352f34e7347e340a33,0x3676362335fc35bf35,0xf73883383037dd375e37,0xac3a5939f039a8393f38,0x8d3c453bd13b893b0a3a,0x2c3dce3d863d333cf63c,0x5d3f2b3f043eb13e743e,0xba4088401f3fe23fb03f,0xd541984150411340e140,0x69430b42c3425a421d41,0x8f4452442b43ee43a643,0x9f4562451a44d244b644,0xba46934656461945e745],#[0xd547984766471e46ec46,0xfb48b348764844481247,0x584a1b49bd4980492d48,0x9f4b624b1a4ad24a954a,0x494d174cb94c504bfd4b,0xfe4ec14e844e314dd34d,0x5b50134faa4f8e4f3b4e,0x55512e50fc50ca509850,0x91523e520151ae517c51,0xb75390534852f552c352,0xd254a05479542653e953,0x2455e755c05583553b54,0xad574456fc569e565656,0xa58c258905853581657,0x4659fe59cc5984594759,0xc45b665b1e5ad65a785a,0xc65d5d5d205c965c435b,0xf75ed05e9e5e615e0e5d,0x285fd55f8d5f665f295e,0x64613d610b60c3608660,0x5e622c620561b2618b61,0x2c631062d362b7628562,0x1b63f463b7637a635e63,0x62651a64d26495644d64,0x51663565e265b0658965,0x90668a66796668665766,0xfb66ea66d966bd66a166,0x45673467236712670c66,0xd167b567a4677d675667,0x5d684c6830680967ed67,0xd368b76890687f686e68,0x546938691c690b68ef68],#[0xd569b969926976697069,0xb96a876a606a2e69fc69,0xb36b766b4f6b126aeb6a,0xad6c706c336c176bf06b,0x706d496d226cf06cd46c,0x336e176dfb6dd46db86d,0x16eda6ea86e766e4f6e,0xda6fb36f8c6f656f336f,0xc970977065701d70016f,0xd971a7715f712270f070,0xde72b77285723d720b71,0xc2738573537321730572,0xd274ab7479743173ff73,0x1975dc75aa7557750f74,0x4a772376e676b4766176,0x2e77fc77e077a3776677,0x49791778da789d787678,0x857a537a0b79ad796579,0x5e7b377afa7ad37aac7a,0x4d7c267bf47bcd7b907b,0x317cf47cc27c907c747c,0xff7dd87da67d7f7d427d,0xcd7ea67e697e427e1b7d,0xbc7f957f6e7f527eff7e,0x5e804d8031800a7fee7f,0x2180e480c880a1807a80,0xc381a781808164814881,0x86826a824e821c81f581,0x28830c82fb82df82b882,0xbf83a38387836b834483,0x828445841e83e183d083,0x3a851e84ec84ba849e84],#[0xd185aa858e857d856185,0xc086838667862a860385,0x9987678735870386dc86,0x7d8861883a87f287c087,0x61892488f288cb88a488,0x248a0889ec89ba898889,0x608b188ad08a938a568a,0x5a8c338c018bcf8b928b,0x288d018cda8ca88c8c8c,0xc8dda8db38d8c8d5a8d,0x68ed48ead8e7b8e3e8e,0xd48fad8f868f498f228f,0xad9086905490228ffb8f,0xc8918b9164913290f590,0xa1927a9248922191fa91,0xa69369932c92fa92c892,0xb69484945d942093d893,0x849552951594ee94d294,0x479615960495dd95b695,0xa96e396c796a0967996,0xe397bc97959763973c97,0xb19895984d9831981597,0x8a9958991b98f498d898,0x429a1b9a0a99e399bc99,0x529b159ac29a859a699a,0x419c049bc79b959b6e9b,0x3b9cfe9cc19ca59c739c,0x99de29db09d949d629d,0xcc9eb09e7e9e579e3b9e,0x849f689f419f049ee89e,0x47a0209ff99fbc9fa09f,0x2ba104a0dda0a0a079a0],#[0xb7a19ba17fa16ea152a1,0x2da211a200a1efa1d3a1,0xaea29da281a265a249a2,0x45a31ea302a2e6a2caa2,0xe7a3cba3a4a388a36ca3,0x94a478a446a42aa40ea3,0x62a551a514a4eda4c6a4,0x4a5e8a5c1a5a5a57ea5,0xd2a6b6a68fa65da62ba6,0x8aa763a731a715a6eea6,0x79a852a82ba7f9a7c7a7,0x5a8e9a8cda8b1a895a8,0xc8a996a959a932a916a9,0xa1aa6faa53aa21aa05a9,0x85ab53ab21aae4aabdaa,0x5eac42ac10abdeaba1ab,0x37ad05acdeaca1ac7aac,0xefadd3ada1ad85ad5ead,0xb03118090150620d04ad,0x81b0311fc2608f048481,0xa41a8be1380e08f0504,0x20a4180341080e08f04,0x1c08407047820520c052,0x23c1036070302eb06854,0x9823c103406c2034f098,0x1c1507025010708541b0,0x3c2b830888420a8a019c,0x182a0dc500ce160a8361,0x608f040d81c0e085c2f0,0xc16080680d8505801bc2,0x2001f82e0043d150e0b7,0x7c23c1036e008a47803c],#[0xe11e081b700452303400,0x1e11e0b8010f44c382c,0x70101fc2341e861c164,0x3c1685e01a18130de0b8,0x6070381ee068541c09c2,0x311c1601ef09823c103,0xa8a04f00608f05e101a,0x6090341bc2f814240ba,0x5e0b040341fc2e08f05e,0xf028541a0fe16c278182,0x82c100d0805a0a803785,0xa834181682a041e17c0f,0x381834201bf8506de050,0xd0405a0abc2f81f0582,0x360e0a83417c2f8182a,0x706de17c0b8308c3785f,0x220a0b81ba1506c203,0x2106c00481016688f05a,0x890aac1201b2a120540,0x3c17800903201b2f0a82,0xe13c022a082220d00be1,0x411106f84f05e00240b,0xc2782f001205f09e0115,0x1906f84f05e00240a0a3,0x441506805f09e0bc0048,0x998fc1a4834b11e0ac00,0x8f09e0bc00a123887a0,0x2f84f05e010f413c1a09,0x68438b00de081a22916c,0xb410601717e0bc28300,0xa291506f84f05e00240a,0xc00374522f84f05e001b],#[0x20f413c1a0907f09e0b,0xbe13c17800902f84f05e,0x9060b781f0121c254541,0xf8080fd09a188055a549,0xa1781e861f45f82f01c0,0x1ba19c28fe13c178001b,0x20680c45f09e0bc07030,0xf82f000a4180a0be85f8,0x64590a8c43c1a2260e85,0x70b0541b080b487220b0,0x240c08380c1506e2006,0x10a130c0b080e88f05a0,0xe6130a06bc010f442,0x4c215181a0480bc2782f,0x390a836101688e441604,0x3f44703b03c18705a2,0x24e47fc289706c2f82d0,0x8731ce1fc1212b0c0c47,0xd0570804b045860622d,0x20881b0e049c1030062,0x582a0d8506e0c009015e,0x3850630541b8b0480c38,0xc3f82e03049c30311e09,0xa009587b088401a0c062,0xc0dc09034b09c041b0c0,0xb0e0dc09034b09c041b0,0x506e61ec2000e020881,0xc041b0c0df808361300d,0x25c041b0a0dcc3812069,0x70ee12c1838201b8340,0x70182a0d8605c63ac3a0,0x2241505c0d8505ce1422],#[0x8823010710542209e14,0x82e020d01b12c041c415,0xb0341c1b835060e1ec27,0x1b0e0dc1ae08e05c041,0xd8506e61ec2702e020d,0x100d02389c0b80844068,0x40e1dc25830703b02c,0x38770960c22410228120,0x81034070110404043a81,0x48c3f02089c04500361f,0xde170470205dc0411100,0x4161ec238506c383510,0x8770b611080372581400,0xe8682a4021040439815,0x18880e88702021ee0f8,0xe1181210062378206c0d,0x9c0b80029060282f90c,0x188e43881700d0c0c45b,0xc4504243d43584a05040,0x80d0188823843f00d0c0,0xa82a12c2e1506c1818d0,0xc1d00ee0011c4d0ba0d8,0x50040b2c213c00160470,0x3a1c1d701e0003c0380,0x8a8803c03805004e1b42,0xb4300eb084e85e020b2,0x61044e03c000780700a0,0x50720785f091440f09e1,0x640f09e162f09e161086,0x6081ae0806c0d0a10ca1,0x20d0706e0c009585b09,0x5090203706b82381703b],#[0xd814000d8240b6041b21,0x437850890490a8361dc3,0xb040860880481b15040,0x1606090e0d008785f09e,0x710488f0411011410c1,0x361c1001e21d409c3b84,0xb140bac2d81a061110a8,0x85f0840fc16080880d01,0xba12c100d81a0a042c0f,0x11410b0382181e86201,0xc0ec084442a0b8742411,0x1822c08440684886b0b,0x806c110404c21bc2f82c,0xb82421821c083725c2e0,0x9215068483410ce1081,0xd0906e0d9c1018f0be04,0x1b385704e045050342a0,0x3c1118c10e1017160dc,0xc0d0b06e0d8433857028,0x8304785f05e050003706,0x4e081ba1506c28187082,0x6de17c08154240d0704,0x86e07c0b0402e0444037,0x268206c0d018880dc1b0,0x4d618110e0a20a831068,0x142a0d0401e01c028020,0x9b8404818130480847e8,0x5c03428361040f04e050,0x9515068180322a0d0302,0x90208e10fa1489036141,0x206c4481890238438000,0x2f0623034027c23c278],#[0x40b15058303410ce0b80,0x9c26812244a2480607b,0xc434480800f20d90de,0x6bc0b81e86044403605,0xb5d0c08ac21223d84681,0x30311421e8100e014010,0x414686a24388e10e0034,0x21f431121fc2782e11a0,0x241101b06c0f408b511c,0xc0311403844d020d838,0xbf420341c09182e01c1e,0xda101a0a0a0136870240,0x8240dc1a036141b81206,0x88c25c238002806c2b87,0x902804cc220c584601a1,0x24087b0200343031150,0x1141361701e01743615b,0x1e23584782d08c03430e,0x8d0823c46b00d0dc0c71,0xd8506f4201b0120682b0,0xb6041b0c04a840370680,0xf044a01b1048909044f0,0x82068361270b60784784,0x5581c2a392824c84ac27,0x6c1a15289802f3060b81,0x850d05c0810358521d60,0x10358321d616c0a15269,0x60ec083408c350d05c08,0xbac1e080583200b0b,0xf0be06c183442a37024,0x543b0b606c1a15068282,0xf20780683b0a3a1205d0],#[0x10aa0e40f15324d49360,0x806b8b81321fc1b8140d,0x60fc1240f00d07618803,0x8681aa0e40f152e4f493,0x8e0c01781ee0bc08098,0x87538a4e83a83e00e174,0x5293a0fc1141f00d02e1,0xd43385d07a0782700a0e,0xc0283b85526329c534a4,0xca1782507e004f86e09,0x6e00a4c653ca4f41e817,0x70070da04950b41f8238,0x8a8e41c15825d0ba0f82,0x18805203f81681d0761b,0x4f49a60fc1240f00d0b6,0x80d08681aa1640f152e,0xfc114d0c0840f20fe07c,0xe09c028394a19c1f00a0,0xca854f29ad0aa0f40b86,0x92a0e83f04e00e194d0,0x2b04ba0f42f04e00e1b4,0x3d17e044614d51514838,0x94f50750dc1380383d02,0x12142b83a0fc138029e1,0x42a7a83a86e09c01c2e8,0x570b41f82783e00a7865,0x2c30e20f81681059454,0xd0543b07e1703f04703c,0x40e0aa42b15090241701,0x4103c1215708f05c002,0xa0d8a83817c170005412,0x3c0d3c103806c482e03d],#[0x8a2a0d44107c03847840,0x541c080aa8a8480d4083,0xa11341d150702e8305b4,0x5600b415785a2aa4c650,0x41b0c20fc17000540dc5,0xb41c0a0b911782e00e1,0x3c1b41f0027c1036e00,0x703029f0823f84782d,0x8b0e00408e10fe0b41f0,0x1a0be0b4088e10ec1b41,0x101b0341b83f820880d8,0xe0e0110371410782d021,0xa836154d51506c1f82e0,0x8155150901a83073a168,0x4f05c2342836194d0360,0x87f05a17800361b8078,0xc308e10fe0b800481447,0x6c202e50611340d1506,0x2a7061128a8a11017515,0x182e502e168a84417c28,0x2e168a837101c515088,0x220361bc16810880d04d,0x101b5151111782d03c00,0xaa142202ea2a0d8505c1,0xb2151010e8170b4541b8,0x6c1b81c2a0e0405c0dc1,0x642a301eb06e070a8381,0x34070208fd060f6c0f0,0x10707e002601c0fe081b,0x1fc16830680e0505de09,0x785c078050556070a902,0x611e081b836068283dd0],#[0x1b0b422c10370680d85,0xdc1b03419c3d8206e0d,0x42a3800361810508304,0xef040e01b034160f708f,0x2030440184683068401,0xc3c827080bc1a0e2a053,0xe384484e000d8905a0a9,0x508017110800f7827020,0x82202fe10e0fc102d05,0x86c0360ac418806c6588,0x3404c47c0d40b62d81d,0x86c1b80781e8532a401c,0xb82700e2c240f86b099,0x981e01b196205454e120,0x415c23827100d8220a81,0x8360883a0dc02e2dc404,0x4668809c2601704e01c5,0x7289a86a0761780a9527,0xce178182a92a3529a494,0x94043816b1392a282021,0xe4a82d11c02128260dc4,0x90f80f0352a0b44e03c0,0xd04e07a1814874074302,0x1e0a0b0311fc14160620,0xb0c08a0b0a08507986d0,0x5005c06c30221f44782,0x270403c0d0188803c038,0x9618130f45f43031a2a,0x1b11628601e01c02802e,0x206b10108340d62d82e0,0xd6110d0b613c10260902,0xf0509ac20481fc1026d0],#[0x44d16a2b4406806c058b,0xc06c189524c1e8663525,0x2a371aa1a4605070521d,0x2090282050c43ac1d1a5,0xf0552a0d8304da100c78,0xc4e44130a2dc151a06c2,0xf05a00131391b4278204,0x2d07a1b8280d2342687,0x958443c0d0601c01c020,0x807701e0d610906a0a00,0x6004c13a000780700a00,0x41742403d03583782e03,0x80622906f040bf420311,0x8370680d84f040db4202,0x17380058608178311b80,0x522820304e101a03114,0x8111d854611c20b41f06,0xb85c2a0dc48400b4c2d,0x21002df0b60c476151ac,0x170c454803c0f68a8381,0x36188bc0de0607a07e8,0x432171b0c70bf040a382,0x358ad81210a88f11a04f,0xd604bd0dc0c0780562e0,0xa309687d09c0f41680e0,0x7a06c5d82b103c2f0524,0xb01613836813014f06e0,0xe0a514520a3161f81d82,0x93c184780e11b054585,0xf00e0140100de09c1ac,0xf21421a821c23821b418,0x904184704c040c8311c8],#[0xe10131846020d0090a08,0x2221bc043410e11c103,0x4437808a8980c0150242,0xc0c08886f010c2318730,0x5c28f05204584b05c040,0x610825305204584b0540,0x61308f810822c1501602,0x2e023414811612c10181,0x30107c212a829022c258,0x20483e02e101107022c1,0x37011f80b840441836e0,0x41a061181f208708e091,0x50c8990d7048544709c0,0x34410e08230844c86a1,0x64360338242a2b8405c1,0x3382602854480c854222,0x54612808341487215089,0x3068e0a80a1508c2a000,0xa980d840682215a020b8,0xa46886a06b05c060a8c0,0xc151894b85b054060a8,0x780c15189488fb054058,0xc05034150c1701202043,0xc1511ec04470a43a0a87,0x1300f610e0980b851c94,0x21411260800e81604100,0x48421904858241004182,0x4010608850741836190,0x8c80c4283a041b0c0886,0x424c170c024038602403,0xc2783842784985c27838,0x241e0fc24210bc278387],#[0x1201c310608850504838,0x21707e12100900e16810,0x4242e13a042b06088661,0xc04807080e0fc24213c,0x40387c278384e0c04807,0x5120a886044098470a02,0x5814000d830456041321,0xd6048688088c25810542,0x3215150ad8121a1a1540,0x489c86024181304404a4,0x607c28a0820089c24121,0x38208a8543410e088748,0xc800c2503068290e42a1,0x7060d281b8242a118503,0x2c0c4404c888242b40c1,0x1106088135860d843821,0x22c148101f614644d054,0x26445618304c088204d4,0x60441036068103606812,0x13485101302270c182,0x850d83b0241d2144834c,0x2115d038681b0806806c,0x28681b0641340a1a06c,0x8021a06c1d004720983d,0x20da041b05a04800360e,0x84208a1d415000642384,0x21b40a0d20c202622423,0x906d02834490da050687,0x83107205a040d00d148a,0xb08250850f6094100eb0,0x7a040e40689422c100e,0x45c068d41e8101a05425],#[0x1a210070841d43681035,0xd00d0c1501a01c18390,0x6da0489080c81105a04,0x4070a44b4084806c2048,0xa040d00d140d00d509a0,0xc488098120202107205,0x180827806b0890ce0887,0x14145000621a81a000c4,0x8e108304450b40047084,0x3681224382650ea0a800,0x340836104f118610e081,0x42142d8201d6105040c0,0x8f42143d8250403ac20d,0x421f03683905a0500540,0x1600a811683d0205203c,0x22081480f01c190f81a4,0x28a022b04c4768114218,0xa02610a1642184502,0x4101a11184908a044a,0x4f408100c0988e109a05,0xd15844867048381f0b0,0x100dd0220a022a038c32,0x4a04078c037408461cc,0x2902800071007684185b,0x4815023020a1021101d8,0x9486d02201d01ac21c1,0xd08048302d218c3060d8,0x511684170038104c1834,0xe134238106c184470ae0,0x90eb0a8185210e11c103,0x1104827614218645209,0x8700ec0a060c1b58560],#[0x409846000bc2806436c,0x50688234103e10228871,0x14090205b04486d04618,0x34708183d824421c1046,0x848307484ac284412090,0x36b021e1206c158106c,0x41181f0b6101a2120d09,0x209049c20340c8438470,0x5c1184b023a12b0b6042,0x60c0b585080700d61161,0x4402cc21c10684ac083,0x150f0a985080700d3096,0x5090a826070a84040c1e,0x3b0a8643c876150c86e1,0x83b02854521d854230a4,0x85423076049306860871,0x18321d8543b02854221d,0x6040c1f04068210ec2a1,0x818321d85440686070a8,0x385108761508c0e15080,0xa12147020b030582790a,0xc08262b2142e04090dc2,0x70210a130262b2143127,0x81e040883e041085e041,0xe0c1241381ac17810bc0,0xd8660bc09070a21b8120,0x851150a930b41f020907,0xf29370ae184538a6949b,0x4c0a40b150e40b15094,0xc41f020b810221781,0x1a24827c09148806340b,0xcc178120e144370241c],#[0x8120dd022f02d02120fb,0x1d454341b454207cc1d,0x8068909282885e04220f,0xc081931501a201401dc0,0x31505203c4e0403b8a86,0x7b86a0bc080a00e1981,0x687c0849844808b9150c,0x1a189ee0424c3e0504c0,0x510bc082180d13810430,0x5007060500770260a03c,0x21206f0290ac004e040,0xc082e04838283503581f,0xb831543283d02a68410b,0x4d68170c2a9c534a4f40,0x3943702d02a686542a79,0xb20c81b02d0283468290,0xd5001441f0241b400422,0x7681200201401dc094,0x3e041c1401da04800905,0x542e05a040a00e128188,0xe0d8101a62a098401cc,0x34482803b4087c080a0,0x4045f409151141e81034,0x8101401c1f0201dc5432,0x534e14453ca4dc2b8313,0x26449c0940d001550a9e,0xc08160605007702a0024,0x5830a13020d02c004a07,0x4837408b09b816810f81,0x68627b8110e0c2330760,0x1c1a2460bc083e050780,0x4707c080a00e13810140],#[0x18c1b810ccf19370ae04,0xa85049a0e70bc09c08c6,0x2b00110a20e107c09c08,0x22f0285fc54322803ac,0x401cc00460f6158100db,0x6860ed83b020c0b11,0x20dc2f020280384008c,0x2144054c02428605183b,0x4407980483100d31501b,0x418a24c06b8262b20c54,0xd640b00100b315126036,0xa43d0690590280460700,0x5060a890093610e08562,0x80c300d020d84126e101,0x168380e8002a0b0002a0,0x1022285a00238420b400,0x8201d454405540047084,0x4554287608075150d42d,0x5155060040709454107f,0xa0a407860c806d1501c2,0x1d1501a1515026a143a2,0x7a054d0361340a9a06c,0x8c036a2a2118d020d835,0x2000d83907a041b06868,0x41b0520f4081a01a2681,0x2d02068068ca681b05a0,0x681306c001b0441e4190,0x81c000a83d020d8262a0,0x2104072a0e8008e1082e,0x760807515101550011c,0x19d155061d8201d45435,0xaa830f4081a01a1d1504],#[0x7a041b0b454068406a8,0x105d079c2e811c1741e5,0x308906e08230a0b41512,0x844b408360e4182e081a,0x24004202a843092041a0,0x1c128162a038503c2384,0x4908201662b20cc18806,0x55408b40016846114083,0xa20406a83140ed829034,0xb044128a80f30a1816a2,0xa11047020d8270ae041,0x2309061c082f0c1b4187,0x881b8405c1034210e08,0xc206d61580044101b585,0x57080d026000bc2b020b,0x4817060d20938222a118,0x82b020d82c240d8222b0,0x5a41b8262aa0c56000a,0x11205c854362a034c086,0xa005c18785406983b022,0x2878540780d30b6045c2,0x21e1501ae043c2a03dc,0x8158c0406b810806b857,0x1203b181205b181213b1,0x1ac6056301b180995c0a,0x74605c0ec605a1ac6048,0x8368c0b460240f460441,0x2e8c0b80e8c0ac368c08,0xc01f460603803e8c0c8,0x7a303d0fa302227a3027,0x2e87d181e87d18111e22,0x50110cae010b43e8c088],#[0xa4404e02438206cc04c0,0x4062804a90d0c0c70121,0x81049510a03c592a0352,0x6e050d02d8c0ac60208,0xe0201f460640f4604068,0x2827016340d83d19a1c2,0x610dc06068824a45d820,0x806a48084af0181a1b0,0x81b05c040d00d0c11018,0xd8901895c07c04868846,0x87105c040d00d178080,0xbc048688088101950342,0xd00d0f8081a01a18a012,0x560f460441b4605c040,0x3a1f460447b4605c0746,0xe0c03e8c0c03e8c0b460,0x80f1047c0d10b005808a,0x16284e020d8504406042,0x6026001b09c041b05060,0x38090d22027010581501,0x570a01f8607c1f860408,0x35c08888889c0670ac10,0x40d9c2d0408824062068,0x911621d604178b410178,0xa00406c84ac2844100,0x7184090902f080b5859,0x908204068a848400340c,0x8c00844817e810c08685,0xc0b180500181610803,0x9c208039c204038c258,0x4700100e708100e310e]]
set_option maxRecDepth 16000 in
def g251H8 := limbs80 #[#[0x60001c61590cc1c02c3,0xa0823022190001004030,0xc004004000004008111,0x830082510400c228b141,0x1406c10c00030151c10,0x1bc04330006b51285a2c,0xc234828c17b3c34d8740,0x278e278e38aad21a50d1,0x8c471253883b18849a49,0x28ad629,0x34f254562c9d410,0xa0000000825cc4909b00,0x60841832c000f0b450,0x38ef0000000000208d,0xe09812232f7d1a0,0x10c10a4000000000,0x235c000437a80d000,0xfeb31e42b00029021280,0x7274000107800042d58,0xcec62bd89f000000,0x240dc0000c5ec420000,0x8794c59423a907cb93,0x450781d26cd311149b00,0x43dc0644ebba8,0x160e47e3cc0000000,0x30fc000000084940,0x3053c6951b4000000400,0x3124321e861a14a006,0x5405c8221ea2008ac0f0,0xd64272434d1c976a5003,0x8a37838d0de011847,0x9500000005087c6088b4],#[0x207b000000052dec,0x228000000000,0xf484000332b8e3,0x6400039de40b418c0000,0x2477e2a64b0db7ba7114,0x306b4330000000000,0x38cf733964ab054,0x5d14c88e8a5904a00000,0x943344b31db44,0x1faa8f53592720000c4d,0xe6d09f2e287fc2476432,0x248f386c000f2c78c493,0x10348e80000000000000,0x14229d8e580f8a130002,0xd831800032c806e946e5,0xaa40e9a8a9c000900141,0x3f6056ca5f425e13f867,0x668e8328f07dd42c0000,0x7cd471c006b9b10602f3,0xf0b7ad8cb46157b04a17,0x9cc02b51250e5459c48c,0x4f22f42a245ec84734f8,0x91080000002505fa8240,0x1cf4cc60580000000000,0xa1314ac22a9f03900007,0x442400140000000000c2,0xc90200000c264617d91,0x76a6dadb40380007890,0xf0000a1e0001eaf12157,0x60bb0e700020f,0x47800088a9ce1d07cac7,0x3a22f3c3d0f42b302cf],#[0xeb7e37fc7124064c100,0xb0eac6cd320866000,0x9e03d9472000311d0000,0x129370d3e8b0002e,0x8191b06000262142ac00,0x4b9000000443fa57e48,0x4c0001118000e1204547,0xa61800028f4e0fcca160,0x8d8b1a10e9ab28000f43,0x2821d7008b2e8000aac0,0x389e92d94029418c,0x3a3bc1e000,0x2ed4ae00000000000000,0xd4000717feb30003057f,0xc8505aa4cc3a263c1cd3,0x2920a4789381a98d010b,0xdb916ac0392948c00440,0x7309c00002308a2a8814,0x68fc00052fc000e0c48f,0x3b4000805f420a01e47c,0xb312000018400c33d1c3,0x800052f0000c04126b1b,0xc920002518191891120d,0xb16c8b31a327170000,0x9536a8f87208000506c0,0x53c608971318fa486502,0x3ec6944c000,0x5b4c2f335225593eaa30,0xd63751454eed1e8cdd32,0x1c3c0000000ea1,0x16b3ec00062f90819194,0x38084ee0324d2e9029],#[0xf0c8000000000098f400,0xd400050ee0ea931486f,0x38e6b]]
set_option maxRecDepth 16000 in
def g251D9 := limbs80 #[#[0xee96258130ee96258110,0xeb96458140ed96358130,0xf5553545319ed86dc940,0x97f855d931ed56358531,0xe756558551ead6458941,0xff1414c110ead6450d62,0xfe9624c110ff1614c110,0xfd9434c110fea624c110,0xdf9754c110fd9634c110,0xbf9854c110dfb754c110,0xdf9764c110bfb854c110,0xbf9864c110dfb764c110,0xff13154110bfb864c110,0xff16154110ff14154110,0xfea6254110fe96254110,0xdf97654110dfb7354110,0xff13158110dfb7654110,0xff38158110ff14158110,0xdf97358110ef96358110,0xbfb8358110dfb7358110,0xdf97458110ef96458110,0xdf97558110dfb7458110,0xbfb8558110dfb7558110,0xfe6624c510fe5624c510,0xfd5634c510fd5534c510,0xbf7844c510bf5844c510,0xdf7754c510df5754c510,0xdf7764c510df5764c510,0xbf7864c510bf5864c510,0xbf78350510fb54350510,0xfb56450510fb55450510,0xdf77650510df57650510],#[0xbf78650510bf58650510,0xdf57358510ef56358510,0xbf78358510df77358510,0xdf77458510df57458510,0xef56558510bf78458510,0xdf77558510df57558510,0xdef7358910ded7358910,0xdef7558910ded7558910,0xdef7398910ded7398910,0xdef7598910ded7598910,0x9fd8750d10dbd7450d10,0x9fd8754d10bf78154d10,0xcfd7658d10ddd7358d10,0x9ff8758d109fd8758d10,0x9ff855cd109ff845cd10,0x9fd84dcd109ff865cd10,0x9fd86dcd109fd85dcd10,0x9fd8755110bf78155110,0x9fd8759110dbd7459110,0x9ff855d1109ff835d110,0x9fd83dd1109ff865d110,0x9fd86dd1109fd85dd110,0x9fd8759510bf78159510,0x9ff845d5109ff835d510,0x9fd83dd5109ff865d510,0x9fd86dd5109fd84dd510,0xdf7815d910bf7815d910,0x9ff845d9109ff835d910,0x9fd83dd9109ff855d910,0x9fd85dd9109fd84dd910,0xbfb8158130dfb7158130,0xfdb8358130fd94358130],#[0xdf97458130ef96458130,0xf9d4350530dfb7458130,0xded62dc530edd6358530,0xddd63dc530dee62dc530,0x9fd85dc5309fd84dc530,0xf9d6450d309fd86dc530,0xddf7650d30ddd7650d30,0xbdf8650d30bdd8650d30,0xddd7458d30fdb8058d30,0xbdf8458d30ddf7458d30,0x9fd8759130dbd7459130,0x9ff865d1309ff815d130,0x9fd86dd1309fd81dd130,0xbdf835d930bfb805d930,0x9ff815d930dfb805d930,0x9ff845d930ddf835d930,0x9fd84dd9309fd81dd930,0xef96358140fb94358140,0xdef724c540fbb8458140,0xdef7258540def7254540,0xf9d6350d40ded63dc940,0xbbd8650d40dbd7650d40,0x9ff8758d40bbf8650d40,0x9ff815d940bbf8359140,0xdbf845d9409ff835d940,0xedd634c560eed624c560,0xebd64505609fe874c560,0xeed62545609fe8750560,0xeed625c5609fe8754560,0xcfd63dc560eed62dc560,0x9fd84dc5609fd83dc560,0xeed73589609fd85dc560],#[0xedd6350d60eef7358960,0xafd8650d60ebd6450d60,0xefb8058d609fe8750d60,0xaff8458d60edf7358d60,0x9fd81dcd60bfb805cd60,0xaff83591609fd84dcd60,0x9fd81dd160ebf7459160,0x9fd85dcd219fd83dd160,0x9fd83dd5219fd86dcd21,0x9fd83dd9219fd86dd521,0xdf561dc1319fd85dd921,0xdee62dc131ded62dc131,0x9fd84dc131ddd63dc131,0x9fd86dc1319fd85dc131,0xfe56254531bf78054531,0xfd56354531fe66254531,0xdf57654531f756554531,0xbf58654531df77654531,0xbf78058531bf78654531,0xdf57458531fd55358531,0xef56558531df77458531,0xdf77558531df57558531,0xfcd5358931bf78558531,0xded7458931eed6458931,0xded7558931def7458931,0xfcd5398931def7558931,0xdef7498931ded7498931,0xdef7598931ded7598931,0xddf7654d31ddd7654d31,0xddd7458d31fd78158d31,0xedd6558d31ddf7458d31,0xddf7558d31ddd7558d31],#[0xdbd7455131bdf8558d31,0x9fd8755131d7f7555131,0x9fd8759131dbd7459131,0x9ff855d1319ff805d131,0x9fd80dd1319ff865d131,0x9fd86dd1319fd85dd131,0x9fd8759531cfd7659531,0x9ff845d5319ff805d531,0x9fd80dd5319ff865d531,0x9fd86dd5319fd84dd531,0xb7f855d931bf7815d931,0xdf7815d9319ff805d931,0xd7c855d9319ff845d931,0x9ff855d931d7f855d931,0x9fd84dd9319fd80dd931,0xdf561dc1419fd85dd931,0x9fd83dc141dbd43dc141,0x9fd85dc141dbd64dc141,0xbf780585419fd86dc141,0xef56358541fb54358541,0xfb55458541df77358541,0xdf57558541ef56558541,0xfad4358941df77558541,0xfad5458941def7358941,0xdef7558941ded7558941,0xdef7398941fad4398941,0xded7598941fad5498941,0xf9d6350d41def7598941,0xdbf7550d41dbd7550d41,0xdbd7650d41bbf8550d41,0xbbd8650d41dbf7650d41,0x9ff8758d41bbf8650d41],#[0xdbd54dcd419fd80dcd41,0x9fd85dcd41dbd64dcd41,0xdbd76551419fd86dcd41,0xbbf8359141dbf7655141,0xdbf7559141dbd7559141,0x9fd8759541bbf8559141,0x9ff835d5419ff805d541,0x9fd80dd5419ff865d541,0x9fd86dd5419fd83dd541,0x9ff835d9419ff805d941,0x9fd80dd9419ff855d941,0x9fd85dd9419fd83dd941,0xded62dc151df561dc151,0x9fd83dc151dee62dc151,0x9fd86dc1519fd84dc151,0xdf77358551ef56358551,0xdf77458551bf78358551,0xeed6458951def7358951,0xdef7398951def7458951,0xddf7350d51def7498951,0x9ff8758d51cfd7658d51,0x9fd84dcd519fd80dcd51,0x9fd80dd1519fd86dcd51,0x9fd86dd1519fd83dd151,0x9ff835d9519ff805d951,0x9fd80dd9519ff845d951,0x9fd84dd9519fd83dd951,0xcfd63dc161bf7815c161,0x9fd84dc1619fd83dc161,0xedd6350d619fd85dc161,0xcff7558d61ef78158d61,0xbf7815cd61aff8558d61],#[0x9fd80dcd61b7f855cd61,0xcfd65dcd619fd84dcd61,0x9fd80dd1619fd85dcd61,0x9fd85dd1619fd83dd161,0x9fd83dd5619fd80dd561,0x9fd83dc5629fd84dd561,0x9fd81dcd629fd85dc562,0xbed85dc562bed83dc562,0xbed81dcd62bef8150d62,0xeed8359162eed8159162,0x9fd81dc143bef8150e62,0xdbd64dc143ddd63dc143,0x9fd80dc5439fd86dc143,0xdbd64dc543ddd63dc543,0x9fd86dc5439fd85dc543,0xf9f8458d43bdf8058d43,0xbbf8159143bbf8059143,0x9ff805d943bbf845d943,0xdbf845d9439ff815d943,0x9fd81dd9439fd80dd943,0x9fd81dc163bdf835c163,0xb7f855c5639fd84dc163,0x9fd84dc5639fd80dc563,0xbed82dd1639fd85dc563,0x9fd81dd1639fd80dd163,0xdee82dd163ded82dd163,0x9fd81dc164bbf845c164,0x9fd80dc5649fd83dc164,0x9fd85dc5649fd83dc564,0x9fd80dcd64bbf845cd64,0xff9544c1109fd81dcd64,0xff9844c110ff9644c110],#[0xff9864c110ff9854c110,0xff96454110ff94354110,0xff98358110ff94358110,0xff95458110ffb8358110,0xffb8458110ff98458110,0xffb8558110ff98558110,0xff5644c510ff5544c510,0xff55458510ff54358510,0xfbd5450d10fdd6350d10,0xdfd7550d10fbd6450d10,0xbfd8550d10dff7550d10,0xdfd7650d10bff8550d10,0xbfd8650d10dff7650d10,0xdff7454d10bff8650d10,0xbff845cd10dff7458d10,0xdfd645cd10dfd545cd10,0xdfd54dcd10dff845cd10,0xbff8355110dfd64dcd10,0xf7d6555110fbd6455110,0xdff7655110dfd7655110,0xbff8655110bfd8655110,0xdfd7559110bff8359110,0xbff8559110dff7559110,0xbff845d510dfd65dd110,0xbff845d910dff845d510,0xff5514c520dff845d910,0xfdd534c520ff5614c520,0xbfd854c520fdd634c520,0xbfd864c520bff854c520,0xff56154520bff864c520,0xbfd8654520bff8354520,0xefd6358520bff8654520],#[0xefd6558520bff8358520,0xbff8158d20bff8558520,0xff95158130ff94158130,0xff98158130ff97158130,0xff97458130ffb8158130,0xffb8458130ff98458130,0xfdd6350530ff56150530,0xfbd6450530fbd5450530,0xbfd8550530dff7550530,0xdfd7650530bff8550530,0xbfd8650530dff7650530,0xbfd8750530bff8650530,0xff56154530bff8750530,0xfee6254530fed6254530,0xfdd6354530fdd4354530,0xdff7454530dfd7454530,0xdfd7654530bff8454530,0xbfd8654530dff7654530,0xbfd8754530bff8654530,0xff57158530bff8754530,0xdfd7458530fdd4358530,0xbff8458530dff7458530,0xbff8558530efd6558530,0xbff8758530bfd8758530,0xfee625c530fed625c530,0xfdd635c530fdd435c530,0xbff845c530dfd745c530,0xbff855c530dfd755c530,0xbff865c530dfd765c530,0xfdd7650d30dfd64dc530,0xfdf8158d30fdd8158d30,0xfdd8458d30fdd7458d30],#[0xbff8159130fdf8458d30,0xbfd8759130fbd7459130,0xdfd765d130bff8759130,0xbff815d930ffb805d930,0xbff845d930fdf835d930,0xdff815d930dfd815d930,0xdff845d930dfd845d930,0xff95158140ff93158140,0xff98358140ff98158140,0xff5614c540ff5514c540,0xfdd634c540fdd534c540,0xbfd854c540fbd644c540,0xdfd764c540bff854c540,0xbff864c540bfd864c540,0xfbd4354540ff56154540,0xfbd6454540bff8354540,0xbfd8654540dfd7654540,0xfbd4358540bff8654540,0xbff8358540efd6358540,0xbff8558540efd6558540,0xfbd8458d40bff8158d40,0xff5514c560dfd8758d40,0xfdd534c560ff5714c560,0xdff744c560efd644c560,0xbff854c560bfd854c560,0xbff874c560bfd874c560,0xbff8350560efd6350560,0xefd6354560bff8550560,0xbff8354560dff7354560,0xdff7454560efd6454560,0xbff8754560bfd8754560,0xdfd735c560efd635c560],#[0xbff835c560dff735c560,0xdfd745c560efd645c560,0xdfd755c560dff745c560,0xbff855c560dff755c560,0xdfd73dc560efd63dc560,0xbfd85dc560bfd83dc560,0xefd8158d60bff8150d60,0xefd7458d60eff8158d60,0xefd8458d60eff7458d60,0xffb805cd60eff8458d60,0xefd645cd60bff815cd60,0xdff745cd60dfd745cd60,0xdfd81dcd60bfd81dcd60,0xbfd83dd160bfd81dd160,0xdfd83dd160dfd81dd160,0xdfd64dc131bff845c131,0xff56254531ff54254531,0xff54258531ff56454531,0xfdd6350931fdd5350931,0xdff7550931dfd7550931,0xdff7650931dfd7650931,0xdfd7558931fdd5358931,0xfdd6454d31dff7558931,0xfdd8258d31fdd8058d31,0xbff8055131fdd8458d31,0xdfd7559131bff8059131,0xbff805d131dff7559131,0xdfd65dc141dfd63dc141,0xdfd43dc151bff845c151,0xff53258551dfd64dc151,0xff54358551ff54258551,0xdfd7650951dfd764c951],#[0xbff8358951dff7358951,0xfef8358951fed4358951,0xbff8050d51fed4398951,0xfbd6450d51fdd6350d51,0xdff7650d51dfd7650d51,0xbff8650d51bfd8650d51,0xbff8059151dfd64dcd51,0xbff845c161bff8359151,0xefd654c961dfd43dc161,0xefd6350961dff754c961,0xefd6550961dff7350961,0xbff8050d61dff7550961,0xdff7550d61efd6550d61,0xefd8258d61efd8058d61,0xbff805d161efd8458d61,0xbff855c543bff8158d42,0xfdf8058d43fdd8058d43,0xfdf8158d43fdd8158d43,0xdff815d943bff815d943,0xdff715c163dfd715c163,0xdfd745c163fdf835c163,0xbff845c163dff745c163,0xbfd84dc163dfd74dc163,0xdfd725c563dfd84dc163,0xbfd80dc563dfd745c563,0xdfd74dc563dfd72dc563,0xdfd80dc563bfd84dc563,0xdfd84dc563dfd82dc563,0xbfd80dd163bff805d163,0xbff855c564bff835c564,0xffd654c520bff815cd64,0xffd6354520ffd864c520],#[0xffd8358520ffd8654520,0xffd8158d20ffd8558520,0xffd7550530fff8158d20,0xffd6454530ffd7650530,0xffd7654530ffd7454530,0xffd645c530ffd7458530,0xfff815d930ffd815d930,0xfff845d930ffd845d930,0xffd854c540ffd654c540,0xffd6354540ffd864c540,0xffd8654540ffd8354540,0xffd8558540ffd8358540,0xfff8158d40ffd8158d40,0xfff744c560ffd744c560,0xffd7354560ffd4354560,0xffd7454560fff7354560,0xffd735c560fff7454560,0xffd815cd60ffd755c560,0xffd6550931fff815cd60,0xffd8059131ffd7650931,0xffd8050d51ffd6350951,0xffd8059151ffd8650d51,0xffd7350961ffd8359151,0xffd8158d42ffd7550961,0xffd745c163fff8158d42,0xfff845c163ffd845c163,0x11200d0007a00380000,0x2c00292023c01dc0172,0x41e03e603a40376032a,0x590054404f804b60456,0x70206ac0656060005c8,0x81007ec07b40786074e],#[0x90a08c8089a08620834,0xa4a09ea099e09660938,0xb9e0b520b240aec0a8c,0xcd40c920c6e0c4a0bf4,0xe0a0dd20d860d4e0d20,0xf4a0f260eee0e980e56,0x103a100c0fca0f9c0f6e,0x1166112e10e210aa107c,0x12ec1296124011ea119e,0x13fa13d6139413701338,0x14cc14a814841442141e,0x163e15f21588153c1504,0x17c41782174016ea168a,0x191818ea189e18521810,0x1a441a1619f219881950,0x1b981b4c1b001ad21a7c,0x1d001cc81c7c1c441bf8,0x1e361dea1db21d661d2e,0x1fe41f8e1f2e1ee21e8c,0x216020f620b4207c2030,0x22d222ae2244220221b6,0x240823bc237a233822f6,0x2584255624ec24a02454,0x272826d22686261c25c6,0x28b82858282a27d427a6,0x2a0c29ca2974293228f0,0x2bd82b8c2b4a2acc2a76,0x2d682d1c2cc62c702c1a,0x2ee42e842e4c2e0a2daa,0x306a301e2fc82f862f30,0x320431b83162312a30d4,0x338a333e32f232a6325a],#[0x34ca34923450340e33ae,0x365a360e35cc3562350c,0x37e037b2373436d4369c,0x398439383900388c3836,0x3aec3a783a4039f439bc,0x3c2c3bd63b943b5c3b24,0x3d3a3d023cd43c9c3c6e,0x3e663e383df63dbe3d7c,0x3fd83fa03f4a3f123eda,0x414040ea40b24066401a,0x4262422a41f241ba4182,0x43844342430a42e642ae,0x44ba4482442c43fe43bc,0x460445c24580453e44fc,0x4780473446f24692463c,0x48d448924846480447d6,0x4a0049b449864944490c,0x4b4a4b084ac64a844a38,0x4cbc4c704c2e4bf64ba0,0x4e1a4dec4db44d7c4d1c,0x4f3c4f0e4ec24e944e5c,0x505450084fe44fa24f6a,0x51765152511050ce508c,0x52705238520a51be519a,0x5360532852e652b85294,0x54b45472541c53da5398,0x560855c655665542551e,0x573456fc56b05682564a,0x5856581e57fa57b85780,0x5982592c58ea58a85884,0x5ae05a9e5a525a1a59ce,0x5bd05bac5b745b465b22],#[0x5ce85cc45c825c4a5c12,0x5dc45da05d865d6c5d16,0x5f2c5ef45ea85e485e06,0x60305fee5fc05f925f5a,0x6148611060e260966068,0x62c4626e620461c26194,0x644a63fe63bc637a6338,0x65b26570653864d8648c,0x671a66ce668266406608,0x6882683667e067a86752,0x69ae696c692068d468b0,0x6b0c6aac6a6a6a0069d2,0x6c566c146bc86b866b44,0x6da06d546d126cd06c98,0x6f126eda6e846e4c6e00,0x70e8707e70326fbe6f5e,0x726e722c71cc719e7148,0x73cc736c732072ca729c,0x751674d4749274467404,0x76b0764675f075a4756c,0x780e77ae776277347706,0x7980792a78d478887850,0x7ad47a7e7a1e79f079c2,0x7bce7ba07b687b307b02,0x7d4a7cf47c947c347c06,0x7e767e487e107dce7da0,0x7f987f6a7f0a7edc7eae,0x80e2808c80547ffe7fc6,0x825481fe81bc8184811a,0x839e8352830682d882a0,0x84b684888446841883cc,0x85f685be8572854484ee],#[0x874a86fe86c686848656,0x88da8870882e87c48782,0x8a9c8a3c89fa89b8894e,0x8bd28ba48b588b208ae8,0x8d588d0c8ca28c388c14,0x8eac8e7e8e3c8ddc8da4,0x907890188f908f448eda,0x91e091a8917090fc90b0,0x93ca936092ec928c924a,0x95a0954094fe94bc943e,0x9762970296a29660961e,0x996098d89896982c97ea,0x9afa9a9a9a4e9a0299ca,0x9cb29c529c069bc49b46,0x9e569e009dbe9d7c9d1c,0xa02c9fcc9f6c9f029e98,0xa1a8a170a12ea0e2a08c,0xa3b0a350a2dca272a208,0xa5f4a59ea516a48ea438,0xa7f2a774a71ea6c8a654,0xa9bea968a8fea8bca870,0xab76ab0caac0aa60aa1e,0xad6aad00ac6eac22abc2,0xaefaaeccae58adf8adac,0xb044b002afb6af6aaf3c,0xb242b1d8b18cb12cb0cc,0xb436b3d6b38ab316b2ca,0xb5e4b5acb556b514b4aa,0xb742b6f6b6c8b686b63a,0xb8fab8c2b844b7dab798,0xba9eba34b9e8b99cb946,0xbc10bbcebb6ebb2cbaea],#[0xbd6ebd0ebce0bc80bc52,0xbea4be76be34be06bdba,0xc002bfcabf60bf32bedc,0xc192c13cc0fac0a4c058,0xc2dcc2aec262c220c1c0,0xc3fec3c6c384c34cc314,0xc57ac51ac4d8c48cc454,0xc728c6dcc67cc61cc5c6,0xc8ccc88ac83ec7e8c788,0xca5cca10c9bac978c92c,0xcbd8cb96cb5ecb08ca9e,0xcd54cd08cc94cc5ccc10,0xced0ce8ece38cdeccda0,0xd056cff6cfb4cf4acf12,0xd204d190d144d102d0ac,0xd3f8d3a2d338d2f6d25a,0xd588d528d4c8d490d44e,0xd722d6d6d68ad63ed5c0,0xd8d0d88ed842d800d778,0xda4cda00d9aad968d926,0xdb8cdb4adb12dad0da8e,0xdce0dc8adc5cdc06dbba,0xddf8ddd4dd88dd64dd22,0xdf6adf1edec8de86de44,0xe0f0e0aee04ee002dfb6,0xe226e1eee1c0e174e13c,0xe38ee356e2f6e2aae272,0xe4bae46ee42ce3eae3b2,0xe62ce5eae5a8e55ce51a,0xe776e734e6e8e6b0e66e,0x3054601b85c04470545,0x78282012221221b85e07],#[0x8034054680385e1086e0,0xe0586c13002785e0f810,0xa04e0d28070ac25e1783,0x900786e1382e008f0701,0x85e1103e0a01e020d110,0xf84e0b80c0f01a18801b,0x834a4382011c15102903,0xe1383e0b8043c210781a,0x5e04980808ea0c151c01,0x1860c460483105436138,0x44405436178484b8282,0x52785c044405c361785c,0x7e1410088122630111c1,0x87e1301e0a0804847181,0xdc7e100384b82821850d,0xd45e118584b82820100,0x8e08310d4500608e0831,0x184b82821860c480060,0xb85e0a0811036238400f,0xb01e14440d88e130184,0xe1444048361c12e1208e,0x5823820c0381701e0a08,0x8350c450643105438108,0x1103a1415110321608e0,0x311608e08311104a1417,0x3820e0441005823820d4,0x1034e1382821830e0682,0x80e0340d840b83805436,0xc381f84c078282047160,0x1010242c01b84e0a0860,0x182ce13858238260e861,0x411c9e0a08e14440d036],#[0x5e141061301e0a082803,0x4470d040b4060d0150d8,0x1b84e0a08614361c2d05,0x617848238204037202c0,0x984382822860c080b021,0xc380e83454380c340052,0x4308e0b000c4381a8345,0xd010c2382c00360e070,0x304543416830a42a4544,0x3e0b000a02a1e83e14,0x1f08e0829040371485c2,0x81834c2382c0186a0c29,0xa480d308e0a830403,0xc38142221782c228361b,0xf080c4340f08e0b0004,0x4007080c434103185436,0x586a102618200e0150d8,0x19070e0360d0441f000a,0x60d0421c000a58609822,0x8e0b000d83114870e03,0x42cc2382c0183a18291f,0x78311708e0a86040311,0x4c0029a18261f08e0b00,0x8612860c41022874098,0x184c003107880b41ee0b,0x90a1c0031203504382c2,0x61686098721801c23820,0x2a18100c450b308e0b00,0x44854660e150e03c238,0xd85854360d0560e8644,0x10198385c380d8585437,0x6170d8341583a184485d],#[0x98170b05616170dc361,0x7a0c020a6150a850a003,0x8a08b08e0a83a17000a8,0xc0400b08e0a85a0f000a,0x1b08e0836c00381c0e01,0xc0708e0836c00311c2c0,0x4c2382a0f00a18292403,0x82c0283a1829200e0140,0x683c042c454603804c23,0x2382a0f000a42d180f01,0x3804c2382c02830e07c,0x2d1c0f014020b0264546,0x311c0e01308e0b00098,0xaa15100e01308e098604,0xa140209a150a8509a850,0x86098a0b406038150d85,0xf01c0500b08e0a84c02,0xa0290b6151031854360c,0x7854803c07016170d850,0x15121703b010e80f60c4,0x382c00470b070a3010b6,0x2285a1b00098703c01c2,0xe0a85c0286098908b82c,0x2c02850d870380400f08,0x85c042c454503804c238,0x804c2382c02850d8700e,0xc44c2382c00290dc503,0x8e0b000b43114020b115,0x22e0b080a686040261f0,0x18311c1e040290983414,0xc40e200e01308e0b00a,0x60a0803c01c2382c0286],#[0x381c0e01308e0b01c028,0x36240e01308e0983040,0xf01c0500b08e0984c0,0x3804c2382c0301a18282,0xb01ee1208e08120e070,0x5e103484b82822860c47,0x120d06e1781048150d0,0x20a0c0c342b85e078282,0xd0821b85e0612613828,0x41c2d0a806e1781c0c15,0x34182d0ab85e07030543,0x700110ae150344a81054,0xc86e1426e1308e0912a0,0x81a8145c380e81454380,0x2c45460b308e08360483,0x3030a42d180f01703a04,0x2382c0f000e07c2382c0,0xe061261815088703804c,0x5e0684e0b080d0780f85,0x84e0708e08120d0704b8,0x38184b82c2186088ae16,0x17810d03e120300385a1,0xc2384e0908048370d86e,0xa0b42a01a03e17814542,0x20e1781e0b0861286048,0x781a18370d9151c2d0a8,0x1781c0e86038152022e1,0xc0303c2286038c0b42ae,0x5100f0340700b85e0782,0x81c0c2c85c80a7030aa1,0x7030aa15100f03407e17,0x1708e0b81c0f000b090a],#[0xe09080dc120d8503c0de,0x361b85e0782c20120d06,0x2860a4804b84e09080dc,0x434180e01308e0b03c0,0xc0286038ae1412c2382e,0x9200f03785e0708e0b03,0xc03804c2382c0303a182,0x85c2382e0703c0286038,0x58305434180f0340700b,0xd385e0583854706385e0,0xe0f810b8150b060dc360,0x6e1683c1107a07002385,0x83a170441e81c008a4f8,0xe86c1107a0700229ae1b,0x1b0481d83c007a7b85e0,0xc0b85e042c8546e17816,0x540b8161a83038152483,0x81a0d8603a15182809b8,0xd89e1781a0c2c8545e17,0x3c0701402c2382c13000,0xdc36e178160c2085470,0xf01708e0b04c02860988,0x4803c0de178160c46180,0xc2005f85e0f81a180e05,0x282e0ab85a0e81111151,0xe1034a0708e082ac0044,0x8e0a83c03060a4820f85,0x81e0b0811c34140e0130,0xc05c2382a1300c182622,0xba9a0ab83a1681454703,0x1300e0a85c230609880,0xea16830ba8111d151c0e],#[0x6a1683a04470b9151c1,0xc13c2382e1034c00311c,0xc0700b84c03060d0311,0x2c0281c1828240e0c446,0x8160e15180e61404c238,0x78160c2e85468182ee17,0x1818e1781854341406e1,0x30d08e1781e0b08a0c34,0xe2b8500284e0708e0a8,0xde1781c2382a0f00c18,0xc06e1382420370d8603c,0x180620f85e0708e08341,0x40d850df810da8345434,0xc1a830a49e09080dc3,0xa83038c0380460708e0b,0x40700b85c2382e0700c1,0x888e178160c46100f03,0x62006e1783e0708e082e,0xb03c05c2382c0306a102,0x85e0700e0983c1b08a10,0xe83c06080b450380f037,0x3c05c0a0b61a08098782,0x80a45c0a0b0a2080a450,0x8382e080a87c0a0b0b60,0xf01a1a080a0503c05c09,0x351ea238261a8004cb82,0x61a1325450b42ce14300,0x50b6056189784c50b605,0x42c25460b288e0a80110,0xf01a002d200f01703c0,0xe0a80110603804a2382c,0x58144160048100e01288],#[0xc2a10440a98281595120,0x182ae1382e0048160565,0x12060a013e1382e0048,0x800a841140d01784e0b8,0x403e1382e00481805e13,0x6001e2f84e002a104403,0xd188e0b850d40d84f03,0x341784e0b800a4351428,0xf8204c34200640b030a4,0x290c050c02d0361e62,0x3784e03821206e1382e,0x6e1382e03030a42d1c06,0x3e1382e02860a4281e8,0x1095228240438a543517,0x25460a90e28385c0f011,0x644c95142d0b105c0c2a,0x6a082aa5448142d4168,0x5c3516820b69544c3814,0xc0425a18971e8240438a,0xd4168625d13142d41703,0x69744c3816970a8410c2,0x1784e0b800a4351a820b,0xa0dc60c384e003810450,0x360d0381003e1382e002,0x18be0b850c0130d08018,0x1b84e0b800e044142d08,0x80dc60182ae1382e0048,0x80090361a86e1382e003,0x703088290b06c0784e0b,0xa8bc0f01a102d188b01,0x60888a1703094220a85e,0x2224300b78222f03c068],#[0xfa1005a2f82c0f01a18,0xb4703c05c0f012543418,0xd08a2f82e0284c0c290,0x4100f01684a2f82c0f01,0x80a102d0c86014950c03,0xb85c0f010c0341e8be0b,0x1784e0b800a430180700,0x11205e1382e000d12050,0x85c0f010b06038046004,0xe07e13800a841102508a,0xb050380462382603030,0xc0c290b470970308829,0x8004e860a4661b84e0b8,0x382e02860a6131b84e0b,0x200e01188e09801106e1,0x7813e1382e0303a1829,0xf0158be0b03c06860888,0x4431b84e0b8003443140,0xe860a4701784e0b8003,0x620300a89e1382e000fc,0x608890380460382e1703,0x503c056118be0b03c068,0x8310d05e138003e86104,0x1983058150d04e0a8805,0x7088503c0560c1685434,0x10a02d8544059860544,0xf05986a238211c221f,0x42c310d040c41e454341,0x311b0be0b040d8311702,0xc310d03c2f82e0286058,0x18242870be0b040c4742,0xd0c4601902614260d052],#[0x10542c1b0be0b80c102,0xe864584485460dc3560f,0x854360d85054440d0560,0x17a18251f01854370d85,0xe17a184210370d583c04,0xd834042505e86108560,0x3411c4c06170dc361617,0x403094220982c1b0282c,0xd45e0a0b0d0310dc561,0x2618220c4682f82e0031,0x8282e83058341a0b00d0,0x38282e8361b0108880d7,0xdf8282f0106034183709,0xb0be0b01a0e86088a0,0x440c31454360c0f01c05,0xb85e090b110362431108,0x2830b433192003b8005,0xe0b80618160c46c2f82e,0x34120b0158608831170b,0xf85110200d87e0a0b0cc,0x2c06614220d85c078282,0x8800ee038282c380dc78,0x22098682f82e00300e05,0x5150cc340c0700a85a18,0xd033130be0b800cc361,0x290dc60c5150e03c2f82,0x3040b4311b0be0b80c10,0x2382a18310888c2f82e0,0xe0304a18311c0fc10006,0xc12860a4281f01c2f82,0xf0140245436170be0b8,0x80f0170be0983058341c],#[0x1206c2f82e02860a0331,0x1254480c2c41688e0a80,0x6801205c058625c41130,0x12062542c0cc30380410,0xe0848140e01288e0a80,0x8010a86068261426e138,0x20301784e0b80098391b,0x5228246a950d84408341,0x2c690e0a8a0e0f05c049,0x189710430d8420895120,0x8180420f86e00981086a,0x86034909803e1382e004,0x8703807e1382e0305a0e,0xb0503804603826201a0d,0x108260e4409422c14260,0x481003c1701254341780,0x80700834120400041a10,0xe450380462382600481,0x7008221204e1382e0026,0xe01180e0988068361c0,0x18220cc5e13800a84110,0xe0a800a41e098762f82a,0x441a88e0a8011040b288,0x35038a03804a2382a00,0x18400e88e0b85c0706a0,0x3804a2382c0706a00282,0xa2c2c26382c0684110b0,0xe082f0c460638509b80,0x84e0b800dc311806e138,0xf01e1382e00240c46a0f,0x182ce1380e0a83078291,0xe0c47e1382e02830a61e],#[0x83088903804603826201,0x503c056118be0b01c1a,0x3e830e46e1382e00310c,0xe0b060d4222384e0b800,0x2e0284110500f85c0588,0x8be0b80a10280e46a2f8,0xc0e01188e0980c18311e,0x1583e1382e03060a0291,0x8c1823200700b0608831,0x80a0503c05c098382e0,0xe0bc180d8208a060bc1a,0x2e0807c231c0f01702a0,0xa060b82037102d215838,0xb8201f09c7606150e03,0xc2011c8e85470b485606,0x178160c8e85460798560,0x30aa15118185c380c20e,0x81e0a8861a80060a0a70,0x81805422182e0b42ae17,0x2382618180889e178161,0x45c380f8503c0de1781a,0xbe0b800d8180e0603c07,0x4703920e090b060381b0,0xe06c2f82e0304c0c290b,0xd8341b0be0b80c13030,0x20dc360d05e0437e0988,0x85e070305420088642d8,0xd8703a1882f82080311b,0x8890a01820b8242c220,0x3c0de178162382c0e86,0x5c2f82e0304c0e860a47,0xc2c4548080180dc220d8],#[0xa434140f03402e1781c0,0xe04370d8341c0700b030,0x2c0f06a0029268840f82,0x800d80e2c0e01404a238,0xf01584a2382c0f81c1a,0xa1ee1382e00310a0361c,0xf06e1784e0988a04372,0xe0b03c1a8108896000ec,0xfc0f060a4803c056118b,0x37220361185e1382e000,0x588c1b820dc360889a10,0xb8003684110601703e0,0x70d840083725436128be,0x83e04200381520070dc9,0x382c182608870b42ae17,0xb8160c20088903c05a2,0x45431118503c0de1688e,0xbe0b80c13060c4603c02,0xbe0b80c13060a4281f0,0x1860b420e090b088361b,0xa0c29200f03785e06831,0x111056070be0b80c1306,0x44c04150d87049010543,0xb8505f010f8808812614,0xa080c44428308400861,0xd88064120218240784e,0x41385e138211208c0412,0x1054381104c04150c44,0x4370d430e14150d8341f,0x1784113820d208c04362,0x11385e0a080d8341812e,0x341187404340e0151105],#[0x4150b888438560815c04,0xe04420352198384385c0,0x11060643440784e0a080,0x50e0301101823820e034,0x8312422a0d150e042751,0x1043822c2184e0b00a1,0x75876130260b000c4352,0x50d0311382c203411c42,0x85e1444054220d850c01,0xc6150dc403818616150d,0x51024042150c43415850,0x84c01860c49042150c43,0xd100d090600ec0708e0a,0xd88a150506308e0844a0,0x2010c0882c2385110220,0xc1f05c0844c04980d036,0x8444047180f4411511c4,0xc29456100a85a0902c21,0x45438141d454300e04a0,0x4a0c294542a102003a83,0xc4445610241d84115110,0x544412050818503986a0,0x14220543811040c49d8,0x80d43123020ab080d03,0x3811050768240b00a13,0x3708618220c08a1e8244,0xc0838274441482c08100,0x8e170111300280362b07,0xe616150d850430220b0,0x1850800ec06150dc6080,0x882c0010a13080c0382,0x8098203f08a121011c7c],#[0x150a84a1426456100a85,0x82908a8609a101e85099,0x382a1829610261c87e0,0xbc24721709c2c411308c,0xb10442789320586a0f0,0xc8361a81c2f091881c27,0x24f0b1486c270b104424,0x3a0485c2f092185e1b09,0x86c270b10442789361a8,0x49e2688161a85c2f091d,0xc270b248660f0926b0b1,0x110a12789a61a8520e81,0x83a070bc24661b09c2c4,0xc8560f09c2c9e149e219,0x14a12788661681c2f091,0x1c270b1985e0f0b27b09,0x81c0c150d0aa1b85a0d8,0x84818370c02661435849,0x10120d8a84981c0a080d,0x2c3404385e138221a081,0xe178440f82820440d036,0x2c0d81110342a1204181,0x340f8609a1221b858238,0x7030d0461b8560b81054,0x612c0c150b898498205,0xc20310d070dc36219856,0x2c203411c505884a0b02,0x870c481054300d05a091,0xd4405881c1444054220d,0x61615098341816854310,0x360d0a0c6150dc30cc12,0x12a16820590540b08110],#[0x68240b08110364483429,0xb08618220c4705a8541,0xc0b08110960d0720812c,0x92083c854310d050db05,0x2685c22e1b8544896854,0x85c1302c202612060a0,0x45c361044a0436454481,0x28691844a85a05152a81,0x81c0036120745c26a182,0x685c0e81454d4498721a,0x1120f40ea190645c1a03,0x680da1a85a0515448946,0x4b034549a0d0545d060,0xb44a8141d04408361207,0x7a1104a0902a15120d8,0x302c202612050d01aa1d,0xd8ac1302c209a0d85c1,0x21f820cb8420b08a1512,0x908826e1041448481822,0x13e1010c2382a19120c4,0xe87a1782a05840d0b0d0,0xd150b0a1118709812c1,0x2c24415020780da1681c,0xa140dc238261281a1912,0x8c0d84c009e30244141e,0x60a08520812c17022d70,0x8311881c1302c20310c0,0x19120c49c13020a30827,0x278c0888511384e0b08a,0xe08b509b85e1082c2112,0x1e144445436182808887,0x10a0785111170d868428],#[0x91704e86a1410a043e26,0x1b84e0b0804847243a08,0xa1a85a043e343404c102,0xc2138400e4218661517,0xa0a385a061245434183a,0x846128260881c2031110,0x382c22120c4371908216,0x158460a81c20440d8de1,0x848a0d01221a85a12826,0x84026e1784e0b0811186,0x341c2003b03454381422,0x8441f85e0b81c2284048,0x437241384b08617000d,0x1c342198460b08c02126,0x43018e1582e05150d03e,0x8c2385e0b81400370d83,0x820dd150d86849842801,0x30204b08280311c22849,0x1781a1815089122482c0,0xa182244a1528370d818e,0x44890a02620846e1781,0x60a02608b85e0b81c20a,0x8361a08a0985604340f8,0x1a120c48e13824203704,0x4834182260784e0b08a,0x2a1822848ae1782e0708,0x36282809984e1781c238,0x1261581c2385e1382110,0x385e1382111810d890d2,0xfb85e05150d090d212c2,0xe05840d090dc36608460,0x685480dc3684b08e1782],#[0x151d300b82a6158160e8,0x434182e0a98361581a1a,0x4a150d056058560c1085,0x2689361683c549615810,0xda0d86c54ac5f06c080d,0x15283004f05c089e24c0,0xf83706c089c24d85a07,0xf020a893a0586c54bc5d,0xd8645490c02f04f0520,0xc54d8c20da152003a81a,0xc1b020c80d21985a0683,0x661493c5482709ac5c93,0x81a0d15371703c0ec0b8,0x2445c0ea150504c0d61a,0x485a068361b153520114,0x430c09e24c0ec170203,0xc00ec1485c098624f152,0xc089e2680da1586c5490,0x803a85a0583454b06b03,0x9ac548a691783702a191,0x915231703b0621b0260c,0x54c836834800ea168161,0x3a8340c1a03586a16814,0xa168161b153120115170,0x2849e26b03c083903483,0x603b0320f026189ac547,0xf152b02a168160c2c454,0x2f21b05c082627a8160,0x3b052170260c9ec5480c,0x90a127985a071524300,0x26178327b151b03c0829,0xee168360686c54903b0],#[0x781a0c2c45470c00dc08,0x1781a0d150b0a08018e1,0xc00481c460f82809902e,0xa0c382485c102ac2382,0x351c1ee103404308e0b0,0x3003881c0304e0b080e0,0xe850a822e0920a068361,0xe81454a1102ec1e8761,0x182403a854141303706a,0x30e07c0304e0b080a848,0x830e09c1308e082dc009,0xcb08885c038411382c22,0x2ae1784c2382c030624,0x1b82c203411c40b4222c,0x70d04c144425a150d834,0x82a07000d8481e150e03,0x507411020d8481d8720f,0x304e0b08268361883a0,0x8b8248285a0584c00dc,0x145490bb07a1d87a0c2a,0x903a8340c1a03706a168,0x83c03840e782c22850d8,0xb00e102ae0b081207088,0x784c0308e083411ca08,0xe083411036341e04083a,0xa168420f0061584a0708,0x561708e08440d8341d12,0x2ae1706e0b08111832e8,0xe810d0461c2284300e10,0x16830d046250007a85a0,0xb9152e1e84182a0515a,0x87a1061583a0685a0c96],#[0xd081c23820e0442835,0x8e08341106216846130,0x382a070861437221026b,0x708e083411c508b00e1,0xa1585c2382110360d08a,0x5a0444c23820d8341d12,0x408708e0a810dc341b8,0x836c00441e83854380d,0xd30060437201ec2185e,0x20d283118661083c2382,0x82c22836102e28204218,0x8360d0c0dd85605000db,0x18440308e17810de83e0,0x1d820d03745436142006,0x82012e13820d03742036,0x708b84c2283e0b006043,0x87a1681e0b08a0d840d0,0x54a8498245685a043411,0xda1261581a16812602e4,0x4308e0a830e0341c370,0x6c2385e08440d834181e,0xa15241e041810e2150d8,0x82f60c2d0ab85e05120b,0x8546c1b85e0d8103a151,0x584c2a1306e1583e040e,0x858c00e6189584c90a49,0x6056318810440b605081,0x6a1362d86c0d82a15882,0x612056098062c481c0d8,0xe84e01a1b036218c1c2a,0x68ca2064068ca2041121,0x1a8ca2041111340d86c0],#[0xca20861786a3113a2054,0x41111e44d86c0f014168,0x985a0b01a20a61a8ca20,0x2041148f8351c44e8ba1,0xa2e8644e882002a2c2aa,0x62c380d4707c0fa0985,0x82620361108612016098,0x58b620441b0160012611,0x58062c3611080282ac0,0x349d25444118406182c,0x504c0dc1701c0c952809,0x84a0a80a2c2a12060908,0x284a0a800b68b44c381e,0x8583411c5c0c292542a1,0x561f828583411c561f82,0x8951206c04262561a0a8,0x800e25448161ac041803,0x8058ba1b056218a23010,0x78790ca1988108587a1a,0x86612056038262c26120,0x32882586c168b09a88a2,0x1d214791a61b0540f01a,0xf201f60e86a228246a8b,0x90680dc148b60f012209,0x1a4602cc1583c0686254,0xb0522d83c048827c949b,0x958325e86108709d0d46,0xc1b05c04952609c05180,0xaa1036120925c860680d,0x3612082618741b82c051,0x8481ca026203c058222c,0x68361a8400e80e0a8b09],#[0x200361209a1280e0a8b4,0x8120728098a130121c82,0x1a0d8621c82c04800d89,0x701254a021846098062e,0xd8a0120720c1a03703c1,0xa426878621c82c04800,0x260c95878342887a0382,0x88a2880d428062056160,0x28a152147906a2d85c06,0xf01a228c1985a2d1ea2,0x41583a311ea205479066,0x54851e41985c0688a307,0x306260b61783a311ea20,0x8507b0503588e0b0160,0x1101a0382a2c310c0709,0xa12800a382a2d1e0c47a,0x7c058061182620361107,0x80981fc048a62d88110,0xb01081846098062c3611,0xc20621e84e0829878261,0x28602c1686e16836070c,0x82e0436c10342a810942,0xc340d86818120dd88e17,0x7040d8442403623820d,0x60437221804f0b617826,0x2860821980c2f8286304,0x36182820b0be1426a182,0x8361107c2f82e1444088,0x41810dcb84985a1e84a0,0xd21261d8460a87a12822,0x4a88e1782e04360d080,0x2a0437c0c36610343c37],#[0x261d856098120287a168,0xa849820d037254361a1,0xa88e1782e0703a01840b,0x1e82608370d036202809,0xe0837a002c0d88052876,0x8e08370d036182006288,0x9a140d62d8811050128,0x118a158461d826003611,0x4980e1382622810dc948,0x468162d880dc50b82c4,0x2a01876098025a810dcc,0x810d0371d20462876128,0x988a04291c200638262e,0x2e81620291f03c1b84e0,0xe018ba04292306c0d826,0x3a1306600d61303c1b82,0x809a2086188e1781e0b0,0x88a13820dc360d060b02,0x82d21482c2e81880221d,0x880820b0b61620088371,0x3182d21482c2d810a822,0x9c1c6826072850941c9,0xd0941c9a209e24d8561b,0x1b09c1c721883a060981,0x60f07c2462849e26a816,0xe26985c1f09189e24d85,0x9e24d8560709c1c62849,0x5831188620d81c270714,0x259120d0446508609122,0x544a818689a480361c36,0x860a810989a45112211,0x79122112a04480d84461],#[0x84864610860a81450262,0x1848441a132821008915,0x87849810d830e8266158,0xd030f4224218460a1211,0x84c24484a124c7849840,0xcc0832268930346c0829,0x886170210c9e24c0d189,0xc8620f02a061a4509a0d,0x1c9cc0a810c8932680d1,0xd1ca1c0a810e49e2680d,0xd1c2c45185c08932780,0x715242c28514c089a278,0x82f0b09e24d85c082660,0x454720f020bd810b3151,0xa454548182a042e0a893,0x18261150d87a042e24c2,0x512a04480d8426a81869,0x269151c83a0500120361,0xa0b915152060a810b82a,0x1220e10a04361c9aa042,0x42e87a1061681242e879,0x15810d844142d0a92146,0x144e8c1612604360e126,0x1361586a1e8c1a0721d2,0xc2a44d822800e2546479,0x250640f0181c8746a8c1,0x4689422d82c049203898,0x72811ac040e260361826,0x860a91a60b012800e254,0x1e8c191a263012800e0d,0x61687a3064791361583a,0x361581c1f0c19214791a],#[0x721883c1d81c3052789,0xf860bd2046080849840d,0x610340c4622184608340,0x212]]
set_option maxRecDepth 16000 in
def g251H9 := limbs80 #[#[0x4018a840002082306096,0x105c0c100201700c0030,0x64000204a00008024100,0x4738a0cc205080005,0x574710000b0021411010,0x4004e18528000010214,0x422c0004000041000,0x12880400010062011,0xc1ad72832050880c190,0x810850022801c1084000,0x71c00010040400003c81,0x46442640d090003c028,0x40bcb00224608000b440,0xc0000c51011400850,0xc58401461c204604210,0x40020033c40c1109582,0x2085bdd2840001410800,0x14061010604100118138,0xa40461c3a843c420f39a,0x718110a1040091120001,0x7fe16a3c34270f800000,0xf95c0dbc01633d8f6ad3,0xa30b000008de00007659,0x468000b48a000322a203,0x5bee5609881085da03fe,0x240821e80001,0xc40000000000000007ad,0xeb32028800070a60b85c,0x47cf774c0490000,0x92a86ec298039404358e,0x66980002332ee43a40bc,0x33c52473c7f0000258f],#[0x31658207a0aac188000,0x32be00028,0x1617cb14ef133210000,0x829f2003c84c53ac9000,0xe6dbb628417000000019,0x183d8a3062d65008,0x2b456f25d82524000000,0x5e3e740400004,0xc7528000056fc291821c,0x978000e4600002d90517,0x40ec090c145e91000034,0x11ac6000196935557b06,0x8530f1ee3cc10c000515,0xa850000331e10b4e08c1,0xd2ab1f2f58e98cefae4c,0x2720000aab4546621,0x295b214e000168c40,0x30cc9104ee5a,0x804af8154a090c300800,0x8a5d0b72697e8b600020,0x6e27a9507d164a8e0000,0x89e2a238b94ac8000618,0xd7a604548ab00000084e,0x8b2f4000389371d10000,0x8951bb000160b9370e22,0x46e0e83eaaa701385078,0x8b04082a861c8000311b,0x5530001c4a4000772,0xb0d145a000000004ba00,0xae4b2b5000038e10001,0x5cd6463a214368000000,0xdcae8e00000990980b05],#[0x20001e38c8a1ad6d0001,0x5515684000000079684,0x102f000017fad,0x2c61c6f40000eeb0000,0x9a800000007c58000000,0x8a100000000238c00001,0x28ac8000b60c,0x42f0e5140000000000,0x486c80bf0d99a7d66a00,0xc0000451a9925ed80001,0x93b55c00000003441757,0xe3032f8032916126b67b,0xd5663f29056b89f235ea,0xa3c221102acb94000328,0x371b9d29139e2524,0x5a5f8eabbf2100004cfa,0x4ee4720d1239d6327d03,0x8e14b05d85127ce2928,0x195ec000000021beeb54,0x36cde90,0x24b00e5b24ac30523a80,0xd0000c46c0003052850d,0x95a1a200000000000210,0x97d540448e80000e452c,0x14a6601f256bc6e7b5b,0xd2b92a446ba63fc85822,0xeab20e46839000046288,0x911420000000017f6aac,0x126e0000402b115e1d,0xac970888000000099f00,0x6044d37800000000001,0x6af41656e95251d000],#[0xcc819fe8d7400000,0x300a0000000652f0000,0x190a0000000,0x0,0x20000000000000002278,0x3601789,0xa2e80003e132362824c0,0x40000735fc7e00000000,0xe3f8c196b28000486,0x285f7447290e5da00000,0x3164e0000b8cb0a92db8,0x7bc000032315e3,0x18238000257ef7dc0,0x9430e639348d222b1ae,0x9f800025f40000000000,0x69480000000f3c1cbaa8,0x810e0001d8380005367,0x86800001c40000000000,0xebe400060689b67b6f51,0x455158ab8e759d80000,0x6e800082f1a72b967000,0x31220000000101853,0x3000019e400014890000,0x49ad0001c1e000050c,0x3ea564632ef47600000,0xe30be0000000056ac481,0xc26d7700004340000659,0xe9f00004975000073720,0x18a7c00076b70000,0xf676733497e6bc000000,0x830f6705e,0xcd3a80000917e2e90000],#[0x5ae600000000000284,0x0,0xf64e6000000000000000,0x2a8000ac520003b71084,0xeaf618ec07f597f755d2,0x1eb7400000007627,0x4848000022cc000000,0x76f8eaeca36f2d071740,0xa2cbc79c00000a55056,0xc0000008581858000000,0xa91fab38000000000014,0xa360552523e3998,0x445be984000000,0x40c80004206630600000,0xf0001027b52e80000001,0x19000032660003b66ba3,0xb4db7e508e000000033,0xe90af1420065457dadac,0x1c580e0001c06c52d981,0x3c625570bd87f3818,0x1da0c0004e7f0000,0xa00000001218c000000,0x23b4000212d00010488f,0x41ac0003c310000,0x1189000025b,0x479b18e0000000000000,0x250b66a755000000000,0x72b40000000000,0xc19c00000002543a2c40,0x12855c918000e133,0x658000304c1410000000,0x322c00000005ac80003b],#[0xa87800000000000ed00,0x8fb5620001045c000000,0x82f80006a29000000024,0x54c00002852,0x70af0000000273f000,0x5a10000082b40,0xd19c22209135176b176,0x25a89193f60002c3b000,0x20940bb800000018827c,0xbcc13858705a80004dbf,0x30cc0000fb50000193,0x47e7c575e10a56944600,0xd222a000283b80000001,0x3554443c630bc0e18c,0x2b0a26d8cd0f02200000,0xc0000000000019f60000,0x8125f2314c00004d6516,0xc0abb7d687304c031195,0x300015a4000018f40000,0x52d111fe0002b7332b,0x2b800005144000045d00,0xc00008c9982e962c01b7,0xbd5c590000a4c4000030,0x7f1d0fecf8b0260003a,0xdc8b06839833432d3df3,0x55b40316900e84,0x210400011dfc0f600000,0x881dc6494f90001,0x0,0x2b2dd73c63634c983cc0,0x1e22c00000001576,0xd1fa4d020600012c00a8],#[0xe3c16053a2e000000004,0x352408174b8197b0000,0x50105422d3c52c000000,0x89fb2afdac60001ec4a8,0xb7248a41f4fa800023dd,0x1430008651c033d6f531,0x244c000000000009af2c,0x1e6560ad800072bc,0x2b63080602000378f800,0x151b9aaf637e0002a,0x40eb58ae014800044d0,0x8fbacfd4d60000000000,0x2920000409a000000015,0x8498065c00000001302,0xa380009dcaa1a7c39000,0x3c88d5c000000000003e,0x914f078f94cc27b0001,0x56000054cf9190000000,0x2b56030545eb54fc5bfc,0xb4c40003d018000a918,0x3e8000ed320000000000,0x49040003a11dadc00039,0x868000060cb1644,0x64bc00030aa800,0x6c104dd00003ddcf8440,0x2669bcb32f080000000,0x5a5900010560000000,0xebf80000001a0b40,0x874cce64dcb180000000,0x5abad10067bdf1acad,0x816d2730000651683980,0xe26e8c60000000043c2],#[0xc800090b80003cf8800,0xa2f0000000000018aa59,0xd0000cb9000000000001,0x10000f5604349f12f23,0x27990e4514d901140,0x3075800052f2,0x900000d3300000000000,0x8128000783e90f3b6214,0x3000067080000000422d,0x955af7b52a00034e2322,0xe9c718afc7f0000843f7,0x624f17a5666700003ab2,0xcc040002cb6caa,0xc67400078dd336800000,0x1c06bc06c3174469,0x5cfe920c0000000000,0x8f000000000001e2600,0xc0000000000044661b5c,0x9a800070e1820c0bf408,0x3cbf8f6a88900000002c,0x1,0x2a800000000000000000,0xd0380000000000000025,0xb191c433c05ce76a4e9,0x5b800064eec668000000,0x2e40000000532220c05,0xc0000c1ab83600000000,0x34800015e7fc05115119,0xad72b065ff399229d85,0xf0001e82c0005a56d26d,0x19ab33a0000284af26,0xb6fc82008a8ddc12c8c0],#[0x62bb69c000000005c5e,0xcc0bf00000003ad4800,0x346e000000000003c,0x2472,0x403e0000c4b000,0xf2680003065a26400000,0x1fa4ad88a11e581e,0x7a5155e400000006e0,0xc872cc6832a000046900,0xc0000f85789ca1f40001,0x1700000001cb0e742761,0xf5ec063000021f6ea06f,0xae04e668400000000000,0x5171c300000000000726,0x30600000000f002f8b54,0x1596775c8000062d,0x300000000000000,0x8cbc00076417d3c00000,0x300000000000000005e3,0x10500000000000359,0x96b0000387a6024e6c00,0x6b4483184d28203691de,0x36c2cd0001e631efdb5f,0x531177200000592b1a10,0xfedbc000083145f9dbfa,0x2fc28352600002560686,0x53190001abf72,0x4d5380003cfff275757c,0x9851d7b290c76b171d82,0x66bb999c1a7c5136428d,0x2000024e08f49a7f5606,0x77f24eb3ad466f57dce8],#[0x28c5d25c253c6a3c3,0xfb029745c00000000000,0x51ccbcc94600000004a5,0x873c000384e000000011,0x628a42074f1a0000a210,0x6a7d7e0000ccdc000133,0x586400020a371ef513c4,0xe0000a21213cad695bdc,0x870000000063910b3219,0x1c400045680001c5c59,0x28ae00008ea8000f635,0xcb764971ac000086f000,0x8bfeac48000f4aee83fc,0x5703104754a95055b274,0xa10957000000034a8760,0x271643a0000812f0820c,0x1a650001,0x630000c3b655ce136800,0x27,0x653400000000000,0x6f80f8a52707c0000000,0x7f7ad88000000042f50,0x97466859c0006a7a4280,0xcfca8834c60003113a8f,0x46a98678000c50449624,0x7b3a0fc4037b5df,0x3e80000000d058000000,0xc1400000000e32400008,0x0,0xed900001506800,0xf19c0000000000000000,0x1fb5400000000000],#[0x248700000000000000,0x1d5e0000f61f6a680,0x1a2e1af7c88f0000,0xf8a48000000000000000,0x4a49c3640000a,0x9f2680003175eadbe16e,0x236c860001254c000298,0x24414eec213629e00035,0x2f50e00010e3d8440001,0x7651c9000184a2018da1,0x7b320daca0cbc2425298,0x9e60084b80f500006890,0xd780000000434d6b0b63,0x4738000b5880002e,0x30b10000ed8e,0x2530639943bad4d800,0x27c0005964a5c400000,0x4a484000000000000001,0x19f7a2320003e47720,0x426cf5cd05d43400000,0x6a120c21400068340136,0x2d7972000177eb05860b,0x877b10b59fa000175d31,0xe507ea0ced2790d17373,0x1e4cfc52e7855383f65d,0x277214b08fdf9070653c,0x5235e57000000000183,0x19042d41658bb8000000,0x95fcc6161,0xdc1d36797f47905e0000,0x27000025b9e5ae54ed1c,0x26805ab1818e049e6],#[0x542fa81f242370d511ea,0x2164000522]]
set_option maxRecDepth 16000 in
def g251D10 := limbs80 #[#[0xd6458b76b12c17bdc940,0x221fe54110ff260886e,0x10fea82887f531443fcb,0x7ee62443f6b1221fd585,0xeba2217fdcd10bfae688,0xd510bfaea885ff74442f,0x985ff76442febb2217fd,0x3f6b12617fdc530ff2c0,0x758d30fba86987ee624c,0xec985ff744c2feba261f,0x503fcb02817fdd930bfa,0x17f5d940f7ac8a07bd43,0xfee6b06fd63582ffb8ac,0x73486ffba2c1bf59160b,0x2637fdd921bfeea90dff,0x1feac298ff5514c6ffb8,0xdd534c7f731263fb5893,0xba2637f5d131fbac698f,0x931bfeea98dfd754c6ff,0xdff70506ffbb2637f5d,0xf731283fb58941feac2a,0x55141bfee6a0fbd43507,0xaa0dfd75507deb2283ef,0x46ffbb2837f5d941bfee,0xfb58951feac2a8dff705,0xee8a8dff73547f7312a3,0x586ffbb2a37f5d951bf,0xc37fdcd61dfac6b0dff7,0xbfeeab0efd65586ffba2,0xf7158affb9ac57fdc562,0x1cc5fbdcd62fda86b17e,0x43bfee2a1dff7050ff6a],#[0xdfd7650fdeb2287f758d,0xfb8ac77fdc163bfeeca1,0xc564bfee0b25ff7458ef,0x887fd43442ffb9ac97fd,0x3feb9a21ff58d10ffaa6,0xf5d110ffac8887fd5444,0xec887fd75443feb2a21f,0x483fea8a41ff4c520ffa,0x1ff50530ffac6907fd61,0xfae2987fd614c3fea8a6,0x764c3feba261ff59130f,0xa81ff54540ffa62a07fd,0xffa62b07fd63503feb0,0xfd71583fea8ac1ff5056,0xb9ac1ff50d60ffee2b07,0x160ffae8b07ff73583fe,0xffd63487fea9a43ffdd,0xfea1263ff5c131ffaca9,0x55131ffae498ffd624c7,0xa98ffd744c7feb2263ff,0x7febb263ff5d531ffac,0xff5cd41ffac6a0ffd705,0xaeca0ffd75507feb2a83,0x2547fe992a3ff5c151ff,0xa3ff5c951ffac4a8ffd4,0xffae6a8ffd63547fea1a,0xd76547feba2a3ff59151,0x12c3ff4c961ffae0b0ff,0x61ffa86b0ffd72587fea,0x7fd75587feba2c3ff5cd,0xeb8a87ff5c143ffac6a1,0xc163ffae0b1ffd7650ff],#[0xb1fff7158ffeb8ac7ffd,0xffeba2c7ffdc963ffae4,0xf5c564ffae0b27ff7458,0x401e00450003feb9ac9f,0x97820706c0162042c0b,0x1583ed0e7c32d0bc42b5,0x5c60916ec55214104921,0x87c21dac71d1b846a519,0x98d24d88fa22d485e208,0x8e2cb8ad72a24a292748,0xc3354c873108c062f28b,0x3be8e9a38e8dec3654d2,0x5310fe42310473f30f75,0xa929c493921247591884,0x54d3516140a4e3d3384b,0x6c259d1626573d578548,0xf962ad84b5fad7945c65,0x6991a2867b19a7651d8,0x6fc1ba26d99b216b95aa,0x855dbe7579d1972c1c50,0x59fbf7d59f117b0de907,0xa1db865a136831206d80,0x3a68d8631c8b5e28988c,0xa96aa541931a44b8f8a,0x49f1a7669c1a69d99626,0xa7d29a6a4d28c2a21a81,0xe4ab68acb2adeaa66a39,0xc2cf4b20ac3daf9abbca,0xeeecba7ae59b80ad7eb4,0xc0c1cb024bf5af88bd0,0xa6c9631efc6cf177c45f,0x3d2f3465cf8738accab2],#[0xdaf7639d7d35afd58751,0x26b84cdffb7c2ddaf714,0x6fa44e7db99fe5478e8e,0xfc3cef97b97ed27aceea,0x2a2e1b0b83c0c100f001,0xc2e0f0215180d85c1e04,0xb0982418220247240c20,0x4c102202852213850804,0x810868091c80c8a4218,0x82844010638270a10c26,0x8046c310a92850984309,0x500430c491c05c2c1042,0x311c2a32143c10c24230,0xb014311c2e340f0b014,0x80e12118241c0070640f,0x30447081013090400c05,0x71b0c42a58180a83c242,0x4061c058210103014061,0x428d8c0be1b0b830a8,0x34190801807848460a03,0x300f0908c12146e1020,0x40701c24230500430c4b,0x4846090c4708101e0801,0x1303820440d0c4014078,0x81c24230438091012c2e,0x44b0b8181a182a30180a,0x42a444b0b8181a182e3,0x431217110602586c2e,0x54a0184b0b84c0e0a11,0xc0487c060be17030316,0x340090be1b0b810a8486,0x24384b0b848460b03034],#[0x430546c2e121182c0a18,0x41c184185491a6170781,0xe102182a385e0586c2e0,0x170781430549c2e0f020,0x8830c46850802e46076,0x20e0042040a03c240305,0x831a1206c2e13038284,0xd0a836120185c16061,0x60361707814260a11001,0x23844607617078183054,0xc16081b8446030141608,0x5019050c0b0404470300,0xc30d85c2223048009900,0x84c1600341306c0d0a48,0xe030b8206c0d0c442f0d,0x70143254884878278400,0x34052e4421041f156160,0x58042c04a1561606824,0x43110a148903813c3613,0xd0980c5585c260b0101,0x14008480e0917031c0d,0xb82458d02648602c1303,0x16005432340c84000c30,0xc0d04c0e0680e110b03c,0x300f84c16030c85098e1,0x580e13058081a185244,0xe1305804304c80f04c0e,0xf86c2e0c2c15180e30c2,0xf05b010bc14110c31202,0x85c682c0e02862385460,0x6340b11c882c0e028623,0x16008e16203101c102d0],#[0x2340e910803015070bc,0x5a182c47242c85c102e,0xd0a361a1b01c003b0420,0x8682c06018020901c142,0xc0342c2f05801b85880e,0x1c061782c021a0831340,0xc470b1022100782c050,0x24200344814070bc1601,0x60a86240c0380e111182,0x64a9384c1e003c1ac103,0x5c84107c551ac1c16028,0x1a20551ac1a0a0b01432,0x689038100586c010906,0x269200c840060f048b1a,0xc0701c260b0105430987,0x4c01050c1a24421e0d01,0x2304800f14420380c058,0x1221407010d70b84c1a,0x101e0309b0b84c060907,0xc401c6b85c260b00830f,0x9435c2e0d1782c02103,0x9120843d84c1e0304858,0x180f84c160306850f0e2,0xc101f180a03058c4101f,0x30591c101f1b0b814182,0xb13185c0a0e0c151d0a8,0x82e3e170283058203e30,0x10c054612a630b8141c1,0x2f05801c06080be1b0b8,0x80c142e0886280c0540c,0x83a068628062c0c61703,0xc222f0b81c0080318205],#[0x300082617038285c0d0,0xac2c2f0581c021830388,0x170306c22230437400d8,0x85c260b0106408dc981e,0xa2f0580832106c681e07,0x15144407010de0781c2,0x5e0b0031101185c1e044,0x581c020c40381406818,0x4c089070123854bc2c2f,0xa11002392180bc1b0a10,0x88011c90e4050b840860,0x405448180701c2043050,0x15302612424230483148,0xb104320e021014a7488,0x500890d0123854a0e85d,0x852260a8a871040f0a10,0x40860a11002392160820,0x90a26080a8910c050b8,0x29430404c40683284846,0xa04830b848e1e4242304,0xc8540906130b1d0b8641,0xf617068640c2e123a0f0,0x854bc2e050c8385c2464,0x4b0490c850b40d031223,0xb098281a6a1085131a17,0x184110d0d44902128061,0x412136160700c26090c8,0x284309828411c24587a2,0x28681854a1d20426864,0xc08f881044824a011617,0x10c121c3012046182f85,0x540a0e2a5e170981c142],#[0x54a1845c260d8124f0d8,0xd45c1b024d61b068540c,0x1b024f617068143454a0,0x1b61702834345481a878,0x30483832060044306f02,0x70a8d06098d05585c242,0x193508428a8c42a0c2c4,0x473034811a6130700c14,0x6818340309820f42068,0x41c230481238d0808215,0x83185c0a0c2a341c0c85,0x4c2e060d828420c68501,0x1703828420c68384a018,0x82c2e0c2b811a1188036,0x7100d85c1e042a2e1840,0x10230b8411c408c2e104,0x91029098a8908c2e1047,0x120a3110384820844060,0xe028b43220c82e1a070,0x2918601f898a82785414,0x22d084420228b1522014,0x62a45910e09a17001dc1,0xc1c2080a130580c2a1a0,0x4c16011629098a895004,0x870413c00c07038602c8,0x1a09e110b80151048c20,0xa150d84c16001a442438,0xc10410a44c15150e1e09,0x1c042d80c142e0847202,0x3016098a44a83110a880,0xb4070021c142e084720,0x43a1a0b0984a85110a88],#[0xf21d041614a184c222,0x660280c12204c1a15142,0x6808291688208c10420,0x64417010661b0688210d,0xf1a1506b068282a2e028,0xdc04228b150691026203,0x980c120e0a8b8d098e0,0xc0120a0d2601d010c619,0x494381807011b06b0982,0x703413c240507801510,0x983c16010d1a45c14547,0x30a8664869400e808810,0x4c39243a168086b048b1,0x1310210f06a0286c0108,0x11440410880c1220521e,0x8460e268f6160d0145a2,0x7910261e3d85c1c1a028,0x680a1088707c228b148,0x302c0c09b0a83c022f05,0x42e110782c0034884879,0x30580458a43c26243c13,0x5c260b00261c92200b21,0x50c8386420610878348,0x12c2a0b0215160f88c2e,0x4d0a8112888302c2030,0x185c0e0a16860c08880b,0xe1111821bc1900362c4,0x11821ba006c404b0b03c,0xc260b003622120601e11,0x30580408dc80f04d0a81,0x51b22c1488250e0601e1,0x2c6e881b0a1f1be060d8],#[0x8181e086e8b1b0d0d412,0xa106c408030844041b0b,0xa0e2310064122f05801b,0x11c4448810585c1e042,0x4022203c854185b050b1,0xc617038285a0c]]
set_option maxRecDepth 16000 in
def g251H10 := limbs80 #[#[0x4c01010000040e02400,0x8140040000c0301039,0x3802010160600405801,0x240b0502a080130342c,0x541a044020080000401,0xc1e094000240105000,0x7805000370380f19000,0x5019000050200304405,0x140100c001540002408,0xc080040d000000281b,0x18140140a0180200000,0x142000000000430e85d,0xb403014020640003433,0x1413000070942500018,0x681e02c060800005804,0xc1705c0a0342e0bc00,0x303b008020240002822,0xf022044010881b09c03,0x601c060c0100fc52,0x20180100a020000541e,0x9007064230001101c08,0x3478134140900c01403,0xb0040805c1f04800,0x24000f41a0284b01c07,0x200003c060980701001,0x28003e0010383d03808,0x12c04048290001705822,0x88000202a02c0000005,0x13009004a10100410008,0x103701011000030b800,0x900d09403104011184e,0x130010ec0d0002f03409],#[0xa84065c030a81f6d401,0x102460500900c6911c1f,0x848d469849d000001800,0xdf6a82423c5953448000,0x16cd40576c0e429975,0xa4f200006f37f0a00000,0x1da9614ab23c258ef85a,0x40400008269d3137b4ac,0xe5de44e1c15b7257cb9e,0x307491aa73e5d6e3e19,0x40c000383af53a0ac934,0x6073828cce3a8f5abf74,0xb0000d2fc5082eecf129,0x2c86fb2b210000cae90f,0x183eb6c7f41000025f6c,0x6059b6ca1873974cb8ba,0x7018676256c1c07bf48b,0x8cb40b3b7984afce20e1,0xd62c9ecaa0c499733244,0xc426d4ddf935fc000048,0x5031acfe1,0x4e56000104b5c326633,0xc6c000068853a682f800,0x4560000108f0000b0dac,0x218159800000000000,0xc6c51b213220ba422000,0xc81c4c91caf52b8e32c7,0x68000a6286765c7ff884,0x3aa8800dbf1d610037d6,0xb240ac3c000330b937e3,0x680005a82b516ca70000,0x284d23da4e401c000094],#[0x9106313371e0065d2128,0x97c1ba9dcdc654c39cb2,0x6dcb1a5ef08c9cc7c740,0x31788018071499723160,0x6c13505af4027cdc3029,0xd80006130751f81d420,0xc10a0000cb8e20822476,0x226e22d0d9f80007adb,0x9b9372b2bd000082dc00,0x41493c11c1deaca00003,0xe80970172e4336287060,0x25498000000000002d,0xf41c05840003adaf43a0,0x980006635f0b466f8b06,0x1ae31bbc7b7a48,0x504600024ec1043d1980,0xd408641bee22c0005061,0x2db914092a70040000f8,0xfb9ea17a40d525f73057,0xf043c0ab13706539d9b6,0x69c02e51056281fc3550,0x5836c8d95370000e,0xf0289c2a48c818ee2414,0xadd170412e73bc27598d,0x2339ea1f82b388feb7d6,0x18ac8138392620578000,0x25923ee9b4a134000080,0xb2c758e2872fe03b088d,0x77226fbbf738782dfaf8,0x30f9030e949f281515,0x1027e9d583f666893340,0x4ceaf540e0002eafc8ad],#[0x6b84256d3e4267ac9f8c,0xa1b25793157aa500000e,0x6330e34100f194d2978,0xab97420000f2a8f3bc00,0x3278685ab93a5e8b0be3,0xf7282c546a1a74372294,0x18b50ca782e96b7e47,0xbdcd2471959e28801cc0,0x53a78f120835b4e79c87,0x68716a31a401ae866d8a,0x1c7a6b74386293485334,0xfb1bbe0599810e7a31a2,0x98a09fc01fc083505518,0xa44800006e3ea21fde74,0x82b1d992288363e3b0c,0x527ca0c2a44b8d443c0f,0xa47545fc93d0000a1180,0x308d4c5306a01ac8cefc,0x4bc0001eef6a00ac670e,0x4c78753854800074932,0x1e879c9c800010f4197d,0x439cdc9904a4832b0d4d,0x81f61c916bdb91754a6a,0xc55c5b33e385f4ff22ed,0x903c4921e383e8c92dd6,0x522c0001532a02155036,0xe800094ff22b08e2fa48,0x4480002e8325bd0c13cc,0xd0f60003c72591da654c,0x9d26ff366fa3408c8000,0x79d25d80001454000030,0x4a7c0004200c2e54],#[0x14a7714a80002c640000,0x3f5295a1f56182e6afce,0x25b22bd7d913e6f147ea,0x100008466a9fae57d00a,0x20b852bc0000000205,0x28616663f195b2b1b2a0,0x8f0451584d1900006a9e,0x118093cdbcf31e00038e,0xd2d763afb6991f0458a0,0x7dd050a8e391c000595b,0x2cd21a4a3e00004ca751,0x966201f6d3400000000c,0x14850b614e59b901c1bc,0x24f82abef2a06072cc46,0x1e4705f245c408dd1dc2,0x7868fdcf0c728d509dd,0xa8000233333982aec00,0x557e890917c80004c536,0x60000864625ea805a0b4,0x75b44e5151e468e23b42,0x910585b8921ac29d009b,0x26993826e697090e21a9,0x81808a420dc302481a46,0xb2c9ab13031441e428cd,0x1041000004264b176674,0x7fe47e02b963f6c136d1,0x7cb203028c8f614a56d5,0x3d259a8b3cb868ae6807,0x167058ed01a7cbccd5,0x71e68aaa025823da364b,0xd0000341241466ebd969,0x150d0ccaeab06f014997],#[0x18b175294f6a284b5ee2,0xe0aef3338af9609993e,0x83eef2ed3dc214000393,0x918ba1c49129a9cf5d26,0xc2911a5c5a5371972a15,0x3e8936f2f135c8d690c3,0x6470a4ef4003e64d160a,0x5e8edc1f20556e4b0bf,0x434e4e8ea945c02a20b,0x34d346c04fec27b72910,0xae0b6c07a138c064d1b1,0x440000701e411234a72e,0xf3f0481084b103e43012,0x90000c10f5b72ceff45b,0x88d8bc8000d64a4bb954,0xa49b8139c68eea06621c,0xd80001136e9158ed80bb,0xbf60c30000c2ea9642c0,0xd0d5b158b4a000000012,0x7040433cac5c2ca409d,0xa1a4966e15f1a16b5613,0xc4b17020150000043c55,0x16a86da7600000338000,0x2d28c42741960002c1,0x60f947ac000623700000,0x9a28300017a300000000,0x3073d55e00012ab590,0x3296c6d645598e300000,0xd2863365e009ec869e72,0xa450d6000065e421c3b4,0x70a114a94b544bb6,0x9a64b25a387cc00050cd],#[0x72fa0bf2e70244d94a6f,0xb84a00025290d8d905cc,0x8a22c602e8998d7b10da,0x4921812501634b78c1f1,0x160a106c000045834,0x39942c2b0cbac0007b32,0xbf4e42a1fcba321dac6,0x21ee6a155533cfbe06aa,0x3e90629093af7453a0db,0x9c987968f862cfeab142,0x5893c1bf56932d6b4654,0xa2a4cf607f740b6de0ca,0x7414c562275c94000217,0x2a08c648492f2e83daee,0x4699590b3260eb6d7257,0x8d7424c8e924e875856e,0x833f18c7a67fb4f4,0x1fa3924052aa1cafa15d,0x65d00b147c3956c1446,0xf45a855a90d8121e35bd,0x768e8231155180004020,0x3b3a50007f1536d3a694,0x23a5484aa1259c01e0a8,0x3102422e6bc84ca8306b,0xb92ae955dae434654fa4,0x628ba9c7d45846c23b47,0x5190b442813747142144,0xa85800c1d7739be37b12,0x43c1e14c000146564f98,0x318e715425ee7858819,0x1225184f39cc000105,0xa27241ccc6efb0822040],#[0x620ca22a000088c64de,0x18a750925aa319906000,0x53f3b4c890801e5290b7,0x6193d4031849915a526b,0x3da2a8d2d7cd6a63593,0x641629a904f764100007,0xf0cb482ee00000000000,0xac44e265e360393713eb,0xb375d3f7945000041ed5,0xc11570001f37086e4066,0x2ea078e872a2ab86bd84,0x1a160c58901460655,0xd8aabb2ece1e9c36609f,0x4ac000101d00018c1d11,0x7456865212f7ee200000,0x62c7290767f01968000,0x15408c1908a1829f400,0x7478115000052d30000c,0x5caec617a00031658000,0xc590988000f4e0ec26ae,0x75a02a8809b7091b01f2,0x10000094a798dc1a0000,0x1dc186d8388e5e2023b5,0xc7408a5040600cc6028,0x4b8f9ae0cd27557809ec,0x3bef4e09bd35ca6754d5,0x13ee661006318a52834e,0x780005c2000000245328,0x25456318f40000e615cb,0x72b3ea3000075a1a52ee,0x47b2c912812e74450000,0x8a8cad40b5c6016b3cc8],#[0x4b6b54a8d320000962a9,0x629ea59f00000000316d,0x97f0421c36414c7fe8a,0x754b69d80d431ee0000e,0xd491f000184a36f50000,0xcde2d4217299bd64be9,0x4816a56ae,0x19ee300003c6098f6ebc,0xb40002703c4b7e3480a,0xa384000103f00014,0x826a5f3f4ca408b10000,0x7a6d603d3f1bd27729d1,0x33c9279ad889a31d29f2,0x7eeb265fecc98d89c081,0x1810bcf]]
def g251D11 := limbs80 #[#[0x30ff483fd10fb98bed62,0xfd31ff487fd60ff503fd,0xbfd32ff587fd51ff507,0xf593fd63ff50ffd62ff5,0x5f09f0f01741b01b000f,0x1b73385d4a7127200384,0x838106151a3b4307c4e9,0x126160c0a04185c60285,0x2c610868483008285080,0x82810308261a160e0424,0xa160e045471286858400,0x4838108820600205c0a1,0x26180a160c042c207858,0xc9078685848280030113,0xa245a1a14120e0a00042,0x4907868483828005011,0x8181c7a16120e020818,0x60e04302068685810b0a,0x985838102060b081e1a1,0x20621a1606002e080c10,0x81090785848281800306,0x82160e0602082c1]]
def g251H11 := limbs80 #[#[0xa6849a00008800a20080,0x4850c2408002002020,0x13880e60300688c4822a,0x8800a04503306cc810ea,0x1a039403b000c0035830,0xaa1640767ba0a8254401,0x210c1d5a7be0dbd3,0x5f2710ca208d440a41b7,0x55c51ac50154000824b4,0x2c17b0fb5248a6e3f8,0x21457b53b825a8dd3660,0x2d7930951a8c620c1d3,0xb6400030f342d0cd777,0x46b980fbec0eb32d8e9f,0xc000979a15925d4df06,0x37f97d9240000006244a,0x230ca17b9d48bc83b6,0xa5d0000003d346470000,0xda94c7e49389562c7147,0x76ac540e94c864000e05,0x361c5d5b31121e8c8468,0x72339e2a58c600930920,0x3f0187d4d26000061135,0x186c00071a4ad9f851,0x925d2bf8e776e2200000,0x3466025617601596c691,0x862b90a1acec98b4124c,0x8d55600052d800000141,0x70f22ca80c0e60a00029,0x20e4499c16d574001d,0x6aaf5c3a89d1f4b40000,0xc25495c52de9c00010d6],#[0x4e3ae26800311353443f,0x2834000000000384,0x40cb0fc6000394800000,0x1c80028ad46a00072758,0x838a46916017c000000d,0x22820d00017a5a538000,0x80000006b4fa000002a1,0xbb17939937a29101084,0xf4a060000003ad6aae00,0xf964218b13172727f1,0xf3d53c5ed33e1600000,0x8a038d68e177e4344,0x4d2c01269f286906e870,0xdad0b21a3b086c1370a,0xc8001129826c08114800,0x6f795d0b000301998d33,0x119dfc8ec46242ca2c8d,0x33c11d3d000101e0008,0x73c20c181dda40be0002,0xd91b800600e540908000,0xd021724a4940000003d8,0x7f84e68a34f000186dc6,0x8700000038b823b00068,0x1727c]]
def g251D12 (j : Nat) := if j=0 then 0x305080c101003ff else 0
def g251H12 := limbs80 #[#[0x150,0x2060000045000000000,0x107001a4b0e002900,0x7d14680102a0c0,0x113800820000,0x4d22000005131fe63a00,0x38415801a58017,0x7826]]
def g251L : Nat → Packing
  | 6 => (29,6,7,0,0,9,0,g251D6)
  | 7 => (294,5,7,0,0,13,0,g251D7)
  | 8 => (824,4,7,0,0,16,0,g251D8)
  | 9 => (820,3,7,0,0,16,0,g251D9)
  | 10 => (186,2,7,0,0,14,0,g251D10)
  | 11 => (18,1,7,0,0,11,0,g251D11)
  | 12 => (1,0,7,0,0,0,0,g251D12)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 9 47 6 10 5 1 g251H7
  | 8 => lookupWord 94 521 6 14 9 1 g251H8
  | 9 => lookupWord 276 1777 6 15 10 1 g251H9
  | 10 => lookupWord 274 1259 10 15 10 1 g251H10
  | 11 => lookupWord 61 307 7 13 8 1 g251H11
  | 12 => lookupWord 5 59 3 10 5 1 g251H12
  | _ => fun _ => none
def g251 : Forest := ⟨251,12,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 29=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 29=true := g251P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 18=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_18 : block g251 7 18 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_114 : block g251 7 114 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_210 : block g251 7 210 84=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 294=true := (@block_merge g251 7 0 114 180 (@block_merge g251 7 0 18 96 g251P7_0 g251P7_18) (@block_merge g251 7 114 96 84 g251P7_114 g251P7_210))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 76=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_76 : block g251 8 76 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_172 : block g251 8 172 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_268 : block g251 8 268 70=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_338 : block g251 8 338 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_434 : block g251 8 434 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_530 : block g251 8 530 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_626 : block g251 8 626 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_722 : block g251 8 722 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_818 : block g251 8 818 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 824=true := (@block_merge g251 8 0 434 390 (@block_merge g251 8 0 172 262 (@block_merge g251 8 0 76 96 g251P8_0 g251P8_76) (@block_merge g251 8 172 96 166 g251P8_172 (@block_merge g251 8 268 70 96 g251P8_268 g251P8_338))) (@block_merge g251 8 434 192 198 (@block_merge g251 8 434 96 96 g251P8_434 g251P8_530) (@block_merge g251 8 626 96 102 g251P8_626 (@block_merge g251 8 722 96 6 g251P8_722 g251P8_818))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_11 : block g251 9 11 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_107 : block g251 9 107 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_203 : block g251 9 203 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_299 : block g251 9 299 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_395 : block g251 9 395 50=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_445 : block g251 9 445 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_541 : block g251 9 541 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_637 : block g251 9 637 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_733 : block g251 9 733 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_765 : block g251 9 765 55=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 820=true := (@block_merge g251 9 0 395 425 (@block_merge g251 9 0 107 288 (@block_merge g251 9 0 11 96 g251P9_0 g251P9_11) (@block_merge g251 9 107 96 192 g251P9_107 (@block_merge g251 9 203 96 96 g251P9_203 g251P9_299))) (@block_merge g251 9 395 242 183 (@block_merge g251 9 395 50 192 g251P9_395 (@block_merge g251 9 445 96 96 g251P9_445 g251P9_541)) (@block_merge g251 9 637 96 87 g251P9_637 (@block_merge g251 9 733 32 55 g251P9_733 g251P9_765))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_3 : block g251 10 3 95=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_98 : block g251 10 98 88=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 186=true := (@block_merge g251 10 0 3 183 g251P10_0 (@block_merge g251 10 3 95 88 g251P10_3 g251P10_98))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_2 : block g251 11 2 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 18=true := (@block_merge g251 11 0 2 16 g251P11_0 g251P11_2)
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
  · exact (rfl : block g251 5 0 0 = true)
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
  · exact g251B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 13 := lower_forest (g:=g251) (i:=0) (hints:=16777283) (before_sound K250 V250) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K250 13 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V250 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 13 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K251 V251) (4, 0, 251, 0, 13) (by decide +kernel) (by decide +kernel)

theorem replacementMargin 
    (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length+1 ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  have lower := g255R
  by_cases big : 16 ≤ gates.length+1
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

end PEqualNP.Outside.L_meta_34876
