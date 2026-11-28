import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52012.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52012
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffafffffffeffffffee,0xfffefffefefeeca0ffff,0xffffffffffffffffffff,0xfffffffafffffffeffff,0xffeefffefffefefeeca0]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,6]⟩,⟨.or,[4,7]⟩,⟨.or,[0,3]⟩,⟨.or,[0,6]⟩,⟨.or,[3,4]⟩,⟨.or,[8,12]⟩,⟨.or,[1,7]⟩,⟨.or,[0,5]⟩,⟨.or,[9,15]⟩,⟨.and,[14,13]⟩,⟨.and,[8,10]⟩,⟨.and,[16,2]⟩,⟨.and,[9,11]⟩,⟨.or,[17,18]⟩,⟨.or,[21,19]⟩,⟨.or,[22,20]⟩], 23⟩

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
    (lower : Impossible true graph 13 sevenInputs.toFinset) (gates : List Gate) (o : Nat) (hsize : gates.length ≠ 15)
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
def K21 := extendKnown [] 4 [(21,[]),(37,[84]),(42,[16,50,84]),(74,[16,50,100,84]),(133,[116,84,101]),(145,[66,50,115,83,101]),(148,[32,16,65,49,115,83,101]),(168,[48,16,82,116,100]),(200,[48,16,98,116,82,84]),(208,[64,16,98,49,115,82,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V21 : Known true K21 := extend_ok (m:=21) baseKnown low21 (by decide +kernel)
def g23Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g23C : List ColumnInfo := [(2,0,21,0,4)]
def g23A : List (List Nat) := [[],[32]]
def g23D4 (j : Nat) := if j=0 then 0x1f else 0
def g23L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g23D4)
  | _ => emptyPacking
def g23I (_ _ : Nat) : Option (Nat × Nat) := none
def g23 : Forest := ⟨23,4,fun i => g23Y[i]?.getD (0,0),g23C,g23A,g23L,g23I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23P4_0 : block g23 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g23B4 : block g23 4 0 1=true := g23P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23T : checkedTables g23 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g23 0 0 0 = true)
  · exact (rfl : block g23 1 0 0 = true)
  · exact (rfl : block g23 2 0 0 = true)
  · exact (rfl : block g23 3 0 0 = true)
  · exact g23B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23G : graphValid g23 (boundsBefore K21) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low23 : Lower true (varsX 23) (graphGoal 23) 5 := lower_forest (g:=g23) (i:=0) (hints:=66) (before_sound K21 V21) g23G g23T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K23 := extendKnown K21 5 [(23,[]),(39,[84]),(43,[16,50,84]),(45,[49,84]),(46,[16,32,48,84]),(58,[48,65,82]),(75,[16,50,100,84]),(86,[16,32,96,48,83]),(101,[32,97,80,49,64,67]),(113,[64,81,98,49,50]),(114,[64,81,98,48,49,50]),(184,[48,65,82,113,33,98]),(228,[32,97,80,48,116,49]),(240,[64,81,98,48,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V23 : Known true K23 := extend_ok (m:=23) V21 low23 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2fc38ff01fff1ff02,0xfc38ff01fff1ff02fc38])),(BitVec.ofNat 152 (word80 [0x42ccdb2a5451240242,0xccdb2a5451240242ccdb]))),((BitVec.ofNat 152 (word80 [0xfdcbc7fffe07fe3ffd,0xcbc7fffe07fe3ffdcbc7])),(BitVec.ofNat 152 (word80 [0x1448490c1860408414,0x48490c18604084144849]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b06085892808,0xa7b6b06085892808a7b6]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x893124c08106003089,0x3124c081060030893124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[48,65]]
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
theorem g27G : graphValid g27 (boundsBefore K23) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=4148) (before_sound K23 V23) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K23 4 [(27,[]),(30,[32]),(57,[48,16,33,66,82]),(60,[48,33,16,65,81]),(92,[32,97,81]),(108,[32,49,97,84,65]),(116,[80,65,32,99,33]),(120,[64,49,32,81,98]),(139,[49,116,84,101]),(142,[16,112,32,50,67,84,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V23 low27 (by decide +kernel)
def g53Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf3e58e3ffc1ffcff3e,0x58e3ffc1ffcff3e58e3f])),(BitVec.ofNat 152 (word80 [0x200012490842080200,0x1249084208020001249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfcfa71c7ffe0ff3fcf,0xa71c7ffe0ff3fcfa71c7])),(BitVec.ofNat 152 (word80 [0x400024921084100400,0x2492108410040002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0e81f8ffff003ff0,0xe81f8ffff003ff0e81f8])),(BitVec.ofNat 152 (word80 [0x804ec924a108a2a804,0xec924a108a2a804ec924]))),((BitVec.ofNat 152 (word80 [0x19fe00ffffffc001,0x9fe00ffffffc0019fe00])),(BitVec.ofNat 152 (word80 [0xa99c924c210c030a9,0x9c924c210c030a99c924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g53C : List ColumnInfo := [(16,0,37,0,4)]
def g53A : List (List Nat) := [[],[84],[32],[32,84]]
def g53D4 (j : Nat) := if j=0 then 0x1f else 0
def g53L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g53D4)
  | _ => emptyPacking
def g53I (_ _ : Nat) : Option (Nat × Nat) := none
def g53 : Forest := ⟨53,4,fun i => g53Y[i]?.getD (0,0),g53C,g53A,g53L,g53I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P4_0 : block g53 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g53B4 : block g53 4 0 1=true := g53P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53T : checkedTables g53 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g53 0 0 0 = true)
  · exact (rfl : block g53 1 0 0 = true)
  · exact (rfl : block g53 2 0 0 = true)
  · exact (rfl : block g53 3 0 0 = true)
  · exact g53B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53G : graphValid g53 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low53 : Lower true (varsX 53) (graphGoal 53) 5 := lower_forest (g:=g53) (i:=0) (hints:=2) (before_sound K27 V27) g53G g53T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K53 := extendKnown K27 5 [(53,[]),(83,[64,33,97,81]),(85,[66,101]),(90,[16,98,50,67,84]),(106,[16,50,84,100]),(170,[48,16,82,33,65,116,100]),(180,[32,16,113,49,99]),(202,[48,16,98,33,65,117]),(216,[96,16,114,49,67,84,82]),(232,[48,16,114,84,100,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V53 : Known true K53 := extend_ok (m:=53) V27 low53 (by decide +kernel)
def g149Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g149C : List ColumnInfo := [(1,0,148,0,4),(4,0,145,0,4),(16,0,133,0,4),(128,0,21,0,4)]
def g149A : List (List Nat) := [[],[116],[66],[66,114],[114,66],[114],[32],[32,116],[32,64],[32,64,112],[32,112,64],[32,112],[64,32],[64,32,114],[64],[64,112],[64,114],[64,114,32],[112,32,66],[112,32],[112,64],[112],[112,66,32],[112,66]]
def g149D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g149D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g149H4 (j : Nat) := if j=0 then 0x34f else 0
def g149D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g149H5 := limbs80 #[#[0x215044c0000063c0002,0xd20008a0,0x3700]]
def g149D6 (j : Nat) := if j=0 then 0x3904f else 0
def g149H6 := limbs80 #[#[0xa8000880000003038800,0x1d00000054000000001]]
def g149L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g149D3)
  | 4 => (3,2,2,0,0,5,0,g149D4)
  | 5 => (1,1,2,0,0,0,0,g149D5)
  | 6 => (1,0,2,0,0,0,0,g149D6)
  | _ => emptyPacking
def g149I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g149H4
  | 5 => lookupWord 2 23 2 9 2 3 g149H5
  | 6 => lookupWord 1 17 0 9 0 5 g149H6
  | _ => fun _ => none
def g149 : Forest := ⟨149,6,fun i => g149Y[i]?.getD (0,0),g149C,g149A,g149L,g149I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g149P3_0 : block g149 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g149B3 : block g149 3 0 2=true := g149P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g149P4_0 : block g149 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g149B4 : block g149 4 0 3=true := g149P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g149P5_0 : block g149 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g149B5 : block g149 5 0 1=true := g149P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g149P6_0 : block g149 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g149B6 : block g149 6 0 1=true := g149P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g149T : checkedTables g149 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g149 0 0 0 = true)
  · exact (rfl : block g149 1 0 0 = true)
  · exact (rfl : block g149 2 0 0 = true)
  · exact g149B3
  · exact g149B4
  · exact g149B5
  · exact g149B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g149G : graphValid g149 (boundsBefore K53) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low149 : Lower true (varsX 149) (graphGoal 149) 7 := lower_forest (g:=g149) (i:=0) (hints:=2) (before_sound K53 V53) g149G g149T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K149 := extendKnown K53 7 [(149,[]),(165,[84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V149 : Known true K149 := extend_ok (m:=149) V53 low149 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,8,21,2,5),(8,0,23,0,5),(1,0,30,0,4),(2,8,21,0,4),(4,0,27,0,4)]
def g31A : List (List Nat) := [[],[32]]
def g31D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g31D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g31H5 (j : Nat) := if j=0 then 0x1 else 0
def g31D6 (j : Nat) := if j=0 then 0x18989f else 0
def g31H6 := limbs80 #[#[0x200000000000000a9b58,0x357]]
def g31L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g31D4)
  | 5 => (3,1,3,0,0,5,0,g31D5)
  | 6 => (1,0,3,0,0,0,0,g31D6)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g31H5
  | 6 => lookupWord 1 19 0 7 2 1 g31H6
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P4_0 : block g31 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B4 : block g31 4 0 1=true := g31P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 3=true := g31P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B6 : block g31 6 0 1=true := g31P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
  · exact g31B5
  · exact g31B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K149) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 7 := lower_forest (g:=g31) (i:=0) (hints:=4146) (before_sound K149 V149) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K149 7 [(31,[]),(79,[16,50,100,84]),(143,[49,116,84,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V149 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(1,0,46,0,5),(2,0,45,0,5),(4,0,43,0,5),(8,0,39,0,5),(5,0,42,0,4),(10,0,37,0,4)]
def g47A : List (List Nat) := [[],[49],[16,50],[16,32,48],[32],[32,49],[48,16,33],[48,33]]
def g47D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g47D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g47H5 := limbs80 #[#[0x690000800100000200,0x2800]]
def g47D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g47H6 := limbs80 #[#[0x84000000000fc7000002,0x2505003140000030800f,0x2935,0x3c67440000281164000,0x2000000c000000c5c000,0x3844]]
def g47D7 (j : Nat) := if j=0 then 0x1605f else 0
def g47H7 := limbs80 #[#[0xba374f00000000e4d30f,0x87b4c4f50030599003c]]
def g47L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g47D4)
  | 5 => (10,2,3,0,0,7,0,g47D5)
  | 6 => (3,1,3,0,0,6,0,g47D6)
  | 7 => (1,0,3,0,0,0,0,g47D7)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 8 2 2 g47H5
  | 6 => lookupWord 4 41 1 10 4 2 g47H6
  | 7 => lookupWord 3 17 2 9 2 3 g47H7
  | _ => fun _ => none
def g47 : Forest := ⟨47,7,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4_0 : block g47 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B4 : block g47 4 0 3=true := g47P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5_0 : block g47 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5_1 : block g47 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B5 : block g47 5 0 10=true := (@block_merge g47 5 0 1 9 g47P5_0 g47P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6_0 : block g47 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B6 : block g47 6 0 3=true := g47P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P7_0 : block g47 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B7 : block g47 7 0 1=true := g47P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
  · exact g47B5
  · exact g47B6
  · exact g47B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 8 := lower_forest (g:=g47) (i:=0) (hints:=4146) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 8 [(47,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc03fe1fe1fff00f,0xf87f87ffff856420703f])),(BitVec.ofNat 152 (word80 [0x50282814404400a0a0,0x51011002098064049249]))),((BitVec.ofNat 152 (word80 [0x7fffc001ffe1ffff0,0x7ff87f01c9c9c381c0])),(BitVec.ofNat 152 (word80 [0x60b03058828042c0c1,0x620a01042181c98db6db]))),((BitVec.ofNat 152 (word80 [0x7ffffffe0001fffff,0xff80007ff233d69c0e07])),(BitVec.ofNat 152 (word80 [0x80c040600308830101,0x800c2208021380892492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf800000000001fffff,0xffffff80013c2ae00ff8])),(BitVec.ofNat 152 (word80 [0x50282811411140a0a,0x500050402c02724924]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0xce2917ff000])),(BitVec.ofNat 152 (word80 [0x60303001800180c0c,0x4604460846010724924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(2,0,53,0,5)]
def g55A : List (List Nat) := [[],[84],[32],[32,84]]
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
theorem g55G : graphValid g55 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 6 := lower_forest (g:=g55) (i:=0) (hints:=66) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 6 [(55,[]),(107,[16,50,84,100]),(115,[64,81,98,50]),(179,[114,50,99]),(182,[32,112,48,99]),(186,[48,65,82,114,98]),(227,[114,50,84,100,67]),(242,[64,81,98,48,49,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff003fe1ff0fffc01f,0xfff0fff0d97f0000f0f0])),(BitVec.ofNat 152 (word80 [0x2a0a814412200a8541,0x41220022993600333333]))),((BitVec.ofNat 152 (word80 [0xffffc001fff0ffffe0,0x1fff0fff3c14bb0f0f0f])),(BitVec.ofNat 152 (word80 [0xc0301880402030181,0x80402040180413111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb02c0a0058442c0602,0x5844280213164666666]))),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b02c116088b02814,0x16000b040249e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc030018000c03018,0x18088c08468880888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(1,0,58,0,5)]
def g59A : List (List Nat) := [[],[64,81]]
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
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 6 := lower_forest (g:=g59) (i:=0) (hints:=4148) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 6 [(59,[]),(62,[32]),(103,[16,50,100]),(109,[48,16,33,100]),(118,[32,99,84]),(121,[48,16,33,66,82,98]),(155,[16,112,48,67,84,101]),(158,[16,112,32,50,67,84,101]),(230,[16,112,32,50,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fc3ff0fffc03f,0xfff0fffff1de0200f0ff])),(BitVec.ofNat 152 (word80 [0x120900881220048480,0x81220020908602111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff8003fff0ffffc0,0x3fff0fff2435bb0f0f0f])),(BitVec.ofNat 152 (word80 [0x240205102402090105,0x2402040203111222222]))),((BitVec.ofNat 152 (word80 [0xfffffffc0000ffffff,0xc0000ff01bb564f00000])),(BitVec.ofNat 152 (word80 [0xb82c1600b8442e0606,0xb84428219b560777777]))),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b05822c088b02828,0x2c000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060030000c03030,0x30088c08460884888888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(0,8,21,32,5),(8,0,53,0,5),(16,0,45,0,5),(1,0,60,0,4),(4,0,57,0,4),(32,8,21,0,4)]
def g61A : List (List Nat) := [[],[32]]
def g61D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g61D5 (j : Nat) := if j=0 then 0xc8404fd10 else 0
def g61H5 (j : Nat) := if j=0 then 0x1 else 0
def g61D6 (j : Nat) := if j=0 then 0x232a8bf else 0
def g61H6 (j : Nat) := if j=0 then 0xb else 0
def g61L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g61D4)
  | 5 => (1,1,3,0,0,0,0,g61D5)
  | 6 => (1,0,3,0,0,0,0,g61D6)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g61H5
  | 6 => lookupWord 1 2 0 4 0 0 g61H6
  | _ => fun _ => none
def g61 : Forest := ⟨61,6,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4_0 : block g61 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B4 : block g61 4 0 1=true := g61P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : block g61 5 0 1=true := g61P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_0 : block g61 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B6 : block g61 6 0 1=true := g61P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact g61B4
  · exact g61B5
  · exact g61B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 7 := lower_forest (g:=g61) (i:=0) (hints:=20482) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 7 [(61,[]),(93,[66,101]),(94,[16,98,50,67,84]),(110,[16,50,100]),(206,[48,16,98,33,65,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff01fffe3ffc03f,0xe1fe1fffb19d500f00ff])),(BitVec.ofNat 152 (word80 [0x1440a1414048028281,0x44044008218911111111]))),((BitVec.ofNat 152 (word80 [0x1fffe01ffc7fffc0,0x1ffe1fc6d3a20f00f00])),(BitVec.ofNat 152 (word80 [0x5882c18582810b0305,0x882804112d3823333333]))),((BitVec.ofNat 152 (word80 [0x1fffffe0007fffff,0xfe0001ff9e1bc000f00f])),(BitVec.ofNat 152 (word80 [0x6113020613124c2426,0x13089201e12caaaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800404080400100808,0x400040000004444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x1808101800603030,0x118111824046c8888888]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := [(1,0,86,0,5),(2,0,85,0,5),(4,0,83,0,5),(64,0,23,0,5)]
def g87A : List (List Nat) := [[],[96,33]]
def g87D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g87L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g87D6)
  | _ => emptyPacking
def g87I (_ _ : Nat) : Option (Nat × Nat) := none
def g87 : Forest := ⟨87,6,fun i => g87Y[i]?.getD (0,0),g87C,g87A,g87L,g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P6_0 : block g87 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g87B6 : block g87 6 0 1=true := g87P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g87 0 0 0 = true)
  · exact (rfl : block g87 1 0 0 = true)
  · exact (rfl : block g87 2 0 0 = true)
  · exact (rfl : block g87 3 0 0 = true)
  · exact (rfl : block g87 4 0 0 = true)
  · exact (rfl : block g87 5 0 0 = true)
  · exact g87B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 7 := lower_forest (g:=g87) (i:=0) (hints:=66) (before_sound K61 V61) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K61 7 [(87,[]),(91,[16,50,100]),(117,[64,81,98,49]),(122,[48,65,82]),(171,[48,16,33,84,118]),(174,[112,48,84,99]),(185,[49,66,114,82,101]),(188,[32,49,64,16,113,81,101]),(203,[48,16,33,100,84,117]),(205,[96,33,49,116,84]),(214,[112,48,83]),(220,[96,33,49,16,116,81,84]),(236,[48,33,97,116,81]),(244,[64,81,98,48,115]),(248,[48,65,82,113,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V61 low87 (by decide +kernel)
def g124Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0)]
def g124C : List ColumnInfo := [(4,0,120,0,4),(8,0,116,0,4),(16,0,108,0,4),(32,0,92,0,4),(64,0,60,0,4)]
def g124A : List (List Nat) := [[],[99,84],[50,100],[50,66,82,98],[66,101],[66,83,98,50],[82,67],[82,99,66,67],[98,50,67,84],[98,83]]
def g124D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g124D5 (j : Nat) := if j=0 then 0xc1a0fd20fd10 else 0
def g124H5 (j : Nat) := if j=0 then 0x2 else 0
def g124D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g124H6 := limbs80 #[#[0xb600000000810000,0xd2007e23e5,0xaa000000009ba7000000,0x8000]]
def g124L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g124D4)
  | 5 => (2,1,3,0,0,4,0,g124D5)
  | 6 => (1,0,3,0,0,0,0,g124D6)
  | _ => emptyPacking
def g124I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g124H5
  | 6 => lookupWord 2 37 0 8 1 3 g124H6
  | _ => fun _ => none
def g124 : Forest := ⟨124,6,fun i => g124Y[i]?.getD (0,0),g124C,g124A,g124L,g124I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P4_0 : block g124 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g124B4 : block g124 4 0 1=true := g124P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P5_0 : block g124 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g124B5 : block g124 5 0 2=true := g124P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P6_0 : block g124 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g124B6 : block g124 6 0 1=true := g124P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124T : checkedTables g124 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g124 0 0 0 = true)
  · exact (rfl : block g124 1 0 0 = true)
  · exact (rfl : block g124 2 0 0 = true)
  · exact (rfl : block g124 3 0 0 = true)
  · exact g124B4
  · exact g124B5
  · exact g124B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124G : graphValid g124 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low124 : Lower true (varsX 124) (graphGoal 124) 7 := lower_forest (g:=g124) (i:=0) (hints:=52581376) (before_sound K87 V87) g124G g124T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K124 := extendKnown K87 7 [(124,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V124 : Known true K124 := extend_ok (m:=124) V87 low124 (by decide +kernel)
def g151Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff01ff1ffffc03f,0xe1fe1fffd19d300f00ff])),(BitVec.ofNat 152 (word80 [0x1440a140a408028281,0x44044008018931111111]))),((BitVec.ofNat 152 (word80 [0x1fffe001fc7fffc0,0x1ffe1fc4d3aa0000f00])),(BitVec.ofNat 152 (word80 [0x5892c192c8514b2325,0x892805114d3aabbbbbbb]))),((BitVec.ofNat 152 (word80 [0x1ffffffe007fffff,0xfe0001ffbe1b40f0f00f])),(BitVec.ofNat 152 (word80 [0x6103020300620c0406,0x3088203e1002222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800404040080100808,0x400040000004444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x1808180100603030,0x118111824046c8888888]))),(0x0,0x0)]
def g151C : List ColumnInfo := [(2,0,149,0,7)]
def g151A : List (List Nat) := [[],[114],[32],[32,112],[112,32],[112]]
def g151D7 (j : Nat) := if j=0 then 0x3f else 0
def g151L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g151D7)
  | _ => emptyPacking
def g151I (_ _ : Nat) : Option (Nat × Nat) := none
def g151 : Forest := ⟨151,7,fun i => g151Y[i]?.getD (0,0),g151C,g151A,g151L,g151I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151P7_0 : block g151 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g151B7 : block g151 7 0 1=true := g151P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151T : checkedTables g151 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g151 0 0 0 = true)
  · exact (rfl : block g151 1 0 0 = true)
  · exact (rfl : block g151 2 0 0 = true)
  · exact (rfl : block g151 3 0 0 = true)
  · exact (rfl : block g151 4 0 0 = true)
  · exact (rfl : block g151 5 0 0 = true)
  · exact (rfl : block g151 6 0 0 = true)
  · exact g151B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151G : graphValid g151 (boundsBefore K124) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 8 := lower_forest (g:=g151) (i:=0) (hints:=66) (before_sound K124 V124) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K124 8 [(157,[49,116]),(167,[84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V151 : Known true K151 := extend_ok (m:=151) V124 low151 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fc7f8ffe0,0x3f8ff1ffcee5000f00ff])),(BitVec.ofNat 152 (word80 [0x121221224090920244,0x812124020ea411111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fffe007ff1fff,0xc00ffe3fe56b00f00f0f])),(BitVec.ofNat 152 (word80 [0x242442408521204481,0xa424084214b22222222]))),((BitVec.ofNat 152 (word80 [0xffffff8001fff,0xfff0003f39f00f00f000])),(BitVec.ofNat 152 (word80 [0x383883830601c48706,0xc038908b9f033333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040802000808,0x10040010000044444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081004001010,0x20080020000088888888]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(8,0,165,0,7)]
def g173A : List (List Nat) := [[],[117],[32],[32,117]]
def g173D7 (j : Nat) := if j=0 then 0x3f else 0
def g173L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g173D7)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,7,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P7_0 : block g173 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B7 : block g173 7 0 1=true := g173P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : checkedTables g173 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact (rfl : block g173 4 0 0 = true)
  · exact (rfl : block g173 5 0 0 = true)
  · exact (rfl : block g173 6 0 0 = true)
  · exact g173B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K151) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 8 := lower_forest (g:=g173) (i:=0) (hints:=20482) (before_sound K151 V151) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K151 8 [(173,[]),(217,[66,101]),(229,[32,80,99,67]),(241,[64,98,83,32,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V151 low173 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe03f9fc07f3f8ffc,0xfff9ff3e70000f0f0ff])),(BitVec.ofNat 152 (word80 [0x204081008102010008,0x20810020000111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc01fff803ff1ff,0xf03fe7fce0e00f0f0f0f])),(BitVec.ofNat 152 (word80 [0x408102010204020010,0x41020040000222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf000001fffffc001ff,0xffc007ff1d60f0000ff0])),(BitVec.ofNat 152 (word80 [0x850a144a14281424a0,0x821452805d6444444444]))),((BitVec.ofNat 152 (word80 [0xffffffe000000001ff,0xfffff8000bbf000ff000])),(BitVec.ofNat 152 (word80 [0x60c180c18309848c1,0x418030a8bb444444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x181ffff00000])),(BitVec.ofNat 152 (word80 [0x81020102040200102,0x8200400000888888888]))),(0x0,0x0)]
def g181C : List ColumnInfo := [(16,0,165,0,7)]
def g181A : List (List Nat) := [[],[84],[114],[114,84],[32],[32,84],[32,112],[32,112,84],[112,32],[112,32,84],[112],[112,84]]
def g181D7 (j : Nat) := if j=0 then 0x3f else 0
def g181L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g181D7)
  | _ => emptyPacking
def g181I (_ _ : Nat) : Option (Nat × Nat) := none
def g181 : Forest := ⟨181,7,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P7_0 : block g181 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B7 : block g181 7 0 1=true := g181P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : checkedTables g181 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0 = true)
  · exact (rfl : block g181 1 0 0 = true)
  · exact (rfl : block g181 2 0 0 = true)
  · exact (rfl : block g181 3 0 0 = true)
  · exact (rfl : block g181 4 0 0 = true)
  · exact (rfl : block g181 5 0 0 = true)
  · exact (rfl : block g181 6 0 0 = true)
  · exact g181B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 8 := lower_forest (g:=g181) (i:=0) (hints:=2) (before_sound K173 V173) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K173 8 [(181,[]),(213,[66,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V173 low181 (by decide +kernel)
def g218Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe1fe03f8fe3fc07,0xf87f87fffcc7950001ff])),(BitVec.ofNat 152 (word80 [0x8204505081204a0a14,0x11411042000715924924]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff001fffc00ffffff8,0x7ff87f1ce867038e07])),(BitVec.ofNat 152 (word80 [0x142882810a42805020,0xa20a010440e822249249]))),((BitVec.ofNat 152 (word80 [0x1ffffff003ffff,0xff80007fe374b01c7038])),(BitVec.ofNat 152 (word80 [0x183103020c03106040,0xc00c22080a70a0249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffe000000003ffff,0xffffff80003b08e07fc0])),(BitVec.ofNat 152 (word80 [0x204004041004008081,0x100010000000492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3066bff8000])),(BitVec.ofNat 152 (word80 [0xc08018182008030306,0x4604460910649924924]))),(0x0,0x0)]
def g218C : List ColumnInfo := [(2,0,216,0,5)]
def g218A : List (List Nat) := [[],[67],[49,116],[49,113,65],[65,49,115],[65,115],[113],[113,67]]
def g218D5 (j : Nat) := if j=0 then 0x3f else 0
def g218L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g218D5)
  | _ => emptyPacking
def g218I (_ _ : Nat) : Option (Nat × Nat) := none
def g218 : Forest := ⟨218,5,fun i => g218Y[i]?.getD (0,0),g218C,g218A,g218L,g218I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218P5_0 : block g218 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g218B5 : block g218 5 0 1=true := g218P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218T : checkedTables g218 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g218 0 0 0 = true)
  · exact (rfl : block g218 1 0 0 = true)
  · exact (rfl : block g218 2 0 0 = true)
  · exact (rfl : block g218 3 0 0 = true)
  · exact (rfl : block g218 4 0 0 = true)
  · exact g218B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218G : graphValid g218 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low218 : Lower true (varsX 218) (graphGoal 218) 6 := lower_forest (g:=g218) (i:=0) (hints:=822153264) (before_sound K181 V181) g218G g218T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K218 := extendKnown K181 6 [(218,[]),(233,[16,83,100,67,115]),(234,[83,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V218 : Known true K218 := extend_ok (m:=218) V181 low218 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff7226,0xa10bae00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403202,0x21032a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe0395a,0x8666308003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x602c02800082390a,0x844210030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb0d842c0fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0409000984,0x905800ca28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9ff000000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048044,0x2914a9dc71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc0000003ffff000])),(BitVec.ofNat 152 (word80 [0x2c0580b008b0088071,0x8a0c430c30c30c30c30]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104411,0x42800420820820820820]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(16,0,47,0,8)]
def g63A : List (List Nat) := [[],[32]]
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
theorem g63G : graphValid g63 (boundsBefore K218) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 9 := lower_forest (g:=g63) (i:=0) (hints:=4146) (before_sound K218 V218) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K218 9 [(63,[]),(111,[16,50,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V218 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff72a6,0xa10baa00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403202,0x21032a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe03d4a,0x8666308003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x602c02800082350a,0x844210030c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb85846c000003f00003f])),(BitVec.ofNat 152 (word80 [0x2084308b0489000d84,0x985804eaaaaaaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc0fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048045,0x2114a9dc71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088071,0x20c010410410410410]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104880,0x4a800420820820820820]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(1,0,94,0,7),(2,0,93,0,7),(4,0,91,0,7),(16,0,79,0,7),(64,0,31,0,7)]
def g95A : List (List Nat) := [[],[16,50,100]]
def g95D8 (j : Nat) := if j=0 then 0x222317f else 0
def g95L : Nat → Packing
  | 8 => (1,0,3,0,0,0,0,g95D8)
  | _ => emptyPacking
def g95I (_ _ : Nat) : Option (Nat × Nat) := none
def g95 : Forest := ⟨95,8,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 1=true := g95P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact (rfl : block g95 5 0 0 = true)
  · exact (rfl : block g95 6 0 0 = true)
  · exact (rfl : block g95 7 0 0 = true)
  · exact g95B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 9 := lower_forest (g:=g95) (i:=0) (hints:=4146) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 9 [(95,[]),(207,[48,16,33,100,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff83ff83ffffec0,0x4950ae1c00f801f003ff])),(BitVec.ofNat 152 (word80 [0x500508010800100c0,0x850001c210842108421]))),((BitVec.ofNat 152 (word80 [0xff80003fffc1ff81cf,0x21c110e81f003e007c00])),(BitVec.ofNat 152 (word80 [0x6016100a0040208cd,0x214100486318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc87,0xd72644440007c00f801f])),(BitVec.ofNat 152 (word80 [0x8218010c108840007,0x572004414a5294a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000031,0x2e4c7923e000000fffe0])),(BitVec.ofNat 152 (word80 [0x500a00050000281010,0x47920842108421084]))),((BitVec.ofNat 152 (word80 [0x44,0x90af8bb00007fff00000])),(BitVec.ofNat 152 (word80 [0x604c02260211302000,0x808e8ba294a5294a5294]))),((BitVec.ofNat 152 (word80 [0x33a,0x529a034bfff800000000])),(BitVec.ofNat 152 (word80 [0x807004380421c04322,0x528a020318c6318c6318]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(2,0,117,0,7),(32,0,87,0,7),(4,0,115,0,6),(64,0,55,0,6),(5,0,114,0,5),(18,0,101,0,5),(33,0,86,0,5),(66,0,53,0,5),(80,0,39,0,5),(3,0,116,0,4)]
def g119A : List (List Nat) := [[],[64,81,98]]
def g119D5 := limbs80 #[#[0x3d8b828688791434c110,0x332080d1815ddd56344]]
def g119D6 := limbs80 #[#[0xd50d10fc54110fc4c110,0xf0f00fd59510fd58d10e,0x213888c084e223026cb4,0xe08a9848c0c48]]
def g119H6 := limbs80 #[#[0x1e00001200000,0x1d407200000000]]
def g119D7 := limbs80 #[#[0xf80fea97f543fa61f510,0x918208201388905a6e4,0x118208246044]]
def g119H7 := limbs80 #[#[0xd20088f400000063,0x81003000000000]]
def g119D8 (j : Nat) := if j=0 then 0x841013f else 0
def g119H8 (j : Nat) := if j=0 then 0x7ed8080099600060 else 0
def g119L : Nat → Packing
  | 5 => (3,3,4,0,0,5,0,g119D5)
  | 6 => (5,2,4,0,0,7,0,g119D6)
  | 7 => (4,1,4,0,0,7,0,g119D7)
  | 8 => (1,0,4,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 23 0 7 2 1 g119H6
  | 7 => lookupWord 1 17 0 8 3 1 g119H7
  | 8 => lookupWord 1 11 0 7 2 1 g119H8
  | _ => fun _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_1 : block g119 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 3=true := (@block_merge g119 5 0 1 2 g119P5_0 g119P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_3 : block g119 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 5=true := (@block_merge g119 6 0 3 2 g119P6_0 g119P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_1 : block g119 7 1 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : block g119 7 0 4=true := (@block_merge g119 7 0 1 3 g119P7_0 g119P7_1)
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
  · exact (rfl : block g119 4 0 0 = true)
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=66) (before_sound K95 V95) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K95 9 [(119,[]),(123,[16,50,100]),(187,[112,32,50,84,99]),(190,[112,48,84,99]),(246,[112,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V95 low119 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffffe22e,0xa00d4a4003f000fc0fff])),(BitVec.ofNat 152 (word80 [0x48010048400040a00a,0x20014201041041041041]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc007fffe0ffff6590,0xc06ab68000003f03f03f])),(BitVec.ofNat 152 (word80 [0x110a20900240804580,0xc04a1412492492492492]))),((BitVec.ofNat 152 (word80 [0xffff800000ffe035c6,0xb7d04080fc0fc0000000])),(BitVec.ofNat 152 (word80 [0x600c02e084050231c6,0xa54040871c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000084d,0x6956a9bf00000003ffc0])),(BitVec.ofNat 152 (word80 [0x80500b000016040844,0x914a88c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x1171,0x18b1dc40000ffffc0000])),(BitVec.ofNat 152 (word80 [0x2604c010898080031,0x18b08868a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0xce93,0x4f80057ffff000000000])),(BitVec.ofNat 152 (word80 [0x380700210e0104611,0x42800570c30c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(1,0,124,0,7),(8,0,117,0,7),(32,0,93,0,7),(64,0,61,0,7),(4,0,121,0,6),(16,0,109,0,6)]
def g125A : List (List Nat) := [[],[66,101]]
def g125D7 (j : Nat) := if j=0 then 0x2cdd240dfd31 else 0
def g125D8 (j : Nat) := if j=0 then 0x2c6881bf else 0
def g125H8 (j : Nat) := if j=0 then 0x80 else 0
def g125L : Nat → Packing
  | 7 => (1,1,3,0,0,0,0,g125D7)
  | 8 => (1,0,3,0,0,0,0,g125D8)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 4 0 0 g125H8
  | _ => fun _ => none
def g125 : Forest := ⟨125,8,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : block g125 7 0 1=true := g125P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B8 : block g125 8 0 1=true := g125P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact (rfl : block g125 5 0 0 = true)
  · exact (rfl : block g125 6 0 0 = true)
  · exact g125B7
  · exact g125B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 9 := lower_forest (g:=g125) (i:=0) (hints:=20482) (before_sound K119 V119) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K119 9 [(125,[]),(126,[16,98,50,67,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V119 low125 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff7224,0xa70baa00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403200,0x25032a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe03d48,0x8e6630c0000000fc0fc0])),(BitVec.ofNat 152 (word80 [0x20642c828080823d08,0x8e4210638e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad86,0xb058468003f03f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0409000506,0x9058048a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc0fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048045,0x2114ad9c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088071,0x20c010410410410410]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104880,0x4a800060820820820820]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(2,0,157,0,8)]
def g159A : List (List Nat) := [[],[49,116],[32],[32,49,116]]
def g159D8 (j : Nat) := if j=0 then 0x7f else 0
def g159L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g159D8)
  | _ => emptyPacking
def g159I (_ _ : Nat) : Option (Nat × Nat) := none
def g159 : Forest := ⟨159,8,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P8_0 : block g159 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B8 : block g159 8 0 1=true := g159P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : checkedTables g159 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g159 0 0 0 = true)
  · exact (rfl : block g159 1 0 0 = true)
  · exact (rfl : block g159 2 0 0 = true)
  · exact (rfl : block g159 3 0 0 = true)
  · exact (rfl : block g159 4 0 0 = true)
  · exact (rfl : block g159 5 0 0 = true)
  · exact (rfl : block g159 6 0 0 = true)
  · exact (rfl : block g159 7 0 0 = true)
  · exact g159B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 9 := lower_forest (g:=g159) (i:=0) (hints:=4146) (before_sound K125 V125) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K125 9 [(159,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V125 low159 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff801ffffe1fff94a6,0x1d94b00003f00003f03f])),(BitVec.ofNat 152 (word80 [0x450940500441101486,0xc80b145145145145145]))),((BitVec.ofNat 152 (word80 [0xffffe007fffff83a0a,0x978b5000000000fc0fc0])),(BitVec.ofNat 152 (word80 [0x164191642810213a02,0x978948e38e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xfffffff8001ffff968,0x38516000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x98020180b082406928,0x3051028a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000063f,0xa863103f000fc0000fc0])),(BitVec.ofNat 152 (word80 [0xe00c0200c00382043c,0x2862130c30c30c30c30c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x984,0x66280fc0000ffffff000])),(BitVec.ofNat 152 (word80 [0x1004010004000000,0x410410410410410]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x6651,0x43c4cffffff000000000])),(BitVec.ofNat 152 (word80 [0x6018060118040241,0x43044820820820820820]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,8),(8,0,167,0,8),(128,0,47,0,8),(1,0,174,0,7),(4,0,171,0,7),(32,0,143,0,7),(5,0,170,0,5),(33,0,142,0,4),(36,0,139,0,4)]
def g175A : List (List Nat) := [[],[32]]
def g175D6 := limbs80 #[#[0xe3c1243e437a94250120,0x5]]
def g175D7 := limbs80 #[#[0xf50940bf59120fe50120,0x42a00ff58940bfd8940e,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c31c871]]
def g175H7 (j : Nat) := if j=0 then 0x80 else 0
def g175D8 := limbs80 #[#[0xa38c2461a403fa81fd20,0x1e851c6121c]]
def g175H8 := limbs80 #[#[0xd3000000,0x700094b80000000000a1,0x420000]]
def g175D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g175H9 (j : Nat) := if j=0 then 0x77b000000000d00 else 0
def g175L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g175D6)
  | 7 => (5,2,4,0,0,8,0,g175D7)
  | 8 => (2,1,4,0,0,6,0,g175D8)
  | 9 => (1,0,4,0,0,0,0,g175D9)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g175H7
  | 8 => lookupWord 1 23 0 8 3 1 g175H8
  | 9 => lookupWord 1 11 0 6 1 1 g175H9
  | _ => fun _ => none
def g175 : Forest := ⟨175,9,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : block g175 6 0 1=true := g175P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_4 : block g175 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 5=true := (@block_merge g175 7 0 4 1 g175P7_0 g175P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 2=true := g175P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P9_0 : block g175 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B9 : block g175 9 0 1=true := g175P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g175 0 0 0 = true)
  · exact (rfl : block g175 1 0 0 = true)
  · exact (rfl : block g175 2 0 0 = true)
  · exact (rfl : block g175 3 0 0 = true)
  · exact (rfl : block g175 4 0 0 = true)
  · exact (rfl : block g175 5 0 0 = true)
  · exact g175B6
  · exact g175B7
  · exact g175B8
  · exact g175B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 10 := lower_forest (g:=g175) (i:=0) (hints:=4146) (before_sound K159 V159) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K159 10 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V159 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffe0ffc1fffff,0xc8026c493000f00f00ff])),(BitVec.ofNat 152 (word80 [0x280a0142008400100,0xc8022009111111111111]))),((BitVec.ofNat 152 (word80 [0xfffff0000fffe0ff81,0xcf68f320000000f00f00])),(BitVec.ofNat 152 (word80 [0xb20c8584850028209,0xcf2873000bbbbbbbbbbb]))),((BitVec.ofNat 152 (word80 [0xfffffffff00000fffc,0x84b15690d00f0f00f00f])),(BitVec.ofNat 152 (word80 [0xc0100600060840400,0x4a15410022222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff0000,0x32aaa8e240f00000fff0])),(BitVec.ofNat 152 (word80 [0x500a02800280002810,0x100088e2444444444444]))),(0x4154991e6f000fff0000,(BitVec.ofNat 152 (word80 [0x600c03008301083020,0x548802644444444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [3,0x3f0502078ffff0000000])),(BitVec.ofNat 152 (word80 [0x80300c010c0210c043,0x23000204888888888888]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(2,0,181,0,8)]
def g183A : List (List Nat) := [[],[84],[114],[114,84],[32],[32,84],[32,112],[32,112,84],[112,32],[112,32,84],[112],[112,84]]
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
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=66) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 9 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffffe1ffffb2,0xd241b1000007c00f83ff])),(BitVec.ofNat 152 (word80 [0x4824020244002092,0x52011004210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffe00fffe1fff25,0x2ccb188000f801f07c1f])),(BitVec.ofNat 152 (word80 [0x409008140480404021,0xc4a0808421084210842]))),((BitVec.ofNat 152 (word80 [0x1fffffff00001ff058,0xf4694e001f003e000000])),(BitVec.ofNat 152 (word80 [0x82e030181708828258,0xf4494a1ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xab846f83e00000007fe0])),(BitVec.ofNat 152 (word80 [0xb0140a058000b0400,0xa18467b18c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c060110c0804,0x1b08521084210842108]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201008000100000,0x42108421084210]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(8,0,181,0,8),(16,0,173,0,8),(32,0,157,0,8),(1,0,188,0,7),(4,0,185,0,7),(128,0,61,0,7),(0,8,21,160,6),(5,0,184,0,5),(9,0,180,0,5),(128,8,21,32,5),(129,0,60,0,4),(132,0,57,0,4)]
def g189A : List (List Nat) := [[],[32]]
def g189D5 (j : Nat) := if j=0 then 0x2f2e0d7154120 else 0
def g189D6 := limbs80 #[#[0x26fb9aca887715154110,0xdd6c2a8241da5455048,0x43f4b8aa0906df735951,0x391eda88440177dcd615,0xb931f2e0209e3c838961,0x41e2d047211a0ae22790,0xc43840]]
def g189H6 (j : Nat) := if j=0 then 0x40 else 0
def g189D7 := limbs80 #[#[0xbd8520fa54120bb58910,0x54520bf59510fe54110b,0x8550bfd8550df54550fb,0xd3918096361384800ff5,0xe98e448d2478e448b3e8,0x4a938e438d8a99102141,0xa631e448a59580f96231,0x6391429650b863929190,0x59488e2298]]
def g189H7 := limbs80 #[#[0x556100004a16c4633,0x120]]
def g189D8 := limbs80 #[#[0x88a4b807f543fa21ed20,0x1ca3846471808356838c,0x2a851c612]]
def g189H8 := limbs80 #[#[0x2,0x8000030c0000000,0x0,0x14200000000000098000,0x6000000147040,0x0,0x0,0x0,0xe6000000000,0x0,0xca00000,0x0,0x0,0x0,0x0,0x3ea0000000000000,0x0,0x0,0x12700000]]
def g189D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g189H9 := limbs80 #[#[0x188000000000800e7e00,0xb80000]]
def g189L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g189D5)
  | 6 => (7,3,4,0,0,8,0,g189D6)
  | 7 => (9,2,4,0,0,9,0,g189D7)
  | 8 => (3,1,4,0,0,7,0,g189D8)
  | 9 => (1,0,4,0,0,0,0,g189D9)
  | _ => emptyPacking
def g189I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g189H6
  | 7 => lookupWord 2 11 2 8 3 1 g189H7
  | 8 => lookupWord 2 179 1 9 4 1 g189H8
  | 9 => lookupWord 1 19 0 7 2 1 g189H9
  | _ => fun _ => none
def g189 : Forest := ⟨189,9,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P5_0 : block g189 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B5 : block g189 5 0 1=true := g189P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_4 : block g189 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 7=true := (@block_merge g189 6 0 4 3 g189P6_0 g189P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : block g189 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_3 : block g189 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_8 : block g189 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : block g189 7 0 9=true := (@block_merge g189 7 0 3 6 g189P7_0 (@block_merge g189 7 3 5 1 g189P7_3 g189P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P8_0 : block g189 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P8_1 : block g189 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B8 : block g189 8 0 3=true := (@block_merge g189 8 0 1 2 g189P8_0 g189P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P9_0 : block g189 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B9 : block g189 9 0 1=true := g189P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact g189B5
  · exact g189B6
  · exact g189B7
  · exact g189B8
  · exact g189B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 10 := lower_forest (g:=g189) (i:=0) (hints:=20482) (before_sound K183 V183) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K183 10 [(189,[]),(215,[49,114,66,101]),(221,[66,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V183 low189 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc00ffffe1fff01b,0x82cb2b0000f8000f83e0])),(BitVec.ofNat 152 (word80 [0xa82a05024400221b,0x82cb000c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0x1fffff007ffe1fff70,0x29c79280000001f07c1f])),(BitVec.ofNat 152 (word80 [0x50320c864080504050,0x9879246318c6318c631]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80001fffed,0xb0415c001f003e00001f])),(BitVec.ofNat 152 (word80 [0x82c030080b0882802d,0xb0404c18c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xfe246883e007c0007fe0])),(BitVec.ofNat 152 (word80 [0x30040100c00030400,0x70206890842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x1132807c0007ffff8000])),(BitVec.ofNat 152 (word80 [0x40080201000040000,0x21084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x459c477ffff800000000])),(BitVec.ofNat 152 (word80 [0x180300c060111808c0,0x5140342108421084210]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(2,0,217,0,8)]
def g219A : List (List Nat) := [[],[49,116]]
def g219D8 (j : Nat) := if j=0 then 0x7f else 0
def g219L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g219D8)
  | _ => emptyPacking
def g219I (_ _ : Nat) : Option (Nat × Nat) := none
def g219 : Forest := ⟨219,8,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 1=true := g219P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact (rfl : block g219 5 0 0 = true)
  · exact (rfl : block g219 6 0 0 = true)
  · exact (rfl : block g219 7 0 0 = true)
  · exact g219B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 9 := lower_forest (g:=g219) (i:=0) (hints:=4148) (before_sound K189 V189) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K189 9 [(219,[]),(237,[32,49,16,96,84,112]),(249,[64,49,33,82,96,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V189 low219 (by decide +kernel)
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf801fffff83ffffd82,0xd41a79c0000000f83ff])),(BitVec.ofNat 152 (word80 [0x541502a01081010182,0x841031e318c6318c631]))),((BitVec.ofNat 152 (word80 [0xfffe003fffc1ff839d,0xa14d50880007c0007c00])),(BitVec.ofNat 152 (word80 [0x61184b08a004420b94,0xa14d40816b5ad6b5ad6b]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffcd7,0xc5b0444400f801f0001f])),(BitVec.ofNat 152 (word80 [0x80200c02c108140051,0xc5904400c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2ed47a201f003e007fe0])),(BitVec.ofNat 152 (word80 [0x4010030000181021,0x4903800842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x180600c0210602004,0x102c80a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x6018030042180400a,0x202034a108421084210]))),(0x0,0x0)]
def g222C : List ColumnInfo := [(2,0,220,0,7),(8,0,214,0,7),(16,0,206,0,7),(128,0,94,0,7),(0,4,74,144,6),(4,0,218,0,6)]
def g222A : List (List Nat) := [[],[49,116]]
def g222D7 := limbs80 #[#[0xa15662e85d03ec83f541,0x498b]]
def g222D8 (j : Nat) := if j=0 then 0x2c21a1bf else 0
def g222H8 (j : Nat) := if j=0 then 0x147 else 0
def g222L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g222D7)
  | 8 => (1,0,3,0,0,0,0,g222D8)
  | _ => emptyPacking
def g222I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 g222H8
  | _ => fun _ => none
def g222 : Forest := ⟨222,8,fun i => g222Y[i]?.getD (0,0),g222C,g222A,g222L,g222I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P7_0 : block g222 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B7 : block g222 7 0 2=true := g222P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P8_0 : block g222 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B8 : block g222 8 0 1=true := g222P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222T : checkedTables g222 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g222 0 0 0 = true)
  · exact (rfl : block g222 1 0 0 = true)
  · exact (rfl : block g222 2 0 0 = true)
  · exact (rfl : block g222 3 0 0 = true)
  · exact (rfl : block g222 4 0 0 = true)
  · exact (rfl : block g222 5 0 0 = true)
  · exact (rfl : block g222 6 0 0 = true)
  · exact g222B7
  · exact g222B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : graphValid g222 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 9 := lower_forest (g:=g222) (i:=0) (hints:=553718832) (before_sound K219 V219) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K219 9 [(222,[]),(238,[99,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V219 low222 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff83ff83fffffc8,0x960ac1c0007c1f003ff])),(BitVec.ofNat 152 (word80 [0x500508010800103c0,0x8400014210842108421]))),((BitVec.ofNat 152 (word80 [0xff80003fffc1ff81d7,0xa14312a800003e007c00])),(BitVec.ofNat 152 (word80 [0x6416120a0050209d3,0xa143020a739ce739ce73]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc97,0xc534454400f8000f801f])),(BitVec.ofNat 152 (word80 [0x48098004c108240007,0xc5240500c6318c6318c6]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2e5c7a201f00000fffe0])),(BitVec.ofNat 152 (word80 [0x901200090000481020,0x187821084210842108]))),((BitVec.ofNat 152 (word80 [0x44,0x90bf89b3e0003ff00000])),(BitVec.ofNat 152 (word80 [0xe01c020e0210702004,0xbc89a18c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x6004300421804018,0x1202024a108421084210]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(2,0,229,0,8)]
def g231A : List (List Nat) := [[],[112]]
def g231D8 (j : Nat) := if j=0 then 0x7f else 0
def g231L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g231D8)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,8,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P8_0 : block g231 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B8 : block g231 8 0 1=true := g231P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact (rfl : block g231 6 0 0 = true)
  · exact (rfl : block g231 7 0 0 = true)
  · exact g231B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 9 := lower_forest (g:=g231) (i:=0) (hints:=82) (before_sound K222 V222) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K222 9 [(231,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V222 low231 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc007fe0ffc1fff83,0xcc2278492000f00f00f0])),(BitVec.ofNat 152 (word80 [0xa8150142048400108,0xcc227009033333333333]))),((BitVec.ofNat 152 (word80 [0xfffff8000fffe0fffd,0xcb48e720100000f00f0f])),(BitVec.ofNat 152 (word80 [0x32064184810028201,0xcb082300199999999999]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffff00000fffc,0x84b15690d00f0f00f00f])),(BitVec.ofNat 152 (word80 [0xc0180200060840400,0x4a15410022222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff0000,0x32aaa8e240f00000fff0])),(BitVec.ofNat 152 (word80 [0x500a01400280002810,0x100088e2444444444444]))),(0x4154991e6f000fff0000,(BitVec.ofNat 152 (word80 [0x600c01808301083020,0x548802644444444444]))),((BitVec.ofNat 152 (word80 [3,0x3f0502078ffff0000000])),(BitVec.ofNat 152 (word80 [0x803006010c0210c043,0x23000204888888888888]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(32,0,203,0,7)]
def g235A : List (List Nat) := [[],[101],[16,115],[16,115,101]]
def g235D7 (j : Nat) := if j=0 then 0x7f else 0
def g235L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g235D7)
  | _ => emptyPacking
def g235I (_ _ : Nat) : Option (Nat × Nat) := none
def g235 : Forest := ⟨235,7,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 1=true := g235P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact (rfl : block g235 5 0 0 = true)
  · exact (rfl : block g235 6 0 0 = true)
  · exact g235B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 8 := lower_forest (g:=g235) (i:=0) (hints:=4149) (before_sound K231 V231) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K231 8 [(235,[]),(250,[64,81,32,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V231 low235 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00fffff07fff07f,0x488a14c93000f00f0f0f])),(BitVec.ofNat 152 (word80 [0x280a0280210002100,0x48820049111111111111]))),((BitVec.ofNat 152 (word80 [0xfffff003fff83fff81,0xede26920000000f0f0f0])),(BitVec.ofNat 152 (word80 [0x320c8320400a04009,0xed820120099999999999]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffc00003ffffc,0x8633c490d00f0f0000ff])),(BitVec.ofNat 152 (word80 [0x140100402821028000,0x221c490022222222222]))),((BitVec.ofNat 152 (word80 [0xffffffffffffc00000,0x32a8bae240f00000ff00])),(BitVec.ofNat 152 (word80 [0x580a0280b0000b0210,0x228ba82466666666666]))),(0x4154991e6f000fff0000,(BitVec.ofNat 152 (word80 [0x600c0300c0420c0420,0x541802644444444444]))),((BitVec.ofNat 152 (word80 [3,0x3f0502078ffff0000000])),(BitVec.ofNat 152 (word80 [0x80300c030084300843,0x35000004888888888888]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(2,0,241,0,8)]
def g243A : List (List Nat) := [[],[100],[64,81,118],[64,81,112,96],[96,81,64,116],[96,81,116],[112],[112,100]]
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
theorem g243G : graphValid g243 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 9 := lower_forest (g:=g243) (i:=0) (hints:=68) (before_sound K235 V235) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K235 9 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ffffc7ffe3fc4,0x204c300000f83e0f83ff])),(BitVec.ofNat 152 (word80 [0x8040200800040000,0x84210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffe00fff87ffc3db,0x928b20001f0001f07c1f])),(BitVec.ofNat 152 (word80 [0x210884421011080818,0x908a2210842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff00007fffc2e,0xeb48003e007c0007fe0])),(BitVec.ofNat 152 (word80 [0xa010080a120500086,0xe340108421084210842]))),((BitVec.ofNat 152 (word80 [0xfffffffffff8000003,0xc557907c000001ff8000])),(BitVec.ofNat 152 (word80 [0x4c120904c002609103,0x455595294a5294a5294a]))),((BitVec.ofNat 152 (word80 [0x39,0xec08df800007fe000000])),(BitVec.ofNat 152 (word80 [0x701c0e070243812239,0xe008d6318c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x10,0x51304ffffff800000000])),(BitVec.ofNat 152 (word80 [0x802010080004000000,0x842108421084210]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(4,0,241,0,8),(16,0,229,0,8),(32,0,213,0,8),(64,0,181,0,8),(1,0,244,0,7),(128,0,117,0,7)]
def g245A : List (List Nat) := [[],[66,101],[112],[112,66,101]]
def g245D8 (j : Nat) := if j=0 then 0x2a5d4c0dfd50 else 0
def g245D9 (j : Nat) := if j=0 then 0x2c6881bf else 0
def g245H9 (j : Nat) := if j=0 then 0x60 else 0
def g245L : Nat → Packing
  | 8 => (1,1,3,0,0,0,0,g245D8)
  | 9 => (1,0,3,0,0,0,0,g245D9)
  | _ => emptyPacking
def g245I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 4 0 0 g245H9
  | _ => fun _ => none
def g245 : Forest := ⟨245,9,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_0 : block g245 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B8 : block g245 8 0 1=true := g245P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P9_0 : block g245 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B9 : block g245 9 0 1=true := g245P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245T : checkedTables g245 9 := by
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
  · exact g245B8
  · exact g245B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 10 := lower_forest (g:=g245) (i:=0) (hints:=2) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 10 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g252Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe007ffffe1ffff9164,0xdc16e000000fc0000fff])),(BitVec.ofNat 152 (word80 [0x44510a204404101144,0xcc00e249249249249249]))),((BitVec.ofNat 152 (word80 [0xfff800fffe1ff8318b,0x3c89500003f000fff000])),(BitVec.ofNat 152 (word80 [0x80602c028040213083,0x3c0140c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0881400a39,0x31110186186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x902404c0009824628,0x3861514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038070110e044104,0x42ec8618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g252C : List ColumnInfo := [(4,0,248,0,7),(8,0,244,0,7),(16,0,236,0,7),(32,0,220,0,7),(64,0,188,0,7),(128,0,124,0,7),(12,0,240,0,5),(20,0,232,0,5),(24,0,228,0,5),(44,0,208,0,4),(52,0,200,0,4),(84,0,168,0,4),(132,0,120,0,4),(136,0,116,0,4),(144,0,108,0,4)]
def g252A : List (List Nat) := [[],[99,84],[50,100],[50,66,82,98],[66,101],[66,83,98,50],[82,67],[82,99,66,67],[98,50,67,84],[98,83]]
def g252D5 := limbs80 #[#[0x54950443cc5515150110,0x54237e0d7654910e6962,0x841d51c08df835c762]]
def g252D6 := limbs80 #[#[0x3b4a92a0904df7359510,0xdf2caa0221fc5454044,0x437cb12a088779525411,0x10bf6e8a8221be591504,0x4427ebb2a4885fb70549,0x5109fee4b2a213fdd562,0x15427fb8aca906df7359,0x85509fae5b0aa177dcd6,0x418027eb8ec4a84fd74d,0xe765e0dd9a5713d08b88,0x8516283033f26f2dac28,0x208504282001088c2280,0x4000182000101840410,0x182000]]
def g252H6 := limbs80 #[#[0x520078001c3003200000,0x2000000000000000001,0x31000000000001]]
def g252D7 := limbs80 #[#[0xf58910fe54110fe50110,0x59520fe54120bf59510b,0x8950df54950bfd8550bf,0x550ff54520ff54910bfd,0x2a0d82400ff58950ff58,0x62a24ca34fc6c2e92c78,0xa496219a24a92296485,0x42985aa50869820448a4,0x29650a20449821c60259,0x9a11c90c182518588718,0x1c60e19a6263083]]
def g252H7 := limbs80 #[#[0x13d91800442980c0602b,0x20005049a10b14230001,0x707d034008000005c400,0x91385800483c87201800,0x1180621b31d084828006,0xb853a580880000000048,0x542424800506000106,0x6840]]
def g252D8 := limbs80 #[#[0x489a3407f543fa41fd10,0xa600ab48d58ad424aab]]
def g252H8 := limbs80 #[#[0x1224000004160000c3,0x0,0x63450000000000000000,0x1054900000000000001c,0x1c54003c490c4a5,0x0,0x696c06a200000,0x60c000000000000,0xc0000000020400000000,0x88210000000000000186,0x30,0x682000000000,0xc0000000b2f25000000,0x70000000000023c80000,0x607001a8b42205054a,0x84c]]
def g252D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g252H9 := limbs80 #[#[0xd6bc,0x2364a0038c9540,0x270a0000000001140000,0x185b131c2079,0x2c9e8800000000000]]
def g252L : Nat → Packing
  | 5 => (4,4,4,0,0,5,0,g252D5)
  | 6 => (18,3,4,0,0,8,0,g252D6)
  | 7 => (13,2,4,0,0,9,0,g252D7)
  | 8 => (3,1,4,0,0,6,0,g252D8)
  | 9 => (1,0,4,0,0,0,0,g252D9)
  | _ => emptyPacking
def g252I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 31 0 9 2 3 g252H6
  | 7 => lookupWord 7 47 5 12 5 3 g252H7
  | 8 => lookupWord 7 113 2 11 4 3 g252H8
  | 9 => lookupWord 3 41 2 10 2 4 g252H9
  | _ => fun _ => none
def g252 : Forest := ⟨252,9,fun i => g252Y[i]?.getD (0,0),g252C,g252A,g252L,g252I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P5_0 : block g252 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g252B5 : block g252 5 0 4=true := g252P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P6_0 : block g252 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P6_2 : block g252 6 2 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g252B6 : block g252 6 0 18=true := (@block_merge g252 6 0 2 16 g252P6_0 g252P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P7_0 : block g252 7 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P7_9 : block g252 7 9 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g252B7 : block g252 7 0 13=true := (@block_merge g252 7 0 9 4 g252P7_0 g252P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P8_0 : block g252 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g252B8 : block g252 8 0 3=true := g252P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P9_0 : block g252 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g252B9 : block g252 9 0 1=true := g252P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252T : checkedTables g252 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g252 0 0 0 = true)
  · exact (rfl : block g252 1 0 0 = true)
  · exact (rfl : block g252 2 0 0 = true)
  · exact (rfl : block g252 3 0 0 = true)
  · exact (rfl : block g252 4 0 0 = true)
  · exact g252B5
  · exact g252B6
  · exact g252B7
  · exact g252B8
  · exact g252B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252G : graphValid g252 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low252 : Lower true (varsX 252) (graphGoal 252) 10 := lower_forest (g:=g252) (i:=0) (hints:=589452288) (before_sound K245 V245) g252G g252T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K252 := extendKnown K245 10 [(252,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V252 : Known true K252 := extend_ok (m:=252) V245 low252 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x42a8b0df401c000000,0xff000000ff0000ff00ff])),(BitVec.ofNat 152 (word80 [0x4088801e001c050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0x44c5070ae0490000ff,0xff0000ff00ff00])),(BitVec.ofNat 152 (word80 [0x40c1030ac001030303,0x3030303030303030303]))),((BitVec.ofNat 152 (word80 [0x321008f8e0a3000000,0xff0000ff000000ff])),(BitVec.ofNat 152 (word80 [0x21008e0e0834a4a4a,0x4a4a4a4a4a4a4a4a4a4a]))),((BitVec.ofNat 152 (word80 [0x4a78c000bfae00ff00,0xff000000000000ff00])),(BitVec.ofNat 152 (word80 [0x228c00026ae1c1c1c,0x1c1c1c1c1c1c1c1c1c1c]))),((BitVec.ofNat 152 (word80 [0xa522ce2403a0ff0000,0xffffff0000])),(BitVec.ofNat 152 (word80 [0x252044000320303030,0x30303030303030303030]))),((BitVec.ofNat 152 (word80 [0xbc0960031542000000,0xffffffff0000000000])),(BitVec.ofNat 152 (word80 [0xbc0020011140a0a0a0,0xa0a0a0a0a0a0a0a0a0a0]))),((BitVec.ofNat 152 (word80 [0x919631a01a15ffffff,0xff000000000000000000])),(BitVec.ofNat 152 (word80 [0x901630a01800c0c0c0,0xc0c0c0c0c0c0c0c0c0c0]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(1,0,126,0,9),(2,0,125,0,9),(4,0,123,0,9),(8,0,119,0,9),(32,0,95,0,9),(64,0,63,0,9)]
def g127A : List (List Nat) := [[],[16,50,100]]
def g127D10 (j : Nat) := if j=0 then 0x3445837f else 0
def g127L : Nat → Packing
  | 10 => (1,0,3,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 1=true := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 10 := by
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
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K252) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=4146) (before_sound K252 V252) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K252 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V252 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x86b0ae106a8c100000,0x3f800003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x809026100a8c002850,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x2831114314bf140000,0x1fc000fe03f80])),(BitVec.ofNat 152 (word80 [0x203010411499161c38,0x70e1c3870e1c3870e1c3]))),((BitVec.ofNat 152 (word80 [0x30c881e42950100000,0x1fc000fe0007f000007f])),(BitVec.ofNat 152 (word80 [0x3000816421401050a1,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x4892df708046cc000f,0xe0007f00000000003f80])),(BitVec.ofNat 152 (word80 [0x48808f308046c0e1c3,0x870e1c3870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x2f49081f86408807f0,0x7ffffc000])),(BitVec.ofNat 152 (word80 [0xf49080a8000898306,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x940f022890a16bf800,0x7ffffff800000000])),(BitVec.ofNat 152 (word80 [0x40f00080020090204,0x8102040810204081020]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x412464885518a7ffff,0xffff8000000000000000])),(BitVec.ofNat 152 (word80 [0x2040805410260408,0x10204081020408102040]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(2,0,189,0,10)]
def g191A : List (List Nat) := [[],[32]]
def g191D10 (j : Nat) := if j=0 then 0xff else 0
def g191L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : block g191 10 0 1=true := g191P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 10 := by
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
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := lower_forest (g:=g191) (i:=0) (hints:=4146) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x92b0ae106a8c100000,0x3f800003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x809026100a8c002850,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x2830114314bf140000,0x1fc000fe03f80])),(BitVec.ofNat 152 (word80 [0x203010411499161c38,0x70e1c3870e1c3870e1c3]))),((BitVec.ofNat 152 (word80 [0x34c081eca950100000,0x1fc000000007f000007f])),(BitVec.ofNat 152 (word80 [0x3400816ca1401152a5,0x4a952a54a952a54a952a]))),((BitVec.ofNat 152 (word80 [0x4c92df700046cc000f,0xe00000fe000000003f80])),(BitVec.ofNat 152 (word80 [0x48808f300046c8e1c3,0x870e1c3870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x2b49081786408807f0,0x7f000007ffffc000])),(BitVec.ofNat 152 (word80 [0xb4108020000888102,0x4081020408102040810]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x940f022890a16bf800,0x7ffffff800000000])),(BitVec.ofNat 152 (word80 [0x140e00088020010204,0x8102040810204081020]))),((BitVec.ofNat 152 (word80 [0x412464885518a7ffff,0xffff8000000000000000])),(BitVec.ofNat 152 (word80 [0x2040805410260408,0x10204081020408102040]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(2,0,221,0,10)]
def g223A : List (List Nat) := [[],[49,116]]
def g223D10 (j : Nat) := if j=0 then 0xff else 0
def g223L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g223D10)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,10,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : block g223 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : block g223 10 0 1=true := g223P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 10 := by
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
  · exact g223B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 11 := lower_forest (g:=g223) (i:=0) (hints:=4146) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 11 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8eb2a4006aac100000,0x3f8001fc00001fc07f])),(BitVec.ofNat 152 (word80 [0x89224000a2c002850,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x30311143043f340000,0xfe00000fe03f80])),(BitVec.ofNat 152 (word80 [0x303010410438361c38,0x70e1c3870e1c3870e1c3]))),((BitVec.ofNat 152 (word80 [0x30c883e4b9d0100000,0x1fc000000007f000007f])),(BitVec.ofNat 152 (word80 [0x3008836431c010d1a3,0x468d1a3468d1a3468d1a]))),((BitVec.ofNat 152 (word80 [0x4892df7000464c000f,0xe0007f0003f800003f80])),(BitVec.ofNat 152 (word80 [0x4882871000460060c1,0x83060c183060c183060c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2f49081f86400807f0,0x3ffffffc000])),(BitVec.ofNat 152 (word80 [0x741080a8000090204,0x8102040810204081020]))),((BitVec.ofNat 152 (word80 [0x940f022890a1ebf800,0x7ffffc0000000000])),(BitVec.ofNat 152 (word80 [0x840900289081c98306,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x412464885518a7ffff,0xffff8000000000000000])),(BitVec.ofNat 152 (word80 [0x2440804410260408,0x10204081020408102040]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(64,0,175,0,10)]
def g239A : List (List Nat) := [[]]
def g239D10 (j : Nat) := if j=0 then 0xff else 0
def g239L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g239D10)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,10,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : block g239 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : block g239 10 0 1=true := g239P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 10 := by
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
  · exact g239B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=4146) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xd180a898841dc28400,0x3f000fc003f000fff])),(BitVec.ofNat 152 (word80 [0x18020180004c08410,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0x39c2d06cac08d9000,0x3f000fc003f000])),(BitVec.ofNat 152 (word80 [0x81982d02c240899238,0xe38e38e38e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xc10f1041f20d217800,0xfc000003f000fc003f])),(BitVec.ofNat 152 (word80 [0xc0041c2092078a2,0x8a28a28a28a28a28a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2862266c54200e0800,0x3f000fc0000000ffffc0])),(BitVec.ofNat 152 (word80 [0x282200041420060041,0x4104104104104104104]))),((BitVec.ofNat 152 (word80 [0x208bd3850de200240f,0xc000000003ffff000000])),(BitVec.ofNat 152 (word80 [0x200392840da2000145,0x14514514514514514514]))),((BitVec.ofNat 152 (word80 [0x167502820823f03bf0,0xffffc0000000000])),(BitVec.ofNat 152 (word80 [0x124502800803302986,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0x2c004932231239c3ff,0xfffff000000000000000])),(BitVec.ofNat 152 (word80 [0x40049222010090208,0x20820820820820820820]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(2,0,245,0,10)]
def g247A : List (List Nat) := [[],[112]]
def g247D10 (j : Nat) := if j=0 then 0xff else 0
def g247L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g247D10)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,10,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 1=true := g247P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 10 := by
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
  · exact g247B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 11 := lower_forest (g:=g247) (i:=0) (hints:=66) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 11 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x11b8a8589e11028400,0x3f00003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x91a820588201008430,0xc30c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xe3802c04c0cdada000,0xfc003f03f03f])),(BitVec.ofNat 152 (word80 [0x23802c000045298218,0x61861861861861861861]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc12f10c1f30c415000,0xfc003f000fc000003f])),(BitVec.ofNat 152 (word80 [0x2a00c1d308005061,0x86186186186186186186]))),((BitVec.ofNat 152 (word80 [0x84226ec55205e0800,0x3f000fc000000003ffc0])),(BitVec.ofNat 152 (word80 [0x842008455205600c3,0xc30c30c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x208bd3050ce250240f,0xc0000000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x1d2040ca2502186,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0x167502820823a03bf0,0xffffff000000000])),(BitVec.ofNat 152 (word80 [0x41502000802802904,0x10410410410410410410]))),((BitVec.ofNat 152 (word80 [0x2c004932231239c3ff,0xfffff000000000000000])),(BitVec.ofNat 152 (word80 [0x200009222010290208,0x20820820820820820820]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(2,0,249,0,9),(8,0,243,0,9),(32,0,219,0,9),(64,0,187,0,9),(128,0,123,0,9),(1,0,250,0,8),(16,0,235,0,8)]
def g251A : List (List Nat) := [[],[64,81,118]]
def g251D9 (j : Nat) := if j=0 then 0x659a8cb1ffd30 else 0
def g251D10 (j : Nat) := if j=0 then 0x3544463ff else 0
def g251H10 (j : Nat) := if j=0 then 0x0 else 0
def g251L : Nat → Packing
  | 9 => (1,1,3,0,0,0,0,g251D9)
  | 10 => (1,0,3,0,0,0,0,g251D10)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 2 0 4 0 0 g251H10
  | _ => fun _ => none
def g251 : Forest := ⟨251,10,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 1=true := g251P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 1=true := g251P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 10 := by
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
  · exact g251B9
  · exact g251B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 11 := lower_forest (g:=g251) (i:=0) (hints:=4148) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 11 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x85870080f286000000,0x3f8001fc000fe03fff])),(BitVec.ofNat 152 (word80 [0x18200007006040810,0x20408102040810204081]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x6a280ed11350000000,0x1fc000000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x6a2804910210489122,0x44891224489122448912]))),((BitVec.ofNat 152 (word80 [0x71c6b5d4080200000f,0xe00000fe03f800000000])),(BitVec.ofNat 152 (word80 [0x718614d408021c3870,0xe1c3870e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0x112ccc68a8e80007f0,0x7f000000001fff80])),(BitVec.ofNat 152 (word80 [0x1004c84888c83060c1,0x83060c183060c183060c]))),((BitVec.ofNat 152 (word80 [0x5cd1cb23810c03f800,0x3ffffe00000])),(BitVec.ofNat 152 (word80 [0x451cb228108a14285,0xa142850a142850a1428]))),((BitVec.ofNat 152 (word80 [0xaa4930220d2bfc0000,0x7ffffc0000000000])),(BitVec.ofNat 152 (word80 [0x8a4920220520c18306,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x212401e4411ffffff,0xffff8000000000000000])),(BitVec.ofNat 152 (word80 [0x1020408,0x10204081020408102040]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(1,0,252,0,10),(8,0,245,0,10),(32,0,221,0,10),(64,0,189,0,10),(4,0,249,0,9),(16,0,237,0,9),(128,0,125,0,9),(12,0,241,0,8),(20,0,233,0,6),(132,0,121,0,6),(144,0,109,0,6)]
def g253A : List (List Nat) := [[],[66,101]]
def g253D8 := limbs80 #[#[0xed56358531ee56358521,0xc238d9d800fe58358521,0xc96271e7cb80e25af3e5,0x11ce3f2e02462]]
def g253D9 := limbs80 #[#[0x5614c7f6b1a43f958521,0x1ac37fdd931bfaec98ff,0x61ffaec98dff735877eb,0xc3f1a4962d0c001ff5cd,0x7189d56cf0c871f31629,0x1315b3cb0949556cb3c2,0x6289225931cf2c09248,0x6cf2c55c24256c73cb02,0xcb0208572c73c0918a24,0x88573c72c0920a256c73,0x2]]
def g253H9 (j : Nat) := if j=0 then 0x3855a else 0
def g253D10 := limbs80 #[#[0x3524803fd61ff4c7ed21,0x8b1633912045ab3940e,0x26a69c64481]]
def g253H10 := limbs80 #[#[0xe2803c74100720e5c780,0x2200601cc44]]
def g253D11 (j : Nat) := if j=0 then 0xca864203ff else 0
def g253H11 (j : Nat) := if j=0 then 0x5101c3b0a else 0
def g253L : Nat → Packing
  | 8 => (3,3,4,0,0,7,0,g253D8)
  | 9 => (9,2,4,0,0,9,0,g253D9)
  | 10 => (3,1,4,0,0,7,0,g253D10)
  | 11 => (1,0,4,0,0,0,0,g253D11)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 3 0 6 2 0 g253H9
  | 10 => lookupWord 2 13 4 9 4 1 g253H10
  | 11 => lookupWord 1 11 0 7 2 1 g253H11
  | _ => fun _ => none
def g253 : Forest := ⟨253,11,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_2 : block g253 8 2 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B8 : block g253 8 0 3=true := (@block_merge g253 8 0 2 1 g253P8_0 g253P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1 : block g253 9 1 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_7 : block g253 9 7 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : block g253 9 0 9=true := (@block_merge g253 9 0 1 8 g253P9_0 (@block_merge g253 9 1 6 2 g253P9_1 g253P9_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_0 : block g253 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_1 : block g253 10 1 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : block g253 10 0 3=true := (@block_merge g253 10 0 1 2 g253P10_0 g253P10_1)
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
  · exact g253B8
  · exact g253B9
  · exact g253B10
  · exact g253B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 12 := lower_forest (g:=g253) (i:=0) (hints:=20482) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 12 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x82a094302a0b300000,0x1fc000fe03fff])),(BitVec.ofNat 152 (word80 [0xa014000a08220c18,0x3060c183060c183060c1]))),((BitVec.ofNat 152 (word80 [0x34b32943501d100000,0x3f80000007f01fc000])),(BitVec.ofNat 152 (word80 [0x349220411019109932,0x64c993264c993264c993]))),((BitVec.ofNat 152 (word80 [0x384883c429f0140000,0x1fc000fe03f80000007f])),(BitVec.ofNat 152 (word80 [0x380083442130143060,0xc183060c183060c18306]))),((BitVec.ofNat 152 (word80 [0x4892df5084464c000f,0xe0007f000000001fff80])),(BitVec.ofNat 152 (word80 [0x48008b1084460460c1,0x83060c183060c183060c]))),((BitVec.ofNat 152 (word80 [0x2f49083f86400807f0,0x3ffffe00000])),(BitVec.ofNat 152 (word80 [0x249083a8440094285,0xa142850a142850a1428]))),((BitVec.ofNat 152 (word80 [0x940f022890a1ebf800,0x7ffffc0000000000])),(BitVec.ofNat 152 (word80 [0x840b00281081c98306,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x412464885518a7ffff,0xffff8000000000000000])),(BitVec.ofNat 152 (word80 [0x12444804000220408,0x10204081020408102040]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(2,0,252,0,10)]
def g254A : List (List Nat) := [[],[99,84]]
def g254D10 (j : Nat) := if j=0 then 0xff else 0
def g254L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g254D10)
  | _ => emptyPacking
def g254I (_ _ : Nat) : Option (Nat × Nat) := none
def g254 : Forest := ⟨254,10,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P10_0 : block g254 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B10 : block g254 10 0 1=true := g254P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : checkedTables g254 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0 = true)
  · exact (rfl : block g254 1 0 0 = true)
  · exact (rfl : block g254 2 0 0 = true)
  · exact (rfl : block g254 3 0 0 = true)
  · exact (rfl : block g254 4 0 0 = true)
  · exact (rfl : block g254 5 0 0 = true)
  · exact (rfl : block g254 6 0 0 = true)
  · exact (rfl : block g254 7 0 0 = true)
  · exact (rfl : block g254 8 0 0 = true)
  · exact (rfl : block g254 9 0 0 = true)
  · exact g254B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 11 := lower_forest (g:=g254) (i:=0) (hints:=554767408) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 11 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff8000000ff80001,0xff007fc01182430b1a7e])),(BitVec.ofNat 152 (word80 [0x5028140a05028140a,0x5028140108041030a3a]))),((BitVec.ofNat 152 (word80 [0xff0000001ff00003fe,0xff800000040d16279f])),(BitVec.ofNat 152 (word80 [0x381c0e070381c0e07,0x381c0c000800506068f]))),((BitVec.ofNat 152 (word80 [0x3fe00007fc00,0x7fd022198e24c5e7])),(BitVec.ofNat 152 (word80 [0x4a25128944a2512894,0x4a25129020098e0445c5]))),((BitVec.ofNat 152 (word80 [0x7fc00000000000,0xff8000bc01f0c0f9f8])),(BitVec.ofNat 152 (word80 [0x1c0e070381c0e07038,0x1c0e0700b400d040f970]))),((BitVec.ofNat 152 (word80 [0x7ffff,0xff000002c06000f8fe00])),(BitVec.ofNat 152 (word80 [0x30180c06030180c060,0x30180c02802000f8b000]))),((BitVec.ofNat 152 (word80 [0x7ffffffff80000,0x23007e00ff0000])),(BitVec.ofNat 152 (word80 [0xa05028140a05028140,0xa0502822007600b80000]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x3c007fff000000])),(BitVec.ofNat 152 (word80 [0xc06030180c06030180,0xc0603034005f2a000000]))),(0x3fff8000000001,(BitVec.ofNat 152 (word80 [0x8040201008040201,0x8040094b0000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(2,0,253,0,12),(1,0,254,0,11),(4,0,251,0,11),(8,0,247,0,11),(16,0,239,0,11),(32,0,223,0,11),(64,0,191,0,11),(128,0,127,0,11),(3,0,252,0,10),(10,0,245,0,10),(34,0,221,0,10),(40,0,215,0,10),(66,0,189,0,10),(80,0,175,0,10),(6,0,249,0,9),(9,0,246,0,9),(12,0,243,0,9),(17,0,238,0,9),(18,0,237,0,9),(24,0,231,0,9),(33,0,222,0,9),(36,0,219,0,9),(48,0,207,0,9),(65,0,190,0,9),(68,0,187,0,9),(72,0,183,0,9),(96,0,159,0,9),(129,0,126,0,9),(130,0,125,0,9),(132,0,123,0,9),(136,0,119,0,9),(144,0,111,0,9),(160,0,95,0,9),(192,0,63,0,9),(0,2,133,120,8),(0,4,74,177,8),(0,8,21,226,8),(5,0,250,0,8),(14,0,241,0,8),(20,0,235,0,8),(26,0,229,0,8),(38,0,217,0,8),(74,0,181,0,8),(98,0,157,0,8),(1,4,74,176,7),(7,0,248,0,7),(8,2,133,112,7),(11,0,244,0,7),(16,2,133,104,7),(16,4,74,161,7),(19,0,236,0,7),(32,2,133,88,7),(32,4,74,145,7),(35,0,220,0,7),(49,0,206,0,7),(50,0,205,0,7),(52,0,203,0,7),(64,2,133,56,7),(64,8,21,162,7),(67,0,188,0,7),(70,0,185,0,7),(128,4,74,49,7),(128,8,21,98,7),(131,0,124,0,7),(133,0,122,0,7),(138,0,117,0,7),(145,0,110,0,7),(161,0,94,0,7),(162,0,93,0,7),(164,0,91,0,7),(176,0,79,0,7),(194,0,61,0,7),(224,0,31,0,7),(13,0,242,0,6),(17,4,74,160,6),(21,0,234,0,6),(24,2,133,96,6),(25,0,230,0,6),(28,0,227,0,6),(33,4,74,144,6),(37,0,218,0,6),(48,2,133,72,6),(48,4,74,129,6),(69,0,186,0,6),(72,2,133,48,6),(73,0,182,0,6),(76,0,179,0,6),(96,2,133,24,6),(97,0,158,0,6),(100,0,155,0,6),(129,4,74,48,6),(130,8,21,96,6),(134,0,121,0,6),(137,0,118,0,6),(140,0,115,0,6),(144,4,74,33,6),(146,0,109,0,6),(148,0,107,0,6),(152,0,103,0,6),(160,4,74,17,6),(192,8,21,34,6),(193,0,62,0,6),(196,0,59,0,6),(200,0,55,0,6),(49,4,74,128,5),(53,0,202,0,5),(141,0,114,0,5),(142,0,113,0,5),(145,4,74,32,5),(149,0,106,0,5),(154,0,101,0,5),(161,4,74,16,5),(165,0,90,0,5),(176,4,74,1,5),(180,0,75,0,5),(194,8,21,32,5),(197,0,58,0,5),(202,0,53,0,5),(177,0,74,0,4)]
def g255A : List (List Nat) := [[]]
def g255D7 := limbs80 #[#[0x83e68e1da35097150120,0x120f96387699525c5504,0x71483e1ce1da65957154,0x55c520f0d7876599358d,0xcac9a002a75f0da9e1d6,0x9138c8c2]]
def g255D8 := limbs80 #[#[0xa09079a3875097150120,0x25c540483cb1c3aa4b8a,0x2eca92e2a8241f685cd4,0x7c71765957154120fac,0x550483cb9c3acab8aa09,0xb2ae4a824175c6dd655c,0xd1735897158130ead32e,0x4c36e8b9f40a12e2987c,0x20a1261b6c5d3a050971,0x5e818455171eb52e8b97,0xfd0d1a84b8a80906d357,0x241f6c5d1a35c540483,0x97154120f3e70ed1ae2a,0xd32cab8aa0907f61a654,0x1f5c699755c550483f38,0x5c520f3e70ed32e2a824,0x26a12e2907da57464d42,0x96597554971483cf3c3b,0x20f3cf0ecb2a4b8a41f5,0x12e2907ce57664d625c5,0x17350d71483cf3c3b26b,0xb2ae8c9a86b8a41f6565,0x29079d78764d435c520f,0x50d71483cdbc3b28a1ae,0x2cb9ac6b8a41a7d6a787,0x7cd57664d635c520f9ab,0x71483b6acb326b1ae290,0xb2c6b8a41e75e1d9358d,0x5a9e1d635c520f1ef0ec,0x82eebd9b28b9ae29069f,0x6b8a41e6d6117464d714,0x5d9935c520b3ef6ec232],#[0xfbdbb0cc9ae29078f586,0xa41c7de1d9664d71482c,0x935c520b3eb69c3b26b8,0x3f46ca2e29059f5b6e1d,0xf1d65975595714834fbc,0xc520f8eaeccaacab8a41,0xcb2ae290797787655655,0x6a78759571483c7bc3b2,0x9faf66d4acab8a41a7d,0xae290797596615755c52,0x87659714834fbd3b2cc2,0x6ae8c1f20a12e367d6d7,0x1b61500f6090042000eb,0xd837e3302e227c22e1f8,0x24bc49e48c47a4504263,0x55e5285165044f24c84c,0x486366245fa5d05a6570,0x26b46a269067e66c65a6,0x74a7387267147026e46d,0x4082e8047da7b077a75c,0x846a3458c58768648528,0xf86a14a8b15f19673e0e,0x9672846a35e2c859ca15,0xb78d13d1d4b8896c8e80,0x2fc088833a1559ca14a8,0x44f46860ce850a68e36a,0x18c4f02a14a8b063b8d1,0xa8bb8d0431aa2ee35100,0x983dc2ea348d2351df80,0xbd8d1815147a85d602e0,0x37c2c66808a201e92370,0x80f0b1d27da72c0469d6],#[0x234629f29dd010a768df,0x5890d4702d1a2c2500cf,0xc1048c6c086243227323,0xa24300018ce020963011,0x2c704a3012c10449e48c,0x842c10648c462888a244,0x37251310dc9487060d88,0x9830120dc9664c4c4319,0x7046181183043b81524,0x2323043d41983066181e,0x622410424c106224104,0x120630418c10660c14c1,0x521c186a2212c944d024,0x9857250c02a61818c3b2,0xc1e070449448d60c300c,0xc0a73090c0ac100c0411,0x8a]]
def g255H8 (j : Nat) := if j=0 then 0x5054bc300000 else 0
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x7150120fe85097150120,0xe7ce1d7150120f6c5d1,0x54250120dea655425012,0x20beae954250120bea69,0x1d4250120eea61d42501,0x120dea65d4250120eeae,0xe9d4250120bea69d4250,0x120fca5515250120bea,0xa5d17250120dda655525,0x50120d7a65d7250120f6,0xd85497154120e6e61d74,0x154120f5c5d57154120f,0xfca5514254120e7ce1d7,0x5254120bda6954254120,0xeda61d5254120bda699,0xd5254120edae1d525412,0x20bda69d5254120dda65,0xd57254120f9a59562541,0x120d7a65d7254120f5a5,0x5d1425c120e5e61d7554,0xc120b7a69d425c120f6a,0xa69d525c120f5a5d5525,0x5c120f3a5d9625c120b7,0x7a60d725c120b7a69d62,0x25c120e7a611725c120e,0xe7a619725c120e7a6157,0x755c120e6e611745c120,0xe3e619765c120e5e615,0xd425c520f695d1425c52,0x20f595d5525c520e79e1,0xd9625c520e79e1d525c5,0x520e79e1d625c520f395],#[0xe9d835c520e7560d735c,0xc520e6d611745c520a7d,0xd615755c520a7de9d845,0x5c520a7de9d855c520e5,0x7de9d865c520e3d61976,0x75c520a7d68f875c520a,0xa7d697875c520a7d6938,0x7450920a7d69b875c520,0xe5b61d7554920e6b61d,0x5755c920e6b611745c92,0x30f745cd7158130e5b61,0x893258130f3c5d971581,0x130f365d97358130fb25,0x5c9325c130e3e61d7658,0xc130f665d1435c130f72,0xe611745c130f365d9635,0x5c530e3e619765c130e6,0x655d1435c530f745cd90,0x35c530b7569d435c530f,0xb7569d635c530f355d96,0x735c530e75611735c530,0xe6d611745c530e75619,0xd7658d30e3d619765c53,0x40e37619765cd30e3761,0x9d425c140f6a5c9425c1,0x140f4e5d5545c140b6e6,0x615745c140b6e69d545c,0xc540e5e615755c140e6e,0xd5d5545c540f6c5d1905,0x5c540b6d69d545c540f4,0x5d615755c540e6d61574,0x85d540e6b61d7250940e],#[0xf5a5c9525c1508fbe899,0x545c150b5e69d525c150,0xb5e69d545c150f4e5d1,0xd655c150f1e5d9655c15,0x50e5e619755c150b5e69,0xd5905c550e3e619765c1,0x550f4d5d1545c550f5c5,0x5d9655c550b5d69d545c,0xc550b5d69d655c550f1d,0xd619765c550e5d619755,0x5c160e5b61d7254950e3,0x3e69d625c160f3a5c962,0x55c160f1e5d5655c160b,0xf3c5d9905c560b3e69d6,0x655c560f1d5d5655c560,0x1f715cd624c971b3d69d,0xd824c971f395d9624c97,0x71f655d1434c971f715c,0x51734c971b7569d434c9,0x971d75659734c971d756,0x659764c971d6d651744c,0x971d6d5d39050971d3d,0xd5d39350971f695d1825,0x50971f4d5d55450971d6,0x6d6557450971b6d69d54,0x550971d6de557450971d,0x97de9d9850971d5d6557,0x825497197d69f9850971,0x1f4d5d15454971f595d5,0x97554971b5d69d545497,0x71d3d6597654971d5d65,0xd56558971f395d982589],#[0x971b3d69d6558971f1d5,0xe517460971d75e4d7360,0x971d5de557560971d6d,0x56117350d71d3de59766,0x58d71f655d18350d71f6,0x355d98358d71f3561973,0x45cd71eb56198358d71f,0xf4d6157455171b75e8d8,0x7561171f4d5d58455171,0x1f1d6197559571d5de55,0xd9859571f1d5d9855957,0x32f335d973589329f5e8,0x11745c932f635d1435c9,0x142e37619765cd32e6b6,0x5d3835c942e6b5d172e0,0xc942f4b5d5545c942e6b,0xb615745c942b6b69d545,0x5c942e6be15745c942e6,0x4b5d1545c952e5b61575,0x55c952b5b69d545c952f,0xf1b5d5655c962e5b6197,0x4250120f7c5cd7150120,0xfdc5957154120fea5cd,0x95254120f7c5d9715412,0x20fda5957254120fda5d,0x1d6554120f9e5d965541,0x120edee1d6554120ede6,0x69d6554120dde65d6554,0xc120f7a5d9525c120bde,0xa58d725c120f7a50d725,0x5c120f7a595725c120f7,0x3e5d9635c120f6e5d143],#[0x55c120f5e5d5655c120f,0xb7e69d655c120f3e5d96,0x425c520e7e5d9855c120,0xf795d9525c520f795cd,0xd435c520f795cd625c52,0x20f6d5d1435c520f755c,0x9d435c520e7de1d435c5,0x520f755cd635c520b7d6,0xe1d635c520f3d5d9635c,0xc520b7d69d635c520e7d,0xd619735c520e7d611735,0x5c520e7de1d935c520e7,0x5d5d5655c520e7de1d94,0x55c520f3d5d9655c520f,0xb7d69d655c520e7de1d6,0x955c520e7d5d9855c520,0xe7de1d965c520e7de1d,0x1435c920f3b5d9735892,0x20f5b5d5655c920f6b5d,0xd97358d20e6f61d7450d,0x520e3f619765cd20f375,0x5897158130e5f61d7559,0x8130fba5c96258130fbc,0xe61d6258130fb65cd625,0x58130dbe65d6258130eb,0x7a5c9425c130bbe69d62,0x25c130f6e5d1425c130f,0xf7a5c9625c130b7e69d4,0x625c130f3e5d9625c130,0xf7650d725c130b7e69d,0x1725c130f7658d725c13,0x30e7e619725c130e7e61],#[0xcd425c530bfce81425c5,0x530f6d5d1425c530f755,0x5d9625c530f755cd625c,0xc530f755cd925c530f3d,0xa5cb9050930f75651735,0x50930df65cf9050930df,0xfe69f9050930dee5d390,0x750930f6b5d172509309,0xf375d973589309fee819,0x435c930e3f61d7658930,0xe6f611745c930f675d1,0x9905c5408ff69b9261d3,0x40f6d5cd425c540fec50,0x55545c540f6d5d1935c5,0x150f6d655745c540fcd6,0x595725c150f5e5d9525c,0xc550e7e619725c150f5e,0xd5d9525c550fdc549905,0x5c550fcd651545c550f5,0x9d659655c550f5d5d594,0x55c950f5d659755c550f,0xe5f619755c950e5f61d6,0x325c160f7a5c9325c160,0xf7a5c9525c160f3e5d9,0x9525c160f5e5d5525c16,0x60b7e69d525c160f3e5d,0x89905c560f3e595725c1,0x560f755cd325c560fbc5,0x5d5525c560f3d5d9325c,0xc560f3d5d9525c560f5d,0xd5d9925c560f3d5cd625,0x5c560f3d5d9935c560f3],#[0x3d5d9955c560f9d65565,0x254960f375d9734c960f,0xf1f5d5655c960f5b5d57,0x4260171f755cd3260171,0x1f5d5d55260171f6d5d1,0x1734c971f3d5d9626017,0x71d7d5cf9050971f7561,0x155450971f6d5d183509,0x971f6d6157450971fcd6,0x5d58454971fcd6115454,0x8971f5d6197554971f5d,0xd6156558971f3d5d9835,0x60971f3d5d98558971f9,0xede818455171d7d5db90,0x611719fde819855171b,0x9fd6979061171d7d5d79,0x71501209fde819859571,0xffc6997154120ffc68d,0x9525c520ff964d425c52,0x20ff964d625c520ff965,0x51435c520ff564d435c5,0x520bfd6a5435c520fed6,0x659635c520ff564d635c,0xc520bfd6a5635c520fbd,0xd659735c520f7d651735,0x5c520f7d5d1935c520f7,0x7d5d9935c520efd61193,0x35c520efd619935c520f,0xbfde8d945c520dfd6599,0x655c520fdd655655c520,0xbfd6a5655c520fbd659,0x9855c520f7d659755c52],#[0x40f7d5d9955c520efd65,0x59525c550fed64d425c5,0x971fbd64d625c560fdd6,0x26c0298000dfd60f9050,0x35605b809e00ff019a0,0x202f20554093010781dd,0x20421703d007260d8419,0xb6415a829684fb097c1,0x6ee0d6219a431605ef,0x17040f87d70f4a1da039,0x1304251448408cb11322,0xe0adf1518291050389bf,0x2106238c0a17842de858,0x1bac36646a88d1419823,0x78f121daa3a607330e29,0x2b082c901c1fa83e307a,0x2480475c8c7913c21e84,0xe93df272e4d10978929e,0x744abf152b29c65214a1,0x2ee05cccb70168d2c5e5,0x6992531a461fcc1617ad,0xbd8d621a71343c6700cb,0x392a7108de19b7b36666,0x39e343bd87638e9d9cfe,0x148ffa1fa13e9c7b94f4,0x43b685f508a20cc411e8,0xa35946388b7d1462223,0x425266248f488e8ffd1d,0x4c8a984d2eb25994a8c9,0xf278c4eb49c7535fa682,0x391453a86a505a9fed3d,0x53e8a6dd4c2a948522ca],#[0x32b885654ab315372a31,0x6c56a9acea5902b0e55f,0x5ee2bc4d75aae6d5c1eb,0xa309760b4c0a17f5afae,0x8418e9b18b629cc44586,0x675ecd71979b295649ac,0xb354e69f6d249a253402,0xc51b5b366e6c4cd779ac,0x717ce181c06b7ba6eb8d,0x3ba7e73fee6b1ca73906,0x3fde45bc0c7788edc5d7,0x7d7efa09f123dc67aa4f,0xe405e802cff39fb2befc,0x9420fec1aa828303e605,0x88370ef61b5431785470,0x145ba8acf1452260c463,0xe2e3a1c6fb8d6719ae30,0x9281238a44d48528fe91,0x54b3795c92a4651f49ca,0x3f66554c6298352f4a5c,0x9d3939266f04d8d9a753,0x1d0469fe73eae7a6ceef,0x8068d7515ba227432e84,0xa7574d8e98dd2bda4bf4,0x4553fa9ef52bea1dd3f3,0xcf2b7a56a1acb357c2ad,0xb1e362a6c2b57f8af1f5,0x75ab1b4916802cd6d95a,0x102df15ba5b6d16caed7,0xbb7d75dae91dcdbb9117,0x25f31bde97ab2f275e06,0x3b3062e07dc0557f32fc],#[0xc38b86230ab612fc2118,0x3e2b4c51b899b11fe218,0xfaf1e26392c6d78ce718,0xc9f792cf240e444c80f8,0xee5f5cb87961b2aa652d,0xce580f06845469631f31,0xc0ce783422a34388c0c2,0x362c6219cf07a3534880,0xc8df00e2c9e8b237c00,0xe4d0591ae2c25963100,0xdf0012cb189047c048d7,0x1c9a0be002148d2c6248,0xbe010d8382208f8091ae,0x31617c684a48e08f8391,0x8006d17c402c84546f80,0x209f423e01468521746f,0x1234290be03468428a4,0xf0c8514595f204fc11f,0x2145161c470676710ad8,0xc368b4d22833339c0bc3,0xe145f8031a18c50c6673,0x8d27a2a14f016349e880,0x48b70e4c46917e020a3,0x60a48bf0057c582b053c,0x1160ac8bf0010caf8b05,0x98d0c63414917e002293,0x45f800a4281a429e0145,0x1bc068b0871484140851,0x6317810a0829e0245852,0xdd8d268209f437e00c68,0x45021bf0062c2f8de010,0x31422f8043762c988a45],#[0x58d26820a1f00100c686,0xc0064836e2c988be0020,0xe0283ef0106dc693417,0x1b71a4d0500fe01c5931,0xfc1bf00634318c0fbc04,0x80398bf0017c380a0f84,0x31c1f0a1837e00c68631,0x8a0c14e78313fc04c686,0xc585f214e783b1a18ca5,0x7c6066a708af86141c04,0xa18c6539457c3701b161,0xb1a18c5539e0c5084031,0x131617c9d0aa73c1925,0x383df1b62c2d949140e7,0x41f78393827f8098d0c6,0xf0e0329cf076343194b1,0x85f2a02c9c00fe18c585,0x50f0131a18c7539e1ac5,0xec68632a6283ef07270,0x4b142db8b2745244539e,0x585f2a02c9cf06e34319,0x3c1b8d0c654c5939e19c,0x1184ff01f012351a0b27,0xa341a0a8a0e03e0245a3,0x18870141f701f0027cc6,0x3f0bb0bd1a3807317e01,0xea3785864182a19c23c8,0xf00a368585a18ce05442,0x17f00a3685c0f1c8800f,0xbf8091bc2c1d0c2848f2,0xe07f8df0142c16122860,0xe00c683e201f09d22086],#[0x1a0f8722703c4fa1ba17,0xd07c391914286e85f803,0x83e1c1e89f837e038598,0x2a0c0f450c1bf01c2cc6,0x3687902710f10f098c2c,0xa3113098a704f83ea166,0xa1e404c53943e85924b1,0xc4642a29c1420fa8598d,0x68e1514e701a16492c68,0x4707a1324e50be02491c,0x403d0a927380d0b248e3,0x42649c13e0f98798de16,0x2705083e61e63785900f,0x323705f80448383d0a9,0xf31b82fc02241e0c8a1e,0xc11f01434278a0f450a0,0x5a1b823e028684f150d,0x290dc1122c62e86f8014,0x7e00360461c3185a0a41,0xf001b01b0e18c2950db1,0x800de0d870a413dc5d0d,0x630d0a2305209462f86f,0xe86871a22383f43e4442,0x43688846202d29c0a262,0x1a4d870d8147c1071b17,0xd26c38710a32703638ba,0x44f10388519381bcc5f0,0xc0687e1ba2c5f0183421,0x550dc14f0142c250dc07,0x61150dc14f0142c250c4,0x13e86c8b50b31be020a1,0x800de11870be1682904f],#[0x5f80828485f0a542ec6f,0x50b413d0d8a12346368,0x1bdc68f63685f800de12,0x37c2c8f0521c2c50bf00,0x1180d017f041bcc6f808,0xd141c1fa2022815d8585,0x23101694e05131b42c38,0x86f0a3e0838d8da17450,0xc105714246a8598da284,0x5ec6d0ba2812070b4a73,0x815e8586f71a386f5381,0xdec50c6f0b218bf8293,0x80087128522e15e4e782,0xdc17f01434278b05705f,0x6c121b82fe028684f190,0x2810d91aa1a62fc04172,0x2f436c5f8009040630b4,0x70a8c342b8c18c1621b8,0x11aa1a62e8b922711091,0x8b8481c3185a53815c50,0x685d0a18d4e057a1b62e,0x6374585a164c58d5161,0x43c2402a28b098370092,0x4c23e0fa4598d920411c,0x648b149636480c24d8e0,0xb8001c916e342d0cc702,0xa168e298916e342d0ba0,0xe8b0b42d1c5206374585,0xf91b51a2e07a38a40c6,0x7d4685a0a2283ef06c71,0x81300e28db161b450988,0x348d0de298b91a2e0378],#[0x246b8b0b42e05d0562c2,0xe0453c1f7172343191c0,0x1a34c585a1702851a39,0x19861101703d067a344e,0x551028b0b4144505da34,0x8b0d8298d0a322c36082,0xc48b71a1685d05634234,0x28e29531ba2c2d0b4714,0xb91a1bc40a8a342d0571,0x68209162e4686f142b98,0xa1302e0ba08c584c1742,0x24062c2e057142891f31,0x880ae484c685c0a82851,0x111cf0307849c8b51a0b,0x3c0a1f12722d4684123c,0x784cc8b51a0b88f040c,0x3322d46841208e782f03,0xb51a1047073e0bc0a211,0x8a4b1a3782f022649148,0x458710884f82f020b945,0xcc983e25bc1030f03235,0x8e096f05e0545c8d0e20,0xcfc0e8d0e262c3010880,0x26946c8b08e4120f040,0x51b22c2211e0bc083384,0x1c9343782f020e51089a,0x50b0744782f020bb46d,0xc189047a080a1430a37c,0x283e82027c8998df0142,0x16168500e637c070b458,0xdf000e2160a01fc018dc,0x3c561be02c586d108fb0],#[0x11a278a0e0c5f80a1a1,0x83fe01c5a2c1686d8bf0,0x5c05435c5f8049e2d0d,0x42c250c62c50780e1a8b,0x11a250b0548b18df01,0x7f0142dc6a2c16c6d0bf,0x1a141e00c5d0d09e300,0x976253398478138bd1a4,0x8fc0411717235cf138c4,0x8a2dc68631c138258054,0xd16e34318e0cec029a42,0x8b71a4f46866684ce614,0x5d1d71a0d0682b053c04,0xc6c8be046849f008514,0xd24d0e4f41a414135e0,0x1a18c6829e0245a1bb1a,0x3b1a18c6829e0245a25b,0xd8d48018c6e05e024584,0xc058b71a0f46135e0245,0x37c038b8804c46a2a86f,0xbe01c6b8b836e64880ee,0xf00e3620134181292383,0x804366344fd8b2203b8b,0x21b31b62c744a0f898f,0xfc058d0c6399907a287c,0xe00cd240201019a31686,0x8018c62680f450d8b31b,0xb07aa846b1b62fc00c84,0xf017176348437e01c6d8,0xc6d151d17527a46a7292,0x2ec6970cd4e701b160f5,0x91a2e24aa714f518e02e],#[0x78c998bb1a9009275496,0x427ec5980b89221c1382,0xc617325439c04c998de0,0x9636c5b25b26389c07c4,0xb1b62d2005f184e20024,0x9ee02664c5d8d2c4f080,0x5944929189c05c873810,0x2e439c0850999e02636c,0x58db16c96cc8e2701ec,0x4058bb1a900a2482710,0xf480cf0b8920a113c87,0x92222e0327a4e38db16,0x88b80c9e93962dc683d2,0x8b61ac258b64a3045248,0xc6863244e5830bf634b4,0x8334382719299ae0262e,0x4e03d142636c599a4804,0x2ec686364b6686866870,0x2202c6d8b48018c61396,0xe02a71c6d8b07aa84814,0x860c762c6216914a8422,0x493ab0b60ec6b2518e35,0xf808a133de010c28db16,0xe00c689fb160c4707588,0x28380d8d0683993e03,0xb91ba2c18c931ccd18bf,0x28d917c044c9427fc011,0x4f0f09311f0213c287c0,0x687143c07c068b31a0f6,0x440a0917e008de8d0692,0x710bd80072a354c70b0b,0x105fc048de160b0ce8d6],#[0x82f237c030b41f2618f1,0x8df000e90df0b930382c,0x6f809301938585a1e0bc,0x385b8791a0b3078e05e4,0x86fc058de160b0682fe0,0x3fc2fc021b31b83c9c1e,0xb1a0b3078c29c1f42c1,0xf80b1bc2c160c86f85f8,0xc018d331c2c2d0d83d0d,0x6f85f80b1a0b3078c287,0x6e37c030b41f27589928,0x41ec2e4eb19209882c83,0x8d07d274605906dc6f80,0x5b8d07d2746837e0385b,0x2c6e87e1669c8837e038,0xc2ec6b0f305169c603a0,0x291a1c500272c104c43c,0x6084ff0b31bc3cab4e49,0x1e4e87a5869c2603e539,0xb0b4389c0a963585d986,0x8541c2a29c142634cc70,0x2d8e4910f582098c2d87,0x9c60b4e0a87d0b71a0b8,0xec786a03a37c029de162,0x53e29c621ec2f46f8094,0x2cd1bc2c6a02a37c070b,0x28de170b0701ee1fc00,0xc1668de162827e1e27fc,0xe0285a98a1e0e87f0161,0x37e038583a93038a151b,0xa1663687a9d2450c8d2,0x83e93a383185827c89f8],#[0x85d821c4ff01e17e00c6,0x70289008f80e87f00e37,0x2404c24f021c111161b2,0xb29384c53960a86b8ba2,0xe87d88d8b61a0c0608d4,0x22c228c5871a1a0c0620,0x42d0ce2c38d0d0603105,0x274278d4560a780a16e3,0x17274278de020db0b71b,0x5617270288e85fc038de,0xd0b71a168722815e0431,0x8a29c0664057a28a728a,0x34199024a0507131b42e,0xe406092560838b0b6296,0x338111aa286368583318,0xd0828a38da160cc638c2,0x78de0021d0b53b634278,0xc160c46a85f8071b2742,0x85ec8146410df80e1b62,0x41d02c44286fc058b61a,0x86ec5f80e1a654160c0f,0x92280c5f8032bc342d0c,0xc44285fc058b61a86eca,0xf80e1b62f0b82c181e82,0xdf8042ec35c5c9d250d,0x5186c3f0ae3134058c6a,0x278c5f0d0b43c0822e1,0xb16c36c8064190e05432,0xa032a62f8685a1d0e054,0xd8b61ac5eca928702b8,0x5c585a201ea1c13815d1,0x15c70a8a7a8ba9cb0543],#[0x82305c4436082a30d62e,0xc0724a2162f62d868391,0xc6229c111a3174368ba9,0x3442c5ec5b0d07231070,0xb0df0122d8bc90074386,0x4a8a0f00a2f86c2c1890,0x808d7803174368ba9d24,0xc150c584c47e28348582,0xf8a47c2618d0a28fc523,0x51f85714900573161451,0xe3645c900d829210a863,0x3d6058e68d71729c80b6,0x2b16a341814118524226,0x48d0c60c0a20b81d0fe8,0x318b891a0c0a20c62c85,0x58c6c8b067254360ee2c,0x44714ad8d5161b062242,0x841255c6c8b06651c6a2,0x8442a6146d8b0725046,0x618b2152341c86393051,0x431a98b16a341c9441a0,0xb0c0385771a1502d05c1,0xd1c184a60a7021b246e8,0xc58602051822f05a2f46,0x80712904a415810d9a35,0x6303314620ac0e8d7161,0x38218a304420b46d1cd1,0x680ac10cc660208c4e02,0x2a02b0445194056386a2,0xe4011381cc99311544a2,0x1f32512540cc1a224383,0x11381cc3062a0110ee0e],#[0xc550221ea188cc0e60c3,0xf59289283c60c2da221,0x21f182213a4450786388,0x2304491208a6086c9611,0x185224114c10d92c2244,0x449607306494918b81cc,0x268208ac0e619928631,0x923c0e60c110c23303e4,0xe1d2544508063882ac92,0x844c94318c4114602208,0x523884b093a89a029045,0xa2680a41072303351940,0x184822682192c230]]
def g255H9 := limbs80 #[#[0xc52e4c21c208f100340,0x33003a40035e000000,0xd8002840020770518000,0x163003ac0028a001cc4,0xd3a9a9532750000ddda0,0x80ae24b518d4827100f1,0xa0000014dc001cc21096,0x8ae70008b93a31000004,0x396e652b3740030fea6,0x41c5d632f0021f45dad0,0x21396c00d5566002879]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0xed2a4a8241fa94250120,0xfbc3ae29077a5c970483,0x72e8b8281dd5735c530c,0xcbaae0a876d5d171503b,0x2ecb82c1d75755c550eb,0xb9a64b8f3d5d9715839f,0xeaa92e3db57450971eea,0x9a86b8f3d5d9625c7aea,0xea1ae3db57450d71eeab,0x2c6b8f755cd635c6beb2,0xaa2e35f59758d71e7abb,0xa8b8f5d5d5545c7b6ae8,0x2ae3d757559571afacba,0x4a157d65d655c79eaecb,0xac7d6d755c952ed6ba2e,0x907fc5c5404839baecb9,0x41fe97250120ff4a9280,0x7ee5d140483f72a8a02,0x1bf98750120bfccaa809,0x5fe65d404837f70ea024,0xfe94254120ff8b8aa090,0xfa5c950483fd2c4a8241,0x796554120fbcaa2a0907,0xe61d50483ef2eaa8241f,0x99754120dfdc3aa0906f,0x54970483fd284b82417f,0x835c120ff4b12e0907fa,0x1170483bf2e8b8241bf9,0x55c120efcbaae0906fe6,0x970483bf2ecb8241bf98,0x5c520ff2a12e2906fe61,0x71483fcac4b8a41fe552],#[0xc520dfac1ae29077d5cd,0x14837eb08b8a41df5745,0x520dfac2ae29077d5d57,0x4837eb0cb8a41df5765c,0x20fd6aa284906fd66171,0x82fdb2aa1241fad74509,0xdf6c3a84905fbe55424,0x2fdb2ea1241bef875092,0xfb6aa2a4905fbe5d4248,0xfdb2ca9241f6d7554920,0xf7c3aa4906fb61d52482,0xdb06b12417ed9754920d,0x6b2ac4906fbe0d624837,0xb0eb1241eed7658920f7,0xcbac4906fbe1d624837d,0xe8b9241bed835c920bf6,0xaae4906fb61172483bda,0xcb9241bed855c920ef6b,0x286906f760d434837db0,0xb1a413fd9850d20ddfc2,0xe6906f760d734827fb30,0x1a413ff9460d209fecc2,0x6904ffe5d834827ff2cc,0x2413fd96e0d209feca70,0x906df6155448377b08aa,0x41bbd845d1209fecc2a8,0x4ff661744833fb0eba2,0x13ff95611209ffc9b089,0x4ff64f844827ff2ec224,0xb7f85595209fecaf0890,0xff661654835fb0cb2a41,0xfd875d520dbec2aea904],#[0xfe51854827fb30baa419,0xf97615209ffcb30a904f,0x65b854827fb29c2a413f,0x985d920d7ec32ec904ff,0x55864827ff26c32413fd,0x3e19209ffcbb0c904ffe,0xf874827fb2bc32413fd9,0xe1d209feca70e904ff64,0x604c27fb2dc3a413fd95,0x8130fec992c0987fc5c5,0x4c3fb2e6b0261ef9625,0x130dfcc3ac0987be5d96,0x4c3fb264b82617f99758,0x30feca1ae09877e5c970,0xc3bf2e8b8261fd9635c1,0xefcbb2e0986fe611704,0x3fe320b8a61bf9865c13,0xfeaa1ae2987f54c9714c,0xbeae8b8a61fd5635c530,0xfabb2e2986fd611714c3,0xeb30b8a61bf5865c530e,0x6b9264987f3589324c37,0xb2899261bdd844c930fe,0xc3a64985f7659324c2fb,0x20a12617dd974c930dee,0x3a86987e75d1434c2ff7,0xcb1a617dd9750d30deec,0xac6986f761d634c3dbae,0xb9a61bdd845cd30beecb,0xe8986f7619734c3bbaec,0x22613fd985d130ddec22,0xc984ffe5d844c27ff24c],#[0x2619fd875d930d7ec32e,0x984ffe49864c27fb30bb,0x613ff9261d309ffcbb0c,0x4ffe59874c27ff28c3a,0x1df9725c140fdca12e0a,0x77e5d570503f72a8b828,0xff1905c540dfcc2ae0a0,0x7d5cd71503f6a84b8a81,0xf5755c540fdaaa2e2a07,0xd661715037eb0ab8a81d,0xd8550940fd6b9284a06f,0xe5542502f7b2aa1281bb,0x9750940ddec3a84a05ef,0x5152502f7f2ea12817bd,0x45c940dbec2aa4a07cf5,0x5545033fb0eb9281dbd7,0x55140ddec3aa8a07cf5d,0x7550377b0aba2817bd97,0xc1509fecc2eaa06df615,0x543bf2e4b82a1f79525,0x150efcba2e0a87de5517,0x543bf2ecb82a1f79655c,0x50ff8c82e2a86fe61970,0x43eeaa8b8aa1f75525c5,0xfbab2ae2a877d5d1715,0x37eb0cb8aa1df5765c55,0xf9eaa284a86fd6617154,0xedae4a92a177d9550950,0xbec3aa4a85df65952543,0xfacab12a177d9754950d,0xebaae4a86bf61962543c,0xae8aa2a19fd875c950eb],#[0xcbaa8a86df61d54543e7,0xeb2aa1e7d7659550bbe,0x32eaa85df65d655436fb,0xbb2a1afd865d950dbec,0xb0ca84ffe49865427fb3,0xb82c1ef9625c1609ffcb,0xe0b07be59570583bf2e4,0x8ac1ff1905c560efcbaa,0x2b077d5cd71583deac4b,0xac1df5755c560f7ab2ae,0xb07bb589325837eb30b8,0xc1eed7258960b7ecb2a4,0x5bf65d625835fb0eb12,0x1e7d7559560e7ebb2e6b,0x5bf65d655835fb0eb2ac,0x3ff9361d609ffc930eb0,0x7b5c9325c27ff2ac3ac1,0xbd7450970ef6b9284b87,0xb5c9525c2bfb2ea12e1d,0xd9754970ebebaaa4b877,0x5d9625c3bdae4b12e15f,0x7450d70afecbac4b873f,0xd1545c39faecb1ae1dbd,0x755170ebebaaa8b876f5,0x9655c3afaeab2ae15fd9,0x60171afecbacab873f5d,0x805c7beae6c02e3bf582,0x171dfac2300b8f7d5d1,0x5c77eb0ac02e3df5756,0x971dfac3300b8f7d5d98,0x5c7fcb04992e3fe5624c,0x71efaba264b8ff550d32],#[0xc7beaec992e37f5944c9,0x1bfacc264b8dfd659325,0x7fcb04a12e37f7905097,0xbfbc9a84b8f7d5cd425c,0xbeaeaa12e3fb55450971,0xfbcaa84b8dfd655425c7,0xef30a12e37f59850971b,0xaaa2a4b8ff9609525c6f,0xaeca92e3df57454971fb,0xcc2a4b8dfd659525c7be,0xe6b12e3fe58258971bfa,0xaac4b8fbd595625c7bea,0xc12e37f59858971efab,0xb04b8f7d5cd825c6fef2,0xc12e3df57460971bfbc9,0x4b8dfde51825c77eb08,0x12e3bf58560971efabab,0x4b8f7d5d9825c6fef2ac,0xae3fd58350d71bfbcb30,0xb8dfd661435c7f6b08a1,0xe3ef58658d71feac1ac6,0x8f7d611735c6feb30b1a,0x3df57460d71efac32e6b,0xefd619835c7beaecc1ae,0xf758555171fdac22a8b8,0x7d615745c6feb30aa2e3,0xf79261171bfbc8308b8f,0xd5d5845c6fef26c22e37,0x58559571bfbcab08b8f7,0x661655c7deb0cb2ae3f7,0x7661571efac32eab8dfd,0xd9624cbf9ae6b1265df5],#[0x758932df6c3ac4997bb5,0x1724cbf9a86b92657ed9,0x5c932df6c22e49977b5d,0x434cbf3ae8a1a65bed86,0xcd32beecba86996f761d,0x34cbbbaecb9a65bdd845,0x132ddec22e8996f76197,0x4ca7ff20c22653fd985d,0x32d7ec32ec994ffe5d84,0xca7ff20c32653fd985d9,0x29ffc830e994ffe5d864,0xa7ff2cc3a653ff9461d3,0x9fec9f00a16fb5cb8050,0x7fb2fc0285bbd74e0142,0xd6aa2e4a16fbe0d7250a,0xdb0ab9285ded755c942f,0xec8706a16fbe157250b7,0xb2fc1a85bbd74e0d429f,0xc3aa8a17cf5d55450a7f,0xaba2857bd9755142dde,0x2aeaa16efe157450b77b,0x1c2a853fd985d542dbec,0x30ea14ff65f8550a7fb2,0xc3a853ff9361d429ffc8,0xea14ff6438750a7ff2a,0x92a5f6d545c9529fec9f,0x8a96fb6197254bbdae8b,0x2a5b7d8755152f9eba2a,0xa96df6197554aefb2eaa,0xa53fd985d952d7ec32ec,0x14ffe5d8654a7ff20c32,0x5ded755c962f76b2ae4b],#[0x79f5d56558b9faecb9ac,0x6fd9759562d7ec3acab1,0xffe4d8758a7ff20c3ac5,0xbd7450d729ffcab0eb14,0xf5d5545cbb7ae8aa2e5d,0xd7559572afecbaa8b975,0xe498750e7ff20c3a87d7,0x9261d639ffc830eb1cff,0xd950483ff2e6a02413ff,0x35c120ffca1ae0907fe5,0xd71483ff2cab8241ff96,0x5c520ffab1ae2907fd50,0x71483feb28b8a41ff593,0xc520ffacaae2907fd595,0x2483fdae6a1241ff5965,0x920ff6b9ac4907fb5d95,0x483fdac6b9241fed435c,0x20feeb9a86907fb59572,0x837fb0ea1a41fbd7450d,0xbfecba86906ffe1d434,0x3dfaecb1a41fdd7358d2,0xdffc3ac6906ff61d6348,0x7fb08b9a417fd9758d20,0xfec32e69077f5d973483,0xfaecb2a41f7d7559520d,0xfc3aca906ff61d65483d,0xaecc2a417fd9759520df,0xa12e0987fe5c9604c37f,0x84b8a61ff9625c130ffc,0x92e2987fd589714c3fea,0x4a1261ff5945c530ffac,0x284987f75cd424c3fdae],#[0xa1261bfd8750930fdeba,0xc4985ffe5d424c2ffb2e,0x1261fdd7358930ff6b92,0x4986ff61d624c3dfaecb,0x261fdd435c930bfecbac,0x9877f5d1724c3fbac6b9,0x81bfd865c930dfec22e4,0x7fd65571503feb26b8a,0x1ff5945c550fdeb9a84a,0x7df5d952543feb2cb8aa,0xbfd865c950fbeb2ae4a8,0xff65d865437fb24c32a1,0xf9525c160ffc992e0b06,0xd54971583fea64b8ac1f,0x5935c560ffac92e2b07f,0x5c932583feb2ab8ac1ff,0x764c960feeb9a64b07fb,0x5d325837fb0e992c1efd,0x554960ff6b92a4b05ff6,0xd52583dfaeca92c1f7d7,0x58960bfecbaa4b06ff61,0x72583dfacab92c1efd73,0x1d60dfec9b0eb077f5d5,0x25c3bfaec992e1bfd956,0x970efea1ae4b877f5d95,0x5c7bfacab92e1dfd635c,0x71ffaa1300b8ffd4c980,0xc7feac4c02e3ff552601,0x1ffac1a84b8ffd611325,0x7feb08a92e3ff5855097,0xffac1ac4b8ffd619525c,0x7fae7c0285ff58558971],#[0x4480368026001300003,0xa880958080006d00578,0x10280f200df00cc00bb8,0x16e0158813e012881130,0x1e381ce01b6019e01838,0x24782348221820e81f90,0x29a028c027e0270025d0,0x2d882cd02c182b382a58,0x3260318030a02fc02ee0,0x3738365835a0349833b8,0x3b983ab839d838f83818,0x40483f403e383d583ca0,0x45e844e043d842d04178,0x4b884a584928484846c8,0x512850484f684e604d08,0x556054305350529851e0,0x5a605980587857705668,0x5ee85e085d005c205b40,0x63486268616060a85ff0,0x67f86718661065306450,0x6c306b786a70699068b0,0x70406f606ea86da06ce8,0x74a073c072b872007120,0x78d877d0771876387558,0x7ce87c087b287a487990,0x80f880407f887ea87df0,0x850884288370826881b0,0x894088608780867885c0,0x8da08c988b688ab089f8,0x92c8919890908fb08ea8,0x981896e895e094b093a8,0x9cf09c109b309a289920],#[0xa290a188a0089eb09dd0,0xa808a700a648a568a410,0xace0ac00aaf8aa18a910,0xb2f8b1c8b098af68ae10,0xb8c0b790b660b558b428,0xbe60bd58bc28baf8ba18,0xc388c2d0c1c8c098bfb8,0xc950c7f8c6a0c5c0c4e0,0xcfe0ce38cce0cbb0caa8,0xd648d590d4b0d358d188,0xda80d9a0d8c0d7e0d728,0xdf80de00dd20dc40db60,0xe688e4b8e360e208e0b0,0xec28eaf8e9a0e848e768,0xf290f0e8efb8eeb0ed58,0xf9e8f890f710f5b8f438,0xfe70fd90fcb0fba8fac8,0x349026901890058ff50,0xa0108d1075105f904c9,0x10690f890e090c890b09,0x1659152913a912a11199,0x1ce91b9119c118911761,0x21c120e120011f211e41,0x27d926a9255123d122c9,0x2d512c712b692a612909,0x318930a92fc92ee92e09,0x36b13581345133493269,0x3db93c393b0939b13831,0x429141b140d13ff13ec1,0x46f14611453144514371,0x4ba14a99499148b147d1,0x51694fe94f094d894ca9],#[0x55f15511543153515271,0x5a2959495841576156a9,0x5f515e215d415c615b59,0x638962a9621961396059,0x68396731665165996491,0x6d616c096b2969d168f1,0x7379724971196fc16e91,0x79417839770975d974a9,0x7fa97ea17d497bf17a99,0x85c18469831181918061,0x8bb18ad189a188718719,0x90118f318e518d718c91,0x9499939192b191d190f1,0x99499869978996a99579,0x9da99cc99be99b099a29,0xa1e1a101a0219f419e89,0xa6b9a5b1a4f9a3c9a2c1,0xaaf1aa39a981a8a1a799,0xaf29ae49ad69ac89aba9,0xb311b231b179b0c1afe1,0xb7e9b6e1b5b1b4d1b419,0xbc71bb91bab1b9d1b8f1,0xc0d1bff1bf11be31bd51,0xc581c479c371c291c1b1,0xc9e1c901c849c741c661,0xce91cd89cca9cbc9cae9,0xd409d2b1d1d1d0a1cfc1,0xda71d8f1d7c1d641d539,0xe179e071df19de11dc91,0xe831e701e581e479e321,0xeec1edb9ec11eae1e9b1,0xf579f3f9f2a1f121eff1],#[0xfc31fb01f981f851f6a9,0x1d200c9ffe9fee1fd89,0x88a06ba058a040a0302,0xf1a0d720c420aea09ba,0x155a1452132211f2109a,0x1bc21a1a18ea17ba168a,0x21da20aa1f7a1e4a1d1a,0x28ba27b2268224b2235a,0x2f722e422cc22b6a2a12,0x35b234823352322230a2,0x3b7a3a4a391a3812370a,0x416a403a3ee23dda3cd2,0x4782462a44fa437a424a,0x4d724c424b1249e248da,0x52c251ba50b24faa4ea2,0x58625732562a552253f2,0xe008d045631e5a9a5992,0x522f800515f1c270978b,0x7e378be00401825e341,0x3c75a49ce378b4945548,0x1b0827382e341e42c734,0x11f8206c1f0478be010d,0x6f206ce089c07f8b4351,0x7e081b08014e378042c,0x5c71bf822738d0810b45,0x45c6e081b0878be010d0,0xb1cc901f8227021e2d0d,0x1f2346f1c1ce341e1b08,0x38d22c9518a7a0b8b470,0x7021e2c8d26061b11c08,0x1311c0788ba3493206f4,0xc4701f2368b24c8e0b81],#[0x811311ca368b2b82e044,0x48b264807c1e188a4e0b,0x2c992382e04544701ea3,0xa2cae0b811511c0848da,0x786729382e04544728d,0x11451c07c8da2c962421,0x1c0808ba34962471e0b8,0x28da2c462071e0b81145,0x348b26881c782e045147,0xa2c9a2382e045747020a,0xb1207e0457473820848d,0x1f93c7e0b8115d1ca368,0x20928709c1de2d0de00,0x2f8006480778d0550be0,0xa34711f82e04210790d8,0x162c5f143067180e0e11,0x808468d474521780a361,0x34711383e008d1a47117,0xb80a34691c45e00112,0x5f1a448478006e8d1485,0xc48e028d10871128de00,0x143367302603868528b1,0x463463168be021463463,0x808528b474521780a2e1,0x2d1823806348b1a47117,0x1c450d2250509ae018d2,0xa2c1b1486c0b800508b,0x45a2f8018c6913028538,0x6d8d18c5c0a8be00431c,0x4578086d8b17c5e0f808,0x8b17c5e0f801018d18c5,0xd8de00401c45e006486d],#[0x103ee0f8086d8d18c660,0x62c5f1c0562f8010071,0x64e2f802858d100601f8,0x8c70fb83e021b6346318,0x17c80c29ca0383c058d1,0x31833a7115a0386c058b,0x8b1006a7280e0c406346,0xd8b17c64182e2709ee35,0xc9c634401c4501f0116,0xa728007383c058d18c9e,0x7e189c62c401c450f822,0x7a7007a038662c5f1c0,0x8c919039270a1e2d8d10,0xf822a728007383c058d1,0xc0b010ba870e4330c080,0x5e0f01e008d0e063182d,0x43d0e0527f80c048d18c,0x128d62c4b18c462f80c0,0xde006312c4e011ba3434,0xc381f80a370127c34168,0x585f1a2508f83e028d46,0xc04a017c66378022f012,0xb637012683d1815e008b,0x15c07800768b0c46e028,0xc4451615e0025a2c5f16,0xc068d62c3d1780a2f010,0x631818e028d62c401780,0x44018c50698be0114234,0x7800768d0d062878023,0x41004e0025a3463103ac,0x8043d8b0c4641b80a343,0xd0627d8de0040148501f],#[0x10052143ee018d875110,0x7e018b0c47014a062f80,0x850fb80c068763434180,0x28b500403f8022e8d0f,0xd1701e028ba343d148de,0x8b0e85f1b01e028da2c3,0x380a2c311a8401f01e00,0xe00491904a2f801245f1,0x40fb8de028b0f4491a8b,0xf800e84017806368b100,0x1701e028b23463158da2,0xf4691301e028d22c5f,0x3e27f01e008d18c6a2f8,0xd06d109fe001ba345214,0xc078062e8d0f85e028d0,0x6312c4a358be004b18c5,0xb0162f80a343e1a8de00,0xa3540138062e8d1004c0,0x5c0780a2c8d18c522f80,0xc5f1c05c0780a368b0f4,0x838006e8b148601f8022,0x17c5e028b0c47013022,0x8be018d1c046368be005,0x368b1004a2f8017c5012,0xd18c6e018da2c4013806,0x8d0d074103ec07802848,0x8c4c078062e8d0f85e02,0xe028d18c53118be00531,0x401702c058be028d0f86,0xf800e8491514e018ba34,0x17c46378012c63128762,0x7e018d14c63118be0050],#[0x66019c15217a370b190,0x620f1a01a378042d1019,0xe011e0e8605c8de030b2,0x723780c2c641617a350b,0x785c1ba3780c2c3a181,0xb0506c171d28de030b19,0xc2c9d83c64438042c641,0xb42f806343e1f8d06f80,0x1b42f806343e180f44e1,0xc9fc2f801b18d83c7466,0x183de021bc2d8d0f8606,0xd0f8683c1b63780c2c64,0xb16c54143de021bc2d8,0x5011910b16c6c1408133,0x6345b151343d0b6345b1,0xc27f0b6370f2119c050b,0x1c2d8d0f89c086c1309,0xf0f19060f502a029c133,0x70b6343e24542718dc2,0xc2c39203d40a80a7054c,0xd16850f42f40b01a1c30,0x8082c4a190403f8082d8,0xf86c060be02826343e1b,0x6343e180182f800b18d0,0xbe003a1a850078082c2c,0x161f8082c3a128600a0,0x3c3e1d0fa3780c2ca714,0x928d201327e0be008d8,0xd83c70c613c041ee020b,0xf0f870b1870920be028,0xc24a347064a182f80236,0x28d83c78670107b8082],#[0xe018d87870b1870920be,0xbe020f0e860f7010920b,0x2482f806361e1ca16360,0xf0be010f2343e1c3dc04,0x68709380c2e8d203d27,0xc0780c2e8d0f4508c02c,0x708c02c070be028d0f87,0x860f4a1c2f802350f0f8,0x370b20a1a370be010f0e,0xf4508c02c068709380a,0xbe028d0f87c0780a370b,0x87e030b0c4608c02c070,0xe88c2f806346a1006c06,0x142300b01a1d8dc2f800,0xbc34681783e010d1bc6d,0x804346862e1b209de001,0xf801b30d2808458631b3,0x378086c3622111486f62,0xc343f14461bc6c1a18bc,0xe0d0d1bc6d1c084444c,0x9c27b0d62f11229c4068,0xd8b43511458a1b302130,0x2f112b82a00711b051a1,0xc46cc086f1449c2830d6,0x1b29c1458bc36874d8b1,0xe2730d0cc81c46f40a80,0xd2744f143d0c902c042,0x685e020d0d86f1211e02,0x8358b1b44007808358b1,0x4f14021bf808346d1780,0x780844381611e0187834,0x14164348be006c158783],#[0x43468170d22f800d86c,0x82e030d10868168207f8,0x4680588be020d844a026,0xb068e020da2c421c5a1c,0x1a28b837808444620711,0x862e0de021f0d881b071,0xd22f802803620711b06,0x28be030d10cb1c46f1a3,0xb051bc021d8711b3821a,0x6f0b1a0545414e010b1,0xfe010b1a18d86c827780,0x8de006fc2c9f211617c6,0xf8042d8d86c7850521b1,0x37801bf0b28470511a1b,0x1bf806370b86c806e146,0x415f0b0fc511817e0858,0x80457864510b1b070211,0xc51a1d8d42d14458aa72,0x7f0b637142b82a00711b,0x46891c46fc086c1449c2,0xa03821bc57a1d8d42d14,0xfc0857270a1c2d8dc508,0x82a728715c6f6370b246,0xb0127039c2c302117a03,0x350be00381bc50f43540,0xd12860078042e8d16852,0xb6345a14158538082c9,0x615e020b10c6c1780852,0x2346f1a14e020b1144a1,0xc2c8d1bc706898e010b,0x20e010b1a0506817a0b8,0x7c9a0b0be00431a05a08],#[0x68711a016e008d82e142,0x1c46f1a38082e8d10c71,0xf1c468a360be02141188,0x206b802360b850a1246,0xe1ae020ba34431c5a13f,0xbe8de020b8504819021b,0xe09171bf8082d8d88091,0x71bc8de030b28491601a,0xbe028d10c91601ae081,0x70b0f4519458123821bf,0x1e8dc2f801607c0780a3,0x60817e010d1bc60086f6,0x9e2c1b85f80c349d1b83,0x5ae091a05f804358b86c,0xe171bd8be030d280718c,0x1c0845c57c343f150606,0x71e9ca0383609174346f,0x1a2f021509c27b0d62f1,0x9ca038215e8762d0d45d,0xc9c2830d62f17206316a,0x6870cf0d0b88c086f15,0xe010da2c5a143d0ed02c,0x4f1401e010da2c5a1490,0x20d1bc741617e020d274,0xa17e01878344f1802e0,0x24212790de028b45c6a,0x3169820688be020d85ca,0x17e0821e020d1be8b206,0xc2c8368be02171207194,0x9003c0687e030d0d0718,0xb01a1c24e030d62c80,0x60086fc378062c651823],#[0xc6d141d2438046e8b128,0x8d1bc6d101be028d13,0xb128520f8046e8d13c5e,0x20e008b1b052578046e8,0x3c51178046e8b1285254,0xe008d1bc52638046e8d1,0x3a0b8046e8d13c626021,0x1f1b28b2378046c931c8,0x45a0868b2378046c991c,0xc46c07e8b2378046c962,0x828d22f8046c96244f1,0xda2f8046c46204a1c46f,0x8de011b26871bc711b28,0x68be011b26890806f22e,0x11b12061684fe082123,0xb833820301c6fa368be,0xe1518b0fc4c170760839,0x83f151f1458d0fc4c151,0x5d8b0fc51145a0cd8d0b,0x4143f0e58b0c04415201,0x8d0b847152115d8d0fc5,0x7001518da2c5a16810cd,0x6345b140e1528b1684c1,0xca418da2c6c14932408b,0x6073001328b6345a191,0x2c5a18544718da2e9019,0xc28b1685073001518da,0xce0d81c1e8d2e0909839,0x4ca345a14450f822c031,0x44c4728247a8d62c9038,0x4ca358b1b46a9c3de0,0xf17002358b2e06f141cc],#[0x8b2e05a14b84718ba346,0x30018e8d62c6d1700a35,0xa34331b440b833a345a1,0x6c180e15e8b16851142e,0x68b1b0525b001458d22c,0x7121a2d8da5474729563,0xc00576368b1686a04574,0x5714290e430a2c5a141c,0xa8d62e981c0e1528d168,0x5c8d62c6f1a811511c47,0x4729862e8d1bc526b001,0x6c1ac30f0330ba8d1685,0x5060385462c4c1ac51bc,0x1446c180ea084c62c3e1,0xe634331b040700e1318d,0x46f180e1458d1305c142,0x2c301bc40700e15d8b14,0x7200e1458b15c5c14396,0x50700ea0521a08546345,0xe8d10480385763454170,0xb85b1c09e0830e049322,0xa346e1c12e0b812368b0,0xba34412028e0b8108a8b,0x2e16c70e409e0b812648,0x68b1d4703382e048da2c,0x368b1b870ab82e0422a3,0x6368b1cc704b82e042e6,0xfa2d8d1047e0b8111c2e,0x21a2d8d1047e0b810c11,0x422a2d8d1046e0b810e5,0x591ca2c8d1c4332382e0,0x2587122e8d110804b822],#[0x147022a368b200a0c382,0x7162e8d11080dc71e0b8,0x46ca346e1a1fe0b810c0,0x1c5aa34631b842178260,0x32412e0b8162c2ea343e,0xc04a81e08714818ba343,0x12e0b810ce8d62c60201,0xb810e49a22e8d11081c4,0xcf822688da2c47200ae0,0xe051c08a8da2c8033810,0x38818da2c471c3d0af82,0x394868b634441f82e043,0x618e010ba345a1782e04,0xc2c2c1610e008dc2c5a1,0x61e8dc2c2c178061e8d,0xc4a158de010b0f84a178,0x770b6342c158de009fc2,0xc17808758dc2c2c17808,0x8d82c4a1413e008d82c6,0xa0ba37800906c1987e02,0xe8701f8082d8d168500,0xd1685078a16360be0210,0x802370b168501f8082d8,0x685a1f80c2e8d0b0501f,0xa344e1685a370be004e1,0x501f802370b1685c2f80,0xc5a1585a1f80a370b0b0,0x28dc2c561685e028dc2,0x7c2c4a1780c2c4a1784e,0x3ac2f806345e158de028,0x343e170de011d0b03814,0xe010d26c38198be002cc],#[0x361f0de00380b070f91f,0x44f1b80c358b1b440900,0x830d13c5e0f804343887,0x62f80875160b0662f802,0x6d138062e1dc344f170d,0x3804368b1b44e030da2c,0xe00381bc5e030da2c6d1,0x561e8be020d13c58348b,0x18b1685a2e0de00461bc,0x160de018b1b4401e0de0,0xb072100722f80c345a,0x44f170da2c4b18c4a2f8,0x287c344f1987a2f80c3,0xf1780c358b1b4409003e,0x800e03d1d8be0287c344,0x687e004e182400d81c37,0x378042e1d12860918bc3,0xc158de009fc2c4a15166,0x8082c6c17808758dc2c2,0x68de020b1144a1416237,0x6345a168d82f801186c1,0x7e008dc2c5a1518e020b,0x45a1687e028dc2c2c140,0x30b1645a168dc2f8016,0xf158be010d8744f168de,0x80a2d18198be00a0c344,0x38022e0d1bc60849e437,0x1587e028b8344f141a86,0x7c344f1a0da2f801206f,0xde018b1d0409003e028,0x7493198be0287c344f17,0xe008d1a0507c8de028b4],#[0x50828de008b1a0507e8b,0xe8d4746a368be00461a0,0x2f80c34621c2026b8022,0xa1f0bc342c14026046cc,0x300981e030dc2c671f80,0x59e2380a1f0dc2c2c142,0x8c78c625c0b8062e8d84,0x90066870285380a2d8d1,0xb86d99243ee018d62d93,0x631e250f425c0b806358,0xe40259a81d8be018d900,0x42e8709ca003e6358b64,0x961cc0b016358ba1d993,0x900c12725272800f42e4,0x118222270661b046118b,0x4018c8249832718d9007,0x71189c81e806698b636,0x364031ca2298662cc490,0x205b0888cc1585c0d836,0x89e2588f8062f01a359e,0x9e2615e03016368b0f46,0x2588c3ac0780a358b861,0x43181f806358b64e401e,0x9423c07806358b875992,0x62f800d18d66a401e250,0x427893e008ba35401e07,0x124f8023702a2c9f282,0x28b0c69350060f9250c7,0x1e8da2f80496931e8de0,0x24e8ba37805005f1c246,0x2c0780a348b27899249e,0x80c048da2ca1202488f0],#[0x28da2d1ba6490f702267,0x125a6474944008d1de0,0xa2e8d500a09187a368be,0xe1c67090a12789908f80,0xa12424c0780a2d8d0f69,0x3a0f70227b80c058da2c,0x24c0780a2c3d6369e1c,0x1d252688bc0780a34632,0xd0a1a2f802349a50084,0x5a2f80a3434a6940183d,0x14018c6a2f80a352518c,0x368b0f5a11e8da2f8032,0xe019dc2c641850c07806,0xcc2f806360f86c985e8d,0x80c2d9816870f8a76082,0xb0ba1d8dc3cb83c87637,0x687a012c69c3ea704c60,0x1507a0054a718dc2d981,0xf16c82383ec3c4cc2c5a,0x2c1c5a249820bb0b6370,0xd1e2827c3f802770ba34,0xe2328c24a090be028d43,0x9e82c2f802349fc3c9a9,0x9380c2e8d16888b03e2,0xbe028d0b30f1d1e43c5d,0xba3780c3ca71c2461f0,0x380c2e8d2742c182461f,0x378042d0fa611e0e8726,0x287802370b2630f1687a,0x708e8de030b46c3aa607,0x4a09380c2c9da342cc3c,0x28209113e010b6350fa7],#[0x378042d0f4669d20310b,0x27f806370b1287a082c6,0x1e030b6343ea747c3e82,0x1e030b6343ea74708f0,0x7020c18bc3711304708f,0x86f62f0d0c311310922,0x62f808361167881c48ac,0xcc2f14634332e2c89e82,0xc71c7118092c09821b09,0x45a188cc098dc2c33c50,0x369d13c885614e020b63,0xa744f211aa0a01e010b6,0x81bc846917a0b806370b,0x58245914c50a3780c2c5,0x65123821be8dc2f8010c,0xc3a85f8062f0d6405a1c,0x261721f8062f0d6545a1,0x872801530d62f1764064,0x8705762f0d6545a1c5a,0x5c23b1715f0d168541e8,0x89c098bc3439c5cc11c,0x2b021bd8bc3439c5cc42,0xa1890e030da2c2c19062,0x9019072430de008b0e85,0x69016870b28b4378045e,0x2c2cc5c845c64a2f80c3,0x2542c185e0eb80c349da,0x22f0d1686e028b2770d,0xda2d2145e9520952838,0xf80c369516870f42ce01,0x28bc342c314548517a2,0x67a8285f808358b1687e],#[0x40b11ae010d62d17a749,0x8be03172770d13c7a083,0x45519380c358b1d08281,0x86fe030d62c65206717,0x63780a405a190616048e,0x180780a2d8da545a1e8b,0x1b6378062e1d64c4a1d2,0xc2ce018d62e1d86d991e,0x199a86d8be021d6344f1,0xf14468205b1318b8fc54,0x8b8fc511a086084c6363,0x8546363f15c68218215d,0x48906368b0b86c1e0860,0xa068262e8d0c1411c5b4,0x629d0a62e8d0c06f1909,0x5471c954498da2c331b0,0x61411d0ca058da2c33a5,0xe46f1909a0439a358ba,0xde0227678742898a358b,0x928162f0]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x20201521001113200000,0x3400511047418010014,0x44232003021130212,0x14000701002100000,0xd96800000091f3101130,0x40000000000002590000,0xcc00000000054d,0x5950000a7c00,0x23000000000000000000,0xa4c0018780005a340011,0xc24800000000062fa,0x41a400000000000038cc,0x0,0x0,0xf16c4d800000000,0xa63af956e000c32f0f80,0x985e678a3800206860a1,0x15960006408002,0xc00114e56d20040014de,0x10000001870000000183,0x29f8cd0928c01c0016c,0x39a6a7845000000000,0x34800069600000000000,0x302d3acc70000000a84b,0x1772d0000000,0x26b53072c4000ee1000,0x220,0x18fd000536400000000,0x40689800000000000000,0x1606b649980804fc0006,0xc3a25d8003,0x836b688003149c53],#[0x1d635aa000000000,0x59400,0x8264800000000000000,0xb98001f48b92c9d00007,0x77c2d7000084eaa7f,0x15590000002880,0xe6390004990000000000,0x2e2000000000030d,0x19490181a54ed054e000,0x63000000069f000316e8,0x1b12b,0x328e1fc0000000000,0xd424c51618000,0xf250000000000000000,0xc71898c0000000000000,0xbff8c7505d9845c00043,0x2a4000000000000004,0x3d0003b3a9100000120,0x5c4c0000001158002c62,0xd0b8768001491e958aa,0x84694c000000,0xd0000000000000000000,0x301d08b74480034,0xa120006217d360000,0x6a705d20000000000,0x8000000b7580018a8132,0x10005020000000000050,0x5c38001f2,0x87d0d108ec8800000000,0x126300400075140002,0x386c0000000000,0x0],#[0x1c7186d907a63a000000,0x4a2819fb3d24efd2400,0xb4000502800000000000,0x6af4e,0xc280000001a3c0,0x16aa1370000000,0x400134d0000000000d2f,0x2d4a000000493,0x7a820fc00000,0x130f0ec00022e75a80,0x352e0006a528642320,0x9446a898700000000000,0x9446aad94bb69cacc001,0x49600029ba000341,0x5d0d84a000000000000,0x1e6a9638000a1427300,0x430a3000000060331f5c,0x213e4c5952e,0x294e0000002458,0xa01a0000000000cbc000,0xa7d8000001c16f08048,0x0,0xc9d000000000039400,0x0,0x6f500000000000000000,0x80000000002a001dc001,0x16f900000000000ef73f,0x51800,0x70d000105400000000,0x50100000,0x5e60000,0xeb90000000],#[0x0,0x90000000000000000000,0x6c000000000000000085,0x2700000000000000000c,0x2a7200000000000003,0xb8083e80000003738,0x9360000000b508000000,0x4a3c0ba000172,0xb000027e000000000000,0xdae9c540002d777,0x470000000a30e5943b80,0x522000a2b800000173b7,0x14dfd760000,0x400000000000000010f7,0xe838000001e56649290,0x54000000000000000000,0xa973b5adc66bc00071,0x4144f200000033fc0000,0xcad51a8000000e63a4a0,0x285f,0xf740bc000000043e,0x4288e25669b1400,0xa0b213800000025800,0x5ab800000020fed6c0,0x9e40aa0005aa00000000,0x24d44285d0cc0,0x2430a7a2824ce389970f,0x390c000000272000,0x42c000000000000,0xac000000000000000000,0xa,0xf5c0],#[0x800000000000011d8000,0xb110000000000614,0x37d5c00000000010dc00,0x86c13875445c000000c8,0x6e00000000000006abd9,0x147b7,0xb9200001a811e0000000,0x1ea0,0x7b510000000000000000,0xe2100001c8001e4,0xa290003c97cf400000,0xc6843a00020880030da0,0x39e0264001f296383,0x1d520001018000000,0xc09a363a68001845000,0xd95800000,0x18ab4dc00000,0x14a600000000,0x1922d00004ab0]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0x5d571df5745c77d5cd71,0x483fe50120df5765c77d,0xff571483fe5c120ff950,0x58920fed52483fb50920,0x482ff60d20fed72483fb,0xbff84482ff61120bff83,0x61920bff85482ff61520,0x482ff61d20bff86482ff,0xff9704c3fe58130bff87,0x50d30fdd324c3fd5c530,0x4c3f75cd30fdd634c3f7,0xbfd874c2ff61930bfd84,0x50940ff571503fe5c140,0x503ef5d140fbd54503ef,0xff970542ff61d40bfd85,0x55150f7d52543fd5c550,0x543df5d550f7d65543df,0xff970582ff61d50bfd86,0x59560efd62583fd5c560,0x5c2ff61d60efd76583bf,0xdfd755c37f5d170dfd72,0x4c971ff5805c77f5d970,0x5c7fd54971ff5425c7fd,0xff5435c7fd60971ff562,0x55171ff5835c7fd58d71,0x5c7fd59571ff5845c7fd,0xfed624cbfd61971ff585,0x5cd32fdd434cbfb5c932,0x4caff61932bfd844cbf7,0xfed7250affe0142bfd87,0x5d142fbd5450affe0d42,0x50affe1542bfd8550bef],#[0xfed7254affe1d42bfd87,0x61952f7d7554bdf55152,0x58bfb5c962bfd8754aff,0xbfd8758bbf5d962efd65,0x5cd43dfd755cb7f5d172,0x58eff61d43fbd7450ff7,0xbfd8758fbf5d963fdd73,0x5d554fbd745537f5d973,0x597df5d565bfd87553df,0xffd43482ff61d65efd76,0x60d20ffd73483ff58d20,0x483ff5d120ffd54483ff,0xffd75483ff59520ffd84,0x61920ffd76483ff61520,0x4c3ff58930ffd424c3ff,0xffd764c3ff5d130ffd72,0x5c940ffd52503ff4c940,0x543ff5d540ffd73503ff,0xffd72543ff58950ffd42,0x4c960ffd76543ff5d150,0x583ff5c960ffd52583ff,0xffd325c3ff5d560ffd73,0x58970ffd525c3ff50970,0x5c3ff58d70ffd435c3ff,0xffd744cbff59570ffd54,0x5cd42ffd8050bff5d932,0x50bff5d542ffd8350bff,0xffd7654bff5d152ffd87,0x50d72ffd7558bff5cd62,0x5cbff55172ffd635cbff,0x2d007800f0000ffd65,0x9001fb06d817a04d40f],#[0xf9c3870d743060b28285,0x1851313a449211a04110,0xc6961944603171c58215,0x87320707bc1d707201b6,0x1a2754990252c90622e0,0xf2da8b252ba4a9b2958a,0x3420cc3321cc4b2fd0ba,0xa50e4f384cdc53624d44,0xa101a3f0cf6c3c54ed93,0x9212475917f44a10b641,0x3d44e613534c5d2c049c,0x8d54d94df522144c5041,0x75b0967d592960557255,0x615d81b5f7d7a35d3170,0x76999e658992663a9893,0x4db336bb9aa969b5a316,0x9d107309c7d7075bd86e,0xec979a5e2d77a1da3757,0x7980adfef7ea9f5c7ca5,0x487b619f858e11583660,0x8e0a3468c062bc8a0224,0x4824e492a2448900e3be,0xfa682991a60a97165659,0x28179f4a7849cfe6fa9a,0x9eba6be961a3e28aaa17,0xadad7eb23ab56a7ea8c2,0x7b38ac9db186c25afa6b,0x1604381ec6a2c6b5b2d2,0xa2c6c1604381fc5a346c,0x821c5a346c16043820c6,0x5c0b001138a347c16043,0x4b8d8122f00710a0e25c],#[0x6401ce207c6e2f004018,0x98d1a39c40e804e6371,0x3802f85471389717808,0xc5e020263468e25c6a2e,0x4a407c6e2f0040184a18,0x53201c218d07e00be8b2,0xc018d1a5637008b20082,0x480212c4e2503c0b1611,0x5c6853005f45938bc023,0x271b80459004280940e1,0x531281c318b0be00c68d,0xdc5e00802e2f008d2008,0x1cd38dc5a1f002518a58,0xc1e361f048d85e002e0f,0x7859ce1e460b1b0bc006,0x2f000f080e804e60b1a8,0x8d05e00260f1cd864c68,0xe091a0bc003c323e1f04,0x34ac16341780078786c3,0x684c2207c10f81f8085a,0x2e07c10f81f8046c2ca2,0x1d60b1b800dc2c92a864,0xb1780868443638781e5d,0xc4e60b168786c4483660,0xb1627c0034de111d006,0x4734609160dc0058223a,0x1b0e6cc162f000d0f84,0x21a4218d187c122e1b8,0x8dc042c281b1cd982c5e,0xa73058d43c2e2841bf05,0xe6cc6e0016140a8c8037,0x141cd1824682f00160a0],#[0x850403e1f048d05e0034,0x98046c2c937e0b1b8005,0x5e008630682e58c3e082,0x17808685c3631bf058d8,0x40273058b43c362e3e0b,0xd05c737e2f000d0c05c6,0x1a210b8d87c122c1b800,0x3a62f001b869182c5e00,0x31b8bc006c3a30842e02,0x73660b168dc006c3e39a,0x108c6fc163517800d880,0xb1b8b1f9382c5a37001b,0xb3624092b950a24c0460,0xbd1a48710300c6c1ce68,0x952200a740c71058b839,0xa60840c02398d83a2cd8,0x86c3103008e62e0e8d37,0xc985107204a882c6e2c3,0xcc16060e8d45a4c93795,0xb030746a2d324c00991,0x82c0e3516411a00548e6,0xc73058183a3516962813,0xd82c0e2c388d20e30028,0xe0a0e8d45a689091805,0x581c6a2c883400af1cc,0x61cf0581c5a348e382b,0x807462d237010b0c0406,0x178009840625637010b0,0x36637000b08078636234,0xc260700843005a85a349,0x80380421802d23616489,0x40038dc01283b0b24321],#[0x87c1a061b801c0c3a0f0,0xb138e27c5e009f0d0e8d,0x370038140e0136c37008,0x8b13e001a6f0f8e6f458,0x81c025a86a2f00381e05,0x34903804db0dc022c4e3,0x31844e1f00e2f004f0ec,0x8742a360f028786e0070,0xa0bc00582a312b1b8085,0x49b31b80058802a31b11,0x3418038042b802d23616,0x1d189581c6e02164518,0x6e003418189f8bc04343,0xdf8bc0034421818de8b0,0x10860038bc013c3b0d24,0xe8c68c587f008d0e8c66,0x130f0e68c6883008b0,0x6e003e131f05818682f,0xb021ec042e1a560b030b,0xbc007832387c26621260,0x2c1b80108647c16061a0,0x82c087b010d859582c0c,0xc2f008d0f0e210c99c49,0x30b06e002c1f23058110,0xc3417800b080838e0b0,0x58186c2f00461ce382c,0xc0e0a1a0bc00684039c7,0x40d81c103617800d0847,0x1a8b499582c0c3617802,0x4c942518c970f0280e01,0x2511c1e0501c02351740,0xb1e9248c6e01169e200a],#[0x2cd2711c4a1007e00628,0x8046900e230584b8046a,0x8470034468f496420c3f,0xf0145e02048d4d142712,0x6011640388c251a4970,0x2a14c00c5163d2810861,0x64193178046a84803094,0x792250c05f0034468f4a,0x6138b14f874142f008d8,0x87a746c3a3617804c43c,0xd1b8087a7c741637010b,0x185e011b0f320e6cc142,0x182111c0435166c19042,0x53a681c2a11c0435166c,0x86c453c3c0d0411c043,0x2e1b8088a80a36609178,0xb469bc6389b0de68c12,0x453010b469bc61385301,0x50641053010b4e9a070c,0x79b0d18246c2f01144f9,0xdf82c02361714508e713,0xe951b0f0d45e022e9018,0x4362e9d1b0f0d45e022,0x50d45e022e9e19058bc,0x839bf050d45e022ea01f,0x79b480dc1a0290c022cd,0x166c1e0227c186f008d3,0xc0234de3c1a021b4ae01,0x517808da4c880e0c3698,0xd45e02369922026cc123,0x3517804b46cb2d407048,0x9a8d907137c04d868c12],#[0xc2cd83404df8246a2f00,0x78046c40c8387c218046,0x8e00690d1e92c810a061,0x30245e021a9e244e250,0xc043458131e9127138f7,0xc408bc0434de309c208b,0x70f8770034868b0c2409,0x508c1f0aa37010b360c2,0x117184f0d81c02361715,0x850601170d378d8186e0,0x1e058146e0116938e8e1,0x4d03c0b038046a2d331d,0xd4d47470b40b008d45c7,0x102c0a2f008]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0x410020012110c3089141,0x2c70442806075004400,0x1400a900408548109004,0x96841403c204084120e,0x940860052828c50023,0x2090000005402c28c040,0x270304e140000051013,0x1a9105f1c00c10cb0990,0x4000504000c39b28b04,0x408310114c2c8280316,0x43f91f80000013090c00,0x77000082ed60a45ec180,0xf00020b90002914b6219,0x462e5540f3000380,0x385647554cf,0xdacceb14c00017934010,0x25811358000509698043,0xd9fb029db10002000000,0x6c0001c8b83b11560002,0x10002d44c1b40ba00019,0x18fd00bc970d12708,0x59495100000000000000,0x444b7774b197bc0008,0xbdfa0003870821d55800,0xd284907000314544e,0x16050c00062b053873f0,0x157f51b556e413927d14,0x15ce58c26ec0d7c26c10,0x79be07000194cf2fe95d,0x98000f064000a1140002,0x253d000000045,0xc7504dc371420e000],#[0x3570d0000000000061dc,0xd00034ed00018d000011,0x1e7000082c0000da,0x783532a2cc000a434000,0x24000000000038c40008,0x10cc0000000000000010,0x8e50000000b420000000,0x434487822b8000f3ab,0x1d8000250500000,0xd7f1c39000254f000152,0x4ce59c810b0590002040,0x38000f12c06800000009,0x7141782aca8976fd6454,0xcb0a2af21b0000000326,0xb60000ce698540000002,0x41b0000a16800000020,0xe52e115c6ab47b74dc00,0x32c03a888800086d9472,0x344c44ec0006830c647,0xb1b800000034a600,0x6951f4a585e480d000,0xb48039d5200039690000,0x30001d5e00038ef00020,0x256d12b000162e0001a1,0x6be857e1cc00062c9130,0x313fa306959707912e3,0x80000002c1d86a6d8af5,0x1d3f29082766f743ce49,0x96730309d8033c768062,0xa318000b74400046468,0xe0dd9b258418cd920000,0x261e538f83583ed086],#[0x61c000317d85d0da00,0x80005778cee0003c5c00,0x99774f00000000000924,0x387e8be204c000005c,0xd17aadc460095acf6840,0x310b000117ee2bf60,0x31516df288467601557f,0xe0000377e56bf1d0cc8d,0x4c4000097c747ac6b97,0xb3c3d7b00031f2000,0x7a000000085b8000e658,0xfe39c00000030e191514,0x2738511c5080009221d8,0x42a06100000000000c32,0x6fa177784000b2140001,0x5f65270000000000063,0x1d2d7640000000000000,0x7020db0280d175f053,0x3e3a4000000000000000,0x90026785c688a0d8,0x365c100000000848e587,0x14ded609ac63d13a9fea,0x2a0858871ae5867c83a8,0xddae70fd6a382f0c7374,0xee004412fc0f400026fa,0x60000000000320926901,0x42f1db4b59c000526890,0x5ca927c895c846177851,0x500000000000000185f0,0xb9190000893066d12aa6,0x542711df0ec00046e,0x360115c4],#[0xb4d28b855e851600000,0x1d0f8724000000000,0x0,0x70000440800000000000,0xa2f0001d310001de8e7,0x855007322d76a,0x20540c00066150e2c610,0x50003c03000000067b12,0x19210001963d01e0f,0x7ac00043545cc0001611,0x6e8f80003593b27a9929,0x402af69695a946d62b60,0xb3a3843b10,0x20932800020cc0000000,0x747e54ed36000000014,0xc2b58c9000000060c000,0x68b522572c0004468000,0x14317282dab1,0x81fb7085e29000394d00,0xbbb84a41f13ad58ed0f,0x22770404a869b998675d,0x9f37c000a89fc04b4124,0xe862cfff7c000021f752,0x4fad78d47000096360dd,0x988750000000862705b1,0xc0005448000c8011f558,0x5c00002590000000025b,0xd6000000000000000001,0x1d2573d000012dc1,0x1823f1fc000000000,0x6571ff0003c822850495,0xa0000e5a000052a8000a],#[0x252d13808a940e043654,0x9530134000f27c554000,0x1d181255fd728557f891,0xfa819de50000000369e6,0x785b5bf00039b80003c8,0x6dc8fa644f99d0002dc8,0xe7dc000545e1869,0x35e9000348ad26116000,0xf2529cd7348000739,0x25270c317c4000902c,0x536a62ad8080,0x7080f982355f9000000,0x244000c789c7c63f94d3,0x4312494b00000000000c,0x1c7943df8bd0001946a2,0x1bcc3c85cf0000d1028c,0x66000244f57cd41261a9,0x10002015e2d759a85864,0xb14382b00b446f1571c7,0x1610de578f918d589cd4,0x3f54a00000000001e231,0x4000525c000f11c00078,0x4a394dad0c112395030a,0xc20000176468d069e069,0x80000000123000000018,0xc8e371c00058b182,0x929e089,0x68000609000000024460,0x4d9993c70529521db3b8,0x2d8b919]]
def g255D12 := limbs80 #[#[0xffa81ff4c3fe907f571,0x42ffa65ff5c3feb07fd5,0xd43ffae5ff58bfea97fd,0xfd74ffaa9ff5cffeb1ff,0x1f000ffaedff5d7feb2f,0x1c03145508f0e81641f0,0x6a4c716f2a04d48d0ff,0xa06362c1c7875011e339,0x701028d8b80401c00720,0x80111a1e0a342e003c60,0xe0a342e0050687828b0d,0x6c687828b0d80171a1,0x818d0b801018060a362e,0x51a1e040a2e00e034787,0x2c360060687818d0b801,0xc702818d8b801d1a1e06,0xb80191e1e0a04342e004,0x6342e007868782810d0,0xc68782810d0b80161e0a,0xd0b801a1e0a062c36007,0xa06342e008068781820,0x82818b800d211a]]
def g255H12 := limbs80 #[#[0x20163500330100304702,0x3600022050212092b00,0xe00043bb080000000005,0x273000000ea240496,0x49d2c000000000916000,0x189b,0x60700000000,0x70000e74000000529000,0xd9fe4a9590000006,0x86100000000,0x38700046f00059af45,0xb30000b5f0,0x83200000,0x785771000548000,0x611000000000000b9c0,0x88000000000000,0x44c4e000e4300000025e,0x230531b0000007672174,0xc8d000d7799,0x11a823000000000,0x504d000d7922043a0000,0xc97c2e00009,0x28ea64000,0x4000000d66d3641c0000,0x49400000000000000042,0xa8b000000000c69,0x52930120000000000000,0x63e31,0xf26000,0x47a000000f7c0000,0x946c5c43900032b00,0x95ae6325448c76ca2d],#[0x65f3100000000034c0,0xc3700000000000000000,0xe62a18000b98134000,0x1270,0xda527ec3800000,0xfb3d00020a391513000,0x85d000a21000000f,0x0,0x242000,0x0,0x37659b00000000000000,0x80d34bf01e35,0x5ca00009220006400000,0xb8329d00000000005,0x15100043f000,0x1900000000005410,0x2a1000e8680000000,0x17f000000356,0xad52d060000001840000,0x65b00065700004742588,0x899981133000000000,0xc000000000e0292860e0,0xa6b81056a37d12a05340,0x1922f000000e03000000,0x53cc09000a750001880,0xd5800077bc7800000000,0xe50a6d872000000,0xd9e38244f01f0000,0x196000ba400,0x114000,0x821d00086000060b0000,0xb1e00018ff6],#[0xfa3000000000000000]]
def g255D13 (j : Nat) := if j=0 then 0xe0808d16006ff else 0
def g255H13 := limbs80 #[#[0xc41e007800000099a140,0x9c8000000000cce2805,0xc6520f4e251434c9acb4,0x6719001e]]
def g255L : Nat → Packing
  | 7 => (5,6,7,0,0,6,0,g255D7)
  | 8 => (56,5,7,0,0,12,0,g255D8)
  | 9 => (350,4,7,0,0,15,0,g255D9)
  | 10 => (562,3,7,0,0,16,0,g255D10)
  | 11 => (166,2,7,0,0,14,0,g255D11)
  | 12 => (20,1,7,0,0,11,0,g255D12)
  | 13 => (1,0,7,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 7 0 7 3 0 g255H8
  | 9 => lookupWord 14 79 6 10 6 0 g255H9
  | 10 => lookupWord 87 877 4 13 9 0 g255H10
  | 11 => lookupWord 140 839 6 14 10 0 g255H11
  | 12 => lookupWord 41 419 4 12 8 0 g255H12
  | 13 => lookupWord 5 29 4 9 5 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 5=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_2 : block g255 8 2 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_13 : block g255 8 13 43=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 56=true := (@block_merge g255 8 0 2 54 g255P8_0 (@block_merge g255 8 2 11 43 g255P8_2 g255P8_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_96 : block g255 9 96 84=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_180 : block g255 9 180 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_276 : block g255 9 276 45=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_321 : block g255 9 321 29=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 350=true := (@block_merge g255 9 0 180 170 (@block_merge g255 9 0 96 84 g255P9_0 g255P9_96) (@block_merge g255 9 180 96 74 g255P9_180 (@block_merge g255 9 276 45 29 g255P9_276 g255P9_321)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 30=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_30 : block g255 10 30 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_126 : block g255 10 126 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_222 : block g255 10 222 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_318 : block g255 10 318 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_414 : block g255 10 414 39=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_453 : block g255 10 453 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_549 : block g255 10 549 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 562=true := (@block_merge g255 10 0 318 244 (@block_merge g255 10 0 126 192 (@block_merge g255 10 0 30 96 g255P10_0 g255P10_30) (@block_merge g255 10 126 96 96 g255P10_126 g255P10_222)) (@block_merge g255 10 318 135 109 (@block_merge g255 10 318 96 39 g255P10_318 g255P10_414) (@block_merge g255 10 453 96 13 g255P10_453 g255P10_549)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_4 : block g255 11 4 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_100 : block g255 11 100 11=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_111 : block g255 11 111 55=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 166=true := (@block_merge g255 11 0 100 66 (@block_merge g255 11 0 4 96 g255P11_0 g255P11_4) (@block_merge g255 11 100 11 55 g255P11_100 g255P11_111))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_1 : block g255 12 1 19=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 20=true := (@block_merge g255 12 0 1 19 g255P12_0 g255P12_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 1=true := g255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact (rfl : block g255 6 0 0 = true)
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
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_52012

open PEqualNP.Outside.L_meta_52012 in
theorem PEqualNP.Outside.L_meta_52012 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), gates.length ≠ 15 → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hsize fit _ correct
  exact replaceShort g255R gates o hsize fit correct
