import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52322.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52322
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffefffffffffffffffa,0xfffeffeefefcaa00ffff,0xffffffffffffffffffff,0xfffffffeffffffffffff,0xfffafffeffeefefcaa00]))
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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

def sameWords (a b : List Sig) := (a == b) || ((a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x)))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords, Bool.or_eq_true] at h
  rcases h with eq | h
  · exact congrArg List.toFinset (beq_iff_eq.mp eq)
  simp only [Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List Sig → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws) ws).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag query xs, xs ∈ links tag query → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ _ hx
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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List Sig → List (List Sig))
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
    (lv : ∀ tag query xs, xs ∈ links tag query → Impossible u T (cap-1) (List.toFinset xs))
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
    (lv : ∀ tag query xs, xs ∈ links tag query → Impossible u T (cap-1) (List.toFinset xs))
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

def cubRows (word : Nat) : SixRows := ⟨Fin.ofNat 512 ((word >>> 0) % 256),Fin.ofNat 512 ((word >>> 8) % 256),Fin.ofNat 512 ((word >>> 16) % 256),Fin.ofNat 512 ((word >>> 24) % 256),Fin.ofNat 512 ((word >>> 32) % 256),Fin.ofNat 512 ((word >>> 40) % 256)⟩

set_option maxRecDepth 16000 in
private def sixWords : Array (Array Nat) := #[#[88254062072085,76437625258176,145756158756117,40871513556237,75111463390236,211450904773909,154258250956992,71778567980301,180750011891904,145756159216668,211726856422677,88254064111668,105833363219493,106378832126112,176508124275756,105863428449324,150089780762649,158898759938100,79990553053320,142663785382209,71812928506908,75111462929685,14482833409317,72293971657089,211726856437840,193995892359360,89683505725632,40737849484332,167504131424448,79445084936217,76025302354988,211519625527456,61783910979609,71881649559608,142526344331553,211450904739984,176094196564104,211795577144613,48538033619136,71812930085940,141875672023176,48434551750848,211692496356621,123386626326600,110140745859144,211726858462260,211519625234472,211450906813492,211726856883228,53983730741304,150222926780472,105863428186152,211450905234460,211692496109640,149843024576704,36837959671968,176748645851232,40871516995776,48434547852325,211399364345988,211795576883240,22557243736208,79509509440789,76025302106208],#[83618919694401,79578230162725,14620274197572,105833364009009,61680429109297,123356561096769,211519625232673,79336773259569,14414112637008,75111462895760,83683345203344,145255996407888,176111443804296,176748641716233,176542484333845,71506927829064,211795574851593,145962316138505,14590091985988,89271183611960,105742699610184,49083494433089,176508123562049,142116191219768,71610007060616,36563073925256,180479428921416,105897788507413,83752065696033,41112035132484,79220873445441,105712634380353,14414112653456,105863428441357,149641358311616,105833363439752,211416543985673,211519623202825,48705130561665,44564723269792,79578230952241,211386479247489,150360362918949,14590096187552,176508127674689,71778575589536,149842953577509,71506928084012,71778567725096,110110681104520,211416543993889,211386479944748,150222925725985,150154205267221,154120809873697,83618919949349,14383930441872,27767252977856,27797435187648,48980012564801,72022323896360,71506935685280,211416546280741,110110688938120],#[110175106121808,211416544444681,180479425265736,193725305733192,211692495642657,176334714243081,71506928873528,61680432218304,211386480734264,211662431330344,10037359575232,10067541786816,211399364118537,211675315767305,61951011029121,44668196831297,36971623743873,142406083952708,142457624346704,141892919263368,150102664888388,71761388142724,154052089381008,23300484907104,23300484923552,96997946163489,167366690341153]]
set_option maxRecDepth 16000 in
private def sixMenuStarts : Array (Array Nat) := #[#[1,17,33,49,64,66,97,113,129,147,195,242,274,307,354,386,417,433,449,465,481,497,513,529,546,577,593,609,627,675,722,753,770,801,819,867,915,961,977,993,1009,1025,1042,1074,1106,1137,1153,1175,1281,1298,1332,1394,1427,1475,1522,1554,1585,1603,1650,1685,1767,1877,1954,1985],#[2001,2020,2081,2098,2129,2145,2162,2193,2209,2226,2259,2308,2371,2418,2450,2482,2518,2613,2692,2755,2802,2836,2898,2931,2978,3011,3062,3155,3202,3237,3314,3346,3377,3394,3426,3457,3476,3538,3570,3603,3651,3698,3730,3762,3795,3842,3874,3906,3939,3986,4020,4081,4099,4147,4195,4242,4274,4307,4353,4369,4386,4417,4434,4465],#[4481,4498,4530,4561,4578,4611,4659,4706,4738,4770,4803,4850,4882,4913,4930,4963,5010,5042,5074,5106,5138,5170,5204,5268,5330,5366,5460,5522,5556,5618,5650,5686,5779,5826,5859,5906,5939,5986,6018,6053,6129,6148,6211,6258,6289,6306,6338,6371,6417,6435,6482,6518,6611,6659,6706,6740,6803,6850,6882,6913,6930,6964,7026,7060],#[7122,7155,7203,7249,7266,7298,7335,7442,7474,7509,7585,7603,7653,7730,7762,7794,7827,7878,7972,8035,8083,8130,8163,8211,8259,8307,8355,8402,8435,8486,8578,8610,8643,8693,8771,8818,8849,8867,8919,9026,9058,9095,9206,9299,9346,9379,9427,9474,9506,9538,9571,9618,9651,9701,9781,9860,9925,10008,10132,10198,10296,10422,10515,10561],#[10580,10641,10658,10690,10723,10770,10805,10882,10913,10930,10965,11045,11123,11174,11265,11281,11297,11315,11361,11382,11476,11537,11556,11618,11650,11684,11747,11794,11827,11877,11954,11990,12085,12166,12259,12308,12372,12434,12466,12500,12565,12643,12693,12770,12803,12851,12898,12930,12962,12995,13043,13093,13170,13203,13251,13301,13379,13426,13458,13491,13540,13606,13697,13716],#[13778,13809,13825,13845,13922,13954,13988,14053,14130,14162,14194,14227,14274,14308,14373,14454,14550,14646,14737,14757,14840,14969,15109,15188,15251,15298,15332,15394,15428,15490,15524,15589,15667,15713,15730,15763,15811,15860,15923,15970,16003,16052,16117,16195,16243,16294,16386,16419,16472,16601,16742,16837,16915,16968,17090,17123,17173,17250,17284,17346,17379,17427,17474,17508],#[17573,17652,17715,17763,17810,17842,17874,17911,18020,18084,18150,18242,18276,18338,18371,18421,18498,18531,18577,18595,18643,18692,18756,18821,18901,18979,19032,19159,19269,19350,19442,19475,19524,19588,19655,19766,19858,19890,19924,19988,20051,20098,20132,20194,20226,20257,20275,20322,20353,20373,20451,20498,20531,20580,20642,20674,20707,20754,20787,20834,20867,20913,20931,20979],#[21027,21073,21089,21106,21139,21186,21220,21281,21299,21346,21377,21393,21411,21459,21508,21572,21636,21698,21733,21810,21844,21909,21986,22018,22053,22131,22179,22226,22259,22306,22340,22402,22434,22467,22515,22562,22595,22643,22690,22723,22773,22851,22900,22962,22999,23107,23155,23204,23267,23314,23349,23426,23461,23538,23572,23637,23714,23750,23844,23906,23940,24003,24053,24130],#[24163,24211,24261,24340,24404,24471,24580,24642,24674,24710,24804,24871,24979,25029,25108,25171,25218,25253,25334,25428,25491,25538,25571,25620,25682,25714,25748,25814,25911,26023,26131,26186,26344,26467,26515,26563,26611,26659,26707,26758,26851,26900,26965,27046,27141,27222,27318,27415,27528,27657,27794,27826,27858,27890,27922,27955,28006,28099,28147,28194,28226,28259,28307,28358],#[28453,28531,28582,28676,28741,28820,28887,29000,29127,29235,29284,29354,29506,29544,29671,29779,29827,29875,29921,29940,30004,30067,30115,30163,30211,30258,30291,30339,30386,30419,30469,30547,30596,30662,30756,30821,30900,30966,31060,31125,31208,31331,31378,31411,31459,31506,31538,31574,31668,31732,31795]]
set_option maxRecDepth 16000 in
private def sixMenuWords : Array (Array Nat) := #[#[10,26,24,0,3,26,31,8,5,6,31,76,31,54,76,2,7,4,16,0,12,16,4,19,9,27,12,102,23,6,1,3,4,53,9,43,19,2,75,25,36,38,8,36,38,6,31,28,3,4,18,25,36,43,8,36,44,7,12,15,16,11,21,17],#[13,0,99,3,32,22,32,41,14,0,2,3,11,12,15,17,7,0,17,0,2,11,17,0,103,0,22,71,0,65,104,0,58,0,105,9,2,5,14,2,5,5,6,14,25,41,5,14,25,28,38,41,54,5,6,8,38,41,8,85,55,30,14,20],#[22,65,20,30,65,56,86,3,13,97,38,5,8,5,31,42,6,25,41,75,31,42,75,1,24,1,3,3,24,3,5,14,25,26,57,3,5,14,24,57,5,8,24,57,1,5,57,1,43,8,24,36,44,15,24,14,15,26,1,5,5,24,70,3],#[5,8,14,24,57,14,15,24,5,10,5,14,24,25,57,12,15,18,23,22,3,47,5,28,98,5,28,31,98,0,12,3,8,0,3,8,3,12,77,5,14,5,77,5,6,5,6,16,3,15,0,2,11,45,3,11,45,0,10,5,31,121,122,100],#[3,5,10,6,14,15,5,6,101,8,50,0,8,8,14,15,47,123,19,23,37,3,22,54,79,4,80,12,17,34,4,40,0,3,4,0,4,16,2,4,11,86,9,13,0,8,9,0,16,11,19,27,0,3,2,4,9,2,18,2,12,2,8,2],#[13,7,9,4,44,4,13,17,87,2,13,14,18,4,14,2,3,9,13,17,18,3,9,38,88,9,15,9,13,89,90,4,9,4,36,9,13,15,20,36,39,2,13,18,13,27,22,53,108,18,53,13,30,65,13,15,22,56,3,9,13,36,39,36],#[8,11,14,38,8,14,38,8,11,42,25,37,8,15,2,4,11,61,0,4,17,4,50,0,2,4,9,11,17,0,4,9,2,9,43,14,15,8,11,14,15,22,25,43,25,43,8,44,63,7,12,7,10,12,15,9,17,12,48,101,113,0,7,4],#[130,131,4,15,43,80,4,27,0,21,2,3,5,12,15,17,47,3,17,0,19,0,3,27,32,49,40,0,12,67,3,12,13,15,21,35,59,0,86,0,133,9,58,68,0,3,8,11,12,14,3,8,12,14,8,11,25,0,8,25,0,9,3,11],#[32,0,11,17,11,15,33,0,111,134,0,35,59,0,85,0,22,32,0,6,17,28,41,135,0,41,115,136,0,6,28,3,8,12,15,81,6,11,28,2,11,33,0,3,32,0,2,3,11,12,17,33,7,29,3,16,0,3,10,11,12,15,45,0],#[1,2,11,17,26,0,1,26,0,1,2,102,142,2,27,49,0,143,17,53,4,144,0,145,146,4,6,0,2,4,0,2,4,27,49,8,11,12,14,34,8,12,14,34,8,11,14,25,50,6,7,8,12,14,15,16,34,8,12,15,34,8,12,14],#[15,34,51,0,2,4,6,8,17,25,28,0,2,4,6,9,28,8,12,34,15,5,15,17,47,52,0,53,2,53,0,30,83,22,71,0,12,65,67,104,0,30,59,0,69,3,9,32,58,68,0,3,32,58,68,0,2,11,0,9,27,49,58,68],#[118,69,50,8,15,37,84,11,12,15,17,30,92,11,12,17,29,29,66,93,94,95,9,22,5,22,13,14,20,87,13,18,88,9,106,13,15,124,2,5,13,14,107,13,14,6,8,14,38,41,54,2,5,6,28,41,5,6,8,14,38,41,13,15],#[18,9,13,14,89,4,9,23,90,9,19,9,58,17,19,39,108,14,18,20,22,89,20,23,90,14,15,20,39,87,20,22,13,20,71,20,22,65,15,20,20,55,40,51,13,20,44,13,18,99,3,13,39,109,125,3,109,9,20,110,9,20,56,3],#[9,14,20,88,3,14,20,9,20,14,20,8,25,38,9,20,46,58,9,14,20,56,106,110,46,2,5,18,22,13,111,112,72,2,5,8,42,50,31,42,5,42,2,5,6,8,2,5,8,28,51,18,20,18,30,30,33,13,18,23,4,22,1,5],#[14,24,1,3,8,14,57,2,3,5,8,25,57,3,5,14,24,25,57,1,3,5,8,14,57,126,0,2,3,5,10,3,5,6,10,14,15,24,25,3,5,10,14,15,25,26,28,54,5,6,8,10,24,1,5,8,10,9,22,127,11,91,4,9],#[22,23,8,25,3,17,19,78,3,78,1,14,15,24,1,4,11,14,15,1,14,15,128,1,4,4,62,71,1,5,43,5,8,24,44,1,5,10,1,8,5,8,10,1,5,10,50,1,5,10,42,129,5,10,51,1,5,24,5,6,10,24,37,70],#[9,113,15,34,114,0,1,7,12,14,15,16,34,1,5,7,10,12,14,15,16,34,0,8,15,16,34,80,5,15,16,34,80,12,13,15,5,8,10,12,15,34,114,132,11,17,2,5,85,3,5,15,47,77,3,5,2,5,33,47,33,52,2,5],#[6,2,3,5,5,31,3,15,18,91,6,11,12,14,41,6,12,14,41,0,6,16,6,16,81,0,6,6,16,5,81,3,5,6,8,15,16,77,5,6,16,33,5,6,16,51,0,3,6,8,16,41,13,33,3,7,12,15,3,7,11,45,107,3],#[11,14,45,115,7,10,3,15,45,116,7,66,82,13,66,82,0,2,5,10,5,6,10,26,3,5,8,10,26,5,10,26,28,31,5,6,10,0,1,3,6,12,14,15,34,1,6,7,12,14,15,34,3,5,6,15,137,0,1,6,16,138,139,48],#[52,6,140,141,5,6,8,10,1,5,6,10,5,6,7,10,40,65,116,1,5,6,7,10,16,4,62,16,51,2,5,12,29,3,12,17,27,14,47,50,14,16,2,5,47,52,29,33,52,147,62,0,30,148,0,4,117,0,4,7,12,16,7,12],#[16,7,16,7,8,16,0,7,8,16,0,149,0,42,5,8,50,37,81,5,8,14,27,29,29,30,33,48,7,10,29,6,46,60,1,5,29,35,44,4,17,0,9,11,0,33,0,2,4,17,64,4,30,83,0,37,73,74,3,9,18,2,14,18],#[4,13,17,53,2,13,18,35,2,13,23,35,22,44,13,15,20,30,39,13,22,3,9,36,39,2,9,13,17,18,18,22,9,18,9,13,36,39,46,13,15,39,3,13,39,15,22,13,18,39,1,19,0,4,9,11,0,43,15,60,8,11,15,1],#[76,150,22,25,7,10,12,0,11,59,0,11,3,17,32,0,3,8,11,12,3,8,12,3,12,13,21,16,45,0,3,11,12,33,45,48,3,7,13,11,12,67,1,2,11,26,1,11,26,1,6,1,3,8,12,33,1,26,0,1,3,26,32,0],#[13,3,27,32,49,5,7,17,27,47,12,14,5,12,15,17,37,47,12,13,15,21,9,69,8,11,12,14,8,12,14,0,8,9,11,25,9,37,0,29,64,0,7,29,6,7,8,12,14,8,12,15,37,8,12,14,51,0,6,8,9,11,25,28],#[0,6,9,28,8,12,0,27,11,12,15,30,45,92,11,12,29,45,1,4,26,92,118,153,154,1,4,26,0,1,7,26,29,6,7,8,12,8,12,29,15,72,13,14,15,18,20,3,9,13,14,18,20,9,19,20,56,9,20,58,13,39,18,20],#[27,18,20,30,46,3,10,3,61,4,9,10,22,1,5,10,14,15,24,1,3,6,8,14,15,54,0,2,3,5,6,10,28,3,5,14,1,3,5,10,14,15,24,25,28,54,1,3,5,6,8,10,14,15,0,2,3,2,19,96,4,9,22,4],#[62,119,3,17,78,4,13,62,2,4,5,22,23,62,15,22,62,2,5,8,25,4,13,15,62,119,0,2,5,8,10,50,1,3,5,10,24,1,5,10,24,46,60,0,2,5,6,8,10,0,2,5,8,10,28,51,0,1,6,7,8,12,16,34],#[1,5,6,7,8,10,12,16,34,21,33,7,73,10,151,16,74,6,11,6,73,74,3,10,12,15,16,45,3,10,16,0,10,45,13,61,2,26,3,11,23,0,18,23,6,16,73,74,96,120,0,1,2,5,10,1,6,31,0,1,2,3,5,10],#[1,5,10,31,1,5,6,7,10,2,96,120,152,1,3,6,11,12,15,16,1,3,5,6,7,12,15,16,3,7,15,18,23,63,91,1,48,52,1,6,7,16,1,3,5,6,7,8,10,12,15,16,5,7,1,5,6,7,10,16,51,67,0,1],#[3,6,7,8,16,1,45,47,0,1,6,0,2,9,83,0,2,12,29,3,17,27,69,29,33,83,20,21,30,9,22,117,19,20,64,21,39,0,6,37,5,6,37,5,37,20,21,27,18,20,30,33,64,18,20,21,7,10,27,29,10,29,30,33],#[46,48,0,6,46,60,5,6,10,46,60,1,6,48,52,6,29,46,48,52,60,1,29,48,52,1,5,10,27,29,1,5,6,10,29,33,46,60,0,1,15,1,14,2,13,35,3,13,17,13,16,1,13,0,1,3,7,8,11,1,3,7,8,0],#[7,17,27,0,27,49]]
set_option maxRecDepth 16000 in
private def sixMenuAt : Array (Array Nat) := #[#[0,1,0,0,1,2,2,3,4,4,4,4,4,4,4,5,2,2,2,4,6,7,8,4,4,4,4,4,4,4,8,8,9,10,0,1,11,12,13,4,4,4,14,15,16,4,4,17,18,4,4,4,4,19,4,4,4,20,21,4,4,1,4,4],#[4,4,4,4,4,4,4,4,4,22,4,4,4,8,4,8,8,22,14,23,14,24,4,22,22,22,22,4,20,14,4,25,20,20,4,4,26,18,4,20,4,4,20,19,20,4,19,4,4,22,26,4,4,22,22,4,4,4,22,26,4,27,28,29],#[26,4,4,30,31,31,4,27,4,4,32,21,21,4,21,0,4,22,4,0,26,4,0,0,0,4,4,4,4,4,0,0,4,0,22,21,33,4,21,21,4,21,3,21,3,4,20,2,4,3,34,35,3,26,22,2,1,2,4,4,2,34,36,37],#[4,20,3,4,38,4,4,22,3,3,22,22,4,37,4,3,3,3,4,4,4,4,3,4,4,3,4,8,4,4,4,4,4,39,4,4,3,3,3,33,26,4,20,3,40,26,4,4,4,20,3,4,3,41,4,20,4,4,4,4,4,4,3,4],#[3,42,4,7,7,4,4,7,21,21,4,3,4,4,43,4,38,38,37,4,4,4,4,4,4,4,26,4,37,4,4,3,3,4,4,4,4,44,44,4,45,4,4,40,26,4,4,21,21,21,21,46,4,3,3,21,4,26,4,26,3,4,47,3],#[3,48,26,48,4,26,4,20,49,3,37,26,4,4,4,4,50,3,4,3,4,4,4,26,4,4,4,4,50,4,4,4,48,3,4,4,4,20,3,3,3,4,4,4,4,4,4,4,4,4,4,4,3,4,51,19,19,4,4,22,3,19,3,3],#[26,4,4,3,4,3,3,19,3,4,3,4,4,4,8,4,4,4,4,52,53,20,4,3,4,3,3,4,3,3,3,54,4,3,4,4,3,4,25,3,3,3,4,20,55,4,4,4,8,4,22,46,41,4,4,4,56,4,57,58,59,60,61,62],#[4,4,46,63,63,4,33,4,4,41,41,64,65,66,67,4,41,4,4,4,4,4,4,68,21,69,4,4,70,21,4,4,46,4,21,4,4,56,71,4,68,4,22,4,4,4,29,72,4,7,73,4,4,74,74,74,75,76,73,4,18,77,78,79],#[78,8,80,81,82,83,20,20,84,20,20,4,85,20,86,87,88,20,4,8,89,90,91,88,92,4,4,93,89,89,94,95,4,4,4,4,96,46,97,21,46,4,4,21,4,4,4,6,6,4,4,4,98,99,4,4,100,73,8,4,41,101,16,4],#[4,102,4,4,103,4,3,104,105,106,4,107,108,3,4,109,21,4,4,4,4,110,4,111,112,4,4,4,4,113,4,4,58,92,4,114,73,115,116,115,117,118,4,4,3,4,119,120,4,121,4,4,4,122,4,4,3,3,3,123,3,4,4,4],#[4,4,4,4,4,66,26,26,18,4,66,4,26,56,4,8,8,56,8,8,4,124,26,70,18,4,26,4,26,4,26,26,10,26,125,4,4,4,26,26,0,26,0,0,126,4,4,4,4,2,1,19,19,127,3,4,3,48,20,128,4,12,33,4],#[129,130,12,131,18,132,33,4,4,4,11,4,4,4,3,4,4,4,4,4,133,134,14,63,18,4,4,18,4,132,135,19,4,18,38,132,4,4,18,3,4,136,137,15,43,4,56,25,138,4,3,139,140,139,4,141,141,142,37,33,139,38,142,4],#[4,48,4,20,4,4,4,4,20,4,56,56,143,23,132,3,144,3,3,144,3,4,145,146,3,147,4,4,26,56,148,16,3,3,3,3,3,4,149,4,66,66,66,66,66,66,66,26,4,1,4,22,4,22,4,4,22,66,4,4,4,4,4,4],#[96,4,4,4,20,4,4,4,20,4,22,8,22,22,22,22,4,22,22,4,4,4,4,8,4,8,22,150,151,26,26,18,4,152,33,4,153,154,155,151,26,46,19,22,26,26,18,4,4,4,4,22,4,22,22,22,26,26,22,4,22,22,56,156],#[26,157,56,158,159,26,26,4,147,160,4,161,162,124,163,4,20,4,19,4,4,18,4,19,4,26,96,26,4,20,4,19,26,4,66,164,165,20,18,20,165,22,19,19,19,4,56,56,4,166,167,167,26,4,4,56,26,168,19,169,26,26,26,28],#[170,26,26,26,26,26,26,21,4,19,96,21,20,4,26,20,4,20,4,4,171,4,165,20,4,26,172,25,19,22,26,31,19,19,63,26,173,174,26,4,33,33,20,21,20,21,26,4,4,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4],#[4,22,21,20,4,22,175,0,26,46,4,4,56,26,4,4,0,4,4,38,4,4,0,0,26,26,0,0,26,4,4,26,22,22,22,4,4,4,21,4,4,4,4,38,4,4,0,20,4,4,0,176,20,4,4,4,0,4,4,4,22,0,4,4],#[4,0,26,0,26,0,0,4,4,33,20,4,20,4,22,126,21,21,19,4,21,20,19,22,4,22,22,26,26,158,33,4,3,3,177,26,178,21,3,3,3,3,4,21,4,3,20,20,22,4,22,3,3,22,19,22,3,3,3,22,22,22,22,26],#[22,22,179,137,96,180,3,181,182,183,96,3,3,34,3,3,121,4,3,3,3,4,3,3,4,3,3,4,3,4,3,4,4,19,4,4,26,3,22,3,20,4,4,3,3,3,26,26,20,2,22,20,26,3,3,3,3,3,184,185,186,3,3,3],#[3,26,3,3,3,3,3,4,3,4,4,4,3,3,3,22,22,3,3,3,4,4,4,4,4,3,3,4,3,4,3,3,4,4,3,3,3,4,4,4,20,20,4,4,4,3,4,4,4,22,2,2,19,31,31,20,3,4,4,187,3,184,20,20],#[39,3,3,3,3,22,20,20,20,3,3,3,39,4,4,4,4,188,189,26,20,4,190,191,131,37,4,20,192,3,192,22,22,22,22,40,40,4,193,22,22,194,195,101,3,16,101,4,26,22,3,19,3,20,20,3,16,101,48,3,3,3,3,3],#[3,3,3,3,3,4,8,4,3,3,3,196,43,22,40,3,3,197,3,21,21,8,40,26,8,198,26,26,4,3,26,3,3,3,3,3,3,3,4,20,4,4,3,3,3,4,3,4,4,4,4,4,3,3,3,3,3,3,4,39,3,3,4,3],#[39,3,3,3,3,3,3,3,3,3,39,3,3,3,199,200,41,25,41,141,201,202,203,33,22,4,26,4,26,37,204,3,3,205,197,20,20,20,20,206,3,207,33,68,33,68,56,208,3,3,56,209,210,211,212,3,3,56,213,3,214,38,215,37],#[18,216,3,40,3,40,4,26,37,3,217,4,20,18,3,218,3,7,7,7,4,3,3,4,3,219,3,25,4,220,3,3,3,221,222,142,3,3,139,142,26,223,4,40,26,3,41,3,4,20,3,4,7,4,21,142,21,41,3,20,3,44,44,41],#[202,3,224,4,4,19,3,37,19,225,37,226,224,224,227,37,4,3,224,37,7,38,3,26,4,26,37,228,229,4,4,26,26,3,4,26,3,4,4,3,3,3,3,3,20,3,3,4,3,21,21,38,4,230,3,139,231,48,4,4,0,4,232,4],#[21,20,4,38,3,26,3,3,233,0,37,0,3,4,26,21,3,3,48,48,48,4,4,4,4,4,3,26,3,3,3,3,18,18,20,20,3,4,4,4,3,4,4,20,4,20,4,49,3,37,215,38,37,37,38,26,26,4,26,4,4,4,4,4],#[26,234,48,192,4,3,227,235,3,3,37,192,192,4,26,48,48,48,20,20,3,3,3,3,3,192,48,48,128,192,4,4,4,26,26,202,4,26,26,33,38,20,4,4,3,4,20,3,3,7,3,20,20,3,3,7,48,3,38,3,3,3,21,4],#[20,48,142,21,20,20,48,48,21,20,48,20,48,3,20,3,49,4,50,4,3,3,4,20,20,1,48,20,20,20,20,20,4,20,20,20,20,20,48,4,4,4,4,3,20,40,3,3,3,4,48,3,20,48,48,192,48,48,4,3,3,20,3,20],#[3,3,3,39,3,197,197,3,39,39,39,4,20,20,3,3,236,20,39,3,3,4,4,3,3,3,3,3,39,4,3,4,3,3,3,4,3,3,3,192,4,3,3,3,3,3,3,3,4,3,3,3,3,56,4,56,4,56,22,3,3,38,237,26],#[26,26,238,175,239,240,23,135,33,22,4,241,22,242,22,243,19,19,19,26,238,4,244,26,110,245,3,4,246,247,248,212,249,19,19,22,249,19,19,250,251,3,252,224,253,254,4,224,19,19,19,4,131,3,3,3,3,26,3,3,3,3,3,3],#[3,4,4,4,4,16,8,4,4,56,3,255,255,8,256,8,257,188,25,39,3,3,39,3,3,3,3,3,3,3,3,3,39,3,39,3,4,3,39,3,4,4,4,56,56,4,4,4,4,56,4,4,4,40,258,259,26,52,3,3,260,200,18,25],#[41,41,25,20,20,41,46,19,4,261,41,262,205,51,19,19,20,263,264,3,263,3,41,20,20,3,39,3,3,20,3,20,20,20,20,20,20,38,38,50,50,265,265,56,266,267,3,56,3,26,268,4,4,4,3,4,20,4,3,20,170,212,3,3],#[3,3,213,3,125,269,3,3,4,3,200,270,25,25,25,3,25,25,25,25,20,141,271,4,172,4,25,25,4,4,3,4,3,272,3,4,20,19,3,224,4,4,3,3,3,3,3,19,273,3,3,255,3,3,3,4,4,3,3,19,3,21,4,3],#[3,33,3,4,21,3,3,39,3,3,3,48,3,3,3,20,20,20,20,3,20,236,20,3,20,236,236,236,55,3,3,3,3,4,4,16,274,3,4,4,3,4,4,4,4,275,16,276,255,277,0,278,18,278,20,3,3,3,20,20,20,20,20,20],#[4,3,20,4,3,3,3,20,20,3,3,4,3,3,4,20,20,20,20,8,279,56,280,8,8,4,281,22,282,283,284,285,286,287,288,4,60,289,290,4,291,292,293,294,295,296,297,298,299,64,66,300,301,302,303,304,303,64,305,306,21,307,308,4],#[286,56,309,4,310,66,311,312,313,314,315,316,317,313,66,4,318,319,96,41,320,58,4,321,322,323,321,58,324,21,4,74,325,4,25,71,25,4,4,4,326,327,328,21,329,330,329,33,18,4,331,4,0,21,332,199,333,334,335,21,336,337,338,18],#[92,339,21,340,341,342,343,344,345,346,347,4,348,349,350,351,91,352,41,353,88,354,355,356,20,88,8,58,304,357,88,358,359,360,8,110,361,362,92,363,364,365,340,365,343,4,176,366,367,331,368,369,370,371,372,373,110,4,4,4,374,4,96,375],#[4,376,377,4,378,8,379,257,4,3,4,26,30,380,4,381,382,107,3,33,4,39,56,4,109,383,384,385,386,108,387,388,389,3,107,390,391,37,392,107,393,394,122,388,395,4,396,397,48,110,48,4,95,0,38,398,4,399,400,0,401,21,4,113],#[4,4,4,0,402,142,4,4,4,4,403,4,404,403,405,58,406,6,4,382,8,8,4,407,408,360,409,4,4,3,39,4,3,410,411,412,413,3,92,358,414,415,3,358,416,8,417,4,418,419,3,420,4,3,4,388,19,4,19,421,4,96,4,4],#[422,423,8,424,8,425,426,4,57,4,427,428,429,430,431,4,432,433,434,435,435,436,435,437,4,438,439,439,172,200,440,120,441,442,142,263,4,66,33,4,263,4,4,4,443,444,4,445,4,4,446,4,95,33,358,358,447,358,448,4,4,4,4,4],#[4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,66,66,4,66,4,66,66,26,26,20,4,56,56,4,4,4,56,449,255,4,22,4,449,96,4,450,26,26,18,4,33,4,4,4,26,4,70,4,4,20,4],#[26,33,4,20,4,26,4,4,4,4,4,4,322,26,26,26,66,4,20,20,4,4,4,4,4,4,4,4,3,4,4,4,4,3,4,4,4,4,4,4,21,4,0,4,4,4,21,4,4,4,4,4,4,274,0,20,4,26,4,187,22,26,4,22],#[0,0,0,0,4,26,26,4,4,176,4,20,22,20,20,4,96,141,449,4,4,4,141,4,4,4,4,4,4,4,3,4,4,26,4,4,4,26,4,4,4,4,3,4,4,4,4,4,3,4,4,4,3,4,4,4,4,4,4,3,4,4,4,4],#[4,4,4,3,3,4,4,4,20,2,127,20,4,4,4,3,3,4,4,20,3,3,20,20,20,3,39,3,3,3,3,3,20,20,20,20,20,3,4,4,3,3,3,39,3,4,4,4,4,4,4,451,4,22,135,63,19,4,48,20,48,128,4,4],#[4,4,3,38,4,4,4,4,3,3,177,4,244,431,452,213,213,56,431,4,215,202,18,4,41,4,49,139,141,141,20,4,4,142,20,4,202,4,4,26,20,431,120,110,4,3,3,38,202,3,4,453,4,20,20,3,4,4,4,4,3,37,4,4],#[4,20,4,4,4,4,4,4,4,4,3,3,4,4,4,4,4,4,4,4,4,4,374,48,37,48,18,4,48,48,4,4,20,4,20,4,4,48,48,4,4,4,4,21,48,20,4,4,4,431,4,20,20,20,48,20,110,4,48,48,4,4,4,48],#[48,20,20,20,4,20,20,20,20,48,20,20,3,4,4,3,3,4,4,48,4,20,128,48,4,4,4,4,3,3,56,56,244,454,135,431,110,244,110,26,3,4,187,4,4,244,3,4,3,4,455,4,26,56,3,4,8,25,25,25,3,3,3,3],#[1,3,3,3,3,3,56,56,56,56,4,56,4,4,14,4,19,4,18,3,456,3,18,18,4,110,213,455,4,56,25,20,3,138,3,25,25,4,25,20,4,25,4,4,4,4,16,4,7,4,20,4,3,3,3,3,3,457,3,41,264,3,20,3],#[3,3,20,20,20,4,20,4,4,4,4,458,459,3,19,450,4,4,3,4,4,4,4,445,0,4,18,4,20,3,20,3,3,20,20,20,20,20,4,3,3,20,20,3,3,3,4,20,4,20,20,66,66,66,21,199,460,461,255,26,26,20,4,46],#[21,462,4,463,464,465,466,467,449,56,468,469,470,471,168,166,472,26,26,33,33,4,147,4,161,147,473,160,21,474,26,26,474,4,475,63,26,66,476,4,477,20,21,38,26,4,38,4,4,3,4,4,4,4,56,0,26,4,20,4,46,175,56,56],#[56,4,26,26,22,22,4,4,4,4,274,4,187,0,63,26,41,20,21,21,22,451,431,26,26,178,19,4,3,3,3,255,197,20,19,3,3,3,4,255,22,4,3,3,22,22,4,22,22,22,22,26,26,22,22,478,96,157,56,3,3,4,4,26],#[26,33,4,3,3,177,3,3,19,4,4,4,3,431,19,4,26,3,96,3,3,479,26,4,19,480,481,3,450,3,3,185,3,3,174,26,3,3,4,3,3,3,165,22,19,19,3,3,19,4,3,3,4,3,4,4,3,3,4,4,4,4,4,4],#[21,21,4,236,482,255,171,4,3,3,3,475,19,22,3,31,3,3,19,19,187,3,483,3,20,3,174,20,20,187,187,20,4,4,3,3,3,3,3,3,4,56,484,37,20,4,22,22,20,224,192,3,192,4,3,485,3,3,4,3,26,3,197,3],#[4,3,4,20,4,4,4,3,3,3,3,3,3,3,3,4,39,3,3,486,38,3,214,3,40,3,487,3,199,25,41,25,41,141,201,3,202,203,488,489,211,212,3,3,4,26,4,26,37,490,453,3,3,218,197,20,20,20,20,4,4,4,3,37],#[0,4,20,4,4,491,37,63,21,20,4,21,20,4,26,38,38,38,492,0,0,3,3,231,48,3,3,197,26,21,197,3,493,176,20,20,38,3,4,4,4,3,3,3,3,20,20,4,4,19,3,38,215,38,37,494,38,38,26,26,26,26,48,495],#[3,48,192,4,3,48,192,38,26,139,37,68,18,37,18,218,48,38,7,20,7,7,7,4,3,192,21,20,192,142,20,21,48,3,48,20,20,3,453,496,235,235,49,3,48,497,48,498,48,497,48,231,20,20,20,20,20,48,192,4,235,235,48,192],#[192,7,20,7,40,3,3,4,48,48,499,500,20,192,192,192,48,192,20,39,20,197,497,20,20,192,235,4,20,20,4,3,4,4,3,501,205,3,3,3,3,3,3,39,3,3,40,4,192,3,192,192,3,48,192,48,192,192,192,192,3,4,4,3],#[3,3,3,3,56,22,244,26,135,26,4,244,110,502,450,131,3,3,3,3,152,40,197,3,503,197,3,4,3,504,56,3,505,16,188,188,188,25,3,39,3,3,3,25,3,3,3,3,39,3,3,4,3,3,39,39,3,3,3,3,3,4,3,4],#[3,3,3,3,3,39,39,3,39,3,3,3,56,56,4,56,4,56,56,40,3,3,200,41,25,41,203,33,22,3,506,263,3,197,20,20,20,38,50,271,56,266,268,213,3,33,33,3,507,25,508,509,510,212,213,511,3,56,213,56,269,200,25,25],#[25,25,25,25,3,25,3,3,4,4,4,3,4,201,201,33,3,3,3,48,512,513,431,3,501,3,4,3,455,508,509,248,212,20,20,20,20,3,3,514,19,19,22,514,19,19,515,457,516,3,517,224,518,519,4,224,19,19,19,4,4,3,3,3],#[3,39,3,39,33,3,520,3,3,3,41,236,20,3,3,39,197,197,3,3,3,497,20,20,20,236,20,236,20,20,20,236,20,236,20,3,20,20,20,20,20,20,4,16,274,4,16,16,16,18,16,3,3,3,3,0,445,521,16,522,255,0,33,278],#[188,20,20,20,3,20,3,3,20,3,20,20,22,20,20,20,3,3,19,277,235,523,524,20,235,3,520,525,16,20,20,20,4,235,20,20,20,3,4,20,22,20,20,20,4,3,526,527,20,20,20,20,20,20,528,529,530,531,532,4,533,534,535,536],#[537,538,21,332,539,540,541,542,543,544,545,546,547,4,548,549,549,550,551,552,553,304,554,555,556,557,558,559,176,560,561,110,4,322,228,3,322,562,458,563,176,564,374,37,565,566,567,568,569,459,570,400,37,571,572,403,4,573,388,574,575,576,577,8],#[578,579,580,4,501,110,581,582,583,584,236,358,585,586,586,3,409,587,588,419,589,590,591,592,39,4,593,4,594,595,596,425,597,598,599,4,3,8,600,601,602,603,604,603,605,606,607,39,606,0,608,609,592,610,417,611,358,612,613,614,613,358,611,615],#[616,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4],#[4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,449,449,4,4,21,4,4,4,4,4,4,4,4,4,449,3,4,255,4],#[22,4,449,449,96,4,450,4,26,26,19,4,3,4,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,3,20,3,4,20,4,4,4,4,3,3,3,4,4,4,4,3,49,4,110,3,4,4,21,21,4,4,37,4,20,4,4,3],#[4,4,4,4,4,4,4,374,38,37,7,4,48,21,21,3,20,7,3,4,48,20,48,4,20,4,110,4,3,4,48,48,48,4,3,110,4,3,4,455,56,25,3,25,3,3,3,3,3,3,3,56,177,4,431,110,56,431,25,25,4,4,4,3],#[3,4,4,4,431,3,3,4,3,3,20,20,20,4,4,4,4,4,4,4,4,4,4,4,20,20,3,20,20,4,431,3,3,20,20,4,4,3,20,20,3,4,3,4,4,4,20,20,617,618,462,4,619,465,467,449,475,620,621,26,70,4,236,622],#[38,214,623,624,211,212,235,235,3,3,625,504,188,3,3,3,213,213,3,3,197,141,626,626,188,188,3,188,3,3,525,235,3,526,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4],#[4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4]]
private def atSix (v : Array (Array Nat)) (i : Nat) : Nat := ((v[i/64]?).getD #[])[i%64]?.getD 0
private def hotSix : Array Sig := #[(inputs.getD 4 zero),(inputs.getD 2 zero),(inputs.getD 5 zero),(inputs.getD 7 zero),(inputs.getD 3 zero),(inputs.getD 6 zero),(inputs.getD 0 zero),(bin 1 (inputs.getD 0 zero) (inputs.getD 6 zero)),(bin 1 (inputs.getD 6 zero) (inputs.getD 7 zero)),(bin 1 (inputs.getD 3 zero) (inputs.getD 6 zero)),(bin 1 (bin 1 (inputs.getD 0 zero) (inputs.getD 6 zero)) (inputs.getD 7 zero)),(bin 1 (inputs.getD 0 zero) (inputs.getD 3 zero)),(bin 1 (inputs.getD 3 zero) (inputs.getD 7 zero)),(bin 1 (bin 1 (inputs.getD 3 zero) (inputs.getD 6 zero)) (inputs.getD 7 zero)),(bin 1 (inputs.getD 0 zero) (inputs.getD 2 zero)),(bin 1 (inputs.getD 5 zero) (inputs.getD 7 zero)),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffaaffaaffaaffaaffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffaaffaaffaaffaa])),(bin 1 (inputs.getD 5 zero) (inputs.getD 6 zero)),(bin 1 (bin 1 (inputs.getD 0 zero) (inputs.getD 3 zero)) (inputs.getD 6 zero)),(bin 1 (inputs.getD 3 zero) (inputs.getD 5 zero)),(bin 1 (inputs.getD 2 zero) (inputs.getD 6 zero)),(BitVec.ofNat 512 (word80 [0xff00ff,0xff00ff00ff00ff00ff,0xff00ff00ff00ff00ff,0xaa00aa00aa00aa00ff,0xff00ff00ff00ff00ff,0xff00ff00ff00ff00ff,0xff00aa00aa00aa00aa])),(bin 1 (bin 1 (inputs.getD 0 zero) (inputs.getD 3 zero)) (inputs.getD 7 zero)),(bin 1 (bin 1 (inputs.getD 2 zero) (inputs.getD 6 zero)) (inputs.getD 7 zero))]
private def hotTry : Array Nat := #[24,1,19,24,13,24,24,8,24,24,24,24,24,24,23,24,24,24,24,24,24,24,24,6,24,24,24,24,2,24,24,24,24,24,24,24,24,24,24,24,24,24,24,9,24,3,24,24,24,24,0,24,22,24,24,24,20,24,24,14,16,10,24,24,24,24,24,24,24,24,24,24,24,18,24,24,4,17,24,5,24,24,24,15,11,7,24,12,24,24,24,21,24,24,24,24,24,24,24,24,24,24,24,24,24,24,24]
set_option maxRecDepth 16000 in
private def allSixPaid : Array (Array Nat) := #[#[0x410010000005,0x111449064440,0x410010000005,0x286205945100,0x410010000005,0x510041000045,0x111441264440,0x244015945100,0x191649264440,0x410010000005,0x411400044405,0x410010000005,0x145550505010,0x544585110050,0x149545440110,0x149545440110,0x46015945100,0x410010000005,0x645042550140,0x512414459400,0x510010401005,0x410010000005,0x145540505010,0x601055415040,0x511414455401,0x991649264440,0x911449064440,0x149545440110,0x911441264440,0x244015945100,0x105945450510,0x154595110054,0x286215945100,0x105555441110,0x145550505010,0x540145110041,0x68524a550140,0x155940545410,0x252645985540,0x510010401005,0x44504a550140,0x111841145450,0x56405585500,0x596609594500,0x596609594500,0x411410044405,0x105585440150,0x510051000045,0x411410044405,0x149545440110,0x149545440110,0x149545440110,0x510051000045,0x556401594500,0x121461264448,0x544585110050,0x455944154410,0x252646949540,0x149980505020,0x150155110044,0x115945444510,0x540145110042,0x554001400105,0x455944154410],#[0x510414659400,0x149541505110,0x41514259404,0x145550505010,0x149990505020,0x592614659400,0x145591505050,0x555950515410,0x451504155401,0x540155110045,0x540545114441,0x555454551541,0x29525a550144,0x55815185510,0x414400000015,0x554409594500,0x59815149510,0x65425185504,0x85519194504,0x515945450510,0x186619594504,0x65161a591540,0x559414491510,0x91194a460550,0x455884590550,0x859844560550,0x695605a25540,0x414040000015,0x145950515410,0x182614659404,0x100424659404,0x182624659404,0x540145115041,0x148045545110,0x421865696841,0x549050551150,0x28915b585240,0x148095145150,0x401855525450,0x548985110060,0x149551505110,0x601055415040,0x196940985510,0x58490a190550,0x559814851510,0x648515911150,0x955940625450,0x555549490510,0x245555841110,0x586244699540,0x249552505150,0x201556441150,0x149550545110,0x455000440105,0x145590515050,0x145540619410,0x544145150141,0x598489594681,0x5104a665a481,0x510894551450,0x9115894a0550,0x9585091a0550,0x285582905150,0x586244a69540],#[0x451504154401,0x244056545140,0x695606619540,0x695616619540,0x15a550589510,0x9952192a5540,0x555549490510,0x111851145450,0x201556441150,0x112555489510,0x159485084550,0x111491149450,0x144055145144,0x65415149504,0x811855525450,0xa5161a961540,0x681255615040,0x155421515504,0x555411515501,0x5505a550144,0x155414451504,0x155060551144,0x540145110041,0x455544154414,0x554545110054,0x555950515410,0x545590515050]]
private def selectedRows (t : Nat) := cubRows (atSix sixWords (t % 155))
private def literalCost (t : Nat) (w : Sig) := sixCost (readSix (selectedRows t) w)
private def paidWeight (t j : Nat) := (atSix allSixPaid (t % 155) >>> (2*j)) % 4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem hot_weight : ∀ i : Fin 155, ∀ j : Fin 24,
    paidWeight i.val j.val = literalCost i.val (hotSix[j.val]?.getD zero) := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem hot_goal : ∀ i : Fin 155, literalCost i.val (chartGoal 253) = 3 := by decide +kernel
private def quickWeight (t : Nat) (w : Sig) :=
  let j := hotTry[w.toNat % 107]?.getD 24
  if j < 24 ∧ w = hotSix[j]?.getD zero then paidWeight t j else literalCost t w
private theorem quickWeight_eq (t : Nat) (w : Sig) : quickWeight t w = literalCost t w := by
  let j := hotTry[w.toNat % 107]?.getD 24
  change (if j < 24 ∧ w = hotSix[j]?.getD zero then paidWeight t j else literalCost t w) = literalCost t w
  by_cases h : j < 24 ∧ w = hotSix[j]?.getD zero
  · rw [if_pos h]
    have e := hot_weight ⟨t % 155,Nat.mod_lt _ (by decide)⟩ ⟨j,h.1⟩
    calc
      paidWeight t j = literalCost t (hotSix[j]?.getD zero) := by
        simpa only [paidWeight,literalCost,selectedRows,Nat.mod_mod] using e
      _ = literalCost t w := congrArg (literalCost t) h.2.symm
  · rw [if_neg h]
private def goalWeight (t : Nat) (T : Sig) := if T = chartGoal 253 then 3 else literalCost t T
private theorem goalWeight_eq (t : Nat) (T : Sig) : goalWeight t T = literalCost t T := by
  unfold goalWeight
  split
  next h =>
    rw [h]
    have e := hot_goal ⟨t % 155,Nat.mod_lt _ (by decide)⟩
    simpa only [literalCost,selectedRows,Nat.mod_mod] using e.symm
  next => rfl
private def fitsWeight (t : Nat) : Nat → List Sig → Bool
  | _,[] => true
  | b,v::vs =>
    let z := quickWeight t v
    if z ≤ b then fitsWeight t (b-z) vs else false
private theorem fitsWeight_le (t : Nat) (xs : List Sig) (b : Nat) (nd : xs.Nodup)
    (h : fitsWeight t b xs=true) : (∑ w ∈ xs.toFinset, literalCost t w) ≤ b := by
  induction xs generalizing b with
  | nil => simp
  | cons v vs ih =>
    have splitNd := List.nodup_cons.mp nd
    have absent : v ∉ vs.toFinset := by simpa only [List.mem_toFinset] using splitNd.1
    simp only [fitsWeight] at h
    split at h
    next bound =>
      have rest := ih (b - quickWeight t v) splitNd.2 h
      rw [List.toFinset_cons, Finset.sum_insert absent]
      rw [quickWeight_eq] at bound rest
      omega
    next => contradiction
private def enoughWeight (t : Nat) (T : Sig) (xs : List Sig) :=
  let cap := goalWeight t T
  decide (0 < cap) && fitsWeight t (cap-1) xs
def closeSix (T : Sig) (k : Nat) (marks : List Nat) (ws : List Sig) : List (List Sig) :=
  if marks.isEmpty then [] else
    if ws.length = k+1 ∧ marks.any (fun t => enoughWeight t T ws) = true ∧ ws.Nodup then [ws] else []
theorem closeSix_sound {T k marks ws xs} (h : xs ∈ closeSix T k marks ws) (u : Bool) :
    Impossible u T k xs.toFinset := by
  unfold closeSix at h
  split at h
  next => simp at h
  next =>
    split at h
    next yes =>
      obtain ⟨t,_,valid⟩ := List.any_eq_true.mp yes.2.1
      have same : xs=ws := by simpa only [List.mem_singleton] using h
      subst xs
      apply six_cut (selectedRows t)
      · simpa only [List.toFinset_card_of_nodup yes.2.2] using yes.1
      · simp only [enoughWeight,Bool.and_eq_true,decide_eq_true_eq] at valid
        have sumBound := fitsWeight_le t ws _ yes.2.2 valid.2
        rw [goalWeight_eq] at valid sumBound
        have positive := valid.1
        change (∑ w ∈ ws.toFinset, literalCost t w) < literalCost t T
        omega
    next => simp at h

private def sixOffset : Nat → Nat
  | 6 => 0
  | 7 => 30
  | 8 => 643
  | 9 => 2555
  | 10 => 4097
  | 11 => 4450
  | 12 => 4499
  | 13 => 4504
  | _ => 0
private def inlineMenu (m k i : Nat) : List Nat :=
  if m=253 then
    let mnum := atSix sixMenuAt (sixOffset k+i)
    let offsetCode := atSix sixMenuStarts mnum
    (List.range (offsetCode % 16)).map (fun j => atSix sixMenuWords (offsetCode / 16 + j))
  else []

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := (forestHints (g.levels k) raw.length i).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag query => closeSix (targetOf g) (k-1) (inlineMenu g.mask k i) query ++ ((g.index k tag).bind (linkedSet g (k-1))).toList
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
  · intro tag query xs hx
    rcases List.mem_append.mp hx with extra | old
    · exact closeSix_sound extra g.mode
    · have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using old
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
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ xs ∈ c.2.2.2.2.2 tag query, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : linkAt fl (laneOf c) i j op ka kb=true) :
    (c.2.2.2.2.2 (keySet (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)) (choiceVal (movedChoice op (contextWire c i) (contextWire c j)) ::
      (delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)).any (sameWords
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
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf (choiceVal (movedChoice op a b) :: (delTwo c.2.2.1 a b ka kb).map Prod.fst)
    rw [hf] at h
    simp only [forceMap_eq,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,anyEq_iff,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [sameWords, Bool.or_eq_true]
    right
    simp only [Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
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
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ xs ∈ c.2.2.2.2.2 tag query, ys=xs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
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
    (hfl : ∀ tag ys, fl tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat)
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
  let ls := fun tag query => closeSix (targetOf g) (k-1) (inlineMenu g.mask k i) query ++ ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)


theorem flOf_ok (g : Forest) (k i tag : Nat) (ys) (h : flOf g k tag=some ys) (query : List Sig) :
    ∃ xs ∈ (contextOf g k i).2.2.2.2.2 tag query, ys=xs.map BitVec.toNat := by
  suffices old : ∃ xs ∈ ((g.index k tag).bind (linkedSet g (k-1))).toList, ys=xs.map BitVec.toNat by
    obtain ⟨xs,mem,eq⟩ := old
    exact ⟨xs,List.mem_append_right _ mem,eq⟩
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
  have hfl : ∀ tag ys, flOf g k tag=some ys → ∀ query, ∃ zs ∈ xs[q].2.2.2.2.2 tag query, ys=zs.map BitVec.toNat := by
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

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[1,6]⟩,⟨.or,[6,7]⟩,⟨.or,[0,2]⟩,⟨.or,[4,10]⟩,⟨.or,[3,5]⟩,⟨.or,[2,8]⟩,⟨.or,[3,8]⟩,⟨.or,[4,7]⟩,⟨.or,[0,9]⟩,⟨.and,[15,13]⟩,⟨.and,[16,12]⟩,⟨.and,[14,5]⟩,⟨.and,[9,11]⟩,⟨.or,[17,18]⟩,⟨.or,[21,19]⟩,⟨.or,[22,20]⟩], 23⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 4, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 4, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

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
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe01f4201840c62510,0x4261c431e7e7cfeabb69])),(BitVec.ofNat 152 (word80 [0xa0a300200480c0002,0x48048010010342001109]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fe0040e00307c9e0,0x381f8ce0799ff00158c])),(BitVec.ofNat 152 (word80 [0x6269046a202168044,0x108d04c1dc85b20140c]))),((BitVec.ofNat 152 (word80 [0x1f7800183f80e00,0x83fe030ff81e0ff366d7])),(BitVec.ofNat 152 (word80 [0x141440840113500000,0x91a80104281c0c204010]))),((BitVec.ofNat 152 (word80 [0x1fe000101fc001000,0xfc0003f0001ff004c8d0])),(BitVec.ofNat 152 (word80 [0x3859600101dc001000,0xdc0003b00017a004c8d0]))),((BitVec.ofNat 152 (word80 [0xfe000801fe00001fff,0x3ffffe0001b731b])),(BitVec.ofNat 152 (word80 [0x20618801c200001074,0x2e85640001a2000]))),((BitVec.ofNat 152 (word80 [0xffe0000001fff,0xfffffc000000001c7c20])),(BitVec.ofNat 152 (word80 [0x408001080000000d88,0x22512400800000400020]))),((BitVec.ofNat 152 (word80 [0xfffffffffe000,0x1f803c])),(BitVec.ofNat 152 (word80 [0x810002301420a12000,0x1000000810000]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(1,0,252,0,11),(4,0,249,0,11),(8,0,245,0,11),(16,0,237,0,11),(32,0,221,0,11),(64,0,189,0,11),(128,0,125,0,11),(20,0,233,0,10),(5,0,248,0,8),(9,0,244,0,8),(12,0,241,0,8),(17,0,236,0,8),(33,0,220,0,8),(36,0,217,0,8),(40,0,213,0,8),(65,0,188,0,8),(68,0,185,0,8),(72,0,181,0,8),(96,0,157,0,8),(129,0,124,0,8),(132,0,121,0,8),(136,0,117,0,8),(160,0,93,0,8),(0,4,41,208,7),(0,16,41,196,7),(21,0,232,0,7),(28,0,225,0,7),(41,0,212,0,7),(4,16,41,192,6),(16,4,41,192,6),(64,4,41,144,6),(64,16,41,132,6),(128,4,41,80,6),(128,16,41,68,6),(192,0,61,0,6),(13,0,240,0,5),(37,0,216,0,5),(44,0,209,0,5),(68,16,41,128,5),(69,0,184,0,5),(73,0,180,0,5),(76,0,177,0,5),(80,4,41,128,5),(97,0,156,0,5),(100,0,153,0,5),(104,0,149,0,5),(133,0,120,0,5),(137,0,116,0,5),(140,0,113,0,5),(144,4,41,64,5),(161,0,92,0,5),(164,0,89,0,5),(168,0,85,0,5),(192,4,41,16,5),(192,16,41,4,5),(45,0,208,0,4),(105,0,148,0,4),(169,0,84,0,4),(196,0,41,0,4),(196,16,41,0,4),(208,4,41,0,4)]
def g253A : List (List Nat) := [[],[118],[83],[83,118],[66],[66,118],[66,83],[66,83,118],[48],[48,118],[48,80],[48,80,118],[48,66],[48,66,118],[48,66,80],[48,66,80,118],[80,48],[80,48,118],[80],[80,118],[80,66,48],[80,66,48,118],[80,66],[80,66,118]]
def g253D6 := limbs80 #[#[0x541102dd655915250910,0x5c95254110611645c952,0x619a2dd1525411061ba4,0x541106d3a75956254110,0xdd162541102dd6560962,0x29da05956254510595a2,0x549106c8976416554510,0x25d655491029da059562,0x697a464887595106c9a4,0x501206d5a221d8059510,0x59562541206c96558551,0x6dfa159562541206d3a1,0x541202e5655897154120,0x59571541202a57659571,0x689a059561545202a5a2,0x54520e91a05956154520,0x5956454520689a059564,0x6c7a26595258150e91a0,0xc2a9ca9e2a71a964a35a,0x62b8aac62b14ac4ab0ca,0xaf03b82ed92b62ad0eae,0x38acc2f21ac46ef12bc2,0x47f82bb18de23518ce63,0x69c38c833887438674b8,0xc10f877a36cc2b8893b8,0x85938650796307962db0,0x8386017844d38268b8,0x70cb68d9b6cbab6ca7b9,0xee63891238926b890738,0x955b854bf6931f88f178,0x84d1c0b02c0053856b76,0x9aece62af56aa2461d0c],#[0x5668b359146a18ff793a,0x3e03f77b3d3667197fb4,0x87f81c09f90a841ec2f8,0x7fb0721fc09c28808bf,0x81eb1718cf319d85c45e,0xc0ae047e006133078e65,0xe198c5328bf0c78c3c4,0x242fc09006b945fc16c0,0x8167182201e90c012fc8,0x2762037d0c2e25103,0x5682b41006c2c4010080,0x8479209a10676200d60,0x61cb0d586ac211c58c1c,0x3702019]]
set_option maxRecDepth 16000 in
def g253D7 := limbs80 #[#[0xdd121443a45d56548510,0x44186551525091061565,0x55152509106595454942,0x50910595645494244297,0x6196554942440a759552,0x54942441a05955250910,0x44297e418550910e9d65,0x54b805091055152e0142,0x5091059552e014244164,0xe9d65e0142441a154b80,0x48550441645492154110,0x4418654921541105d952,0x5512154110dd15248550,0x541106a5544855044164,0xdd162485504415458921,0x48550441765952154110,0x44165dd1215411065965,0x54942541105979448550,0x54110611525095044164,0x68552509504418654942,0x50950441a65494254110,0x44184589425411059162,0x595425411029d6550950,0x54110689655095044176,0x6118250950443a759542,0x54950441a16554254110,0x44174589525411059162,0x58952541106116254950,0x5411069d625495044186,0xdd16254950442a758952,0x54950443945895254110,0x4418459152541105d164],#[0x59152541106196454950,0x54110591725495044194,0x6197254950441845c952,0x54950443a45c95254110,0x441626455254110e9176,0x65952541106599154950,0x5411061b7454950441a1,0x68b745495044196dd152,0x54950441a2dd95254110,0x44186e5152541105db94,0x50961541105494258550,0x541105c9525855044182,0xdd15258550441a954961,0x58550443945496154110,0x443a7595615411029d65,0x5c96154110e517258550,0x541106937258550443a4,0x693925855044394dc961,0x58950440a75956254110,0x441a1595625411065d65,0x59562541106916558950,0x541105957258950443a7,0x6557258950441845c962,0x58950443a45c96254110,0x44165609625411059182,0x60962541105d18258950,0x54110619825895044184,0xdd182589504419560962,0x58950442976556254110,0x441a2dd1625411059774,0x25d65541105979458950,0x54110e897659550441a2],#[0x25d92595504409764565,0x5c950441a2e5d6554110,0x44186e51725411059794,0x649865411029d6560950,0x5411065965dc950443a5,0x61994dc9504416565372,0x50951441765954254510,0x44162e41425451065965,0x59562545105979050951,0x5451065d6558951440a7,0x5977458951441a059562,0x58951441a2dd16254510,0x441a2e11625451059784,0x5d965545106889759551,0x5451025d9059551443a2,0x65965dc95144165e5172,0xe095144165e137254510,0x4416565382545105d965,0x595625491029d6558952,0x5491069d6558952441a0,0xe9165589524428759562,0x58952443a75956254910,0x44165e11625491059774,0x25d655491029d6559152,0x549106909759552441a2,0x25d9059552443a45d965,0x59552441916416554910,0x441a4e5d655491065190,0x64b745491025d9161952,0x595105d965e115244165,0x6959221d65441a464887,0x5d565443a46488759510],#[0x441a221d80595105db92,0x59584dc9106556561372,0x501205d56550940481a0,0xe856550940481a759542,0x54540481a65d54250120,0x48196509515012059542,0x58551501205096154540,0x50120689655454048165,0x65954549404817655152,0x54940481855915250120,0x481765955250120aa564,0x59552501206916554940,0x501206858554940481a8,0x6958654940481a661552,0x54940481656515250120,0x481a6e51755012061994,0x59152541205d16454950,0x54120611645495048176,0x69d64549504818659152,0x54950481a85915254120,0x483a15915254120aa164,0x5d95254120ea16454950,0x541206858654950483a1,0xe858654950481a461952,0x54950483a76195254120,0x48176e11525412061b74,0x591545412065b8454950,0x54120e85645515048186,0x6917655150481965d954,0x55150483a15d95454120,0x481646495454120e8986,0x65954541205d99255150],#[0x54120e919655150481a2,0xe5152585504819854961,0x58550483975496154120,0x48198595615412065d65,0x59561541206896558550,0x5412069d6558550481a4,0xe8565585504839759561,0x58550483a45956154120,0x483a26056154120e9d65,0xe116154120e898458550,0x54120597945855048165,0x69954589504818655162,0x58950481a95516254120,0x483a95516254120aa554,0x595625412029d6558950,0x541206916558950481a1,0xe856558950481a759562,0x58950483a45956254120,0x481655d16254120e9d65,0xdd162541205977458950,0x54120597845895048195,0x65d655915048394e1162,0x59150481a25956454120,0x483a45956454120e8565,0x61164541206198459150,0x54120a619259150483a2,0x5979159150483a465564,0x59550481a2e456454120,0x481a45d9655412068576,0x5d96554120e5d7659550,0x541206499159550483a1,0x68b9159550483a364565],#[0x59550481a4e456554120,0x48176e51655412069f91,0x54971541205d9525c550,0x54120595625c55048186,0x5d9655c550480a959571,0x5c550481965957154120,0x481a2595715412068565,0x5957454120ea5655c550,0x541206195260550481a2,0x64d52dc55048394e4986,0xdd1504819358b7154120,0x483a4597745412068965,0x59784541205d965e1150,0x54520e8565e1150481a2,0x68165585514818759561,0x58551481a45956154520,0x48387595615452069d65,0x5956154520e916558551,0x545205978458551483a7,0xe916559151481a059564,0x59551481926416454520,0x483875d9655452068576,0x64165545206499059551,0x5452069f915955148394,0x69f9161951481a0e4586,0x59154481765978454520,0x481a7595645512068165,0x5956455120e856559154,0x551206997559154483a7,0xe857659554481a45d965,0x59554481926416555120,0x481a0e456555120e5190],#[0xa61765512069b945d554,0x551205918260154481a9,0x59564e05544816560980,0xe0554481a95db8155120,0x48165643815512059190,0x60980595205d58260165,0x5952061f936056548394,0xe819161d654809464587,0x61d65483a36458759520,0x483a0e51875952068794,0x6438159520e979461d65,0x59520e8197e056548175,0x2617559571481a9a1f81,0x59571481865d5655c520,0x48098641655c520e8185,0x65d655c5206499059571,0x5d52061b906157148098,0x6879459774483a0e5186,0x59152541765d16454950,0x543a25d96454950e8974,0xe497454950a619059152,0x54950687905d952541a6,0x687925d952541a4e4176,0x5d952541a4e497654950,0x541a75895258150e5392,0x5915258150dd16254960,0x58150aa56454960541a9,0xdd182549605416460952,0x54960541a16595258150,0x543a2659525815069196,0xe11525815065b7454960,0x58150649915956054196],#[0xe4991595605439164565,0x59560541a2e456558150,0x541a1e496558150e4b91,0xe117258150e539259560,0x58150597945c96054394,0xe9192dc5605419258b71,0xdc960541a15977258150,0x543a1597725815069165,0x6477258150e9165dc960,0x5855059784dc960543a4,0x64b9059561543a064965,0x59561541a2e416558550,0x541a4e49655855068b91,0x6477258550e1191dc961,0x58950e9190e0961543a4,0x687905956254194e4165,0x59562541a4e416558950,0x54394e416558950e4b90,0x59580589506939159562,0x58950e898560162543a2,0x617946016254165e5180,0xdd162543a2e518758950,0x5419460b8059550e8965,0xe0b805955060991e0165,0x5d950e4d826057654192,0xe979460976543a0e5182,0x58b7154182647805d950,0x547a460962dc550e5182,0x64165585516499059561,0x5c15168b905956154792,0xe51825877054794e0961,0xe83ec1bfa460961dc151],#[0x5a3a719e8bf45b62cf07,0x1b987cb6a4db1ea8ed47,0xd4e69d34d9a5cc7a63b3,0x3969b54d7a6b735a9ab4,0x4f3a79539e9cece72735,0x54cea5d527a8df4679ed,0xf54769f54eea75537a9b,0xb1556aaa553aa7551fa8,0xcb563aabd55caadd56aa,0xb955aaacf5676b3959aa,0xaed5762bad5d2ae75732,0xacaf64fb0f5876c1f5e2,0xab555a72d3566ab2dd96,0x36e1770ab6d5b4ad956b,0x17b8b5c56e29713b875c,0xc76e3971bb8d5c66e317,0x756ba9dd3ae9774ab8f5,0x5e4af1d78dbc55d6aeb1,0x57cabe45e72f35798bcb,0x7627b0dd867bf45f62fa,0x3b91bc87e3ab1b58d6c6,0xad653b29793ac95e47b2,0x32d98ecb5657b2b995bc,0xce9672b33d99dcce666b,0xb49da1dd0de83f3f19da,0xad556a7b533a6ed35696,0x6762db0fd876c2f615ac,0x58da5ed2b675b1cd8d6c,0xe73735b98dc76e2b6b5b,0xc1fe0f7077837c0fde56,0x7277935c8ee45714b85d,0x7d1ae89743b9b1ccae55],#[0xcf563aa5d4ee8f7473a3,0x35d98ec7762bab9d5aea,0xdf86bc1de0aed47673b,0xcb5e58f2578ebc55e1ef,0xf4d7a67d31e8ef467a2b,0xbe17f0af747b2bd91eaa,0x8fa57c73e35f19f8c7c3,0x23f31f92fc57e27f11f5,0x6c8ccb6d99257db224ff,0xd99f4cdb23e98b666633,0x765451b4ca6d66193a62,0xcb10bce1a1f78c343f59,0x95dcadda3af598659e2a,0x256d59b471afb62e3bd5,0x609ef30c13e36182147d,0xc13cce582798cb04f7b8,0x22d6db04ebba609d734,0x5bcd640b61972126bed,0xaf0b0c14ed5942ee4db,0x1baa6983590cb06903b4,0x32c7da06245a60de42ec,0x1dafb422e6728453bed0,0x5a276446446c890d6d91,0xdc85949d54b293321652,0x4c6d9126456527d52ca4,0x381860e3af681f636c89,0x6832a21bf6583d60d307,0xe36187489d90a0b7b912,0xd4ba0a647a61dd974c3a,0x59ba17ec30c2fd861855,0xc76e2ce3ec4597ec30c0,0x16d85c2dda0b587b616e],#[0x8c30e05aba1aec30c356,0xba1b8b36c389ce18713,0x70c3f9c6187f88cb0c67,0xed87f13cb0fe25961fce,0xd90e4c3b420987683e16,0xa71e227643c16ed0802c,0x5261a9594c552b29622c,0xd0a2c3d9145cbb229423,0xa14175b32830b64502de,0x436c234c692d6d8c0b2d,0x867326ccce6cd9198b7b,0x80352db19041b4329836,0x9cb5564394d30c00b865,0x38967727091698e7a4b2,0x7a836a4ef50b29e0efb0,0xeb54539dae1973ccfaca,0xd181b23a167687560ec8,0x41b4c7e586d0e8b8d99,0x1b85d90459da1fee1964,0x86d5d1f4d9b23ea47688,0xf9d54075436c7b0f6d0f,0x5174c0ba26981784cb02,0x26e41f7ecb037816506,0x9fd801c45ba0229f6002,0xc9a1424cb5089026e814,0x7374861b6c10f5253a12,0xaecd0aaeda20d69b3418,0x8d923d13b24823f68955,0x9b247183688f326cd1e6,0x34c979c6d534035d24c3,0xecd45d4bb287cd6551c1,0xdc28277b84f0cb6e9f46],#[0xb853a9f70a7ea6994c9d,0x74a93e6d953c0cb2a30b,0x5963c0c32c3a97658053,0xa2b3abb455752ecabc16,0x45729f68ad9cedd5945d,0x4b253ed15e99dbab94fb,0x1a068dbb3ec9656d0cf6,0x35e11a76ea1766ce276e,0x819d364d63aec9a2e4d9,0xdcb6962196c343f1b96,0x6618dc2e859b75d5ff2d,0xd781865af52ecb5ea619,0xb30f6eb6eaed169a0cb2,0x766ed16fb1dbadb83b45,0x22ddbae14fb45c56768b,0xc31ba5ca7b6cb9536d17,0xb3768c1096e5762cdbae,0x9cee983bbda3045bba60,0x85da30d4fb461eef68c2,0x53b35e8b368c0166d179,0x6f68de4c6d18099dbaf9,0x9eddbf61da37db7b46fb,0x6db388fdb4709ff68e0a,0xbb47675768ebea6d1d43,0xf6ee5a9e9dcae1d9b919,0x5d994c2da3a5b7b47330,0xd9317199665f030ccaea,0xb76236f64c4136dd8a3e,0x68c8d7edd89c1d931167,0xd18cb3da3199bb26389b,0xa3307db266d1748c9c4e,0x77bc82caf83f6c99a7fd],#[0xaf4256d9ea52da3d611a,0x1e0a3d93ce85867a582c,0x3bdb5b27936f68f0b0e9,0x7b0fb64f6c6ec9deb3da,0x12ace922358d24329576,0x26a7da452b1b2896232d,0xa9d767f4af46fdd7ed2,0xe30f64f9c4ed204b3da4,0xd806921cc3d93e841b47,0x4a1d845ac9a28bcd34f1,0x51fb4942c76919506c23,0xb1f6121496c24425da49,0xe05966a17da49c13b493,0x7cb2ce761769b6daed35,0xd9979bdcaed3abb5da73,0x2f612ab068a5201da4e2,0x4e9260b3d84b695b0965,0x3d84b835b4979fb65319,0xfb3a7807693413ec266b,0x7693dd85da7701d24f00,0xe9a86f65251403b4a311,0x4a501ec949fc07454281,0xa2a1005753e7ae5280f4,0x674198e9a8737d2d0a77,0x92dd11d2d3a37a2a7117,0xa56a1165b797f696e86e,0x4ae567495fb0e92bcdbd,0x563066eaba70da574e3b,0x2c78dd958d67b4b1b0f6,0x5806db4b127f6564c4ed,0xb11d3636239ecec075d9,0x6dbe596d875d9584e9b4],#[0xe2bbd9dc21165ba1c769,0xa63fa3b3c7f476561eca,0x51d3656b1aeced520d15,0xd83596f970b2dece7b3b,0x56eb2e4473b0bcbe2cb7,0x491b6a99336953995972,0x527495257ecaa148bb54,0x9ecaac11d9d5427b0aa,0x2dd955857b3aa83f6757,0x5bb0ac43b495914eceae,0xd7677f26ed30e71da618,0xe6930475d95fa41a4c08,0xdd1e2e17a6c40df65808,0xba4c6bfb498c7de9314f,0x2cb9781e9b1f11d2e39e,0x61089f0c210e6965cc5c,0xc3077d5a60e7930845e9,0xb41022f721e6cedc3dd0,0xc22f569442d9db881db,0xc8476ad2097a16513f33,0x9098ddb911b5366236c6,0x615f7b0c2fef61854d8d,0xe2c73ed059a6c30c3958,0x86ddec30d7c5841af7f6,0xc5b3b41bd7b0c38df61,0x19e8b2c34e261865d8c3,0x3faf6587f5ec30fdcfb2,0x8431dd0f5b3b21ed7b6c,0x6371862b77aca5637edc,0xbb676857ef660ab5eca9,0xbef594b7ccc2167bd862,0x9b8c317fbd652fee30c5],#[0x9cfb42d7bb625ae5594b,0xf2b0c5eefedcb5de5b96,0xaf654c5b9db9754bb42e,0xa8d898fc1b130d5b0c62,0x95b42839f6453c9edcc7,0x7b626e05ee8d4cada151,0x5ee8df92d31bb29b4376,0xda1ada9b335b63646b0,0x3b43457b7064af6d0c8d,0xb600567edc0719cb9b06,0xedc0bd65b817d1b102fa,0xda019a5b3035ab4808eb,0xb044b3b68094d6e00cce,0x628ae56c115dcd8a27bd,0xd10766d221367b745723,0x9a2d89b245b136888626,0x64a66b6294ce6c128bcd,0x48d17ed1188bd92471da,0x1382fd924a99b646d6b6,0xa58bbb44cdd32c9b9e69,0x521ab6a988a6953114d2,0xa7b56914af3d8a8bddb2,0xb6efd9b39e3b1673b762,0x4ecda469f2b64dcb3595,0xc32f6ed473ed1a767d23,0x2736c9b2dfda355cdb26,0xbeed8c1517b98238f66d,0xbc17684e9f7305d32e60,0xe495307962a615debb42,0x436ce0ce7d942327a983,0xabd8b0d15b285a0b6906,0x97b176f2b62ed216dd7e],#[0x9b68e7f6ecdc9efd0b93,0x36c5d0e7d8b95cdb773b,0x6d93c5cdb174b9f62e67,0xd767f90f68ff556ca2ae,0xb62fb20ed20231dbc02c,0xe922f68d245fdda28bb2,0xd846d93b78c3a76917b4,0xb08e377691974ec232e8,0x491eb368a3da6b2c81d1,0x9246ded847dbfb48f58f,0x149915b29269aed2396e,0xa4153694ace5d6972ed,0xd494a6d28e96d9d1d97b,0x25657d95348db4a65030,0xd6b2576a210769326f6c,0xb96d76375da6c6eae7d8,0x68746cacccad8dcd95b4,0xf07bda5de4da4bb8f769,0xea4f94bb49b29761eed2,0x4aab6385736c7083dd85,0x628ed7203dd860d89b1c,0x925d264dd3b0c9e02cb9,0x77b4ca9e3699492e932,0xc602c004280640058000,0x1c7031c059809d811901,0x815f829a04ce08c00ff0,0x440e101b30342062a0ba,0x448084410081f103c207,0xc25c84a00918120c2310,0xfc15a02a9852d0a04139,0x6210bf6178c2d585900a,0x4352867f0cce194c3198],#[0xe61d783a4872d0df81b5,0x83e104a1ff83e2879a0e,0x446f88b4115422384390,0x8a26ac4c489521258244,0xa63147c288050109eb13,0x457b0ad4158c2a805420,0x942ed45c48b6a167c2c3,0xc8218d031106140bfa17,0x467e8ce1199c32e064e8,0x2e35f06af0d3c1a5c342,0xe4a1c5438286f10dbd1b,0xc77a0ed51d763a4c7378,0x683e4c7bc8f5c1e903c6,0x6c208240788038fe11f,0x89310f721b042c084d9,0x1047848d9118e22f8450,0x2c2253a49f492b922924,0x9b31353265e4c349731,0x9e50b8a0593fe279c4e4,0x50b29ba52e0a4f146f28,0xcae015a22b165570a9c9,0x685a64b3896432c20576,0x76f2e6c5c64b7b96d42d,0xcc2518232ff65ea0bc59,0x6c6468c8318de3184620,0x9e73378666ccbf995b32,0x8d509a8134c068e8d089,0x326de4dab9b2235c26b1,0xc76389670bcdfd1bc937,0xce929cf7399072b8e4d9,0x847684ec49d7c3ab274e,0xe6e3c907874efe9de03b],#[0x8f8b9ef83dba7af4f4c1,0xb47f0cfd71f893eba7cc,0x55408a80c90091ff13f,0x908ca10341aa82c90432,0x3487c50d1a17b42ce851,0x2c9452289ed126a23244,0xd1b7a355465e8c5d17c2,0x168fb91e623ae47328df,0x4b0491691a922aa43148,0x52b3a5524a3c93e526ba,0x6e9885304a5db4b56960,0x7074dd69ac933f26594c,0x93c727754ebe9d013932,0x18a191417a8104fee9ed,0x93c5236a411472a8b751,0x550429e95398a6854b62,0x9eaae954daa5b5498a8b,0xbae572cadb55992afd55,0x5618ac1157d2af495e52,0xa2b30d64eac7758acb0e,0xd385a30b3e1673acdf59,0x56e5ada95b0cb5c16ada,0x82ba8573eae475c3eb7d,0xf3b5e3cbc01778aed05d,0x97f92fc55f3cbdf97afa,0xecc31984c3073608ec06,0x1c06330c5e58a4b12161,0x994232586470c8618f83,0xe4cd3599332fd65a2cac,0x43d6828cf899eb33a766,0x1a87b4e7696ed239a31b,0xcad745ad535896ac2d4e],#[0x6a66cd8d92db0db5f26b,0xdb9cb7166de2dba5b63b,0xcdf91be6b7b56f3adda,0x85f70a0e121c1cb82570,0xdc6ab8c67158e22dc3db,0xb0e4e9c92390a71f6e38,0x9e6737ee659cbcb96672,0x9d453a727492e889d02b,0x4ebe9d743acb7554ea8,0xb527684ecc1d8b3b0e76,0x5de03baa7734ee25dbcb,0xb8f111e0fbc0877deef6,0xcc8795ef29de47bc7078,0xde9a3d267a0ef3b9e6cb,0x7ef675ebebd757ac6f50,0xe377c38f805ef0bdd97b,0x5f52be837cf6f9b9f26b,0xf8fdd1fa63f2f7de6fb3,0xfef7f9cfeedfcdbf8a7e,0x604d406b808900b2006b,0x8d04b6086c0f181c3032,0x18a82f905ae0b1c15682,0x20f3c1df83af06f60d14,0x1909b612ac236842707e,0x2f185bb0b12155c2a385,0x21acc33e866d0c62184c,0x350fe61f043aa87230da,0x4dd898f12ba236443088,0xa2b1c52d8a39143e279c,0x3517922e545a38b0915d,0x6c38d4d19ee333c63a8c,0x2393c71f8e231bde36dc],#[0xab1eca3cf47858ed71d1,0x847905b205e401c7ed8f,0x2449488090ef21be4334,0x3d2436478c8d7918d22b,0x9a8931d25ca4ac493292,0xe511ca14941927aa4eec,0x952b065494a6f94a528a,0xb0695e92bb25724ad295,0xa5b5cb6396a32cfe5934,0x6b2fa65e74bbd974b2e2,0xdf01d8578981e045f0e0,0x5de0e01e023b89d8c06,0x8d037d0fe00f88071b8c,0x7d82072025f0578cc1ef,0x837f0243701e046b89f8,0x3df83b84227813e8a020,0xf41f88af87783e85a1e2,0xc1ff88051d0402b98c52,0x5d8fe8c04f02641f21f,0xc2632f985a8b410a1fb,0x8a28a5f8f0a5227827d0,0x1c857850a3d88076053,0x201823f42378e41205e7,0xc8a82bc88f0182281e01,0xf03c45e237b83c12c13,0x291558ca263ac43ef85b,0x648261aa09c0a283c8a,0x12069d8a98d837824610,0xe82322302a43c12a0614,0x38968ae1e786f0261fa8,0x89122a19a004a3820d87,0xcd89b8ef0582a92a057a],#[0x22450788027e8fc8e02,0x29c0a6197023881b1a85,0x703eb8d58bc21441f859,0x5a52821fa2752bc22e2,0x8904022e633786ca2626,0x752278d600212531b8be,0x58801d04483e330a2323,0x278a142b6134274a5989,0x4385e8102e22468c2229,0x233300704d82f8318d18,0x1192a52ab2b433a23922,0xe05803c0370100118104,0x9c0da210041a11210f0,0x2681263781998a522711,0x7700820e124a5a1291d6,0x136e8c13602832612673,0xaf623b01e8291e42370b,0x98445780a584a1213e1,0x66c36c84612620e0042,0xafc8d88d43607528a68a,0xb61e9a845505443390a2,0x6100a538c129014d288a,0x4082fa0b19c19c34006f,0xea2ec2042e6290212208,0x630732928a202a351170,0x37604d8b98f636332e84,0x381da19024aada0822aa,0x58f705065012e882ac92,0x1c1ad12ad0400b134135,0x98a83360ad05105ec2a5,0xc22ca54ad1266ad21d41,0x8da8dd0b0aa2abf0a912],#[0xa91942942042ad8512f6,0x13c42451f4aa464e220a,0x1a41940b188625500684,0xc70c62ed8c0482a45143,0x12c42849c81cf0622c89,0xe1918a12e38c38a708,0xc88aa8a58c08a601a044,0xc82c8a783c00382c1018,0x8738390498ac40ca1304,0x4f8fce8cf890c615e03b,0x980dc10987038b950c89,0x3bb320d0f356e04d0297,0x5945c00c7f6d06870638,0xf42b5e0352a6a5efa2c2,0xb808712501353831fd72,0x27353001e1f93500d879,0x707a2e2b30110009d5f1,0x24b35251c8e814491a6f,0x718052c5f4ae300a593d,0xc05221ad13e0e6962fa5,0x7fb0c801fec3261ed0,0xe4425b97e4425b97e442,0x7e9144526397e4426397,0x860111bfacc24b0b3067,0x7ef9384021ade9106be0,0x920e5e80c552da5e0835,0x11eb648388435bf41002,0x18666e60a7ace34c8bc2,0xd6fd2188a4c6508303e8,0x63af0624bd65ba334c8,0x6682129a095e148a46cb,0xcf890fb7f98c5a936f8e],#[0x1d3fa089ff120e9c5ce8,0xd521431bd51400855e02,0x301574b400b70a9c02e9,0xa3043a4e7b0b3f952013,0x2f041cb2f041b326caa2,0x102a6efb6fe800cc014b,0xc1050bba989168fdd76d,0x9949ffb802b350439bb7,0xc7944999b794c2e2edc0,0x2c48c9fa00324f9343e6,0xaf012284d783c4142ccc,0xe01db15d4450abc2c48b,0xa984f52247c13c4ca,0x1353f7028e1436dcdd43,0xb2892fc88021a94f3c2f,0x2015283ff0098414349,0x58e40149ed3c10787f88,0xa5a9177721228fe0089d,0xf7fe0112f811d3c105b,0xc00ca8822df08012904,0x85b9aec4d7fd681347f,0x1429dc48d12901cc06e,0xe9813203c901427b9336,0x3bfa28ca4dbfd1465247,0x2991c798c2130bfb18a4,0xa30aa52fc61888cc5faf,0x5107c4928a4d249d7e96,0xdc46154b23c00ac35f92,0x25b0c25c3f00252932fc,0xc2962ff212169fd4624,0x1588d9e05b74fea0109,0xc030aa55ec12a8d1bc20],#[0x3bb320d114bc6610007f,0x87f813632d3a466f0638,0xa6e7cb10023fe50c252,0xb2bee640a969f3245080,0x92560a0b0c8fb9902a45,0x142d1e430e5215a90b0a,0xec2a4666c20e121013d1,0x1df6eda413307d62cb02,0x7015301272781665d015,0x1d61e97c65601e5e0599,0x280a587980284a1cc426,0x76201490e564189e6743,0x5206a5abfed2020a956e,0x11050c5cbe08996cff90,0x9d1ed932272c6367fe8c,0xc00000de2757a6dff048,0x295222a5036f93aaa2b4,0x2f97a0e5ff7ec72156ff,0x9840f69536cacfa24d08,0x4b1d3538137b28d9e7e9,0x15e2a36a2b3a302ef2fa,0xbfe92861e98a4460b194,0xe8d126c437ea50a58505,0x15a8dbdba19c309853d8,0x27393f4181c7372ac312,0x9ed651cbf412cc1710f6,0x3437b91ca4d3fb483526,0x41910c93e722c3c3e2ca,0x24296dfcdad10859736b,0x50987ae4e86942e5cada,0x1fabd5a926fdc5a8f076,0xc043892809aa19d86c1d],#[0x6505b0f8dbd86c38067,0x3144a1bc7e4cb0c09b8f,0x44077f6d13701a3dff3b,0x8647cde836758495ed6f,0x43c6d6e18c2b3f7b38de,0x3ff4046014a6f9241ec8,0xa31bca8b19a007871869,0xa8bac3b7fa47290cf91c,0x9b7f82d1f39b44a12af7,0x584a963feacd903d20ac,0x2295285fa477149176ea,0xe41a8eefb780d4917946,0x83179379084fa9a0f4f,0xb01a18bcb6f4a0337bd8,0x445c117f85901951162e,0x23e260210be03197c063,0x19f47061841411f0842,0x522f23816c3272ffaa6f,0xf7ee52dd9a1a8de9dc52,0x66183c319b01a1bbc063,0xcf3b4b8b661c84365c17,0x41c0ca23e4f3c294858c,0x12c1c746b1f5c123c569,0xfc438bc694b88a981e,0x9e602185e9f80420ce62,0x4a5b2c2b7812d092ff95,0x49e42370860dafad0aea,0x99fde03243f6087cc84,0xf80da473a1951b2683ed,0xc24b360a2c5e0369208d,0xb010b06f6105a477e7c6,0x3ef0196de0da68462bee],#[0x72c175fd680f0175337c,0x679bcf3a9ba967c48445,0xfc873d1ca58ff3943cc0,0xf068684f7f20a25e70ac,0xfd89f0843c9630b1a935,0x83fb026f13453753b01a,0x8af5d41e87617a37430f,0x29397a0c6f2a2179a3b0,0x45e2c96d244821e0fb94,0x689e4d386e369c217e61,0xfaa01988005fd19d80ca,0x48e0c577bbfe0990a13,0xc3b3a144e6762e8d0788,0x4d847ff2411b0c931dfd,0x126dce6940004fd79a67,0x94993518b0e4e25d47a7,0xa83703f3ac7b0e4fd166,0x5b5d840bed5cd0b2e300,0x986ffe92daea5de421cb,0x80308053e5e47616c81a,0x96179c15203297af0be1,0xb11ae8510061f1651d2d,0xd900300a88f0ca771591,0x54af8a4cf80a1b2e7c09,0xd843612bd5d836906f,0x795f14603ac8d868bc10,0x1a144c9b8290495f149a,0x850093e830f4f457c526,0x4996e74112979fb840c1,0xcac499300a665c5565cc,0x419bb2a112f1244691cf,0x80d47748af709a3862e0],#[0x3ebec086a4d7ea341f5f,0x2e2c2b3e0c0424afb12c,0x52abbbe42402185c1d,0x86c69f820c04371072c,0x58a57c09caa4174f910c,0x9f90b788252d2e6cabc1,0x7fe001b1199bf562342c,0x76b028c5fd58f26021a5,0xffd10014b5b6a7309896,0xbca01862d1f21810a015,0x358f2e2094a57e015465,0x67701ce1bbfc4a00890d,0xbf163112162fdac42229,0x72c5ad5312b6b75aa620,0x44e8cc55bd5d4f498053,0x87004d4ab6534a084f94,0x43e5c34293df805a0d0a,0xc3817c3336d2ba4250a5,0xbcd408517e0da6c06860,0xc90510ab394c80cc447f,0xf3d530f37900c37111f8,0x1c087210f4fcc8805270,0x3c006c525f8830062,0xeb8a6d34fcb1ac3c3b9,0xfc18084d1ee2661cdc6c,0x1257c5271fa2be290031,0xa084a63a04af99a229a4,0x8b138f0a256f09889f75,0xae2ef51838ff41099782,0xfa083f70201ee041e609,0xcf01854bfd9ec3bdc1c7,0x716c429d8ac26c0b6210],#[0x6c2f31e051dd034485d8,0x16f18620185f28fa1b15,0x8fa6f51c1fc9180a405c,0x310cfc6b105231a3aa8c,0x6de0516de05116f69500,0xac4b7c84a3e9f6156180,0x897c223c461005908076,0xf06d70410f9ba0c2d6e0,0x68947ab85afa415ee080,0x6bca4b57b84a3d5c2233,0x3f9468f305878145e0df,0x7827b01c200dd80c2731,0x2d5d8c379ec616356088,0xb4622bf104a387030c0d,0x275f74130e07a4130c02,0x19a0f5ab61a10038b1ae,0xeab0f6e0a2e78cd07cf,0x310068e63c3009a0e2f,0x6ba76331738e1757d87c,0x88c67af8300023fae658,0xc3b5e0c30201bb8ae301,0x3f179ec61f7062ddcd14,0x87a945b3b5630e36e40c,0xd9730704c522c7c78148,0x5d6b70b6729f438262fa,0xa07a4130fefa128d2e8,0x37bc1009a0f6e0e8eeb,0x2f3788005bf14cd5e143,0x4bc3001cfc529e100003,0x8f732f0af6d70618019e,0x8bb4c200cb7b4557b0f6,0xe046fd28b18209170185],#[0xe048b8071000df90147e,0x4417a3d8c012f31f189e,0x38cbcaec76b13c02c9d2,0x5a013274ed7cd1646ea9,0x781eb4dba25d5037f915,0x8372880faa2d5dd61003,0xbd169a8bc334147ba483,0x947cc0eb982038fe551,0x63c36145f96446a463e0,0xf2036186ffd288480d8c,0x85d4382022fcb22352d8,0xc9c26783a41f3e5ef466,0x8605bb91e247c148359,0xe215e254098946a09a30,0xd64257db150f6b0b7b5a,0xfc6227ae0a576b0b1e6e,0x9dec0a392d47889eb82c,0x8529a8f1177c2010000d,0xd428e5b51e2a6f0acf01,0x7f8406524b64164f072c,0x807e165d4651db62bc50,0xf1ed071e9e84c5c090e2,0x19ada400c702003d8e94,0x81f84c3d90cbd1bde4,0x61f0800075fd89faab43,0x37138e924e1987c20000,0x27e5a3004ad888be1aac,0x13ef060dce882b3ef101,0x4f84e0c333ef]]
def g253H7 := limbs80 #[#[0xb00b8a80c6200699a402,0x220180700a641c0a8b99,0x81547410c4e43b8360b2,0x18200020e00000138b16,0x38d2bc0000000024d00,0x37c8780010c17d0000,0x50740000000713000000,0x84089092500000000000,0x3496c006488160015ee8,0x80800000c320038dc3d8,0x22000706c00007c26,0x78006380028421500000,0x374658181b8000000020,0x84684a04800c0384316f,0x108817]]
set_option maxRecDepth 16000 in
def g253D8 := limbs80 #[#[0x59554485105915448510,0x65d54485105d95448510,0x5d56548510a5d5448510,0xe51754851065d6548510,0x61774485105977448510,0xe1774485106577448510,0x551525091065b7548510,0x59552509105915250910,0x64552509106195250910,0x65d52509106595250910,0x25d6550910a5d5250910,0x61565509105d56550910,0x64965509106416550910,0x661655091065d6550910,0xe617550910e5d6550910,0x65d85509106458550910,0xe418550910a5d8550910,0x597805091054b8050910,0x54921541106578050910,0x58921541105512154110,0x59521541105912154110,0x61121541105d92154110,0x65921541106192154110,0xe512154110dd12154110,0x58942541105494254110,0x5d942541105954254110,0x61942541106094254110,0x65942541106554254110,0x59152541105895254110,0x5d152541105c95254110,0x61152541105d95254110,0x64552541106195254110],#[0x65952541106515254110,0xdd95254110dd15254110,0xe595254110e515254110,0x54961541105096154110,0x5c961541105956154110,0xdc961541106096154110,0x5916254110e496154110,0x5c962541105956254110,0x60962541105d16254110,0x61962541106116254110,0x65162541106456254110,0x65d62541106556254110,0xa5d62541106616254110,0xe516254110dd16254110,0x25d6554110e616254110,0x64565541105d96554110,0xe4965541106496554110,0x6117254110e5d6554110,0xe5172541106197254110,0x5958254110e497654110,0x61182541105d98254110,0x65982541106198254110,0xe4586541106498654110,0xe5d8654110e498654110,0x61372541105977254110,0x653725411061b7254110,0x64b765411065b7254110,0x59542545105894254510,0x61942545105d94254510,0xe4142545106594254510,0x5d162545105956254510,0x661625451065d6254510],#[0xa616254510a5d6254510,0xe116254510dd16254510,0x25d6554510e516254510,0x64165545105d96554510,0xe5d65545106496554510,0xe1172545106197254510,0xe497654510e517254510,0xe5d8654510e498654510,0x61b72545105977254510,0x65b72545106537254510,0xe1b7254510e137254510,0x597825451064b7654510,0x65382545105db8254510,0xddb825451065b8254510,0x619545491064b8654510,0xa1d545491061d5454910,0x5516254910dd95454910,0x5d162549105956254910,0x61d62549106116254910,0xdd16254910a1d6254910,0x5956454910e116254910,0x649645491061d6454910,0x5d9655491025d6554910,0x641655491061d6554910,0x65165549106456554910,0xa1d655491065d6554910,0xe516554910a5d6554910,0x6617454910e5d6554910,0x6617654910e617454910,0xe617654910e517654910,0x58981549105518154910,0x61181549105958154910],#[0xe4184549106198154910,0x645865491061d8654910,0xa1d865491065d8654910,0xe498754910e5d8654910,0xe558754910e518754910,0x656875491064a8754910,0x59774549106628754910,0x64b745491061b7454910,0xe1b74549106637454910,0x663765491064b7654910,0x5db84549105978454910,0x65386549106478654910,0x647875491065f8654910,0xa6087595106488759510,0x21d8059510e497559510,0x60980595106058059510,0x21d81595106498059510,0x61d825951021d8259510,0xe498759510e458759510,0x66287595106568759510,0x65f82595106478259510,0x64787595106438759510,0x261655c91064b8759510,0x597845c910e61655c910,0x65b855c910657845c910,0x5db825d510e45865d510,0x653825d51061b825d510,0x64b865d51065b825d510,0x64165dc91061565dc910,0x66165dc91065165dc910,0xe6165dc910e5165dc910,0x65584dc91059584dc910],#[0xe5185dc910e5584dc910,0xe5182dd510e5985dc910,0x5954250120e4986dd510,0x50951501205d54250120,0x58951501205855150120,0x65951501205955150120,0x59152501205515250120,0x5d952501205955250120,0x61952501206155250120,0x65152501206455250120,0xe5952501206595250120,0x64965501205d56550120,0xe45655012065d6550120,0x65975501206457550120,0x5915254120e517550120,0x5d952541205d15254120,0x61952541206115254120,0xdd95254120dd15254120,0xe195254120e115254120,0x5d954541205915454120,0x64554541206195454120,0x65954541206495454120,0x5496154120e595454120,0x59561541205516154120,0x5d161541205c56154120,0x61161541206056154120,0x65d61541206516154120,0xdd161541206616154120,0xe516154120e116154120,0xe616154120e5d6154120,0x59562541205516254120,0x61162541205d16254120],#[0x66162541206556254120,0xe116254120dd16254120,0x5d964541205956454120,0x61964541206116454120,0x65564541206496454120,0x661645412065d6454120,0xe456454120a616454120,0x25d6554120e616454120,0x64565541205d96554120,0x65165541206496554120,0xe45655412065d6554120,0xe5d6554120e516554120,0x58971541205497154120,0x5d971541205957154120,0x65971541206197154120,0x5957454120e557154120,0x65176541206457654120,0x5498154120e457654120,0x58981541205518154120,0x61981541205958154120,0x5958454120e498154120,0xe4984541206198454120,0x65186541206458654120,0xe498654120e458654120,0xe5d8654120e518654120,0x58b715412054b7154120,0x64f71541205977154120,0x61b74541205977454120,0x5db84541205978454120,0x595615452065b8454120,0x61161545205d16154520,0xdd1615452061d6154520],#[0xe1d6154520e116154520,0x61164545205956454520,0x5d965545206416454520,0x641655452061d6554520,0x65d65545206516554520,0xe1d6554520a5d6554520,0xe516554520e456554520,0x5957154520e5d6554520,0x61971545205d97154520,0x61974545206597154520,0x645765452061d7654520,0xa6176545206617654520,0xe458654520e1d7654520,0xe518654520e4d8654520,0xe418754520e5d8654520,0x61b74545205977454520,0x5db84545205978454520,0x65f865452065f8454520,0x59564551206438754520,0x5d965551205d56455120,0x641655512061d6555120,0xe45655512065d6555120,0xe5d6555120e516555120,0x64575551206197555120,0xe5175551206597555120,0x65176551206197655120,0x66176551206557655120,0xe457655120a617655120,0x5918055120e617655120,0x5d980551205958055120,0x61d81551206098055120,0x65d86551206418655120],#[0xe518655120e458655120,0x6458755120e5d8655120,0xe4187551206598755120,0x5938155120e518755120,0x5db81551205978155120,0x64575595206438155120,0xe1d75595206517559520,0xe597559520e457559520,0x5d5805952021d8059520,0x60980595206058059520,0xe118059520e058059520,0x5d58159520e458059520,0xe05815952061d8159520,0x2518759520e4d8159520,0x65187595206458759520,0xe458759520e418759520,0xe558759520e518759520,0x5d781595206628759520,0x643815952061f8159520,0x65f81595206538159520,0x5d78459520a1f8159520,0x64784595206438459520,0x643875952065f8459520,0x261655c5206478759520,0x615655c5205d5655c520,0x645655c520641655c520,0xe61655c52065d655c520,0x659755c520619755c520,0xe41855c520e15755c520,0x661655d120641655d120,0x619815d520e45655d120,0xe41845d520e41815d520],#[0xe51865d520e41865d520,0x65b845d52061b815d520,0x64165dd120647865d520,0xe4565dd12066165dd120,0x65985dd120e5165dd120,0x5d964549505d16454950,0x65d64549506416454950,0xe5d6454950a5d6454950,0xe4974549505d97454950,0x65176549506457654950,0xe497654950e417654950,0x61b7454950e517654950,0x589525815065b7454950,0x5d152581505915258150,0x64552581506095258150,0x65952581506515258150,0xdd152581506615258150,0xe515258150e115258150,0x64965581506456558150,0xe496558150e456558150,0x58971581505497158150,0x5c971581505957158150,0xe497158150e097158150,0x5957258150e597158150,0xe1172581505d17258150,0xe517258150e457258150,0x597715815058b7158150,0x64b715815060b7158150,0x64772581505977258150,0xe1372581506537258150,0x61d52585505d15258550,0xe1d5258550e115258550],#[0x649655855061d6558550,0xe456558550e416558550,0x5497158550e496558550,0xe0971585505c97158550,0x5957258550e497158550,0x61d72585505d17258550,0x5498058550e517258550,0xe4980585505c98058550,0xe418758550e518258550,0xe4d8758550e458758550,0x6468758550e558758550,0x64772585505977258550,0x66372585506537258550,0x6438258550e137258550,0x65f82585506538258550,0x65787585506438758550,0x645655895061d6558950,0xe4165589506516558950,0xe516558950e456558950,0x5958058950e1d7458950,0x61180589505c98058950,0xdd180589506158058950,0xe518058950e458058950,0xe498558950e418558950,0xe498758950e418758950,0x64a8758950e518758950,0x597745895065a8758950,0x64774589506177458950,0x65b745895064b7458950,0xe1374589506637458950,0xe0581595506098159550,0xe418159550e098159550],#[0x60b8059550e418259550,0x64b80595506478059550,0x64b8159550e0b8059550,0x6478259550e0b8159550,0xe1382595506538259550,0x5d9525c550e438259550,0x5c9625c550e09525c550,0xe19655c55065d625c550,0xe19765c550595725c550,0x645655c950e45765c550,0xe41655c950e19655c950,0xe41765c950e45655c950,0x597845c950e49765c950,0x65b845c9505db845c950,0xe09815d950609815d950,0xe4d815d950e41815d950,0x251825d950e55815d950,0xe51825d950e41825d950,0x60b805d950e55825d950,0x64b805d950647805d950,0x60b815d950e0b805d950,0xe0b815d95064b815d950,0x653825d950647825d950,0xe43825d950e13825d950,0x60962dc55059162dc550,0x61962dc55061162dc550,0xe5162dc55066162dc550,0xe4986dc550e5182dc550,0x65165dc95064565dc950,0xe5165dc950e4565dc950,0x65984dc950e5181dc950,0x65186dc95064586dc950],#[0xe4981dd950e4586dc950,0xe4165585516416558551,0x64980595516098059551,0xe458059551e098059551,0x643815955164b8059551,0xe49615c151e09615c151,0xe45805d9515db825c151,0x64b805d951e49805d951,0x643835d951643815d951,0xe47835d951e43835d951,0x60961dc15159561dc151,0xe5182dc151e4961dc151,0xe4986dc151e5982dc151,0xe09715c165e4980dd951,0x64b715c165e11725c165,0x647725c165e0b715c165,0x643715c565e13725c165,0x60981dc16560971dc165,0x61182dc165e4981dc165,0x65182dc16564582dc165,0x60771dc165e4582dc165,0x64372dc16564371dc165,0x64980dc56560980dc565,0xe87d87786fe4980dc565,0x8fd8f78f68ef8df87f87,0x7b97797696f95f93f8fe,0x79d69be99e97f97e97d9,0x9ea9df9de9dd9db9da9d,0xfe9fd9fc9fa9f69ef9ee,0x7a76a75a6fa6ea5fa3f9,0xa7ea7da7ca7ba7aa79a7,0xd7acfabeabdabaa9fa7f],#[0x5aefaeeadfadeadbadaa,0xafdafcafaaf9af7af6af,0x3bb2fb1fb1eb1db0fafe,0x7b56b55b4fb4eb3eb3db,0xb5eb5db5cb5bb5ab59b5,0x77b75b6eb6db6bb6ab5f,0xfb7eb7db7cb7bb7ab79b,0xb9eb9db9bb9ab97b96b8,0xd6bcfbcebcbbbebbab9f,0xebddbdcbdbbdabd9bd7b,0xbfabf8bf6bebbeabe9bd,0x77c76c6fc6ec5fc3fbfc,0xdc9fc9ec7fc7ec7dc7bc,0xcddcdbcdacd7ccecbecb,0xfbcfacf5ceeceacdfcde,0xfd1ed1dd1bcfecfdcfcc,0xd4fd3ed3dd3bd3ad2fd1,0x5dd5cd5bd5ad57d56d52,0xad76d75d72d6ed6bd5ed,0xd9cd9bd9ad7ed7cd7bd7,0xcddcbdcadb9d9fd9ed9d,0xaddeddcddbddadd9dced,0xe0fdfcdfadf8df5debde,0x3de3be2fe1fe1ee1de1b,0xfe5ee5de5be5ae4fe3ee,0xe7ce7ae75e6fe6ee6ae5,0x9de9be9ae8fe8ee7ee7d,0xbecaebeebaeaee9fe9ee,0xedeeddedcedaed8eceec,0x1af0ff0eefcefaef8eea,0xaf2ef1ff1ef1df1cf1bf,0xf58f4ef4cf4bf4af3ef3],#[0x78f6af5ef5df5cf5bf5a,0xff8ef8df8bf8af7cf7af,0xf9bf9af99f98f97f96f8,0xc9fbafaafa9f9ef9df9c,0x9fd8fd6fcefccfcbfcaf,0xd72ff8feafe8fdcfdafd,0x2c37740961aba04aaa64,0xeac304b0ddd82586aec1,0x5d0268f2ca13bd786095,0x423af5960a604bb0530b,0x3204b2897025944986ae,0x2e9c488114e242f5651,0xb4e1c3a9860e15acb861,0x60e9b6c307455e903a2a,0x8655688422af4c1d36f8,0x5132e274016513caad10,0x7a21795e4b8bea265870,0x300a5268c5d2ab442e92,0x9750b2c48285971f1a6c,0x923a22195e4b90ed35d8,0x4aa0445168c852a34442,0x8ced007485c807a32e5e,0x6e8b5a237400d21da016,0x458d11c203aa4dd15346,0x1e8ce901552708a5a338,0x4e82c257541403d19ce0,0x430b7d320ce0619062db,0xac2e590c6132c8642576,0x2ec873c9854362eb2a1,0x7644072d421cea6190e8,0x22093e591049b2c8836d,0x26a30c8b075a445473d3],#[0xb5965c9b7c32e4db6197,0xb2aeb00595735a326b9a,0x97443f0cbaa1d865d556,0xec017647612ba23aa265,0xb6c323c5569d1d7530c8,0x619222ab429136f86479,0xc92155a6489b7c3244db,0x9127cb24893659246dae,0x55e911f2af428f8e5a64,0xf4890957a7484aad0a46,0x44f072d224adbe9d211c,0x85005953e3534c9e45d6,0x752caa1a639450e00b2a,0xa74f4d5d227a3469943,0x324cfe5d9268074e9ec0,0x440c344962899649dd0c,0x289965d89fd22eca265d,0x4bb2ac18689566a2ecbc,0x854f24f48a8127a15414,0xd291da76949ed229e576,0x5ed0ba003e81b523f4e,0xe91e701d52e809da474,0x251a007a37b90a4a3bc0,0x88601ba432a25963752b,0x691e52221cb451128996,0xdf450f9aba287c28d344,0x658ed44b2c7214e921f5,0xc4849e9238512cb1d351,0x950acb2b851a489cd1d1,0x4965ac51ab2cb601e8e5,0xc94c6d15967b502cb3c3,0xea649b254205ba3a0977],#[0xa807a3ab01dd1d4c07e8,0x5cb204aa1596d669acb6,0x550279730c12cb984096,0x8134b9a509e29ba04f2e,0x9a21bb04d105d82695ac,0xc9658267bf0c133dd860,0xf4c131e5a609993cb04c,0x50a1935484cc96a4263c,0x5ce56182e882ca174896,0x5cf2c172e5960b9cbc30,0x5650bd01d1056646982e,0x305eb9dd82f5caec17b2,0x2a1134c17a77860bd3ac,0x8ba40b53a5485864e90,0x2d288d2259446972a423,0x5047886e823c417411cf,0x23b25a911cf3d208ec9e,0xcc9d2092b9e504964d52,0x25944a3234825ae79412,0x4218489a212044d20992,0xc252c20612959030973,0xf661830876ec1843976,0xbb4c1831d960c1edc306,0x650c64cb206277e98303,0x64fa6103463b2a18c81,0x60db52192fd960ca08bb,0xc7760d962bb06cc96843,0xd306c96e18364b30c1b2,0x83f057501b84ba90cc37,0xfc43740fe20ba07f2e58,0x20bb07e79e903f64b281,0xe183f7bb0c1fc43760fe],#[0x21c1e7a60fd92cb07ef7,0xe21cba07120590389734,0x77e903863f281c43b740,0x54e1c439a70e240c3070,0x40ea1cb207477e903a87,0x730e6183a877481d4398,0x5fb2c1cbb5860e618ba0,0xb860edbcc30765969c39,0x3076b1e583b58b2c1db7,0x426f70c2137986108b3d,0x965a610963cb084b1658,0x3bb088b15d8443bf441e,0x98444b70c22259861116,0x1f165a410cb3d20781b6,0x8b3d387c77e883e3cf42,0xee9c3e7b7441f3dfa10f,0x4820b25a1104b3d3882d,0x11563d3882b129c410df,0xec965454912ca2a06da4,0x2ca28c399513cc5d209,0xa914208b28a0f0618519,0x8b5045945a313442d04b,0xe0db4a2dafd6516c24d4,0x1197138dbd209d226844,0xd389d0429c4e8252e274,0x85758d2e2b2c59715a09,0xc84ba415c9dd30ae62e8,0x37d28b01ee90582734c2,0x59465317443186da5170,0xc32a2f8619516c30cab1,0xcd62b28e68b2a4640934,0x12e987345f0c39a2d861],#[0x75239167a41c220d08e0,0x619c25d20e88bea47209,0xbe90e586a5ff2c33c117,0x822ec301e7a217d92c90,0xda418563cb8c0b125c60,0x10bb04e885e36f442f06,0x750934833165a2188b2d,0x849a21bc44d10da12e90,0x2d10de3de906c2234436,0xa40281aec00c65650006,0x4161a5010bbd200611e,0x60d4010b0654086eb0a,0xe98094532c04845a902,0x4c050c1a602d14cb0163,0x1c23d200c58e900508f,0x811698074570c03a2986,0x4aca3db39621ec23d201,0xa61ed3bc30f69d6187b6,0xef1f5947692ac83b089,0x908f523c2f9961de06bb,0xd651f445d00f409ea47,0xb2904616888208f523ec,0x4832134441845a920a06,0x2025a920d14cb906ec59,0x6cb8f9226807c5f2ca4,0xe9c7c8194e3e40e971f2,0x83f137a61f8c3d10fd03,0xfc85d10fe4d6988008f4,0xdd5948b1ab4c408d7a61,0x2ca460c1a622d15cb116,0x623115c31188a6188c58,0x28dd594941874845045a],#[0x582ca490c1a625114cb1,0x7a624915c31248a61892,0x19225fe8c91883404804,0x93183484a8c3a4245c7d,0xa29762652ab293211e90,0xed012e09e9899456ec4c,0x909b187484c3b17625de,0x443259221c13d2134306,0x607d110c6ce888681aec,0x16908d2c34444961a221,0x2647045a223c23d212c1,0x27060d111e096908e4d7,0x4fa590227db4211027a4,0x1b4c1126d96089ecb284,0xa708d2cca84643e98222,0x489d6842405352118c7,0xd3e74808ca15404415d3,0xcd8603615bb01b0a5d80,0xcb81ac3e580d61b2c06b,0x80f8c2ca0742a9703614,0x990fa0041d6c301f015d,0xacd28285c690142e7480,0xe8017137500b35586058,0x40e013a80681fd18343b,0x7415d0036046a01c0834,0x8b65c214eb2210811a60,0x34c10a75a1085174b842,0x20805dd103e42e881e05,0x7b1f594bd1334a100b9a,0x227405fb13942f183cb1,0xf963017dcb17d035d8be,0x29466b698a18c2c850a3],#[0xa81735053c056529e02b,0x47da128a40d0144eb594,0x3439450161ca235f4851,0x9ca280b4e51404a728a0,0x5295ba529603d394501a,0x98d314c56694a62674c,0xe909e2b7444f159a228,0x524f941a427cacd113e5,0x2dc09d4954d561ca9063,0xe04698b80634a5c043a2,0x4f0c67a258633d5cb299,0x9833546cb19a10e98cf4,0x99c046a4ce1474867211,0x2352688c1a134409d4,0x2e8730516c398204e98d,0xc895e28e90d56aaec6a2,0xb53b744582c4972bd92,0x715ba22b895d215a1b68,0x94d316626e90ae2574c5,0x68cac2b34456031a92cc,0x65915ba22c8a0d215853,0xe894d31684ae98b229f4,0x10e88b9023505d041a22,0x74a5c837a42e41fd1972,0x42ec18d297604e90b906,0x8404e90d30874869011a,0x12b4c62899a53144bd31,0xba2311144b98642e88c3,0x218c28e90c415f46620b,0xd8057406b827a435808d,0x841a431d5dca98e04e90,0x8d31900c698c90834c63],#[0x98cb0674865843a43280,0x77827a436409d21980ce,0x809d31e0046a4ef4232a,0x4699000274878811a43b,0x427e049a03f172c89f20,0x3ec4dd21f0046a0fc08b,0x40469901023487e813a4,0x8b446e913a237808d220,0xa338860d11c231aa4dd1,0x9c604aa4e214348710ad,0xc0274874827a43a057d1,0xb9a536818d21b8a35d8d,0xd11c809688e4023446da,0x8e60234872a239339460,0x5027a23ac09d11ce0ce8,0x9d21d88a648eb45b247,0xe90f60274c7a8afa33d0,0xc81813a43dc22d11e404,0x2264a121004691040234,0x135d90794aca83c89654,0x2c884b2f9641d96cb20f,0x6429e0c3213205950993,0xa7de85051074685c117,0x89b4c8344da141a26d3a,0x98544996ca2252955112,0x4a1b296950d94b2c863d,0x1394aca89b2ea943596d,0x32d9644df4c3227135d9,0xcd0a20f66a10e94b4887,0x910f7b34c883d996441e,0x8a3c196445ecd2a2313e,0x537d4228cb6911421f50],#[0xb651170934e8c885a246,0x488b26d9845decc2a2ec,0x46167d2230b7e8918867,0x85ee911a317448d22fa8,0x17448d979a647166cb23,0x524c063d42365ee911b3,0x26479e9530912ca984b9,0xd912ca99203a24ca5ca9,0xdb844b61dba25b0e5d12,0xcba5ac765d2d63f2896b,0x53163f3096b1d984b58f,0xcbb5654e208b2a6f0459,0x45d0a5e1269d395faca9,0xe5d2f5fb2e97c81a24be,0x49d06fa54d443d126abf,0xd814d42741b6953a10b4,0x1be9536107469b087a24,0x2ecac06da54ec42d1276,0x6561edc32b0f66195887,0xb4c7e5559902caacb1f9,0xdb4caf2c57657a08bb2,0x9865c951cb2b659e955b,0xa2c6b6619758734ab9c3,0x637b308b1c3b7458e1cb,0xc397658cefd22c6c7e51,0xfcb2c6f661963876ecb1,0x95653bf4cb19dda658d8,0xb431d545a1e0c32cb205,0x18eb2ad021691684db08,0x5e516410b4cb426d865a,0x2cb3aff9659a08bb2ccc,0x47652c223a77e851d487],#[0xaf66a11d8734e8ec8186,0xbf508ebdaa8474eed423,0x764821cc32450e6191e3,0x248c7659207b30c90439,0xf873428f9dfa147deccb,0x3ba447e1cd223f0ee851,0xd3a4277e91213bf4290c,0x5217b342909dfa74861d,0xbdba4485ecd2242f6e8,0x40c3279296513c7b74e9,0x6a53c63b529e481a64f2,0xa9f1dfa94f18f54a7877,0xfe40b2a7f0e655428732,0x206853d7b32aa1bc1864,0x7489ec81a44f641d0a7b,0x450241d3a7b2069d3d90,0x830ee9d409030ca01dfa,0x94ac89531d924a4fbd22,0xd964a9ecc32550e5d92a,0x324d2968926397429331,0x272cf4293c31a749a34c,0x1dfa24a208cb24f0c691,0xdd125059e9d283974894,0x912b6f74e943d3a44a1e,0x95b1da24acb3d3a5672e,0x442d129ab1e9d2b62f48,0x269d4d0db4aa6afd6553,0x2aa44816552014d429a1,0x519374c2909b6614863b,0xd065d9468d2caa31f7a2,0xd748a2481a2511dec328,0xa452609d3a890465d448],#[0x28ab165d49822eca49cb,0xa2774ea39bfa251e0dd2,0xf7a452d6fd12945ee914,0xd229812e9d4b10f44a58,0x94e05352a60d9a65307a,0xf849a753836d2a9c2168,0x19d22ed0e6897687344a,0xe917709752bb97ba45de,0xcb5b1d655ad17d4aeee1,0xaa08bb2d2216996b4db0,0xe1e91797b344bc10fa25,0x746a8b1d9254537d12f4,0x25558ec92ab045d9513a,0xa4c765152822ecaa9dda,0x902eca91dfa45498fca2,0x7a754d63cbaa7045d953,0x12ad045d9563bb44ab16,0x508272ea81b7a15418ed,0x411a454209d0aa104685,0x5d22a877e895482748a8,0x89602cb48ab9dda255ce,0xb1167a558163caac062e,0x442d22de62e896109348,0x3e896c09348b8885a25c,0x28b7a6d945bc81d1ad84,0x5b487d12da436916f4df,0x243689714df44b80c7a7,0x1acabfc0d655f062d22e,0xa05ec60d3b00ec595808,0xaf6ece1d7b7630ebdc89,0x122740bf40ea75ee06d3,0x9f9664206bb31e446818],#[0xcb33c2be8d9351b2ec12,0x9a014748cf8afa367d46,0x8a3a468508cbb40d55d,0x8ec930e04e99a202352d,0x69d8c81aecc61e5a0631,0x2c2b5787615aac3b0a58,0x2c77d030c4ae918581b4,0x4ae998928748c48eda06,0xb40cc097a665094d3314,0x365815d032c256999818,0x2c64e819503748cb023a,0x14748cb0afa365863d03,0x5a766444d03323168197,0x3b363069d9922340cc84,0xa302348ce029a067008d,0x29a667537c933a04e91,0x4d03ea0de91f40574cd2,0x91bc1334cfc011a77d41,0xdcb91766f1ecb2b78fa5,0xe08bb375065d9b98d2ca,0x9591ca14748deb65866e,0xcae3a2d767292cb2b949,0x7210ccbb8ed65d9c774a,0x283659c94232ee435576,0xfb0ed2c69a069408d4b9,0xa6699ffd3b4aff69da57,0x352c5e51a963b24d4bfd,0xc7faecd61c9a06b0e5d2,0x2ba169ca0d3b58a965da,0xd035050e91a87fb48d39,0x1aa58f40d5143a46a9bd,0x7967a06bd62d035aa9e9],#[0x52cb36250685b128748d,0xe91ae28748d7141a66c5,0x8db943a46c0b3d0360da,0xcc08d436e0c695b706b4,0x59e81b454b2ad997ba06,0x748da8c7a06d497d2364,0x6d41bd236a12e81b514,0x6c25699b618b40db22fa,0x634adc035a46e008d4b,0xd926f81ad3b821e681c1,0x3b800a681c01ef48df26,0xbf1434ee08f5a070408d,0x22da070851d237e31e81,0x3d038631699c506b4ce3,0x81fc5bb24fd0c7a07106,0x28c7a07ec08d43f8126,0xc24d040eb3e52055bb25,0x6662086d30b04011a881,0x5104035a182166d04108,0x74851d241286e9206433,0x69be51d321b44ea103a3,0x22ece890da2755ecbaba,0x8776958babb431aa5d08,0x3c828e91d84450eed221,0x506f48f3811a97a051d2,0x2ba479537d13ca9b649e,0xd03ce28e91e70274ef30,0x1e745f40f381ba479c15,0x4813a479d0dd23ce8629,0x37d13d49b649ea28748f,0xe81ec6d748f4823a37ad,0xe5a8d767390dd23d88b],#[0x3895d3396a3e59cb2cf4,0x4a685cf2cf40e6031a47,0xf2aef2cc947790dc3bc0,0x678553d2bc0a9e55e058,0xc099e51de4df24ef28f9,0x72724ef21ba778133d03,0x5a4779c3ca3bce1251de,0x1bb831e81dc6f72aef0c,0xdc43728ee2189477057d,0xa189477c4dd2bb828e91,0x154bb604691df43728ef,0x55e070f40f00c7a07745,0xf0219a1781b5d2bc0dae,0x517d03c4d5e59e143742,0xb651ed04746f726d927b,0x48ff2c7957f96fc93fc8,0x80851d23fa12699fe093,0x12e82030934cff8a3a4,0x9f29002cc948016fc940,0x9580424d2400b1e56005,0x408a9e960159f4100aa7,0x863f2514481628a009d2,0x1d728a4dad3450bfe5a2,0xd3456a8e5a2b822cb15c,0xa2a5facb16bb5658b09d,0xa2a1948d02ad145c6de8,0x25d246f0459636277491,0x5d2195fb2d0ec11a28d4,0x90e1dfa187240d3c3320,0x71ecc24390edd21c902c,0x2065a1c3bf490e31f948,0xd530d2fda986a40d1435],#[0x68857ecb43677e8a1b5f,0x3ced65a221db43114119,0x36f490fc83a287d7ecb4,0xda487d7fd0c3ebf6861f,0x244077e8a205ff490faf,0x31822cb182fd658c8e5d,0xafd658cddab2c6299e52,0x8d0c7012e923936f4917,0x9238823491c413a18e20,0x122fd9289245c8c4904e,0xa39d1c486de8a245ff25,0xd68a265ff25132fd9289,0x2912c8392894dbd0c4a6,0x89cdbd244abfe52255fb,0xe6d692275ff29139b5a1,0xfb4913affa189d7ed0c4,0x929157eb2c9ebfe92275,0xc90ec5964781acb2331b,0xd1df411e8eda08f97cb2,0xeda08fc71d1c7a3ae8a3,0xd1c96056a63f1d3451f8,0x65a08f492ba2b8495c57,0xb28d6596008d4cb4d559,0x15d24b604e925981f432,0x64a42027492ea3965970,0x1209b1a290cdad1484bf,0xd9d0c806ce864136f4,0x9de465108b45291a7a39,0xf2b29029a29452dcaca2,0x29540ad14a892e56534a,0x1805e8a5f057452f047a,0x6e2ed460e9a4a31b8ba5],#[0x565a35abc35163a69a8c,0xb520d5e1a9006f494740,0x916c70d490cda2a3d47c,0xa2794ac5aeb25622568a,0xab2d6483662b01774958,0xa2b541b0d5aa8d65ad5a,0x5b013a4ad04bd2566046,0x8d256e0469ab6422cb,0x66620c76b0d0631d9283,0xed051c7a28292d4c4189,0x82cd7d14166de820b7fa,0xa50e920d80f4505c13a0,0x834907067a283437d041,0xa083c18d4c1c4a69a0e2,0xc22056a20f0cb450786d,0xcb4d08ab97684432d0,0x43a485cadd142e56e8a1,0xd1430dae92176e7450b9,0x2140db430a31f928515d,0xa865a18558fd042a1b69,0x1dc942859686140cb490,0xe8a122cf4109165a4852,0x30ac3ba0854a7d1c2456,0x555dca42aae652152b34,0x56e8a132cf4109959a48,0x30b362fd659b15dd142c,0x59adecc2cd120596684b,0xdaed596696f30b35c116,0x9074533a59859b57eb2c,0xfa49a9edd14d46de9267,0x2ccc316826676aed350e,0x7680f453aa8d659dc4cd],#[0x43a29e94dd14f256e8a,0xad0cc686e927a44f453d,0x92635ff2931afd9498cd,0x311a7a3984dbd04c26d6,0xdbd04c0bfe826536f41,0x96926f63f253719fa498,0x29382df929c178bb4de1,0x9c5644a4e2a8e5a70599,0x410692715372d38acb94,0x274d392cba29c949cb4e,0xa4a6417d24e810e92735,0x52a0ae829b147494d0df,0x86cf0d4b8cda1a51dbc3,0x11a6af108b2d78d7e1a9,0xd1d7028e92bd177455e8,0x2c015f475f15ba2ae4a7,0xa5982a085dd157e0469,0x2cca5083be92814b3294,0x60a7f0df49418eda4a11,0x73f24b939f036d14fe96,0x37d050a9464a864972,0x1b692804b7094025984a,0xf41440e9a2a242fd1d0e,0x3a1c76d2514966528a0d,0x4c96e82881df41440e3a,0x1df4b528f7a4a9441d1d,0xba0aa815d254e9b64aa8,0x254a0ae82ad047475602,0x9e0974953add92aa0bdd,0x49a2a7963cad3cb9e46,0x1c9d3a28e929c447274e,0x92a951f2d502b395a7d1],#[0x5504ba0aa912c955628e,0x9664a544b7e4aa202749,0x2692a258f2b512cf94a8,0x4151aa795a8d65c95421,0xab147cb548a9e96a359f,0x812e82ad173455703fa3,0x234960813a4ab057d1d5,0xa3b317cb2d96ec596ca0,0x5a830e92d5457296a8af,0x80234d6ba1165b5e06d1,0xf992b0808d25b204692d,0xd15866ce8ac25f725612,0xed00d74564869a2b1cd8,0x68fda0b4c13d15a09ae0,0x11c1d9e88e0ece08b456,0xe0ed008f4568013a4b3d,0x568a2392b44bed05a6b5,0x6c08d25b42b68ad215f4,0x86e52dc44b256f22393b,0x7277121994b801fd1dbe,0x4bad14c95d28b60aea44,0xca04692e44472771a2d8,0x2349740afa3b985dd15,0x3a4bb463d05d831e82e7,0x208f346084602349770a,0x4b8b30824cc5a411e62c,0x4c1760c1fac209516610,0x6c206330698309830c18,0x943493b0c18cc1a50c66,0x194c5a10c9f8c3069305,0xa2453865245d83298344,0x4ea4353374e1ac4ba70c],#[0x481c4c1940e260c20702,0xe660d1073306a038983,0x32461839963281ccb184,0x930c21449860ee48cb07,0x96101f2c307b12658428,0x7c7be903c6530c22329,0xf3df4820c4ba70f8f7d2,0x9d641462acc09f156104,0xc20a315dd0518aae828c,0x8509232a26cc195145f8,0x94218616a24ca8b50861,0x48b28aaf161852922ca2,0x6604e923482732995156,0x829c9186158f7d20ad24,0x8d03d10b108e9c533874,0xba6186573b0c31c49651,0xb0c38c49651c4cdd20c8,0x41c174d30e6ba6187373,0xcef9594693374839449a,0x922ec339efa419e62d08,0xfa51a225d38cf1229c67,0x38d446e906a7e744351e,0x6b3df4a35a07a21adcfd,0x1efa418194ca0c066e9c,0x5cb8dcbae5c6c3df4a36,0x886f5d74e372e8a71b97,0x3ca0ba01e4f5d28f0666,0x48bd213065e909132f4e,0xa6940e9532c06ca97603,0x4807cbda103e60d001f2,0x3e1e5381f215d80f953,0x63e9c123f7480943fa7],#[0x2aec0b331940659ec903,0xa8054c0d182a63688158,0x1432a650a131b440e0c9,0xd90b48514856529242d3,0x21952ae42b29565ae9c9,0x5395323684a99234054b,0x8cf5c30c67c17a72a60a,0x7445a133624d019ab869,0xf0d09a8f9680d409f526,0xe88b16532857b7fa7351,0x85b169a42b0ddd215a78,0xf9ccd09fce7680fe2d34,0x8c658ff6fb2a7f389a43,0x7246f8cba83e974ca1f2,0x4368f7d29c046e90df7e,0xd8b8e90da5c3486d04fa,0x99b2c838cba43cc27d21,0xba142e60d12153369109,0xa1d33e850599b4282a0,0x1940f428a4c3a143a60d,0xcc1944b660c225a81689,0xd125d306612d9832e96,0x953340f4499cb1944ba6,0x97c91a44be48b2a69245,0xe48d3a5f2465d2f92748,0x2e85369233097c93a74b,0x2cac4c186560ffd1a6c8,0x56a62d0ab53069559983,0x51269d5a9232cad4c1a2,0xf44ae32ba95699454ab,0xa148503d12ba24ea55c4,0xa5081e854198742a04c3],#[0x492342a21efa14acf7d0,0xe7a15e1f2d0af124e854,0xd1aa3306495198f22a8b,0x95598324aac91765465b,0xac9176554f6d22ab3068,0xf7d0aa730e85523db4ea,0x685573df42aa1eda1558,0x8bdc8d655f448d3adc7b,0xee46c3af723e917b91b4,0x65e9d9191f4ebdc8da75,0xb24c220ba064847d4b22,0x60a36b2b07245958467,0xf30649878df48c1491a,0x3df48c3b2b9461d94ca3,0xda0634b5d3b11245d987,0x31305e5d8582b0ec29e,0x963db40c71cfa4624f7d,0x873a565847d0b2c24e81,0x6d3b32d06819966f26cc,0xd5f267b24f9337a16684,0xf8445757cd3e4c3e5125,0x5bfcc3e0df261f082b0c,0xc261f47730cf89efa07c,0x40fa8f9a47bc82d1bde8,0x7dcb5d2bec66e81f6233,0x232ea1f732f42fb99ba0,0xdf42d2c6da16953ec33f,0x82748e6d0b587b681ab8,0x3ac81689d47e304ea3f1,0x582aeceba09a0765f8c1,0x297579449d23cacf649e,0xd03cf055d9e309f4ef33],#[0x61f2d342e687fa479c49,0x7c91a18bcf7d0c4124e8,0x48c944d2464a24927431,0xe524d9274312c91a289a,0x31e9e3a28f248b2c9cca,0x320ab2c9475e8e3d3d74,0x5692569274124b01659,0x32920b01659420bd24ad,0x4910ddd2482c0e524160,0x2e2368a5237745201b9a,0x92343339eda1850b5d0c,0x5a19d5f3d0cd524e8667,0x1cc323e466182f433ac1,0x6537743311b9a49923bd,0x9e1a19bcddd0cc06e686,0xdc352ceee1a933db434a,0x86bb2d3495d199a1a5dd,0x53073a4a14f4d14fa5a6,0x48dd05529fe0aa64fb05,0x6e82aa12741550f3a5aa,0x496627b94b288cd0d5e4,0xb0a46d15852364ac2197,0xc97e52c43df416248fa2,0x774d628f1a4b192fca58,0xa2b413cc95a01ce92c83,0x5c224e82dd4e3256f117,0x1e74b7691ba0bb047d1,0xba004a001640072000,0x2e4014d00960044401c2,0xb803f401db00d5006380,0x80bcc059a02a00131808,0x1f100f1c072c035a019a],#[0xbb0244811a0087a04050,0xc054702978143009ca04,0xc6a05f702e2016600ae,0xd300e2406dd0355019d8,0x501f800f82079303bd01,0x4578221c10da0845040,0x98404ad024dc120a08d7,0x9a0a2604fe8272013620,0x815e80acb0553829c414,0x2e70170a0b6e05a402c4,0x25830ac18200beb05e18,0xa0696033a819760c9306,0xe1006f0036a01ada0d4,0xdf40ec00749839d01c86,0x441f5c0f8507ab03c701,0x8427020b8102807fd83f,0x8a604474220e10d40857,0xb08f68473c233c11770,0xe12a1093d04950245212,0x26c61338099104bdc259,0x7c27fa13d409d904e08,0xf052b4292014730a2105,0xac9055ac2a8815240a6,0x63a0b09857942b8e15af,0x2c16f40b5e85a2c2cbc1,0xc2fce17ba0bb705d0c2e,0x6320310c18650c130601,0xd2866103294191d0c7d0,0x30d30868b4340819e50c,0x1b700da306c6035a01a9,0x8c61c3c0e0286f1c3718,0x903a041ce40e5c872443],#[0x876943af61d5d0ea3074,0xf3a879543c681e080eee,0x5f0f9807bdc3d9c1e9e0,0xa1fff0ff007edc3f121f,0x41ee20c9104b08190405,0x8d043d421a510b8084dc,0x988b9c4566227c112908,0x11e988e8446e82342118,0x4e7125b8922448a6240c,0x78259912b6094b84a262,0x84c8426311306097344b,0x9cb44dcc26c11349899c,0x2c8a0644faa27a713b60,0xf14750a314514a289414,0x29ad14c38a5985274290,0x5002a5e15170a80c53ae,0x8c565a2b0315638aa8c5,0xb01c57ac2bad15c68ad,0x6830b2f859122c671621,0xe816e18b6505ad22d371,0xe2e9117298b8d85c1c2d,0x5eca2f2f17860bb6c5d6,0x164603c2fdd17e10be54,0x70c42861a030a918440c,0x18eb0c6ac630e315a189,0x29b19358c90c644631ff,0xd2333b19858cbb0658c3,0x683e33e619e08ce6866,0xd3f869a834a31a400d14,0xdc8d6246af4354c1a920,0xe1b2a0d8906bf235dc1a,0x37161b7c0daf86d38367],#[0xfb237b71bc78dd7c6e80,0xd47176387a1c290e06c6,0xe6b4730039501c930e3,0xd540e96074663a0a1cf1,0x4d1d930ec0c75b23ac11,0x23be31de30ee7476e63b,0x795c3c891e308f0f0783,0x6607abe3d3a1e830f364,0xc0f8c07c143de21ee30f,0x1f808fb087d303e791f2,0xfee1fde8fe2c7eac3f2c,0x8040862029100c4801a3,0x883104148208d103b881,0xa38848e421c20f3906d,0xae10d04862e42f821689,0xf220510f708746438021,0x44ea225a1121888b8442,0xb90459822b3114f48a1a,0x88cbc46332309117c08,0x91c8c8df246cc235091a,0x3fc11f288f28477623ad,0xe724591221490b4482d2,0x849a124bf1253c924a48,0x950a4a5e251b9280c93a,0xdc8968e4b1c257a92af0,0xe1304497e44bce25d212,0x2678132c898f84c60261,0xdb426cc135b89a944d1f,0x124e5f2716137fc9bbe4,0x9e9e4f21277413adc9d,0x40d8a01a4fe527d313df,0xb014460a1c4509c28381],#[0x929089477ca34e519628,0x5325297d94b1ca50a524,0x7f253cc29d494d78a678,0x90a97a54992a2b150c8a,0x155b8aa9055212a82153,0xb28958e8abf855ca2ac3,0x242b7b95b34ad3a56652,0xa57e42bcd95dccaea057,0xb1f658ca2c5216184b04,0x824b3b059982cb2164c8,0xe16b64b5445a7c2d2216,0x2dd316de8b6a25b2a2d7,0xc482e1397014b7d05bbb,0x305ced2e6217270b8f05,0xbbb25db62ec517524ba,0x7a5cbcf85e5b2f129780,0xaa17cb8be025ee52f651,0xd301397fbcbf745f952f,0x60db305d18274c0c8604,0x306615b309a9846cc1e8,0xfcc43a620530ed186b8c,0x18c14c59e62a33141188,0x1d618e38c6ce63463197,0x87322a990b4c7f063d03,0x6540328199354c95e64,0xcc1665ea32e31967ccb0,0xab0cd2466703326198a0,0x519d2cce4666f7336d19,0x33fb99f4ccf50678d33b,0x8b434449a18cd066680f,0xae694034939a414d1ac6,0x8d42069df34cf9a5b8d2],#[0xac24d5986a9c35321a8b,0xdc9ae80d6ec6b5d359e1,0xc36379b0fcd8306bf535,0x6d18367d9b368d96e6c8,0xb786da436c91b570da7e,0x4dc806e2537049b790d,0x1bd94de4c6ef0375b9ba,0x8319c0c8dff46fcf37cc,0x6a389c1c408e1a870a03,0xc720f38ed1c6d4e30e71,0xe5e672c039481c9c8e47,0xfb4e778738d39ab9cc9c,0xe9d244e8ec74563a139c,0x3aac9d4d4ea0274e33a5,0x61b3aff1d778eb687580,0x8e76a63b471d9a0ec7e7,0x4eecc77333b869dba8ed,0xe23cf09278193beb1de6,0xb79e538f23278f33c5c9,0x53d231e828f3c079a43c,0x7b233d7a1eb48f5427a7,0x8647bfe3de11ee34f6ac,0xd8f99c7ca83e3d9f140f,0x1f698fafa7d563e921f3,0xf621fa24fcb87e163ee9,0xdf3fd71fe18fe6e7f083,0x80774025a0099000c7f,0x28a8124407b2035d017,0x969044281e640dc205cd,0x220d3d060a82b6414fa0,0x41f420f0d0730837541b,0x4b14249211b90844840d],#[0x58857b42a4a146509c68,0x50cbe86354304217890b,0x1d910e6c870d4365a1a7,0x37220c9101e87d843caa,0x7449aa240911b088a544,0x8a3144faa2715134e896,0x6668b0a456422a6114dc,0xe117a68b9845b522d551,0xa338d19468c544611a2f,0x6ef236d11afa8d53468d,0xc24749239851c568dfb4,0xe8f7d47a6a3c8d1dea8e,0x21269067481c23fb51f6,0x5192252910e487ba430d,0xa247752360918848b024,0x495ba4a2924da923c490,0x38549aca4cad25f092df,0xbe94314a0124f95275e9,0xd2a0a94d74a58a51e528,0x57412b5c958a4aafa54e,0x32259212c6c96054af52,0xb4b78a5b392d5696824b,0x97bd4bc5a5d6d2e7c971,0x13298704c21260792fea,0xb93278991f4c7c2636d3,0xa68b1342099e64cdc265,0xdbba6d3136069ab94d3c,0x884e33a70e138029bb24,0x29d494e8aa7391397e9c,0x3c889e034ee6a76713af,0xc5d3dd29ecc4f4da79ed,0x6a7eed3f289f724fa227],#[0x503aa8149405ea01d4ff,0x1515090283f5418aa08e,0x2ea1ee50e6a864142e8a,0x54600a2c45141a891144,0x90c947e6a3b551b828cd,0x9da9411496aa48a522fa,0x3530ba97814b4ea57552,0xa70c5374a9ad94cfea64,0x4a7d553cf29dc94e58,0xa5520aa8c35439aa1055,0x2a755534aa98554a72a4,0x568aaa7954d4aa395506,0xa55deaadbd5658aafd5,0xaaccb56492b1b95882ac,0x5b2ead7056a12b46159e,0x9795c68adff56ecab6cd,0x72bc015dd4aec05746ab,0x580eabfb15f6eaf8257a,0xff5863ac25960e8b04c,0xdcb1b958ca2c571626eb,0xd6558b266591d2c7fd63,0xcea96710b35c598a2cb8,0x4c2d1b9686cb41259e92,0xa5a9aad3f569dcb4c05a,0xb5d75add2d6856b08b55,0xd42b6735b272d8a96bfe,0x396e6ab7115b7c2db056,0x2df596f58b7855bb7add,0xc602e27570b8b81d5c02,0xb75cc82e5717230b8ec5,0xba515d13ae83d73b8b9,0x7690bb1e5d6faea91750],#[0x3d77e0bbe15dd7aee31,0x9af305793abc625e12af,0x5ed62f6217ac6bd335e7,0xe585f19af8357be2bdd2,0xf8bf405f7dafae97d1eb,0x9805ac0065ff22fe797e,0x4d58216c0d46053301b,0x9b07758372c18b60ad3,0xd615c30a3584c4c22c61,0xc3536195b0c4585eec2d,0x83ac40661f230e8586f4,0x15899cc4a762433112d8,0x316b18ac8c5396295314,0x339b19518c56c60d62fb,0x1f638831b998d8ec6906,0xac79163bcb1d858e76c7,0x90bec83b6401b1f7d8f6,0x46d91dec8cc645232201,0x33267592fec958649b32,0x65213286d93fcc9e864e,0xafa6568b2ab19512ca75,0x76cba465c1b2d59964ec,0x99884cc2a65f8b2f6d97,0x347599f4ccd26659b31d,0x32338419b82cd9d66b63,0xa67a733c719de0cebe67,0xd0386804b3fad9f8ccf8,0x2c4d12c686db4289a0e8,0x25a432d1ed68dc34639a,0xb4c55a5c6d2c36942349,0xa02b4f4da74cd37469aa,0x116a6fb525da8cad42d6],#[0xcd5ed6ad235615aa88d5,0xad94d6aa6b37b5925ac2,0xf69af4cd77b6b9e35bed,0x7b62bdb11ad84d6c0235,0x6ce1b65c5b29ad9176c7,0xaeb6d4e369a5b472da01,0xc2dbfb6de136e61b6a6d,0x5ba40dcea6e5937219b8,0x790dbc0addc76ebab750,0x97b7c01bd92de9d6f3cb,0xe6ffab7f21bf02df5c6f,0xe0df7059381cdc0a8e01,0x35ce18170b0b8499c202,0x3dc4dee2437108b8749c,0x38c5dc5fce2e2715cb8a,0x1eb38ec9c700e36671a1,0x987237b90fdc852e4037,0xce56e7299b93b9c986e4,0xcc82e60f72f5b9729cb3,0xbe1cdb2e6af7346b9991,0x5b9eadcedee7507394b9,0x74263a099d006e7eb73e,0x9017471ba2f1d13ce888,0x76e99474b23a4e5d238e,0x1d49cea32750e3a77dd3,0xace9d60aead875543aa0,0x1abb051d7daebac75b93,0x27662bb281d906ec5b76,0xeda576b2bb4e9da04ece,0xcdeee3b770ebb7c5db94,0x8dde76ef0c776d3ba61d,0x3c0a1e00aefc777cebbd],#[0x875bc2e5e13af080782b,0x778eabc67de2b0f1257,0x4f2d67959bca45e4a4f2,0xe752f38c79b23ccf5e61,0x1ade89cf41b79ffbcf31,0xc3d589ea7af4f57a58bd,0x7b37bd91dec34f5e87ac,0x73e7b84bdb8ded88f6a0,0x1af7da7be03de3deeacf,0x5f124f8697c283e0cdf0,0xe529f26ef90b7c78be2f,0xe7be6ddf332f9817cb43,0xa7d423e94df42cf9f97c,0xfb777d993ec11f59afaa,0x914fc5f7e103ef95f754,0xcdfa82fd167e75bf2b9f,0xbf9c1fc8afe007ee4bf5,0xfb8bfd11fe20fedd7f4c,0x37801240001ff86ffa17,0x300f5805ec025a00d300,0x3ef01d080c3c0552024,0xba20559028f8129c0852,0x1c0e7206dd0333818c40,0x822f410c2081703e381e,0x54c8291413ba09690471,0x81060082e74161a0ae10,0x20db706a48346419a60c,0x1f620f65078383acc1c9,0x57421ca108f082684024,0x584cec259a126708ea84,0xa9d8535c28be13f709d,0x7350b70859342bd215a9],#[0xb218a90c2585fc42f261,0x4358a1a270cea8658431,0x735c38ba1bfb0dd486d6,0x45878b43bc21d810e918,0xd101287f043eba1f090f,0x217d10a5884344162205,0x59a228b1120887ac435a,0x8c477e237f119f88c1c4,0x895144a0e24bd122e890,0x38989ac44cbe261912d3,0xa314358a01c4f8a276f1,0x229d514c88a52451d228,0x56ee2b0115588a97c542,0x48459ca2c7516108af5c,0xc8b7fc5b862d9516ad8b,0x17ae8bc3c5da22e97171,0xf518528c15460162fab,0x6a31e118c88c55c625e3,0xc669a32f319568c9bc64,0xd184683633df19cd8cda,0xf28d6146a7234df1a4f8,0x91b788dabc6ce236291a,0x382f1bed8decc6f0a374,0x2fa39371c7d8e32c70fa,0x1474f63a451d048e6d47,0x8ef9c76f23b4b1d898eb,0xeca8f4cc79be3c991e1e,0xb1f5e8fa1c7c8e3dd91,0x6408920118fee47ece3f,0x84ba421120de9058481e,0x6c87b6438b21a490b3c,0x2914fc8a2e44ad222691],#[0x2351918f48bde45bf22c,0x82723f191e548e9a46f1,0x9649572476922a490a24,0xc95ca4aa12538928d493,0x31f498524bd725bd92d2,0x2a937bc9b224d3d266f9,0x727df93cd49de24eb527,0x5139287394284a0ba502,0x6b25303294d9488ca36a,0xd4a8d6542929e994e74a,0x958a4aba255792a80952,0xbec95dacadea56c92b43,0x9d2ca19637cb10258392,0x25ae52d5296954b42e59,0xb8b65c1b2de996df4b65,0x6a4bad65d392e7797294,0x97ba4bd365e472ef097,0x302c98004bf765f7f2fa,0x1f330c9984e4c1b66097,0xb263e331b098b7cc4aa6,0x4cb62657d328f992ecc8,0x9cf4cdc66677330f9977,0x569a1d4d06a67e733c59,0x734ff9a6a4d2ba68eb34,0x6b51358e9ab44d51e6a5,0x8ea6c4f36069af54d726,0xbcdbbe6d6d36949b33cd,0x9bf14df0a6f3937539b8,0x8d59c57ce21270b33815,0xdb394d9c9a4e45e71ef3,0xe74873a119cea4e63672,0xed4e762b3ad19d4f4e98],#[0x1f4f07277e33bab9dc2c,0xf9e774f30e792f3c709e,0x3dda9ed5cf5a27a993d1,0xd593e9e9f384f90a7c1b,0x7a7e593f159f7acfb567,0x5004a7fe53fb89fc6cfd,0x7f5031e81134068a01d,0xb1a0bf5056682934122a,0x1425ba11bd080e83c541,0x862d42eba168d0a7284f,0xf3a8765438ea1b1d0ce2,0x2511ae8897441da1f550,0xa28dd142e89e744c5a25,0x5d0a2cfd16268abb4545,0x8b469da33a5190e8c0d4,0xe8ecf4735a38951b828d,0x20b28fe947c4a3cc51df,0x16c6e8be1fc0035a431d,0x82e8d83ee23c6070f136,0xe8503c0f7c1b8df0c1b7,0x8ae103904fb13e26c7,0x3fc2e8702f06e87f07e0,0x62f81f8ef081774721e8,0x83b23644c1182861e86f,0x50a370408f448a371c17,0x2744f2282901ec4f040d,0xf058429578704760bc7c,0x9098080aa84408015210,0x9587036082a2a0870014,0x8213824e201f0a104e2,0x61285684897e8235848c,0xf60088834074b1308c91],#[0x34281258d7152889591,0xa103713704323415027d,0x9528a142263209b04d15,0x162370c0eb8711e0ae4a,0xaa94be115122146e6151,0x86e2ac09012657406472,0x6a3a55522060c0056585,0x748a7028bd49830a881b,0x28a84059a2300115a082,0xb8026019054384d19c14,0x8a256a31b048a2b08786,0x8f651219c3e8870852,0x2a014386352499936214,0x80a0e84154ba5638c66e,0x63ac5584a093b12c308b,0x8d31e0938805885d47d4,0x9126289088b119c49151,0x8a2cc485e47f2141719d,0x21123112424d805f8c24,0x5313b0f44a50e12225c,0x5a8504f858683b00c67,0x8d1f2865548ce1962994,0x42b94228c551140464a,0x4dac3200a4800114e0da,0x1c1c0a60a6a116510843,0xa00431006420583224a8,0xa14084b24eb111382290,0x202a929b736b58c56005,0x14658570a8ca42f13322,0xb02aa8261ac0e06624a0,0x43c14c526730a29c87a2,0xc0422244086e36e528a1],#[0x132b88b15aa108b06612,0x8e489e9018560a03332,0xf899d108808cb4318a3,0x98f04265e0fc9a134865,0x283d0310640540a09495,0xa266521393a2fc42850d,0xb1e82c97e09c0a13804a,0x407128e15a5749d9b904,0x5a2ed22848e51c732545,0x8131a5030a3c01b55521,0x82d90700920d0ce0d8b9,0x5656ab494090a378094a,0x3842e4e4002a82e83c85,0x4768ae19341814d56a2d,0x24da1cd594708291d358,0x1bc574265400600729,0x30a142102642c7394869,0x14d6708ca248d18b4922,0x5159016806582cc4a192,0xa1d021c11107586888c1,0xc148a40866acd288340e,0x298105a514d8aea08268,0xea9d60743094300e024c,0x42711d032d199de9110d,0x2e18d1e9e6fe2492d464,0x2511043c74d3a30669f1,0xc5298c1960fe42273d9e,0x88459bb88450ff15c032,0x1f08b6fc8251b08879bb,0x2087e7c1e8c3220879ce,0x3882103454f6ffea8c32,0x405263f21106161b4ff6],#[0xdbd0845b0488115c7c18,0xb2618c488df5c8762393,0x89cf6038244087b7ff50,0xc0c243efacf50469f8a0,0x94bffa4f10330bfd5ca4,0xf27e73c20405346b4c81,0xe1f9e92042a7fbba840c,0xa294a33d88816b3d411,0x800297384b0065bbf939,0x118fe9c19e4021e6fec1,0x2344546bfe0fc19e3001,0x820c34008783e74ad498,0x155339f0f088982a6e7f,0x7310b75c4a703739d939,0xf022517f478010a1aee9,0x7e7412283f811e1050c7,0x5480306a71f8f589111d,0xe0223bfc9c0242e9fb5a,0xe868010ad3eea801893d,0x9c21438bfe2a10850d8f,0x1ee66a4a77dccd847e4c,0x731a7af5cf4399dbfd32,0xb0b303ff82b7cf421f38,0x1e5275ffc00ea4e0e386,0xb87ff85b71c753699ba,0x5173f8c990ecd6ea4e43,0x981fff1c5480e87938f7,0x338731e70e638e169439,0xddd76693cced7fb8e3a9,0x341082bd8d10b182b42c,0x40014fa9e28ab0d53247,0xd8b1d014acff065230be],#[0x3aadff31c62a206a89bf,0x20443bfc41184ae35859,0xb579a04a205fc5b6e889,0x25a62f64c206f299df5b,0xe9c3071c0d118aebce14,0x9f42adc010cbf1121153,0x86846cfa7d388d8381a4,0x87afc73cb5e0005a457f,0xd49c2d284333afc54010,0xf2c04c158431385a5085,0x5694a1b1a63e3e98a12c,0xeefc1c4d1104852a239e,0x88c021f3db4efacb6708,0x58c65ac3f7dcc60f670c,0xe20cc2e5c600d6185d0,0x6b09ef84d29a00870ec1,0x34768cec91da33b27319,0x567f1ec02159f24bd804,0xde71a8d24b41bf73b008,0x7d9056a90c1cfc86cecd,0xd0999e858c2d9fbee63f,0x7466fcf29720b672796b,0x54b2c7c5d29819e67594,0x75789674f848a0cb5fb3,0x17a14190bd0a0c95fe79,0x50500089e7ffe590a143,0x21629f81995dffeecd2e,0x83771724810aee2e490,0x434fc0cc8b72f44b2ff0,0x607edd61d0a6fe581c21,0xe0ead945ac86ce511c06,0x32bc02b413eb25181950],#[0xc41286e3b3852913ff3d,0x408ccf9b6b580cfce4c9,0x63486b7e868b866ca712,0xed4cbd1fb00ca0eacd2,0x32c9fe4f6c02443ca8c8,0xfda2a004e114a8ce3685,0x200a44b63de3b8529bcf,0x78aa7a7d7554614365d7,0x54360df0197effdd401c,0x67676189fe2b412a421e,0x26a2405303abeec02149,0x94e2566fb892043d9fa2,0x648052a58fc9ecc0a402,0xe8aaa30a198fcddad0a1,0x42ecca8ebf6e6d996637,0x1912cfea8693565022,0xb99251104469d23beddd,0x1810d0dafd2550217567,0x80430dcc547c239bfec,0xf2620849bd1151b1f26b,0x22a307c0639c9fc2119d,0x310053d5e24c8014b37a,0x1b1f26b0804359ff6d20,0x233bfc93a13df2095402,0x26680fd39b4033053f84,0x101fa7304a662fca7304,0xb2041a1912fdbb20208d,0xc2062e7c66084ccf2fdb,0x151a1fe8cc010b8b21e2,0x83441bfed9020d0c2bd1,0xd91d190421dde2f94640,0x81333dbf142c81068777],#[0x2e57880b4b0d509fe030,0x22235f670830008d10d4,0xc60132104513f2b005cc,0xcf6448179088ac74fd76,0xdc928679b66851a9ffec,0x10fcfdbd90cea3223be8,0xfc8296110c4e4fc3ab09,0x8e50ca6e64fc24b0b0d6,0x35327f1c4c8199f8fef0,0xedb09100d11c7e627208,0xdbf409b8118e74a2d94f,0x6d0344bfe2858490d0f2,0xcf0fa73411dd0dd97501,0x4489b7a09061a4bc7440,0xc76b541221ff46236041,0xa2449e813b15d10332fd,0x708e88199dc7fca96220,0x65143ff78040863d020,0x2526bf06c72090d18b72,0x3e50c09c10408a43ad90,0x1fc9929622c4244ebfa,0x261d8a4ff07431c22122,0xff519ae68842455aff29,0x4ebfff0bec6884244ebf,0x321ec0c5f517ec688424,0x4a4af219023337f842,0x94086178a2ca410d37ee,0x11dd0a2f1eee84160e19,0x60a10d2e98a727430bc5,0xf067178361c810c2c18b,0x2145e3d80842f2f90d2,0xa481114c0bc810b8f639],#[0x2c0fffb208f8f93b7a35,0xbc1e88ff7fc0ac304053,0x5ff9da23f7c33232af1f,0xc1014ea83c95c1248758,0xcb182fce466d3fe474a1,0xe3ff46c3040533153e40,0x8730cfc43b9b000184a9,0xf77048810feffa54f440,0xd90819e8f90204052ebc,0x46911c7ff1a208ddff72,0xfd10454f87642066dfe8,0x42e933fc6e3081014e3,0x1090f3ff1a208d4f8582,0x40d0afe0412101e9c202,0x4ff400a243869ffc2088,0x33d04835fbcfc0922403,0x84a783fea18d6c014254,0xc1840a24341ff8a0c002,0x38f805233061c291975f,0x11046a7fcd120c021222,0xb048657ed00a4a869ffe,0x2010d3fc25c88d8f7700,0x88ca8ff2604085d6eedc,0xaaa010a5e51c8cadffa2,0xe208f8ffd0601090c0fb,0xa1190beeb420665e3e7a,0xa010c07ecc554014d1ff,0x737fd9880024353c20fa,0x88d8f47e8230deeb3d04,0x2620810cee96e0e18040,0x111adfd5c000121adffc,0x1229f042620810f3fc08],#[0x19ab897ec4665f77f801,0x4c582ff8402183cbd809,0x39032d5fa1d2040531a0,0xf9cc082528f47911629d,0xc08819edcffd641021a6,0xf7571021134f20642fb5,0xbc11935f47a200000488,0xe8a9213cfb80084a54c,0x86d50988cff0f500890d,0x810025425ffa208da3,0xbff0a0082094dc7fdc0a,0xa482004a85f7f8884475,0xe0e082021091077f8138,0x444662fc97821023453,0x21adfc9c82012183f2f,0x7fb3b0082043b0dc9dd4,0xff55684474ff45204665,0xc74d821232bce0408cc3,0x231f7e118f9b840fe48a,0x56c810b0e01d2904367c,0x87c19a3345fade504786,0xf24c2042b9f8016094a5,0x562cda1890e5b7946497,0x3ede712167d8cf6233bf,0xae79002332fee7a0223b,0xbd3980233eb6d62c0686,0x466c7e8c36a806876e,0x965fdd0daa0009115f9a,0x2a458bc0454bfd088002,0xe3125e83120850bfd052,0x7f81347a44c19724c6da,0x21b4289e79206d0a18c3],#[0x9b937f48db30bf87c100,0xf534a690a6479490a421,0x484365fa3c14d214ca7f,0x51239d3f302637ff4009,0x26302a65c1ce5232e0c7,0x9ffe1069018288f3fd21,0x5e6206a553fd409a0a95,0x881aa0afdba9990a5438,0xf6ea66429402bf0c4539,0xb80d4c87a2c66206a62b,0x14d54fdb60297af9191a,0xc28946bfe8e50c20ca01,0x341933373f1e7d5daa04,0x7eb0a4ccf6ca0aa11bc,0x49188f5701a927ec022b,0x1cf602f20c4014e3e788,0xdd3802266dfe8e788492,0xf20040a979f92630010d,0x90e0a9f7def9e21248eb,0x53379f380652347ab6,0x67bbb1b6c052d5fb1930,0x542a060a9a36fafca362,0x6af09a111f8e109a176f,0x8f5fe6444cc6ffc0a275,0x1332bed2284478be6284,0x2f3f24c60021a3d7f991,0xee5c480214fd7d820c15,0xa1e6f892469fb008bf7e,0x3e788924837fe4240430,0x454331ff7920820a9b7e,0x4363f67808a8517f1240,0xfdc40808a8717f124045],#[0x52e1b5db53ecc40d50cf,0xd7f8cd208d0c67fb3085,0xf530f93cf5347f338065,0x2020d4c67eb69561a95e,0x266617f1c4950b27fe4f,0xc5ffc648086143b786b0,0x9a4542cdfc1f909842a9,0x6700cce7bd9842a941e1,0xa1728de0a1b0aa68ffae,0xa846bdd48aa457ffd040,0xd011958394850435b2c0,0x1820ab21c0f7e1107f37,0x9ffbff24241a28837eac,0xa46044ceef67c8508a1b,0x13b02267afd2b22656f0,0xddb48c0899c8eff60ebf,0x84fea8950d4b337c248c,0xd5fa890a130e79cc7ba9,0xfa890d879037942529a4,0x1e109d15ca129e59a4d5,0x8336090d87903794252e,0x9b048905f7930131318f,0xacf8b211e203e098b741,0x6ea3144ea7c23cdea242,0xa12a76f6f7690a95ef4f,0xaa840876b175be9b1840,0xf78c01e0a00a2edfd3b2,0x48be6c2a282029dcef8,0x94ccfd9dba3f2090e7a,0xd7261b04053a5e2d7a44,0x4558ff5a89c0080638de,0x2e090fef8f78c344f801],#[0xd14123820054b2fd5a69,0x2604028bf3fa812908e6,0x97f34ea230347b0721be,0xd81438453f3e907c1121,0x2002a89afce8246a3f46,0x4d7e7412361ff23512d0,0xe8e3b2691953a6bc9233,0x6f1291af839025264b61,0x94a94284a9c88fa2928f,0x20f8c1c24c2a67bf37ab,0x1cea2e307070a86400aa,0x25e1f62930005387f314,0x8b79e14301c9ede00053,0xd0021af4aacf5818acf,0xbc8010b16f9c01949e4d,0xedf573490a23805144fd,0x5383eae6da1d80002261,0x9018254d1ff916980000,0x75f5c40091c6f4e78b26,0x8ac81014eafea75b0028,0x21e64b304f000a6ab8d9,0xa400002a01c5edcc000,0x461e657442029b0ff4aa,0x200021ed8c7fb09a5d24,0x2a7632fc20292c6fffd2,0x81e8e20422c07e4d2e00,0x7dd32026687eaa600021,0xffdb00066c76e0e01428,0x91d93da88050db8c434c,0x37848acfe4824247bc81,0x400994dff20200021b7e,0xcd00a149f9a0002173ff],#[0xa00a1cdffd1002428a6f,0x122e33440025473e49b4,0x580466e7d9d2802860bf,0x8987091f79e0f0023f67,0xf844e77feb0c0283532f,0x8eb0cb0d4c6df0898f36,0x25293e61131b7c226b3c,0xa264a3dbc4a43b955b4a,0xf341524b56da3fd70d00,0x890e2d1d64f00a08703e,0x1b8798010b2f93c9e0d0,0x53ffc2e0c000222f3c12,0xe804ade300065ef19032,0x42d3fc44b6e0e000214f,0x54beb958c4d88ef4ba01,0x5b2be88000862be64000,0x32e1e8221dc8e2000a,0xbff37b10000005505e18,0x6fcd810050d7ef30227c,0x40016231fb573c02054c,0xb7cfe02278fe225e9f0,0x111978f044567fc1005,0x29b3fc500099b67fd,0x43869f9000334df43e00,0xcf1f98010b8edff00000,0xddf240004331e4f20149,0x2235976fcfc4280111c,0xb9c009189bbf1ffe0c00,0x7e7d3c4484e8fb720ccd,0x61292ae101477cfe022,0x70f512126fa0202926f8,0x4cbf991820296f0c2266],#[0x4cd87e3285094adc3646,0xe0046173f8d099fe2800,0xffa26809989fe012cfc1,0x94947e44abd8e9048fd,0x8cc0780d9b2014c87a70,0x91b9ed92a844337acb04,0x2313fe6c0844865f58a0,0x89973112478488be3a41,0x95167dc4b6480a6d878,0x4060090f27fe10240180,0x7c680aa659ef01175f2e,0x4ef2d6e81000a9eae765,0xf8260022257d404000b1,0xc0fe8cc5043536b2e9f9,0x86026743e8225ff32089,0x31c00015389f09133e4d,0xf8899abf8df332e5ff99,0x844d8ff0d270850f5fc6,0xf4048fd7ad7281296fcc,0x9a77e888b03d03ec395a,0x87b1afcc844d5fc6f889,0x9fe4418d106c943c3901,0x207fac00996bf89c0899,0x79f27aa36be22237d023,0x94b2a079fd30177f92af,0x421c0422776aeb214e04,0x983f46d088e7fe20211b,0x9c05bddabac85302dfc3,0x7d5dd14bb4ed6f12a8a2,0x8a65391f1008a28a7235,0xfa8d2c2314e41d33c4ca,0x99c4e5e75ac17a9bef89],#[0xbb991f00e876ff2f8033,0xfee64d7ffb84a03a1b5f,0x49c75219dfc89b9d0c54,0xb90deff0abd095087ebc,0x7fcf4d098e87a7c7fbd0,0x1fe8c4a03a1b4f1fca3d,0xe12a10ed0cbe1f1505a3,0xf6fe205381d0d4fc3c8,0x2800c7430bfaa6e50039,0xa8440d80af7403a999ff,0xbfe2501d0deff0abb084,0xe432ea9d4516444b84a2,0xa8b8c95a3f42e3ff29c2,0x5203f8c95d25f43afd53,0xa21d4d71d68a3b9fa244,0xf12cb1219f5f18a3a91,0xf828cd4ef864a0c34865,0x63051f5fe4b21d0b35e0,0x482fe7ce8424fb639af3,0x5f42c9e6790a493ccf21,0x8737cbc9020a90eef712,0xae31434440beae929054,0xe5f509e62a608ae767c7,0x48454cdf5f02324533a2,0xca32114a67f3060c89ab,0xcceb3ee9bda9604469e,0xa87cf92049434a69c823,0xffae515a514c9b73d865,0x8a961e7fa21381f22256,0x455e82b13c8893b85d04,0x2882c36ba24fe10586d7,0x184ad7f0ea4e2b4538f7],#[0xd0fb7689b26029a9b7f1,0xbf110218a6a7f05c4400,0x892e9d32f84583419f0,0xfc810587d3bcff4de81a,0xa81f2219a52f664d03f4,0x9f22151fda9f00d0dee7,0x74288647e0f80685f73d,0x8523838d80e229a5e2ed,0x8697abe1e442ebf171d8,0x61cc1d0216bb66fe39c8,0x96ed288959c08b2f3f96,0x56844fbb4912b421edc3,0xf69224682295f022a772,0x552c9c91247a1d1672c1,0x4733ffdc708008c20245,0x8f36e742d0871e838f63,0x668279fe45afd512c6cc,0x510e1d189230c58c15a1,0xc521900012ff98e31521,0xff118108a58d2a50cb1f,0xf97a45a4433be4c3a10c,0x9d36c865f53d91142d9a,0x4e604de06aef97b42285,0xcee3ce27ae8d0b4b77f2,0x1a889b6523a69e445e06,0x8767808b668011a08c9b,0xaffe51dd2d4008d045e3,0x1880fc16427798a0fa87,0x168cc9f210bc80de4b42,0x645516c83ea1cb6fae42,0xfe9cd0650fe9a6197d4f,0x76790559e534fcdd845e],#[0x4c74333fc49e0031d0e7,0xc5a7fe204283443fff68,0xfc0063a1d593ffa131d0,0xdf3a94cfc230ea457457,0xc0d5bf974074243c86f7,0xf915073417ffdd9640c1,0x81ff84c1186a01d501c4,0xb7da454167af69150733,0xd62eb5c79a353b12da2b,0x64e2ac161da987f9035b,0x7266c6aae3f8b2cb6ffb,0x1f08b6805e88cfcef6a5,0x8c02173dedde200cb483,0x43dbfca0003008707fc8,0x2da4828114affd424906,0x200cb42fd53a8b2d5da4,0xbedba200018044e7b7de,0xce67c3fee6690704e53f,0x245caac181721c21f152,0x2ce6627fba6d58302922,0x8c77415bab06b08df5f5,0x488068022683c6a41106,0xacba183e2a59ccd2f543,0x232bda0f4ca0ad12f2cb,0x9154ffb2dd2cbe461650,0x88220d30f0961642b759,0x4fcfec88220d2dadbfec,0x12208834ab242c8530c1,0x1b83e77718172193f3f2,0x15b0f9fe3caba20ce2f6,0x7878f26e74373a91b3c7,0xc4c416917fdf1280e862],#[0xd4a9f76d52a0b45279e9,0xf9ccb02cca536dc4d201,0x461d4f2e5012b8c46a44,0x56d0f204283661e8db10,0xddf2fc121259c3fe509,0xff94e11a90f4eaa370b9,0xd9ba89d7f3a35c23d4de,0xbc9d646fb4eb27711064,0xbd3921419bbfb403419b,0xe4118753227f0921259d,0x141a1bd3921419a2fffa,0xa60868af1b32573fe101,0x6cc66fd92e110aeec46c,0x4b2cf4ffea10e01a1cbc,0x42e2147a254433153f8d,0xf9579422118dec9fb263,0x69fd32ce67e7cf441f2,0x4f365d065f1ff1633338,0xe3d8042b61f5fb220883,0x16043e7c6388220d04f,0xb2cc6f8f6010a4ffe832,0x2684a62d300854ffc938,0x4347b1064b78d60d86fa,0xd99a0e3662864f7f1eb3,0x917558c08a59e6f1914d,0x34299834c6a4366eccd0,0x8a38dfa80d874ffc9c0,0x220d0007d5d580d0d27f,0xdffca0008834e7f8c400,0x5bcec685b63e000e4326,0x7ab1a195ed97b2c686b,0x624eff026182203545ad],#[0x6146a8bdaac2146f5214,0x1ea96fff6ec8b399c6e5,0x659cee019f4b227461,0x260e13f3e849660affd9,0xf8b0174488a83022f1e6,0x679ddcc854a1144546bf,0x1559fedc32acd4e7942b,0x6a19e4fec64175804041,0xb423ea423d0ad41df7df,0xbff97590048b228c08bc,0x9aa19ebe80997a530349,0x441a99c3827085fa79c,0x1a2bcbd0a0cac1eed739,0xf390253034a51bfe0822,0x782347dae7208834769,0x283493b24b339021e7f4,0x68d6eda22d75fa9552f4,0xab7c1a0844c8a9f3f74d,0x29178b911a90f1fc5d8c,0xcf4fd362c1a43563ea19,0x7f80465021bb4e5e94c0,0x67cef2c2929f6166840,0x3cd10334774f18e0fd0d,0x6527e2891091b314787,0xac2806882f8831c65e16,0x53ff2712804043ebf803,0x72f8fd88199c9f820642,0x1a21b40f9909f8206421,0x97d003424317f9388080,0x97e04d40cfbaff8a2047,0x51207f9f5daa0b9d2a1b,0xac0029f9468eea83f306],#[0x9be8f4801a1caf4b9d86,0x2241fc4588d07ac443b,0x57a1544bf87255cb0530,0xe7f51ed05138706142f1,0xd4b06725f98ba53592f,0x45e50353006a5ca06a60,0xa1d907f917143eae35b1,0xec29505118c5c5cf9a59,0x11e7a0abdac35343fdc8,0x1ecb1a1e1fee771a9505,0x51347e43cb0d4bcfa2ae,0xc2505116d44ebf1a950,0x391fc8784502a6d7eee0,0x3022975e149184730692,0x769c886b7c9eeb5958ba,0x430bcc6fa1de8287d71f,0x572c0e26289d49ff5c41,0x519ad06ff7e11c320de6,0x5122a3158de6fb19d850,0x77c4523b83f27b61d520,0xb8e102a72bec4845235f,0xb611c34cee0761f4d7f0,0xa1ef17f520f343b01ff6,0xaa7e023534b373fd01a1,0x82a6a3f780d2006a67b8,0x51ffc004152b8f7abc00,0xb04e01a261012dfeb343,0xbfa0700105558fc22f97,0xfdc50400415501158e01,0x1e1c7b8e006a7022f5d1,0x3ce102a4d7fb25c03437,0xa054b6f575d27b806888],#[0x801a9467c10923adea4e,0x89993ffba202267d3a9f,0xd66a149a48dd475fee90,0xe91f114cc7ec3885219e,0x828687ead1ea215cff4e,0x4f526592285373fd0eb8,0x42aab0e63a9f29003b12,0x5c874bf9855bdac02942,0xf8ee10a0687879bdb368,0x6d21b9fe98aa10b90fcf,0x737afe478462895e2f5e,0xa676bfb42101e2b341a1,0xb72c80014f65cec19850,0x486eb8e6f1750510b72b,0xd71cde2ea0a226f9071d,0xbb7f41343cdf20e3a90d,0xb361220601111e620700,0x28008ac7e2029808627f,0xfc140021c94fff708004,0x2a72d3c08461d4d6f2e4,0x3021b6ffa72a8e084060,0x16066e7f1d22139fc510,0x2cfb7f3be09006aaf8c6,0xcff8844268939d108a40,0xe17217dd9dd000864cff,0x132217e42e9c22181f46,0x7c243303f4db42084144,0x7834192df83a142850a4,0xc8bb0a54fde64953741e,0x350a49a249c6a14bcf9b,0x74a290cc9ba51485124e,0x9050144715348b2a3d93],#[0xfe3b123178d98cdf4c75,0x7cc6e3d406c32f85b1a1,0x2ae2c29637988986250,0x6a9d9178ff382506a51b,0x10a28affa6c70411c454,0x7fa90ea3421fbef109c0,0xc6f411a978f063c11a97,0xc003fe60d1644cc2a14f,0x76e20a1610f37dc010a1,0xbece20a1ebcbc2c0caaf,0x5f35200d4b987cc64f3b,0xffe84918394619703347,0x550f7f2a150004029d2,0x7e228e67d343e0a9686a,0x59651da75fc42a0a293b,0x3cf4866fa10e9fbf8199,0x4481ee49e3a83b0cb911,0x12d08a797ed9a2ab6060,0xa4a18ffb12369f73c14,0x9f52d8181153f98fd486,0x10aa37e4ee8d10d2fdf9,0x322910c7fd891b98a08d,0x4ba3441d4e4dec36bedf,0x1e5e114910b67ec22452,0x7800394bce487fc42a0a,0x2b753e825000306a8f3b,0x1a9c8fed16c5ce0060d5,0x253c1da10aff82ecd00c,0x6120fdebb14200c100a9,0x2144bb8b924085566a72,0x703842879332fabd5e41,0xb19af8dd5386a5f7e6f4],#[0xffc1c44cd0b61a38e280,0xee0384286abe81c35217,0x1c35213e9f4838d0dcff,0x44d0fedf10104343f9e2,0x6a5e7ff7010410a1ee57,0x9bcfa0704152e9c0c438,0xc3344d70cd1337f08399,0x10bfb51ad2d8970cd135,0x15411fd4386a497e2710,0x2e25a916ff9e87352704,0xf5ff91071133ac6e4483,0x2e6d651a37d5ce294854,0x9a0a0288036fd49d485a,0x2ed42abcc8c75243e1ca,0x919c0e10a2aef188bc75,0x2c20802041aa49f761e4,0xa760e951b9f0a263b9ff,0xd07dba43b0ecec1fbe50,0x47ce2fd7c0821a1edfb8,0xb90a6e25d386a573e70d,0x4a26be0410d0b7a30e4d,0x338ff94372301f8516c4,0x58cbfe06248d10f08711,0xbfe06248ca3f94007020,0x9997fc0c491bbc80a4ca,0x44cf3e78d491b3ebc388,0x81c684bd1ae4c1ffc451,0x21bda547afc0270a169f,0x9bf0e22650edf871133,0x7e271010b6fdc68377ba,0x2976124dee6a4e082a69,0x642dbfa06f6173f63ddb],#[0xd47e47ca10a5a7a3e59,0x72b8b21ea577fd048085,0x80d095e758e97801d870,0xde0a840344472649cdd,0xf406ec088a685218317c,0xc8aaffc73f922082883b,0xa1246a75eb17285d3fe8,0xe55ea2d1900844c64f9f,0x91b2d12b8b1105a989e0,0xbc402fa4108504617c64,0x40c898494002a2acdfca,0x306240800944ab1effc7,0xafd5142128a68bd0f637,0xa12028da2cece4583a95,0x8ab17045082028a8efa5,0x51b066f23ffb3c210a08,0x38be466434a5e1d081e6,0x2941fffb25a08a4a23dc,0x5d431a280a75bfee4083,0xbfd00e4624104011767e,0xc6727f39b8a263a1ddff,0x222dfdf989662e1236b7,0x7c9c2e430bc2bda4e172,0xc66443a6b24a7aa43fb1,0xc3c811a81a99f67e7588,0xe11a90e8cb627085f14f,0xa72797ee846a44cb564e,0xf14218c029aefb2751e3,0x212250faff61098e8673,0x943a723e0353393eb76,0xddb7799743bbfc7fa88c,0x6ff22e09a902060116ec],#[0x4408043f6bd3d24cd8d1,0x5d2116dc8c201b3df303,0x27a499829b4de38593e6,0x87ce9f54283307f70b0b,0xad3a6c042b26f0ac9834,0xd0a84d6bbb47d3989510,0x40115d7d688230ea6b4d,0x8840c022656727ab4403,0xa607d3640150d6ddf2ee,0xa35d80a86d3ff6d5600a,0x99ffab08200c00802a79,0x61ebe2fc4203008044,0xd9fbae8a5416513a3ed,0xe2872a5b0e4c9e4ac10b,0x8040955fdade80521ba3,0x2d0255127fa033975cb2,0x41236a413b5598df482b,0xd8043b55b23c83834435,0x8d498a444b2319f932a9,0x498a45662811f2f67e23,0x426509aeffff8fc04d8d,0x3e80b002966f5e38bfe3,0x2811d8f9bcefb314088b,0x39bff57c9995f7140406,0xe35f813c67d49661042c,0xca0694be3fc080600a76,0xb533b8091611bada7c2d,0x19f245a94619f338a514,0xce1054015188ba24c5ae,0xfecff6211a004401a1fa,0x525521bfff02111950f4,0x945531add3da1b435993],#[0xcfcf92a52a18effac631,0x7e3e98994d6d9e4aad0c,0x972f7a3792c86a14554e,0x17b79aa542b1fc2c860a,0x7d6c91b2d2cfd7418aa7,0xaa5f65a6097374995131,0x53345bc4648e1736815c,0x1fc6a8646182a7ac1138,0xba1d22a052c5f119237,0x611590782a887f256084,0x14a6c9f5141c2c3fdfd3,0x188f3a90187e7e2dc00,0x68367f40b514284f75a9,0xff24adacc96cb6387d5,0xa9a7a23e2b7faa42844,0xa55bd73aea44bf0a4292,0x1fdf4888548e7f000922,0xc0cd1647eb10194d1ef3,0x14a8cded8e42183e7c73,0xd399f7037b6b7bec4440,0xebe660e65c0114f91ff2,0xf0fe0ea5d3ad99888aa6,0x36de0014959473065020,0xf37075219f9e1316014c,0xdfab9432e7b529e099a2,0x99be3e03257f276cc4ce,0xbb69df1334d57d83344a,0xda89a003054f37f08918,0x7ab1e068b27e0448da7f,0xa09985afa7764cbc9cac,0x8dde3e5fa04a172200af,0xfd4430217ab9f0a3a0f9],#[0xe3a0e3d603209f61d464,0xc60c99fbf8f4a883333f,0xe30cae2ebcd5311abffa,0x91ff40c5e8c105115fc2,0x11c102a682ccea3b33a8,0x188b169d1e8c16154f4f,0x4395fc47040a9457ee7e,0x71a1c088f64ddf2ed20,0x1cf1252533410a726a67,0x8a4280748fb4271847aa,0xd88a4293e645210927d8,0xe349462c9f32290a017,0x658e005b243d1030216,0x687fe102040c0888f016,0xb67d0441443bfdcb1488,0xc085af8e05832f3fc9f,0x86c227f84613033b3f44,0x8f9fe41e34800d18eb,0x1ff840810302277feb16,0x80a969ffa1c40008707e,0x14fafe611050ae78df00,0xcd343033b9fd79401000,0x4213fe5c5cc25001109f,0xa50b99fcae02975fd041,0x18d1bd756e8f8e8f2b80,0xa512a855f1c48943ddf,0x88c7715853526a754db7,0x2fd5f8bc18806802268f,0xab0053511757240c014e,0x968abc40628115f7e0fb,0x9fa2403a42500a807d5f,0xa657103a709c01c58522],#[0xb1c4396a6b82fb1c4396,0xf0c0216b6e8580333927,0xf5fd111420da3b28cda3,0xe94c64c84d5879e888a1,0x31c0b06457a3f4416050,0x541384dfabfc0862811,0x614054d1fb52fe010614,0xbed393520dfe39966010,0x68022d4ffca110000a69,0x90029bdf82efcc2f1f14,0xa2e95e2f00865bfaca1,0x9e81ee3e010fe995217f,0xd0b68bc02115f8bc0210,0x8333fc011c6536b90f56,0xa9bf8222210288998ec2,0x721e3b0bea5f5104054c,0x6b61e952329fcf281028,0x2a652e0b8f0b4ff0547e,0x415309cdf4202a5e28cd,0x13d4abe5d2251f6a6633,0x9a3fc064b3847055fa1,0x88497879365e75118e3b,0xe6f4188fc000398902d6,0x18b835bdb8840508c7e7,0x6887906a19967ee40081,0xff43843009530f5b9e24,0x194089b3f6691502976,0xced003194d8cbffcfec2,0x53fc57fd6106280a7cbd,0xa00632a021bfeb083140,0x5e38acd2334b47def938,0xb9d6092000a7d7694358],#[0xa902a5cbeb2c0014a57f,0x15727f1c4420b5359dcc,0x445e17279076f0440040,0x60002aa1bfeffe940403,0xaf263000529dffe23328,0x91410c554771fdb80198,0xc43f9801005361fe1763,0x18002956a1fcc0080298,0x42363ff108c80432dfce,0xa13fdad2a40294ebfa58,0x4810f2860a4f6805290,0x66810f5b80a528bde2e2,0xe1f9e0e4a543d7f9802d,0xcd00a534087d5d4b528b,0x53eff534409021c4ffd1,0x3126fe617fd1cd00319,0xd085a21249e0c923c070,0xf1cd047054fcfff86ea0,0x864920a9f446b48b57ff,0x10d7aa88a803156e1ff3,0x9bf919c4209054ebcde1,0xaf701ed1e3fb90685267,0xd0fe2616d0ba231148d3,0x6fc762e0299c3e25c14c,0xfe767ad0360055452182,0x82a6cb9933c220e0a9e8,0x31f92554a867bffe0861,0x6000a977ba0a1fac5ca1,0x81094287f3b226778178,0xcccfdc4aa0862aa15fe1,0x7adeb9234636969899f,0x50f27834d82761d41ed1],#[0xa985c927e89b41ac13b1,0x6345e4652d837c1d5de7,0x97ac85ababb641114c4,0x2761212bf2f0c291981e,0xd7ff4648ccaf8f048457,0x40a717f2d637290a0894,0xd48c124a902056e27a45,0xe5a148a814cd7e8ef58b,0x2b4403f1fb3b5536875b,0xfe6d72eb520ac0ff511d,0xf8532d4f8e3fd00a4ad0,0xa5f6a40532d4ca6c6561,0x8e770e1ff1f638d2b43,0x4496a9e3f39a20612991,0xf16ada17a8dfc263c801,0xd4b5294a4f8dc2bc5d62,0x436be7d1695a18cfe81b,0x6aaa16c711210783b15b,0x88d8a29c01bfe1707e38,0x5161785dd8aa58bdb0b5,0xa9d59c9f2e64db889b5,0xb6a154d0f170b8398e20,0x5ec366f9614a313183bb,0xe05e300200a7962fb7a0,0x7b908c303bbb1a50bb7f,0x2145e0f9a6802185f45,0x538bfdc114aa86c7dce4,0x1c46614cffc9f00440c5,0x32992def10e90ca6f7f9,0xa2a512b9b834b7bc43a4,0xc35bdcace78a946596f8,0xa3abcba22dc66144a18c],#[0x82146feec540529dea69,0x9ef064f1e7a86183d71d,0x9d4687fb1d4691ae0c81,0x832634f8269a010e87b7,0xaa4f8afc10f8aa6c975,0xd4c0ac59bf4154655afa,0x6f8b24c344954e2bfa8,0x1b5ff01b010b2f8b5021,0xacf56a0433b2ffc79d82,0x3e100c373ef788014b2a,0x1e0951b3e62790f010e1,0x792d48403153ce70832c,0x3826c30292d2fa64e103,0x270b0f6e26021720bcea,0x2a2087e64c8b1356d767,0xd8718158a6ff6f954140,0xcbc43310b82fde0ca2bf,0xa3d6577d00f22c8829e,0x23be5251f989928e2c2c,0x433de0c907b2051d4f0c,0x920638147bbea3810031,0xc464bfcc010b1f51e9,0x5203feabf3b0437cc977,0x8587c317608583a3a00,0x69e0c592fa064f7bfc54,0xb6171f6eec2a169e4d50,0x179d47f708ea3966e9f8,0xf14032652f1f8e2da462,0x3e72b61ede7515722f3,0xf192c33c205271a32b47,0x6c83930d120b1d875e8b,0xa26a862699340217401],#[0x93b92909eb9498457ffa,0x9667a4a187f392070f08,0x1a2c3772a8d8fe7c0b2a,0xa0be524856267d314da,0xb197dce78b66466db841,0x634a4e548365e951d04b,0x21117e62532c406ae583,0x3d9e455263caa837436d,0x31bbe164195f17c8aa48,0x14a0b02d62a6e431a83e,0x6f4b2a740a583e670e8,0x2b5c9c9e454b0f89d821,0x987f847c345fc6053806,0x647c54627b7e7cde5569,0x52e0b8cb50c42cf2dc4e,0x8e733d0018855dff7420,0x6014c38ded2df6869a9,0x395ff01800c9a9bdf936,0xd81aa61a9fefe7042c6c,0x9c03109ec9376085f7e4,0x4e5789cd638740a795ca,0xf108b0c0f8da59532001,0xf2ea8061fbc49bb042d6,0xa687f52bc4e0864f7831,0xd3090d305074bf2e5b4d,0x4909e0c78f72b8322bb7,0x9a7e35a51ea643cedecd,0xd9ed586e976fe43d3523,0xaf2f080c4bb87b55a4cb,0xc9a9558b0483fe11619,0xa1aca6cba74d2938fe9d,0xd5ea508d4054eb7eacad],#[0x39ea34bfdeaad6015359,0x28717d618211c6e70bef,0x6352c7a031cb9b260e5c,0x99f77c5106589f60cef5,0x2fff469042864e350ac8,0xd5b4226767fe80a8850c,0xf4a14c93cd6ea0fb1538,0x309fbbb5405c5016e855,0x41ba80162abf0e8feeba,0x4e9c338c041e272f3a74,0x65b19c344f0dc512474,0x2dfc678970a81c1a138d,0x98cc64b44a23101f436a,0x8f9667034446ae44a10c,0x5d29bae69bd74ec39bc2,0xfde236f72f38d6fce8c0,0xe75e70e2e665e86d2aa6,0xf6ab180c44714ea042fa,0x632959ab2728b99cae23,0xe1b6e3050302974ff68a,0x288274d3187eabe987a6,0xc393d0f34274260899b6,0xe1665fa18de1b13f3395,0x576e021d322dff596df4,0x652b3b7e0dc6d70c4c3c,0xf697140e9e88b3fc0928,0x7f7ce738581bd7d082ff,0x2979ee11b8423ecc6a39,0x23b599982986a3bd3620,0x31523efa1161e88785b5,0x21e949c349f60850be8a,0x28ff4c8ce1dd61b8b8e2],#[0x54a2d8ee26ab821dcf1d,0x2949da4cb3c29ddd048c,0xb346406da6110feb9b6d,0xdb48a943b954d71a5ee,0x6d3a8c548d9e9c190cfe,0xe08128a978897a0a3153,0x20c62abf9030b62c309f,0x90186f418c2a815c57b9,0x6e8614e9d9000150a7fc,0x1441de200053d1c002a3,0x229880a9904ffa780455,0x58a001972b800533df2,0x27ae0a7782c259f72af6,0xd87b70c9b14a2309acc3,0xdd2052ede30de831854,0xdc504339edf000a4a3ff,0x880c318afa381486d545,0x53c661edc397e788325e,0x7cba00c4f3ed91054761,0xfae0014b974a0290a968,0x905c39050974eab47c09,0x740b0d67bec22bf2e902,0xc3fbe82a305ee816182f,0x667e82a5ae4c51bd218,0x1386f0d8fe6e88914a36,0xc50ba7dafd374448a749,0x7e6a14f196854ec9a657,0x3603eb5bd6587ca05545,0x2a6d5d868843bbdad0a9,0x756df1c154ddcd77df5c,0xa96efaae60152ec07d6d,0x61f8c6c5970b77d57300],#[0x85eb472bba058643f95f,0xc2e1caf38161fae0b0b2,0xfa0c70e691c800548c8d,0xa537df000184ff00a9f8,0x14fe57f850887c2ba665,0xf5fb06a6f385dff06e20,0xff674a86cf1835448c61,0xd4c768767f6c73835435,0x2978756152414b23b480,0x33329f2bc211008960d5,0x428761ca71b0cbfacfd2,0x4b0866460b125f9b3d40,0x8bea9c1054b27cc5a28d,0x633a014ad408beaac2a6,0x40ce028226af4028d0fc,0x7ebcc3559494dafa3076,0xdd36da530b36e9aaf608,0x821b1ee901b698643f95,0xfebcccb10b61a7d66674,0x515ae58561c9fa5151c6,0xd28613c4bd5992a9bef1,0x239aff66804283e2a705,0x1d100c3c7f9c3d8f6502,0xeeadcd4a5f99cc712c4b,0xcb2620153f0f24030c6d,0x43f06a7469014d27febe,0xf280e642c41b1aae2a4,0xd48f66a6af8e0583299d,0x9c3d184e21d2ce2d9def,0x4907f1255a0c94d3b291,0xd20292dffa90665233c9,0x41e0c87972ac531bef8],#[0xa7e08403ea2a9014b6f2,0x521c94bacc2f300218ca,0x47b4f83fa46c53a473cc,0xbde082be2d9a6c8ee6a3,0xe37ede94627870640fd2,0x29e330cc1bf30a2a6854,0x3761745f0e06f326629c,0xdd85d16efce226588174,0x7d8b45db1dde4cec2552,0x815a1ae60318022b0fd0,0x98a36f7fc82a658ca791,0x18ea7151311e7f78b0e4,0x314924df148dae5d962,0xd36b833438411dd0045e,0x99841af78462dfb26610,0xc250b146fb9b7c1696b7,0x803ac6e73110b1a57c61,0x51565888a6bee05f50b1,0xa1e]]
set_option maxRecDepth 16000 in
def g253H8 := limbs80 #[#[0x1132011000000002200,0x200200120110201,0x101001100110,0x11001244000002200000,0x2004103201001021100,0x281110010460000100,0x2021020110300031002,0x30001110002130200210,0x201000007300123004,0x4100210000000040010,0x22401113452502311001,0x20000101002340,0x10100002010300c0204,0x22101000121061000322,0x3000000063303000,0x7030403200000060100,0x3201011006031150003,0x20510401104211300,0x10000100200015,0x4161020e0100000,0x24bc0000,0x0,0x0,0x10123000000000000,0x8b000000000000000000,0x411fa0,0x0,0x469,0xd1000000000000000,0x80000a21cc528821fc00,0x4234039e000000004812,0xc4dad],#[0xd0000000000001024c00,0x16800000000a0f,0x422f00000,0x88000000000000000000,0x80000000125830000526,0x20550000081bf44bf,0x34000000000000000000,0x800480000000082,0x0,0x0,0x6986310720000000000,0xb40000303b40000000,0xf40000100dc0000,0x2d017600000000000000,0x34b0b00c828490000201,0x202c,0x205f40001212d00000,0xa00000000003aca0c500,0x9,0x0,0x0,0x801b800,0x28180000000000000000,0x7646f280000000000005,0x450380001099b04,0x2e0000000000000000,0x1ee0a38a90200004062f,0x78000000000000000060,0x606f800000000824,0x0,0x44be0000000000,0x821900000000000],#[0x0,0x24000000000000000000,0x51064c07400001a4bf40,0xc08540f0800000001025,0x0,0x0,0x106020000000,0x0,0xf000000000000128b60,0xa0000c8d56191800008a,0x1024,0x0,0x8000203780000000000,0x506,0x0,0x0,0x500f8000000,0x0,0x9c000000000000000000,0x100000b8e512f0000040,0x823100000000000018a6,0x806ac96ec0001,0x141e20085800000,0x0,0x35c4cb781020000,0x4aa9868000021390,0xc000000000000351d200,0x83d905ce0000688e30be,0x2a32e00ff000000002,0x30033400000000000000,0x10966807,0x0],#[0x2116c00000,0x822f614d800,0x0,0x0,0x10b735c700,0x0,0x1c8a6140000000000000,0x1e4b9e00000000000020,0x50a6e48,0x0,0x0,0x16818000001c400,0x0,0x41142aa0000000000000,0x5bc00000000000040,0x1a0ab000,0x60a0000000000001265a,0x3e00000000000021417a,0x40a440ef8000010,0x0,0x0,0x90000000000000000000,0x2ca,0xb3f89b4000000001022a,0xc06b014e20,0x0,0x1178490a51ee00000000,0x8,0xf8039527b00000000000,0x202f,0x803b00f500204,0x0],#[0x0,0x0,0x78016000000000344040,0x15c,0xc4400000,0x28104000180f400000,0x600880000000000,0x0,0x0,0x5fe05880,0x100700000000,0x0,0xa50f0,0x483cc000000,0x3000000000200b0000,0xc91f00001,0x0,0x11952a12e000,0x0,0xe8438000000000,0x3ae000000000000000,0x10800000000,0x130000000000000404d8,0x12,0x0,0x4d4000000000,0x0,0x0,0x0,0x20000000000107c00000,0xa6,0x413000000000],#[0x3e800000000872880000,0x30000341b60000c01e48,0x120,0x42ac0000,0x0,0x10048000090ae8000000,0x1a0a700000000,0xc0638,0x1823b00,0x0,0x4a6,0x42e00000000000000,0x80000000000000000000,0x9500868000008728083,0x425874650035700938,0xc01ef0000011b4000000,0x303c,0x0,0x6039c00000000000000,0x0,0x1340000011b800000000,0x379000008,0x2e3b10808000000,0x3137e000000000000,0x4ca8000000000,0x0,0x244c000,0x268a0c70000000000000,0x648819,0x0,0x5307,0x49444b0200000],#[0x0,0x0,0x6735496a18b000000000,0x20,0x28cb21381241580cf000,0x608ac000085d5,0x0,0x10930000000000000000,0x0,0x28000000000000000000,0xc07b626b60112000044,0x0,0xc7e00000000000000000,0x2,0x58fa032500b40000000,0x8000000000805e44df,0x4,0x0,0x0,0x0,0x180fd559a000000,0x21b4081c00000000000,0x2640000,0x53400000,0x0,0xc2000000,0xd7800025406000000000,0x300d8000098,0x222b000000000426a000,0x1c1800000000000001,0x404f40,0x1d300b800000000000],#[0x88250000,0x44048c000011acc00000,0x1057c000000000000086,0x203f8000,0x8bc0000023d000000000,0xc0000000000000100aa1,0xc05,0xa32e800000000a0f4,0xbc000000000000000000,0x6810c02,0x829810a4000081018000,0x6680000000042f66,0x40000000000000000000,0xd1ed0000000000000887,0xc1a000050ae0000042fa,0xa5003a00000000703350,0x406,0x12590000,0x0,0x8875022b80003033200,0x283c,0x0,0x78000000000000000000,0x165,0xd900000000202620000,0xa0f5b421800000,0x306000000a88000000,0xc2110000,0x64800000000014f00000,0x12,0x303e8000,0x890f800000000],#[0x80a20000000000,0x1116981120000000,0x6e000031be800000000,0x42a800009,0x0,0xa6000000000000,0xa3c60000000000000,0x1250a000000,0x0,0x0,0x30bfe0,0x0,0x11bc0000846c00000000,0x25b00004,0x0,0x204ac0000000,0x0,0x0,0xc0ec000,0x0,0x1c1990,0xe0000c30b80002008600,0x40632245,0x0,0xe805900ee0167000000,0x845,0xc903400fc00008053,0xc323e58e709060,0x610c400,0x0,0x0,0x0],#[0x0,0x1042c60c8ca2980ab6,0x20400921d0000414680,0x237880260000000,0x8503,0x0,0x20000000000000000000,0x11b80850321237e3196,0x7b800000000808280003,0x7000000001a013492be0,0x441,0x0,0x0,0x1235c000046358000000,0x0,0x85d300000,0x4e100,0x3022e000,0x414,0x5663000000,0xa5040000000,0x12f00000000002400000,0x4a000000000000000008,0x1a2,0x6b9e920d000000000000,0x63400000000000000003,0x618fc00000000000001,0x0,0x2069800000000,0x618f800000,0x2042a0000d0590000000,0x0],#[0xfa800000000000000000,0x80,0x80776061b11fa000,0x963a0000000000000,0xa203960000d2862b8f40,0x8927a03,0xc4c2624000000000000,0x6496f415000001,0xf00920000403bc000000,0x49200000000285d1425,0x1,0x60000000000000000000,0x213ca0000131,0x13f800000000,0x2042443540,0x1806c00005120100e400,0x4500000000000000000,0xe6800000000000040b48,0x35ce40,0x3426c000,0xc0cd800000000,0xa3c80,0x4100400010a0c8223000,0x4c10400000000c2e6,0x40514000000000,0x272c000000,0xc4b280000000,0x303680000d23180000,0x0,0x308540000000,0x101760000,0x1041b40dec11af04b20],#[0x80001803400000000000,0xac0000000088ee811c,0x2228d08ee000000002,0x0,0x0,0x86a00000000000000000,0x9496800030,0x0,0xb3a00000000,0x0,0x23200000000014c400,0x820000000000000000,0xeb1be700219101c1436,0x38000000002024000028,0xd8d,0x0,0xa0fc00002273000000,0x288000000000000000,0x0,0x0,0x2307c000000,0x530d800000000000,0x6ca00764026c,0xf80001a08ad052ca3e00,0x11880000163c0000404,0x1010000000000000,0x905500000000000000,0x800000000487b4000000,0x10179000000002409,0x24c2a0000000000000,0x0,0x58624a80000000],#[0x0,0x0,0x0,0x10bb8000000000000,0x22c4c5c000000000,0x40000000021937814b00,0x52c20000100ad019,0x924e0000000000000,0x102060000000000,0x106390000000,0x0,0x41124000000000,0x2a8d4000000,0x83be0000127468080000,0x1337e018a0000232b1,0x12858203580000000000,0x924d402,0x0,0xda0000000000003024f0,0xa21a60f51022f00,0x0,0x181f600000,0xa10a000000,0x12b801125260000,0x9655000000000,0x840174c435047a000000,0x200a135c6d261503,0x41218000124230000,0x1d00754003c000000000,0x1804614972047810c222,0x101ae000000000000,0x69170],#[0x0,0x10a48000000000000000,0xdd4cd68000108c9ad0b,0x5900000000000012,0x96ba8000000,0x66f80000051ba2398000,0x14008340000000000006,0xc411aeb314000121a401,0x2982c0000000,0x9000000000000030b9a,0x31,0x0,0xa9360000,0x0,0x10df5000000000000000,0x0,0x0,0x4097c00000000000000,0xd2b8000000000063a000,0x10243,0x0,0x38330000000000000000,0x0,0x5a800030b40000000000,0x64,0x45f0000000000000000,0x0,0x0,0x1200000101570000000,0x0,0x100550,0x18174105a8000100c400],#[0x44c00000000009858000,0x204600000c6fc80002,0x298a400000000000000,0x309a80000000,0x0,0x0,0x54200000004e78000000,0x16840000812ce236846a,0x11d40000000000002,0x144f20086e03f2000000,0xba800d,0x0,0x0,0x1a0c60000000,0x0,0x22298000000000,0x47180000000000,0x2f0c585000000000000,0x402e5,0x684d000000000000000,0x100920812636c0000000,0xc500000000200638113,0x39009f00000943803038,0x6012e000000006982002,0x116a0425822e00006009,0xff8000201d828e851260,0x0,0x8623e944c0000000,0x3f800000000000000000,0x3023b81c986b2800010,0x0,0x81180000],#[0x9d00,0x2005c00,0x60704000,0x19225a04200000,0x2580e0000000000,0x43d0000000000000000,0x62d0000618f10b940000,0x12,0x4a32000000000000000,0x1620860000000000000,0xca00004,0xe2000000000000000,0x8254000000000485a000,0x8220000009266,0x3401200000000000000,0x80002028202370028800,0x44300000000000004056,0x405c800000000c,0xfb80000000000,0x0,0x79800000103000000000,0x60324000081c6148fa3,0x0,0x3080a0000,0x48600026a0,0x40330000000,0x2070,0x0,0xc053800010826000000,0x0,0x80e00000000000000,0xa2440000000000],#[0x3,0x49b80000000000000000,0x98000000001013028ac9,0x8c9a000000000043081,0x14bf8de7000000000000,0x65400000000000000001,0x70,0x0,0x1a200000000000000000,0x26df0000000008,0xe4b8809c100000000000,0x2036,0x0,0x3d30c80000000080ab00,0x1822,0xc072800010002,0x10c8d0000000000,0x3029200000000000,0x2886f815a0000,0x1ea045604f304a000000,0x20000000000000000180,0x121500000000312b,0x6e899920553c4cbe84cc,0x301f0000040e120,0x176800000000000,0x0,0x1886046960000000000,0x80000000081268000000,0x1000000000040fc7477,0x405f00000251d00004,0x0,0x0],#[0x0,0xae1108064b805a800000,0x10304000084e0280,0x473c149c1bc7a4e70000,0xa7000000000000000005,0x7180001419a28,0x0,0x9288021cc,0x266c00000000000000,0x0,0x0,0x201ba0,0x2a2b400,0x0,0xdc000000000000000000,0xd2,0x28e800000000000,0x1c400000000000000000,0x51e800000000000014,0x101f600000000000,0x200464a0400000000,0x0,0x91200,0x128e4000000000000,0x20004000082f5e1180,0xe0000000000000c23400,0x208b7040a0000007,0x812e822c504020000,0x0,0x80000000000000000000,0x56c0001021400000046,0x11258c23f2],#[0x38112000000,0x600a80000000,0x883544b0848a3107a,0xa00a0000000000,0x1570000000000000000,0x0,0x0,0x0,0x996000000001243,0x1460,0x78000000000000000000,0x89040000000000000945,0x0,0x363da0,0x0,0x803600000000,0x203d40001825200000,0x3000000000000181b900,0x807,0x34046,0x0,0x4bc0000000,0x6972000010df70000,0x0,0xa0000000002953145200,0x202b,0x0,0x101000000,0x0,0x5c900000000200cfa008,0x1a,0x250000000],#[0x0,0xb6800000000000000000,0x301200000c0,0x310f2000,0xb5e82020000000000000,0x21,0xc007c000011ac80b5000,0xd45a,0x84000000000000000000,0x628880418000101,0x43a00000070c0528000,0x2a400000000000000001,0x18618000060,0x245000,0x44d8b24d400000000,0x0,0x0,0x333,0x0,0x21000000000,0x203bc217000000000000,0x0,0x8c9c8515000000,0x81e30000000,0x8d20000000000000c003,0x80db0000000000000d,0x12d2b000000000000000,0xca000042b280000000,0x16b0000700d2,0x0,0x0,0x101b1],#[0x0,0x12141c475027cc00,0x0,0x2061400000df200000,0x119fc000000,0x0,0x32360,0x0,0x701b8000000000000000,0x0,0x28019809d0,0x0,0x408700000000,0x0,0x6065400000000000000,0x0,0x0,0x302e60,0x2525e000040f9b196000,0x15b5a000000000000,0x6b4200000000000000,0x82ad000000000000000,0x0,0x140,0x6c000000000000000000,0x6226c000000000000400,0x30d00000000000000000,0x1184000000004,0x0,0x0,0x0,0x204b80000000000],#[0x2131800035aec0000000,0x80fd8000000000000,0xfa0000281b0000000000,0x8,0x0,0x0,0x1a52700,0xc487800000000000,0x430a000000000,0x0,0x0,0x0,0xa8f1601d4000000000,0x20960000000,0x0,0x86c02410084000000000,0x20b018086005ea8,0xa380000000120a4000,0x805280002a3d90191,0x0,0x0,0x1814c02158000,0x10007812dd4990,0x806700000000180fa00,0x0,0x41000000025d16180000,0x184780000000010,0x408e80001022940ee800,0x28e00000000000000000,0x8a005,0x111708098808e00,0x1007f427b00001001],#[0x2f400000000000000000,0x2815d121c0000000029,0xa8a1000,0x512000000000000189f5,0x2a40414a0a,0x0,0x1004940f80133,0x10a40000000000000,0x8419000004b0e00d200,0x608900000000,0x0,0x13b200000000000000,0x0,0x151e600004092,0x0,0x80000000000000000000,0x40cf00003002,0x0,0x203c4a23626ba00,0x6030400004cf2000,0x18470,0x6a000004fc8000000000,0x823942350000211,0x10940000000000000000,0x4f01278000128e520528,0x124b9847100,0x0,0xb880000c075e28c80000,0xc115000036,0x207b0000000000000000,0xd980000000000000000,0x202b80000c],#[0x28ef80000000000,0x4780be000000000000,0x11e000000006a3e6,0x148bc0000000000,0x524b800000000000,0x59b00000000000000000,0xe8458000000014,0x12d147a800,0xa2d000000000c0460000,0x1920554000108cf40142,0x70000000000000000042,0x80cc0000286ac0001817,0x9d200001304c0285482f,0x150d64,0xc8dd000,0x11e000004b0485250000,0x200d200004,0x1746182400,0x3980000000000000000,0x14a2e0000000000001,0x1010a000000,0x0,0x6c000000000,0x20afc0,0x0,0x0,0x19888580000000042f20,0x659000e000000000c0,0x0,0x370,0x301a800000000000000,0xa6e00008087800],#[0x2c600000000,0x0,0x288c4000000,0x14100000000000000000,0x69079,0x342448087000000,0x0,0x103a50453,0x15198000000000008e0,0x109e600000000000,0x0,0x0,0x180ed00,0x0,0x50be000000000,0xc00000000000002c10c0,0x8000011fe01bb0000203,0x4cd0000000000000c0b2,0x3a4000000008,0x101b7000000000000000,0x482dc000,0x6076c,0x70000000000000000000,0x4226a02180000809,0x0,0x125cd04f3a60f492720,0x120fb84012008000,0x0,0x57000000000000000000,0x14,0x0,0x95e00000000000000000],#[0x2445a00000000000031,0xc92d000,0x12c5,0x35c5200000,0x1acf6000040464090200,0x0,0x147e80000,0x0,0xd4000035c8000,0xf30000409054c180000,0x10,0x40000000000000000000,0x5b05aaa8d1d0000202c,0x490343520000d28a6,0x4084d0242000000,0x0,0x0,0x58000000000000000000,0x181330000706,0x96b0000,0x0,0x6000000004331f018800,0x280801344f180001049,0x145bd000000002,0xc11e5447d8a33000000,0x8241000020274280784d,0x98f00000000000010083,0x10,0x300d0000000000000000,0x44ca8000,0x4259c0000049900000,0x0],#[0x0,0x0,0x101c34418800000,0x7c4000000000000000,0x132e,0x809f800000000006f0,0x40000c7282173c000000,0x60ce00000007,0x70220,0x2032089a2c4ec00,0x488000242f40000000,0x410f0000191480000,0x0,0x80000000000000000000,0x17a8033e001900004970,0x942f0950000000006,0x0,0x0,0x15c00000000080f00000,0x34,0x80000000000000000000,0x4009e04c5c1f5511d,0xc08fa06d600bf0c360,0x40636043e00,0x15195000000000000,0x0,0xf2849800000000000000,0x354800000000811,0x2270000000000000,0xc52060343002c0,0x0,0x0],#[0xe1800001322000000000,0xc904800000000000012,0x15988000,0x0,0xdc000000000000610e80,0x350,0x2100000000000000000,0x3416c262f1,0x0,0x44c000000000000,0x211c2e8627dc,0x505680,0x821c000,0x640c09c8000240320000,0x1210200000000000009,0x1c19d00002803000,0x63c4c1a000000000000,0x2189d880700006,0x0,0x4080000000000000,0xc909c01680000,0x0,0x10a0800000000000,0x11e80000000000000000,0x15aa981665,0x0,0x206bc000,0x0,0x0,0x49090000020af000,0x7077a82220000,0x632b8000000000],#[0x1d500000000000,0x9b40000401e8000,0x0,0x70000000000000000000,0xc90600000000100b,0x180820000404881afa,0x0,0x102210000000,0x184505500,0x46042d40590000000000,0xc0000000000440000002,0x805980000029,0x48510,0x0,0x0,0x0,0x12000000005023401860,0x1c4060000405ec5a,0x2e8000,0x1780002a112000015250,0x24158000082,0x26c00000000,0x889004580d4204a40000,0x5c000000000000000020,0x227c8000080afc002498,0x42a80000000000000000,0x0,0x0,0x130f84630000611e8000,0x2,0x10078000000,0x2b881240000000],#[0xf20000252840001007c,0xce000000004a2c800018,0x80000000000190000010,0x90b3009aa51a0000080a,0xc83e00002,0x4489c0001251b00,0x0,0x8df00000098700000,0x121a50000000000,0x80f9000,0x51c86b011fc00000000,0x435000008,0x109d1000000000000000,0x0,0x0,0x0,0x818e000,0x4848508120210,0x1133c0,0x3145a0000c098408cc00,0x0,0x0,0x0,0x0,0x1005400002186c0000,0x28000009860000000000,0xb4,0x24d00000000000000000,0x7300000000000000000c,0x200e3cd,0x0,0xd00c00000],#[0x1865680a180,0x181a7000,0x56830000000000000,0x80ac00000000000000,0x0,0x0,0xa3f8000181a300000,0x62e00,0x800bc518800000000000,0x4006c015c0001,0x0,0x80000000000000000000,0x27180000000148a540f6,0xa800000991c000000005,0xe00bca81a5065e818ca8,0x5c740000d27f00002025,0x810480001,0x38000000000871000000,0x80c,0x2018223700000,0x101fdc6bfc17f400000,0x80000000000000000000,0x4a39,0x611600000000000000,0x280e0000000,0x492f00000000203d2000,0xec0000000000000024c,0x18080c47e424540,0x41085136600009686019,0x291ac000000000000,0x47d47d00000000000000,0xe0000000000001049d10],#[0x301e,0x0,0x1a4ec000000,0x303480000000,0x6062400000000,0x0,0x80000000000000000000,0x111bb00004119,0x0,0x24034886500,0x11b70000421350c16000,0x20300,0x202900,0x0,0x2868000000008236c6be,0x2029000005,0xa00000000000014b9c00,0x20c8,0x204180000000000000,0x38000000000000000000,0x309c4963b844,0x0,0x124200,0x0,0x0,0x8f000000000000044bd0,0xd008de08800000000004,0x304c7045,0x0,0x18cb3ad8f0000000000,0x603f40000a1125495000,0x0],#[0x47000000,0x0,0xa0f2000000000000,0x434c0000000000000,0x7021c0001a200000000,0x2260f03a60000000,0xba00000000000000000,0x45cc08b000000000a,0x201a600004279e96dc00,0x31042000000000000,0x1925600000,0x827fa0070434e000000,0x80f14124000000000000,0x82470000000000000,0x9b7e04a14603800000,0x0,0x4459,0x0,0x800004436e0910514600,0x38e000000000000391a,0x409b80000,0x90000000010005000000,0x245,0xc0d28000000000000,0xa16191190000000000,0x15a08005b00000000000,0x0,0x3c814d401b0000000000,0x30000007200000000040,0x1851,0x0,0xb03c00000c0f3a213c0],#[0x600fb832999a25130ed7,0x48018000000000000,0xc0aca0728516388660,0x0,0x0,0x0,0xa017000000,0x30805c020000,0x20c5a0000,0x0,0xf038a051900000000000,0x89856688407a,0x0,0x10b40000000000,0x909bc2319422e000,0x5800000000000000000,0x22c7b004f0000000021,0x141c3017ec113800,0x60778000000000000,0x2054a02a000000,0x81e400002482f002a00,0x500d80000000,0x83c000001aa000000000,0x34b730061000020,0x3566f4b8c0000000,0x8b300002050800000175,0x2b3d60bcc8,0x488d400,0x131c0000000000000000,0x211040000000000007,0x406740000000000,0x205180000000],#[0xd280800000000,0x0,0xc098400000000c125000,0x2127127a,0x0,0xa2cd00000000000,0x0,0x10030000000000,0x0,0x0,0x1fa001c0000,0x308ce0,0x258b0000200bc00,0x0,0x0,0x0,0x0,0x0,0x0,0x4857c000000000000000,0x4054c02f480c60000,0x5143b091b89680,0x1012812e380000000000,0x0,0x84b6000020190,0xe0000303260000000000,0xc0e,0x0,0x4218a00006057c00000,0x124,0xa40,0x224360f68],#[0x0,0xc411000000000000,0xe409798807818ec1352,0x0,0xa80000000,0x0,0x30000000014c5600000,0x8156412168450000092,0x10510000028578000,0xc232e4838,0x4801d810c0000000000,0x0,0x0,0x2602260000046a000000,0xc0000815800000000143,0x6b41,0x0,0x0,0x686d80000000,0x1213a00000000004a2,0x0,0x80000000000000000000,0x612295c00000000a8cc,0x20f180000000000008,0x4cc0958000000,0x1008000000006c694000,0x3,0x0,0x0,0x0,0x0,0xa00f4000000000000000],#[0x3e7032e20d480b8a02c,0x1a3180cb005b6,0x3c26cc093c000000aa00,0xb5c9000000000000028b,0x1400000000000000000,0x1f109c00000000000030,0xc088e00,0x606b4000000dc4047,0x2cd007e8000000000,0xc0000000048260000000,0x356f502d,0x18170000000000,0x48000000000000000000,0x22360000203a20000d02,0xdf00000000000000000,0x103418,0x1a0a900004891c00,0x1135ca65d00000000,0x0,0xd518800000000000000,0x0,0x3800000000000000000,0x3b1384000088afa29751,0x1,0x101e50000,0x9c0000225f4000112550,0x51,0x2a11,0x20a7200008b0100000,0x8000208f6aa34000000,0x431e8000101bc0000c0d,0x1d4000d0000000000000],#[0x807d0000000018b250,0x809c00000000000,0x416000000000000,0x1800000000000000000,0x31054004c82,0x0,0x4111000020ab2,0xd4000000000000000000,0x547,0x108290000,0x1044000000000,0x0,0x61048000,0x2d05000000000,0x452900,0xc4350000000000000000,0xcb60000292f800010088,0x421b8000214b98,0xc0000000000000000000,0xcb401a,0x4340000000000000,0x10c8900,0x8031c939300a4000,0x0,0x1881d0000015240,0x417f9803e00000000000,0x407f800018029804a,0xda000000000000000000,0xc0d900000000000,0x0,0x34c3e000082cf00000,0x1925e000000],#[0x81320000000000000000,0x410b00000309b8225,0x5467400000,0xc0000000000000000000,0x404e,0x0,0x0,0x0,0x181ce0000000000000,0x80c4000000,0x0,0x333fb4a31256f0000,0xaf000000000000121730,0x21,0x0,0x502380000,0x5033374b120000821c00,0x40350000200240000404,0x0,0x0,0x0,0x1634c403300000000,0x2a800000001a09000000,0x93]]
set_option maxRecDepth 16000 in
def g253D9 := limbs80 #[#[0x48510595214415448510,0x44374485105d52144174,0x595424415250910dd521,0x50910615424417550910,0x4438050910dd54244187,0x54950441425411048550,0x54110589504416154110,0x44176541105c95044165,0xdc950441865411060950,0x54510509514437654110,0x44172545105955144162,0x6195144182545105d951,0x54510dd9514437254510,0x4415454910e195144382,0x59552441645491058952,0x549105d1524417254910,0x44184549106055244176,0xa1d52441875491061952,0x54910dd9524437454910,0x4438754910e195244384,0x60165441755951021d65,0x59510609654418159510,0x4438259510a1d6544187,0x5d172441655c910e1d65,0x5c91061572441755c910,0x441765d510e157244384,0xe0975441865d51060975,0xdc91059772443865d510,0x44182dd5106177244184,0x54540481425012061b75,0x50120595404815250120,0x48154541205495048175],#[0x59150481625412058550,0x541205c5504816554120,0x48181541205d95048174,0xdc550481865412061150,0x54120dd9504837454120,0x4816154520e195048384,0x5c551481655452059151,0x545205d9514817454520,0x48187545206195148184,0xdd9514837454520a1d51,0x54520e19514838454520,0x48165551205915448387,0x6015448176551205d554,0x55120619544818155120,0x4838655120e055448187,0x60165481755952021d65,0x59520611654818159520,0x4838159520a1d6548187,0x595714838759520e1165,0x5c52061571481755c520,0x481765d5205957448385,0x61975481845d52060575,0x5d520e1175483815d520,0x48183dc5205977148386,0x6077448165dd12061771,0xdd5206077548185dd120,0x54174549505915254186,0xdd95254374549505d952,0x58150595605415258150,0x54371581505c96054171,0x595615415258550dc960,0x585505c9615417158550],#[0x54187585506096154180,0xe09615437258550a1d61,0x58950595625438758550,0x54185589506016254174,0xdd162542875895061d62,0x59550609655418159550,0x5438259550e056554380,0x59571541625c55054971,0x5c5505d971541725c550,0x543825c5506197154182,0x5d172541655c950e1971,0x5c95060572541765c950,0x543845c950e057254186,0x60976541815d950e1972,0x5d950e0576543805d950,0x54165dc55058b7154382,0x5977254186dc55060b71,0xdc9506137254181dc950,0x54582dd9506077654186,0xe0165545805955159561,0x5c151585705478159551,0x545765c1515c97054565,0xe0176545805d951e0970,0xdc151e0d76547815d951,0x54582dc1515977054561,0x5c57059580dd95161b70,0x5c16560570595725c165,0x597715c165dc17059582,0xe0970597815c165dc970,0xdc165e0171597715c565,0x59582dc1656077059571,0xe077059772dc165dc770],#[0xdc5656037159782dc165,0xd9ef3be6fc7f8ef1bf80,0xef5dab7d5fa7f3fe7f4f,0x6facfd9eaff5fabed7ba,0xefadefbbf77aeeddbbaf,0xfdfebfb7f2fddfabf37d,0x7ecfb9ef3be6fcbf8fef,0xdbdb776dedad7ba7f3fe,0xbbf37defadefbd777edf,0xff9f71fe3dc777fefedf,0xb575febdd77adf5ae9fc,0x77bef5de7bbf75edfdbb,0xcf37e6bc7f7fefddf7be,0x97f2bdf7bdf3fe7bcef9,0xf73edfdafb1f5fe7fcef,0xff77edfd7fabeffdefbb,0xeffcff7febfcff8feffb,0x81f596508615481bffbf,0x31d3c5d836f57609425c,0x14a1715428475d49c079,0x74298c64cbf09522fae6,0x5d8a6bb8429c2dd0a709,0xb8629ae618a70b7629c2,0xe5104f5762c54594acb,0x4996505458940f565520,0xbc595d44b9250bd5954a,0xb915406ee5881a07937d,0x6a06501b3f7406cf5d01,0x1b3d7606e45941a83940,0x6b8e181ae18606cfdd8,0x82191520820e581a8196,0x20720e48213f72084f5c],#[0x441e419707186541d895,0x7407e25c81f896207e46,0x5d81e639407c5dd01f15,0x78607b16181f177607c5,0xd5c822639607986581ec,0x6395099065c23616508c,0xc5e542715650990e5026,0xe439609aae1826a98609,0xbaa6182f15650b906502,0x2483910a906582eab860,0x9585d82463920964644,0x82863950a45e5c251497,0x10b106483117950a10e4,0x5c2ce3910b10e5c2c839,0x92011de48043d97002ae,0xe5404a78501296140533,0xd950229e1408a585020f,0xde48063d9700c45d4023,0xa586018fe50073392019,0x8f6500a3f9601a9e1806,0x283900c8f6580aa78602,0xe0f65c355d650d0f65c3,0x383f940e29e10385f950,0xe296183913950e44594,0x40a784100fe5838a786,0x61029618411165100f65,0x504483900f0f65840a78,0x7611295d844c16511066,0x5d83791900d8665844a7,0xf950ec4e5c3710970dd7,0xf6484313950e8fe483a5,0x3f970f9be4c3e83900f8],#[0xb4e4c3e1b920fb8e403e,0x8d952060664846a7970f,0x40266011755403076541,0x121f900482660160b980,0x52ae40141f900502e5c,0x8600b9814d55944a0b95,0x71906644640998180e64,0x6054958713be5d84e099,0x98188e648620b9815026,0x65c6619911982e5c5a09,0xf90170ae545c3b921702,0x9e445cab901706e445c1,0xb961725e545c0b94172,0x26605e2995178e6485e,0x3b921f86644681d901a,0xf02654849785200ee488,0x820b981f02a607c08981,0x2502658860994218fe44,0x92099824a5614920b95,0x11b82e58960b942582e6,0x4078a4871c2a21c6ee18,0x761b0265c7819911e076,0x6486afb961b0ae486cf9,0x7931d02a606a35931a8e,0x6e44741f901d0ae54743,0xa7911d2ae407417931d0,0xa5e54749f931d02e4874,0xa1d901e826607629951d,0xea96447aa9901e866447,0x8a4390228ae548809921,0x23026588e0994238fe44,0x8903793230fe448c4390],#[0x22682e58980b94260264,0x90a1a16527685089e0b9,0x762862594a1a19428685,0xe58a079962836618a135,0x394291065ca31575289e,0x2548aa4396292a618a52,0x63952ce2548b361652ae,0xaa618bf15652fcd588be,0x989522e10658beab862f,0x9e2610a78964299ee48b,0xad89542b62618a789762,0x2b36e10ad37742b4d5d0,0x8a979642a62648a98995,0x62a31e18a8c5862a455d,0xd8af61652b98e58a8619,0x862d45594b441972bbf5,0x594c04191302ae18b4a9,0x196302ae18c0a9863045,0xa5d8c4c565311ee48ba4,0x63942c62648b01d96312,0xc5e5cb114972c585d8b0,0x643942d90e44b663952d,0xf1ee48bc419130c5e54b,0xbc1f942f36e48bc43972,0x3757594c81d9431aae5c,0x8cc09973802660dc3d91,0x8378f644de0b9834be5d,0x5ce20b973585e4cd6099,0x90360ae54d83f9136026,0x654da3593368f644da1f,0xd654a25e15101d90390a,0x5615269f954a27655289],#[0xb964a82e6126099849a,0x8265cf61d903db6608ee,0x8f9763a415d4e74d6539,0xa8ae5ce829973a2561ce,0xea97863aa5618eb07943,0x3c82e60ec09983b0ae58,0xf409973e07640f80b97,0x63d02e44f4ab903d0be5,0x512c0b954b82e61160b9,0x984b026612c95854b0be,0x608fe0b964c02e45300b,0x997420764108a8873fb6,0x265d0a957542876410a0,0x2b943f0ae44fcf9763f0,0x8b650fa3d913ebee58fc,0x42b95410be51040a983e,0x12ae410413944107e410,0x49b944126251040b914,0x418a6550697954102e51,0x50ca99043076410c0998,0x468ae55180994430264,0x411c0996480265120439,0x9047826592209914890e,0x651240991490be511e43,0x1655102e45340b964c82,0x64948fd625214e59456,0x17745058591418982501,0xd86594063945031e1141,0xa41915294e5947616551,0xd864542419452aae114,0x55639250d86494363915,0x570f6455d5d655458595],#[0x55e1d9057826615cf965,0x153d8e414e099757ac59,0x59583793560fe45595f9,0x955605e4d581f905609e,0x641602596568f6455a0f,0x3865fafe097a0d955807,0xe595a6a18269a4e1982b,0xb946a82661a6918669b,0x82e49ac0b966aa5595aa,0xc95864f16e4938f9764d,0xe98e413a29964f25e193,0x3b0f924ec5e413a5b924,0x59d85956629944f8ae51,0x56e9b845b8e6496ec585,0x58826616e25965bbe59,0x496a5b925a13e5163639,0x925b09e596a2f945a8ee,0xe1990b38663096596c39,0xb966c25595b00b946c24,0x2e59b295656c82e45b20,0xb946d02e45b42b946b8,0x31e0974c5825d1864574,0x257935c18e417061925d,0x80365178c7905e18e417,0xa041916807649a01d916,0x688de4d9c43906710649,0x5a42f946790e419e0992,0x16e02e49b60994690264,0x19c35d657082e51b80b9,0x86720de4dc8b386712de,0xe51d83f927529609d493,0xb927682e59d895657602],#[0x7e45bd5f906ed7641ba0,0x19907434e0dd05d90701,0x27e0dcc3f917334e45d2,0x99273a7e0dce379373,0x4cae45d32b83740f641d,0xde0b927727e41d29d907,0x7e90641fa37937d0de4d,0xdf641907f05e4df6a581,0x17e27e4df60b927d8de4,0x901a0b928082e51f80b9,0x4208726181bc98406f25,0x6081dc162077260821c9,0x77607515d81d99650770,0x26581ceb86073a6181d4,0x997407e65901e8998072,0xe65d81f999407e66101f,0x3999707e66581f998607,0x8db59023c18208f26442,0x228b9408d1dd02345740,0x8d165c236d8608e6654,0x268b9808a2660234697,0x609d1e5027458409a2e5,0x102b45860bd16102f458,0x760ae65942a8b940aba6,0xe582ae9860ad1dd82b45,0x7920a22e482999920922,0x1e5c2c8b920b72e442d4,0xa964003ae482ce9920b5,0x50dd8014176006559401,0x141970021e5800859600,0x1d06140941650250a5c0,0x33bd620cd0e500687940],#[0xcd0dd83341760ce5594,0x3485960cb9e1832e586,0x40d50dd03541740d5a59,0x5c3541970d21e5034e78,0x840e39a6034e5980d50a,0x6104143940e21e5038e7,0x5761121e503d41861050,0xe483a87920ee564836e,0xe9650639e483e87920fd,0x695900dbd91033a5d418,0xd3b76034e5d80d8d6503,0x31fe580c7d9603376180,0xf197503cea5c0d39970,0x391e5c0e459703b2614,0x8164796042b618102198,0x104bae4012459605ab61,0x5c12ad970488e5812e59,0x7415e555057bd6215aba,0xe5056e58415d0dd05741,0x37615d05d857956515a1,0x35504a879615b9618574,0xdf8412cedd04b397412e,0x63550513a8712ce61c4a,0x91b7612465d8487f9414,0x24661c48cb8612326184,0x52ad8713595944d1a871,0x14abe1852ad8614c6594,0x46047981491660524796,0x6182be1860ad86184659,0x1c588b90161166060459,0x76193259464ae87162b6,0x6404e2196192bdd864ad],#[0x5761399e504f959113e6,0x625c4f1a8713c661c4f6,0x1b9713c6a5c4f199713c,0x91e605445981511e5055,0xaad87169166062459418,0x6b96445a479716aba1c5,0x5aad9716ab25c5a23941,0x170865066af9716aba5c,0x85d1b951711e505d3b92,0x417abe505c23941711e5,0xd48421941a116585e459,0x852111e50802195212b5,0x65484ad65211165484ad,0xd95252b59494479420ab,0x1e5093419124d164092a,0xad9625ab65096ad98249,0xa1e4870e5821c3a6086e,0x2ad871cab21c7319751c,0xb0865078af871caba1c7,0x7445921ac6e486c67921,0x1eabe487423921d11e48,0x8ead921e886487a4592,0x422886588ead76238865,0x188e45942391e508aaf8,0x9623ab6508e459623ab6,0x5889fc9612791e488cad,0x99627d15d89f996527f0,0x658a1c1912822e589e8,0x459728f0648a28b9128f,0xf25c4ab45962951644a5,0xb45742ae6550abc9812a,0xaa2e50aaeb842ad1dd0a],#[0xaa89982aa2e5caa89972,0x2ce6594b3c1622ca2e60,0x8b2eb862cba618b34576,0x42e70588b945862fa2e5,0x10b947742e515d0b9995,0x762e66594b88b942e3a6,0xe58b8e9862e51dd8b945,0x9912a70660adc1842b22,0x2e44af99962a66618a99,0x99952beb610afc1922ba,0xba660af45972bdb618af,0x48b982bbaa60ae89982b,0xee6594bb45863051618b,0xb199912c3a618bb45762,0x2c66e50b199942c66e44,0x4b68b912de6e5cb19997,0x42dd1650b747912dd164,0x50bdc3922f22e44bd479,0x912f22e5cbd47972f22e,0xe50bce9942f3ae44bce9,0x37432505d0c8eb972f3a,0x9e1cc8e5873239e10c94,0xe58633d05d8cf956533b,0xd9594ca879633b9e18ce,0x11965341165ccb017632,0x746594dcaf86342b618d,0xe04596372be18dcad863,0x3308658e0ad763832594,0xccd65763365e44cd9990,0x7334665ccccb87333261,0x60d2af8734ab61cd31a9,0x983491e50d3419134886],#[0xe4cd6879135aba60d2ad,0x39435b5e4cd6e791359c,0x865ce221943888e5cd62,0x2396363ae40d84794360,0x9165d0f19754388658e4,0x24796442be1910239843,0xbba604ee21964522e411,0xef45763be6594efad643,0x3dab61cf119753c3a618,0x8f6ad763db2594f6cd64,0x43a66640e92587398865,0x5ce919973a4661ce97f9,0x963ac6618eb19913ac6e,0x654ed25943b11e44ed19,0x5983b2b660ed01863b46,0xae50f247983b2ba60ec4,0xe9903c91e5cf2ad873c9,0xab65cf2cf943c88e44f2,0x4ad913d08644f8af973c,0x591e4517459045ab658f,0x2c47914b516412cad984,0x4c2b64530ad984b49e51,0x8feeb813fba604fead96,0x43fba610ffc3923ff060,0x4d0199753fa2e50feeb8,0x87402b61d011975401ce,0x61d091975422264108ae,0x990421165d08ae87422b,0x865d08ad97420865108e,0xad8740c65d502ae97420,0xa26410a479740abe1d02,0xa459742ab61d0b197542],#[0xf2b65d0a219142ba6410,0xfd19913f46e1cfc67913,0x4146e50fd19943f46e44,0x104af87411ae51048b90,0x44149e510524944151e4,0x4504eb904146e5504479,0x91412b64504cf944108e,0x66106af94412b65104af,0x99043116510c89904311,0x2e411aad9443086450ce,0x8b90478865920ad76482,0x88645244797479ae511e,0xaaf8446ab6111b479046,0x6ab6191b1b954691e511,0x20ad864811e591aaf864,0x489164522ad864711659,0x922ad91489165922ad86,0x44791e451f479047ab65,0x551e479447c9e511f249,0x914d2b6452445914946e,0x5c9456d62516654944ad,0x5825222e4944eb825151,0x66114199745066645414,0x8b9151e6661419994506,0x22e5146eb8451d15d146,0x195525422e4955995255,0x321e4950e78254505c95,0x4cc9875332e114d1b745,0x54ab61d53656554b2e1d,0x5564594572be115caf87,0x2538865d5e219457d959,0x4559658753d9e494f659],#[0x905611e495873935621e,0xe4d5823925639e4558eb,0x19258116495acb955635,0x9e517acb845ec65d17a2,0x65965eb2e197b19765e9,0x595957d39725f19e597a,0x47975f1165d7d01765f,0x46595804794602be118,0x848b906111e5980af866,0x62325958821946219e55,0x58267925f8865988ad76,0x161a2e4186479260d0e4,0x498a6795619ce4d86879,0x9469ab611a7016469886,0x649a8ad966aab661a647,0xd744de664136ad926b46,0x965d3719974dd95d9377,0x19764e19e5d371a974d9,0xe6e413b19864f3261939,0xa67944ee3e493a67914e,0xec66513b1b914ec66453,0x67c17259a2e45671b944,0x59a2e5166e98459d1dd1,0xd6501765959595656d76,0x55b916456eaf87592b61,0x4563659158916616f198,0x8758d9e5163659458d9e,0xe51698f925a66e416965,0xb945aa2e416b65765a19,0xee496a47915ad1e416a6,0x47945ac9e516b24945ac,0x916516c45915b40e596a],#[0x6c9656599e55928b9064,0x6465958e219665ab5d99,0x98ad7666325959821916,0x6419e518d9b906308659,0x1913b926411e45914790,0x4651fe49948b906511e5,0x45b221916699e55946b9,0x916bc6645aead966cab6,0x645b51b946bc6651af1b,0xf946d2b651b4af916d2b,0x5e057199925d6660974a,0x67925c32e0970c9825c6,0xb2e0976c9825de0e4d70,0x267915ce6e417265925d,0xcb2e1172c9845ce3e097,0x78cb845e196457867945,0x5e32e4578c9915e19651,0x9a089916832e5178c994,0x26822649a0eb82683a60,0x559c73936722e419ce99,0x9467a2e419e21926899e,0x645a4eb906919e559e6b,0x7826851609a021946908,0xe059d47906751649a14,0x4792672be099cad82675,0xab609a31b95674be4d9c,0xead926891649a2af8268,0x7cee099e479167d1e419,0x9f249467abe119ead846,0x6946e559e479467c9e51,0x1a4af846911645a54790,0x4692be45a4ad91691165],#[0x9c2ad916e2be51a4ad9,0x9472abe11c6879270b9e,0x659caad7672b2595ca21,0xd96762b651d847927208,0x5e05bcad9276c6649d6a,0xcb826f32609bd97916f6,0xe5641c065926f99e49bc,0xce5907421641d0219273,0x391649ce4792732be09c,0xe7457279d0641d0ad927,0x779ce4ddf437177a2649,0xdde479277abe09df4381,0x37891649e8af827a4be4,0x49ecad727b19e55e2739,0x847851e41e08b9078086,0x651eaaf847a91645eaaf,0x1947b99e55e46b947911,0x1649faad827eab609f42,0xad827d88e51f8ad847f1,0x2b611f845927fab609fe,0x8ad917e11e51f8af847e,0x2be51f8ad947e2be45f,0x285907c08649f245948,0x80abe0a02ad828088e4a,0xa04af9280ab64a024792,0x408f46181dd176071164,0xd82bd19808f465023d18,0x920b746482dd1960af45,0x65035cd860cf35d833d3,0x19003f16580dc5760373,0x75d40fc59203f36440fd,0x49760452e5c0f489703e],#[0x675d849c58412a3e5811,0x19d9513716484d9d8612,0x3bb618599d6516526186,0x928f9416a3e50559d941,0x1cf4e486fd1921bd2650,0x4a3d19627a3e5072ed84,0x42af4610abd39128f464,0x18b3d1982af465cabd19,0x843274e44bdd1962cf46,0x658cfcd8633f361cc9cd,0xd65356c610cbd19032f3,0x7650cc8f96353b618d59,0x9d97336761ccd9f94336,0xa3660d3498734e7e5ccd,0x7b79335f3e44d68f9834,0x623e5cd6ed8735a3e50d,0xfcd9143f46410e8f963,0x43bb2610f499743e7615,0x9134996445261910ef98,0x13a67644e88f9644bb61,0x4ffd1813fa3e44f39f9,0x934073e0501d3913ff4e,0x65109d19042675d501b7,0xf9140a365d099d754223,0x36450c8f9141236450a8,0x9d7453745c9548f9147a,0xd25d1539d8753676114d,0xa8f925623e51568f9454,0x323e456b9f915a67e453,0x954b916467e458d9d916,0x5de7609779d825c23e45,0x9a2ed8268e7e45739d92],#[0x1693b649a28d9268bbe0,0x49bd9d926f67609bcef9,0x727a3be09df497277e7e,0x5c9ec8d927a3be09e949,0xf917ba3649ecef827b52,0xb64a028f9280bb60a02e,0x36000dc0000ef9280b,0x17f00a90047c01c000a6,0x8e022400f80073c03440,0x805d402c70149009c004,0xf240760037b01a400c7,0x630125408d0043001fe0,0x702cb015640a4e04f502,0x66d0326018600be805b,0xe4006f9036e01ae00d28,0x780fd407ad03c381d2c0,0x2370115208850423020,0x4e00267812ea09380485,0xb5054202978145c0a040,0x80b69059882c1415b40a,0x182a0be305e182ea8170,0x34419580c890628830b0,0x835a81a6a0d19067703,0x70e837e81bb60db906c,0xed7075d83a481cda0e46,0x1c0f6107a183c8c1e000,0xc208c100a07ef83f081f,0x43e021c210c10853841b,0xdb8466422e0114c08878,0x9091d8483823e411cf08,0x12fd096204a982510125,0x770139409b304d382668],#[0x4c28a8142909fb84f502,0x54c82a0a14ec0a5b052,0xb06857b82b7e159e0aaf,0xb6505aac2cf016410,0x6178b0baf85d142e4817,0x30a818330bfd85f3c2f6,0x4bc322018db0c53061d4,0x886744335c19750caa86,0xd4f869d834621a110cf,0xb730d9b86c7035ec1ace,0x781c150df406f1437341,0x439ac1cb70e460719c38,0x75743a7c1d250e85073c,0xfd877643b7a1d960ebf0,0x80f41079a43c881e220e,0x1f330f8d07b783d601e9,0xfc41fb90fc907de83eba,0x7440f420531018080203,0x88518426a2114106a082,0x10f087a84394219a10b7,0xf4116208a2c44da22411,0xa23a011bb08d2c463c22,0x48d8243c121008f98479,0x4b049fe24e2125a89228,0xb096544af4256112a289,0x132f098b44c0025d612d,0x720137489b184d5a2685,0xe027bf13d089df44ea42,0x5122286914258a0884f,0xa5a85252290a146a0a2d,0x200a89453ee29d414cd8,0x115680aa6854f82a6215],#[0x2bc315c78ad68565a2af,0x9602c86162f8b09857e2,0x45ade2d4216838b3805,0x8b8445bc02dba16d40b6,0x7650ba945d0a2e611720,0xb117c78bd705e5c2ef81,0x8305218098bfe45f962f,0x61f830d7185e8c27860e,0x72c633a317d18ac0c48c,0xf0c9606470321a18f18c,0x19998cc2465da32c7193,0x40e19e70ceb4670e3370,0x48348b1a388d150685a3,0x86a4235001a730d30069,0xd74c6b7035981abb0d52,0x308d9086c48360a1af90,0x41b940dbcc6d6c367e1b,0x38131bf10dee86f0a375,0x1ac38a51c3e0e110704a,0x3c72de394b1c910e3f07,0xe87073f839e31cda8e6,0xd7c8eb4075603a821d26,0xee1de48ee7c76e03b3f1,0x23ca91e410f11078263b,0x7ace3d421e920f40079b,0x87c7c0c3de01edd8f650,0xa0fae47d103e6e1f248f,0x1fb68fd547e503eff1f6,0x1e20008ff6c7f6e3f98,0xd440bb2043901a080884,0x88328417a20aa104a881,0x970846c421020f6106b],#[0xa310c7c85e842c621481,0xe21f890f308758437321,0x44fb225e112208890440,0xbe845c322ce1158c8a66,0x5c8d6e468d2329918788,0x11e188ed0473d238711b,0x427120948fec47d523d1,0x132475922e8912848712,0xc49ac24c512594926649,0x949c4a2424ff127a8939,0xc8495e64ac72552929c4,0x92fbc97784b8325a712,0x265d1328098d84c38260,0xdaf26c2135309a304ced,0x124e58271f138689bc84,0x9e324ef2276b93ad49d,0x3f649f584f7627ac93d0,0x57941bca094501927f81,0x928b4144a0a20c50ca28,0x52432907147c8a38851a,0x61c52ef295594a34a4c8,0x74a774538929b014ccca,0x1520ca8b6541d29fa14f,0xaaf154e0aa0254e02a5a,0x2a2af71573cab5855852,0xc56f52b6295a2cacc456,0xafe657c32bc395d6cae4,0x3f0b176587e2c1f96054,0x16700b2f8595a2c9496,0x2d46969b4b4685a032cf,0xb552d9316bf0b5985aad,0xd65c232df996ed4b6fa5],#[0xba425cf92e6e172c0b8,0x78dcbbbe5db72ec79759,0x9897bd8bd825e932f2f1,0xe300517f5cbf4c5f742f,0x6108306f982a0c0e4603,0x3e461c830c898578c266,0x64c55c6276312518894c,0x18e0cc6b46338318498b,0x24c1917cc85a63e531d8,0x7832a79947cc9de64c13,0xe661c32f819724cb4c65,0xce0a66c93357199f4cc9,0xfe0cf82678e33b299cdc,0x1a274d0d26837340d99,0x34ea1a614d2a86915347,0xad8354e9a9a8d46e6a0e,0x726b8435ac9acc0d6026,0x4d8fc6c4336039afa0d7,0xb554da646d0b36729b2a,0x1c1b7fcdb946d9936bd1,0xb377e1bb48dd2c6e7737,0x6fe937dd1be08dec66f3,0x1b270a8383e1c150e044,0x8e3a671a338ae1c4bce,0x1ca30e4d4724739131c8,0x9c99cd78e65272f83961,0x913a331d0d4e7fe73cd3,0x75693a971d41ce98874,0xecbe763f3b049d760eb4,0xdb4ee7e77133b6a1da8c,0xa9e0f8f01677d63bcb9d,0x3c881e3a8f17c78a33c3],#[0x9fc3ce71e67cf2f27943,0x47ac23d491e98cf4567,0xf75c7b7f3da81eca0f6,0xf298f8de7c433e079ef8,0xd71f5ccfa587cfa3e6b9,0x53f301f88cfbe87dd93e,0x7f643f951fba4fd787e9,0x8c801f3fff1ff3cff3a,0x1d01dc80c3404c201d10,0xa069502e481524095a04,0x13aa091d045681f740e0,0x534191a0bd90580829f4,0x283fe41e8a0ea1070e83,0x9ee84c542472116d084,0x8050bb685a442bd21509,0x121acd0cfa8647430e21,0x43bea1d910e5c86fb437,0x84a441921ffd0fa8879b,0xde88d1445aa224510d08,0x91342896b449fa242111,0x2a2d14c48a384504a274,0xa922cc516168ae6455ca,0x446122300517988b8d45,0x8cf946682325118de8c5,0xc308dd146ca2356d1a5a,0x411da28eb247402397d1,0xa3ec11f068f58479a23c,0x857a41d120a4900d47eb,0xa448bca4549222290dd4,0xc925e4912a47dd239e91,0x26889312496e24ac1250,0x7d27d893b649c8a4da1],#[0xc253952972947c4a2225,0x4ae3256652ae4953d4a8,0x6b54b44a59552c669609,0x975a4b99a5c4d2dd89,0x5306498024bec25ecd2f,0x6541324098e54c56a61b,0x3c268fd341699cf4cc42,0x84daa26c7d35ee9abc4d,0x9c4a4e0fa6f9d375c9b8,0xa929d174e76a72b938fc,0x613c3a9dea4edba76093,0xa7c693dde9ebe4f41279,0x2ba808d3fcc9fa44fae,0x8250aba849941b2a0975,0x4a2315106a878d4366a1,0x466ea3125168a8a3144c,0xfd4812a3cf51d5a8dad,0xc2942d49bea4a35238a9,0x5304a97394b40a56a529,0x6fd537029a914cd4a632,0xb2a7b653c5a9db14e72a,0x95130a865541c2a0294f,0xa6155292a9155473aa2d,0x512a9755468aa0f54e42,0x355b32ad1d562aaacc55,0xac465607aaf69576cab8,0xa2aacf256692b26958da,0x815c38addc56c9ab5655,0xabcad5db0aeba5747ab9,0x822ac0495fbeafb057b8,0x3d5888ac3816136b0795,0x4b20058df2c67162e2b1],#[0x664eb2f85965aca0964a,0x1256824b3d559d62cdbd,0x42d44569ccb4ab5a3bad,0x5b0c2d76d6b30b55c5a9,0x7125b77adac56d00b659,0xe8b7d15bd6addb96e88b,0xd7146b86c5c1fae0616f,0xe5dd72a8b9395c87ae36,0x3aae9317414b9da5cd8a,0x75d8eaebe975aebaa95d,0xbbf65ddaaee5176e2bb4,0x968bc855e2d2f0b9782e,0xdd7a78bd095e772f3517,0x2f89d7c02bdd95ecaaf5,0xf812faf17cfebe605f25,0xf5fe8afe997ee2bf4f5,0xac0f6605db02198092c0,0x83d2c1b960c0b0549823,0xbfd8592c296612530829,0x2b0f29873ec365619b30,0x626cb128988f8c442620,0x60262e1316198aa2c514,0xbcc6b96345b19658c5cc,0x58f32c77363a031c318d,0x21e5908cc81f63f8b1f2,0xc3325159248c8ea645ab,0xe6533b28d993f4c9c164,0xcb70659fb2c19958eca8,0x8a2cc1465f432ee19728,0xd9a42cce4665c332119,0x338199bbecdb366bab35,0x75db3a919cfece61671f],#[0xb567c4b3d419e18ceee6,0xed06b6821340899fd6cf,0xa2f6d14b688ab4385a14,0x9fda482d20c68f1b46b5,0x5b4d05a612d2e4695fb4,0x6a1734ff5a78ad3a369b,0x5366a8135341a93ed467,0xf6d64b6afab56d9aae2d,0xdae56d7126b7335aa1ac,0x60e9b002d7db6bd4b5d9,0x93b6419b1c8d8ab6c39b,0x76cdb36681b2f2d9536c,0xda926d2eb68d9b3fad9e,0x7b2db926daab6c4db5c4,0xcdb982dc916e29b7059b,0xb7689baf2dd556e97b73,0xf47379bdbc58ddfe6ee5,0x4e6f8b37bf9bda0deb06,0x4e00f6ff3b7eadbf04df,0xc232e0dc7054b81adc07,0x975c41ee1c070c738579,0x3b8cf1c5dce2cd715238,0x721038ffdc79ae39c71b,0x50e727839311c908e454,0xce5ca72c7b9599ca82e,0xdcd48e66f732339885cc,0x9e09ce9ce72b738539b5,0x333a105d022e7d973d13,0x7485ba3b1d178e89d74,0xea0474e53a659d2b4e93,0x588ea9d75413a961d44e,0x7dd6faeb5b7598babddd],#[0xbb095d7f2ebdf75dfbae,0x68bbb379d956ec8d762d,0xeb76e03b671dae0ed427,0xeeeb5773bbb939dc18ed,0xdf84ef8b77acbbc95ddd,0x2a5e102f0567810bbfbd,0x3c5f1e27ef0fa78643c,0x7950bc985e440f1ed78e,0x3aa79c2bcd61e61af2d7,0xcf4ac7a353d0a1e7cef,0x5ec70f5f37ac9bd4f1ea,0xdca1ede2f6c07b4a3d96,0x193e04defc4f7b97bb53,0xf7c783e339f136f86c7c,0xf9cd7ccabe5d5f284f90,0x5c4faba7d3dbe931f41e,0x2df742fb667d9d3ec39f,0x3f281f8dcfc3d7dfebef,0xec8bf569fa48fcfd7e68,0x8c7f29bf891fbeefdc77,0x8ff6a7f993fbddfd84fe,0x8d001f7ff8bff01ff2,0x4ce021b00da805a401fa,0xbc078e0361018980b740,0x8171c0ad604ed0241810,0x3e981d940e02068f0319,0xcb04ac8245c116208390,0xa0b69057f82a74146609,0x1ae60d0d06568313417b,0xd8c1e320eb9072783794,0x8842c420ae100107e383,0x956848ac23821177088],#[0x4df0a4585014272a1327,0xda16790aff8569c2a9a1,0x4310a18330bdf85d742d,0x69343406199d0c938633,0x2786f1436ca1aff0d5b8,0xb0ef8876343a461cb70e,0x1fcf0fb887c6c3d7a1e5,0x2d6210b105c8818c402a,0x5445ce2289111a887944,0x8925c489a23fb11d688d,0x31b8973c4ada25371272,0x5f13fa89db44df626ab1,0x22a1714df8a54c519628,0x588e2bd515b08ab9454e,0x8ce258da2f0fe27001ac,0x83e1f8e0b87107e8d613,0x8f627040f21e10684e17,0xf87851c284f6386de16,0x8a1cc3704226e3877e36,0x45a2236118a3a042607d,0x83438521785d8411e840,0xaa2a821080104dd83803,0x1128b87898a8282220d9,0x2229123c0aaa021112ab,0x88c49ac8821249d801bc,0x37a0e12c3d1fc3023619,0x8b4dca944813283000c6,0x23049a948c8b4412a0fb,0x364483aaa28f882a209e,0xa12380c4a3081d0ac453,0x1542d274a98c10d01232,0x2aa2326484a4a128cab4],#[0x28050248a85661a8a160,0x9c610290a99c65380caa,0x8f0a4508532818304120,0xad852194a2a58110c691,0xb4550582488c312f82c,0x2c00054a532317868228,0x830922423708061a1480,0x9383686a189aa0924c09,0x9c8bf80c780636805431,0xa4071080094c192c222,0x7c48644222d2720a1e4,0xe80e73724c9024484467,0x24a48921362b4229a628,0xa901401682044c886cb3,0xa28690e05c0cc2862eb5,0x25138664749a06ea0836,0xaf0b99aa64a721c82c65,0xc81a3bf92719a01a348,0x4ff407e0103537f916d8,0x35363be9deb8040d51e,0xe60809a23f19f06f9580,0xd596a1fbe4c9acf1b6df,0x6d951f75c48ad0c11ee9,0xb2a3eed908a5443877ac,0xab2b79f4d1b19b3dd344,0x94a9b6fd68908d39ef93,0xafd9904aa9d0f94fd139,0xfe20aad43943f4e4dccc,0x312c1569d3f9391a6de0,0x723423fa202544087bd3,0xcd475a1523487fcd475a,0x44e46767e8550a24307f],#[0x684ff1a10d68cf59ff87,0x8276d1021e3a0fcd5ab4,0xcb447f14d60504c89e7d,0xfa1514ac212224abe540,0x6c45a9434157b9503353,0xf5ec0c474f4d103297f9,0x4fde6a8234775d10332d,0x432df5ec0c474f4f032,0x9c5f009421227dc4eda2,0x6a0044895bebd3911e9e,0x5fe5d159a48d00fe8764,0xc495290cd4bccf637c8f,0x20969b3f1100a40ffeba,0xf2b23fe60824e7e884b4,0xb10884044a7f01f8040c,0x4c8d5f6b224667c7e4aa,0xff4d23929030235ccd7f,0x3f1820935d79030233c7,0x8608252c7f83408fbd63,0x40cd307fda0479591fe,0x488959fe6210486f0f4e,0x2463c8083e7f96562080,0xefd0190f9904bb4bda43,0x4c604427ff51001021e3,0x489510806882f5c01033,0xbcc402240f98c104747f,0x3d1f5f1008903e636451,0xbeffca3d38408707e808,0x677fbbba6004088b3904,0xb888d9d701196775e444,0x1b888e3ebd3004489fe1,0x8b088cc5eb102066d9fe],#[0x7e1d78819ade70499bfd,0xd174786e91947af22232,0x850f4fe0210228611a53,0x29463b808b4fbbe0607,0x4f20a20600b1317d0a00,0xcc46231c9e88330b8e,0x5c672465f701119f6d54,0x162a09a70e7a1e1cf43d,0x1428d5c45523e7fffe03,0xb9c18f471ba45c7f7601,0x510d38b548bf723c0292,0x681e5e891a18bfc0a,0xd2c68b3f411234714f3a,0x42694fdb6f112941348c,0xa6c73f202257fb413622,0x12e132b7fa6c0884cf18,0x1fbf1996328ebd122c7f,0xe33082067d6ce09414a2,0x9953ffbe849b02123577,0xe7fcdc4a0848d3df8cc3,0x904f91c283d86ae29b1,0x281a6c1004d539f3e040,0x75810925a1e61cca9ffc,0x2c5440871cafa08b31e8,0x3d3fe3cc5780288a71f8,0x233a79119dffe62bc014,0xf9cbe2367f6f2d80404d,0xa187b5c446f126c32ee,0x1147f9dcc091e1cd9240,0xa9c78f4a4209254ed7,0x329ef9c889c6fe390008,0xfaf98467e2687af12c9],#[0x8d2c09a1c9f5648cfc4d,0x932d1a147c2e922f3ff4,0xc2c67346888f520065e7,0xfa0be4591f0ba48c0ff2,0x8a8f5200655fa0be455,0xc00d0b6f12bd24bb0000,0x2491df1da52c199c9dbf,0xe51307f1b064cbb1111c,0x2153f1a997d40001aa87,0x650ff180044cf6ff4200,0x6685dabc02043665f106,0x943fc6001133f7e11022,0x143fc600113387f9f189,0x69f966346ecd0731df11,0x5be62d469f966397b2d0,0x2044cd17f44a7f3b8a27,0xa63be0246ef20064efc2,0x32e7f980ccbdf8440899,0x28e7c8747fa254f3f08c,0xcd129fda58a9133c5fd1,0x99c3e80c60e1949572d6,0xcc04bf7316a34fae3088,0xd557f4685afd0ac44cc7,0xf6bda01240faf68208e4,0xa2fe5421a153d7a9132e,0xfc9c1d384087cf94accc,0x32a3ffe83a020002448b,0xbfe80c84ccf204af5800,0x1d100810d5fd0180899f,0x8a46040d07cf6004fcfc,0x26084a59ff60048ddfe3,0x344000222f93022753fb],#[0x429bfe9440204353cbef,0x930fda9048cf8ffc2d22,0x3ff0b4890b417f881121,0x10ede1076ff6a410133e,0x53f61136bf0cdf881005,0xf7c98113f3fe88000043,0x87ed4824670fda90008c,0xb7fb5208099ef93024c9,0x69f9663a7f822676f083,0xc2044e67fe8a2797b2d0,0xe010133e3ff0b4890a7f,0x44cc1f6fd30202676ff6,0x406307d5880685efc9a0,0xfea62a987cd3da0cca1f,0xd0c055e17714753039e7,0xe6487d245685b6dc32a9,0x73413b7082153a1fbfba,0x1bd79775ccc9870e095d,0x5466fc272aa66efeeb99,0xd426a577c9dab2a81fa5,0x34a898fe4dcc93ff9117,0x7fc1260cf6ff8b850950,0xb307cfc1be6ac6da6bac,0x4477c59892221b39158d,0x4e77a8894cee0a3ce678,0x3f298c8072d11dd4b832,0x2e3b4908e88ac6013b2f,0x89cd28fbae24568667ff,0xfe854464121c8be5a1d6,0xde06068666fc6a72a1b1,0x3e3fe1b800c0d2dfe5f0,0x43d32eaacc6fc6a72a14],#[0x9fa273319edc3204b537,0xd0ddfb8fa4439139ab2a,0xfb44e66adc8c9f904aa9,0xc346bf62ab50b5b91e07,0xf2fc5ce08688c7fee0e0,0x46afbbb3428daaac846e,0x580cf4eab2a085daaac8,0x9ff2a25523034c7fe895,0xf1652434c7fe895580ce,0x13bae6493fa46a9233f5,0x1a93bae648fa4439139a,0xdc1108ddff43d2db5220,0x8ce4a0cb19fe7744b36f,0xf223dbf0556a174f5045,0x2b7f584330021a57f0c4,0xa86eeab9a65c6392ad4,0x88022234d6110dfcd691,0x7a82377dc10cb0fe86b4,0x7668011637e1145526fa,0x263e6d22165d29e69c08,0x9ac7c7003e248037e626,0x1729c319635a30c724c0,0x5129e9c086587d6c022,0x876345092f5e88a1fe01,0xe2507ecb41a7e4954266,0x252613b251c57ed8e23f,0xf0c9c32a7c26c6b79d3b,0x5e8c10cde3212bb672,0x232c16561d308757098c,0x855f6c6bbc53d16b4cd3,0x3ee2d47dd326b25523cc,0x76d386ed85104ff9683b],#[0xa23dafed8942518512c2,0xf4a04a5434bd1328d90e,0xe600688ffc1f15313423,0xd0f92fe4c9acd1ffe36e,0xf26e64adc8e1e5ba2011,0x743317fc1f0050213547,0x485f87e0c042686fd078,0x50c9ff8055328df84515,0xe917af9025a925d64833,0xc092674ffc01b99763c1,0xabcae542165c18c3f00f,0xf706313567e3c34c7533,0xd2287e01f8124cedfac2,0x8606c2fc3e847336c783,0x7dc9021a29f7fc0fad40,0x99ebcff80a44339bff0,0x8acc3ff787046efc3608,0x3517fc3812109a333e88,0x68010a1f6f1d075d409,0x4568553bf1a20d287a7f,0xf1b03225782ac337b07a,0xff9909099d5d058310a1,0x7c7da219796f9a8d42e7,0x99ef4e24b9ffb42132e,0x8c4c7fde8c628ef88521,0xc3a834fff022121345e9,0x7c122199df8d10694353,0xd3d044cf0f6b43033d7c,0x9ade9881445f590502a5,0x683af1d67359a39e2d55,0x204b5277e12a84cc4ff9,0x3821109a7622f12375f],#[0x84d55fca8a8091a13ff,0xc438084cf5f979fc3d80,0x3226bd0c89ff805532f7,0x207ffb07015640d495f4,0xcdde12d723377c055a33,0x7d79e95a723437a9608a,0xc058ce45c3ff5a116342,0x31983ff5a1163377b74e,0x1a7351d641c8d01cfd01,0x7baa2b42270f8f8ac929,0x58d2bf129456f5d2d233,0x801af1035875fdbd70c0,0xd07ff585af234527fa73,0x881a45ffe2b90908e244,0xe58708c819eb3ffe8513,0x842a53fd36b4ac81a63,0x33a9127cbc5121c5e8c8,0xfff328e2890f5f84a061,0x4248a7f545cb8a00a201,0x2c09a7a1ac8195788ae1,0xefe7b34a04cf1efb6f36,0xc943bf9137a1e6540286,0x6597d304fe3090fd0d68,0x67efe7b34a04ce41c234,0xc461f893988d9ec11d02,0x640cfd8f0cd6b36e30bc,0x9973f408c819bbf97a04,0x66d7dd9a8a1021fbdbaa,0x1642067792451dec05a4,0x24cdbda877c9604defa8,0x2d4929318aad4357e20b,0x6577fa683108e87a3c81],#[0x1a356791d53a193e144e,0xf371010a864fe798aa0,0x400a22397f3cdc840d3,0x9aa2fb4ce543ab879b91,0x445f158530504a7aec8e,0xbc6862b4271f48f207ab,0x96941b50fed7d41e7e5d,0x27134ebcb4a0da8657d7,0x87cfbe649034a7f85430,0xa800022148c9a7dd4347,0xbcdfe5e584813473c51d,0x52143838ad064dbe5850,0x84a78be500286378b920,0x85190a8f15a0e5dbc56,0x51a17a213f878008517e,0x79fa7a2715cd0ab1ba4,0x133d34b2527e79808743,0xcdfe960a06268efa4c63,0xf785103081adb86bc40c,0x2881840d47dde09529f2,0x80144b70c068cb5f97bc,0xd530510351bff2528071,0x82694359fb825cff975f,0x881840d03cbd88aef5f6,0x412824e8d7d411bbffc2,0x38c00a290c47c451e0e,0x70535f49c89edffa5222,0x133affa9f042920e6ee9,0xadff904028268efaea06,0x822633664563cf8170ac,0xd9fe24585e5440894ffe,0xff148c0819c0ed7aef11],#[0xf2ce223438a292424347,0x4a0c2f3f60292d084885,0xf1844777d0d90d0beeab,0xec01061234a7b332cc63,0x1014f8866e6c18a88113,0x521fed640cc34aeee854,0xf184868fff599c00711a,0xf8fab5b118487f7e1cd,0xfb353119f5c583b7e309,0x21b9fe6d1ecdc6122131,0x67870ea92105ffee1691,0xf51c335311abbf0dca04,0x7983fb87a6e3091318ff,0xc2437bd7160ddcdc6122,0xb0e6fb3718487370f9b8,0xa72c2201524567d394cc,0x3423e230f0be822abfd5,0x2a204463fde8d69121f6,0xd0455acd504604dfafa3,0xf16d22437b0041841e17,0xc58d1defd5d60b3c3fe,0xa0690c7f195466aefd72,0x78b0980c898fe849e122,0x1b0bfd3ea68819d06471,0x429acbe1ff010f412a02,0xcfc102477c3f1cbc0821,0x81f31a048ae7f33201f7,0x24b7ffa24b25204066b9,0x202fe7c210a66bc68410,0x52f1341019ba607cc681,0x4fd3371a15bffaffad82,0x6c2021a7f195fa024094],#[0x126d5fcd098c687c7fd5,0x200466b07ed12296838d,0xf84fc60824f7ffd23b25,0xd101a25508ff9820953f,0xcde3e176e40d1dff1528,0xf484094df1ca96a480d2,0x1ffeb10884043afcaef5,0xf7ad743240fe34801922,0xd30040d12b3bfb841230,0x38bffe0b48040870fe39,0x31841284cd33af5f8082,0x30b21010d1ae1d0466ee,0x10c4ebedc26010d116f,0x68fffa9802067b7c3821,0xa3798c223c3fe1300868,0x7f894cd199d9e8d9b8d0,0x20666caffc9ca8320348,0x8d206668ae7d630fc62d,0x337f2c56541901aabfa7,0x7467eb210490ff3bb333,0x9221a1e3dbd2db4599e,0x14224a7e1d78819a1fc8,0x204851ebc888c318fe5,0x43c8fd44008248fd70,0x87fc11e002181f12bebc,0x907e4106efe022494287,0x780087141f2db0478008,0x8577c1f5e002185a7edd,0x727a2080410eeffb0511,0x274a3e393c828818988c,0x3938a521a30c4e51608e,0x486b2f38b6330c0694fe],#[0x128243487e5f0a459360,0xe5f7d09360486a2fb687,0x4426e2dbdb112873407,0x91213507e3d64414c256,0xa47f1d69448f1eb8a712,0x11d686493db438948021,0x3a7e4414d3a2426adffb,0x7f90e352467dbf1d7412,0x14e3d02672af1a90133a,0x228674fdb6f112963447,0x213222316943297fe225,0xf424d8031a55fedfda31,0xc694e3c4a504ce9ffd,0x8773ac40474ffe140d36,0x65df3e5428cdede5ba19,0x186a653e5148d5f86c92,0x9ff5b5a598d0e07cba0b,0xc4044fbcba327494ae22,0xd2abfe81165fcbe226f4,0xaec80cf5d7f86720e2cc,0xfbfe1f700b8b11350672,0xd10abfe81167e4bfe811,0x6a8104d0c2fe9929c274,0x4931fafbacad24069a7f,0xf7f5c613336ff07e1552,0xf885492567875c61333,0xebe7b1f1a5886226f1e4,0x6345f7ed0815999f3c0f,0xa1599a3507d79c584924,0x50b27ae46781a9abada9,0xf889973e0ccccb6f68c8,0x90c0004467b61cccbdf8],#[0x3dbc6c0038219114fe2a,0xb41197c6807c95ed0004,0x9a6bfc6803e0dcd15fd0,0x218000876fc7f0236d60,0x870ff2d17c6009a21f65,0x4d31f000cfae4928dc40,0x84004543ec0138000872,0x5dfd08019a1ebfc4a300,0x84288afc300efe000cd2,0xc7ce80000446be4c3600,0x440684fc1bd79203383f,0x89ac0ffc81143b374f8f,0x1231a1eb26ff0ef92158,0xfe4a28918400449bc1ed,0xf3471a198fc61840295d,0x2002269f83d1c68517f4,0x981800850fefbbaa8a34,0x110ef4fa3420021e1ff,0xd3e4880086e6ad1d1a10,0xa0e5c910010d8f2020f9,0x34ff82b203403f7604d0,0xc685ccf1fc150101a70,0x6ccfdae3c15019a186ff,0x24f5c8cf035377c76c42,0xa11a185fb0de68a11a2,0x4d55ff8d92c44cf4fe9c,0xd92cccd5d7f8271cb0c4,0x3a81033ee3eb1c923877,0x10feab0b7e0021cbf5f,0x5d2d9744043fbf5e8410,0x622021b1fc0ec000021e,0xcfac592ceba10a20ded5],#[0xe11fd501963f4cbea400,0x21456b47675d0850,0xfcf04000a235ffabe494,0xc8083c7f8200050c4ffa,0x2200227be387d81033e3,0xc1bc61920346b2705a89,0x3fc8003397f92002664f,0x42ffe5a14000042896ca,0x80003487008fda00040d,0x1fffd8010494fc023fa,0x3e144cca011fd40001a0,0xbe32a844d0b5d6f8411f,0x87d800033a7ecba03296,0x943f144ddff82481998b,0xd0899fd808198b5ed0d9,0x6407b3ca6068d0fcf0f0,0x1fdff9050508687ad340,0x9eb4d01901e0f981a10a,0x9ed21026864ff5c54801,0xef4d22463440f89c491a,0xd4081a21d9e8968d0d0e,0x17dedb82bc102203c035,0x68683dad708240ff9c81,0x6adf5af088defe89508,0xd796001a2bcbb87a6204,0x87f7ed06c20001115e49,0xcc3a41a2cdfa3a40800,0x77eb0400d2cd5fcb080,0xac11348077eb080ce9f8,0x459ffea201193f2cd2b,0xa20abe122a333ce56,0xfed2d00000695797cd80],#[0x1dbc20e5ffd9200119f3,0xc4400d0f5edf3b40009a,0x778a64676f083ebf97c,0x9103529b37fe180021a2,0x44d0ff9084010a1f8fa0,0xfe2b113238ef14c8d7d1,0x12619ea645b78490685d,0xbe9dfd7443bf041cfbca,0x4ba1e9dbab04ba1b1224,0xfb146812e87e78953d1e,0x92e86c4b1f4ef825d11e,0xccd4ddf1297436254f47,0x7953ddd18aa19bf7d619,0x944f88aa8edfbd7601a6,0x113b3e26d464f8dcdb99,0xd50b4a8ae7417d035081,0x7f064a81a543ca5fd4b3,0xfa00b004344f55881466,0x34fbf0caa2153cad3207,0x96aec3347e1ff02ad184,0x1b67ed57f41055a69eff,0xefdbe2e3521a7b51fe00,0x86c468fd80932cc044b7,0xa3035d7effdbdc10d514,0x85cef51bb87ffe001826,0xa677a8d1ff398c9a4344,0x53306bfce7c20cd4e6a4,0xb0533f425ec5331770cd,0x4c2e3fc01c52a1b3e10e,0x1ebfc3182f2129dfa141,0xa8d9fccd61c02c094e6c,0x23f60e060ae0358c6379],#[0x60114a87a8f3b84579a2,0xf37801102cb0c8a860fe,0xf87046e66d7fac99d0b6,0x88c5e19b03f5832733f7,0x114a880f97ec81619e3e,0xd81f2d832cd8fdc5e60,0xaff4561782453ec53039,0x604150fefff6a808c443,0xc5352f7cb60cb2e3f00a,0x1980d35f7439c28a3c5e,0xdc7f08086743a7fca88c,0xd846ba67444de2090523,0x7ea72d60d4b04035e3e4,0xb650688069afc62960a6,0xe2ea6969deb184423e07,0xbd867df946110904df10,0x97f4e4432048d71fe518,0x98161953fdaa19866af5,0x58a67cacfd790e28692f,0x6be5ca03208488a8fe20,0x1237d3d41196dea30aa4,0x824c8dcf00291bf28c22,0x4ccf88a051d7ff23cf01,0xdbe51846096b6f51840a,0x86acf85a4787f810d33,0x2bfc6268ce1d1a1c3fa0,0x169f5e43c0426aefc6fc,0xa3d0034e169f5fe3133e,0xffd5dddc2213687b6faf,0x3da7857ee1109a93416,0x63d109a43db7d7d1e89a,0x2245169aa004577db67e],#[0x1d239d78e001a1353bf5,0xc3d3a8a3a226f9e7205,0x14742a6b1fe54c24340b,0xa4b4f9f5ec193cd30f3d,0xc06a3a193d4ff2816121,0xce1fc31c0b090d14e3,0xa5f1c02b44d49b7a7fb4,0x7601a1bc3cbda2664a7d,0xf07265260c288ab6be19,0xd801a1a59ded63d64d3e,0x48feb1e22c4d11fd79a2,0x18543742d2f8e491626a,0x111ff5cd16084d56853d,0x52c10998223fd3d394ce,0x86e7bf9c380404d91fe,0x35dbffe188a0a000828a,0x8804d41084f1ff2e8101,0xf8e0c30a1c213c7fc83,0x29c0ffe263fc400a27de,0x8028c87b3d831c18020a,0x6084cf6fd1e21a1f7e00,0x50fefd18020a19abff29,0xf89762d899e147a68c18,0xb52bb664ff9236099a3,0xd3144ccd1f2edd442688,0xfff4e0c19a88b135b7a7,0x4ca5fffca28b49c626a0,0x43cfc1757689a7bfe96c,0xf7d185f4fc1c395e50a2,0x7afc6dfc8ef689a460d8,0xc0433a1f691838ec18ea,0x9ab1f915010ce87c3bc1],#[0x16533a1a36f6fe0e8193,0x145531df9d70a2a949fa,0x1ea552485054f86f676e,0x5e2b44d21a43e9d0033d,0x1101b7fc9a2664947e5e,0xc940300d3cfd9c804520,0x3fe2e4d34c004407f8f8,0xd16a04a6006bbc366134,0xf6a2eb8fa263400878ff,0xc4da8deffc0433a152e7,0x4910ccfed8070c28759f,0x87a7e05404b4353f9590,0xd13e248a28bd9b60541c,0xd7d907218bff1700954,0x80088278bc5402488756,0xd11d29008a87fc5c9a69,0x3f8070800b1358b0b3fc,0xe021334cf88a051dbd3c,0xfe98b934d010008a8ff5,0x82003668f94458093a,0x1b6ab0c2876f8ffbe36a,0x1a67c4da8bac48da101c,0x3dfc5794ca1ed5528060,0xd60621293fd01700954d,0xa86cfe45794cc07fc95,0xe7ac2860034d40eaee82,0x6ca0ea19ccc96a2fe8b1,0x4286a0927ff01a904260,0x941820881b63e5eb2290,0x7fcb830412352698ffbe,0x7a7fa52bdc843035f74c,0xa8c04522717de703824a],#[0x6408000469696cac83f7,0xb011789b21a3e4263637,0xfec0148426bcf0f2d867,0x91a4b4effaa4433d68d6,0xdff304bd4939ed0c1160,0x50884cff96c0d842681f,0xbfc5b244590200a2b1f0,0xa082864b7f80a412346,0x2868f6ff0d820268363e,0x20d58f82844263fa2208,0x9420036d7fff03e98108,0x689810c5f7fff3a71402,0xcbefe01011084d86c1f0,0x10c24cfad7011c125bd3,0xa809c68483022e47fae1,0x97ff402010a109ac5f7f,0x81122082881feb023823,0x78fe814110800d56ff37,0xbfd38d01293c3e1be006,0xd1a79639383009ad738,0x894406272510bfe60a5,0xf4ce9810844473e45a68,0x630ffcffd042121351bf,0x2244cf98527f6d8c013,0xff618c629c7f64bea021,0x228a24bcffd042121341,0xd34fd9072117fff8f02,0xdff5a4213367d67d4111,0xa228441e8f8104110512,0x1045239f9e4e2273f3c9,0xe022219cffb0c63148f5,0x2233f32d3044303557eb],#[0xa822181a49f3f3704400,0xc40456ffad21099b3c3d,0xd7d44e89a7479277a369,0x34d05fe9c9a266497f7,0x2f3f010010514dff7898,0xab6268df6503c024a2ae,0x96bc689985468ee5f4e0,0x8c67efa2378cb5fe58a9,0x629c87a266459d3c7019,0x42026c27f867421a1e64,0x109fe19d085f786a8115,0x466ce9b4834edccfb3b5,0xa326d20c399e684e9921,0x99913a8aa4cfa20e644e,0xe0101352fffeac06144,0x426b9f115514b4fec1,0xfec260629afcbcfe1a0e,0x612e76a999384ac19663,0x35615abb12bc32e754c,0xcf0e02d71035a7fc3b07,0xd3ed840cc5898db9fd7f,0x5cc4681a32acd1e3bff,0xc6ace184b4d8cfdfe1ee,0x40414a22b9fc2d44fb04,0x55790d0185089368fe08,0xdb1aadfe08e020a50ece,0x97f708acc1ffb281ba4,0xc1012ce1789adffa0349,0x8ac39ec5084a06acdbf6,0x497f30f45edbf4451836,0x898db8f0bbb620c33251,0xa6a8d11ffbd3c4c7092c],#[0x3f7977c6cc4694fef3b0,0x2504cfc7fac9a002329c,0xbf07f2adaa0169e0dbff,0x6e91b48d52ba9e5e4218,0xfb93fad822016a8fb9b7,0x264297ee4fcb81582d25,0x990bf968400991109bf8,0x4814473e8c4a0d30008,0xff85971448797ffd3647,0x1131ff4f9f94d000d20f,0x72b50908ab5fa3832400,0x884a6efb4fb168cdabdd,0x70ffc6314099dcf484c6,0xf7da7d9388cfbac117c4,0xc38c24397bcb2a366234,0x198a64bf045f11e5eecb,0x286edbe8d5466f3cdc8c,0xf6f166b5a145f833585,0xa2d90c06b27c14780119,0x85f9f8c6d90e682f595a,0x66b732ae101e9f1d0909,0xd4d1f96b064cc11a6c0f,0xcc9e06acfc71cd993440,0xb8b074d8c94d7ddb6b26,0x652a153f716cdb22d09f,0x371dbf7148a05911afcd,0x2a1cd3bccff2cd619635,0xbe60d3633a1cbfabd3d8,0x3b47ed9832c46d190335,0xc7a7028247bfb41b8264,0x46857cf266e000a0448f,0xd4a3ca283407f974d908],#[0x9042448b4fe9c204337f,0x1a275997c4697fbd2c30,0x3e53708488cede5d3651,0x411c3fb4042d19e507f8,0xee5d506ce0991031fa57,0x51983f03c6477fb29509,0xb1465021c676a217d307,0x20840e4559d7724c8fab,0xe2f3008a5443b83f1b7e,0x80968748f96c08d67c7e,0xff17980452a1d1e9ff6a,0x28f1e18ad4aaf012d09e,0x23a201ff26c235d33a2,0xfa6c0188e87a7f56a808,0x229a02ffe7d407104a77,0x878b80c82121fb8efd53,0x3860122387fb20660a69,0x2891fbf23e70c0250f1f,0x198189ae5fe88804400c,0xc2c7ed4dc196b8e1fec8,0x7ab65d281cc8847221ba,0xa143a81aadf4aa4b186b,0x809688179105e123d9fd,0xf2a0d13b687f7d796ca,0x355a9c42ffc93ea0a510,0xbfc620c0161c4c28bb11,0x19032d1afe5ea580e43e,0x87fc3c3b8d04d39f976f,0x13deba0ffdc43c6826be,0x20008dc64ddf88063205,0x57d9e1e9d5533f708063,0x517999783519e93fe653],#[0xc224cf9f24f1e5068003,0x8823081af06d706dc4f5,0xe4dba080870a2aa1f3ef,0x4099b3db48e20d468465,0xdff2f7108c0269afa2f,0xe40a205fede00442051,0xf6f95012209a79f26de0,0x1b3cf7a8ca58f046b297,0x6af1d67359a5d5c8025a,0xe5010d3cc21e43d131b6,0x5da8ce889e610edf97c3,0xc0691af688f08f2a3eae,0xa94c4e301191b7f64c0c,0xfc385019cd00776f9a6f,0x69e7f446aa19d640228b,0xeb201175ff97b6506880,0xec0b10a89e7f401b550c,0xbf2dbea0d088d58f1550,0xa685239a0cf1ea52a260,0xf2cbf04aa67ae7e1604a,0x35995c5465e04082a24b,0x48585096a1aa66887b02,0x2a1c5fe2031d0a0fe24,0x4bf82c30150cacbf0586,0x30a3deffb84031808045,0xf1432234ac50c88f78b4,0xd316964c2ff100c66430,0xc35c40d094f97bc35c40,0x389aa5ff388010b5f97b,0x3fc2e4019b3edf09f1ab,0x25388010edd374ae499e,0x8a2f87cb8dab389a9dd7],#[0x362e713556de7c6d5926,0xebfa6080a206b8ff5a64,0x10e41dbb57800d19ff2,0xd20f1814136abd3a1900,0x83c740a001ba3ff7c388,0xf0508028006c4ff0e234,0x30279f88bf2023c7fc3e,0xa7d120200240011877f2,0x4a09a0bfc03e00336b6f,0xd78390110043c7c7f1ca,0x8d7d41193ff450280068,0x512824aaebfc35114256,0xe5fd0803061035aebee3,0x8623e22bbf829c204357,0x423d04627ead00e3090e,0x202881ae3ed4d988ce3f,0xfdabf210058d35ff1298,0x917dd0cb8299f84e891f,0xff160200b1a4788b9858,0x89412975c78351142517,0xfe09f71aea08cbae3c1a,0xc504fd5a9500010f1e33,0xcd7f148c46005115ba49,0xabe00491ebe201732004,0x8904d03f423d04613df8,0x24d7d27227afffe4d5,0x964a2be93913affa4b99,0x804d25ed5d000339cfa1,0x87cfe214925ffebca211,0x23cfda1eb1e8214973f6,0x5affa1c08429267c4885,0xb82a9f84e8979bc31181],#[0x2c78f124f500251cdd0c,0x862302b9e2687ea78429,0xefe4b227bbf92c89ef37,0x2d10fc32389cfc32389e,0x52d16977e9a198a869dd,0xe7c5764221a1fbfd7350,0x8ff2c21241a1c778a646,0x881a94d9bff0c0010d10,0x343343ec10da2cfc7d04,0xe33cc73e462353f494a4,0x2844a421d51943e28432,0xfebc40cccffee23a586c,0x882f0fef61e82901a921,0xa82811a40a67ff60aa40,0x767f57bd07c0870fefcc,0xfd92811a49fb19403c48,0x121f18fa914710dc1f49,0xecf45194c8727f29ac46,0x6c104668fdac9408cecf,0x53588c243fb074484ef8,0x5c9f3fc120a3281144fe,0x104513e7f82414e10226,0x40be82413e9f3baa6b60,0x24513f96ca5440875fed,0x268189345f7f7a148d2,0xfeb66c43068d7efc954d,0x818b07ffde852d121fba,0xbe82403fe425101ac214,0x281123f423d0465fed40,0xa5a10227d753affd29,0x9fe25305510360bffe58,0x765e7f894c15440d9d97],#[0xfcfb2c9b4e5a48195038,0x503757feb60a57c0d059,0x1c3b977ffc9b4e5a4819,0x39ea3f6fdab2ed240ca8,0x30bfeacb61600a132281,0xbec5e80442c6b1d705c2,0xf1940c3abeb803e04357,0x4f3feec06f48187b73e8,0x99180b7c1ff44044a04,0x5a066f7fba6d7bd39005,0x1969fa3c654990f5f086,0x29fb43af07a50971d2d5,0x1428a81a41fc1044a043,0x57ea822e81faa08ddfaa,0x14540d3dfaa1428a81a7,0x5b44881e3d2845efd50a,0xc17fa654408a941fb4d4,0x33cb0411d0cd12275e2d,0x1465322431fc0535634,0x8ce18fe32a8cc8ff0474,0xe18fe318a8ce18fe30ac,0xf93149911018fe318a8c,0x5021f3c03a9e0670794d,0xf0c72588c089959f8a75,0x610e3ce9f5cd284937d5,0xbfcc5a22643691f5d0ea,0xc0f450668d6d8d350344,0xd84d0a47e04c32684437,0xc23ceaedc684ffc87a46,0x6982189f9557fbba1abf,0x1a6938255618340bd102,0x22333043f63978c35d0c],#[0x225e4f75595950e6ffd0,0x1ca8b100f2f24d839516,0x437bed692310d2f2480c,0x7bd16fb4043d3eac0127,0x4e3ac19bcaabc9f0e862,0x410f2abc7a7629811101,0xec26d4f042fbf4c4ae80,0x83d2808577da207ed010,0xb8c8af069890af002209,0x406a043a227bfa066ece,0x9cbe9e1e98981a354727,0xc9f7398c0874ee1ea981,0x8617f9284b3a1105126f,0x1f52ebcee2312c777aee,0xab36224ccdbbf3b86c4b,0x7338dce66533b6d2301b,0xa958704dcbc818cd5103,0xa5e0d0b86044b3e1d8ae,0x941941260877391c3ebc,0x8846ae11ecaf414455b4,0x82bf6926807e21c17282,0x561e46fe39c4c50e9f9c,0xe11ec0f14473dfa6d6e0,0xea7a42d6d25054ea453,0x2fb7a2850d8d73749505,0x884fdc5d7f000d14e,0xe21c956c4d2ee2dd2aba,0x8033c78be0bcc189a636,0x287af21e31335663d1ff,0x14349d40a8c941326ee8,0x33a8915fa0a199ec0af4,0xf2f5821344bcd2fd4814],#[0x4da2134f17ff18997ba4,0xe900f0097d806a28f872,0xa233ffb202c35e00d35f,0x9782b04d20fd3e571d30,0xafb0630385985145e5f8,0x229a0a2003f82f626676,0xa1aa99f9e704cf4ff825,0x3bd2326e89a782a15d58,0x100ff100dc7a004477fc,0xd932450da7797cb818c5,0x78acfd6ada6981a848fd,0xcebef9ae08c5f5369a86,0x1f6f0d001a6304cb8684,0xb4624c03abcbc4d3dc68,0x4883f1953e84d0bdae96,0x1e330a6109a63af97899,0x3f105149f79a7e800ce1,0x9f361001a7df74d260a1,0x287d60c1427e20a223e9,0x836913414c8f8aae1948,0x4c86e55f9571c384381f,0xcf965d6342cf0fd98f7f,0xcb9f2b633f3cd4ba3086,0x45f93030b07e1a3293b0,0xbaae0042dbf4eb240864,0xe1006a4c34e9ee0068c7,0xb5ecba714cd9fb529363,0xcf81ca85b3e1110cac54,0x2f70c9f87384ec3c1a0b,0x85a7b9d2f70aa27f5d,0xf0215ef8a499498f755c,0x3460ea13d7020cecf549],#[0x79021e1f1c6b03810e2a,0xf413854650223de3d146,0x7045a08884f0f45066d7,0x6ff2ab1c02031468b17d,0x829e957f53e8d630f49a,0x491615818acacfa8c404,0x1ff018b2a408807fdb0a,0x7c0dee12270b3a22cd24,0x3135ffc63905cd0b4cc5,0xd46c0c4132599242c9b0,0xecc9247b499118fe6703,0x676648011dc606265]]
set_option maxRecDepth 16000 in
def g253H9 := limbs80 #[#[0xe1180100a0680000e009,0x8008020081680180709,0x9807024044080000000,0x90d600c00002006078,0x80120000000006601c01,0x28000000740e01,0x1800002016008018030,0x80280700e01400006014,0x10010000e80680501403,0x2000028030390200280,0x200000805014024000,0xa1400f8400020380c806,0x300a80109e0140280900,0x780e00202c0000f06c0,0x8020021640082200e008,0x80100500080102803400,0x2058000150bc0700000,0x641481900e000118140,0x20000080844300a004,0x80007e0640280c11e01,0x6020000200110780240,0x14008000000000080b8,0xe0b80b8070a439804800,0x70008060000ec6200007,0x40061140001104e0,0x81505c0640580200c2c4,0xf00c0a04200401008400,0xa41401701a0183b81,0x2000803016058000050,0xc0000900809401804000,0x380f0860040200c0000d,0x40000f82800208c2],#[0x40040800200003c070,0x81286903f06e0bc08833,0x1c058430ac0a00704c01,0x300c01c0d00202c0,0x87d00406406051000008,0x12a0000101301a01000,0xaa01c130170040300080,0x40180308c004000091,0x80684e05601811005004,0x900108a0000000201600,0x20120100c0010000200,0xce31420819008368020,0x20dc0081900e1281881e,0xc488271de1b02580203,0x2c81c00e01c0501504c0,0xe0160580602500c01c,0x50000281680500201807,0x160000000101203c0704,0x241180b07a020058020,0x8110ce0c806830010,0xe81100606c0700b01c1d,0x1916608c1b0200060cc1,0x41000c00a028030,0x4104080000060005e02b,0x120160680100000,0x103d0c8010158730500,0x80f00403008014032074,0x70360000100507601807,0x22004010040ae0cc0085,0x1005001016020120360,0x82e8440181602280003c,0x100102601c0d8000ec03],#[0x10420d8040020181840,0x240800b000006004168,0x61800181100e00007842,0xc160c502e0040289000,0x2200209600c0782f0720,0x84e0bc00804813026028,0x90987580b0000940308d,0x1801c170a000c000120a,0x80100500220c068280,0x40905c1760e00083c000,0xa84d0120300d00100414,0x1903c06c120370000580,0x1921c8308010dc000008,0x400c0301800601001004,0x202200204e0280081604,0x280002c05c2800d0060,0x600404013810008050,0xa0160c40d80100002425,0x80083680907802c0702,0x141181100a0100e0260,0x1c0900686100c,0x240101d00005802200,0x2f0940103a0010400400,0x2c00008022002090018,0x6014028040c607c15042,0x50190010bc1201380101,0x110000260040483d0120,0x81800c0182080f03e254,0xb0ee06c3300103613414,0xe0038238121623b00403,0x43080200a060140110,0xc2781700203018013012],#[0x781f01c0000400800201,0x1900000c0280d0400000,0xaa004338020040ec008,0x80ec1700c02e0042d872,0xe41600e01e0707103800,0x180580201582a0280b60,0x2507603c0300e17e178,0x300c0200081004a1482d,0x8c01408005000008c280,0x2681900f00a098048120,0x80081100000c000320c0,0x80200e0340402400006,0x41120e00000c01a08c0,0x163d00182b0561906d0,0x20c80000008c04407810,0x2073807004010028001a,0xb06a0140181283019c0,0x80000001c0088f01e060,0x101c008138090280440c,0x4a1500b8891600001209,0xb8018060060fc088030,0x40081305a0783e000004,0xc00102014c0000310c00,0x240241d01303b0065704,0x141383c00e01c088,0x800c0003d04c0c87c814,0x28008ac0060000284e1e,0xb200b01e0b00a96707e0,0x300a5e40700c00e088,0x50040ec050380d8000d1,0x80c4171250080b43a84,0x840703d0280a83e09b0],#[0x83581b0f80e400001072,0x894c01c0140201f00802,0x1e0240680700818e0dc3,0x2e12c1105a08400c198,0xa024060d00002ac33802,0xf84200d01e5141880104,0x5100206c078071261,0x8281c8238408020cc075,0x902c0ac4504000800414,0x607c2f0190021180581,0x5480895b02c008000660,0x42a03713800807956022,0xd0070143243601704600,0x1c0001ac1b00d0880386,0xe05c070800140e8848,0x415c088de3d41b400004,0x64030020461c43c00c04,0x688e0000a4280964820,0x841a806c03819050008,0xf0f20f41d80002604813,0x620182603b07600c0513,0x1687508c0141288d0,0x40280600e044010274aa,0x383b02a0005b85f0ae01,0x2244700450081082,0x1e63e80500a01e0c4b40,0x1ec3f8a026400011025,0x88230a601400c6806f04,0x900c0040002b8080001,0x8030081b8130090a4a58,0xc61100306c0163241d,0x7a02c018070460c80580],#[0x40d1cc35c0200311b0,0x8080070080040a031130,0x49c20006680e0260e602,0x50080000382b1393dc2,0x7a01436866010618090,0x6300007e0000043e804,0x8b5904200c2603408300,0x7181564091081ad62eb4,0x2bf98089a0a6c00be403,0xd60631446482db209706,0x38682d68a7d24ccdc2f,0x68267d0304053c404458,0xbe48210e0e5281ab29d9,0x3720243823224000000,0xa1822cd810c800000000,0xb5a0bc10ac02265691,0x2c8044d1e8400dd00087,0xcc103a4c2a2e9360a80,0xf20e100010e0b7f06848,0xa218422e0937,0x189c0808ca95ddc82160,0xe0880ec60b03256b0929,0x8000180a248b9c21d940,0x7b297b0a76e60c6ca23f,0x825da067602e800000a3,0xf480b98000000002126b,0xa4a2c05340079e26,0xee09e28367e06a2c6c00,0x1f605e2060ec31b8c33,0x4039000e13a72584db40,0x236002b80d65030fe0c3,0xe0c2f01b2086888363ec],#[0x1d6101881988000140e3,0x8884ea0e20f990000001,0xfa03abe8d63007a6807b,0x84cb80001047780a,0x60978965720dd6a5b28,0x1312421102b1a425c000,0xb003f638428281800018,0x646209480001c0e548e4,0x800012b5d000018a6f00,0xf2a0cb8820de0943815b,0x87aa000042e9e00,0x1c470c0b9a00006063e,0x933da49d218e78251800,0xd049bd832f62bd990906,0x21c88002902670c2f827,0x81c5a02590c924a0ccc,0xb3b84c58011c852fe4db,0xa023d05cc84e7b27a6a0,0x5f601de8310607618225,0x8340600b650e6a077300,0x9483b6a355007877321e,0x230346c8c4b0a84816,0x28074104ce40b10adb5a,0x33d2913f0402a077aaa0,0x1a4bd70d18885e2088f0,0x4820e9de0a2502d78000,0x818eb2481404a5a184e0,0xd4049b500bd2c41a8187,0x81fd20b1f0104a894626,0x65a887601cc29fa829ea,0x346c2dbc00020074aa5,0x4c09de80588098153448],#[0x3aae048905e3d1b568b0,0x8319cb61002a1000001,0x3ba188861643013ad010,0x22351223f000018a9fe0,0xe2804d000000463701a8,0x1a28072ba2670000106,0xe989c2430802264815c9,0xa4811fc9dd00197423,0x1b4d0a80eb5184f80f64,0xd8098246d7e888a00c,0x982ab09dc602c054409a,0xd9715e7e0ae30cf0c804,0xc8230a77004d9c8318c0,0x5a680f125cee04bda1ef,0x2d496c646d60078600,0xa000c820a3f8b27a08db,0x152085bac26f88481c15,0x80001cf20696a921536,0x9fe10868055c872301a,0x5042a91b09c06ce4a160,0x81701106a7e90248c871,0x65df40469230e5820aa0,0x68a04470112a4e930b7d,0x9d9412b323278000184,0x28000045d5ba76c0a554,0x2bc0000a8089f8466697,0xec9b62a158141bd83790,0x19f22a24927549ae3a9f,0xe05cf602c4a1a7608b72,0x11947a3082e80c29006f,0xc0cf981162065e012dc8,0xdce42d1003528c6e0d0e],#[0x32b8856608e120d6682,0xaa931ac0a7a000040a50,0x1257138e6bdea0d1ee25,0x2307e8338204430b5f6,0x2a4a0bdd317d4002d027,0xa04c764e5800fdc577a8,0x500000044e050228a95f,0x84e98410060c1c036dc2,0x5f2137c809ae252b89c1,0x34b0adf20799a272301,0xee88b162c778300c0b94,0x82df275f2031bab8f257,0x2a69c82f6c4e3d02460,0x12300000037c2ad64000,0xd5073f4d0981af00a528,0x3be3104609642e9c842b,0xc3d2fa2d8000014114b4,0xca000ee8368802b72026,0xe6c8c5f7c6bfe231402,0x1c00000061400004a67c,0x13b7825b80000a6d140a,0xf8000004a0c0c110203a,0x111c403aa422f1833,0x880f361e1f038b601e40,0xb602daa4080d84cd4216,0x143ff85d9a8bcb836fe0,0x2160c96826de594c0227,0x2b568000002e66ae4181,0x40415434c40100,0x17600acf095a70d1f800,0xe81196c0558275600eac,0x1e84090281510254e909],#[0xbc47e00e8e0264c81010,0xc4400002127502b8541c,0x8ce4a000060075295d41,0x72845dd02cb048d88135,0x114e3983a6bde466202,0xeb2459404648bafe00ed,0xa5c7a2cd22372023,0x40824071fc88fa82cb8,0x1fa6085226b4c1cca000,0xe0000000000000614700,0x3fa0000045df177a42e0,0x8964a8b4de06928330c0,0x29011d30eaba00468aac,0x8166e21f834a280ba5c1,0xda0132ea532a23980000,0x4cf582f4a0350813b602,0x761dbd8b9b61090a2605,0x38d607c3a395600fea15,0x830ec4d8585ff82081a,0x14a024e204fc8049a128,0x80001822f02dae000060,0x380000000f0022fcb312,0x5c6296d38266680f902,0x838b6a80927a05aa07dd,0xb2409d36029a08ad61d,0xb543e746106145b865fe,0x165000000ce7022c0012,0x7135900bcc0000000008,0x75d0316a3abe094b6181,0x41df393272122825cba0,0x25c0e1608c7222e6833a,0x939f82e112df854c3137],#[0x8e926f829c750ed65e03,0x2c70b2f40e612208c83,0x760b528084c038fa1ba4,0x227e0823909ca178b025,0xe2953c0e9e8b03829b7a,0x8f886644094096556970,0xeb0e10955b0b6d25af48,0xbf81725800fa18108389,0xd1de4523c888aa68a09,0xac82ec8017b81d2c0d41,0x4122820260421029360d,0x3e927300c4503e001616,0x211c069a01d52223b823,0x127a7004f2000060ab38,0x171215ba059ca22f8000,0xc9b0ca2f5a621b00ca80,0x35c021e50e9e28a48b08,0x80e700001a03a8087693,0x1d0323622181241c1250,0xe29a265087e50242662,0x7c116d81eb0119f04466,0xabe62c5d03af28e3a079,0xb08df80001847e41df80,0xa71ee070f02f1e271,0xc0457005c80d43138880,0x7d800008470c109a017d,0x81018814e854982d7b13,0x3d42fc20a5b8275688f0,0x24f80000000010404c06,0x3a6c818b2be1d0a038de,0x16c00e1e93b1000008dc,0x8314a0d3600004824b0],#[0x4e800aea0c81839ac08c,0xe0b86000000afc000000,0xcce0312895a80001877e,0x4a3a5c14093a80,0xed82918066482cc02048,0x1aa00aa74cef0724d09,0x3f52170c3c908df86010,0x936901882adc45f002f,0x7a2db612c7c68514ce6a,0x302019fa042c80a4e055,0xc9733165a64cc1802f50,0xafa01f881aa001be8ad4,0x8b3ec081823739284488,0x7e85b4209e9804e0041c,0x88d003570132b2153e2d,0xe0a1902c6220a2822d4,0x24148d8c02cd80000aa0,0x39887e8d9901690016c1,0xd660822413fcc103e308,0xa215b8dd060acf81a7e4,0x44119da38c00001001f,0x609c280bc00ee508,0xee000002ea6000029a18,0x9491f42b985055601d,0x1a2e74000004c6c4472a,0x74c49d0f0c8187815,0xa05300000a021000000,0x2440000202aa421d0000,0x8000022f914ce8218802,0xcc6e0000503e9a115,0xa993e23bc83af801ec00,0x44000074d2d2e9be07af],#[0x1ee1015482bd7a36ea0a,0x400ba28aaeaa0791272c,0xe60057aa454ca7dea59,0xa00d540d55811be10f9d,0xd1480cf2482882a84089,0x603a103050133302d0c3,0x186264bad5080001806c,0xc4542857c8161800018d,0xde891cc0cdf48864451f,0x48a800000b6ceb085a24,0xf30c3f294ab107004626,0xad5a0448994e406e300d,0x90046a4dbfa1c4e462d8,0x9af8447412638654c219,0xe182080d260d3c0258e0,0x52a96ea88212bdec0c86,0x88060055a278e8000087,0x490048a08ae82a0e1eee,0x8e9c3af44d98821b835,0x8a2a1e8069a15afa1552,0x1e0203d00bae62cb904e,0xe81b7a10e9225f800010,0x7550022a0ab4004ca470,0x2aa98b6de1ed61392e8,0x89696ab0282c95a1124d,0x207fe050c09b6e1de704,0x1037744dcb04a860286,0xad61780402450bab800,0xc0036da2666887993ac2,0x58f8973c028a2245d0b4,0x91266022d504db252b78,0xb3dc24de0377a211205d],#[0x285dc0031e5e07221b40,0xe800018064e29e28095,0x8c908809001a60ed180,0x8a00004001b80c600001,0x1dd215c605f1a468a08,0xd634f102f260844c0c2c,0x2ce2268000060c99805,0x904e2085e204c1e4e652,0x34c0abd6179013a7c00b,0x104b580000000000,0x42e2ea90b1571c3247ab,0x45b9f4d0f01840099506,0x8f871060b970a8ee0c36,0x8a5a07e0378e0000609,0xf608ad002849afb41046,0x9a60574e03f001e,0xa8862000000000645340,0xaca17b748d6712bceba7,0x1647c33a829c0000069,0x1d6580a5407cb0358,0x3a20000102c5021c400,0xe000004239f02fce29f3,0x925e0773800000a28e12,0xb00001837ca2b9200002,0xf482070c0000000012b6,0x81398615d9a2d34884e8,0xd849374721fa2960e231,0x68183830583cf2206281,0x9161d9803720dc7b02aa,0xa21ca203681a30829283,0x940e6a804e6237f20c65,0x36260aba039dcb1],#[0x8a9c71843ae07ef8ba88,0x49c82be8033f407c8ada,0x7af6bc1cf5c0f6a22fb3,0x45c02d40dc99406ea80a,0xa48d4939ac04c0281fe0,0xc2c2b44a59564c628938,0xc3436a08101348227a81,0x40a955d1eba00320000f,0xbe701e2819678342618,0x3a0b320370a1bad836f4,0x315a0b41c06be0020808,0x55077a0da784b0a9ada0,0x361001dc0ce701900472,0xe0a9b02c4e22b9ad5120,0x61b44600aa5a0a0d81c0,0x805684e8701c60127aae,0x7fa319606dc048160ad3,0xa652a05ea29b98845416,0x98060f81e880ae8834ce,0x32990cf50b9dc01118a9,0xf8410c4d5a23a4d1b550,0xe1101b60800484aa80ae,0x11c5022140caa038908,0x45609f82ef1a0411a76f,0x846869d8283226873153,0xcc021d40d5725c63036d,0xa3b0ab9203f3ae9c62e,0x2c07c603a8405cf21fa8,0xc1f01529024f8034109d,0x125c8a131505fc2035c2,0x65a037e904a70333a0e5,0x2d42849ca969d876ec0],#[0xabc04e1029a4b6ae4708,0x81d3809b08b270000125,0xc2c30f01e32827c80001,0x131284fc62c3a804ba0b,0xf60ca2816fc879b00fae,0x43b004608019a0893024,0x54c390102b0943208310,0x50609a5010e484d7606a,0xb1b688e63c2566000062,0x4ae819a0245c971490ad,0x888ba4d7e29530025381,0x5c9008e0de7883be048e,0x1c10301475131c68d,0xd864031330800d1a9580,0x2c008fc317ba004d04a,0xe221d607ffa682e20308,0xb7a20808972401d98183,0xc0db2000002df621dba0,0x2984ead201de1daf8a54,0x81a7001c600002051804,0x3ba99da25218221e0aa5,0x33c1902bc8917919d245,0xa14cf9a82214d1040734,0xa5b60de8a81bf11588a7,0xa8140600b381a6401140,0x8dd82a00854780110a56,0x404fb0065c126da06760,0xbcc2167039088078010f,0x8377d4053357e08d69a6,0x8782faa1dfc8229e0ee1,0x422f89af48c0311e7a04,0x4e8e408ab0703120b238],#[0x20c7f24054909a050,0x1937d2050608e3b132a0,0x826039f2097000000000,0x60af08cbd20c59911480,0xa16177301abe0467245b,0x503fd05,0x6f29fb209c9047da3430,0x173f077b002dd2b9080e,0x800cf693a520dae8364c,0x88fa488da54ac0514898,0xa016ee21fb207c200990,0x334814ba8c668175c1cd,0x60625023590d29817180,0x9dc90149209c4c0eb,0x13b2a5ede268fe04b400,0xff00a9ca64d533ee857b,0x97f01c7c00cf09a2ec1,0xc51af5004c402ce82bd0,0x31800790b17930d2d065,0xc8afa80ed6875ee260a0,0x593806b0008e00004181,0x84d6000490066eadb0c4,0x4d3321315e6621b7026c,0x304c8df2828b237878f,0x36a206e2aff29d541385,0xa538000060b2a0382e04,0xaf0b718821800018310a,0x44f14c2f81f60a07702d,0x792b1151c2236740cbf0,0x1805380ecda43e64da,0x21e6021c6e1408084400,0x474b541a83f8a6800210],#[0x37843085805542a5353,0xd083ad82afac471c073c,0xa69e00000044c21f8a96,0x881ccc823ce4e5f04b26,0x46361309307e0136900a,0x1ae9f600d9894fe09fe2,0x2b1832ec4dc901e60000,0x82d2391c2e9b61a45460,0x36000000242a02e50aa7,0x86d2c127f830e0158801,0xf040c4011aa03ba208df,0x88a22742d620234e90,0xa4276a3497e88f200006,0x8fb0c3a006640403a5b,0x80dae0e9a8722c01660,0x9350b5d845ee81318000,0x60dcb808e61709205a60,0x7240c0ba20ca2964809c,0x49fb0000000003039d91,0x6001aee873681f9c0136,0x97a83634032f86ac819,0x620bf4036500d7c01420,0x172e05aca56b80862407,0x481662420d81fcc2eb69,0xc307794274e032d013c,0xad94c03a4288e4896460,0xd4a0e4e836420668029b,0x8374a0b622373290e880,0xfba43ae0990890f21117,0x807813d20c23095b211,0x88d9b838fe00c022d1c,0x22000973c4c851b668af],#[0xd4a3420a64822860a8b0,0x6e784cc2217b1635601f,0x113a0e2cc2a69540,0x3942509a6b62137e0043,0x804240cd80b94c0bb981,0x5d005bf01be8abdc1d0d,0x8a96506cb01c005f8029,0x800008857010f481df2,0x6ade2c26000000001b08,0xa0000000000000423288,0xedbc70d40e960005a42b,0xa15818871c7e000002,0xcd0028c08d3a132601f9,0x8ba9205519380a0bd5a1,0xaa15b006fb841029c9a,0x47f402a320ae62574a02,0x6201b6007b806f78b626,0x32b00a9e0b4968e020b3,0xd02bfa03c98195e45a30,0x7e501c7204c82773e9b6,0xa0b4f023500001833232,0x4080d6280808007a8323,0x83862087084b9e2d0609,0xe4d10040a5dc3b701c35,0x807c276151e878015245,0x4b51c48198480b8a6bfe,0xe5e0290832c00000165,0xaa07c800000165c01f18,0x5d8a1ecd13240174ca7d,0x10ba760882893369,0xa5e9d9846f080530812e,0xab7e806370a6d5016405],#[0x75215d8046b03ab4b6bd,0xd0780708030b813df0a,0xb049758983e197a26b42,0x23fc023b46d8943ba8b3,0x4c06e4091f08d5430ab8,0x5dd873c0000042af80b5,0x8078908eec4e6e000000,0x87b037a547e6215e804e,0x2da6034420df60ac121,0x280177821a0012500710,0x5c6e075205ec621,0xae07d6893d880bba76e8,0x51bc4ea7259f825bec0d,0x90273000008b3ac82118,0x1d34c6064e0170aa7d,0xe0aa3a10328e2fc0e400,0x6e2d780767609fb0444,0xb03220e0041b5137e01,0x32835a9326517b66811b,0x2823c6bdc12b902ec602,0x480dd5927122222939d7,0x6b7e1d7f00a3a180da5c,0xf114f02aeb8b2200a572,0x3b4028480000817bc05a,0xa0304000000797033900,0x9b0000188b0a138b02cf,0x32a60bcbc0fdb2868a4,0xc620484268e027d88009,0xec1a468202ac0039010,0x708898003dc053702c76,0xfe0026800000012b838,0xf02718103d93ad0da3c4],#[0x73788bb809338015c0ad,0x1d9a000040135a5f7e1,0x41e05a158a010e896a,0x5c980317037f4239a00,0xe408b62b06c0000085f4,0x1039a768c2263a039890,0x54cc64800602cd0135c8,0x3a6c07fc0331b03b72b8,0xaa19d69daf8aab311d29,0xdd104910054908c5c076,0xc0bd0a03ef03b995e8a0,0x1462c3f813bc8013902f,0x217da4d77833a803f504,0x3da9a80852ea18a00001,0xa08781d5a0e8189b4ea5,0xc205f382b0c0e15a25bc,0x6ad687b18371a0ee3822,0x104af40c4b030102ce08,0x200520adb817e8000,0x316d2060521036829e00,0x2a040fa083000000081,0x485e4da58a5a730e121,0x80ab58c90ec816ca5966,0x3471a6d302cee5311a88,0x748372a1869286c8169e,0x20b8086021c1e039442d,0x481b560834834a2067c8,0xbdc0150826c100464968,0xcc66077341df6830862,0x1d8003980c0b0371433e,0x890946219a042c801003,0xb9022f802f2099e483fd],#[0xb6e181e4e067a838aa87,0x748564033161995893a8,0x94f2057902ef611cf805,0xf802748aaf835449ae00,0xeec8353e12c0c06d0204,0x415b5238600d69016e08,0x4e42ed5220f6a023833b,0x8a8ae2372239c65edba1,0x6542d9702fe82814041f,0x1abb25cfc0408938f81e,0x350d100969a015e84806,0x381c4e8d019ac0d79030,0xb0179000000088496ad9,0x3850b1ae21608027881e,0x802cb824022b478d16e0,0x6e6257506aa70d17275c,0x816464c882dad4398783,0x98a95b427520960e2951,0x49c8215009cf830ac0a,0xf4026e043224c7281cc0,0xb176289d8421201a282f,0x183814899a023b809a02,0x99b05e822b3b889a8000,0x1059004edd851740,0x19814960000000000000,0x28bf2a49810d1d2a,0x954b29d7b12d104cce,0xa7c321c36552aa5ce000,0x8621e240e58dc9a8327e,0x18d000f08a81c0e00815,0xf04a971e8800e9005a00,0x3a703760000182baa0ed],#[0x204cc000040bec82b260,0xb5a01eb860e415b88247,0x851e0a54600000235fa4,0x69ad6000000000,0x49dd82c28ad580000000,0xc0000181c24021705238,0x10e420a8a9a625960801,0xa0329202740040a0d2a0,0x5e792ade8e5ba5cc0800,0xa10000044,0xbe007b500374151e2562,0x3ac808aa01588039a82,0x848343203e184130005a,0xa114e0c860000239,0x180e67828e2964c82928,0x5c24add488adc124f841,0xa6fc0c0083b10892da,0x2dab20b5708890000,0xe078389d569c8c00ea00,0xae840f588a382718843e,0x18300b8108560346203,0x89056ec0b9c817142cad,0x4298181ea06c236fcba,0x3303a380f681707038bc,0x15060d340abf09740231,0x1000d401c001fc60c83a,0x5a9931660ad4842c2095,0x81c4e0889c0e9d81c8c1,0x28ab6a70776c97b81271,0x1eaa016403344051323,0x8aa1ff68678041100280,0xbfb4568400c40378c4e],#[0x440363a0a3a2c39530fe,0x4ad6271126c0703b0811,0x8c6860076d8317e8a930,0x443a316a0e84132ec062,0xb01c8833c6021a856883,0x7e21b9823de068729fb,0x80984045e810c0000006,0x1c02a2207c0038c608fb,0x15fc208a0000202,0xc0051d886ca3ac302398,0x46460776812ca83f9177,0xa0000221bb0b2120c940,0x8760c860204c445b40bb,0x890f5095400000038d22,0xf2065400002061292a2,0x1884c95b400000000187,0xe10a2d701d6000060083,0x6ce000021e30a9a1002,0xc85c9b25301793114c4,0xf7a42c68136780336a6f,0x10067009ba805484cbf2,0xc4503b2e08c683140000,0x83d648eae1221e8dc214,0xa544ae5a2ea6058b8b0d,0x21a8609ed12052083881,0x6c079560e6880b600997,0x3c284f322cba80ce8d2,0xb880ab8493600a2829f6,0x30e0222902f5903fa81c,0xfc2d5c11c61276c815cc,0x178c2d7e0e5e836080a8,0x89820000206d6570ce1],#[0x53e038b357e943cc90ac,0xca0f622168311807b781,0xb6a4ca487de0056223d7,0x1d5900584809c878ea39,0x4e2a4a000004cc9024c4,0x9a5a237729e0e2249860,0x801be60b0d009694cea0,0xa92081000018032e8aa,0xa243ba45528157043d80,0x6d8971bc0fce0805822c,0x24a3285491290e005023,0xf125580c7a271f69270,0x8199a684687ec886fd44,0xe50bd6b102a809002aac,0x266c854b132d02d0b299,0x2866d207c40248603d61,0x81cce03238108f01d,0xa855f00ff60c0f081e00,0x694868b04e0e2c99c4cf,0x3a97062089410463080,0x2cc2d64823888dd605ea,0xba82ac690129040803,0xd82b8f8179eb6b1d06e8,0x1f8a014401378000085d,0x453434087a0062009480,0xbe2850180e4a000022e1,0xc1d5a0047a2aa10aa2e2,0x9200be1c0fc2077ea9a6,0x80f9088648ba08893880,0x6a470d80b898611c180b,0x8be025c9a22bb01d302e,0x968102a76462c0680bda],#[0x16740ab9823e00e7b80d,0xb0f3d404bb9030885792,0x13781bf409b9032460e3,0x201b992b182e71ca13a2,0xa9c1ba70099943db04bf,0x2766e9735030a09d9d83,0x27881d40a30277320a54,0xa914311c0898a061007,0x89039f020a6029642136,0x313a2c09a5cda059e026,0x701adca648888f4098aa,0xc3f8127ca85da31409b4,0xa495ab17b207628a7441,0x5c0c457a595b44a70145,0x80c9c4ec2023c4050e03,0x5a80ace4c8fa75fc48ab,0x127d821fe2d09932c403,0x4c4e66a2afe01ba86ec2,0xba04dc8d40e828b57a1f,0x281d2006f201bae8c240,0xe28136a402d93732b21,0xa02aea18730be4016380,0xdd2025da723a0856085c,0x16a020d001d78000101,0x3e117e00d1c02e280ee6,0x178c0259e253382c1a01,0x1e8b5891fbc6c768a7ea,0x154cb6b3819129036087,0xe0d5041e41433da205d1,0x37a814a422678285c043,0xe81f501fec03b68e5de0,0x58903e580ffe8b4981b1],#[0x90f8006d0845d82ea007,0x24001e40390a49608d46,0x8931085c29bcb877d080,0x5202100001021b508d02,0xaaa8c80af9e172100c,0xb00b50000000004119b9,0x116803a000019253215a,0xe841b808d2472a033883,0x58809fcd073606890aaf,0x76decc4d13b66347dc0,0xa7a15a806518256727e2,0x4b040f040d5f88ab22c,0xa7f88de0406f402d9a,0x3ace237ca382416a0000,0x2207804e28009816c31,0x181060000084652272,0xe8551015902221012680,0xe7e16a601cec8c1b0407,0xad70a76200a862aaf05,0x5aa1e70000101b0c177b,0xadd981530da55808b0a8,0x78000186e524aa580234,0xf9a1156021440a00257,0x50276a02e3c6dbc92880,0x2c5a36b2083e00f3e87c,0xa0a9640c028200000061,0x3fa0cca8983481e1919f,0x84bfc42ad1548605cd01,0x8aaea16047a924c80001,0xabc881880a400ba3e19,0x92023782558d26181280,0x34a6051f83060075100c],#[0x800004869a0bb400000d,0xcc7873ad08780000495b,0x4a8068262000008361c4,0x7b8003c021b69d5881e7,0x847768623a093e125921,0x20829d20c458290a0649,0x705837d8207e01e962c,0xf70bb880bb00001c71d2,0x3480000009710000002d,0x917b2a08a800c6a2180,0x142a2d68000182822a55,0x80001aa32c07ba000060,0x6a000008b21c2ecf06cb,0x2e3d030c506d6247600,0x110256809e0893f22562,0xb5c8c1f09e988957408,0x3a4e17b71f224cb80f70,0xfa0000140ea00000331,0x8129e8299821ab04578,0xfa93ab8000101c564b9,0x551c60000001f5b4a329,0x7b8000080e0a0d492456,0x42f2c00a7036141e2304,0x4c00006851db17a80001,0x3c550e700000a568888,0x460a3713310b6c9814ed,0x5c1800008160a82348ad,0x781810084d0487883fa2,0x1000d80000a56ea066,0xc09d8221653262020f00,0xc2800000000000008261,0x77520d0b077a0000121],#[0xea4105e4e45819b54c3a,0xa69782fd8479201e6c2e,0x940468053d2b6e51b172,0x621ac238093ea0684870,0x980a0c01b482aba04a80,0x69002f600000817e310e,0x205fd807400052035342,0xa2aa08d2da962ce60000,0x818cf018fa4cfc145ec7,0xe6506fc4091034143440,0x83f200006068e08c8a00,0xb41d9a94e845951247e,0x38e85822c86007d3222,0x301cfccc5a000004eb9a,0x800116661e02813c00c3,0x6014d43110816d02a76a,0xa781919243dc1e21256a,0x50700005f839fe0b0fa1,0x3e025300000008a22271,0x85d62bde936f610,0x160d5b08cbe08ed0b9e0,0x78840938b4bead720cf,0xa80940030880b7a0aca0,0x449a0fc288bb24cc70eb,0xc2e67a8394ae5684a122,0x20c038082c26118e40ea,0x352c0a218f3c25df208,0xe4a6c0a06aa0b28c1b31,0x47c570d211cd914e685,0x15c7e02bce04ce09b22,0x32824cd1828080000016,0x34206e918609ef002fb0],#[0xd2e000020c6f86d4e3ab,0xa4daa0b6d4354e46b470,0xf48117550722051a26b9,0x822300000829d8000080,0xef1182a1693002001430,0x9e68026a0ece08b3a2a,0xf2127184a6c08e582c8c,0x89080000000020279816,0xc800a607709321800008,0x366ad9fe1ced0037e052,0x55262a04a090e800700,0x60501da89c7a46100000,0xc1260578b8e5ea09bd80,0x46881dd43b0008c48647,0x2693094e60c9d04e1a1a,0x60139a80024867b0344c,0x3b2622f90230a9c8b018,0x7827c68771012a808890,0x79e000064edaa32700b1,0x4970c811de1114000060,0x56411d5177ee2a8d0a9a,0x83960243506e0000121,0xb98f4da90d7001200609,0xc0240000629aea047c39,0x20490000020a1a22dae,0x918217ee0019245ae000,0x901b96cd47a05fc076e0,0xe4da356a3c5622688132,0x409d28345ea864a6bd20,0x6cf1b6d3723e0492086b,0x888761997003e65dee13,0xb0a19d80df58f99839af],#[0x2c7fa21a1041bc300a96,0x601cbc33f0355a8097c,0x1cb7016a00eba2d01837,0x501e34130f01bbe02e90,0x3be046f891128608e4c9,0xd8a04ae80000035600,0xedc908e407421c8f80e3,0x82964031e0000603d50a,0x1d8486807ea2237e1741,0x62c8243281e60000227,0x6c29c533140c20002082,0x4a209dbf23591016601d,0x602d6e0868916940b82b,0x7f10288c2e910219543b,0xe819fa29a007a982d325,0x7e22e9581ac20e1b0b59,0xa5a9e2bf50663a8eba97,0x28a9528858b8412416c9,0x29c897b8603df865b001,0x601b2000022ed3a1600,0x725000010413845d8000,0x92e9b00554299ee169fa,0x473838f096c2c21c6180,0xe16aa93a260720c4c1e3,0xb9143b800bfe0758126c,0xa6858123511a92bde782,0x76ae60a937fadada027c,0x617936b800018a9900b,0x34c24e2370f36c68957e,0x592287e9200aca54888e,0x38887aa0e7109242bdaa,0x6a1832168163a5c840cd],#[0x20d442a04631b180fb49,0x2308923803480330c0fd,0x89b98880c2596a9180a0,0xf004cd84e9602b6227bb,0xadc0217405ed006b824,0x4401775074e084a01b82,0x7b5e8c52818e6201a81f,0x882336b0a28105d51cb1,0x21a0a9e01aab018ba0d1,0x743c10aa000e79031522,0xf802a5101bc44df00780,0x88a909db6126931844cd,0x7b12cb024e4239220b46,0x130c8c2980cb2029fe92,0x5e20f30c910a562a3650,0x2a9cba86925b101b0534,0xf02ffca68304d5e99710,0x3d1878189070308d4a7f,0xc21568b3ce869909c3b0,0x3aa10f2c0eb801a00b61,0x81ca295aa8a7b8053d00,0x3603bb205b6000001edd,0x3a3017a40bad8373c18,0xe800002957429b3829c0,0x12680000029618ea,0x202db0000183a5000000,0x157c2d5407df840e8052,0x418a2256d80001a20929,0x2400001809901d75828f,0x1d0a01e1839b2a7f502,0xe0c7af45de6a021e42af,0x9378182c024682c1448],#[0x22c0a819c04c91249b8,0x76e4e4e01b022a90000,0x1a02221ab140f7800000,0x100f1807b10398a014,0x6da27246030d036600,0x8fa8074adaf819a30312,0x2bd827910a9021248b6,0x6f01ce20570805e00a87,0xbe8841fe86e6a302a20,0xb20deb44c260da4a175e,0x99d640f804b78000088e,0x33094806730af520c26a,0x26502556258f827b80e0,0xc0b58109d4061ca020a2,0x982014900b0a11b9038c,0x29fc0000080bbca07482,0xa88102e845a41022063a,0x119206f7a45ce000043a,0xf8a21a085183d3142da4,0x1b09b100000409bf2b8,0x8010d40dbaa25ee0c698,0x98e0c4a60b490760618e,0xe8df402c6a15d40088a4,0xcc237e2035bc0cd4020c,0x412a9b560b3020be3c4,0x638d17423ed880fe8a6b,0x29580000639b44344ca8,0x48231e40f9e06b200002,0x11e4034e0a7b00000a36,0xda820a853b803680c750,0xdb1b06e726be2925,0xd039a03a180001135880],#[0xf7e03b2000031bcba56c,0x8349e466100412089585,0x860396c0baa085be1d3e,0x87588954a2957812be03,0x680000a1c44072500756,0x18fe2a150b0cc2361a1d,0x480c7206e88d1e0183c9,0x4ec00002064b0583a8de,0x406588a62e216c225050,0x5c8bf10188941d7a212,0x4b44ca380654852c21,0x3e8524b31fba6b1a2b54,0x15b150e888e1aa5ece85,0xce04dd014c80d028ad94,0x1264055c83b4f0b67833,0x5032da09a90a8c80675a,0x191a267e4ea8822e006c,0xe8ed7821220bf080d091,0xa100000225d6147a84af,0xafb82a48031f40d38a4,0x738b6c00001889ca3d12,0x10a1c3428037fa6d6400,0x60496f086a000008246e,0x92e57920af2e9257021,0xa000020d7e83376a52d8,0xc8d85912255b04c1422c,0x10b82c9e081d025f21,0x32201ca83f42a2c4245,0x81fe0091392e6213c281,0x67a34bc61fa295982d34,0x16c5954a0a8b6815b20a,0xc82a5b8289c26080b2d6],#[0x59c220b13afc172d829,0x100d28096b8b290268d2,0xb7127260000089be8a83,0x4dc95200300000839c00,0x1a5740917f0dae,0x89e3000019332812b000,0x868326e8113836800000,0x6b80054201c9939f223,0xf69b49a37280000177f6,0x494e811c9243a0187406,0xd247dc0d5321c701abc0,0xb4b07712c2051171d00a,0x42a0142fce00580b9340,0x42dca2172d4c390407,0xab5981076000040ad000,0x22c810865e2d8a,0x2366000003ce98c38000,0x6402060125e131a00004,0x34fcadd6a6d6e2d69a2a,0xe2957a0a5f801380b748,0xc8a01f3416b0a7a7a2e7,0xc167a00000000007708d,0x10b14aa8580025,0x4206078e00000240200,0x680000703bf081b207b2,0xeee000025ded883c33a,0xf30d084073800012299e,0x4f00001ab7f20ac5205,0x3c4c9800000000417988,0x86681d152221031c4cc5,0x82ee240dfc80ac87b780,0x26f701d181cab800b],#[0x837bc0d3a000002c7a00,0xdb81b302382000000c1f,0xb6aa00004158780d5a0d,0x40593a54980000039ce,0xbb0405882250e203c000,0x420578000181efe0cfa8,0xb500399602141364612f,0x28b55a381a80b7833368,0x4038988a8800008344,0x8080083e182d9004f800,0xa9882a8a0cf40ffd130a,0xeb486ab8012125c2808,0x481c83871084d8da0a42,0x15cc03ef8eb000000819,0xd05a96021901e9e4aa88,0x472d70de0969a5a7a894,0x220ac924320712000060,0x44c87a682f140b92430c,0x8863e02852db00424209,0x2812fe0cef028384d4b,0x4230c4cea0084cf1da06,0xc20d0e81da4067800002,0x1131e000020edc03a,0xda5a8ca82e00000927c0,0x16b26c188895821cab6c,0xe45d3811b04027062680,0x6a81e43c595a018f8217,0x236e0420b00b221d9302,0xec0a79912fc090060182,0x1600253b439e035d006,0xf496c803ba8a80f034c1,0x6350025682f7ad26e897],#[0xc0000412a3225c6dc900,0xa359365000000062c45a,0x2000a007e8138026dae0,0x37a147784068a0850010,0x126743a00000200f243,0x9705da0000081a5c972d,0x11d72a17e80938180012,0x20e821b08a840,0x8bca05f48f4c8807e000,0xd0051a09a4000071a0d8,0xcf640ed22dcc8576e02f,0x13a6ba0b8c084e000074,0xe76126e91c20a8618003,0x88b725e04025100e0784,0x7c89b5505e2a020712d7,0x889601010813e894a64d,0x8e1dcaa43c8000000004,0x1ee8042e0000012ea0f5,0x902030088e060d22a,0x18aff4171c22e80051,0x489ed8241e01f703a0e0,0x4b00bf98012e85eca948,0x809de862b08c8647e702,0x3a2956d0cec000041267,0xb07f08ee2172a8061647,0x2c097400000000030928,0x2a886240c1b2428e11e,0x2257e00c9381726155cc,0xeba02e40a0e181898495,0xa2dbb8168a11ca165b62,0x90800008aa6889150f48,0x8ba2416c0275d0000101],#[0xd9138664cd39373c964e,0xa26280da31b718804c1e,0x98102180ef68dc6c117c,0x15aa0378801a95c7540e,0x988d140da9810ea9ebb0,0x26d2398a8d4802d124db,0x807b9847f4057400b4c0,0xb7221488083743a484d7,0x207a40ec280ae22c2989,0x52080560d9ca5a008574,0x1cad0306c11a629940a5,0x8c80c9a653616bfa3ba4,0x140e195d843800001139,0x1405a003b981c6829898,0xe9d0423ec416a3890052,0xc4f8f3aa05cb08d904,0xd3e00aca3742a8cd214f,0xa2d8c89840a254019086,0xe62370085430b38ccd2e,0xe49828aaa80ca3b650c,0x78247029ff02c6221860,0xce426fd08b4a05db028,0x4900da966c000030cef8,0xe6889f0226c4a0dfa95d,0x818078174209d1916702,0xafe04632f6c20e38015d,0x245609040af160e5481,0x15288b44023ac8254,0x92e015050ce80765800,0x926263276042cb381f6c,0x35b005c0c3122c5e3834,0x6939a6019a02ed08aab0],#[0xc6b837e20aec135aa899,0xe080013154116e0391c0,0x1f016cb84a40245a835d,0xc699802d180e620e75c2,0x620000008f501cd80000,0x2c78836020c0602ea202,0x7a19b2802a8000126856,0x24711848224f0085a825,0x19284804d508694030f1,0x188c6a22e4a25f4009,0x743c402eba08e30b1d00,0x46058d116443d240000,0xa165495b18373609e521,0x9f03710006fcdae20735,0xc318366e134caf7b803,0xf8000182cd0000000006,0x24b1216802fa810580c,0xb038320681022ecad680,0xe48000009692933,0x882ecc0e629ad5137e80,0xb0e002400006152bc886,0x202bc08b78005d09,0xc3a4282152d025b22044,0x1d08818a89d,0xb40060831ce17a210918,0x8c260a62803340470046,0x8000042b4a2001eb6ba0,0xe8082a50000101e12131,0x8017e8322a0116a1e304,0x3b69133277170d2b00a2,0xc0f0a18310236005e18f,0xa72042b014142ed8],#[0x9d940000017740aa3800,0x380000000040cdb897fa,0x1c060c088109c08d0029,0x8239360eaa93b8000008,0x7eda02c4044f950c4172,0x401ce055ae07f78a7e20,0x28bf4863fc9652a059,0x30900001a235a141000,0x924a1068236132780b8d,0x12d82597495280000423,0x43718d0eac22b300a7a,0x17fc0e8c215ce0a32000,0x9a0922967144cf2173b8,0xdf685b1801ff0075a237,0xd01ca80dc8082c218525,0x1561dc6895fa1dd0c20c,0x31e68e60a2a5416a901,0xa60395c1e63000188545,0x7614d2f00dbe9d,0x5e0299237a62bc6a17a8,0x1f5403c5008aa354513b,0x2cb601b4e1edb8,0xb21a1a184a0588b8a496,0x412460142c0ea388b5a0,0x43c1739076c20db408cc,0x8254c0a6b812060d7ac3,0x6a0261696c421a5a053e,0xa654a709800018130c8d,0xe80000000024df200000,0x69ead81f3c8987809,0x4837b60d1fa6c2a462e0,0x19f886f28d71824a8076],#[0x339a92a7e0a2f008220,0x42b8d22104045a8eab,0x4d1c03f880a9102d600,0x72095c20778867880063,0xa57806caaa0200d,0x982af30ab0c0acc0d110,0x19022564935e00001a5b,0x90f3be45a12561809ea9,0x93e009c8130a27a5e0ed,0x8a528886548159825288,0xd8a9b54849de087c0d50,0x51b5c533f30cddc2,0x3c8df963043816aa081e,0x24ddd076803598b17c9a,0x38001f0122e1cf2889e2,0x5a9245e229fda1d7d893,0x7800ca024e0d4b24e432,0xc5800b0003e2135788c5,0x40d2e80baa89a0900d42,0xe788161003d00cd78100,0x8345607e042f860bb602,0xe600002053981a429d93,0xfb8071202be8bb942a,0xca194d81c1e8568849e0,0x2e148df8000020015a9f,0x4000002554a4cae055e0,0xdab095de15a74209209b,0xc27be8457100494e99a0,0x1802c2f0aae006a700d7,0x8388a23b69547a892fc1,0x66a1cce4e348b0b48704,0x12088b496584345005],#[0xe60b380978f00e882676,0x2ab6064c936b257a003a,0xca11791b648175297112,0x27d821e0871f93682098,0x211651391c09d6020084,0x992971680ad64a1080ca,0x29d8005b5a21f1005384,0x1a224a609ac03170857f,0x818d8b7082c9604cb208,0x2a9ac40b7cc1286036c0,0x24a00dff86f740a4903a,0xc0e90b6d902fb808128,0xadd8603800000646c1df,0x42e730232295db02de69,0xf362164335200e5c865e,0x2490000085e5b41b0c0,0x690b9960ed591c101974,0x4ec01371000000000605,0x7101dea167aa53f48788,0x20525d5905c3c2a4525c,0x2000009296808be0c2c0,0x79400004b6e288b6b000,0x4890183b1a29632b8380,0x1b6cc5750f444729030f,0x9112972b82dbc02cc0b,0xf8b3d619540b5680001,0x81eeb095201060149c0e,0x8a022483a620e204207e,0x65a42bf7a5afe172f88d,0x421510f16a04240,0x100939e0c4ccc650000,0x242151324c96c08df760],#[0x72c0960006342022a01c,0x3964024c8a8c408c5a7,0x7c806f60ba684f00061a,0x1e188035e080bc0eec91,0x8409dc0000086eb007ce,0x36a00d46000000bbfa5f,0x60abf1]]
set_option maxRecDepth 16000 in
def g253D10 := limbs80 #[#[0x54510541105091048510,0x5d5105c9105951054910,0x5412050120dd510dc910,0x5c520595205512054520,0xdd120dc5205d5205d120,0x585505815054950dd520,0x5c9505c5505955058950,0xdd950dc950dc5505d950,0x5d9515c1515955158551,0x5c5655c165dd951dc151,0xbdedf9fe77dc565dc165,0xdff7edf777d7effbfafd,0xfabdff7bddf6b9fe7b9d,0xffffeff7fcfeffafdfef,0xacab018349ea9173508a,0xc216121081c1c6c59606,0xa12b72094b90515482c2,0x11586095bb04a5d828ac,0x2575013ba0095d002f0c,0x3820d3b90695c834eea0,0x860d3bb0695d8382ca19,0x7102c3825e001270c191,0x202c2101e1460f083058,0xc3c38a161c53aea28585,0x2c312160890f0c387821,0xb116adc4b52ea5595228,0x216add0b52e85c5542ec,0x16add8b52ec5c5652cbc,0xa75d4d0b0a917862cac3,0x75d4e0b0a985814c2c39,0xe1110f0288787382c39c,0xc560b0ca0581503c3221],#[0x9d72cabab725a2a92cad,0x53ee8a858674eb2ba160,0xb02f396560fbb2a75d9,0xf00c858678eb2bc1611e,0x2e2b8070bc0382e0998,0x3205827c2c0be1e09c0f,0x858690eb2c8160a44ac,0x87808c7c1c64e0638703,0x581a02c04a8e0e34f031,0x42082c0523e0e70b0540,0x60b4c105a5c82d2c4169,0x32ba0195500d30c1697,0xf2b10795083caea06565,0x2c30795d83cb041e5720,0xc282bdd415aea0dd5207,0x90975884cb022198704c,0x8bdd045ae82495412eb,0x8bdd845aec2496510dc2,0x661c45b0e21b8610cc30,0xe1065ae831b871174388,0x1065b0831b85196ba8c6,0x485f0a32d85196b28cbe,0x537042e581174c00ab59,0x330e2ad87156438b25d4,0x70439b87157c38aba1c5,0x43ad821cdc30eb5d873,0xa56951297c30eb61875f,0x5e9812f4b897a584bd2c,0x69862f4bb17a610bd2c8,0xf74316ba1995c4ccac26,0x76316bb192594c370862,0x7316c3986e18c330c62f],#[0x3d6ba9e6e1cc5d0e6198,0x4dc09ba600d5aca91b85,0xcc31ab5d8d92ca6d1643,0xb2a6b59505b0e69b8634,0xa9c6e10e370276980396,0x9c661ce5b0e72c873a4b,0x26e051370e72f8739743,0xbe0515b0289b86456bb2,0xe1915b0c8af84456c222,0xc57d300be9725b4b8acb,0xd73704baf725e4a92f95,0xa370ebae875ccc3aeb61,0x92cad1b82696b9352549,0x2c8aad6274dc334b5d9a,0xe8c6980624bb2b25d159,0x2dae87616c3b1261585e,0xdc9656cdc236b5d1b370,0xcb81664c0b26e19b5aec,0xb81735c0392e0999304c,0x82717c0b8b605c3704e1,0x2896b945958625f04e2d,0x84dc344b5da292cb11b8,0xf3c0c66e02397010c980,0x5b84cbe0235b011d7838,0xb94c6e0665ee332d719b,0x8d0b5c68370532f72996,0xd0660a85ee541981a17b,0xebe0a85b0542f81a16c0,0x66029af073e7719cdc04,0x5d41daca0af80a56c052,0xd84db0826d74136b209b,0xcdb042ed87136c309b5],#[0xcdb0c66d76336c219b59,0xdb026ed853f6b29fb61c,0xb0876f813b6c09db618d,0x28ef873b6c39dbe10ed,0xebed825f6b92fb6191db,0xc6d866b6c135b589adb0,0x6d866f6c0b7b61d8dae8,0xf82736c139be05cdb02e,0x819b6c0cdbdc66dae336,0x29b6c14dbdca6dae536f,0x160001b6029db0546f8,0x9401ea066014603b00ac,0xc03cc0e2835e0bd82ae0,0x85a815504f012b845c10,0x7961d307081b00660182,0x7c24e08e622788441fd8,0xc2c18ac829a0a1a27289,0x31d0c262fa0bac2dd0b3,0x878ddc3630d563448cd2,0x30f563be0ebe3a30e523,0x90e242b104c4030fd23e,0x2c649a1226474117644b,0x7450913e64e893644c31,0x857c15ba55b951e52d14,0x5f797865ce16ce5a3963,0x63193c63f989a617182e,0x89ace69f1a2e67c99c26,0x9cc27169c0a6ed9b6e6c,0xed07a31e3c77a9d72744,0xc82ea0527f89f9a7d41,0x68bfa2aa892a1c685e21,0x944a4bc919a4128e7a34],#[0xc126d0995a61896ca562,0xaa90ca20a82e9f7a76c9,0xab66abfaa9ca8829c2a5,0xd48b43acc4b21ac2caef,0xeeba82e4eb86add2b66a,0x4c162ffebedaf74bc9ae,0xc7b31aac593138c32b08,0xdbb338cbeb2c2ca23242,0x1b4d4d203420cf833a8c,0xb6f0da6b64ed7c35a4d5,0x900e313866e03b7a8dcc,0x44ebcba96e88b9e4e5ab,0x4f30bc6af00bbc6ee4bb,0xfb93e5cf813d90f543d0,0x27404cffe3fbafe23f46,0x2c27b085c1a105640ff0,0xc4550fc43a50d7c30b0b,0x60f168c55f14b4501126,0x2f1f2c75f1c446b71934,0x3278c99d253c8ff224c8,0x2f14b652c84ae729f4a2,0x78cd8134acccb315cbff,0x54f4b3c54edd3a14e3f3,0xd121432508f40bcfd33e,0x2d34a4d25748251c545c,0x89514d3f74ebd3634c6d,0x157e55a1558d52b530d4,0x5fdd7b55d9d6f95a8d66,0x8f59c765a591d62b583f,0x2dbaf6dd5b1f6b75a956,0xdd61744dcdd7245c4f70,0xf737cadedd7a3de3376f],#[0xf3865e12d83060657f65,0x5905e3ab8cf62cb895e1,0x99ce61d96b654b93b648,0x34687fa0867c19d566eb,0x16ad5a9c69f7a606925a,0xed51b3bec83b00ebafad,0xf59bbbee9fb906dffb6a,0xd3c53f0e7c1e7035bf0e,0x1ad178580e27287c8cf1,0x887b0a8c0fe371d8d87,0x41406205c20c7a16168e,0x26101e0d8db043813b14,0x98a137074784511138d8,0x42a88f0c548814076510,0x691e030222520370f821,0x529c5c40bd0e95050892,0x810ac1202c26890a4222,0x6a8545c8ac266d211414,0x46270330341a811ea245,0x958924922a9042223074,0x350c37618750a8006c00,0x6a588706aa8e5ad02412,0x21e09a0a2b12008002c2,0x42c7a0d03520b351a0d,0x80733021d19a07432486,0xe5040ceea336108dff89,0x71033771a9f4819f3f7c,0x24cf1ffb81060492f0fc,0x2673d08211f0ffdc2c08,0x8271b581d7ffaf014081,0x3afe7b850820947fe42,0xf90a09ef3ff2010527c9],#[0xd0468f1afc3640a1341f,0x68dfd7194da0256df8f,0xef2a31ad402577eac48e,0x513b992023cefa83023,0x20e9bfece400acf7efd0,0x37331b800095338e6041,0x2e29e6522a1a776f0012,0x2475fd669008edf79843,0x533af59d980485f3fdb3,0x20243932613a7f8fb242,0x4eff7a00eff7a00ef67,0x75228122bf900141f934,0x190e658ffb804040d0bf,0xc8f31c3916625c0d478f,0xd9143a601cca3ff7884,0x42516781a893dc3646df,0x8899147c62b889024a8f,0xcaa3d0945d51e84c8fb,0xc8b3ff08dc05493dc04b,0x76439988b8eb186683c6,0x310033efe3dc2501233f,0x80c113417f2480a03fea,0x60844ce3aec6491c3f04,0x3e304665eea2acca1f81,0x8dbebe02908fbc894119,0xa3df0d718000d2be0290,0x69fe312411cbf4a10059,0x20242ffd206a35ccd82,0xa801a56394251b2ffca,0x3a1b7e8448c23c63ed6f,0x953ff082819a1f99800,0xf004a00673fc8d04e78b],#[0xf7cc8d0527f91a09cbff,0x387827737c06a3b804e7,0xffe6f208e5fd400b998e,0xf9b11048cfd3112019f0,0x17fedd41207e6c4411d4,0x6d2fe2068a8f0ee20679,0x7504a1e7e2310476ebc,0x8b4636c78e206b5999f1,0x7d243a0913fada310480,0x2906d890358fd76908d8,0x135291cfe36823369b63,0x495fff1e0080204a03f8,0x8667c1b29cbffd780a30,0x214144f5fcf70a220957,0xfe1cf029192309b2f3ff,0x9a0e2488d7fd84c95686,0xf0e274aafca8dbca27d7,0x48dff99dc28620132c39,0x33e874a569227d46a56e,0xdaf1bc00481c5eb30209,0xd2d1a6c54acda1194a67,0xbad20cc9350e762a32ff,0x335c8094147aa22facf7,0xe7ef2a3f8010096ba9f2,0x9ec7f6cc9227cc5f8c11,0xcd002e39ffe17d30124d,0x9f1f0a332484fc2adc84,0x3ac24026cfacf5810049,0xd3f02ca0480d1b7d9f02,0xf2040123791fc9002012,0xcce5e9e511c1001a67f7,0x74cb2bf821163f836924],#[0xcf700a3cad3c91b3fc68,0x48f78b08662cfd0265fb,0x8023afde7b8051c28f54,0xf178219cb3f40987f998,0x27fc00411ce7bc284f1e,0x5050be6030f3fae00012,0x3b7c399f2000069bfdca,0xf8010463f9e7104efe00,0xfcf3882799ffd4000903,0x218287ff90073f826131,0x8039fc13098fdd01354f,0x7c150843d4e90c14bffc,0x148cd3e07c3c064303e0,0xbfe7cf0c39213ffc0903,0xffea102333cd54ec0690,0xfdee226488fa740399ab,0x21f237124cd51e84a321,0x99d3c5a03c41134c85ff,0x1e7c01aa19a0bf4c1aa1,0x1bfc7eed5125477584cb,0xcc8c3f94dfe46d8804d1,0xa02ff426323b124c9e36,0x1db0dd126706f6c37a09,0x9977d9e44d86fa8a490,0xa48daf62a11aca4b8eeb,0x1cccd84258651e718c0c,0x821134c790e132c7d3a0,0x8d6e30e104ce5fc1b0f1,0x44d0597d1293ba60844d,0x6a2461c2099738e30e08,0x9f6e814338edc214683c,0x1859844d31f2fe44a520],#[0x9523aff31f2049203bf,0x282bc8fed5398335083f,0xf1bf992471bfe3790201,0xc7f05f0804898f90646d,0x2587e64384cd31f20491,0xad27d0148ea69e7b8889,0xa89a31a18fdf8d1c2804,0xe888804bda730351e0f1,0x8052095977425187efc0,0x246fa55c0521247ff1ce,0xf8722a13881a874ce268,0x20141a03f1d680100682,0x13ffd7042e00680fe21c,0xc3915ed41217f80c8012,0x3491afed04518f1da08,0x63ae232c406973f10ba2,0x2095774cd414dd23709d,0x2819ee87b04ebaeab189,0xfe9e59908209a823fc82,0x7282848d62fbf000e876,0x4e674ffe68ef603461fc,0xd1b1bf501183f3fd6a,0xe8c688d8f80c9196c7d4,0x48da7b1a8d9fe1e0e655,0xf0fe39425277fac72828,0x9bff875c015655e25146,0x3cf81140485ff8ad0023,0x98fcff234141fc092050,0x6b80291f024846be75e0,0xcc81b029bfc6b8029bfc,0xfa03a64126ff206c0a0f,0x20693f82613176cc261f],#[0x1828a9e1827eff486602,0x910344f2fe304824c7d2,0xd04842f79032a72c38d7,0xb0e36870f1034acccf8d,0x1e31e840cbbff08c411f,0xdf87bca6a41307da8a41,0x9d051df18b5890a40d5b,0x81af4c7dac1a4251ffb5,0x7764a68555fc6aa90191,0x6bdb240ca3fb0d208e7f,0x12aee9e84d23f029a412,0x1947f0e9046d39eabb4c,0xce08b3d576982457b648,0x744910342cefc1d04755,0x49ee1b1b63a4881ab3e6,0xe39fe1b411c41ac7c6d0,0x4aa39ef03281cff0da08,0x2f2c00926affd2d1a6c5,0x1563fd7210ce3ffef1e7,0x4a100d5bf9ee470ee2a5,0x49de677e040127bc1e44,0xce800801a87f542b9e30,0x31fae11dee4226a8ffcc,0xbfb124a04ff2c271584d,0xdf907723a001a87ea4e3,0x8f544923fec175a8a495,0x4d2bfb4a91aca4a5f9d4,0x80b2f04ce09fe54a3438,0x69efc83a1ca02006b8c,0x6e63d424965fc1e1cc20,0x29250f1b98f50924ace8,0x248dcc7a849236898def],#[0x8e09cef514933b4ce3a5,0x1401aa7f5ed64cf02c25,0x9590569034b7d7e81cca,0xc0d3bff2eab40560971e,0x2fc3bef60a4bfc068a98,0xc04cce36f813530d496b,0xe3864305a3610e6f808,0x73ae8290d00b38d63467,0x3fb85e155fceba09ef9e,0xa6a412c0f1f01611c8fb,0xef2ed62429034ef7c7bc,0x1bd0503fff1ef29a904a,0x81a6d94feeec87a16dfb,0xeaa0609c136bf8d50431,0x4829fddd90f42b1ffe30,0x24f1f1b41232feaba70]]
set_option maxRecDepth 16000 in
def g253H10 := limbs80 #[#[0x3004010880002443,0x3003038050000407813,0x43b008200704901c0a,0x1d0540002c0700014,0x40009c010600500409,0xc0141c4020140913c06,0x4c77000000940c0a803,0x12c0200c1c0000c00808,0x70040744301c0000801,0x140601c110300101001,0x8060440102c280000a,0x7004010000900019,0xc003020130b84807409,0x2051014020000404c10,0x1941e5a002034050341d,0x605c140580001000,0x3804040011a8400000f,0x15401004050000101040,0x480400c0408c0003400,0x4c0b0086b0081400002,0xa005008000140a0100b,0x1ec090240a0946800c11,0xb008040186400001,0x80020202b0141002c08,0x1c01010040200300004,0x4030cc010182f00c03,0x500d0040d1481c00810,0x20020781b070090e42e,0x440a0bc050ac040cc00,0x2c0c000140200d0b813,0x2404004010148600420,0x17014000880b01018],#[0x1058010340f00437,0x4400b0140100c0003016,0x8120181c0240203400,0x40d034020340402000,0x10010e00002c2c0a811,0x740c00c010480706c20,0x411000060001600040,0x807d0681302c0600810,0xbc342100000c0e0e005,0x8010045d0042401804,0x180b4442b0080e,0xf43403400000010003f,0x1c0c000020440a0ec0b,0xd0360f01b0280301c00,0x4010280a10c0603c4b,0x403000010840200000,0x16c1b0180d000000041c,0x705c4d0400002802,0x6c00060051200201c08,0x1101c02000000c006,0x201d0000703c1c01807,0x1002201c000480c01045,0x1c0a060010000601c56,0x306c1506c8f11800,0x280100406000240181a,0x142b00c000080f08406,0x8053ec0c01856,0x4805014310205805823,0x20040181c0002305847,0x300300c2201c0f17415,0xc0e0000710c0919800,0x64300c80201000018e8],#[0xc0a034041c80001c2f,0x724e01c010104b00c00,0x28002580801c0000008,0x11000034060603325802,0x4803038001640700c2a,0x1400c0f1281100415,0x62034102083009015,0x80d0080d0282600048,0x12c250083d00c3616008,0x4170000603c0608c02,0x5000220a46c0487e,0x822000000240200800,0x8c5a0001100c2224401,0x2c0405c1d000920c032,0x4110010100a00000,0xc620e00a0002000812,0x6c1a05c250182b00007,0xc7e070080182600063,0x3024080482106c00,0x78070840603c0c01c03,0x28020580300417064b9,0x40a04c060340700465,0x405800c310080511400,0x1807070060ac040d008,0x541e2a0283302217804,0x2b02c04058001bc70,0x141c02c020600a08801,0x14c1d0382b108b90cc06,0x1b83c000030080808825,0xa82a000230300b0dc00,0x78011801e2000600011,0x20b400a96304a200020],#[0xf85c0100800c1803000,0xc130000340030407,0x37c020342d0f80008814,0x100121980e00c0100c0d,0x48560482b00c030154b,0x2b53501c011441001477,0x248715825000000e40a,0x3006004d20101f0c0be,0x390491e8130842008c02,0x801b04c2e0bc2f07c01,0xc08020020000005c00,0x400a1500d02c0b0a862,0x7002008041748a07c4b,0x4113c491500900069,0xc1001c3b0800403c0f,0x4340240b0c00502475,0x30010dc310302c36c4a,0x4511b0a0080800001096,0x5f0010306c0848816800,0x24c0716c8319cc805401,0x34031d40500c1067848,0x2842b00426014870153d,0x246c000a0011f43d,0x463fc00004082c18,0x4244f2000000000c1048,0xa1a82b6214024317c01,0xa000010126e0a8724a60,0xb40486b4000000002455,0x1255098b89a599a0a810,0xa290367c2e7484eec478,0x88f2432cd84256400aa2,0xc001f2b2ea14f21255],#[0x10690000105a544cb000,0xa9045800d041522014a8,0x481c03890117d00bd520,0xe000000000209d5036d8,0x5644018000040def0a7,0x6050042a7b00d41209d0,0x6ab0a84e379355cc8918,0xc075301c8809a305ba05,0xc98625453dac546c0214,0x8144602a24524800,0xf4000080ca2016500000,0x156bc89b784f5513,0x2533c78c62895ff821d0,0x5d560bd8000084cb9010,0x4000000aab028f409eb4,0x7c20ae6001288cf7406d,0x826951403c09b011d861,0x5b4420e02a1d727949ba,0x4ac0841303b80558943,0x2397c04c0000000002,0x955e15de00002018584d,0xc47ef018880979a2c78,0x4b62087c000001553149,0x87a000034346013210,0x8aa0a7000a50000004b8,0xc94609db00b8382e780,0xc2806520487410c30320,0x5df004ae0a1c4300e05,0x580000000000087905eb,0x49e442e583152247a40c,0x91942df888cfb04cf8,0x14702dc7239041478056],#[0xd006e0480b4ceac56f31,0x15301068225614a248fd,0xc8ccd4841c09c8160305,0xf54021910a1014bb03e0,0x4332a01a1a2ca1020b02,0xa804b0d01a013349152e,0x910f0094105ac00d8411,0x8411880d3d8562c01a48,0xcfa533bd44a1c5200021,0xb04a0c02d800f902cf98,0x4ee220a00cea14ef237b,0xa32f9859f826d302dac5,0x1580cb845518c0cf5406,0x3be8cb3325ed4849401,0xbf53c742f0f15ef82a8c,0x3157700003057e003,0x990fe4140400474117b0,0xa4000000000c173205a,0x285fdc00d4000054ead8,0x26a0175d046a04ea9093,0xd07e8252857,0x4a03480b42411ea014e,0x3730529d0aaa401ee15,0x1054d00000047718436,0xa23028a121890822000,0x4807972d41000000000c,0xd08b60922a8b2225b,0xb40ff449d8097b8067c0,0xd242d3f02a4c0000c57a,0xa486a4fc07c8000008,0x3f016efa318003fb859b,0x41010000025fe0126015],#[0xc90348407e40000933d4,0x155e016350ac51275897,0x50000008860000224ed4,0xfca16540000d33b8281,0xc453ac92de04ab10ae21,0x35e0469d279c057a9155,0x927e4000080d900000c5,0x3d000000000000011398,0x8a9137c303a3c0de203,0xff09ee000000000504cb,0x4465405f025c40000808,0xc00000000094ef443339,0x60a0304bd08cfe53b,0x3052d101fd14ba82b000,0xb9b02190ae72052fc131,0x44a7e200381765132106,0xb6c04914011d8bbd4cbd,0x89baa726302636090f01,0x72245e0000104f29127b,0x1054a2a784e960026054,0xa00001220de726f8cf10,0x1169457e147c0000009a,0xe409e8254c0000407820,0x32bd00001203e012e,0xc008000000000314ee00,0x94e5b149840848043f,0x4958a2df70000000,0x225ea84d592b9ec15bc,0x16da45440441724c9000,0x5c117705fe0000009f88,0x61c93eb0a87517be00c,0x600bf0000303d2415f20],#[0xd1c00000000304b2807a,0x40a64000000001049580,0xc18151510000024cb3,0x12c9615515c9cc13f000,0xf0000040200000081448,0x4a4f15e5811bd0943011,0x8000030a3d001bc0000c,0x5bdc13580000000030a8,0xc0ae160ba40000409f75,0x3bc0000e33bc0000c416,0x1c344b39038381,0x66000000b6ec21840000,0x83110000000000242509,0xca18a38132d8d0000001,0x51ea00a64163c0000417,0x2048f40a51c04f005d8c,0x6ce8c63d0221044,0x9058840c141233d40200,0x3135a414840000440a,0x80bed004000d698cee00,0xe6c02b90340e962d01d1,0x20040afc0000451cc11,0x6104ddc4c2a03f3c038e,0x23d80000c329f05ca40f,0x7000000000c0a9f21a14,0xa000e480000c1440a09,0x7018c80bca23f281422a,0x4628a86c091c8cf5051c,0xc94ac0000e0a640cf0d0,0xe598c5d42efc03480000,0xc450000004670014411,0x3d045b84a6f80a6446ac],#[0x80ea02b4012a7092fc8d,0xb81120040d532c103bd1,0xa5202904009cc0441010,0x6111300fab011980acc0,0x2c40000c2e680000556c,0x2fc40a7da37c111a713,0xe006eec0c0a414940000,0x6de8b6800000000182,0x62102d28b1189e710874,0x4cde10ff000021043e0b,0xd001d609fc44e5d4cc28,0x21f00000000001810010,0xb8cbdc13340592440ad4,0x5e4445c00a60023d4925,0x814e20596c0c60009081,0xeca13ce008b1a73208ea,0x1dc60068145c526f602,0xd355da423fd24e281022,0x8cf010634973c0078403,0x3486e3213740ad921f24,0x3384100105c10000205a,0x70019886dc000040cec4,0xbc21d9a000010221c24c,0x180930000308c8a0,0x15d8c55453c4094421b0,0xbccc00f902c3d446183,0x3453240aa00000c8d54,0xff00000c243305bd000,0xf42874000064eef0daec,0x5ef94e9910a7c37db054,0x6034fd2011049040da80,0x280000d0f8a104d8084],#[0x841bc000000ffa402082,0xe084122147e8ae5da2dd,0x1030000315f9c15c51a,0x5d4a530283d2b90e007b,0x57825f5c2a0a857620a,0xc517f70b9ec57ea050bc,0x39748437011380c680dc,0x800001023c0000c17c24,0xf340000c05da6035124b,0xc0e7880954094b0b8582,0xa186b86a29f000010454,0x84dc097102dc805ba01,0xbc0000205ad1ca761528,0x27f7036c00ba00000d0d,0xb0409705f4000020013c,0x4092d21ccc175d42b,0x204dfc17a40000c97c40,0x84fb5016700230000,0x9049e0355c15e2410700,0x2132cb8a8700003486f,0x4041429a201ba4440200,0xb401f1802230569a2012,0x4b0a15d500000000020b,0xd08fa10dc4805f40000c,0x124000025407063ec40b,0x80000000010335d24998,0x4bd539480eee53d5c054,0x42005092900000136bc9,0x1ec36af1238411cf002a,0x934c2e2400000b6d110,0xa81368452d1009208d4f,0x37f1593c0df60d3ec12],#[0x44517f0b86533ce0b838,0x4211900c0c023e047,0xf23914892e0369885b00,0x551084e80f2213158069,0x497ee4249c0588029311,0x159400004103b82ad,0x138002c400005103c00,0x704da692dd16557c1385,0x57c50155c12440514010,0xc16556246c0b2402410,0x427420680a8cc2dac000,0x408fc0000101d7000014,0x6f500d6c0749892140b4,0xe8a7801ad000015006e2,0x23532a8011750fb14840,0x31172650b8d0149f13,0xa6007e0361a05f580e98,0xd4e45eec0dde53b902b,0xf000000000402ec0000c,0x82c41b00000217b6011,0x404a10010d41fe695f10,0x6270443c811200ed92db,0x8945844a094f110586e1,0xb7415a3056bc20431094,0x8aa437220574c54d005,0x6a402192414036500000,0xb230b70000000000e08,0x2000000000c01640000c,0x2e40a5685540429,0x344fa0000113f9813680,0x18594817c5038b28aa,0x9151a005754cf3217400],#[0x40000000000000020585,0xc0f3f2b8ce0a6c04,0xd400000000343bc00000,0x253c58068c0000843,0x40295d49210000000000,0xbb184c400000c8d67006,0x17f84d0d0360000010,0x89c0000000000000d13d,0x10580abfc8f82431080,0xdb0000101609447a1059,0x44a94a59866a005,0x84186180c40303213fc,0x172001bb410e025dda09,0x976f0db5924cf024d4,0x4020000353d400000000,0x400000000e0166017755,0x5ae8971c0000ca68,0x95765491d00003058b00,0x3b4581604e8c93f40b73,0x239dc0c12234d0000205,0x4000081503a0968098a,0x3a244c6a6f04ff82d,0x900000000000000159e0,0x93042512858800001240,0x8000014ea712e5c54590,0x3b50bb44544b455b80b9,0xc05bd0573c170e01c9e1,0xcdc8ddb003b008d460a6,0x462a405430000212,0xdc000042e84000000000,0x134d12950000382bf408,0x8405860492000038cf3c],#[0x46600000056a496ab03f,0x42cd2973018d90f130,0xcdc00000000242e9d4ee,0x5240b42df8076c05f890,0x7000000134d0151d01dd,0x10a404027808,0x6f0084000000000805a8,0x28f4027c00003829c805,0xf40d3404700000000006,0x38090ce400000498e591,0xf44ea000000000051640,0x670031cc44f704fbc527,0x34dedc05cd052605,0x9a00000834e0000205e4,0x58cc176805c7a829401,0x30418c9063085d02cf0,0x295403cc510874b75000,0x5410170a9bc0ed500d0d,0x45dc017325cc1244e201,0xe01410169c0000000001,0x9280226c49de82b584fe,0x404948a8208ee0000084,0x3f055e40118513bc402f,0x3700003101f48ecf82,0x79028982d87019880a7c,0xee900a5d56f1050ec4b,0x2c2182809240bbf45761,0x276810f482c054f62226,0xc2b8a0000205f9844f80,0x29e53c1036a4055c8104,0xe0bbe015c82,0xee4556e53c3c57d00000],#[0x2b2c4fb080ad0ae8b44,0x2b4044c8d4004be44946,0xe18a593c49bb04ad915,0xa82d7c0cecc123e491f0,0x373145e8000001319829,0x51029c8e6a13645107e2,0x3f2858e42617005f805e,0xd1595411b016a80000c0,0x633ec0b460074f10c3,0x83df913d6005482b0400,0x7a112c0418902480529b,0x2214018000002493540c,0x4000020376493c914898,0x20d0000123be0ae2d409,0xf01d8897c201bc82b970,0xcc00000115800000468,0x10282127bc0bcc0a50c4,0x40c5604070ae761052,0x2b005f303c10000000,0xc70b82006e00483c01cd,0x4507251508d18024f410,0x780d4315d040b3f049c9,0x44d06483049bc02af53d,0x44537933b723a0c03800,0x7115398847e94a89907e,0xc0b4c45f00153080ae80,0x802261d8741288105e,0xd60c521a43b9e00b703,0x81018ac0ecfaa50c21bb,0x296b0bc8a0a555400924,0x7840e182c6d296141004,0x37840446049980f900b4],#[0xe12910929f82404136d1,0xaeb12cc0977d041d4145,0xd029b02ea02d280000e0,0x1a820790349800880000,0x158010e442380000242,0x3b05bcc26ad03aa016ad,0xa9a822210479042d00e,0x5576bc00000222f02d66,0x42170135f449ce53a,0x702cd027e80000106400,0x9230122637b449191168,0xe88fa05930000325a848,0x9c487da25f6809ec01c6,0x81230000000000000105,0x1f01b9506aa14e4c148e,0x87e10d7e40a56046e80e,0x740338a24580fd404260,0x3d088fcd0170c02820d8,0x445d0d4ef82009433ae0,0xab903c9c01ca401d814a,0xc0a0c855200709031028,0xa94491b0204c07fa0db8,0x2c2012ce0932c43f803,0x3924828207d0459821d3,0x976542e2c14fe01eec29,0x6c129c84fe0033200c80,0x2f800a7311a4408e80b0,0x201ce02e4e050744af60,0x3fc00f7401ae13e98012,0x1085f4065b04b963,0x4ea13e60366407e12201,0xa72000031314c01fc85],#[0xda131340c39128b411f5,0x14dc000080804419b924,0xac32990420902100000e,0x45204dba02cb057a70b3,0x5028d00002210ac0c2b0,0xcd90070813de08624134,0xc03c01330c0e720ade10,0x740120b2501c0e5a1320,0x44538968c000004c2c15,0xf24023c2cbf444a00003,0x9031423a425751576d03,0x844e72050a0417315f74,0x2854108f43f4003b9039,0x8050100f641568000010,0x7881ae5804da04d944ac,0x5575801ae90cbe087880,0xde0574c008180285146d,0x233b400004445062,0x2b29455249502a9417dc,0x9ad0a8182583144b412,0x682d720435807ae806dc,0xb728052b028440dbb107,0x136280f7605c684c660,0xc7f858580e9511dcc8f6,0xc025604ee824dd032740,0xe7a0a93236c000022345,0x23dc00003059f4042600,0x824398031325d780950,0x4b4d2310494f9855ed01,0x948dec0824420e04b6c0,0x583407555162c8cf7423,0xf0b30c068223bd009910],#[0x145af815078122491f,0xc402c01a600001244200,0xa9613c314f381574238d,0x420f80105c027f14,0x3a0356c0bbb088200000,0x90f124d1180ef043c404,0xde0ab12335c2a60001cc,0x4b1016cb822c4268700d,0x6027e00002444e0204c1,0x5b144f10000224d842cf,0x812d00000c44bc019301,0xed236190135905e10114,0x412e8552c0b990000302,0x10012a004be53bf444f0,0x87c2449ac97a71237841,0x18c918093a23384,0x51090217ec0148000,0x10394616611453000000,0x7ac034b807dc0000c41f,0x9174683dc07f203ff09,0x24c03cf43e906b7b1252,0x435900bc0047f90f5f04,0x8840fb9023b40fda074f,0x4ea10542c156a15ee80f,0x99113400b446918532ec,0x4460000109a3d21a102d,0x405a4c0e4f0168c902e2,0x3f80000c221c00004574,0x4729a00afc003114e3d3,0x56509ca0410d43ed82bc,0x46bd049812e468b5f4a,0x7b2ba3413c103c5a8a82],#[0x3a001318cb4114f1927,0x8412604280522d02d88,0x121003a4045008140000,0xf157ac0b7724cec76550,0x1ca032d4033520f6c0f6,0x4c75827c6027001c105,0x10509440d22189,0x1333406ab1066214fc00,0x3313f0511570388e0ac6,0xb5fa03d48135625b506b,0xf408c512d28151603231,0xa29c60506106440da,0x3045c4815a5334056640,0x3002235c0f7800000000,0x415bb84f80000304cc13,0x72002a4414b40e5c20c3,0x251f009e400008a3d923,0x1904e40939a0004e13d8,0x13ce098e103af05f3411,0x34960e40d1c004244175,0x81c54441219a00ba82a,0x1acf0409a01cf806254,0x46904d80000000008895,0x88f02014bc7144051f04,0xd3005b30437a13f01455,0x1543802b00000046ca00,0xa8008c5ad32053488c4f,0x33c00000c498a809bc92,0x80000081fd010d012d01,0x1fd4061c000040137010,0x313254049ca2f6c03ec0,0x7f101378094180630074],#[0x4df30841d1548039001,0xac04ffa20a8c2b920a54,0xa9202dbe0068911de01,0xaf03c742229133698343,0x3226b43694002400b,0x1509dd8564c148b154c0,0x4094214d00bcc0f680d9,0x725e84003400009293c0,0x54c000008f770bef609f,0x42ee71018d177f8a3bc1,0x96401e611468030f8cf9,0x58101087a2a14008542,0x462f3c60e220a7c1689,0x11a10804c0f2c039bc81,0xe2283f131114fe943124,0xbd1057804b62021ed8cf,0xf0058143f224df40c4f1,0x6788a4044c6f8a85c6e2,0x529c403704070162ed80,0x9fc21140000d2d031271,0x76811e0447400000a5,0xc400002168142b780cb1,0x1038f480bc1604c8e,0xf6048405d40b7db05b40,0xc200fb213520475725f,0x8476b042a849620,0x538000000dac0044c17a,0x40deb05eb00001515cd1,0x380226202bac6286122b,0x14750051c6d7f8485c0a,0xb8042e808a3ac9108efd,0x20be85730043000a300f],#[0xe80cc503d6800fe436d0,0xa7100cc301970003b11c,0x489bb8a29b12838417e0,0x201e708d3901bd408e,0xc04fc0000889766c9300,0x814515800000096002b0,0x42e705608195d80c5125,0x5653d6821b50399c0cab,0x300ec00002015f507,0xd817554029455041c4c0,0xc5259204d5047410f,0x302c60086c04c2c4ffc0,0x20e19dc6080243b60000,0x4152c108a000030c1680,0x1fc0dc905ee451274315,0x427100ed81077415ec04,0x6f49fd10f7e24e0a0c5f,0x5a1449880bde25f9c03,0x4c43caa59b4229a12c79,0x44c5e0a4,0xb048e052a00000c14e40,0x4fb45ed6965c8922933d,0xd02b8000054d6f034ecb,0x4284e403a00002422c,0x2b5072a400008162400,0x5760d2c0a6d245b00000,0x18854d000021204696,0xdc4fd423cca33c04091c,0x2f10000012df012f3002,0x102a5c12fe4b3e000038,0xd4443ae46b9201cb12d3,0xc12c50a868946c1b2344],#[0xc0f72082a820600598,0x15780000115464554400,0x37013b0000302af0100f,0x165205e34208d03d18ae,0x8806fd00da08d5000678,0x3f90000253ff0043e01a,0xf00b5496e10b01608990,0x5f244f8577c401e008e,0x40f9f085e011ed04b8c4,0xb3302ac000cc030b,0xa24340f1203ae92dc400,0xa404f300001050f0031c,0x24b428160b0308855,0xc013c70329c011800000,0x556406bc403500000012,0x8107d80d0e053cd208b0,0x2b0000061645037e4276,0x40912513e00cd213f4d8,0x820000000008263623f5,0x5ff54f4701e4c860625,0xff1acbc0eb3050390096,0x518382bb82f1450f9d14,0x91319b412345425a29c0,0x2c4d293a00cf621bd054,0xc14b94408d859900b490,0x54405ac431244922c124,0xd1048158bd4511300,0xd280dc4084fc0d5202e5,0x18ab480f045a388cbc15,0xa15f240ba440f900000,0x9080000d05640d26c25,0xa1065604860000000004],#[0xfa813d8000086b48000,0x6055e00000136940a691,0x5700000442a11d99c578,0xae31ae8e33f0238e89,0x257a12e79104b0447,0x411250174000004d1000,0xef01b2c158c8cf6d0661,0x5ec00c181128005e910,0x4000000000000000309c,0x3f6c064212c8913b5126,0x233e303a0000021,0x74000000003146a9010,0x402e184ec0000189fd84,0x1b8065400000000105b3,0x41d3c62994cbc4151905,0x111488038a4b6ea6947,0xc1e1270c0d09024a000,0xc57cd41030000125674,0xb0060b1f82f341378000,0xe0229c025e82c84085e0,0x75c2db5411800000c2b7,0x1466853a1046755abc4,0x7c413b20567827290156,0x154c0d6d084702f1f00,0x2001570919a031101033,0xfb6225658b018d31422,0xbc157c03f60046d03465,0x5e5c0020a2e0502b3821,0xb424649806106a445e00,0x43a0077ca00d181360b2,0xc535a02bb02f39248949,0x674528e1a9dc1789019c],#[0x490910c4c0000000000a,0x3000d141546105400002,0x4f80000240cf14d5c12,0xc428a8292840b343358,0x11b813d714b880f94000,0xc08ab851ef849b5042b1,0xaf705e08016b035f00aa,0xc4e9e09fb0000304e680,0xf580b78002994ee941da,0x849eb15e602b1b42,0x4b13f8a28010319495b8,0x214b4110421cd1444503,0x5100fa420fc1327226c8,0x8a2c676b017e41133146,0x6103980ede0351a319b1,0x125a240e0c4e0017406a,0xc0e75018412733044180,0x892206804c7000000000,0x8a38016a000000000004,0xd04027000028271c0bf0,0x101715062203b0805,0xa4046b4573524be05660,0x210893ba049600001008,0x22300014000000,0xc8f04a6407e800000000,0x900c6050c6083d00a442,0xbfc1483a29758b6100f2,0x12840000060aec36dc05,0x451680000c90cd,0x939e11b71245815cf000,0x6c063b49b9500db0b030,0x599c25520803c86f2030],#[0x808250038813ac0,0x7c20a9dc138e49e5c174,0xc06470c4c8103e01b100,0xd302a521446804b7095f,0xa095094b3023e927fc55,0x2a2d8c0ccb1564d1787,0xef3013210973083a000,0xdd2a2800000000000000,0x3180000000008842f03f,0x80278a007509bc133b38,0x2b00e5c163441778133,0x98b6d409300fae021cc1,0x1b40c6d1ca80000002a0,0x45120a9d82df4069404,0x751531a0220025685362,0x2a24044500c3e4b73c14,0xb807b303f18294c00008,0x2e2049bf0505845e4241,0x205b9402fb0234000000,0x4f5490c50ee104c1097f,0x442b401a4042901,0xce442f6a589c251755b2,0x1398896c125b0000102,0xba042746b7f538285408,0x730480a408af40fe92c,0x2002655163057d945cf8,0x60198b9e02be8118d053,0xe422600002401ac0d170,0x7ad03d5d4574000016e2,0xc051325da80de5032b05,0xff8023400000000245fe,0x3170050a11e20140800],#[0xac05ce176c203d782f10,0x5126d0d40020,0x90127701ded02f84a0f0,0x419c035e4de7a150a03e,0x40bfe04979029d480e30,0x67402e300003105ac2a3,0x408d9017245575048480,0x412952b93c4b1b44fe,0x42b9e09020073400,0x102d440406033686e54,0x15352568cb6e30df8000,0xa524c753a80363313e8d,0x41414ce039a40328241,0x54080000201df891661,0x75b82da524d153dc0000,0x95b6052cc29f3427881,0x4061b04fee023f858b,0x94d6402138166c00,0xa25d1c125d03ba60b94,0x954c000040f8f624c00a,0xd02cc8097854dc151ac,0xdd7440fb136a42cba80a,0xca594e02521239191df0,0x5a00aa4c060f53f04053,0xa8a6c00000174f013a54,0x47d8b9604af804f7008e,0x41a9c8d490da6008b610,0x8f02fa10889036810db0,0x20a52430c40d94b6b40a,0xd01187127440061a242c,0x4cff8a890236b15e,0x443e852dc00000d26ec0],#[0x3492910dff0ba3001c,0x108c400008901e18fa00,0x5d8205725a2c6b9d0580,0x3e6000000994c946912,0xce25c500e2b854500002,0xab2e0326c54f91476402,0x4246e25c9d0fbe18fcc,0xcec50b6f55be4117844f,0x103af9017104e9000028,0x54f0940c026b01f60000,0xc31381022c0b92014800,0x2454fb300aa602940000,0x16d823ea022448c5682,0xc0000c55005b6569620,0x16120274c179c00000a5,0x20114e010440e841272c,0x1e304ded15f8497ba14e,0x82e20024fa2a3a8afc1,0x58a042b109d61602404d,0x80b0155cd86bac05c4c2,0x5f0acc10c25c04ba0a78,0x55b50473025d4d09d912,0xe8007d00b8500fd008f0,0x8dae03c694f1a024640f,0x154f640000613f782db0,0x10560b7608500000202c,0x4033e000021445c0ee52,0x2126474c00440b624ae6,0x154900001015a20,0x9451800004404d237c,0x45a2379f108260ac800,0x223312a8f684f2c0ea3],#[0x48542b2f454c305dc000,0xc2dd04b414,0x3b2404a3123ac2414000,0x9449dc0ade0465002752,0x73614edc2db75158c12e,0x813e2412500d8924f584,0xfb4060810a3c0d7b0030,0x156300001050d0000208,0x720352802a12daf40c86,0x3930d19c075a0d56c6a,0xf000780000629ec12690,0x47890040021e80482044,0x91567401eb086f848fa4,0x3ab023240dbe0d844085,0x22246949474930c0,0x670000303f02827042f3,0xd8d25a44238908,0x2a5b60421516c7aa80b4,0x56480f29aa40407,0x6821030245454d400410,0x867417e8001fa0a7e44f,0xa128e852834b5d009dc1,0x468147090c4419424169,0x93c60422c039b018181,0x7bc096a148140829234c,0xa29ad07f7045584fb86c,0x4000004053403b1834fc,0x9c702d7411b105ad40a,0x4c2a720233814dc50ff4,0x3389170903abc0d5c456,0x524b80041f80ac491d50,0x45e515a8248503754099],#[0xc0a05157500785025992,0xcb45597829e84af05033,0x223c162900c6533c90a,0x77052840f4f049f4165d,0xb7905d100c321267005,0xa80cff02d084d4ea23f9,0x92608f99024900003021,0x266c01550485543f80,0x1182f5008bf0933c2aa,0x841ca0169c17db5b5da0,0x65411fb151d28b192106,0xb9cc03d4131fc222522,0xf5145750759021d11166,0x970b016b4152201e6531,0x4424fe6c7d4216705440,0xb844350403c34909624b,0x61296c172f11d000d310,0x58f515b805190096534c,0x936a400eb824744cfdc9,0x208059100d9c05261806,0x555c90aa02ff429a689,0x2c0000c10500475c13e7,0xa94d14ebd008b822d810,0x2c0f7e403b00001026a9,0x224d150b02ad40dd1057,0x3422ac050f04d2c0e164,0xd7e4212810d841224516,0x91264809e80af05b6112,0xcd10020000b01543425d,0x5c0000cb043e8551d05,0x6710d4c231d01da402c0,0x12a0100884ca00a5c805],#[0xe444ee4b4602e63115f4,0x4f28257185ef40174901,0xb42f0037dc0b75042311,0x66b0012841840406597f,0x815b502b150d20808e81,0x3ac00570464809fe25b7,0x822a260784545c08ba04,0xc65b634018d019b08fd8,0x156705be85415821288d,0x920f46c7c84c7325dcc,0xd94440e84c7ac0c0603c,0x71818809d72348963ef1,0x8fe4b3c4163a00e1d319,0x1683137e803734c7b02,0xedc43a400005005f02f4,0x3588a68e053e0409e05,0xf61312000141497e025b,0x911a58e0000301ff855,0x21487013ea00a2e,0x5d2841e4084c03509006,0x8a2a5d2a1f000000ccc5,0x30ac3c076601400912,0x8998000041291425b00,0x618167900a792d2a4b47,0x404c00b0037c90db802,0x440000000010199021fa,0x104e5400940000c0a,0x5d892705362034780810,0x3224145a049e81314022,0xa043300003091f927e80,0x48d038dc0b7c0000935f,0x813282036e33c8014580],#[0x8bcb11e020600fdf04d4,0x2535206809bd4424601,0xdb239e046ce003c01462,0x4fc4124812d850243890,0x9c24d6035c0000253c00,0xc880f0591c0974516,0x800000000000000003c0,0x8080524c4db455b3e0a5,0x84cf300650177901eac1,0xc938d0432c4c7a034a,0x49a90424000040f0800,0x8325d000e9025401573b,0x82000008979e052b120,0x6409a502ca8002600ba8,0x1b1892015159a33f4a2a,0x1006a08d1e0570120862,0x13c53c2c11c510e01034,0x68a9202870080e04b740,0x3ce0c4924a3c248001b7,0x432d0511f11d4413b741,0x5953c840f3753a7d018c,0x97e0011cc4471145b80a,0x140b1c53334019b32ce8,0x3f441302128f4254a053,0x400000000313edc57f60,0x2259e12dc8000080b1,0x12d5e00f642c4d857c00,0x7ce8abd4cae013421583,0x8593e0adea2ac00d134c,0x6304940000001f5001b0,0x20302815,0xb00fb5026e80f3a24220],#[0x5d25601902f9124c8126,0x54b3ac978c133b415d80,0x13902b90000153300898,0x811b7027300efe031280,0xe1041d38082516890480,0xbf528af3033cc28ee05,0x96021fc447d0919137be,0xb9f63108011d2444631,0x702e5c0000e2cf402a64,0x6000095f044b800bc00b,0x204b5800a30b904156c0,0x5ec083d4068a6a590000,0x840904b5cc979b8a50c3,0x1c40644937c8fc75336,0x417113b313f2907fd00,0xc582c488fa60575504bf,0x42915fcc0bc50267504,0xd4492c0000804cc00000,0x942051880000c0ce5410,0x61580e1519153ae08f82,0x1620984098211dd1003,0x82efe482800003151795,0xc1458201edc41c3024c,0x82909069a855c0000313,0xec04448037915fb04d42,0x5697038260d980000041,0x58517a136c007a123e30,0x56200c941b3000001135,0x42140c24d905b1a32b40,0x100d5c52cb02dba024,0x405e34b3d00,0xeac0e8b03374180e19ab],#[0x8555221096826d05,0x204ae0000042ed01548,0x144e4d7f808e305af000,0x8489ba421b0000210810,0x394081c0000836d0819,0x305b50000382b840fc90,0x28c0202000012472448f,0x229f703a700b56011e01,0x4101880000402444026,0x235c90cc1445b0000205,0xbc5b5c680bb01fb00000,0x179904d710eee0205a00,0x10000209252091443318,0x33756d7b08e3d20fb244,0x982af8227c6a55410795,0xaf082aec096d0b6c0978,0x3004b014c10192c2,0x9c340fac0541149d,0x24fe400f60806c147000,0xdf6c79a20be14e50153a,0x56750016c13710411a13,0xc12788858ac05dc001d4,0x3a48d2f020c5277f038,0x24cadd50061361808540,0x456144880d7401c5049a,0xc4acc1553090b1031d05,0x8d011c912478b1252260,0x1ad5e01894028545f204,0xf4085180e0614ea443ee,0x130e0dcdc8163048804d,0xf4097d13a600003044ec,0x5ce50dc00000000024ca],#[0x324c3c54ca0240849962,0x401f44899c020f0000,0xc16c285ee853e002fe81,0x9be13e9028c0000014b0,0x2804138111d2c088800,0x8853ca112710b8c88d0f,0x4000577c36b02263013,0xa0000000278021405cf8,0xadd02482db780e125b8,0xe4030c06c02541444c94,0x111f5480e7059d052d,0x263a5a0800ba8def00,0x95494fe15bdc11e602a4,0x859704a1600b2406f903,0x960a0814560831407bd,0x15292431c2ac64334c10,0xd0800a1294801d014a5c,0x41a21545436b40a39057,0xd234100002219d000000,0x8b0000044c5800009204,0x480f4018f009540000c0,0x3948664000014401112b,0x84a40a5c1548803ea11,0x10062920be15a4503e1,0x13d20457817b34060000,0x809bc0000004a40000c,0x5ec00001028bcaba5023,0x4126d000034406e09fe2,0x1174da5296600000943f,0x82301239c84c6b24cd40,0x79825bd00429459c6a58,0x51dc00000000013],#[0x14000040131020e484d0,0x10e4004e64801292c17,0x2d0a5605b88158511f91,0x17a92dbc42c08810c157,0x300530000105a1084220,0x55c2bbfd43e903b40485,0x125cd434f282a845,0xf714f6d25fa000000000,0x4c624059e02ae508a725,0x8101c7931e503fb84b98,0x435b03e8a08a58281008,0x5446805fd5211705c98,0x7495f715a7c96760bd,0x40000000010b09c0dff4,0x8c04255069405351156,0x8161e4bb9613c7103d92,0x6a7a03ef809b7248b,0xc519a014c8b50000,0x3602fd4112611e429644,0x12c45a8bc603ad00c,0x8c02b40000928e000000,0x54410b624c9380c92155,0xc120c82e29511d80e448,0x16c0000406d00000429e,0xc0cbd2c25000030590c0,0xee82e880000c06ad09a8,0x647840d6404fdc57f94d,0x8355b480f840000040dc,0x3c64cfa8139c1600886,0x14311c05fb037520036c,0x1bc44b4001a415fe23c,0x24402c20b1242d602000],#[0x11ba60b5f00cb003e,0x82a0e029e5157001e300,0x400d841503d0823042f,0x49fe613bc1bcf014e80b,0xda414f4536923b542258,0x3043bc526c039f00b,0xb80eca0b8b10aeb15ff0,0x192011d901f3c4c0a048,0x31225e0a960112000012,0x44dda4cf40000]]
def g253D11 := limbs80 #[#[0xdfdefdfd655455048110,0x5c82544248435407fff,0xb540b5008dd405d40dc8,0xdd485d48dd085d08dc4,0x15950dc915490dc53581,0x9595a5858dc18dd905d9,0x45080dc60dc20dd985d9,0xc544c5d4459445c84548,0x458545d4c594c550c5c4,0xc5c1c5d945c9458945c5,0x4dc645c64dc245c245d9,0xa1322183805106204400,0xc25349690f1f6398658a,0x861031e738e6c8cb17f2,0x16e2c3552a4539a53464,0x3dc776e49b6b4b64abf,0x89d730e4b47489508e0,0xb1b12e2d9faef56296d,0xa14411914221e003f1f,0x285100461827011c6f15,0x6c808c149e201cd44e08,0x49494145101008ee3e12,0xa01c88d85ce0555550a0,0xe04dfe2201453c3a8140,0x61c03208093cf019ee78,0x817e243ee944c17c2d24,0x3aff62048fe5a48a5f44,0x73f004a7f18413d9d12,0x517fe8104efe4057efc4,0x828bed0099e2053fa810,0xde374107f61b04e66607,0xe29f04d1ee413586c133],#[0x155fb9e8140a8fc0c389,0x401557f00305264e8618,0xbac5070fb8e362a37fc1,0xf770d4a04fd62491ee70,0x3fbb5282adf158024901,0xfbff2a042a3f32600a2f,0xa8fe6104dbf43a100901,0xa075c544c8249bde4a00,0xf055be2a742091639c20,0x1bfa186823df4c52]]
set_option maxRecDepth 16000 in
def g253H11 := limbs80 #[#[0x58b00804008103031,0x26080c000340f0007068,0x5000020086c3a0000038,0x481400010a8040647088,0x6c540414800482a0,0x201379ac0e5802880040,0x812051c00428041382c5,0x1010130780038050000,0x840021117814000101,0x20102c0e061200c0a05,0x9a2e1400052000287c24,0x3858011b8140008029bc,0x30200a0b010200481008,0x7038b478050600c623a0,0x26000d800090f844001,0x4412010980258018500,0x406041180458c31101,0x480c0802070000e0607,0x9000001e65078600e24,0x8033803036042208c04,0x8260310145180805004,0xd9b8280b010002270010,0xe0b00012090e90402290,0x380e1bc3c451800c061,0xc0057008009605940580,0x40029098146c070188,0x5d182be07010003a063a,0x11f0dc58433157312b44,0x192920200848e00008,0x1a02d80798559812a0,0x47823ba468005a04e80,0x16b0458040d915d048a2],#[0xbd81fd00a7211300d61,0x8a000f8171855b35e50,0x8202ae0001806fa4e60,0xf2a9779017046681018,0x11680c2410f8425a0c5c,0x153825b226b124120123,0x4eb812501c4000180210,0x8a98077c22e000109658,0xab6909e924481aed10d8,0x668000110101238a8560,0x4f0224126080a9f0cf58,0x8e401160000950e40d48,0x83da049a1d9a48fa0e60,0x100059102b4080c00008,0x17f002508ed405f087c5,0x238000188262026c1178,0xcf01e520fe857010da0,0x184a21e827f80c822080,0x2980001846e047702200,0x1029a0001c0368c549,0x9fd813aa426103c00000,0x8960001094e845480080,0x1901280f180fa0abe8,0x28980e80001014c08780,0x8d800b820ca000096248,0x60784fbd105056b8c668,0x8e189c48294c22021354,0xa4721e8b10c082aa9790,0xf7801f028e0001a0230,0x236003e81cad0faaa775,0x267025f01340000a04a0,0x2298a82c2c1912a210ed],#[0x44000dda23500d5a097a,0x9804998931019d88110,0x19081338572901ca0b70,0x2930863410c08e625f00,0x97b88b18815866189098,0xad899f36998a0e8aac8,0x14a012200a901e816718,0x2490de006c8a1701ea0,0x24cc101822c80f9820bc,0x1638004018e0119a0540,0xd06005db010012801f80,0x264014e9093809401ff8,0x17ca4600947c205a5d18,0xe2c0a80224809029a08,0x22e8177855e00f50255a,0x42a81040087a15642aea,0x13c00010097085002b38,0x5cf88903101511210890,0x2312a84810884120913a,0x80aa000000cc4104a,0x16b20ee1285824600000,0x8a3526aad5f890da4b68,0x98a0001847300d281560,0x28b40fba098000080b6a,0x14302699210000108710,0xa9302600000904909e6c,0x2529243052e0000015c0,0x2af807d8c5609ce8192c,0x42522c00518423789711,0x203882d01460a1400002,0x2a7087b426601f489fe0,0xaab888c862400019],#[0xc546020001004145f20,0x8cf12268,0xa07050e0000000082780,0x1cc91d28277018201f20,0x1082209cc202ea19d9,0x2580548ab8000102980,0xc8d015180a3c430857c2,0x8280430817988eb124c8,0x618402d88b4827c0d728,0x3800000001223c81ba8,0x9ef002a02a1326b25635,0x8d3113c11280ca01c80,0x9671186026e22b0a1890,0x40fc26a819a0671801ba,0x1205c0032806080fc8,0x823f88ef82bd10580,0x29c425891b002a201b60,0x1c60000801700bf0,0x4f04f80000081282280,0xd100000813025e508d78,0x143209a0030a137895e8,0x2b800000000422500668,0x604824f002e24eb0181c,0x89c8015222124d726940,0x26a092a908f299181e30,0xc8baa8782430053841b0,0x13e0218957580188,0x3804b7815e918382300,0xaf296e811181bc12120,0x206a99400008867c13d1,0x89a8235006412a9012e4,0x1060072867d1203a0610],#[0x85a117842f810c88b90,0x262046801418a50850d9,0x519177884d8011c0fe0,0x6180001127e000600008,0x2b189dc00ef803d0e684,0x4d7c2190a64c135c0381,0x1817584560000a2590,0x22311580093448e00000,0x48800e080db246510cd8,0x20cc6088084206590460,0x4dc8138000302b995551,0x923c25c89368a3b81cc0,0x4bf81499143141816260,0x1a6a605886da4a9c0318,0x1b8d10ba204a871c0ee0,0xa7e2021882591df02841,0xaf84d4810fa45e08f4a,0x109d80001c0b704ec8,0x18213240c101982260,0x2b7817b82a8a558820c0,0x184a78088c24326988,0xa80503c45f11c301a00,0x104f624580976a,0x55a915480f7843c899c0,0x8a804c91d88a4e0000a,0x99681dc0000a855812d2,0xa25301fa50f5001c2,0x2c0a0ba226f85698a1c0,0xa0991db8c9980d080c08,0x2032115814580b381668,0x10b00de824bc5f102ba4,0x808e8a1a25ed103b4],#[0x56d0080a034000000000,0x95c0000857591f624319,0x281024889e40001907f8,0x856d137828c09ac90d68,0x2b108da02500001018b8,0x13d526381642467425b0,0x6180000000002900000a,0x266825688e381b181602,0x1f0000180c7a14200000,0x25c00019235848d05388,0x979a99e0a7680458,0x21c00000001a03140e80,0x1d000000000003a8,0x22680ba221945ce25f40,0x1580000916d05a20000c,0x136c02faa82000104150,0x6a011d852d885411e0b,0xa7340cba98f855480ed8,0x2112242829f8063128ea,0x378048c234062600008,0x29681a580f20000c0f4a,0x3482a600008d90810a0,0x1cf34d78198000005c38,0xa0c25e00e38036919f8,0x5c300e5a25a8a85888a0,0x9e9489298d894d02089,0x271171913381d6a0f20,0x2ae82758a9b805e00008,0xabd819581a8000000d8a,0x1d200008113260622078,0x20489060058823341378,0xa3fc2630461009b90b21],#[0x2201dfc04681ee21548,0x186012740c5000d84e70,0x22a000125ee0000c4ea0,0x1b4901f01b888648a998,0x19640f7404bc2090a488,0x6028d0e815b0102a55e0,0x1a20046827aa05e01ec8,0x988000001b32a88a2360,0x1e41674200d8283856da,0x418000000010a6f81c31,0x10e09e902440001c4b78,0x42985d0526fa412269fb,0x26d01688918007122268,0x85d20580000025800000,0x1d80d080240818c917ca,0xe70137885cc099a15b3,0x10155913d0,0x287825342b0000002720,0x1d8525f021ac69402178,0x2ad206a0000021e00010,0x80570aba00740,0x96001db918b020e00000,0x181d5819e011551148,0x92b209cb004a0,0x7e811a115b4228423c0,0x2a5a10185c7c21e82068,0x203a971096681f70a3d0,0x24aa25da056907429922,0x906889926022a8000019,0x1be822fae7009a700b41,0x20481ac0478423089eb0,0x1140000127a326e00010],#[0x1a1eb0524a22401c13,0x417823c0000000000000,0x60400001570c26e00010,0x1016d00b0858f85624,0x95840480000844600000,0x16e00000820012180ea8,0x10c22b92010000000000,0x2dc1154240923612a22,0x1b744a9403520d3086a0,0xac0d21,0xbb12258e6400280d0c0,0x8068956b821489dbc,0x5c582aa807b50d584440,0x17381888043846400ff8,0x4a02700000851084e18,0x67411ca0000000185821,0x1e1801301aa000092820,0xde600a481e7009d85848,0x4260000a5f284f40001a,0x522045e000084d80a950]]
def g253D12 := limbs80 #[#[0x65ff547fd50ff483fd10,0x9080071f7295b8dc03fd,0x91a282011cd8e223458,0x50e38f8d121058e007,0x2242801a38518846890a]]
def g253H12 := limbs80 #[#[0x40001009000003000001,0x1000146111660,0x20000000000000004000,0x1860000000383e92,0x4174030001807c8280,0x14982581c02468480000,0x45d0400000007,0x51980000000000000000,0x809000,0x10b800,0x42d000000000000000,0x681500600000000000,0x11000000000000000000,0xc0700000000000002176,0x40008010002018000161,0x687,0x104a00000050ac00000,0x1e098682020000080f80,0x80b604e4340,0x4a8e1520000000,0x380584c0138000000,0xdc930000000000000,0x409000,0x82f000008924e21f00,0x8e084c00000000000000,0x40d80000528212,0x90a80000590150000000,0x3548000000643c050118,0x0,0x0,0x1a40a4a840000000ab80,0xac0008],#[0xa400000020ca909c230,0x812e8e8000000,0x1002429,0x628603a00020d000000,0x26000033294800009d00,0x21bb08400000008,0xc282a000000223e2660,0x10170140000000004245,0x163a000,0xa3f41c000000,0x23c90e02b40e00,0x1b40b800145680483180,0x382a00000000000001,0x48180000000000000,0x40b545c0000000000000,0x98f8098017042000,0x20c000000000000000,0x30a48000620400000000,0xc800202200060e80010,0x8a00000000000000000,0xc0022a31200004080003,0x9b88c00068b501e000,0x2014000000018000,0x10af92f000000313d84]]
def g253D13 (j : Nat) := if j=0 then 0x30a20400e37f else 0
def g253H13 := limbs80 #[#[0x1820000000280,0x0,0x0,0x22300040,0x0,0x22b4a000000000000000,0x0,0x0,0x3a000000,0x251c080000000c1000,0x11000000000000000,0x20a0000000360,0x0,0x0,0x30300000,0xc0000000000000000020,0x4ac42,0xc2c0000000,0x0,0x0,0x10100000]]
def g253L : Nat → Packing
  | 6 => (30,7,6,1835032,85,9,1060,g253D6)
  | 7 => (613,6,6,16318873,137,15,1447,g253D7)
  | 8 => (1912,5,6,20251375,154,17,1530,g253D8)
  | 9 => (1542,4,6,7667971,121,17,1304,g253D9)
  | 10 => (353,3,6,1835050,86,14,1164,g253D10)
  | 11 => (49,2,6,327685,51,11,1075,g253D11)
  | 12 => (5,1,6,0,0,8,0,g253D12)
  | 13 => (1,0,6,0,0,0,0,g253D13)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 15 97 5 11 5 4 g253H7
  | 8 => lookupShort 387 5741 4 17 10 5 g253H8
  | 9 => lookupShort 1213 5261 11 18 11 5 g253H9
  | 10 => lookupShort 953 4349 10 18 11 5 g253H10
  | 11 => lookupShort 237 1087 9 16 9 5 g253H11
  | 12 => lookupShort 33 337 4 13 6 5 g253H12
  | 13 => lookupShort 5 167 0 10 3 5 g253H13
  | _ => fun _ => none
def g253 : Forest := ⟨253,13,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem timing8 : block g253 8 288 24=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem timing9 : block g253 9 864 24=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
end PEqualNP.Outside.L_meta_52322

open PEqualNP.Outside.L_meta_52322 in
theorem PEqualNP.Outside.L_meta_52322 : block g253 8 288 24 = true ∧ block g253 9 864 24 = true := ⟨timing8,timing9⟩
