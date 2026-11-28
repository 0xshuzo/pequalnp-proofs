import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_35106.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_35106
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfffefffffffefffffefe,0xfffefffaeeee0000ffff,0xffffffffffffffffffff,0xfffffffefffffffeffff,0xfefefffefffaeeee0000]))
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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
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
private abbrev Guide := Nat × Nat × Nat × Nat × List (Nat × Nat)

private def ruleMask (check : QS → Bool) : List QS → Nat
  | [] => 0
  | s::ss => (ruleMask check ss <<< 1) ||| (check s).toNat

private def eligibleRule (s : QS) : Bool :=
  Nat.beq s.2.2.2.2.1 0 && Nat.ble s.2.2.2.1 s.2.2.1

private def guideWire (s : QS) (i : Nat) := s.2.2.2.2.2.1.getD i 0

private noncomputable def forcePairs {β : Type} (p : Nat → Nat × Nat) :
    List Nat → (List (Nat × Nat) → β) → β
  | [], f => f []
  | i::is, f => force (p i).1 fun z => force (p i).2 fun o =>
      forcePairs p is fun xs => f ((z,o)::xs)

private theorem forcePairs_eq {β : Type} (p : Nat → Nat × Nat) (is : List Nat)
    (f : List (Nat × Nat) → β) : forcePairs p is f = f (is.map p) := by
  induction is generalizing f with
  | nil => rfl
  | cons i is ih =>
    simp only [forcePairs,force_eq,ih,List.map_cons]

private noncomputable def withGuide {β : Type} (n : Nat) (qs : List QS) (f : Guide → β) : β :=
  let good := fun s => eligibleRule s
  let count := fun t => ruleMask (fun s => good s && Nat.ble t s.2.1) qs
  let atWire := fun i =>
    (ruleMask (fun s => good s && Nat.beq (guideWire s i) 0) qs,
     ruleMask (fun s => good s && Nat.beq (guideWire s i) s.1) qs)
  force (ruleMask (fun s => good s && Nat.ble (Nat.succ s.2.2.2.1) s.2.2.1) qs) fun extra =>
    force (count 1) fun one => force (count 2) fun two => force (count 3) fun three =>
      forcePairs atWire (List.range n) fun wires => f (extra,one,two,three,wires)

private theorem withGuide_eq {β : Type} (n : Nat) (qs : List QS) (f : Guide → β) :
    withGuide n qs f = f (withGuide n qs id) := by
  simp only [withGuide,force_eq,forcePairs_eq,id]

private def dropRules (x y : Nat) := x ^^^ (x &&& y)

private def pickRule (v : Guide) (i j op : Nat) (ka kb : Bool) : Nat :=
  let (za,oa) := v.2.2.2.2.getD i (0,0)
  let (zb,ob) := v.2.2.2.2.getD j (0,0)
  let a := za ||| oa
  let b := zb ||| ob
  let da := cond ka 0 a
  let db := cond kb 0 b
  let held := v.2.2.2.1 ||| dropRules v.2.2.1 (da &&& db) ||| dropRules v.2.1 (da ||| db)
  let fixed := if op=0 then za ||| zb ||| (oa &&& ob)
    else if op=1 then oa ||| ob ||| (za &&& zb)
    else if op=2 then za ||| ob ||| (oa &&& zb)
    else oa ||| zb ||| (za &&& ob)
  (a ||| b) &&& (v.1 ||| held ||| fixed)

private def suggestedAny {α : Type} (ls : List α) (mask : Nat) (p : α → Bool) :=
  if mask=0 then ls.any p else
    match ls[(mask &&& (mask ^^^ (mask-1))).log2]? with
    | none => ls.any p
    | some x => p x || ls.any p

private theorem suggestedAny_eq {α : Type} (ls : List α) (mask : Nat) (p : α → Bool) :
    suggestedAny ls mask p = ls.any p := by
  unfold suggestedAny
  split
  · rfl
  · split
    · rfl
    · rename_i x hx
      cases e : p x with
      | false => simp [e]
      | true =>
        have h : ls.any p = true := List.any_eq_true.mpr ⟨x,List.mem_of_getElem? hx,e⟩
        simp [h]

abbrev Lane := NodeContext × Nat × Nat × List QS × List Nat × Nat × Guide
noncomputable def laneOf (c : NodeContext) : Lane :=
  let ws := c.2.2.1.map (fun w : Decor => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum,withGuide c.2.2.1.length (c.2.2.2.2.1.map (quickSpec c.2.2.2.1.2 (c.1-1) c.2.2.1)) id)
noncomputable def forceLanes {β : Type} (cs : List NodeContext) : (List Lane → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => force c.2.2.1.length fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
    forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
    forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => withGuide n qs fun g => ih fun ys => f ((c,n,l,qs,ws,t,g)::ys)) cs
theorem forceLanes_eq {β : Type} (cs) (f : List Lane → β) : forceLanes cs f = f (cs.map laneOf) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change force c.2.2.1.length (fun n => force (cond c.2.2.2.1.2 4 2) fun l =>
      forceMap (fun w : Decor => w.1.toNat) c.2.2.1 fun ws => force (ws.map kwN).sum fun t =>
      forcePools c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => withGuide n qs fun g => forceLanes cs fun ys => f ((c,n,l,qs,ws,t,g)::ys)) = _
    rw [force_eq,force_eq,forceMap_eq,force_eq,forcePools_eq,withGuide_eq,ih] <;> rfl
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
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2.1 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
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
    (or (suggestedAny l.2.2.2.1 (pickRule l.2.2.2.2.2.2 i j op ka kb) fun s => fastCost s i j op ka kb) (linkAt fl l i j op ka kb))) (checkAt l.1 i j op ka kb)
theorem fallback_sound {c : NodeContext} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : fallbackAt fl (laneOf c) i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,suggestedAny_eq,Bool.or_eq_true,Bool.and_eq_true] at h
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
set_option maxRecDepth 32000 in
def g255MarkBits := limbs80 #[#[0x5018100602008000200,0x180c0582c14090401c0c,0x3822110803c200f07034,0x903c14090401c2813090,0xb0d06832180b8582a130,0x200f8743c1c0e8701e1,0xc4c241289046220c8842,0x8bc5c2d160ac54291409,0x188081e0f180a4041017,0x290783c06320180c5202,0x48351a0cc522f1789052,0xec5a391d0e470241b8d8,0xf8fc542a1f0f87a3d1e0,0x2210fc543e208f880401,0xc2f0811488442190c824,0x8e4b251249041239088,0x11480412013c9c4d2393,0x29948a24028108804020,0x3d1e9585e102a8bc2054,0x6c5a28164b02a2b8f47a,0x5e421b16c84472396c,0x8180be5e2e8bc205c201,0x30711cc20e06988c20d0,0x4690d1a0ce6632990906,0x4da6c3598cd469348683,0x1cc7c3e391c4e06f371b,0x3c9e0ee783b9d8ea753a,0x7f3f1f4f87b3c1ecf07a,0xfe7e3f1fcf07840a0100,0x1d108743214ae8441a08,0xc0e918394622d148044a,0x11e9f91e9047a391a573],#[0x29349924844049245229,0xd2c494a950ac7b3da50a,0x83c1e104c83d24984b25,0x4da68207b3d840207b3b,0x794f9e53c9e4e9cc8a9c,0x8a563c1e4f2793c9153e,0x7942703aa8942a020100,0x3a994a7752011461e0f0,0x382b45eac55aa952a85,0x6415910562b057ab8827,0x568785c2dceab65aad16,0x94c22535d11572b43c9e,0x592f11a5e2b1e0ac995d,0xbe5ea45223d1ea211e8f,0xc0415f90542a12fafd64,0xc5ea1608bd84c060b00,0x2b118cc562b1186a160b,0x2b15820100783d8cc56,0x6c863b218e2f2b0cc5e1,0xd94c90883990c76431c6,0x441e0e080401e0f2b03,0x70441c0e08159965607,0x5767b38f6cd66044220e,0x68d56a34cf6c969345a0,0x614a562b159aec937359,0xaa912ec92bb3db4786cb,0xe6eb71b6cb2b25cf6786,0xecf03b8c8ae270b81bed,0x5168b73225cae42738ca,0xa411c8d2ba34743a1c8e,0x73914e44e48a447a3d47,0xee76bb1d66049ba9d2e8],#[0xe4f13cbc1e0ef30175dc,0xe0f00f081e01ef37996d,0xabd16272569b8f078081,0x97c040204a7bbd9eaf53,0xafc34869f6fa0e8e916f,0x5e0bf12109fefe5f891f,0xaa025a02c012291488f,0x80420d068296e090381,0x8080405e5583840f055,0xd291349a4341a489a435,0x2c210c85c285b0954108,0xd10a21068796e1d0e86c,0xd89c2e17121b2d0f1117,0x8d2f0bc5e5c84c50201,0x4822d88451223d442422,0xc542010078441c0e8a8b,0x8c84083188bc581e1108,0x1a8dc68fa3b1da452236,0x381d8f074201d8ec703b,0x723920080743b1f0e876,0xdc85f03f8e3e6383319c,0x39248dff20913d6403b1,0xa3b48a45223b482411ef,0xe4c3b48040f113078da4,0xb30200f0795a4e0f078e,0x963323d2b95332532817,0x27179e198cc5a1e25a1d,0x1a5e46c1cf72e08158ad,0x4522911e8f51e8f484bd,0xd8ec7a3b468856e2f982,0xd46a3442f5990ec5f311,0x2f92e4da6a5f9a4cc7a3],#[0xa73389b9800a5f82401f,0x4fe7d3d9e4ec433a9d4e,0x1ace2866091d0a83409e,0x365128a8b44150a85435,0x5e2f58d168d462412090,0x122436a392090361b0d8,0x58f2954991c8e4723a44,0x522904834c2a9548a45a,0x102b158ac4220d36985,0x854e20d369a40201008,0x840ac562b10480412490,0xa6108ab50080402010a7,0x4da610aa4422110aa249,0x5e41208bc20100810a9b,0xfea8ffa9d4c805624d30,0xb3feacff7fbfdff55aa3,0xd4e8140a0502816ae75a,0xf58229ae0f07838140a9,0xcea75ac89240755b97cb,0x9d56e45add14d707ad54,0xaf576b95c3a9d4eb0783,0x7520d8ac2b7b048ebe42,0x46b7b197eb14e028140a,0x14d75aa9adeca2490592,0xad9d2c405bc1d6f66add,0x3399cce875199d45e2f3,0x15bad958acf9ad958e67,0x8040201008169205a08,0xc8ed4b7b19d4ea402010,0x3a9d4ea753a9d4eb693a,0x755b9d4ea75b5dac80b4,0x80b4569d56f233a90ad8],#[0xd4eab73a9d5244020100,0x9d4eb6db590168753a9,0x62b3e6b6563a9d4ea752,0x36e2b24ab092ac56eb65,0xe47702e24ade887cbe5f,0x1d5f2f9919188d7191c8,0xbabc6ea0f07dd2e773b9,0x42babc6eb75ba9582010,0xcb769048080402b04084,0xd6b723919d08a45bc5de,0xa2d2a779bc9d448243a9,0x205e8acd85a2d2a6d85,0x8b43a566db0790482f64,0x6d765b6db6d640af5f16,0x108204020090497d5bdb,0x91c8df2753a9148a1021,0x5b4f9d6ff7e3ad64acf9,0xf6755badf03812fd6300,0x54b45a1b109feff1b51d,0x60a8a5f2fd60aa5a2d1,0x52fd60aa5a2d0d8854c9,0x723a65316f20c148d6f4,0x46610c215706552a955f,0x8cc6610198cc6610083e,0x7fbfd0436c2e14663319,0x552d16884421b10884ff,0xa588213c69923c3d170c,0x3298b75bde16f78a2df6,0xbadd6f23919d4834ca65,0x5a2e260d06a9168b74c5,0xeb7b2ade8b52213c6987,0xd6e755badd6e42a65316],#[0x8cc20107c8416f4c5bad,0x90480663319840663319,0x237cc824010211082010,0xdd89ac626b024123e647,0x8f145cc4dbd10f919be6,0x7e2c48337cc8f17715bc,0x62b040218ec6637180f0,0xd8cc7630218cc6040ac5,0x31e562b04082402015b1,0xcd6eb719c8e475b2de4,0xa4d25eaf57ad32994c1b,0x5a7a9d5eaf5a5d269349,0xeaf5198cf2591c88fc7f,0x2e73391da4477475bbd5,0xa97cbef5a2c8cbe5fc9d,0x591d16465fc9e5261837,0xe103ad30e8757abd4bef,0xc1e757abd4667417d305,0x25cfb953e8bea6881783,0xcb1f4fa7d2b158ac1008,0x560848240564b9f52e7d,0xe398cbdbd10f97cbe5f2,0xc6479991e6647237c972,0xcbe5f2f97cd66b365b6d,0x7add6d6f2391980f2737,0xaf51d8edf32391be56eb,0x5ea3b1dbd5eaf57abd5e,0xf076f97cbe6dc2f7abd,0x1da61319b7ce68b9392e,0xb73a900823b7fbfea888,0x82417ac8e472391c8cb8,0x8e7138b897e472391c8c],#[0xe671f2f97cbe646f591c,0x53a9d4ea753a9d4ea75c,0xe3319d32999dceadd6e7,0xc6633a62dd6eb7a62dd6,0x532b72391be647237c8c,0x3a9d5f32391be5eaf5a6,0x3e646f57abd5eb5b]]
set_option maxRecDepth 32000 in
def g255Labels : Array Nat := #[0x601424130d03462,0x300024104b01151,0x800040209804273,0x800040209804274,0x1000020109808275,0x2830241a0983472,0xc04840221406872,0x2830241a0983430,0x601424130d03473,0x300024108b01262,0x600000884261263,0x82040281082420,0x820241a0982430,0x820241a0982431,0x220241a0922130,0x2200a0d02a2130,0x220241a0922140,0x22040281022130,0x601424130d03472,0x601840221403872,0x280024128b01651,0x400040205402163,0x280030188e01251,0x280030188e01272,0x300024108b01272,0x400024130d02463,0x400040221402863,0x200030188e01265,0x200040209201272,0x200040209201273,0x1000008049208275,0x200024128b01251,0x8000180c8e04265,0x210110c8461120,0x10000180e0e08454,0x8000180d0e04465,0x24011188464170,0x800008048a04283,0x800040209804283,0x280301c0c28160,0x282020300882462,0x22040241022150,0x220241a0922160,0x2820110484c2472,0x446018240646261,0x24008240224160,0x443020300843261,0x2200a0d02a2140,0x1000030188e08276,0x8000180c8e04273,0xc03000208847064,0x220241a0922150,0x840111884c4441,0x24011188464140,0x24011188464150,0x280110c8468160,0x800040209804284,0x222241a0922340,0x22240281022340,0x210110c8461130,0x21024160921130,0x400040221402873,0x2830241a0983462,0x2200a0d02a2160,0x2830241a0983442,0x906040281106843,0x283040281083442,0x22040241022170,0x28011048468150,0x2830241a0983482,0x28008140228170,0x28020140828160,0x24040301024150,0x24040241024160,0x446008240246271,0x28020140828150,0x446040241046251,0x2830241a0983481,0x2830241a0983431,0x24010188424150,0x24040241024150,0x443040241043261,0x240110c8464160,0x220080e0222130,0x220201a0822130,0x220241a0922180,0x22040281022140,0x601840221403883,0x2400a2102a4150,0x408024160d0a064,0x220241a0922170,0x283040281083482,0x2200a0d02a2180,0x906040281106832,0xc04840221406883,0x2200a0d02a2170,0x906040281106883,0x288018280688451,0x48020140848260,0x21040241021150,0x10000100a1408865,0x10020180c9208284,0x10020301c180a084,0x10020181c120a084,0x6000301a0e03863,0x400040221402864,0x200020300a09074,0x606040301207054,0x2830241a0983461,0x6200a0d02a2160,0x204040301205043,0x606040301207043,0x443040301043251,0xc08018240e0c054,0x801040241805074,0x2820110484c2442,0x606040301207064,0x2830241a0983452,0x400040221402883,0x602020108a03273,0x200020108a01273,0x230301c0c23140,0x200020108a01272,0x602030188e03273,0x200020104a01183,0x200020108a01283,0x21420140821530,0x601040221403883,0x200020104a01173,0x440040221402a83,0xc04040221406884,0x40800020442a053,0x601440211403483,0x400024124d02173,0x283040281083431,0x40000a054682174,0x906040281106842,0x400040205402174,0x222241a0922330,0x2220a0d02a2330,0x2220a0d02a2340,0x400024130d02473,0x303040281103832,0x400040211402474,0x400024130d02474,0x400040221402874,0x21040301021160,0x204040301205074,0x446040301046261,0x2830201a0883432,0x220080e0222140,0x602030188e03283,0x400024130d02484,0x1000008049208276,0x22040281022160,0x22024220922160,0x28011108468170,0x2800a0d02a8170,0x28018240628160,0x283040281083472,0x21040241021160,0x28008140228160,0x443020300843271,0x602030108e01273,0x602040209203273,0x208020300a09073,0x1001020141809087,0x208020300a09074,0x220182c0622170,0x100400814120c087,0x210100c8421150,0x6200a0d02a2130,0x620241a0922140,0x6200a0d02a2140,0x808008240a0c054,0x220301c0c22160,0x240101c0424170,0x808008240a0c065,0x21040301021150,0x21011188461160,0x2830241a0983441,0x210101c0421170,0x220181c0622160,0x283040281083452,0x600030108e01273,0x210102c0421160,0x24010380424160,0x220201a0822140,0x400040211402473,0x21024220921150,0x40800a15068a064,0x210110c8461150,0x48008140248260,0x908030280d08852,0x40010a054682174,0x2200c0e0322140,0x288020140888431,0x288018280688431,0xc030181c140a053,0x200000a05229074,0x60201028160b074,0x602030188e03263,0x600030188e03263,0x10000180c9608276,0x200020108a01263,0x204000108245043,0x602020108a03262,0x601424130d03483,0x403020140843286,0x202020108a01263,0x602030108e01263,0x406008140246286,0x208010288649083,0x600030108e01263,0x204010188645043,0x2830241a0983471,0x606040301207053,0x202020188a03263,0x602030188e03262,0x2820110484c2431,0x20220a058481283,0x401411098242483,0x90180c160502843,0x44100a0902c1281,0x4440240a0944281,0x448008240248281,0x282040241082442,0x40000a054682173,0x400024124d02174,0x204040301205083,0x208020300a09083,0x204040301205087,0x208020300a09087,0x204040301205073,0x801040241805087,0x808008240a0c087,0x210100c8421160,0x24010188424160,0x28010288428160,0x240101c0424160,0x280102c0428160,0x283040281083441,0x210101c0421160,0x28010380428160,0x204040281205074,0x210110c8461140,0x443030280c43241,0x21020280821140,0x902011108542873,0x2200a0d02a2150,0x21010280421160,0x2400c160324140,0x230201c0823150,0x23020140823160,0x260081c0226160,0x400040221402884,0x22040281022170,0x4018110a8242873,0x2400a0d02a4170,0x24018140624150,0x906040281106873,0x23011048463140,0x230201c0823140,0x204040301205054,0x10000301a0e08865,0x443020300843251,0x80000c068b04274,0x800008048a04274,0x8000180c8e04274,0x602030188e01273,0x800040209804275,0x23020140823140,0x21020300821150,0xc02018048e06274,0x443020140843241,0x800008048a04275,0x446008240246261,0x200030188e01276,0xc02008240a06275,0xc020180c8e06275,0x210301c0c21160,0x2400c1e0324140,0x200040209201283,0x280181c0628170,0x22040301022150,0x10000180c8e08276,0x200030188e01273,0x606000208247063,0x210110c8461170,0x20011108c641173,0x28011188468160,0x906040281106853,0x26008140226160,0x304040301205853,0x204840301205853,0x8000180c8e04276,0x200020108a01262,0x200024128b01262,0x602030108e03263,0x200030188e01263,0x200040209201263,0x906040281106882,0x602020300a03273,0xc03040241807084,0x240181c0624160,0x446008140246251,0x210241e0921130,0x902011108542842,0x4048110a8842884,0x210241a0921160,0x21030140c21140,0x26011108466150,0x260081c0226150,0x210301c0c21140,0xc04840221406873,0x8000180d1604465,0x8000180d0e04476,0x10000180d0e08465,0x601040221403473,0x601040301403474,0x601024320d03474,0x10000180e0e08865,0x22030380c22170,0x26008140226150,0x906040241106863,0x24011188464180,0x22040241022160,0x24008140224150,0x443030140c43241,0x21040241021140,0x21020140821130,0x21020140821140,0x24011188464160,0x28020140828170,0x28008240228160,0x220241a0922190,0x601840221403893,0x288018280688462,0x283040281083492,0x204040301205053,0x601040221403884,0x10000100a1408886,0x40800022050a064,0x40800a25068a075,0x210110c8461160,0x204040301205064,0x210110c8461180,0x22040281022150,0x40800a25068a064,0x601440211403494,0x601840221403894,0x100200a0d128a096,0x40800a25068a095,0x443040241043271,0x446040301046271,0x28008140228180,0x1000008049208296,0x208020300a09094,0x280082c0228160,0x220082c0222150,0x28020300828150,0x28010280428160,0x28020300828160,0x2830241a0983492,0x28010280428170,0x204040301205094,0x2200a0d02a2190,0xc04840221406894,0x908030280d08863,0x906040281106893,0x288020140888442,0x288018280688442,0xc030181c140a064,0x1000008049208286,0x448008240248261,0x100000a0d128a086,0x208030380e09094,0x208020300a09084,0x801040241805085,0xc03040241807085,0x601424130d03494,0x606040301207094,0x280182c0628160,0x28030380c28160,0x446018140646251,0x446008240246281,0x800008048a04295,0x240181c0624150,0x282030140c82442,0x601840221403884,0x443030380c43261,0x24008240224180,0x208030380e09064,0x21020300821160,0x4460182c0646271,0x24008240224170,0x800008048a04285,0xc02008048a06285,0xc020180c8e06285,0x902011108542853,0x260181c0626150,0x22040301022160,0x208020300a09064,0x200020108a01293,0x24008140224160,0x602020108a03283,0x200030188e01283,0xc03040241807095,0x8080182c0e0c065,0x8080182c0e0c096,0x902018140702853,0x601024130d03484,0x4430301c0c43241,0x4460181c0646261]
def g255Mark (j : Nat) := g255Labels[packedAt g255MarkBits (9*j) 9]?.getD 0
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7e00003f8003f8,0x3f80000080108220002f])),(BitVec.ofNat 152 (word80 [0x841082102040820408,0x4080000000000000000f]))),((BitVec.ofNat 152 (word80 [0xf80001fc0000007,0xc000000300611d7f65cf])),(BitVec.ofNat 152 (word80 [0x94508a50a1428a1428,0x428000010020096f654f]))),((BitVec.ofNat 152 (word80 [0x3f0000fe00001fc00,0xc0082204092bf])),(BitVec.ofNat 152 (word80 [0x8c31863060c1860c18,0xc18000040002000090bf]))),((BitVec.ofNat 152 (word80 [0x7c00000000007e0000,0x8030030041809abf])),(BitVec.ofNat 152 (word80 [0x8d35a6b264c9864c99,0xc9808010010000809abf]))),((BitVec.ofNat 152 (word80 [0x800001f00000000007,0xff871ec07c0c7e1cddb2])),(BitVec.ofNat 152 (word80 [0x28a314214285142850,0x85010a441406761090b0]))),((BitVec.ofNat 152 (word80 [0x7ffff8,0x781f007ff07fe12151])),(BitVec.ofNat 152 (word80 [0x72ca58458b1638b162,0x16282c415afc7b780040]))),((BitVec.ofNat 152 (word80 [0x1ffffff800000,0x7fe0007fff80063e08])),(BitVec.ofNat 152 (word80 [0x430c60860c1820c183,0x1832a01063d980800a00]))),((BitVec.ofNat 152 (word80 [0xfffffe000000000000,0x7fffff80000007c044])),(BitVec.ofNat 152 (word80 [0x1081020410204,0x204451aa800000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(1,0,254,0,12),(2,0,253,0,12),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,11),(64,0,191,0,11),(12,0,243,0,10),(20,0,235,0,10),(32,0,223,0,10),(72,0,183,0,10),(128,0,127,0,10),(33,0,222,0,9),(34,0,221,0,9),(36,0,219,0,9),(40,0,215,0,9),(136,0,119,0,9),(0,8,87,160,8),(0,32,82,141,8),(24,0,231,0,8),(130,0,125,0,8),(1,32,82,140,7),(4,32,82,137,7),(8,32,82,133,7),(32,8,87,128,7),(48,0,207,0,7),(80,0,175,0,7),(96,0,159,0,7),(128,8,87,32,7),(128,32,82,13,7),(12,32,82,129,6),(49,0,206,0,6),(50,0,205,0,6),(52,0,203,0,6),(81,0,174,0,6),(82,0,173,0,6),(84,0,171,0,6),(88,0,167,0,6),(97,0,158,0,6),(98,0,157,0,6),(100,0,155,0,6),(129,32,82,12,6),(132,32,82,9,6),(136,32,82,5,6),(144,0,111,0,6),(160,0,87,0,6),(160,8,87,0,6),(192,0,63,0,6)]
def g255A : List (List Nat) := [[]]
def g255D6 := limbs80 #[#[0x3e3d2f01b9e8587a1564,0xa7a7e0373d0b0f42ac98,0xf4bc06ea95e458759307,0x9f80dd52bc8b0eb260f8,0x930c0c1e9e]]
def g255D7 := limbs80 #[#[0x65974551b6aa4875d154,0x551b121d965d1546c087,0x61d9021d646d88765974,0x21d64ed18764087593b1,0xed98764487593b461d91,0x21574593ba61d9121d64,0x593b2695765d1645d985,0x6579161d64ec195e4587,0x61d64ec1a5e4587593b2,0xecda5e4587593b269791,0xe4587591baa579161d64,0x593a7e939161d64e9ba4,0xe8587a1564e9fa6e4587,0x5d9656d2a921d76595b9,0x6c48765176595b021d94,0x65176595b221d945d965,0x5d3b3697865d9746d087,0x697945d974ec9a5e5176,0x61176e9fa4e45865d3b3,0xe9fa6e45845dbb261791,0xe49855dba7e8f9261576,0x3f3b26a685e1176e9fa6,0xd70f3c3af0dd8db633d8,0xf16dc4f713bc3f30f9c3,0x36cccf3339ccb732bcc9,0x6de0f7723d3e34f4d3c7,0xef0b7a2de83f933e2b78,0x780803c053c6cf0f3c2,0x78203ba10c565051e841,0x84a23c052be195aee891,0x827fb4107e2a86f0d43f,0x377b617de309eed84ff8],#[0x5fc422ddd0f7ee86e76c,0xf964b7cba38e1d1b78c4,0xc0425e1993f0cba7845e,0x44c7e2a06f0d03f84823,0x391d39b3f0cda7846ef9,0x1bc3366e9cf3f4e74bc3,0x7dabab6d5d6728d33867,0xd0b2fe8580d94bc3a159,0xabea6d5f9786f07c155d,0x439592022e9117c3895d,0x834160903814050012da,0xf87436190b854261107,0x31178b45629138944621,0x86411f8f476391b8d466,0x54a65127934964923914,0x3994c6612f974b6592b9,0x200bf0ff0b79b4d6693]]
def g255H7 (j : Nat) := if j=0 then 0xb004010000020 else 0
set_option maxRecDepth 32000 in
def g255D8 := limbs80 #[#[0x684875d154680875d154,0xaa4875d154698875d154,0x698955d1545d8955d154,0x5d9655d154aa0955d154,0x659755d1545d9755d154,0x2a1765d154261765d154,0xa95765d154695765d154,0x21d965d154e59765d154,0xe9d965d154e85965d154,0x65a755d1545da755d154,0xe85985d954261955d954,0x69994dd55469e985d954,0x65d85215645d98521564,0xe858721564ea58521564,0xe918721d64e858721d64,0xea58721d64e998721d64,0x61d9121d6461d9021d64,0x614855d1645d8855d164,0x684875d164680875d164,0xaa0955d1645d8955d164,0xe1d755d1645d9755d164,0x295765d164e8d755d164,0xa95765d164695765d164,0xe95765d164e1d765d164,0xe1d855d1645d9855d164,0xe9d855d164e99855d164,0xe8d955d1645d9955d164,0xe9d955d164e99955d164,0x5da855d1645da755d164,0x69a855d164686855d164,0x6a6855d16469e855d164,0x69a955d1645da955d164],#[0x5db855d16469e955d164,0x5db955d16468f855d164,0x660985d56421f965d164,0x261855d564e1d765d564,0xe9d855d564e91855d564,0xe95875d564e85875d564,0xe85985d564e81985d564,0xe8d985d564e89985d564,0xe99985d564e91985d564,0x692855d564686855d564,0xaa6855d56469a855d564,0x5db935d564e63855d564,0x61f935d564617935d564,0x693985d564a17935d564,0x680875d96469b985d564,0x688875d964684875d964,0xe89955d964aa0955d964,0xe91955d964e8d955d964,0x692955d964e9d955d964,0x21f945d96469e955d964,0xe5d7661564e1d7661564,0xe858761564e5d8761564,0xe5b94615645db9461564,0xe819561d646549561d64,0xe899561d64e859561d64,0xe919561d64e8d9561d64,0x6869561d64e999561d64,0x69a9561d646929561d64,0x2579161d64e569561d64,0x6579161d642979161d64,0xa579161d646979161d64,0xe1f9161d64a979161d64],#[0xe579161d64e539161d64,0xe939161d64e5b9161d64,0xe9b9161d64e979161d64,0xe1f9461d64e9f9161d64,0xe85879d564e5b9461d64,0x6a576a156465d76a1564,0xe8587a156465d87a1564,0x5d991a1564e9587a1564,0xe1d91a156461d91a1564,0x61d94a15645d994a1564,0xe9d94a1564e1d94a1564,0xe1d96a156461d96a1564,0xe8598a1d64e9d96a1564,0xe1594dd56469594dd564,0xe8598dd56469596dd564,0x65b85dd564e9198dd564,0xe8587e156466385dd564,0x61d93e15645d993e1564,0x69295e1d6468695e1d64,0x691765d56569a95e1d64,0x684875d965680875d965,0x690875d965688875d965,0x690955d965aa4875d965,0x21d945d965aa0955d965,0xe9d945d965e85945d965,0x691769d565e8f9261d65,0x659762157469196dd565,0xe8d85215746598521574,0xe858621574ea58521574,0x6919621574ea58621574,0xe9175595745d97559574,0x29576595742617659574],#[0xe9176595742a57659574,0x5d985595742618559574,0x5da7559574e859859574,0x69f98595745da8559574,0xe9d865d574e59765d574,0x5db945d5745db935d574,0x690955d974e17945d574,0xe8d955d974e89955d974,0x692955d974e91955d974,0x697865d9746a2955d974,0xe1b945d974697945d974,0xe858661574e597661574,0x5db9361574e5f8561574,0xddb936157461b9361574,0xe5f9361574e1b9361574,0xe539161974e5f9461574,0xe939161974e5f9161974,0x2579461974e9f9161974,0xa618599574e5f9461974,0xe9d869d574659769d574,0xe8d989d5745d9949d574,0x6a576a157465976a1574,0x65f85a1574e8586a1574,0x6a785a157469b85a1574,0xe8586e15746a786a1574,0x65495e197465b86e1574,0xe9d945d975e8d95e1974,0x65b94e0d75e1b955d975,0xe8d8521576e898521576,0x6159421576ea58521576,0xaa485611766999421576,0xe898561176e589561176],#[0x2179161176e8d8561176,0xa1791611766179161176,0xe5b9161176e179161176,0xe9b9161176e5f9161176,0xe5f9661176e9f9161176,0xe4f9261576e5f8561576,0xe5f9261576e5b9261576,0xe9b9261576e8f9261576,0xe5f9361576e9f9261576,0x65f85a1576e5f9661576,0x6a785a157669385a1576,0xe8985e117665495e1176,0xe8995e1176e8d85e1176,0x6a685e1176e8d95e1176,0xe9d945da7569385e1176,0xe8d985da75e89985da75,0xe89955db74e61955db54,0x6549561b74e8d955db74,0xe859661375e8d9561375,0xe899561b75e859461b75,0x6549561376e8d9561b75,0xe3df1bf87fc3f61f70df,0xf9b5cd9e67f337997cb7,0xbe9bf4bf9e7cebe73f36,0xfca7dd3e69ef4f5a79d3,0x67eaef53fa97d3fa9fb4,0x5e7ae7d6f6b775b7ad7d,0xdc3ecdf64fb1fd8bebdb,0x772fb975cb6e57727b8f,0xbddbaedb74fb9f5cf6e7,0xff87dbeadf36f8f79dbc,0x79e3bf1bf8dbc6be2ff0],#[0x27792fc7f63f71f78f7c,0xcb9e5bf2db95fc9fe4f7,0xf35f9adccfe5f72f7977,0xbcf3e73f37d9bdcdde6d,0xeb3ed9f5cf9e7bb3db9e,0x4fd1fe8f745fa27cfe67,0x9fb4fba7bd3be9bf4dba,0xabdd5deadf55faadd4fe,0xeb9f5bdaddd6deb3f57d,0x3af6d7aebcf5ddaedd75,0x6ec9f63fb0fd7e6beb5f,0x9fb3ed9eecef66fb2fd9,0xc7edcf6ddb6ddb5ed9f6,0x79bbb3dd6eeaf74fb9dd,0xe36f17f87fc3ee1ef07f,0xf8fdc7de3e71df8dfc6e,0xbe6bf33f97bcb7e57f27,0xd79e7cede73f37b9bbcd,0x3be9bf4bfa3fcfce7cf3,0x63fae7d6deb3f53fa7bd,0xe2ff0ff83fb67daded3f,0xfc3fd5be8ff36f93fc7b,0xe117007645d885f2bf93,0x282e01109d302210a903,0x15d051a0a8064234c04,0x1d761d612ec23865d854,0x32ec42076e87290d48e6,0x6ae0570cbb0d596a8134,0xed8110b3b31616f642c2,0xbba480a762592e6c4885,0xb606714ec54604dca340,0xec4405ad919cb9b13397],#[0xda08673b6105076820a3,0xa90e1e774219bed8433f,0x4c8354e990679d887cf3,0xc8f631d81eda7a741b87,0x3a1409ba3e8a7667b16e,0x33e0b7647c18ec0f8cdd,0xbc845d97a01dd1b853b,0x17e015d30a689861cd13,0xb686db45a9ff52b72a6d,0x6985766d40bec9a829d8,0x2300ee9e69bd3b8423b3,0x427d93dd0fa45900775,0x6d2ba7838a7670216eca,0xca0752f800eea2c03d94,0x949e9e1e9fd3c38ffa97,0xe60db028d3b704807752,0xcc1b6079ab620f366c01,0xe5aec2a0c6d806195d03,0x306d18041d9a700fba22,0x64d8abccdb05795f6ea7,0x26ba5798368af316c95e,0xd76209cae581012da2b0,0x4edc2675d884f2b96091,0xedb8164d7602c6d50043,0xb9606e572c0c0f6d80c1,0x7500ec42a01c695c0372,0xe94213252840a6b905e2,0xd4041f0a8084874e1099,0xb5084cf2a109925420f9,0xe109021c2133da84264,0xe020ba4c04243b708487,0x284634a508be770107c2],#[0x808b51501188e98231bd,0xc008de54231a4a845aba,0x40511cb00a439600c8f2,0x85e22b90144172020cae,0xab6f6e1574ed82a4bd8,0x20ace8a40cfdb0591bb9,0x511dc38aa57961555f47,0xa32895146550a28ca614,0x46576a28ca2d45195ca8,0x9c66145311d40a221a81,0x195ca8e329851c357502,0x221a91c4435038caed47,0xbb34e23c85d84710dd0e,0x76ee8478ddb88f18b711,0x6c548c223ba114455222,0x22ba18181743088ea461,0x272c310e6dc6526ba8ca,0x8e5866535d0c713a618e,0xebb0ea65751d4476c338,0x1a91cc43503997e58752,0x36e3b935d47710dd0e62,0xedc77115b8ec39b71dc4,0xbb0f621b61e4472c3c0e,0x96214aaec4255ed87aaa,0x2a2688ee883115490657,0xd84f11dd09a22a913653,0x38d657961acaaec35715,0x51a65f46348ee1c6b1c4,0xe3688e1c6d10438db2b9,0x47d11cb0de37951bc476,0x8fe23871fc410e3fcae5,0x204472c408de548110db],#[0x2ec46145d11dd10e21b6,0x56615c8af29a5159836a,0xb32fb316667642c30ae8,0x2185722fcae945b95d28,0x491a544922ca89244951,0xb20ca896409512c8f2a2,0xe7b42c4872a2590a544,0x1db625aab260b06fdb16,0xaba60b46edb168e5b42d,0x65d8966df872bdff6857,0x8bb72cd476c59afed0b3,0x357447935d8907bcc126,0x8e1ca4f0c394a5176290,0x6bb14de298293c330527,0xd872a3b70e537661ca72,0xb745641660aadfc3951b,0xe4c953bcc11b0d852301,0xcc129e285253c30a4a60,0x932520f304b46e60948c,0x724a78ed494f05a929ff,0xc48a35d811519b925231,0x29318793260bf644519e,0x526b07264d47e6098f34,0xa4e5fe4c9c8dcc135e28,0xca2b7c99411798273bd0,0x9318bb22631f624c56e4,0x262f7684c5e5d098c3d9,0x4c4761c98b3db1316576,0x9ababa1351fb82623f0e,0x3563b626ac2ec4d5ded0,0x7237704d46e1c9a8cc39,0xe5ced09cb8ba1397fb32],#[0xc8bc39391587272baec4,0xd597627adae84f45ee09,0x2aaec5044e1c9e88c393,0x555d0a285c3941098728,0xaabb16cfb87289f30e51,0x19b944bc76a89555d0b8,0x27669a246cd368ddca25,0x9ec540acd1a7c7fb64d1,0xfda27087b24e22346a01,0x3b64ea330a9d5ded13a3,0x34a9db0ed13b61d22756,0xed93b53d32751ba54ea3,0xd32791bb54ea336a9da9,0xa70c6194e18a665c314f,0x4e199e29c334dd48630f,0x9c34235d06444ba0ccf7,0x386906a70d20b4e1a412,0x70d2096e1a116dc3483d,0xe1b41edc34835b86905b,0xcdb7cba9b51bb90da332,0x1a155a7360fb6e6d5569,0x3493d7268c4e90d189ca,0x6b7ce50d76dda1a6dba4,0xd6f1da9ade0b535bc4ea,0xa919b935a372e6b74e58,0x54f14a6aa1e90d549d09,0xc0ed11f3bd31aa7ba53,0x28ddd242a7b648587689,0xadaa7495b34e92196dd2,0xd576a93b0ec526abd3a4,0x56dd2a24dba529fb649,0xabda22ed9b4455b7488a],#[0x9bb54b53f6896a9ec52c,0xc76a8d046dd3020dba5e,0x165d1c8cdca35199746b,0x3d223293a14620b728e4,0xfb4514ef4c8c9ee95194,0x76ca3afed14765d8a8ef,0xee5428ccba85199550d4,0xba18663b330b8ae86046,0x8730cb7686196e50c32c,0xe8628aedcc315c398628,0x1cc5124398a5794314aa,0xb98e238731c410e6389e,0x732c2f2a6488e50c911d,0x866886dccb11c3996208,0x4bb0bca99a21b4334472,0x97632952ec632a5d8c25,0x2f45b2a5e8b254bd19ca,0x5f8a254bf17ca97a2e95,0x4115ca97e2a952fc532a,0x8296b51052b6a20a52d4,0xd236a21a42d4434bda8,0xcc7e903949da88692b51,0x98bdb07317a60e63f681,0x713a60ed27721ca4ea43,0xd27621f9dea43d43d487,0x3d6943e7a5287e87b40f,0x3bdb07cf7a50f9ed4a1f,0xf6b50f9eb6a1f3d2d43f,0x870e80c0e99007bda87c,0xe91055b42a06b58540d,0xfd21ff1f943fd4f0e82c,0x3a641e2f4c7fc5e58ff8],#[0x36885b0e1d0780db20f0,0xe1d1032da9fea78742e0,0xd32032796406272c87a7,0xa641e4f2c83c7e9d0193,0xea797ce9d078fd3a0f27,0xc0f6335d1e6b5a53cd6a,0xa1eecbb33dd9f647bb4e,0x53dd6f4a7bad294f761d,0xe7ba9ed8f633da9eeb7b,0x50232dd1f6b7a53ed276,0xa06b5a540d6cea81ad5d,0x42e2f4e85c5e9d055b52,0x7a6de950cdad2a19d3a7,0xf969d81f065b73d56b4a,0xf2b7a53e597667cb3ec8,0xf56f4a7e19edcf88dd39,0x446e9d0832dd1f865b73,0xd5dd81b865b5430cb6e8,0xaafb337567646eadec4d,0x4f76e6ea6ed8dd55da1b,0x83e44de83dd1b847b737,0x1d99be0bb237c1f626f,0xd79637bef686f7de50df,0x776e6f6ee5cdeebdb1bd,0x4e58e0f9da1c1f394383,0xbdb9c1b797383a76c707,0xf9438bf7667181e44e2d,0x72e7173e58e2f7da1c5e,0xe58e4f5ca1c9ff913936,0x4a9cdf39139b5f2e7272,0x9739b8f2c7376e54e6ec,0x2a7471e50e8e9c89d1ab],#[0x50eacfcb9d1bf953a379,0xb9d5b7973aba72c757ce,0x63b3b72a767ce44ec8dc,0x47842e5cecd5cb9d9c79,0x4eee3ca1ddd3913ba0b7,0x264fb973bb3f2e776fe5,0x4cac76c9946a1532bbda,0x9946a95328c52a66c3b4,0x488d5aa6518b54cd4f6c,0x95d97552a332ea4785d5,0xe1f32ea66f5d54c84cba,0x6caed18795da3172bb45,0x36c4c30616a96365768c,0x72ba5f15d72bfb6a618,0xa3770c452edd88bbda31,0xbbed19557d1b953bb463,0x46db332e976665bf0cca,0xd7a5645b748c8b6e1996,0xb70ce84ee5192a1c9b26,0xb591d29cca39edba4735,0x9c33a5118674a82ece95,0x5865c262ecb85a591708,0x74cb6a65d96d56cb2dd0,0x6d97083d32e046ba5b53,0xdb2e105b65c20aecb811,0x855adb368b5b6e916a83,0xeaba46ee572f0baae6d5,0xdd76aabb2ed69755da0a,0xa366ed646ea776ebb4e2,0x16d0ed70dbb7e19b377d,0xedaa8ed9b55fda36acbb,0x9bd50bb37057b76d5176],#[0x35adba46b2634cd84e69,0x6bbe728d77fe4daf6dda,0xd7782d5ae8dcab5de395,0xda8dcbb5db7976bbc76a,0xa905a677a0b2eee4c699,0x627768ebb66d1d56dd23,0x466e5d88ccbbb1e3b57,0x2f0babc4f9767822766f,0x91bb978a332af1789d5e,0x9836ad588e19a94fda3c,0x886d99b11c3336359566,0x1fda33a3f946749766ce,0x3b9467c576cce8ae199d,0x476cd088e19a113c333e,0x7ed9a510db346238668c,0x1d337f03866f92b6adf6,0x786705e748e0bce9dbf8,0x74ee1256d5c373d3382e,0x695c5795bb8577a770de,0xd2b9169a571a974ae252,0xba79d5f66f3b6e19c89c,0x312172659e8e4bb3d107,0xc56671d8a9daf9891367,0x2ac08bb15a15f6eb338e,0x85845f4eb094e9561285,0xab09425560e9d42c1d0a,0xd6129daac250b5584a72,0x2c22fb75845f0eb08b21,0x58ba770b0742e160b04c,0xb185e95630a52ac623a4,0x630a4aac59fa858b3950,0xb835b756c9ae8ad85e55],#[0x545f28a98ce51501ada2,0xb09ae55711ca2ae2b945,0xad7c1bd622b955c4172a,0x99d868eb7b48f667e19e,0x22b291e6c5d23ce6b247,0x6b5d23ee4b247d17948f,0x88cb49113948fa23291f,0x199592be7692544e5a48,0x2b292774eda4c8ccac99,0x4e525088ca4a1179493a,0x4dac1703a482e0709054,0x3a4835e70906b9e9e0a4,0xd7501ad5d60373d341af,0x2960565d9c0acfb2810c,0xdac0ab7b58156f4b02ad,0xb7815276f02a9eda0433,0x7503196de075bd2c0c67,0xd6095b3ac12b575820cb,0x3c1c89b5838cd7504196,0x5845cd6f0758e9e0f73d,0x2ff415d5faa5d2c2149a,0x1fef7ca3fdfbb37fc0f2,0xbfdb3977fb9f2cff7bed,0x803d729007fe46008bcb,0xfe44e5e00d7cbc01cb96,0x2e96d2c26db84848f36a,0x6117b98bbdae9177eece,0xda27671b45eca36f4ba4,0x6aceca2ce3db47109748,0x2fdd9c6507ba8b55f671,0x9e9748d3db29197b5d23,0xd5f66fbacec9f6f4ca46],#[0x41ee9f755da3eea9747d,0x97dbbf12cb77e29aeafc,0x5847d262e8fa53591f4,0xae8fa116d1f483d23e9,0x15921683da3e905b47d2,0x3c242ec58485deae90bc,0x1648690b690cb85d2196,0xb690f57e921ebfd243ae,0x692156eb244547a48810,0xcbc5131a489a5b49124c,0x804800b8000416922a82,0x10503c40d402a407b017,0xfe07241a7060015904b0,0x90bc42c00a3825a08ac1,0xe1836d0d3c32c0c8430,0x844090fc43d40ed839e,0x4c4ab122046d11444391,0x453414a451c13f44e413,0x5af1690593160855a151,0x75193062518445f9176c,0x31cf47091b6c6b41aa46,0x1f707cf1e987791db876,0x19c853210483620407e7,0x508fe23ac8cd22f48942,0x974255894e251893024,0x9ee27489bc267498925f,0x3a28c8a2a2888a1a2810,0xa2988a5a2948a4a2908a,0x2a48a8a2a08a7a29c8a6,0xb08aba2ac8aaa2a88a9a,0xc8aea2b88ada2b48aca2,0x8b1a2c48b0a2c08afa2b],#[0xb4a2d08b3a2cc8b2a2c8,0x7a2dc8b6a2d88b5a2d48,0xa2e88b9a2e48b8a2e08b,0x2f48bca2f08bba2ec8ba,0x8bfa2fc8bea2f88bda,0xc8c2a3088c1a3048c0a3,0x8c5a3148c4a3108c3a30,0xc8a3208c7a31c8c6a318,0xba32c8caa3288c9a3248,0xa3388cda3348cca3308c,0x3448d0a3408cfa33c8ce,0x508d3a34c8d2a3488d1a,0xc8d6a3588d5a3548d4a3,0x8d9a3648d8a3608d7a35,0xdca3708dba36c8daa368,0xfa37c8dea3788dda3748,0xa3888e1a3848e0a3808d,0x3948e4a3908e3a38c8e2,0xa08e7a39c8e6a3988e5a,0xc8eaa3a88e9a3a48e8a3,0x8eda3b48eca3b08eba3a,0xf0a3c08efa3bc8eea3b8,0x3a3cc8f2a3c88f1a3c48,0xa3d88f5a3d48f4a3d08f,0x3e48f8a3e08f7a3dc8f6,0xf08fba3ec8faa3e88f9a,0xc8fea3f88fda3f48fca3,0x901a404900a4008ffa3f,0x4a410903a40c902a408,0x7a41c906a418905a4149,0xa428909a424908a42090,0x43490ca43090ba42c90a],#[0x4090fa43c90ea43890da,0xc912a448911a444910a4,0x915a454914a450913a44,0x18a460917a45c916a458,0xba46c91aa468919a4649,0xa47891da47491ca47091,0x484920a48091fa47c91e,0x90923a48c922a488921a,0xc926a498925a494924a4,0x929a4a4928a4a0927a49,0x2ca4b092ba4ac92aa4a8,0xfa4bc92ea4b892da4b49,0xa4c8931a4c4930a4c092,0x4d4934a4d0933a4cc932,0xe0937a4dc936a4d8935a,0xc93aa4e8939a4e4938a4,0x93da4f493ca4f093ba4e,0x40a50093fa4fc93ea4f8,0x3a50c942a508941a5049,0xa518945a514944a51094,0x524948a520947a51c946,0x3094ba52c94aa528949a,0xc94ea53894da53494ca5,0x951a544950a54094fa53,0x54a550953a54c952a548,0x7a55c956a558955a5549,0xa568959a564958a56095,0x57495ca57095ba56c95a,0x8095fa57c95ea57895da,0xc962a588961a584960a5,0x965a594964a590963a58,0x68a5a0967a59c966a598],#[0xba5ac96aa5a8969a5a49,0xa5b896da5b496ca5b096,0x5c4970a5c096fa5bc96e,0xd0973a5cc972a5c8971a,0xc976a5d8975a5d4974a5,0x979a5e4978a5e0977a5d,0x7ca5f097ba5ec97aa5e8,0xfa5fc97ea5f897da5f49,0xa608981a604980a60097,0x614984a610983a60c982,0x20987a61c986a618985a,0xc98aa628989a624988a6,0x98da63498ca63098ba62,0x90a64098fa63c98ea638,0x3a64c992a648991a6449,0xa658995a654994a65099,0x664998a660997a65c996,0x7099ba66c99aa668999a,0xc99ea67899da67499ca6,0x9a1a6849a0a68099fa67,0xa4a6909a3a68c9a2a688,0x7a69c9a6a6989a5a6949,0xa6a89a9a6a49a8a6a09a,0x6b49aca6b09aba6ac9aa,0xc09afa6bc9aea6b89ada,0xc9b2a6c89b1a6c49b0a6,0x9b5a6d49b4a6d09b3a6c,0xb8a6e09b7a6dc9b6a6d8,0xba6ec9baa6e89b9a6e49,0xa6f89bda6f49bca6f09b,0x7049c0a7009bfa6fc9be,0x109c3a70c9c2a7089c1a],#[0xc9c6a7189c5a7149c4a7,0x9c9a7249c8a7209c7a71,0xcca7309cba72c9caa728,0xfa73c9cea7389cda7349,0xa7489d1a7449d0a7409c,0x7549d4a7509d3a74c9d2,0x609d7a75c9d6a7589d5a,0xc9daa7689d9a7649d8a7,0x9dda7749dca7709dba76,0xe0a7809dfa77c9dea778,0x3a78c9e2a7889e1a7849,0xa7989e5a7949e4a7909e,0x7a49e8a7a09e7a79c9e6,0xb09eba7ac9eaa7a89e9a,0xc9eea7b89eda7b49eca7,0x9f1a7c49f0a7c09efa7b,0xf4a7d09f3a7cc9f2a7c8,0x7a7dc9f6a7d89f5a7d49,0xa7e89f9a7e49f8a7e09f,0x7f49fca7f09fba7ec9fa,0x9ffa7fc9fea7f89fda,0xca02a808a01a804a00a8,0xa05a814a04a810a03a80,0x8a820a07a81ca06a818,0xba82ca0aa828a09a824a,0xa838a0da834a0ca830a0,0x844a10a840a0fa83ca0e,0x50a13a84ca12a848a11a,0xca16a858a15a854a14a8,0xa19a864a18a860a17a85,0x1ca870a1ba86ca1aa868,0xfa87ca1ea878a1da874a],#[0xa888a21a884a20a880a1,0x894a24a890a23a88ca22,0xa0a27a89ca26a898a25a,0xca2aa8a8a29a8a4a28a8,0xa2da8b4a2ca8b0a2ba8a,0x30a8c0a2fa8bca2ea8b8,0x3a8cca32a8c8a31a8c4a,0xa8d8a35a8d4a34a8d0a3,0x8e4a38a8e0a37a8dca36,0xf0a3ba8eca3aa8e8a39a,0x23b07e1fc1f85f023ca8,0x680c688057e100e7049,0x1c2c9004408417029f0a,0x1a0a313b23a2991d0a0b,0xc0b08f06e0d856953336,0x1a23438568498a545c23,0x2716e2c965824b7a201d,0xb5839c8614b22e1cc852,0xc2c2104614cc860a8350,0xe450155202b82d033720,0x39878108d4c663506d63,0xc241f0bbc00212302f4,0x89167008257e3010fc,0x940ff8c004236ff4b00,0xce5f0810143e201dcc02,0x3cfcc1413cfce0600211,0x4dec80104f79f700209c,0x900008475f111c400202,0x1049dfcec40060913ff,0x1fe17842848df8ee400,0x1df91118dfe27c006120,0x8881fc802190016e042],#[0x843bf22233382126fd0,0x311ebc89a0e9c40883dc,0xe0121ee0121df9311df9,0x404116b80231bdd8802e,0x9190075e3a0006cb3c6,0x1001300947e92221e42,0x403af5c0888657640211,0x1dfe00010cc00988066,0x233e201ae0c033738081,0x2427f0a0021944fac004,0x61061180109fd6fe0004,0xc3400271f00309138e,0x4b9e1002234700cf40,0xc81c658edc12402b3002,0x75f8400a8c0098055e13,0x806b8210025fd6108114,0xd20699423d769008ccf8,0x9ec840feb241a201e7ae,0x30e48d3e2918cc3923,0xf71310d04021f8a18300,0x4f8a46330e48c02fc241,0x30e48cc3923]]
def g255H8 := limbs80 #[#[0xc308202c8813000d0,0xfb0026f27c4013580000,0xb2b680277b4dd595dc04,0x2afab86cc0000d73350d,0xbc919b9d3700f9c46080,0x4032003540060031c027,0x4413ca5039002399b886,0x22c7e95bc4917128da30]]
set_option maxRecDepth 32000 in
def g255D9 := limbs80 #[#[0x59554640875518721d54,0x550955d15421d7455176,0x5d574551655d15426174,0x5d15465974551765d154,0x553765d1549d57455265,0xe5974553955d154e1974,0x5d5545d975550875d554,0x553965d554e4d7555386,0x66176551955d95461d76,0x61954a6176552955d954,0x5539561d54e4d8755395,0xa1e655518799554e5987,0x9d55465e755529899554,0x55195a1d54e1a7555298,0x6637555196dd55465375,0xdd9546537655386dd554,0x55287e195461f8655198,0x614855917621564a5f86,0x21d6461c875918721564,0x590855d1646448759190,0x5d574590955d16421d74,0x5d16461574591765d164,0x592855d1649d57459195,0xe1d74593855d164a5574,0x5d564e5974593955d164,0x591855d5645d97559098,0xa1575591985d56461d75,0x5d564e1575592985d564,0x593985d564e4d7559387,0x65576590955d96421d76,0x5d964e1d76592955d964,0x5917661564e557659394],#[0xe5185593876156461d85,0x61d64e5d855939661564,0x5929561d646558759095,0xe51875939161d64e1d87,0x9d564e59875939561d64,0x591879d5646167559176,0xe1e75592989d56465e75,0xa156461e8559176a1564,0x59196a15646528559191,0xe1e8559385a156465e85,0xa1d646568759194a1d64,0x59194dd5646628759196,0xe177559198dd56465b75,0xe156461f8559176e1564,0x59695e1d646578759193,0x648875959021d6561c87,0x5d5655d975594875d565,0x594875d965e517559793,0x65176594985d96525576,0x61d65e5576597945d965,0x5979461d65e4d8759792,0x65e75595769d565e5587,0xdd56565687596989d565,0x59598dd56565b7559594,0x61f8459576e11655d784,0xe1165a1f8459675e1165,0x5d17621574dd78459697,0x658855d1862157461485,0x59574e18855d29821574,0x5d185595745d9655d175,0x9d5655d1985957465d65,0x5d574e61655d28559574],#[0x5d1865d5745d9755d085,0xe4d755d3865d574e1575,0x5d974255765d3945d574,0x5d3865d974a55765d195,0x5d9855d3955d974e5176,0x61574dd9855d18661574,0x5d39361574e19855d385,0xe5d855d39661574e5185,0x61974e19865d09561974,0x5d39561974e51865d391,0x616655d17599574e5d86,0x9d5745da755d19499574,0x5d1989d574652755d186,0x5da855d3869d574e1675,0xa157465a855d186a1574,0x5d385a1574dda855d197,0x61b855d176e1574e1a85,0xe1974e1b855d196e1574,0x5d695e1974657865d095,0xe19765d5945d97525576,0xe0d75e55765d7945d975,0x5d586e0d75613835d576,0xe13835d596e0d7565383,0xe0d75e53835d786e0d75,0x5d596e117561b845d796,0x650855d9852157665386,0x61176215845da9821576,0x5da8561176615845d895,0xe45845db8561176e1184,0x61176e59845db9561176,0x5db9261576e15855db97,0xe59855db9461576e4d85],#[0xa1576652855db9761576,0x5d885e1176e16855d997,0x657845d985e117625784,0xe1176a57845da85e1176,0x995945d665653855db85,0x5d584997985d665e4d75,0x5da75619769d69761265,0x9d7945da75661769d594,0xe59879d79461e75e5576,0x5975465d65d517659754,0xd51765d754e6165d5297,0xe4d75d51965d75461975,0x61b5465576d53985d754,0xdd186597745d965dd297,0xa5576dd1955db7466165,0x61b7465586dd09561b74,0xdd5966137565584dd695,0x65586dd59461b75e5984,0x6137625584ddb9461b75,0xb8f78df87fa5584dd995,0x9df9bf97f8ff8fe8fd8f,0x7f9ff9fe9fd9fb9f79ef,0xbaf7af3aefae7adfabfa,0xb3db3bb2faffafeafdaf,0x6db5fb5eb5bb57b3fb3e,0xfb9fb7fb7bb77b6fb6eb,0xbd7bcfbbfbbdbbbbb7ba,0xf7befbedbe7bdfbddbdb,0xfc7ec7dc7bbfebfdbfbb,0xcf7cf3cefcdfcbfcb7c7,0x77d6fd5fd3fcffcfdcfb,0xbdb7dafd9fd7fd7dd7bd],#[0xddfddbdd7dcfdbfdbddb,0xfedfddfbdf7df3defded,0xfe9fe7fe7de6fe3fe2fd,0xedfedbed7ecfebfebdea,0xfefeefdefbef7eefeed,0x7f6ff5ff4ff3ff2ff1ff,0xfbbfb7faff9ff7df7bf7,0x6fedfe7fdbfd7fcffbd,0x64ad000d8586043a2ec,0x4089a0080db4c0324684,0xb81746272068c2042d10,0x703e882e09d085c17a00,0x204d18680ba315017461,0x84da31f00752003e61c0,0x1234235256806ac2bb0f,0x4e84ec04d199809a324,0x3cd013501763d00f522f,0xf987190e3444d1d6849a,0x27427300ea4627ac38cc,0x3e8a4a05d1b6c07a94e8,0x2d120089a04001747250,0xba34a01f44942068d004,0x344841d685083cd02100,0x61cfe7cc39f86da4420e,0xd1a29139345007527d3c,0xa2838af44e615e89c889,0x520601ea5dc05d1c1c0f,0xa4146154028c1a705181,0x301dab8603bc2ec0730a,0x6023570c0b785d81661d,0x43069808f1bb011e17,0x1060d3039e176071855],#[0x21e2a5043c34a08142a,0x631f5008632a010edcb,0x914aa41a28548349aa9,0x64cd300c9ba7049b742,0x78c7a30f331500226aa4,0xfa17521e6be8c3c13d48,0x96a43e24d407cc1a40,0x6d7c304d17860984b4e2,0xc48a808a872c1157e582,0x84b4c2209e984284cb88,0x6e984e0cd48a10f8612,0x46d386108980b11f4e16,0x47a60a8b7461542e6030,0xbf441718e842e33d005c,0x69c3221d385c5ba30b8,0xdd18ad58a5148334e191,0x9a9160934a2c06ea4562,0xb4c1c126945a28d20b41,0x6983824d307117960d84,0xcc46199878c04f4c2406,0xa38c997451966ea230cd,0x471958e8a3225d4464c7,0xa23454d34690ba88cabf,0x347c49a78d84b531a126,0x88e3330d1c5765a3ed6c,0xd2012ea23c65d14784ba,0xa4424d2c890b98908934,0xdcd7a31b83353221169,0x1a3530a34765d876ecbb,0x392be9872ecbb0e5d976,0x786cd08f09ba71cb1f0e,0xf099a71e15b4c3c765d8],#[0xb3b2ec3e3568c7c14d48,0xa35e8c7429540d9d9761,0xa4dd38e8afa61d3b2ec3,0x99a71e95b4c3d765d87,0x3b14a3876e1c70ecbb10,0x76e9470ed528e1d9a51c,0x4d548d5db8720bb10e41,0x178725a2b0e4b525d896,0x9b42472ae988861d2111,0x8e848a54d311cc1a4239,0x9d111837a12307740461,0x3a62305748460be8c8c1,0x74264086989814d21302,0xe90eaa3d31d02fa3328c,0xd31d82ba43b06f427651,0xa63b21f487647e84ec11,0x522f4265c5eccbb0bd07,0xd8aea3cb15c63a118217,0xb9518b872a0534e57515,0x72a8c742550869cb093c,0xe6a4761cd4a8bb1a8ff9,0xcd686c39ad457635a3f0,0x9a049a7370574e6b43e1,0x3620b0e6c086a4d092cb,0x6918e84d211d39b10787,0xf4a4bb1e8fd97348974a,0x49d887290c742794561c,0x796f444f11aa09cedc39,0x1fe9c9e57d213cb3a32,0x23f549347da72815b485,0x58ba618b1f483164e846,0x2a72c5e5ae50bc7fd48c],#[0x54e98bcb5d217993872f,0xc7c397d47962fa3f0e5e,0x78730b170e6143e1cbe,0x392a5e6ee90bcddca179,0x7e54bc8f4a9791d952f2,0x9d3979a3a62f3472c5e4,0xea52f23b4a5e47294bcc,0xf2c5f47e9cbc8fd29791,0xe84b633d016d09952d33,0xd216c5ba32d8bf445b18,0xa42e0c3425c11e98b629,0x467111698b885ca97051,0x84f88fd09cc37a13985f,0x228845a63e0a3487c186,0x653a1130a2755d94461d,0xa423e9d48eabb291d57,0x15046d3aa1d576542113,0xa8ddba451a0930a342a6,0x51a4930a375e9546ea52,0xa50be8d4a19d12952698,0x4c1bd0a983ba05305748,0xa41fa75305f46a60ce89,0x32b2eac80669d520ed3a,0xf4c5d95e854c31d0a986,0x96bb2c15b855822f0ca,0xd2796558934cad0a6996,0x8934ccd0ae999696bb32,0x9ea53a17d1b31259664,0x85d4a7509964eb5f469d,0x1ba94f0c7429e4965938,0x53489f416594224d2a84,0xcdd97898bb2f133975e0],#[0x7cbaf517865e22b0cbc4,0xea95ca4f2cb74ae5d749,0x32ed4076997e31d0ae01,0x6a5a884cbb5049a66a25,0xd4b4c1da967a4b2ccf42,0xa96a8974ad018e85a00e,0x2cd918e85ae0fd334819,0x196a0cd3b602ba46c20b,0x32d499a55aa8f0cb567e,0x35914744b22669162edc,0xb326691664dd22c89fa,0xd84b5ca3087da55a0835,0xb0d3ba7612d748c24ee5,0x6d05f46db49e5d8297cb,0x2342e55b82dd1b6d0995,0x4ccc52c918ba891ba94b,0x9c43a89313f472628e8a,0x48bf4529426565020d44,0x717e892e85caca85ba39,0x224d2a641ba94b8b7469,0x45ba34a8335299116993,0x332ec98665d92ad7d1a5,0x412a52c0cd4a6c49a74c,0x22d326849a54d20f5296,0x27a447a82ec8357e5104,0x77428706e912812d2240,0xaaa10a54d22147fa7439,0xf54a107da44215348892,0xba445237288a096911a3,0x3488d126911a8bca22d1,0x69220d7d1c3c27a44883,0xca43419a9880934b1014],#[0xa671893490e12ea218ae,0x48e816e91c82cd339c5b,0x59d22dd33951796728b3,0x23985ba4710b34ce9456,0x6708bf44eb16691d42dd,0x91511691be12d23859b8,0xe262fd144c47a48884b4,0xcac19a48b8334d1616e8,0x970a7492c18e86582dd1,0x2f17e8a5e23d34b863a1,0xee9dcbbdd53967b8b747,0xdd1e857ba3b0af747215,0xaa774ef754e99ee8fc2b,0x317e89e60d54bc52f977,0x893cbbe50b957a0b746f,0x85fa2832132b04146920,0x8a3490a066a6102dd1c1,0x426560a17d1c1c33a283,0x85cac245ba3838bf4507,0x27a9770434cef42615de,0x1752ee6be8ddcd9d13b8,0xde5df8a7cb3f173937e2,0xbd3bf14fa67e2e746fc4,0x7977fa572efb4ce5dfa9,0x349034a65e060ed24012,0xe920484d4c0d09978189,0xcacc419a7858474d0b07,0x9603a172b3316e8e6484,0x42097a2601106cb02e0d,0x9c12f5c3825e88704c3f,0x3094dda6029bf4e097ae,0x525bd70e3786e8c6eb6d],#[0xe44805d897094292e118,0xc92695491db4982214f4,0x90d23982494b4e493868,0x211a74a453ae848aefc3,0x463ae848c77d01192198,0x8c6fd2118e3a3231cf44,0x20e1a32407f4a462fe98,0xa2ef466534e94c891cc1,0x755658eeb6d29d16f853,0xcbfca97955a53aa43307,0x96f952fad92a5f5fe94b,0xaef467155e58c0abcb16,0x29e9d58f6bb2bddca951,0xb7cab0d6c956194f4eca,0xf9a440a7f2ec44fe5d80,0x1742875569126fcd2239,0x7e9d0eefc3a1ddc8743c,0x3d3b78bda44317f4e877,0xf97792af2cf229e9e245,0xf2c074fe5df0abcb3e13,0x6580906bb0120f9605c1,0xcb0220ea50441b2c0e83,0xa906bd550087a2a010ff,0x520d6f6a41aded3834de,0x581307d28260ca504b7d,0x4025bca804ad930097fe,0x807bd70e0f7a21c1edfd,0x146daa424dad38496c9,0xc3091540996fa612acd5,0x8646ba90a9a550183469,0x8ea474e1d1a69c32cad3,0x2184e8e430bd1485b5a7],#[0x6f07428de0d851bb6f51,0xddff961bc1f2a3783254,0xdc1b0a3b37ea06e6ed40,0xb7ae1c76ffcb0ee0f951,0x8febb0d0dda91d9bb503,0x4dea91a1bb4e347fe586,0xbff4c397fe5872febb0e,0x7ae9c72f4538e5bf871c,0x6fd48e56ca91c9bf4e39,0xdda71e3ff2c3c7f5d878,0xfaec3e376a4786ed40f0,0x7aa47c6ed38f9ff961f3,0x4438d9fd761b41b2a363,0xba31d1bd52367ae1c6cf,0xf2c3a7f5d87507ca8ea1,0xe1c74f4438e9ffa61d3f,0xca8f4dfa71d3d74e3a7a,0x871ebff2c3d7f5d87b07,0xec403769c7af5c38f5e8,0x9470f5c3901e887203fa,0x28e1fea51c3fb4a387f2,0x720bfd4a417f69482ffd,0xe4b7061c966ed28fdff8,0x96bacc12d749825b870,0x92d758525aef304b5da6,0x25aef0e4b5d61c96bbc2,0x4b5daa096bad412d74a8,0x881ed49112398222ef50,0x11fba6223f2ec4483e90,0x23c94e446de1c88dac39,0x77e5d88edbcc111e7a72,0xedacc11db78723b6b0e4],#[0xdffa4219a350476da608,0xaab30437ee9486fc5290,0x2fe988a6fd2115579821,0x91cc115219822b2f0e45,0xb4a522b7f484572e848a,0x41524569e988adbd2915,0x8e609490cc128d1a5252,0x154929b6a52536b4a4a4,0x3a02324730460faa4849,0xf46465ee888cbfd09198,0xe988cb3d29196fa4232e,0xd21303fa72327f4e4655,0xa6262db484c2f698986e,0xe636d61cc6fcbb18d55,0x94c4ffd218967a931b6f,0x49895598313bf0e627ee,0x6321bf48643ae84c8aad,0x26448660c8cbc3990bfa,0x8c8dbd2991bfa4323974,0x19cd1a533a47526469e9,0x3a24352676d694ce90cc,0x752969cee70d19dd6d85,0xecb7d21d97fa13b2ab0a,0xd921a53b2af4c7648614,0x7b6b4e2f6d29c5e91d29,0xe7fe905cdbd38bdb6a71,0xe5d08c157a9172ab2e2,0xd23a91834f4c306fe906,0xb7b0e577fe58aefebb15,0x5b65caeb64b95dbf872b,0x6ed395d6f972badd2e57,0xffa42a2dd0e575b61cae],#[0xbf2e547725ca8d3c3951,0x5aa4a85e5495157972a3,0xa4b961a7872c34b0e585,0x7972c2ad2e585565cb0a,0xd0e585561cb05ed39615,0x294aadfd2155cba12aaa,0x4b955a7a62ab6f4a556d,0xa72b2472e5565e5caaca,0xea595be90b2355495869,0x1cb29ec396557a62ca7e,0x39ad7e87352fb0e6a4fa,0x735adb4e6b5ba1cd6b6c,0x685565cd0ffd21a16ea,0xcd8aac39b155a9342ab3,0x9a556a7362ab4e6c55a1,0x34b6f4a696fe90d2e5d0,0x6d1a69cde90cb9a5a7a6,0xda9ec39b555a636adb48,0xe1ffa43c243506d4fa1c,0xcb97427955ea4f0aacb9,0x248ea4f2d3d31e5bfa43,0x4fed2949fe95293fb2a5,0x9f995273ff0e527fa94a,0x97d524e77e1c9cee4393,0x7fe909f01d193e07a227,0xefc393ddc8727bf72a4f,0xfb952817f4e4f77e9c9e,0x7b4e5077e1ca0ee43941,0xf694a2efc394ddc87299,0xb528c595a518b294a312,0xfa42f43f285e65e9462c,0xd2a5e5f654bcbe4a97a1],#[0xe1cbd05d317a0b962f2f,0x529797e852f2fb0a5e72,0x952fafd4a5e5f694bcbe,0xe5f7fe58beb74a97d6d,0x94beb74297d6d852fb7f,0x396965952d2dd4a5f5b6,0x53032f0e6059a54c0cbc,0xa6148e1cc0b342981658,0x4c2d3c3985569530aab2,0x98555a530aad0a615561,0x2eb2b2a5d1a694baab52,0x5e72654bce44a9799695,0xbce452979cb952f3952a,0x79cba52f3954a5e72694,0xfb7b2a5f6f254bee5d39,0xf6f694bedfca97dbe952,0x4d3cb169b5952d37d4a5,0xdcfa02d8d5525a48e5cb,0xb87465b71e88b6e5d096,0x69e58b6dbca96dbfa42d,0xdbca97197a72db4f4c5b,0xa796302472e5c69e58b8,0xdb0a7069a94c2d2d2985,0xb694e0b6529c16e85382,0x2c29c56fa5382dd4a705,0x685392ab0a7259a14e2b,0xd4a7255694e4aa529c95,0x294e6bfd09cd57a5392a,0xd31ed6fa43da454a7348,0xa7543f2eca84865cf8ab,0x4aa37fe91466954aa0d1,0xa14aefcc28ddc9851bf1],#[0x1b1c3da754a7b4ea90fe,0x657b870caf59ea58f09d,0xcb05b61960bbc32bd758,0x954dac32a9e576552df0,0x2b5b58656bcaecad3469,0x55bc94aab7ae915668d3,0xac3ae8558efc32ade7a5,0x96b6c332d22a9571bf48,0x35b58666bcaeccd5be19,0x4bcf4ac97ae919268d33,0xa4f6a5929ecc325df866,0xc90cc328dfa4651d742c,0x43fa6662470ccc486a59,0xb6b0c9d795d93b09d1a7,0x6d5d93ab3d4a7565964e,0x9f4c271eba44e36f4c9d,0xbfa44f397429e4fea538,0x47529e1ae9d3ccbd3a79,0xf69d3eaabb27d6da44fa,0xed3281218650245509f0,0x3865e3830cbc7b5d9781,0xb0cbc5d5d978bbcb2f1c,0x6197af4bb2f577865e2e,0xd32f56f965eb7f0cbd6f,0xa65d36b0cba795d9746e,0x2cb777e196ef5d22dcd1,0x857053542e53ea95bbbf,0x2ae1b4a55c37f48b872e,0x75c34f4cb869e5970dbd,0xeb865e9d7091cbae1979,0xd76cbcbaeda5765d8d74,0x2f86aa95da4552bb48e5],#[0x5f2ab0cbe555d97cb7d2,0xbf4f5d97e9fcb2fd3fa7,0xa8f2bb3513f865fa7b0c,0x51b5766a1a34cd46d619,0x7bbf0ccf7ae919edad33,0x72e85a0535434d3da96,0xd3d3341b7a56837f48d,0x46ba76832f4ed04865da,0xa4352d54865daad2bb35,0x55619a2aabb3456da468,0x90d43443da768a7b4ed1,0x3f866927b0cd24f5d9a4,0x7f52d67ae91ac9ed3349,0x5e9daedfd235dcba16ba,0x5d4b5d23a96b8d74ed76,0x1a76c07b4ed85be91b03,0xd2ab55b6556a91d3b612,0x6156ab642ad5ff865aad,0xd2ad56f855aadd0ab55b,0x955a3492ab45ba956ab6,0x4ab469e5568d34aad1a5,0x556af4caad5a6a55a34b,0xaac5eaa55abd34ab57aa,0x95894d50b177e1962f2c,0x8b27be8d64f9d12c8a6a,0x964efc32c9e795593d74,0x2cde7955994f50b277e9,0x5b3bf0cb6296a166efc3,0xc277a9568eed2ad0a6a8,0x84be4ab0a1fa46143f28,0x97f95612fd2ac25f655,0x13ef2ec282e998505c33],#[0x25f21584fbd3b097f976,0x4bfc2b097e85612fb0ac,0x97ea5612fb4ac25f2958,0xadb2ac35fe9d84bfd2b0,0x7fe19866ed2b0d6e9561,0xb2cab016f9761bd72ec3,0xdf9760acd0ac459a5588,0x790ac54fa558a9ecab15,0xfe158a9f42b153d8562a,0x4d3b706ba76db8746db4,0x79893b2f31261a6a5b83,0xf52956d65d2aabd4a599,0xea52cd2d4a59a5974b36,0xd2239fba440acd508369,0x9443aaf489348aa124fd,0x4a877ee550efc4aa1dff,0xa10eaa4c21dfba543bf1,0x3a21dc874434f5087692,0x787a474e8c5526110efc,0x8e270691c471d2389b59,0xdd891d2bb167a5763874,0xb7964956f1d742de48e9,0x7017f4cde69e19bcb3ca,0xdf34691c268d237522a8,0xda91d2bb567a576b4f28,0x496795891d7431248e9d,0xa24331122fe9a24d2c34,0x369e522268d245521a88,0x690cb4ac6ba489a47291,0x1cba1960d74d2b48e5a5,0x397432e486965adfd24b,0x4865660d3d34b9219597],#[0xfc23dc6ba497a434b30,0xc9857bb910af787e91ef,0xf92af772e15eee542bdd,0xfe55eebf4abdd7d957ba,0xbcbbde0ba67bc172cf75,0xc857bbef4ef75fe5deef,0xf0af75fa15eebec2bdd7,0xa95eebed2bdd7ca57baf,0xc2bd57fa77baff4af75f,0x977abff2cf56fa15eade,0x2ef165e5de2d3cb3c5eb,0x8de6e3d13cc6aa978a47,0xabcdb49579b7f48f370e,0x6798d74af36de95e6dbc,0xef365e5de6d3d33cda79,0x5e835d3bcd97a779a472,0xbd197977a34f2cf46de5,0x7b34f2cf61a69de891cb,0xf648aa5ec91cbbd99797,0xf0b34abe16595790d552,0xe556957caab2af959a15,0xd2af2ef977e5df25ed2b,0xa4f215f49f4abe93d957,0xc9fc2be93e857d27b0af,0x9a7a683387470671e8a0,0x24753061ae9e0ccbd3c1,0x1a6a61034d3c206ba983,0x35d3c1dc3a383b8f4507,0x6d74778d353091a69e12,0x7b4eef55699deb2c2bbd,0x4e8ddd0bd13b922a8778,0xaba3b967a97736b08ee8],#[0xb947e07b48f06de91dcd,0x708fc5e611f8bcba3f17,0x5d1fabbca3f57ba47e2f,0xba3f977847eaeb08fd5d,0xa77f2af4cfe5b611fcb6,0x48ff55e51fe68d23ed3f,0x12009eba4013f948017b,0x24056d7480a7f09004f6,0x780a7b4f015569a02b6c,0x9036d6120690d44043da,0x204dad240db574819a34,0x4093f848127b09024f5d,0x8587b4f0b55e9a169ed2,0x2f000091d3c2d21a7,0x4f808880e50184024003,0x41407840e5019702dc0,0xc82ce05740a3c1348233,0xf341d3837506920c7417,0x92a11a421e840c07ee0,0xa053e0a44143427404c3,0x94031205f80b8e16682b,0xe661c0436886a90d001,0x287fc0fce1eec3c78764,0x3ec46a88ac1102214441,0x13ce26d84c0094f12622,0x98ad2155a29c85218a1f,0xf685db0b7916be2cec58,0x19e233006488c5118282,0x58dbd1b1035846a18d28,0xaec7480e5f1c5038386f,0x1f5a3e047a60f161df83,0xd109c20d4411c8088fe0],#[0x5ec8a7111b2202439485,0x246648288f411bf23404,0x89335261a4b4c9509272,0xf0a0393d427744e8c9b,0x29f65348a54947f28ac5,0x95902ae85520a9a150f,0xa98b3d964e2c4257c0ae,0x2f445dd8b9e97242dcc5,0x189230e260dcc0497d6,0x668cb8994f323863b8c6,0x34f66944d0f19ea33846,0x79b5d366a6c68d729aa4,0x1b8e269c1c37ee6f0cdc,0x3ae474e0e899cdb39487,0xe9e553c667830eee1db5,0xe84fb81f2d3dda7b08f3,0x4110813501820133fd07,0xf2166425e842d07120b6,0xadd13ea246441e875d0c,0x470e8d9119ea31945e08,0xba452484a90011efa3b1,0x4b527ea4e1498a926123,0x4ba296c92cc25614a8e9,0x1a6b64cfc995931025f8,0xf193d1a7804ea89c7937,0x5154a22542a28274fec9,0xf299152b0a4b947ea8cd,0xae55472a625458a7f54d,0x5764ae015a9ab1f55d0a,0xeac8158cab0fd6092bdd,0x545693ad0659b8b2c964,0x5c26b7a16e9ada85afcb],#[0x82ec15d18b9bd7292e26,0xeb57c5af6a5e9cbc6577,0x6126c1a581ab0045fb2b,0x2b1596246c3e5863b0a3,0x9c5924b21863ccc6d98c,0x66a4cca197bb2ce6542c,0x9b41567f8cf0d9cdb378,0x469a7c34bf6948d225a2,0x6c48d795ad1b57c6a84d,0xb37246decdad1b463658,0x10dc1637fb6f72de45ba,0x721ae38dc60b88d70b8e,0xaba05739ce679cb73940,0xcd9d7c3ac0753ae9b1d1,0x7860efd9de2bba276cce,0x4bd1d79e8f311e483c67,0x899f033dd87b44f5cdea,0x7de2fb05f483e727c80f,0x3fb97efefd39f9d3f10,0x32e050407580910085ff,0x831b05860a4c11081eb0,0x2c27c848b08660f6c1b9,0xdea1aac31c85f30b3615,0x88c110be20243d687510,0x8c5328a11138225a448f,0x8862f6c5ce8b4b15ee2a,0x8de71b1a35146738c9b1,0x947bb8f231da63a04727,0x32244e4873909320a63f,0x931f25ae4a1c91a91d12,0x14a53943f27ca4ecc9bd,0xd3e59b4b0b95b92abe54],#[0x98052fb65e1cb9096c92,0x94cca994131de6254c2e,0x7a26e14d969ac734d267,0x9d8f3a46733ce319c253,0x3cfb89f1f3d7e79acef9,0x35e856d07ca0a5407a7f,0xa37f465e8b4513fa2234,0xdd299a4d948fe908d1e6,0xe7a9ba534ca63d4ba695,0xa915514aa16d3faa7994,0xf5568aa615402a6ad4ad,0x9beb205618abf3573aac,0xae955c7ab7b56caad295,0x15835b0115f7abd35779,0x552c94d8fcb175623ec3,0xb41367aacdcd998b2ff6,0x85ad8b53f69d2d23da33,0xed6dcb5b68b6896c56d7,0xb89370b2e085bf4b7ad6,0x8dcedb989729ae43dc6a,0x66aebfdd6eba9d74bee8,0xbc6b787eefbddd9bb737,0x45eaabd377a32f3ede52,0xccaf8bdef9bdcd7b5ef6,0xbf597e62fbd5f66be8d7,0xd6042c0558036ffc5fd0,0x3c3063e0a4c10981bf02,0xc2fb857f0a4e124c2258,0xe225c40f87a30e4e19b,0xb8f15e629cc4f5897712,0xc6e18d4719de31cc5f18,0x6398c7218e231c06378],#[0xf231e063b8c7618ea31d,0xc7e18fa31f063d8c7a18,0x6418c821902320063f8,0x1232206438c86190a321,0xc8e191a32306458c8a19,0x6498c92192232406478,0x32326064b8c96192a325,0xc9e193a327064d8c9a19,0x6518ca21942328064f8,0x5232a06538ca6194a329,0xcae195a32b06558caa19,0x6598cb2196232c06578,0x7232e065b8cb6196a32d,0xcbe197a32f065d8cba19,0x6618cc21982330065f8,0x9233206638cc6198a331,0xcce199a33306658cca19,0x6698cd219a233406678,0xb2336066b8cd619aa335,0xcde19ba337066d8cda19,0x6718ce219c2338066f8,0xd233a06738ce619ca339,0xcee19da33b06758cea19,0x6798cf219e233c06778,0xf233e067b8cf619ea33d,0xcfe19fa33f067d8cfa19,0x6818d021a02340067f8,0x1234206838d061a0a341,0xd0e1a1a34306858d0a1a,0x6898d121a2234406878,0x32346068b8d161a2a345,0xd1e1a3a347068d8d1a1a],#[0x6918d221a42348068f8,0x5234a06938d261a4a349,0xd2e1a5a34b06958d2a1a,0x6998d321a6234c06978,0x7234e069b8d361a6a34d,0xd3e1a7a34f069d8d3a1a,0x6a18d421a82350069f8,0x9235206a38d461a8a351,0xd4e1a9a35306a58d4a1a,0x6a98d521aa235406a78,0xb235606ab8d561aaa355,0xd5e1aba35706ad8d5a1a,0x6b18d621ac235806af8,0xd235a06b38d661aca359,0xd6e1ada35b06b58d6a1a,0x6b98d721ae235c06b78,0xf235e06bb8d761aea35d,0xd7e1afa35f06bd8d7a1a,0x6c18d821b0236006bf8,0x1236206c38d861b0a361,0xd8e1b1a36306c58d8a1b,0x6c98d921b2236406c78,0x3236606cb8d961b2a365,0xd9e1b3a36706cd8d9a1b,0x6d18da21b4236806cf8,0x5236a06d38da61b4a369,0xdae1b5a36b06d58daa1b,0x6d98db21b6236c06d78,0x7236e06db8db61b6a36d,0xdbe1b7a36f06dd8dba1b,0x6e18dc21b8237006df8,0x9237206e38dc61b8a371],#[0xdce1b9a37306e58dca1b,0x6e98dd21ba237406e78,0xb237606eb8dd61baa375,0xdde1bba37706ed8dda1b,0x6f18de21bc237806ef8,0xd237a06f38de61bca379,0xdee1bda37b06f58dea1b,0x6f98df21be237c06f78,0xf237e06fb8df61bea37d,0xdfe1bfa37f06fd8dfa1b,0x7018e021c0238006ff8,0x1238207038e061c0a381,0xe0e1c1a38307058e0a1c,0x7098e121c2238407078,0x32386070b8e161c2a385,0xe1e1c3a387070d8e1a1c,0x7118e221c42388070f8,0x5238a07138e261c4a389,0xe2e1c5a38b07158e2a1c,0x7198e321c6238c07178,0x7238e071b8e361c6a38d,0xe3e1c7a38f071d8e3a1c,0x7218e421c82390071f8,0x9239207238e461c8a391,0xe4e1c9a39307258e4a1c,0x7298e521ca239407278,0xb2396072b8e561caa395,0xe5e1cba397072d8e5a1c,0x7318e621cc2398072f8,0xd239a07338e661cca399,0xe6e1cda39b07358e6a1c,0x7398e721ce239c07378],#[0xf239e073b8e761cea39d,0xe7e1cfa39f073d8e7a1c,0x7418e821d023a0073f8,0x123a207438e861d0a3a1,0xe8e1d1a3a307458e8a1d,0x7498e921d223a407478,0x323a6074b8e961d2a3a5,0xe9e1d3a3a7074d8e9a1d,0x7518ea21d423a8074f8,0x523aa07538ea61d4a3a9,0xeae1d5a3ab07558eaa1d,0x7598eb21d623ac07578,0x723ae075b8eb61d6a3ad,0xebe1d7a3af075d8eba1d,0x7618ec21d823b0075f8,0x923b207638ec61d8a3b1,0xece1d9a3b307658eca1d,0x7698ed21da23b407678,0xb23b6076b8ed61daa3b5,0xede1dba3b7076d8eda1d,0x7718ee21dc23b8076f8,0xd23ba07738ee61dca3b9,0xeee1dda3bb07758eea1d,0x7798ef21de23bc07778,0xf23be077b8ef61dea3bd,0xefe1dfa3bf077d8efa1d,0x7818f021e023c0077f8,0x123c207838f061e0a3c1,0xf0e1e1a3c307858f0a1e,0x7898f121e223c407878,0x323c6078b8f161e2a3c5,0xf1e1e3a3c7078d8f1a1e],#[0x7918f221e423c8078f8,0x523ca07938f261e4a3c9,0xf2e1e5a3cb07958f2a1e,0x7998f321e623cc07978,0x723ce079b8f361e6a3cd,0xf3e1e7a3cf079d8f3a1e,0x7a18f421e823d0079f8,0x923d207a38f461e8a3d1,0xf4e1e9a3d307a58f4a1e,0x7a98f521ea23d407a78,0xb23d607ab8f561eaa3d5,0xf5e1eba3d707ad8f5a1e,0x7b18f621ec23d807af8,0xd23da07b38f661eca3d9,0xf6e1eda3db07b58f6a1e,0x7b98f721ee23dc07b78,0xf23de07bb8f761eea3dd,0xf7e1efa3df07bd8f7a1e,0x7c18f821f023e007bf8,0x123e207c38f861f0a3e1,0xf8e1f1a3e307c58f8a1f,0x7c98f921f223e407c78,0x323e607cb8f961f2a3e5,0xf9e1f3a3e707cd8f9a1f,0x7d18fa21f423e807cf8,0x523ea07d38fa61f4a3e9,0xfae1f5a3eb07d58faa1f,0xe13c3f07c2f03ec07d78,0xac1806819d1411e141c,0x9202d0b3440bac5c124a,0x246c8c2816b04c871585,0x6c10706c332b0852184],#[0x7214a0a44a7134870e88,0xd0c51c1519f1015b1108,0x516113158aa150a02a84,0x1221986884f1485d29c0,0xa8c1240050128a914c3,0x2238a910cc90f88445c2,0x78085060a46a0862104,0x8124907427094220844f,0x1164c5310510d4346218,0xa458932428526c04b450,0x8c140801f3118772991,0x15e2d132101088360c26,0xb08c251c5231d104248a,0x2246ffc68000447e0cc6,0xe9fc8008566dbfe34000,0xe00109e1e9c420005866,0x20090a1fdf80128ca7e,0x209cbf3f2000119b9ddc,0x89fcc000042c35bfcf80,0x211e7ff0080a8cc4101,0xd1ffac24000333cfc440,0xb54f0004a42eff2000a8,0x8081170fef401ca00141,0x90b0f88001090abdfe,0x34fe1fd20010912f8840,0x32fe5040208fbee8002a,0x90bbe4e3d0005484040,0xb2f88400090b0f88001,0x4a7c0013c233f8802009,0xfa420190100d6f880038,0x5464e3fc0000021a1,0x423f69f0020119b7f9],#[0x658fefc009465dff3fc8,0xf8fd8000466afefc0804,0x7ce00108ebfe60405462,0x4000b0ddf4f90010acd9,0x470fd3e40402b363e988,0x8b4f0004e42afe280004,0x54620203134f0080242,0x8cddfb7b1008cabf3c44,0x571f020090adfd6da100,0x4f9e000a8cbfed040546,0x7e80a0e9f5ec80000434,0x4680fedc0001033b,0x507f6e0000819e3fd038,0x5c002140f9d50d000022,0x11a4ff78f000214de,0x1a9fe3f80811dfcd2480,0x223e7fc942880001c,0x2fa02835e56014144d73,0x80a33fe4b84000008d,0x691fffa0340001126f1e,0x20955fe0012000004,0xffe5000108ebfffe0454,0xcd0bfe8680006485,0xfe02033740407aff2090,0x8248008683f2780084ed,0x1613effd2800088f1fe4,0x400005877d09418fdc0,0x5476ffb680012b36bfa0,0xf41b100002b4affd8000,0xb60000a1a19828082f5f,0x8e3ff1bf80020488fc3,0xffa400000ace38ff0001],#[0x20008911ff6d00005666,0xa122ff9002130ffd2fc,0x611ddf42c075ffcc000,0x3e80a0cfb0100fbfe000,0x8000a1217faf5c001024,0xef005087fbec1c046f79,0xdbdf238083fcf900213b,0x9090000434edf8400811,0xb0dbfef8000211ebd3e9,0xbbf0402024c3f3000010,0x8094bff0080a8c3f7e,0xf80000050ce3bdf5efc8,0x4676f0a01981803b7,0x22ffae80002b3d7fd080,0x8141ffe400a09df40406,0x9cffc9800a4f7ff0801,0xf900293814031ffe400a,0x7bfff10038280280627,0xa919fe8000028677d808,0xfe8000028675f8d40000,0x4000959932f90104acd9,0x8019a67fcc0002a387db,0xd8800015a6bfa7dcd800,0x50d0980808af4fa0,0x12071fe000211c3fe1db,0xa00000159f7fc6fe0008,0x1b457fa900008cd1ff,0x521edf00c105c3f93660,0x719cc0407489fc980001,0x18675ff60000a123,0xa005050ff7c0083c7fd4,0xc00809effec00149efef],#[0x40aebf50c600081a0ffe,0x59cec0010537f719d800,0x620000056abef9680414,0xefece42c0040591edf4b,0x4053bfa800088c5f0141,0x3bfc8400c341fff26400,0x101457f673b000415d6,0x400f7f9db90020293f16,0x49df585f30001125fbd8,0xa80003a56ff1c7200005,0x38683eb2010142ebac8,0x1380001c1a83f5f26b40,0x64839c9e0504e1ffe8a,0x1359cf800728dffa9000,0x60d6f77b60801273e014,0x111e3fd6b59140000,0x3ff727e2a0000e9537f5,0x6488fed0f0d80000a0d4,0xf14000020d7b5fc68000,0x337ff00003656e1ed44,0x900030d0f7405077be02,0x1d2f9e9001048affed61,0x1e7c90060a12f1f40061,0xd84010008439ffbc0c04,0xc1267fe6390000c127df,0x8404008344fff0620000,0x242fefe100101a4e7d7f,0x402060933e33f08200c1,0xf137e120018254f3fbf8,0xffbb020107fc84010289,0x39fb002027bfcc80404e,0xe673d006052bf9410032],#[0x517fbc02026bde010135,0x35fef008098cffcf1050,0xc67fe7880828bde0101,0x2a001090ff0200cfd820,0xcd07404041d01011bf8c,0x41c5c30084fcbe101000,0x4464ff00030caf9f01,0x9679fc400001049dfd40,0xbfc2020021a23e100061,0x400c345efff28040a33e,0xe9f20200199d25fdb860,0xd7c200897d620023852f,0x9a0000119ddfb608043b,0x103347f840000a19e3e,0xf3cf6b800010490fd380,0x88efede04021fdf0400,0x3fd0000050cf3ff9a800,0xe240060495fca080191f,0x11a67be800020903d7c7,0xc500c0549fdbaee08000,0xe173aff08080066889ff,0x3ff5000111bdf600000,0xc201005879fcec000409,0x23f7595640001b4591ea,0xff0200006481f0bf4014,0x20923ebf00081187,0x2230fff2000151e7e231,0xff4080afdc080a3f2a00,0x1846de2bc4081190200c,0x801235ff1080947f07c0,0x15187f07840068fbc578,0x2effd40028461de3e80],#[0x180802cfff0002046608,0x6222f1031137ff800081,0xcd9c23c808006685e20,0xbfe82005464ff901001,0x77c03110bd479010010d,0xc8f7fc414135ff20809,0x67debd040108e07fd040,0xaf410020939ebc808005,0x1384020ef1f400a8c227,0xbff7840040a41ff0004,0xf7840204241eff910705,0x208e7eff9402050bff,0x9f7ffe0000411d7ffe20,0x1f0001047a8ff20200c1,0x208f79ff40504ebff,0x1196f5f3d006053bff3c,0x51ffbf4100423d7e5200,0x7bbfb00809ebdfc80036,0xa51ff4c0101457ec0042,0xd2f0350755ffb2000002,0x2a4c7ffd80000000a,0xb406073680c11bffb200,0x63808dffd42000028253,0x15247dc800611dfab,0x351f9f80282753ffeaa0,0xad35ffad400000020,0xff28000548affd520000,0x546dff5f28000548dd7,0xb6e8362000306a5ff804,0x85865f1f1000a11ebd,0xfec57f8200c1261f9800,0xc400060d4bff0080a8db],#[0xefe84000103397eed0ae,0x40007487c1003302007,0xebffd7800008913ff3,0x60537e7f900193bfb784,0x7c7e8002047bcf0dff00,0x7000e1227ff17200111e,0x8f9ff140000061a10ffa,0x9e40000893bff58a000a,0x600e5fa7800004679ffa,0x91fe3f8000005497ffb0,0x119e3e5db5d2000306,0xff9790200081a23f8100,0xfe00000a8e6f700609eb,0x6681f7e3f0000011267f,0xfd9801c1427f14a40800,0x4669ff9d610020483,0x470a7993c02828cff840,0xa3df9fe40064f2cbc000,0xf342000419c7d75e8002,0x40149a373f98030296ff,0xfd7000020487d0a01af6,0xfd0020010866fc014227,0xde0064bbfcd50000a914,0x151d080177f9e0020463,0xc7e00003824cfffc0000,0x40693f4fc0304e3ef,0x7df98400a8d9fff94e00,0xfe6e000c50bf3ae00284,0xe6100c23eff07800346b,0xc7c300005497b80a0c33,0x85f800010cce8500c3d7,0xc4000089385f800040cd],#[0xa5385f800008ccbfe6,0x8fcbfa10100cce49fcc0,0x79f3005051bf81000347,0xa7ec0404e49fcc010053,0x70304d3ffe6400000549,0x4471ffbe0800d1cefe,0x661ffbe0800d1f7e3b8a,0xc7e00001033c7e000020,0x6800c144e39f90006488,0xdb004279cf11001848be,0xdd0b01d7e61000547bcf,0xfe02022368fc200088ef,0xffc0141efbfec00c4fab,0x2000891bfcee0000a092,0xc00414aff808088b3cf0,0x20159aff000a09cf2ff0,0x347e7ae80002b3a65f20,0x404e7ff84028277a020,0x2c39fef08060507fbe8,0xfd200000e1cdfcea4000,0xce38008507de808106eb,0x700028483ffc200c139f,0xb000005673ffc040619e,0x2239ffe100a09cbfc,0xd0002a41ff0802934f32,0x121e80a0cf98600e3f4b,0x66f664004344fd44000e,0xb00a0a07ff0a000223c7,0x4484ff08000e335ffec,0x197f14001623af7e6800,0x5fe1040547210033d094,0x323ebe6c801004869],#[0xfffc100e0a08080d3cf1,0x3a7ed60001199f30c01e,0xefc3e4028283ff320029,0xa64c00011a6ff9900809,0x3385ff100028484fafe1,0xe0f800111e3fda80000c,0x5ae000647dfee000d147,0xad3980046ce4fc010967,0x80046cf5dbe000232d7f,0x21e58f0000233d7fad39,0x8cb98e786f000100d,0x1a367f8f000023347f88,0x44fefe8002047dfd6820,0x7000e122bf8e0c000043,0x4671fc6000c11d7fdae,0x4aaff108088c1f5f0000,0x8007090bf589af500182,0x4673b9be010144e3b3,0xc145cfafc1013d787640,0x91bd5e280611cf93a01,0x3ebc4202a3ef58f0006,0x9b7f0064cbe07a800447,0xf9c400a903fe671001a3,0x546efe94200219978f3,0x151f7cce2008479fce20,0xc7fcce2003471ff32e80,0xe4800e501d3f40000219,0x40995ff0020040221ee,0x40cd7ddf20104e77f4,0x3684ffc40000466cfa80,0x162042848effd2410000,0x18a09fcde50140a47fff],#[0x405467fb80a0d7f97900,0x4144e35cf0006481fce0,0x17ffad62040848b3d200,0xfb2fc00c9cfdf794040a,0x87000e1227e39000051e,0x40161c7f83800088e3f1,0x75eb8800051c1faba200,0xd37b1006ccbff0800044,0xe0411b29bd124408e15b,0xaed2fe9bd8800da6bf9,0xe781046ca6f449101c85,0x67a10035a5e0002385af,0x575fc50000a907990052,0x2eff3c00108c6fc00c9,0x3665ff84000223a10,0x61ebf8e18000224d630c,0x80105367c80202874280,0xccd663fc8020273c3ef2,0x9548c9363d4d120bf08a,0x9630b0796307a7920dbe,0x13c59b8c9df144630b07,0x22520d2dcf0b22cd2f51,0xe4dfc8c9ca32d4888587,0x11911864a41ebd1c9069,0x3920f3cb0b1af10bbc70,0x293d1a907dd25c2c92fb,0x5fc2c7c47c104ab8ca43,0x5b22b645dcdb35521992,0x8ad915b2217b3920ed91,0x18a4f7a218bd9c9079f5,0x311933f1895fa3920c3d,0x865549f094842fc626f2],#[0xa930e8c6ab682cf6faa0,0xa417bd2086d6a886d6a8,0x287d38a46457e8e483f7,0x909235f98644ff92340b,0xa41c0dd05ad10374841a,0x9149eab341cae907072b,0x1c527e264a42f42c892f,0x160f2c6160f2c789b4a4,0xb9440965a719216c8906,0x4c6a4105b82c94a4daf0,0x4d512288748324523748,0x4510e907e]]
set_option maxRecDepth 32000 in
def g255H9 := limbs80 #[#[0x648001300c3a81e0028f,0xc10b10000071a100020,0x820e0400b85082420428,0x4810000405222410d6a0,0x11808009042c3091800,0x13410108000c38700181,0x64c004360001d021418,0x89660430a0024302,0x100990e1d10500044800,0x4c010c34a04001d70000,0xa0102005042428100020,0x2248808000042b22810,0x60214400040010076843,0x10180040edc20c0c3050,0x85490e4a4009a1401104,0x1c2974e2c406860c2060,0xc001022c3290c0019f40,0x5b40a142882210004dc0,0x1906083810e080056034,0x64c798023c5840c44c,0x59f5c700000,0x1c000000b31b1c000000,0x9913f00c473840004050,0xeef0a,0xa70e2a8533e000aec000,0x34449518896c90000000,0xed5b428dd1d2b390004d,0xe8de6a1c57338dc84b8a,0x399ced745558fc96919e,0x96ec06d952728e13279a,0x2190006f8189000,0x80e0000f0e410000e9b0],#[0x13241f6da00047200058,0x88000b8ee2443a000000,0x6000586295f65f080000,0x692000aea00000013f19,0x4188945ea53e,0x81a000979000000ed60,0x36a65229ed654b300,0xdf125829f5b9e7c59000,0x8ac79ba330ae4000e269,0x9ecea9000621f091b,0x28620dd371bdce000100,0xdda1f475e36e0478c656,0xdf25ac41eee21f92404a,0x9c4b02eecd0176b2e000,0xec210002508db38bc376,0x9b3f41654f68000000ec,0x57756cd8e7b4bfe80139,0xc591c48ac6e03607aa78,0x70684300090d00063136,0xc69d3a383ce6b86201,0xccfd498000a81b6e4280,0xad98f077adc5415416a8,0xc4b5c51d8bc4be23cd99,0x80006f296b45b143d27c,0xa17000ed45674e4b7,0x85d8e769897000000449,0x3192d23575d022f286d,0xf769ed55b2bde1f00,0x91203d000000a4ff67,0xbabf52f842e7e2bb7130,0x4230912e1000492ebaa8,0xca49f0000000000005da],#[0xe000000e5805aee3a6e6,0xd07000af785,0x2c000677d83000611a32,0xd1c40000008ba000000f,0xd2d6cd000c1217cf0,0x1ca0000002ff,0x4cd20006150001fdda80,0x1a6344202771d188a29a,0xf2b7ef04ccc83e291f73,0xd000ac06bc24b41107b4,0xc0e20b8a54776af000b4,0x12e470001229bb000000,0xe346b4300090ca369363,0x89b0003581e8f70a8ea4,0xb6000d5f980c640000c1,0x4c3357f000b640000002,0xe2bb5f48f4ae0c3af4c0,0x37935921000caa000000,0x1000cf8530082dfcd02f,0x61af16d9021b5dbb5,0x58d1cf981000000,0x566d0004303798bd0000,0x187e46f77d69a574ee0f,0x2e68c9de2c38f26000,0x45a087a5efcb90b40000,0xc7e0006b3e0800095441,0x225bf0009aa84b000c61,0x5156340000007,0xcef00004f00000000,0xb5000c6700000065625f,0xe5da22c46703133a,0xf14531000f5055e00000],#[0x514454870000b2000cd6,0xd481c5c0680f1439204e,0x156cab83bf8575ae2327,0x7eb360004e9000f7bdd5,0x4d9aa1450a2001d9a769,0xf872d340a663000c7982,0xb8e89f55df7e6026a192,0x28a42e7031546b6df5de,0xa0deeb2c886d6b977f1a,0xfe00027c0000005fe5cb,0xe8a7f25a70a2,0x2abe27d702cf5824a000,0x69df7c000123000860,0x646ca99b02e1d0005cd0,0xdd640b000000e55f116a,0x36000db4a3a33bc93c00,0xb64d9fb63dc0204d2338,0xc502aab1eaa111ea2d2,0x43a84835000961503630,0x8e7a12dabd77b82d0f6,0xe5bd531dc2056a433400,0x3331836ff1db3a68ae41,0x33f863000000453d9ef,0xf802c448dcc7e0c97200,0x7f0004f4000ee5000cb8,0x351f6fa4a1760566148c,0xe35ce367192956d0facf,0x9ad1a5a53499cc5bce7a,0xcd52c7c5ffc8c6100000,0xc54c6ba1ecc208a00093,0x20140e6cb881756a14f6,0x306f44c1040009d7d8a0],#[0xadcdc065c6b2e53c74f6,0x285dd00038f2492dbcbb,0x44ca80c486598cb1b38d,0x82d00022e72a81700096,0x2ed1e41d761000000f10,0x3b4f0004d74500000008,0x8eaad8d74819edf2c,0x1c4a000000b62f2923e,0x5955a3714b0000009c95,0xea500000dd5034b000a6,0x580fed3b000000a97000,0xe07dc5f33dcff5e00004,0xe61000000000c8,0xa068d4fc0000a6b74000,0x4a0f5176649f400042b2,0x89d32f000e7980f1d,0x9c000875f89000000910,0x1707dbde2da5e0000008,0x1b9963781916000062ef,0x75b66000225b2d000ec1,0x4909deb000499d427282,0x557547490a4a20a72569,0x48eaeb23194141dc802c,0x89b7000f356666a30007,0x16f1b24cf70cb726b45d,0xad00052e4a86785a7193,0xeeded110e7750000086,0xd41f01ad00054400,0x568a366fc4173c332524,0x7000031f0005f1d4a4,0x26000000f2126b4838c,0xb7c76000000568d5d000],#[0x6000000a59c320006f6c,0xd498cee09cc6cb,0x66d714510000004f7000,0x92c0009f50009065600,0x644ef548b00058be7300,0xdac0343f000d6c301645,0x94fb409158000007f0bc,0x31734ac01d2a9e94409a,0xc1d5902786a000a836c2,0xe4c4de480000eb7f15d,0xd6a0005e123f85209e00,0x64274535ece52b0629,0xc70fad09973900000000,0x6700001c69de9ee05dac,0xe6295cc34000,0x1c2000000d080,0x46ef8c2e9b1a00000,0x9569f5fa17b0006de000,0x4dc18457800054e000c,0x5f368fd8c1f600057a00,0x248f9000d9d0000004cb,0x2b7d926000000d3813d3,0xa2ab400ed4af690f5,0x4250001aef54efd,0x74c000ef90,0x1b1a48000000a9a00,0xbea1329894fedd000134,0x759000af3e16f05000a,0x413000f6bde4000000b2,0x692965c3000afc95a000,0x850bd1c0000008ac0006,0xd90d122c34e00042f26],#[0xdf9b60009b501bf53cec,0x44ec220002934b531e8,0xd200000001b0a3b00,0x450000001f8d37000000,0xe186f0000114000dbe1,0x1af000ecb51b28700,0xde5e0e00000027472b,0x9620004eb0000000000,0xd4c0008c800000000,0xa38000000000000000,0x1eac00099b0006880000,0x6060004d5c73000000dd,0x54d000aa80002c52fb,0x10500000000063917d0,0x88500000083ce8287100,0x2678cd]]
set_option maxRecDepth 32000 in
def g255D10 := limbs80 #[#[0x5955421d546187561075,0x619545d9545d5545d154,0xa1d549d5549955461d54,0xe1d54e1954dd954dd554,0x5d16421d64215641d564,0x61d64615645d9645d564,0xdd564a1d64a15649d564,0x5d56521d65e1d64e1564,0x9d56561d65611655d965,0xe1d65e1165dd565a1d65,0x5d9745d5745957421574,0x9d574995746197461574,0xe1974e1574dd974a1574,0xe0d7561975611755d975,0x6117621576e1975e1175,0xe1576e1176a157661576,0x5da7561e65612655d665,0x5975461e7561a7561275,0x61f5461b545db545d754,0x617745db7459774ddb54,0x61b75613759977461b74,0xff3f67dcf76177661376,0x7f6fddf7bdf77edfd7f9,0xf7beefdbfaff3fdffbfd,0xff6febfcff97effdfbbe,0xeffbff5fe7fbff5fe7fb,0xc4c0e4c47ffffbfeffbf,0xe4e785c897019338aae,0xea81c9c60393440f2488,0xaba84766508eaca100e4,0x4779508e92a11d9d423,0x38608830c118dd8230bb],#[0x63f280d8e1c23043844,0x70c0da5d81bbca033b86,0xc665c19fc3833d8706d,0x65c49fc3893d8712372e,0x28fca0523930a3530246,0xc30577940af72614de1c,0x55c870a372c14fe1829e,0x96147f0c28f61852fc38,0x83b28306a6050ccb8a19,0x3018e618306cc0c37871,0x43e603074c060d980c19,0x60686cc0d19951a3b283,0xa1ca073b860e372a1c3a,0xb8e0f970e1f2a1cfe543,0x259204532208b640106c,0x8046b0e085658110c982,0x6f0e206e54411c9880e9,0xa20fe54421ca08479310,0xde1c58cca8b0f96101f2,0xe39ec3c769768e1b2c3c,0xdc9c83f988e372f1c665,0x493f9890372d20f61a43,0x995981f3124366249cc3,0x261f2d2c3e5e506cc4c1,0x10e4dbe589b6bb134385,0x40a644816c810638726c,0x65880eca102193204b24,0xa11c9940e98201b30405,0xcc180f98281d30503260,0xb1596363b286c3a60c06,0x942c7b0a443a60d86cc1,0x23b2864a644c8bcb161f],#[0x26703660c8acb193f853,0x4365ce1cbb1c45933843,0x4092dc39558872adf285,0x10c992259224532248b6,0xc12358724352a4866549,0x17962e3f285cae44b874,0x52e87285d3e44b9bc397,0x2b2c687650d1dcb170f9,0xca43654e86cc1a378734,0x3e614874c290c9852b2e,0xd5074c2e0d985c3b28b8,0xeca2f3f85543f28a88e4,0xac2393587b0aa0fe1578,0xd9664232ec0fe15809cb,0x56c728acee1958fca2b0,0x72eb4ae456894c315b86,0x3565da69ec2cd0d95662,0x616887cc4d0d989a730d,0x707cb4f47939e1b3144f,0xbaa61b95421f2b40de62,0xf0d974c72ec98f9d531e,0x933e6f0e7c5e58f91c99,0xed72c7da5d8f8dca1f7b,0xec8c66511afc39f5c873,0x4565928d4c23199746d2,0x550344aa00d984a6f0e9,0x16c81e5b8740b10e81ae,0xa1e21933c4b2478a644f,0x2792441d3078d61cf0ec,0x2446f0e886e55111c9a2,0x7f2a883e51123c9a24b9,0xe90665521dcb220f9544],#[0x3e5e09ebac10d944e6f0,0x211fcc401b9480f72700,0x1cb004196001f2c003e5,0x373b94027328043e500a,0x7866e8b0cdd1e11ba2c2,0x6e8aecdd1e51ba2ca374,0xb2ce08e4daa3cb374596,0xd89e49b1dc3341b95681,0xe56187cb440d94724726,0x323c9c60f948a730d0c6,0xca530f96a41f2d183e52,0xa0d957c272eecae45d87,0x97784726f09e49e1ec2b,0x81b28fc465de9fc2bd13,0xec103e52aa3c9d50f95a,0x20e58240cb0483860902,0x182bf43897d871301301,0xbfc3057d760a672c154e,0xb0c538618faec29fe582,0x51870cfd2a19f654318c,0x80ca330194260329c386,0xa50e39461c729cc06529,0xc094a5c728cb8e31971c,0xc6585a9cb08339610632,0xa43ebb487e978efb2f1c,0x8cc49518792fb2b25f65,0x4b529794a32f294e624a,0x852704ea4e05d49a8cb,0x27070a4e0a149c0c2938,0x72a4e0a549c0ca938095,0x521e4ca18cc108387270,0x61ca38bb147e8528fb0a],#[0xc19cc14319828a70e514,0xc398518730e2ec61f614,0x1319836633060c65cc29,0x942c632e45461c8b8bb1,0xca30e59ce58b38bb1683,0xe65c5d8c99cb9653872,0xc660c98cb99538732a3,0x54a98cb9c518738e2ec7,0xb9ca9572952ae32a55c2,0xa178f912e632a49ce1ca,0x53872ee72c5cce54bc1c,0x52ea52a5d4654ba84a97,0x632a74c660d18ca9a539,0xaa5f5d54a94a9d51953a,0xc5d94bf42a97d8552fce,0x14984c29339752632ea5,0xebaae3398526530a4c66,0x2e31985c632eb9f61573,0xf8554f90aaa1e4d5194c,0x5e672ca94e19532bb2a7,0x32cbd4e197b2bb2f7f85,0xa195d943ec2a831985e6,0x659429c328518650ceec,0x641ca2c8793586530a0c,0xc32c677658caecb1fe15,0xc679758672cb14e19628,0x7660caecc1fe15819cba,0x632cc14e19828c33067,0xcc99dd9932bb3231976,0x945d9918cb32538664a3,0x19599caab839456a32cc,0xb34aab659556c92aadce],#[0xaad83945b1f22b59e555,0x33975acf2eb5ce19699c,0x566a32acd4255998cab3,0xcb2b399256729cab3529,0xb414256833cace66959c,0xf5d5329cad05295a0a32,0xd32943a651874ce2ec99,0x8cba653754ca2ea98c65,0x257f943e67287d4a5d32,0x9840e72881c651018ca,0x48a72888ce51118ca1e7,0xb29014a5e0a8cbc13194,0xdd46500a8cb00519484f,0x619c19cb3553866b0aec,0xa28cb38517670632ce14,0xca367f9568f92ad0ce51,0x3517688a328e4c651c99,0x95a4a3310dfe56199ca4,0x6a3294d4e5a928cb5251,0x8ee3e45da8cad35394a,0xd4a15da8c2bb50857707,0x5ddb9cb3b339576a70ae,0x28c2be50857c672eed9e,0xabe31957ca70af94a15f,0x53957ca52af94655f284,0x2786530e9f615d18ca3a,0xff0af0ce51e43c9bc8b9,0x8f4ce5de33cbbc739678,0xc651f98cbbd7f857a632,0x6a28cad45095a8a328fc,0x9c294918528a72b514a5,0x14909829270e52461ca4],#[0x187312730524a60a48cc,0x2f212a5e4e14dc9c3989,0x12ab646197c8c32a9395,0xee46521c8ca3493955b2,0xa603484c06939577212a,0xb49439691872d230a6e4,0xcb9692972d232e5a425c,0x791952f250e66461ccc9,0x86552730a642614c94a9,0x9230ca245d9449c32f93,0x2cb24e19648c32c91765,0xa4e19848c33091766127,0x555c8cb3291866522ecc,0xc9caab929557232aae42,0xab393975b252ab646556,0x9394872728d24a559c8c,0x577250aee4615dc842bb,0x272eee4a55dc8cabb938,0xafa4655f4942be91857d,0xc800048ca3f939479252,0x2200388058008700b200,0x1f6039e06a40ba81420,0xd416882a404f2091810f,0x73e0e0c1af033906380b,0x436083810041eb03ba0,0xd426204a908fc1190228,0xb3415b42a9053b0a2013,0x86380c4018042eb05b10,0x9036486b10d2819c0329,0xf5e1e083aa87270e181b,0x8837103a1fe03ef07c30,0x5845e08a0110a21ac428],#[0x312258049a091911e023,0xa2b142027e04ee89b21,0x6c5638ab015022998529,0x7062d985a58b33160e2b,0x8c42184c30285ef8baf1,0x1066e8cb6193e3220635,0xb5636506bc0d521a5234,0xe781c9a38886fd8dd21,0xd07ab0f381e0e3b5c754,0x38401c7f28fb01f243d,0x90ca213e41cc82410332,0xe08c3916022704460875,0x4ae489890911f423ac46,0x932125ea4b2c95612832,0xa4a0813e0275e4df89a6,0x9ca52f4a46145f288e50,0x95842ade553ca93150d2,0x6cb2316142bf6573cad1,0xe2c5ba4b6696b92d1859,0x97ce2f565e14ba917342,0xccc469864306a602cbfb,0x31e659cc9b990b31b262,0x9a4a34606828cf019bb3,0xecd871ae6357a6a60d39,0x7f86f64dda9b9136c86c,0x9cba392e71d0e281c1e3,0x48eb49d433a3073f0e72,0xc567800eee9dc13b5276,0x9ed03d447a18f2f9e433,0x58fd61f7e3eb47cd8f82,0x1008191026203040087f,0x213d420e83ad06b20af4],#[0x210f821d9435c86650b6,0x55c8a151352247444888,0xa340462c8bcd16e22c54,0xb920423d347608e191b1,0xa1c9365255248148b690,0xa5dc4b7296512b3a5374,0x25357a6844cbc98c5301,0xf409de13a7a7204dea9b,0x285a5070a0493f427c44,0x4d497290951c2a2cd441,0x448a7e54ea29a9530ca5,0xaaea559eaa9d53baa4a5,0xed5cf2b8156a6acd958c,0x8f8b145613ac0457bcae,0xad2459f4b37d658ac975,0xa96e02da55b14b5816a2,0xcf0b97171fae225c0ab7,0x2f375e3abbcd76a2ea75,0x897faafd85f5ebe117af,0x1f0c351853b07a609ec0,0x31ea6378c6058acb1256,0xf1964b29b64d2c8f5904,0x7c0cecd9c3b35b665ecb,0xb48c68dad109a1134016,0x15aaeb52f6a0cd369a5d,0xc72d861af335c56b4ad6,0x36d96d72da61b3c36586,0xd1be3378c6ebcdca9b7c,0x176e24dc33b83e701adf,0x39607278e469c7c38d47,0xc1d0739ec7394e679cc0,0x5c6eb1dd4b3a7474a4e8],#[0x3b8176c4ed09d933afd7,0x71e16bc0877d4ef41dd7,0xa60f449e703cb77922f1,0x3deb7b82f689ebdbd567,0xc1f5e3e957cdcf90df0a,0xf6afe51fb73f457e2cfb,0x406d8091009e002bfe77,0x42098411181c502e2049,0x42507c20e841a7830505,0xc2b6851d09c612a42328,0x621b7c34b864f0bfa168,0x8ab10b6202c3e787850e,0x451a89ed134a25244828,0x722f9c5d28b3f15b229e,0xdc11ad634946648c7b18,0x479d8ee71d42396c7038,0x2a42c4832901d1faa3e0,0x29f24b2484c8ed917f22,0xca0f93db271e4cec9739,0x2e56c4ab69509295e519,0x7c72eaa5bbcb57965d2c,0x4c9798e53146616cc0a9,0x426b6cd429a2f33b6663,0xcc538d27054ddf9b7736,0x4f1e9df73b5a759ce909,0x467f74fc99f373db67a2,0x1a542b68445059a06940,0x51aca2ef4546894d0f5a,0x5a939524ea44d48028ed,0x6b34cda98852eda58f4a,0x5421a7ed4f269d15382a,0x3aa7854bfa93351c2a25],#[0xb79566eabb5553aa6954,0x566eac9b58b2b04d5dda,0x56b86d705adc75b06b4e,0xe7b5cd6b96d725ae3b5c,0xd765aebb5d56ba6d745a,0x56bc6d785aefb5dd6bb6,0xf7b5ed6bd6d7a5af3b5e,0xd7e5afbb5f56be6d7c5a,0x56c06d805affb5fd6bf6,0x7b60d6c16d825b03b60,0xd865b0bb6156c26d845b,0x56c46d885b0fb61d6c36,0xe70f83c2e058a5b13b62,0xa0c514324a168470b840,0x4c4a23205c2ba41218a1,0x908858252911c5057121,0x8208aca16306108ac405,0x2184054c3a1814098a82,0x158c93d122948924061b,0x9c4d258803e1ec1b0898,0x9c4c254185c462210890,0xf8001049601088812010,0x10901ffb00209e7196,0x5049b9ff940413ef3ac4,0x1f18f810191f758b3800,0x7800412671b0fc001049,0x4f3be855c0010923c543,0xa0bf1e004145fde0008,0xaa0ffc0010a097fc001,0xb9f80008537f2e770020,0xde00084f6df5c00602a8,0x4ebf82007b7de0008517],#[0xe029fdc00109cfee0008,0x11dfe47015fc8e02bfc8,0x804067f2380a3fc00001,0x1f00407004067c0101df,0x293f80a0d7fe130010a,0x6283f80a0c7ffcb0001,0xef701418f020293ffc20,0x84e7014187afc2000a8,0xc127f5280100a8ff800,0x203bdc25065435075d80,0xff00407be3c004277f80,0xd4004287f00a0ca80a0e,0xfffd40029437c05063bf,0xd0001522fcff80008517,0x1018fe0283002032fd8,0x842a80a107e70004277e,0x60af80203ae80a0eaa02,0x1df004077fa23057f44,0xe00c107ff68008287c01,0xc0801c658f6c0009d663,0xd4008d193f801038ca5f,0x25065435077f04a0d3ff,0x4180101aeff900313bf8,0x4059ebbc2000c90f701,0x94aff80000223802031e,0xe02832a0283dff1d0003,0x93ffbc004143fc0101db,0xccc002945fff58000814,0x1119bf01019fd01418ff,0x3604053da02846e7f800,0xa501fde0018a1a0283,0x88c7fb8006273f330],#[0xf405063fd60014a37fe4,0x14a2ffd0002143604057,0x151c3f7e0101387fcc00,0x47dfc28000a8fbfa8000,0xff812006479fff8100ae,0x323efffc08203238f,0xdd01421b6c05081fffc1,0x102a7d90182137c20085,0x3dfd60464d5fd3f7840,0x254700203b60405002,0x314df9e08003148fea0,0x3143f4408024fcf500,0xc005274f9010093fff2a,0x9003a41ff1c005273fc9,0xbf01019aec20085bffa0,0x199c010196f420087,0x2144ff808001a3961e18,0x1023bfc408083ff2000,0xa8e3fd40000a8ebdce0,0xe7ffe30011c8e3fc2800,0xc0040333efffc6080191,0x708ec7e88002c678fe0,0x314320303bec810101c,0x3fa3e12008483fff2a0,0xb7ce70008517ef480085,0x8135cffca0209df8080,0x814df80102600203df20,0x31ff28002814dff0c002,0x1cfffc8200202a3e028,0x548bfb9b8002815001,0x90fe80a0c0080d3e7a80,0x60766f010217f068000c],#[0x64d07e2ce0001d25df40,0x10a0ff40029399ff600,0xfb7600305002031de7c0,0x3c0042783e39c000c90f,0xcc002945f7800305173f,0x2949fff53400205579,0x145fcef8000294de9ce0,0x3dfcefc002145e9ee002,0x1977d520204739ce0021,0x14a1f004079f900011,0x4273fe000213dffda,0xe00189effed000a507fc,0x31447f4a0000d9affe,0xe50b8fea000547bfedc,0x80084f77380084f73d00,0x60400c0aafe0004273f6,0x7f82007a7bc004273fce,0xfff08018a1fbf403843f,0x4467dc25063c080a4,0x850fef500304cfcfd,0x4a0c986a0e701418c3fe,0xff0004283fc00084efb8,0x2143fc02832602839d9,0x40001521df0141aefea0,0x8527f9333c00102a1fe8,0x9ef3c00109efc9df8000,0x50fdb0002759af3c0010,0xfdb0020759abfc0801c6,0x77f825065ff8d0023464,0xe80406477f825064c350,0x320101ae7fd00313aff1,0x13d7f8f40203243ee128],#[0xf610007299fa3d2000c9,0xdbfd0000111d0080c7e,0x42777c05064c0507381a,0xb01419fdd602841fe000,0xa0cb810176bfe00088cf,0xa2f1e00213ae0405580,0x213de3c00427bf78f00c,0x427be5ef00c0a0bde00,0x46af970a400033417bc0,0x36f58f400151e79d8005,0x207f3b000a8d3cec002a,0xc7c000c923c2e76001d,0xc003240fe7600151941c,0x5095ff60400223a1e347,0x3463f680084ef9e700,0x88ebff72020323cf3a8,0x4477f99c014267fe0100,0x890fc02036fd0c000,0x6485fd5800088fb93c0,0x465f1d4001a32f35b880,0x528acf400628dfaa8003,0x1119675e2020472fb400,0x80582afe0004279f9000,0x3242aff2b8101921fd7a,0x517df780084f27e57800,0x8155cf10014a2e7c0010,0xcd1fd00109eff9d90800,0x547ffcc07082e3c00008,0xaafd7002528abb780008,0x99ae0003165adef00080,0xa4dc1e0413fb8012945a,0x42177068104fff680014],#[0x4a0f7fa78000214ae589,0xdd7e00204be50b8217f0,0x14bad50050a3f8f00d09,0x87f7cf80201573d80002,0xe0000e54f802039f0040,0xffb000a0a0f802045eec,0x35473f0680efbf007083,0x3f00c0e7e0981c7e3400,0x80efe094187e34003547,0x87aa1e843fc0101dfe00,0x2413ffda0005297b03c0,0x8149e5056095fe590002,0xc0141436c080d7333000,0x9800628acfe0014a0fcc,0xb60407dfd4001aa39ff9,0xe6802029feff1400e167,0x80802eb9f6000294bfdf,0x7093fbfcd00405bfdf66,0x892ff5f9b0080a7f9a00,0x79fc005c51be39a80000,0x2548bffd98e12008058,0x40102a4df080227c6140,0x56ffef220601679d3f78,0xf7c6003859ff99040040,0x702b3ffd904004056ff,0x5bff7f0810051ffec820,0xffa5c84805bff3e88100,0xfd8008093fb280004153,0x80a9e040402df3001214,0x5297ec860117e2c800,0x14a1f3c03041f7eec0,0x28059fe6c0018a2ffccb],#[0x147fd6000c50fff74e0,0x700a018f0a01014f2204,0x10090ab9fd9400020ac9,0xa7c10400a7cf07c10f9,0x201216f9c00709798008,0xcb9600082a7cf00c10f0,0xb8a363f3880001124ff,0xdfe4b9600042c3ffbf00,0x1c0708df1850009522f,0xfe90040a07f47c240109,0x9c008143fbfc88200593,0x87fd1008093e028347f,0x200a7ff101c21ffc410,0xdee406087c10400a7f91,0x87f9f0141dfdd2dc0142,0x4095df001025fe5c3e0,0x7c0600a5df001025d7c0,0xf802045bcf7c00010a95,0x21f9afc01014f80203a,0xf7c08021d7e01c217c01,0x59bc100277eb24000890,0xc0062866f08021b60406,0x652adafe02003c907ad,0x855e3e000c507fc39e44,0xffc8ba00042b7f5f603a,0x8a2f1f0006283ad81022,0x1025e5fe003855e3e009,0x394bfefd8008126f00,0x3149e723e00462ab9d28,0xe12f2ff4018269c8f800,0xbffc53000572b797ee00,0x7c7c8001922f1f000628],#[0xc7c0018a0cffa000a508,0x9f9bb000652afc00709b,0x523ea0e0147ea18045f,0x584e7f7000427576004,0x802e28bc7c0018a0fee0,0xe104fcaf00018a8ff8f,0xf00006292ff406085fa8,0xe032855cf240109efff0,0x9f50200a6ff806077e5f,0x4082ef001c293f701c20,0x6fc0014a1fe0080e7f00,0xafe67e000a507c01022f,0x43ebe00284acfdf415c2,0x4779fbe02b051bdc0131,0x44fd000811977d52020,0x404e3eb800088cef802,0x102aff1d8000a537ff70,0x18249faed00062a79b00,0x7018217dd4020257dd40,0x329bf30fe0005295f7,0xff21f80003951dffde48,0x879ffe00304bffc0181e,0x62867ff800e12ffb0040,0xa50fdfe0941cffcfc000,0xa23bf7f82c07bf39e004,0x34087eff0580e3e56001,0xa0e3e56001a23bf7b8,0x3894207cac0034477eff,0x74c01429ffe30b821ffa,0x1cb2f743fc00102a77,0xc7fde78012945ee84cf0,0x4273fc00084eff04a0],#[0x62003143ffa61e841fe0,0x182b048fd60006a8f7ff,0xe1e002139f6a0084eff7,0xe71e800ea39e1e002939,0xc00109eeffbe0c034299,0xe02841effbe0c03429bb,0xd801935fddac00ca1f7c,0x19128e7cd96800295dd,0x9c9df8002946ff033008,0x64cffb380a1179c0010,0x4953eaf801026f360,0x8524efc0014a2f09ce,0x28d7f73802059be680,0x100a6dfb80c10eb6fdc2,0x20537eee030439bf770,0x46659d7880811dbfeb38,0x3f0be40018a5bfe40000,0x28ffe603043dfcc3808,0x8099eff402040fbcc04,0xa527f7e4028273cff0,0x147e07e8002949fc9d80,0xc103ffb018216de6020,0xa54bdea0040a5bfb8,0xe123ff300809a781fa,0xb2563ff7014207fe6,0xc10f7bce02e137fc93b,0x82f5f0a80403343dbff0,0x7b7a8024294fceb00064,0xecff40094a1edff80e08,0xca6f3c00b09ef3c00b09,0xef6ffc03045ffb3e0001,0x9dafba0090a3bea0084],#[0x1021ebff400c127f8001,0xc5097fe801c29fea0,0x848c3fa082da91effcfc,0xc8461ef10b05140fe216,0xc4338f885b0a8cb85c42,0x615197f364448f300e8c,0xea16122cf50b2441f10b,0x5d18981a2afd8cd65140,0x8a39e00c0828fa313114,0xa348b3d951a459da5884,0xc42450e9505c8059e7b2,0x13a89a28c4ea268a3263,0x3]]
set_option maxRecDepth 32000 in
def g255H10 := limbs80 #[#[0x22060c01200600170106,0x10e1d050a021e1a,0xb0616000602010715,0x2061a280040030f2607,0x20619030e4b000a0005,0x11120914050418004221,0x7010003050f020402,0x10202000e04010c1b13,0x1070e050d0112000401,0x90917050102010a1101,0x130a00060c1007004264,0x60821202e0129000613,0x1214100402080e030201,0x21100b15062616522216,0xc1502000c0003001601,0x1090e300e1906000812,0x3d250e0200000116,0xb001b2f000400000a05,0xd0104320201050801,0x211511040115130206,0xe07250002010418020a,0x1b081610012e0001431a,0x93f04000d04081b082a,0xe0d022600140a110107,0x174b220e2a060c020002,0x2012f09000001281607,0x2061639031801120701,0x4b080500330309370000,0x3d000d180f0c04293672,0x1b0106041b07097a00,0x1b0000061d03343a11,0x5f007138010015014f],#[0xe0d09015e012a218c08,0x20012153b00021f0802,0xd0cc90e3d0907092a12,0xca700403020219264502,0xb638b051ba2e800169e1,0x93590d80008620000006,0x20779892556678003ab8,0xa2589f00001c5c8f000,0xc7253a480002196fd800,0x6e106528a4022cc000dc,0x23a89d06b00023,0x77c36b00047f394c0000,0x99bcaa8000b360004456,0x63047648d89d1985cfe,0x556749b246e000556800,0x289e013b53162d40001c,0x530004310a091044e6ca,0x76758c000949a1998219,0x89e80023ee3889c50,0x14144c11620000000,0xb9f4100800006abbf000,0x14524a638c4ff31c70a,0xaf24600,0x56800000006fd52528c0,0x4e30000a120064e76,0x890cb6467f8cac118000,0xc00130600060b832431a,0x96258e45651117e7a8c8,0xb871c000a6068f800005,0x69006ac10a9d4ec2a50e,0x55fa153b196b0001470c,0xcd48aad2876f60008873],#[0x80f26680000368cbe738,0x93ae64f58c6723225ec,0xaf676a07954ceeaa0c00,0x11d6fa990d7e11842184,0x278ad035e9d5de87463b,0x2b2489d75c9f4000b81d,0xc79d41b097920000083b,0x1807443df4c95c805b7e,0xa3343f6481a032cb000,0xf034c000643b39830421,0x9a0cc44d3d9c536246e,0x634133c4a4c3ab44b07a,0xab192c000287e00006e2,0x72c531fb2a6962ae3680,0x58c8ec0c1a34093f0d66,0x7ad6f1a309b85100e13b,0x4781b19887c12a2d388e,0xf3ad058fa809695ac338,0x73e980d3b87a1704be45,0x17d35903facdaec28a7d,0x55d09121ed32db5c9446,0xb687afa974a2ffcde2c4,0xd31a8c55952a5b42ba40,0xb32ca68719b946fd85e5,0x3e892399e534b5513509,0xc005969022138327c1a7,0xcf47030bb7a22801c2c1,0xbba108522c71244681b3,0xe422613ccfb1bfe17356,0xca0000001670000d7ba0,0x4fb97,0x9fb233d9648bf4440000],#[0x82068fe52d3a4ebfb054,0x191d17b8a13354001529,0xe58aedbc15f2d54a3800,0x7937d3878f68a235ccb5,0x6d8b22db39540000f075,0x17c00187b602c2f79595,0x3335a723f08158454cc3,0xaa1a903d5de7e15d8001,0x50ef27c8041a960e440a,0x73348670eb0a5d24811,0xb48010004643b2589800,0x5b8e8c7ba0dd27449508,0xae6000eb5a0526b4cf1c,0xc754e3c373824dc2a852,0x956b66279e0a111d8b6,0x567780004908add50800,0xb071a000c99000272521,0xbdd8f2a3719abdf4d270,0xbe11000002681062344,0x92ae31eb6f7b702b6ac4,0x13220000000000000,0x5262adaa5c79e134000,0x52940010520004c6d59,0x8fe21d86e8000c2200,0xd929e38d8000ac556300,0xabe1d10734c2169849fc,0x9ef6119232d908222242,0x2203a8b6844ff2327a98,0x1a2f6b36313869e49800,0x125f0d9e3fef544c356,0x545e6b1374d18765cc80,0x8f00000000000b7c001c],#[0xd3e470920e260000a99a,0x6e0c001a76c8c00015cb,0x3e8000348041b41305a,0x30197632a4da6dc6fc00,0xec00022129a531d9e,0xc3ee5e885b9d93f00000,0x8f5cf700007900013fb2,0x8580000004294f3e202,0x80000f5dbb2a43ace36d,0xe0be0002453457e4f684,0x1ba25aed0000000af24e,0xfe433b5b12d19bb64e07,0xb304e2000465c0e92,0x3969562ada7cc2d2eca8,0x948553494ce1330e8001,0x1c7800000000003a08e0,0xf6bca7e2a8200062ab15,0x8c0eeecf3069648871d6,0x878097035362de100022,0x193ad300000026979381,0x10f139637c,0x11dc4db143b338c2e,0xa45280037d600082f306,0xae14123611600039bb1f,0xc584bc6d4000b1c5300e,0xaa064b40101380032900,0x4ed198292850a1c4110c,0x445262c3bb0004478001,0xd2ca6643804c5000,0x853e01a4000000210800,0x9670004db8000a949a,0x666ac293a00483e62040],#[0xa8387e845e89b06248ac,0x46afc8000000903497e,0xa970000e08c1c22d7301,0xd1e8b53072355099b3d,0x18e0415490800000,0x598a900015f132b19900,0xf043af42000042c288f5,0x51793ae82c27380a5576,0xd5c48b2c1ea9000114c,0xaac36542eb2537add252,0x5c04b3d505f06a8df37e,0xa198369400000eb3c04d,0x5142b0000c3067f80012,0x8f84e54796808a4eca05,0xd43e7a726f97e000020f,0x48da256ec700016bad3b,0xe4e161cd5f9cb25ac05c,0x2952ca220700031f2cd,0xc94329c909b69e8480,0x9cf6d09840862a440000,0xbb49fa61ea854b138302,0x26b0000813000000278e,0xe0009bca3fc0012a9e9a,0x43d8a3292b016e8c7a8,0x660006a0000209800000,0xa2826a3a928e1382ec29,0x454000eb2eb14001109d,0xc9130be1294bce758af3,0x15c6d10cad8000aea9a9,0x243647ca6781e5981f38,0x2e2e000081973600003d,0xba1de80036d400058bf4],#[0x97d80007b10,0xae7d1caf212e644f6b70,0x80015e60004f7ad47483,0xf14fd9de9680011d000c,0x665103d784acc30fb306,0xc2000000000081ec4462,0x1bfa00071707,0x596000cd10003ae357c0,0xa12000378a000e436244,0x1183976d854c803cd158,0x859f22f4180001a4540,0x6407b2810004d7188200,0x560fd0dc0001432a292,0x89e7f1b90aaa80035d88,0xfb97151950f13a60000,0x4f1342313f97b9338001,0x63edd335390001436000,0x48001b040000006cf53c,0x74000c1d6ce93edc6ee0,0x68807d4bba6f52580039,0xa2707d66594072ae15a2,0x64c000297200046149a9,0xc824000c53e098001048,0x3ecda5a73460000a6cdd,0x242fc614c50c857e63c,0x9a1491e1b015f11800,0x59aaf400000015443180,0x52500055300e4406533d,0xae6a1cb56a4ffec7c001,0x452d57b4747f2be3cef,0x800b04f28cf95ce2f000,0xa18b2d490001a63548c2],#[0x7a6c38001baac570003a,0x27826e07a4d800c8ba86,0xf9e4b85e885400045f4,0xc001a2d000684d1c6000,0xec68000256ece9510683,0xf821a3ffc4987d4001b2,0x6ec6f634c001a99db880,0x8e90d40006b9331c0009,0xaa6cfca41c8ad41dc82c,0x2762ad239b05486a8341,0xe0000000b5c00000050f,0xf0df50ef01144384b118,0x86000c0b00017debb3e5,0x4d46c000143da968003a,0x2bca895598001a8d50ca,0xd03d4682eb956428e995,0x47719af4db039480,0x2000032e157c3900066e,0xd335c0005a934fc22186,0xe1000240c2e400080bf1,0xd0c000ae04cf800260a9,0x58f535d2218fc9818e46,0xf706e6314d83ace2457,0xd0ce25d817460083f018,0xf73645d2a7c1b08af67a,0xfe363a70937c83d2c9a1,0x1a2cf80002be87b94342,0x92a34d43700000010c69,0x248548c03c000a272731,0x63f0a5e0000000000000,0x86cce1e400148286d70b,0x8c1d09c900051ec0c2d6],#[0xe09bd000272632985f84,0x6c423f1d329ce5ab476b,0xe2ceebc0198639930,0x4f8b5654ca9123668000,0x68e95600bbb81b9119b2,0x646b74e212d000023d9a,0x44000aba30afaf0535e4,0xa9a6d12df14500112dda,0x1cc31e5cafc1040001,0x1828000cf76b40,0x8c396d35c1b00000,0x82d0002170000a35d34,0x5c001264989458957600,0x8e3941650121ac3fb0,0x183b578cd500000,0x52228400000015d0,0x8001017a236cb800374e,0x355357c800000080e1ba,0x96c0013ce0004ffa09,0xe40008cd8001a3e00000,0x63516d54fb8600012fd6,0xb17370c14af300420002,0x347b00c40c9a50000,0x89605161882218000000,0x9283c69c0000001d969e,0x12c29c000262361bb0,0x8b449b8800002c200,0x4463283a9c84000195e0,0xcea0006ff4001d5ad177,0x8d1d7ae57da796d1a809,0x800060b0a833adc62029,0x2ee1352aaf5e9e298c6e],#[0xcac25e338000000c5089,0xa211ab3961d200000026,0x53b94147d535c5b9b89e,0x61a25873bc2f0a9841ae,0x637ac27951cb3c31c470,0xe8edf21609d0d750c869,0xfe2384b5a8e55806054a,0x1bd21af538e73d3d0049,0x3c40ac57e4d0f537aacc,0x54287c526ca750e79da8,0xa655205aefaa78a3d0b0,0xb38b0006859728129697,0x451cb1e08220000b09a7,0x9488563035dfa9229ea6,0xa500017720006c9e2fb7,0x4110ed027803f80ec49c,0x1dd00032cb2fd0fde73b,0xb30a344d028d64000000,0x8936800226334992914a,0x30b1b19a4198eb531617,0x56e32000000021861ab3,0xfdd92f502a28f1d42ee3,0x11409ef387cb48a72,0xd35ba5c000cb1ab85488,0x2000d55a87c72b3c990e,0x4c301ac4c9682d828d8f,0x8facaccea5253e324ed2,0xbd000176d2ea4ae04930,0x26c5378b61457b0c2f6c,0x5bc697000000024688c9,0x879bb8c104932850000,0x6821a49eb2200005c800],#[0x10000d1af6263c403,0x8c06d85e4001a5000005,0x273c89f0004e8b58ea,0x30e00000004cb0,0x1b800000001176]]
set_option maxRecDepth 32000 in
def g255D11 := limbs80 #[#[0x995765d5745956455075,0xbdeefaff76dd774d5275,0xfbfdfeff7fbfefebf6fb,0xc0d820460415800ffff7,0x5d04b835061805840260,0x199d465751999465651a,0x6596e1c598716e185986,0xa9742661e5986995d665,0x151b872661ca17626e14,0x66169b8647dd91d7646e,0x5395d4db843661a9d76a,0x98476e1cd987385d8e67,0xd5986066101987795d5d,0x61a198486e195b845be0,0x66e119986b6612d98786,0x751c5945985c66131b85,0x71861cdd871761cdd471,0x1c72871c61c70871ce18,0xc5d4b0752cdda71769ce,0x52c614b0852cdd4b2752,0x2872c61cb0872ce14b28,0x531754c99531654ce1cb,0xe1532854c61530854c9d,0xac596b3864c61931764c,0x753c5d4f3843c610f265,0x73873ca1cf1873c21cf3,0x1971865c5d973845c611,0xc215b3846c611b1768ce,0xc0940033856ca15b1856,0x4683c83302cc2641c412,0xbc7446b86585c45544c8,0x4af8a689f495c8e08507],#[0xe30dd0d70ce0c54be4b5,0x910f908cffcf9cf3ceac,0x54c144d3d133d2a522d1,0x8d583d7a972d6a55ed55,0x7dbedb6dadda5d9e5965,0x9f65f05e71dddd4dcddc,0x30e29621e18a102099ff,0xe26565ca5464b642a39a,0xea529ba91e8928067666,0xde6d42cc6c5abb6b4aac,0xab11b09b01ef86ee2e66,0x74c742f3a73432a72171,0x81779771f6ab6475c754,0xf03070ba4b9cf9638bb,0x29231711161470202a13,0x101468604465122a20b5,0x9c58b03834302d0cb8ac,0xc4e7f8710713dfc3a058,0xd039ff0c80b13dfe1c11,0xabca5c008a1c8340ef20,0x802084822087f7710620,0x7fb8001053802104bff6,0xc0d043ff701408500208,0xffda00821eeec04812ee,0x843ffb004e12de00a025,0x901408bccc022276f40b,0x1204bd405041e7800a13,0xdc0501db9f809025ef50,0xf804e12fda05021c0881,0x685410c02e10e0640ef6,0x9ffa10020a420e412eff,0x284bd380410fdec40082],#[0xa025bfd204e12fbd381,0xb7de409c25d582e10ea4,0x7794b805054ffcc81304,0x70973205012dbc813848,0x14053ff2604c12df7302,0xf3a0a842efa0b843d9c8,0xe10dd5e048127f585410,0x902c10f75a04e12ff482,0x4e16faf405012e004e12,0xc0a839d76809c2defa00,0x6ffd10680a27b600b142,0x78097d7e05c21d01608,0x2bbc1f042ef02e10fff0,0x60938ea0020c79dc04e1,0xe0b841e77013853cee02,0xc77013053ce60120a71f,0x49dc7b81405bcf705c21,0x4e12e3980a02de770090,0x5821fed00270b779fc0,0x851f017084e009416ede,0xc0b041d80a087f73e013,0x6e01204bff9d009029cf,0x5bfbb7809025dbc05043,0x140776f07c10b76d0140,0xa1026092dbc016287f9c,0x20eff8834053ed581404,0xc20d012fb5e0b8425054,0x5b6fa0b043eee0a03bff,0xe7417082e0a039c883c8,0x12149dde01043ce82e10,0x821feead0270ab96980,0xfea50260a75782c10a70],#[0x1f]]
set_option maxRecDepth 32000 in
def g255H11 := limbs80 #[#[0x802010030042200800,0xe32002100d2000021,0x10440290250042010402,0x22200020042020000,0x1424200243802100060,0x4010042210c4300004,0x6000200044008400,0x88003884018826114e0,0x10441280170000000040,0x40026008201804000040,0x1ae38000000000019a23,0x26c00000102a0014ec00,0x197abc7820000,0xe00091e001a9c00194a0,0xcd400115,0x2711fa,0x2634171460000,0x66000b0000000,0x88001c6400000124c000,0x5ad018b3ab9872e612b4,0x19ba0013b8a0f26,0x4006a154,0x10369040000000,0x4a00000000,0x7e000001a3e000000000,0xdab3cf11e6000001b664,0x9610e600000129288a47,0xca4000bde000000000,0x1a6e00039dba60000000,0x1490a3800000,0xa8000000a5fcd2000000,0x1c2e0d40000c50b12],#[0x0,0x953a80000000002da908,0xa0c00000080a001cfb8,0x18a113c00000000000,0x1c26255b62,0x0,0xaec00000,0x22000000001b0db3e000,0x1b,0x3b1e02a20023c817200,0xe8000385a08000000001,0x18bcabc0000000009ebc,0x0,0xd0000000000000000000,0x1a60010320000000000,0x1aa000ce000150400000,0xce000000001b72c1a001,0x8001af0000000000cb9a,0x33a016bf285ab34b4,0x3990dc,0x4340000bd33f00014b20,0x1f20000013ea9f84a29b,0x1,0x13800140004aa2480000,0xc3a00187e08600,0x1d00000000000000000,0xc0000000000013c499a0,0x1100000011c8001b7,0x0,0x105c00092633c0000000,0x1027c4800000000,0x1b5f4133b6000a5a],#[0x101a0a60000473ca0,0xc86916001ae800000037,0x5800045c35a000001442,0x8,0x116e001364b6c00,0x77b311bc0000000019e8,0x132c3f800191db4d49d2,0x130200000000000000,0xd60000001de000000000,0x1cfe000adc000c,0xbe800085400,0xecaca0000f20010713d0,0x80012f68f40013140018,0x3d,0x87c40000000000000000,0x978a6a001b,0x1480c0c00000000,0x0,0x1c3800000138b0b80000,0x1a7bac800000000000,0x29bc2000980a9e000,0x4064a040000011bfba20,0x14a1c6c000000000a1,0xaea00000013a000,0x192e0,0x9fd3833ce00000000000,0x8db,0xc4340c816317c0013520,0xac7c9800000048d8debf,0x199809e000000000000,0xe0000000013dc0900000,0x4de0011e234],#[0x36000000000000001856,0xc000001c371b813491bb,0x11024a9ac,0xb60004be16ca2398e390,0xfa963960ae0002a40010,0x1c3d41038,0x8207d936000000000000,0x252c5ebcc0011,0x8f80be0000a297e00000,0xee4713e58c1cb0000b42,0x970000000000a94a323,0x4441f89600000032e00,0xd2d02000cdc00000014e,0x18529,0x93e00019c00000,0x13383b40000014f6000,0xb40a001a060000000000,0x49e00121b24f2003b,0x84001308c4a000000c66,0x120000000001900c,0x1008bfa00131000000,0xb2000001bf40000a4,0x11480013ae0000000,0xb0b2e000000096800000,0x356,0x1988a260000000000,0x8120011c000000099221,0x1a46000000001,0x1bec0008d20000000000,0xafe00000,0x8fb21e,0x8000000cd9b194771060],#[0x24a00000000000000125,0x19b6000,0xa00000000045800094c0,0xc5,0x720009940000001d8000,0x11380000004b40002,0x76000001c6080400000,0xee000000cea000ad6,0x20001fe0000009da0000,0x89c00000000000000121,0x23b4b2fd29bab806c001,0x19c41580000e8c,0x375a5cc080011539ca00,0x139392c000001,0xe001a9087a001cf40000,0xf0000000a780001a,0xa182c000088000000000,0x12191560018d60018cc3,0x10ab1f185f217c6e00,0x1c333c0184000,0x4280000000000010780,0x0,0x8a9282,0x17600000190a0,0x38c0012d381c0013e200,0x30c8f31d3a427c000000,0x200000000000049388c1,0x18f64f2000b892c506,0x1c00000,0x1ad92f8288000b9e9ec0,0xcad45600000000000003,0x14ce001114],#[0x14444300000000000000,0x1d1cae00000000,0xe2824000000000474aaa,0xa411d60014509f4001c,0x10b4000000c5332000,0xa0000000000000000000,0x1cc20000000012354e7a,0x0,0x4c7236018b50,0x40009640009dc0000000,0x1231304000001b2639,0xa000008e0000002b0000,0x38fc000ad4000000a029,0x12c,0x500004ee000000000000,0xc000000944000167cca0,0x1006b9a4c,0xda01e000000000000000,0xc0000000000000000d93,0x8c746842c000b24822aa,0x12ae00000010f,0x12436183c0000,0x1860a7e25,0x4295d150cc0000bd7a3c,0x4200000012,0x8e09ce0008bb4c400000,0xcfc0000003d4001,0xb0800019740008923280,0x95b1ee0000002240010c,0x47a332000000000000,0x135544fbf60000000,0x4e001455a68c3e00],#[0x1280001b2000000,0x60013440000010e40000,0x4800000000000000019,0x10ea000000,0x48758392f2001aa60000,0x103e0000000011d,0xc18000,0xe912001c620000000000,0x1b782b,0x8cc25a80000000000000,0x3810000000000000001a,0x2e4000a2000000000192,0x1482000000000001,0x0,0x0,0x772ba22a000000000000,0xb68000000000000b,0x189a00000000000,0x0,0xe00000000000041c0000,0xae,0x10699c600144ca66ce4,0x2980002840000720,0x50600000128a00000,0x91c2b9c2000000000000,0xc9a000a8fca74979,0xa2e2f4a560009cc00000,0xc20fe001b46001b1616b,0xb8e20000000000000000,0x131e000261cd,0xc000000184c46a001932,0x4000000000001cbcb0f2],#[0x1ab437abb000000024,0x4000000000000000019e,0x4f8000000001b2a0001,0x0,0xbfe000001b7e000000,0x4d01a83be98c0000000,0x21c2de000c04a7400000,0x0,0x1a2cb580003120,0xadbe00000019ac00000,0x18cfbb336acba000001,0x2a29c72000001bac0000,0x1e400000086ec1435c14,0x19f6ab6000b6e000000,0x60000000014c844623a0,0x4781a4000b0,0x8a001082be6000406000,0x8000000000000000001c,0x10cbbc02f31b11,0x19b000c000000000000,0xe0000018840000002860,0xc0,0x1a0a000000000,0x10340000000000000000,0xc020014b649509800000,0x1,0x2fa0000000000000,0x180e00000084200000]]
def g255D12 := limbs80 #[#[0xccab2ee8ba2c9aa2a9ff,0xc17006ecbb6eb3aaea3a,0x1d4d45f29118742e9185,0x848914508830e1408c40,0x83008084008108020202,0x10214020210028420080,0x102001008000102940,0x140142140202000508]]
def g255H12 := limbs80 #[#[0x514100c201981202005,0x509400110305500811b0,0x658011bb219c003704,0xbe34ba88e00e524417c2,0x6a27001ac000cd6b,0x699e23640004985f823c,0x6f7c08877000033a786f,0x914e204b2a17ac001927,0x44e90431d57cae989bc,0xe449a1a3053f5ccf2180,0x97400009edae985b29ce,0x4a2e00028000d800d528,0xad00001cca1000038056,0x6000c7600168002077e,0x1d37802bc00e1d3a,0xc0b2e0000003730cd90,0xb000c400005d5400000b,0x6ce4c018ab631401a,0x796e5105b80000170000,0x13c7100000e3a302]]
def g255D13 (j : Nat) := if j=0 then 0x5103042006ff else 0
def g255H13 := limbs80 #[#[0x11c8137400000001,0x44000000,0x15c188a0000000,0x9ae000000000200e0]]
def g255L : Nat → Packing
  | 6 => (4,7,6,0,0,5,0,g255D6)
  | 7 => (56,6,6,2097187,86,9,1026,g255D7)
  | 8 => (913,5,6,13435178,137,14,4176,g255D8)
  | 9 => (1439,4,6,8913204,137,15,4239,g255D9)
  | 10 => (644,3,6,2424918,103,15,4177,g255D10)
  | 11 => (113,2,6,851981,68,12,4129,g255D11)
  | 12 => (13,1,6,65537,0,9,4106,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 17 0 4 2 0 g255H7
  | 8 => lookupShort 14 71 5 8 6 0 g255H8
  | 9 => lookupShort 228 1249 7 12 10 0 g255H9
  | 10 => lookupShort 359 1777 8 13 11 0 g255H10
  | 11 => lookupShort 161 1613 5 12 10 0 g255H11
  | 12 => lookupShort 28 157 6 9 7 0 g255H12
  | 13 => lookupShort 3 53 1 6 4 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_296 : CutRow g255 9 296 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_105 : CutRow g255 10 105 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

end PEqualNP.Outside.L_meta_35106
