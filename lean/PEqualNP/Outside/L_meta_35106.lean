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
def smallCircuit : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[0,1]⟩,⟨.or,[3,8]⟩,⟨.or,[4,8]⟩,⟨.or,[5,9]⟩,⟨.or,[4,6]⟩,⟨.or,[7,9]⟩,⟨.or,[5,7]⟩,⟨.and,[15,10]⟩,⟨.and,[14,13]⟩,⟨.and,[6,11]⟩,⟨.and,[7,12]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([4, 4, 5, 5, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 5, 0, 0, 0, 0] : List Nat).getD i.val 0))

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
def g81Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0)]
def g81C : List ColumnInfo := []
def g81A : List (List Nat) := [[],[100],[64],[64,96],[96,64],[96]]
def g81D3 (j : Nat) := if j=0 then 0x7 else 0
def g81L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g81D3)
  | _ => emptyPacking
def g81I (_ _ : Nat) : Option (Nat × Nat) := none
def g81 : Forest := ⟨81,3,fun i => g81Y[i]?.getD (0,0),g81C,g81A,g81L,g81I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81P3_0 : CutRow g81 3 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g81B3 : CutRow g81 3 0 1 := g81P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81T : mixedTables g81 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g81 0 0
  · exact mixedEmpty g81 1 0
  · exact mixedEmpty g81 2 0
  · exact g81B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81G : graphValid g81 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low81 : Lower true (varsX 81) (graphGoal 81) 4 := mixedLower (g:=g81) (i:=0) (hints:=4) (before_sound [] baseKnown) g81G g81T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K81 := extendKnown [] 4 [(81,[]),(82,[16]),(145,[118]),(146,[16,118]),(161,[84,118]),(164,[32,16,84,118]),(168,[48,16,33,84,118]),(193,[100,84,117]),(208,[64,16,33,50,99,83,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V81 : Known true K81 := extend_ok (m:=81) baseKnown low81 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf71fc7ff03fffff8f7,0x1fc7ff03fffff8f71fc7])),(BitVec.ofNat 152 (word80 [0x710490a2850401207,0x10490a28504012071049]))),((BitVec.ofNat 152 (word80 [0xbe838fffc07e3ff0b,0xe838fffc07e3ff0be838])),(BitVec.ofNat 152 (word80 [0x4368db4c3260892043,0x68db4c326089204368db]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xeee63ffffff803ffee,0xe63ffffff803ffeee63f])),(BitVec.ofNat 152 (word80 [0x88724904085124008,0x87249040851240088724]))),((BitVec.ofNat 152 (word80 [0x193dc0fffffffc0019,0x3dc0fffffffc00193dc0])),(BitVec.ofNat 152 (word80 [0x982db6e08306038498,0x2db6e083060384982db6]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := []
def g51A : List (List Nat) := [[],[64,81]]
def g51D3 (j : Nat) := if j=0 then 0xf else 0
def g51L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g51D3)
  | _ => emptyPacking
def g51I (_ _ : Nat) : Option (Nat × Nat) := none
def g51 : Forest := ⟨51,3,fun i => g51Y[i]?.getD (0,0),g51C,g51A,g51L,g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51P3_0 : CutRow g51 3 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51B3 : CutRow g51 3 0 1 := g51P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : mixedTables g51 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g51 0 0
  · exact mixedEmpty g51 1 0
  · exact mixedEmpty g51 2 0
  · exact g51B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K81) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 4 := mixedLower (g:=g51) (i:=0) (hints:=68) (before_sound K81 V81) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K81 4 [(51,[]),(53,[33,84]),(57,[49,33,84]),(99,[100]),(102,[32,100]),(116,[32,65,49,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V81 low51 (by decide +kernel)
def g83Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0)]
def g83C : List ColumnInfo := [(1,0,82,0,4)]
def g83A : List (List Nat) := [[],[100],[16],[16,100]]
def g83D4 (j : Nat) := if j=0 then 0x1f else 0
def g83L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g83D4)
  | _ => emptyPacking
def g83I (_ _ : Nat) : Option (Nat × Nat) := none
def g83 : Forest := ⟨83,4,fun i => g83Y[i]?.getD (0,0),g83C,g83A,g83L,g83I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83P4_0 : CutRow g83 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g83B4 : CutRow g83 4 0 1 := g83P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83T : mixedTables g83 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g83 0 0
  · exact mixedEmpty g83 1 0
  · exact mixedEmpty g83 2 0
  · exact mixedEmpty g83 3 0
  · exact g83B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83G : graphValid g83 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low83 : Lower true (varsX 83) (graphGoal 83) 5 := mixedLower (g:=g83) (i:=0) (hints:=68) (before_sound K51 V51) g83G g83T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K83 := extendKnown K51 5 [(83,[]),(147,[118]),(165,[33,84,118]),(172,[32,49,84,118]),(177,[64,81,33,50,118]),(195,[100,84,117]),(197,[33,100,84,117]),(212,[32,65,49,99,83,117]),(225,[80,97,33,50,64,67,116]),(228,[80,97,32,49,66,67,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V83 : Known true K83 := extend_ok (m:=83) V51 low83 (by decide +kernel)
def g85Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g85C : List ColumnInfo := [(4,0,81,0,4)]
def g85A : List (List Nat) := [[],[64]]
def g85D4 (j : Nat) := if j=0 then 0x1f else 0
def g85L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g85D4)
  | _ => emptyPacking
def g85I (_ _ : Nat) : Option (Nat × Nat) := none
def g85 : Forest := ⟨85,4,fun i => g85Y[i]?.getD (0,0),g85C,g85A,g85L,g85I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P4_0 : CutRow g85 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g85B4 : CutRow g85 4 0 1 := g85P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85T : mixedTables g85 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g85 0 0
  · exact mixedEmpty g85 1 0
  · exact mixedEmpty g85 2 0
  · exact mixedEmpty g85 3 0
  · exact g85B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85G : graphValid g85 (boundsBefore K83) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low85 : Lower true (varsX 85) (graphGoal 85) 5 := mixedLower (g:=g85) (i:=0) (hints:=1540) (before_sound K83 V83) g85G g85T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K85 := extendKnown K83 5 [(85,[]),(86,[16]),(113,[64,82,50,96]),(149,[118]),(150,[16,118]),(153,[50,118]),(163,[33,84,118]),(166,[32,16,84,118]),(170,[48,16,33,84,118]),(178,[16,82,50,118]),(180,[32,16,65,49,83,118]),(184,[48,16,66,82,118]),(226,[16,82,50,100,116]),(232,[48,16,98,84,66,116]),(240,[64,16,82,49,99,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V85 : Known true K85 := extend_ok (m:=85) V83 low85 (by decide +kernel)
def g209Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g209C : List ColumnInfo := [(1,0,208,0,4),(16,0,193,0,4),(64,0,145,0,4),(128,0,81,0,4)]
def g209A : List (List Nat) := [[],[118],[100],[100,116],[116,100],[116],[64],[64,118],[64,96],[64,96,112],[64,112,96],[64,112],[96,64],[96,64,116],[96],[96,112],[96,116],[96,116,64],[112,64,100],[112,64],[112,96],[112],[112,100,64],[112,100]]
def g209D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g209D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g209H4 (j : Nat) := if j=0 then 0x1c else 0
def g209D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g209H5 := limbs80 #[#[0x1804100000000001c60c,0x113100000228079]]
def g209D6 (j : Nat) := if j=0 then 0x3904f else 0
def g209H6 (j : Nat) := if j=0 then 0xab00091432000000062 else 0
def g209L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g209D3)
  | 4 => (3,2,2,0,0,5,0,g209D4)
  | 5 => (1,1,2,0,0,0,0,g209D5)
  | 6 => (1,0,2,0,0,0,0,g209D6)
  | _ => emptyPacking
def g209I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupShort 1 3 0 3 1 0 g209H4
  | 5 => lookupShort 2 23 2 7 2 3 g209H5
  | 6 => lookupShort 1 11 0 7 0 5 g209H6
  | _ => fun _ => none
def g209 : Forest := ⟨209,6,fun i => g209Y[i]?.getD (0,0),g209C,g209A,g209L,g209I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g209P3_0 : CutRow g209 3 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g209B3 : CutRow g209 3 0 2 := g209P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g209P4_0 : CutRow g209 4 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g209B4 : CutRow g209 4 0 3 := g209P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g209P5_0 : CutRow g209 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g209B5 : CutRow g209 5 0 1 := g209P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g209P6_0 : CutRow g209 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g209B6 : CutRow g209 6 0 1 := g209P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g209T : mixedTables g209 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g209 0 0
  · exact mixedEmpty g209 1 0
  · exact mixedEmpty g209 2 0
  · exact g209B3
  · exact g209B4
  · exact g209B5
  · exact g209B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g209G : graphValid g209 (boundsBefore K85) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low209 : Lower true (varsX 209) (graphGoal 209) 7 := mixedLower (g:=g209) (i:=0) (hints:=4) (before_sound K85 V85) g209G g209T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K209 := extendKnown K85 7 [(209,[]),(210,[16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V209 : Known true K209 := extend_ok (m:=209) V85 low209 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffc07ffffffe00,0x3fffff80ffd386b20f0f])),(BitVec.ofNat 152 (word80 [0x41a8128d052280541a,0x82502916291304a21111]))),((BitVec.ofNat 152 (word80 [0xfffc00007ff01fffff,0xc007ffff01a37d4800f0])),(BitVec.ofNat 152 (word80 [0x81311b160644c89893,0x136232244d835c485555]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfff80000003f407df000])),(BitVec.ofNat 152 (word80 [0x5c05c18178702e01c,0x380bc38703340753333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x160260205808130120,0x2404c00000642314aaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1803800060001c01c0,0x38070040808c9308cccc]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := []
def g55A : List (List Nat) := [[],[33,84]]
def g55D4 (j : Nat) := if j=0 then 0x1f else 0
def g55L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g55D4)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,4,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4_0 : CutRow g55 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B4 : CutRow g55 4 0 1 := g55P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : mixedTables g55 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g55 0 0
  · exact mixedEmpty g55 1 0
  · exact mixedEmpty g55 2 0
  · exact mixedEmpty g55 3 0
  · exact g55B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K209) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := mixedLower (g:=g55) (i:=0) (hints:=1348) (before_sound K209 V209) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K209 5 [(55,[]),(110,[32,48,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V209 low55 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8003ffe00fff803ff,0xfffffffffffb5d61e03f])),(BitVec.ofNat 152 (word80 [0x501a80941a02905828,0x540940a414940616249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000fffffc01,0xffe001ffe008a3d3c1c0])),(BitVec.ofNat 152 (word80 [0x61530ad8ac2b22914c,0x2986d84c8668a351c6db]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000001,0xfffffe000004e42dde00])),(BitVec.ofNat 152 (word80 [0x819c0ce13033c4e270,0x4e04e06f0b84e429c6db]))),((BitVec.ofNat 152 (word80 [1,0xfffffffffff22feda007])),(BitVec.ofNat 152 (word80 [0x5e02f01c0bc070381,0x701701700c022f8c8db6]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (word80 [0x600300000c0000001,0x80180180100018861924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(4,0,57,0,4)]
def g61A : List (List Nat) := [[],[50]]
def g61D4 (j : Nat) := if j=0 then 0x3f else 0
def g61L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g61D4)
  | _ => emptyPacking
def g61I (_ _ : Nat) : Option (Nat × Nat) := none
def g61 : Forest := ⟨61,4,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4_0 : CutRow g61 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B4 : CutRow g61 4 0 1 := g61P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : mixedTables g61 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g61 0 0
  · exact mixedEmpty g61 1 0
  · exact mixedEmpty g61 2 0
  · exact mixedEmpty g61 3 0
  · exact g61B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 5 := mixedLower (g:=g61) (i:=0) (hints:=21764) (before_sound K55 V55) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K55 5 [(61,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V55 low61 (by decide +kernel)
def g87Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffc07fe03fff,0xe00ffffe07f469d401c7])),(BitVec.ofNat 152 (word80 [0xa0a86a128d0a458a05,0x46a250a4b29029d49249]))),((BitVec.ofNat 152 (word80 [0xfffff00007fffc07f,0xfff007fff813a68c0e38])),(BitVec.ofNat 152 (word80 [0xc1304c1b160c891309,0x84c360c924d1a28c9249]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000007f,0xfffff800000bc8b47000])),(BitVec.ofNat 152 (word80 [0x5c1705c182f0e1c2e,0x70382f1c70bc8b5b6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(BitVec.ofNat 152 (word80 [0x60180602030102030,0x8040300000654212492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x80200800040000040,0x10080400000000024924]))),(0x0,0x0),(0x0,0x0)]
def g87C : List ColumnInfo := [(1,0,86,0,5)]
def g87A : List (List Nat) := [[],[16]]
def g87D5 (j : Nat) := if j=0 then 0x3f else 0
def g87L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g87D5)
  | _ => emptyPacking
def g87I (_ _ : Nat) : Option (Nat × Nat) := none
def g87 : Forest := ⟨87,5,fun i => g87Y[i]?.getD (0,0),g87C,g87A,g87L,g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P5_0 : CutRow g87 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g87B5 : CutRow g87 5 0 1 := g87P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87T : mixedTables g87 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g87 0 0
  · exact mixedEmpty g87 1 0
  · exact mixedEmpty g87 2 0
  · exact mixedEmpty g87 3 0
  · exact mixedEmpty g87 4 0
  · exact g87B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 6 := mixedLower (g:=g87) (i:=0) (hints:=1604) (before_sound K61 V61) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K61 6 [(87,[]),(151,[118]),(155,[50,118]),(167,[33,84,118]),(171,[49,33,84,118]),(174,[32,49,16,84,118]),(203,[50,100,84,117]),(205,[33,49,100,84,117]),(206,[16,32,48,100,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V61 low87 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x3ff80ffff909e9b81c7])),(BitVec.ofNat 152 (word80 [0x41a8251a0a458a02a1,0xa8251a148a00928b9249]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfc0000ffc068da648e00])),(BitVec.ofNat 152 (word80 [0x8530b62c2c891314c1,0x30b62c191348da44b6db]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffffff00000ff10e7038])),(BitVec.ofNat 152 (word80 [0x1c038300f0e1c0701,0xc038301e1c02d10e1249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580a,0x2c000a000192c606db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x30040c0202504304924]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := [(1,0,102,0,4)]
def g103A : List (List Nat) := [[],[32]]
def g103D4 (j : Nat) := if j=0 then 0x3f else 0
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g103D4)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : CutRow g103 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B4 : CutRow g103 4 0 1 := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : mixedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g103 0 0
  · exact mixedEmpty g103 1 0
  · exact mixedEmpty g103 2 0
  · exact mixedEmpty g103 3 0
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := mixedLower (g:=g103) (i:=0) (hints:=1381) (before_sound K87 V87) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K87 5 [(103,[]),(109,[49,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V87 low103 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe007fe1ff0fffc03f,0xffffff0ff9621a00ff0f])),(BitVec.ofNat 152 (word80 [0x140501440220028281,0x4040022088420a111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fe1fff01c1fa90f00f0])),(BitVec.ofNat 152 (word80 [0x982609882402130309,0x80842402180f09333333]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe001ffff239766f000ff])),(BitVec.ofNat 152 (word80 [0x204812004844240402,0x5084800211064444444]))),((BitVec.ofNat 152 (word80 [0xffffff,0xfffe00001369f8000f00])),(BitVec.ofNat 152 (word80 [0xc1705c117088b8282c,0x160170441329f0eeeeee]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0x18060018000c03030,0x1811808846a080888888]))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(0,32,82,1,5),(2,0,113,0,5),(32,0,83,0,5),(1,32,82,0,4),(16,0,99,0,4),(64,0,51,0,4)]
def g115A : List (List Nat) := [[],[100]]
def g115D4 (j : Nat) := if j=0 then 0x5dd4542 else 0
def g115D5 (j : Nat) := if j=0 then 0x108404fd42 else 0
def g115H5 (j : Nat) := if j=0 then 0x4 else 0
def g115D6 (j : Nat) := if j=0 then 0x2c458bf else 0
def g115H6 (j : Nat) := if j=0 then 0x4 else 0
def g115L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g115D4)
  | 5 => (1,1,3,0,0,0,0,g115D5)
  | 6 => (1,0,3,0,0,0,0,g115D6)
  | _ => emptyPacking
def g115I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g115H5
  | 6 => lookupShort 1 2 0 2 0 0 g115H6
  | _ => fun _ => none
def g115 : Forest := ⟨115,6,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P4_0 : CutRow g115 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B4 : CutRow g115 4 0 1 := g115P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P5_0 : CutRow g115 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B5 : CutRow g115 5 0 1 := g115P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P6_0 : CutRow g115 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B6 : CutRow g115 6 0 1 := g115P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : mixedTables g115 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g115 0 0
  · exact mixedEmpty g115 1 0
  · exact mixedEmpty g115 2 0
  · exact mixedEmpty g115 3 0
  · exact g115B4
  · exact g115B5
  · exact g115B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 7 := mixedLower (g:=g115) (i:=0) (hints:=68) (before_sound K103 V103) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K103 7 [(115,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V103 low115 (by decide +kernel)
def g117Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0),(0x0,0x0)]
def g117C : List ColumnInfo := [(4,0,113,0,5)]
def g117A : List (List Nat) := [[],[96,82]]
def g117D5 (j : Nat) := if j=0 then 0x3f else 0
def g117L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g117D5)
  | _ => emptyPacking
def g117I (_ _ : Nat) : Option (Nat × Nat) := none
def g117 : Forest := ⟨117,5,fun i => g117Y[i]?.getD (0,0),g117C,g117A,g117L,g117I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P5_0 : CutRow g117 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g117B5 : CutRow g117 5 0 1 := g117P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117T : mixedTables g117 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g117 0 0
  · exact mixedEmpty g117 1 0
  · exact mixedEmpty g117 2 0
  · exact mixedEmpty g117 3 0
  · exact mixedEmpty g117 4 0
  · exact g117B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117G : graphValid g117 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 6 := mixedLower (g:=g117) (i:=0) (hints:=1284) (before_sound K115 V115) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K115 6 [(117,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V115 low117 (by decide +kernel)
def g118Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0)]
def g118C : List ColumnInfo := [(0,32,82,4,5),(32,0,86,0,5),(2,0,116,0,4),(4,32,82,0,4),(16,0,102,0,4)]
def g118A : List (List Nat) := [[],[65]]
def g118D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g118D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g118H5 (j : Nat) := if j=0 then 0x8 else 0
def g118D6 (j : Nat) := if j=0 then 0x18989f else 0
def g118H6 (j : Nat) := if j=0 then 0x21560023500000 else 0
def g118L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g118D4)
  | 5 => (3,1,3,0,0,5,0,g118D5)
  | 6 => (1,0,3,0,0,0,0,g118D6)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g118H5
  | 6 => lookupShort 1 11 0 5 2 1 g118H6
  | _ => fun _ => none
def g118 : Forest := ⟨118,6,fun i => g118Y[i]?.getD (0,0),g118C,g118A,g118L,g118I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P4_0 : CutRow g118 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B4 : CutRow g118 4 0 1 := g118P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P5_0 : CutRow g118 5 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B5 : CutRow g118 5 0 3 := g118P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P6_0 : CutRow g118 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g118B6 : CutRow g118 6 0 1 := g118P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118T : mixedTables g118 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g118 0 0
  · exact mixedEmpty g118 1 0
  · exact mixedEmpty g118 2 0
  · exact mixedEmpty g118 3 0
  · exact g118B4
  · exact g118B5
  · exact g118B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 7 := mixedLower (g:=g118) (i:=0) (hints:=18941248) (before_sound K117 V117) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K117 7 [(118,[]),(121,[16,64,82,50,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V117 low118 (by decide +kernel)
def g122Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0)]
def g122C : List ColumnInfo := [(0,8,82,32,5)]
def g122A : List (List Nat) := [[],[100],[83],[83,100],[65],[65,97],[65,83],[65,83,97],[97,65],[97],[97,83,65],[97,83]]
def g122D5 (j : Nat) := if j=0 then 0x3f else 0
def g122L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g122D5)
  | _ => emptyPacking
def g122I (_ _ : Nat) : Option (Nat × Nat) := none
def g122 : Forest := ⟨122,5,fun i => g122Y[i]?.getD (0,0),g122C,g122A,g122L,g122I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P5_0 : CutRow g122 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g122B5 : CutRow g122 5 0 1 := g122P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122T : mixedTables g122 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g122 0 0
  · exact mixedEmpty g122 1 0
  · exact mixedEmpty g122 2 0
  · exact mixedEmpty g122 3 0
  · exact mixedEmpty g122 4 0
  · exact g122B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122G : graphValid g122 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low122 : Lower true (varsX 122) (graphGoal 122) 6 := mixedLower (g:=g122) (i:=0) (hints:=20009024) (before_sound K118 V118) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K122 := extendKnown K118 6 [(122,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V118 low122 (by decide +kernel)
def g157Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffc003ffc01ffe00f,0xfffffffffffeddea003f])),(BitVec.ofNat 152 (word80 [0x80a81a8128340a4160,0xa02a094148524c6a1249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffc00001fffff0,0x7ff001ffc0118f681c0])),(BitVec.ofNat 152 (word80 [0x15315315b158ac8a45,0x314c6d89919918f6b6db]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffe000000,0x7ffffe000031f070e00])),(BitVec.ofNat 152 (word80 [0x19c19c19c260cf1389,0xc2704e0de2e31f0736db]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x7fffffffffcbfdc7007])),(BitVec.ofNat 152 (word80 [0x1e01e01e0380f01c0e,0x380700e0300b3942492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf800000000036237fff8])),(BitVec.ofNat 152 (word80 [0x200200200001000000,0x4008010000000004924]))),(0x0,0x0)]
def g157C : List ColumnInfo := [(4,0,153,0,5)]
def g157A : List (List Nat) := [[],[50],[64],[64,50]]
def g157D5 (j : Nat) := if j=0 then 0x3f else 0
def g157L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g157D5)
  | _ => emptyPacking
def g157I (_ _ : Nat) : Option (Nat × Nat) := none
def g157 : Forest := ⟨157,5,fun i => g157Y[i]?.getD (0,0),g157C,g157A,g157L,g157I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g157P5_0 : CutRow g157 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g157B5 : CutRow g157 5 0 1 := g157P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g157T : mixedTables g157 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g157 0 0
  · exact mixedEmpty g157 1 0
  · exact mixedEmpty g157 2 0
  · exact mixedEmpty g157 3 0
  · exact mixedEmpty g157 4 0
  · exact g157B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g157G : graphValid g157 (boundsBefore K122) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low157 : Lower true (varsX 157) (graphGoal 157) 6 := mixedLower (g:=g157) (i:=0) (hints:=30468) (before_sound K122 V122) g157G g157T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K157 := extendKnown K122 6 [(157,[]),(158,[16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V157 : Known true K157 := extend_ok (m:=157) V122 low157 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc07fc01ff03fe07fff,0x7fc0ff81fed6800e07])),(BitVec.ofNat 152 (word80 [0x950a8d44a68a4b282a,0x35129a292ca6d6849249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffe0003fff81ff,0xff8000fffe0725a07038])),(BitVec.ofNat 152 (word80 [0x26130986cb0c924c4c,0x261b2c32493725a49249]))),((BitVec.ofNat 152 (word80 [0x7fffffffc00001ff,0xffffff0000074b4381c0])),(BitVec.ofNat 152 (word80 [0x381c0e070c0f1c7070,0x381c303c71c74b449249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff80000000000001ff,0xfffffffffffacd3c01ff])),(BitVec.ofNat 152 (word80 [0x2010080010000080,0x40200040000000092492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x532dffe00])),(BitVec.ofNat 152 (word80 [0x4020100020000100,0x80400080000000124924]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(1,0,172,0,5)]
def g173A : List (List Nat) := [[],[117],[50],[50,117],[32],[32,117],[32,48],[32,48,117],[48,32],[48,32,117],[48],[48,117]]
def g173D5 (j : Nat) := if j=0 then 0x3f else 0
def g173L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g173D5)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,5,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P5_0 : CutRow g173 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B5 : CutRow g173 5 0 1 := g173P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : mixedTables g173 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g173 0 0
  · exact mixedEmpty g173 1 0
  · exact mixedEmpty g173 2 0
  · exact mixedEmpty g173 3 0
  · exact mixedEmpty g173 4 0
  · exact g173B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K157) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 6 := mixedLower (g:=g173) (i:=0) (hints:=21765) (before_sound K157 V157) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K157 6 [(173,[]),(199,[49,33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V157 low173 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc3fe00ff87f87ffc0,0x7fffffe3dba15000ff0f])),(BitVec.ofNat 152 (word80 [0x288140a05101100285,0x502004842a141111111]))),((BitVec.ofNat 152 (word80 [0x3ffff0007ff87fff,0x807f1ffc2adc600f00f0])),(BitVec.ofNat 152 (word80 [0x310984c26212011306,0x260444812acc43333333]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff80007fff,0xff801fff949db0f000ff])),(BitVec.ofNat 152 (word80 [0x421209048024222408,0x82889001410b4444444]))),((BitVec.ofNat 152 (word80 [0xffc000000000007fff,0xffffe0000b66bf000f00])),(BitVec.ofNat 152 (word80 [0x801c0e070438443810,0x30300e120946b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x2010080040004020,0x40401000000008888888]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(1,0,178,0,5),(2,0,177,0,5),(16,0,163,0,5),(32,0,147,0,5)]
def g179A : List (List Nat) := [[],[64,81]]
def g179D6 (j : Nat) := if j=0 then 0x6c09f else 0
def g179L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g179D6)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,6,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P6_0 : CutRow g179 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B6 : CutRow g179 6 0 1 := g179P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : mixedTables g179 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g179 0 0
  · exact mixedEmpty g179 1 0
  · exact mixedEmpty g179 2 0
  · exact mixedEmpty g179 3 0
  · exact mixedEmpty g179 4 0
  · exact mixedEmpty g179 5 0
  · exact g179B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 7 := mixedLower (g:=g179) (i:=0) (hints:=68) (before_sound K173 V173) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K173 7 [(179,[]),(181,[33,84]),(185,[49,33,84]),(227,[100]),(230,[32,100]),(233,[49,33,84,100]),(236,[32,49,84,100]),(244,[32,65,49,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V173 low179 (by decide +kernel)
def g182Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g182C : List ColumnInfo := [(2,0,180,0,5),(4,0,178,0,5),(16,0,166,0,5),(32,0,150,0,5),(18,0,164,0,4),(36,0,146,0,4)]
def g182A : List (List Nat) := [[],[82],[33,84],[33,65,81],[65],[65,82],[81,33,66],[81,66]]
def g182D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g182D5 := limbs80 #[#[0x3527f7bbf6f4050110,0x5f405d50654155045435,0x66ad0941001546b525d4,0xc08024050462b13e3bb,0x4040201642000001201]]
def g182H5 := limbs80 #[#[0x240000000000000000,0x80000020000400000000]]
def g182D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g182H6 := limbs80 #[#[0xc0170000000000000089,0x21c1020000000000,0x840000000000,0x19c3000000000000,0x130000000000000000,0x0,0x70000000000,0x0,0xc6000000,0x0,0x1109000000000000,0x88,0x1400c5000000000000]]
def g182D7 (j : Nat) := if j=0 then 0x1605f else 0
def g182H7 := limbs80 #[#[0x1894000004,0x400059000800058e8009,0xc20050000000642]]
def g182L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g182D4)
  | 5 => (10,2,3,262147,34,7,1030,g182D5)
  | 6 => (3,1,3,0,0,6,0,g182D6)
  | 7 => (1,0,3,0,0,0,0,g182D7)
  | _ => emptyPacking
def g182I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 29 0 6 2 2 g182H5
  | 6 => lookupShort 4 137 2 8 4 2 g182H6
  | 7 => lookupShort 3 31 1 7 2 3 g182H7
  | _ => fun _ => none
def g182 : Forest := ⟨182,7,fun i => g182Y[i]?.getD (0,0),g182C,g182A,g182L,g182I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P4_0 : CutRow g182 4 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B4 : CutRow g182 4 0 3 := g182P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P5_0 : CutRow g182 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P5_1 : CutRow g182 5 1 9 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B5 : CutRow g182 5 0 10 := (@joinRow g182 5 0 1 9 g182P5_0 g182P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P6_0 : CutRow g182 6 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B6 : CutRow g182 6 0 3 := g182P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182P7_0 : CutRow g182 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g182B7 : CutRow g182 7 0 1 := g182P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182T : mixedTables g182 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g182 0 0
  · exact mixedEmpty g182 1 0
  · exact mixedEmpty g182 2 0
  · exact mixedEmpty g182 3 0
  · exact g182B4
  · exact g182B5
  · exact g182B6
  · exact g182B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g182G : graphValid g182 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low182 : Lower true (varsX 182) (graphGoal 182) 8 := mixedLower (g:=g182) (i:=0) (hints:=270599488) (before_sound K179 V179) g182G g182T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K182 := extendKnown K179 8 [(182,[]),(186,[50]),(234,[50,100]),(248,[49,66,82,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V182 : Known true K182 := extend_ok (m:=182) V179 low182 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f01fc7f01fc7e7fc,0x7f1f9fe7ea000f00f0f])),(BitVec.ofNat 152 (word80 [0x50a14290a142905028,0x50a414051ea111111111]))),((BitVec.ofNat 152 (word80 [0x7ffe007ffe007f9ff,0xf801fe7f8b700f00f0f0])),(BitVec.ofNat 152 (word80 [0x60c18320c183208430,0x60c821084b7111111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8000007fffff801ff,0xfffe007fe640f00f00ff])),(BitVec.ofNat 152 (word80 [0x810204010204010040,0x81004010000222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff800000001ff,0xffffff8001af000fff00])),(BitVec.ofNat 152 (word80 [0x20408020408020081,0x2008020000444444444]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x181ffff00000])),(BitVec.ofNat 152 (word80 [0x40810040810040102,0x4010040000888888888]))),(0x0,0x0)]
def g211C : List ColumnInfo := [(1,0,210,0,7)]
def g211A : List (List Nat) := [[],[118],[100],[100,116],[116,100],[116],[16],[16,118],[16,100],[16,100,116],[16,116,100],[16,116]]
def g211D7 (j : Nat) := if j=0 then 0x3f else 0
def g211L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g211D7)
  | _ => emptyPacking
def g211I (_ _ : Nat) : Option (Nat × Nat) := none
def g211 : Forest := ⟨211,7,fun i => g211Y[i]?.getD (0,0),g211C,g211A,g211L,g211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P7_0 : CutRow g211 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B7 : CutRow g211 7 0 1 := g211P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211T : mixedTables g211 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g211 0 0
  · exact mixedEmpty g211 1 0
  · exact mixedEmpty g211 2 0
  · exact mixedEmpty g211 3 0
  · exact mixedEmpty g211 4 0
  · exact mixedEmpty g211 5 0
  · exact mixedEmpty g211 6 0
  · exact g211B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211G : graphValid g211 (boundsBefore K182) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low211 : Lower true (varsX 211) (graphGoal 211) 8 := mixedLower (g:=g211) (i:=0) (hints:=68) (before_sound K182 V182) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K211 := extendKnown K182 8 [(211,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V182 low211 (by decide +kernel)
def g213Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g213C : List ColumnInfo := [(4,0,209,0,7)]
def g213A : List (List Nat) := [[],[118],[64],[64,118]]
def g213D7 (j : Nat) := if j=0 then 0x3f else 0
def g213L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g213D7)
  | _ => emptyPacking
def g213I (_ _ : Nat) : Option (Nat × Nat) := none
def g213 : Forest := ⟨213,7,fun i => g213Y[i]?.getD (0,0),g213C,g213A,g213L,g213I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P7_0 : CutRow g213 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B7 : CutRow g213 7 0 1 := g213P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213T : mixedTables g213 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g213 0 0
  · exact mixedEmpty g213 1 0
  · exact mixedEmpty g213 2 0
  · exact mixedEmpty g213 3 0
  · exact mixedEmpty g213 4 0
  · exact mixedEmpty g213 5 0
  · exact mixedEmpty g213 6 0
  · exact g213B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213G : graphValid g213 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low213 : Lower true (varsX 213) (graphGoal 213) 8 := mixedLower (g:=g213) (i:=0) (hints:=1540) (before_sound K211 V211) g213G g213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K213 := extendKnown K211 8 [(213,[]),(214,[16]),(241,[64,82,50,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V213 : Known true K213 := extend_ok (m:=213) V211 low213 (by decide +kernel)
def g217Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0)]
def g217C : List ColumnInfo := [(8,0,209,0,7)]
def g217A : List (List Nat) := [[],[100],[64],[64,96],[96,64],[96]]
def g217D7 (j : Nat) := if j=0 then 0x3f else 0
def g217L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g217D7)
  | _ => emptyPacking
def g217I (_ _ : Nat) : Option (Nat × Nat) := none
def g217 : Forest := ⟨217,7,fun i => g217Y[i]?.getD (0,0),g217C,g217A,g217L,g217I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217P7_0 : CutRow g217 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g217B7 : CutRow g217 7 0 1 := g217P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217T : mixedTables g217 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g217 0 0
  · exact mixedEmpty g217 1 0
  · exact mixedEmpty g217 2 0
  · exact mixedEmpty g217 3 0
  · exact mixedEmpty g217 4 0
  · exact mixedEmpty g217 5 0
  · exact mixedEmpty g217 6 0
  · exact g217B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217G : graphValid g217 (boundsBefore K213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low217 : Lower true (varsX 217) (graphGoal 217) 8 := mixedLower (g:=g217) (i:=0) (hints:=28676) (before_sound K213 V213) g217G g217T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K217 := extendKnown K213 8 [(217,[]),(218,[16]),(242,[16,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V217 : Known true K217 := extend_ok (m:=217) V213 low217 (by decide +kernel)
def g229Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fe1fe01fe1fc3ffc,0x7ffe3ff1ecd460071c7])),(BitVec.ofNat 152 (word80 [0x141441414144088028,0x50a04802424506249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe001fffe001ffc3ff,0xf80ffc7fe17493038e38])),(BitVec.ofNat 152 (word80 [0x181881818188100830,0x60c08104095412249249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffe0003ff,0xfff0007ffcc2f51c003f])),(BitVec.ofNat 152 (word80 [0xa0a10a0a0a00a11140,0x810512280082e1492492]))),((BitVec.ofNat 152 (word80 [0xffffe00000000003ff,0xffffff80003b4be00fc0])),(BitVec.ofNat 152 (word80 [0xc0c00c0c0c10c22181,0x2060030902a49492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffc00,0x30628fff000])),(BitVec.ofNat 152 (word80 [0x10010101001000202,0x4080040000000924924]))),(0x0,0x0)]
def g229C : List ColumnInfo := [(1,0,228,0,5)]
def g229A : List (List Nat) := [[],[101],[32],[32,101],[80,98],[80,98,32],[96,82,32],[96,82]]
def g229D5 (j : Nat) := if j=0 then 0x3f else 0
def g229L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g229D5)
  | _ => emptyPacking
def g229I (_ _ : Nat) : Option (Nat × Nat) := none
def g229 : Forest := ⟨229,5,fun i => g229Y[i]?.getD (0,0),g229C,g229A,g229L,g229I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P5_0 : CutRow g229 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B5 : CutRow g229 5 0 1 := g229P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229T : mixedTables g229 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g229 0 0
  · exact mixedEmpty g229 1 0
  · exact mixedEmpty g229 2 0
  · exact mixedEmpty g229 3 0
  · exact mixedEmpty g229 4 0
  · exact g229B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229G : graphValid g229 (boundsBefore K217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low229 : Lower true (varsX 229) (graphGoal 229) 6 := mixedLower (g:=g229) (i:=0) (hints:=1285) (before_sound K217 V217) g229G g229T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K229 := extendKnown K217 6 [(229,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V229 : Known true K229 := extend_ok (m:=229) V217 low229 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffffffffffc0001f,0xfff5960d3cda07900f0f])),(BitVec.ofNat 152 (word80 [0xd40554a0155482aac1,0x554496013cc205811111]))),((BitVec.ofNat 152 (word80 [0xfe00000fffffffffe0,0x21573fe243e2000f0])),(BitVec.ofNat 152 (word80 [0x988666c4199904cc82,0x66621413fc203e255555]))),((BitVec.ofNat 152 (word80 [0xfffffff00000000000,0xd32e8f462f040f000])),(BitVec.ofNat 152 (word80 [0xe02787015e1e0f0f07,0x878d12e8f46290433333]))),(0x1db31d1c98c6f0000,(BitVec.ofNat 152 (word80 [0x37f8019fe017f00b,0xf8019b21d1c88c633333]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xfff311ee8fcfdc9000ff])),(BitVec.ofNat 152 (word80 [0x1380009e00018000c,0x101ec030dc01aaaaa]))),(0xcee977135e36fff00,(BitVec.ofNat 152 (word80 [0x1c0000e0000200010,0x60160015620ccccc]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(2,0,61,0,5)]
def g63A : List (List Nat) := [[],[50]]
def g63D5 (j : Nat) := if j=0 then 0x7f else 0
def g63L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g63D5)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,5,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : CutRow g63 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : CutRow g63 5 0 1 := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : mixedTables g63 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g63 0 0
  · exact mixedEmpty g63 1 0
  · exact mixedEmpty g63 2 0
  · exact mixedEmpty g63 3 0
  · exact mixedEmpty g63 4 0
  · exact g63B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 6 := mixedLower (g:=g63) (i:=0) (hints:=21828) (before_sound K229 V229) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K229 6 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V229 low63 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ffff8000ffffff,0xffe9602e3358ab00f00f])),(BitVec.ofNat 152 (word80 [0xab502aa5155a0aaa45,0x5528600a3348aa111111]))),((BitVec.ofNat 152 (word80 [0xfff800000000ffffe0,0x2a5fb8b20d500f0000])),(BitVec.ofNat 152 (word80 [0x3260b336266c0ccc89,0x99aa5f38b20940333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0x14c31bf86126f000f0])),(BitVec.ofNat 152 (word80 [0xc3803c3838700f0f0e,0x1e04c11af04126111111]))),(0x769db068ae4000f00,(BitVec.ofNat 152 (word80 [0xfc023fc03f804ff00f,0xe007699b060aa4555555]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xffcc4f666ee7c9000fff])),(BitVec.ofNat 152 (word80 [0x4c0000000900000,0x66408a441aaaaaa]))),(0x33b4dd991e36fff000,(BitVec.ofNat 152 (word80 [0x700004000e00010,0x1100c5081610cccccc]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(1,0,110,0,5)]
def g111A : List (List Nat) := [[],[49,101],[32],[32,49,101]]
def g111D5 (j : Nat) := if j=0 then 0x7f else 0
def g111L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g111D5)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,5,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : CutRow g111 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B5 : CutRow g111 5 0 1 := g111P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : mixedTables g111 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g111 0 0
  · exact mixedEmpty g111 1 0
  · exact mixedEmpty g111 2 0
  · exact mixedEmpty g111 3 0
  · exact mixedEmpty g111 4 0
  · exact g111B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 6 := mixedLower (g:=g111) (i:=0) (hints:=21861) (before_sound K63 V63) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K63 6 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V63 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0xb261513c2a0001f07c1f])),(BitVec.ofNat 152 (word80 [0x2a035012805216141,0xb0605114080842108421]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x17e8d44785003e0003e0])),(BitVec.ofNat 152 (word80 [0x44c12609b046424262,0x1360d40781294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c2c299d107c00f8000])),(BitVec.ofNat 152 (word80 [0x17003801c017838381,0x98c2c018d118c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4fe283ab8f8000003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x48a2828305294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1711a3877600000ffc00])),(BitVec.ofNat 152 (word80 [0xe00b805c02e0040408,0x711228326e739ce739c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x40150240048421084210]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7),(4,0,115,0,7),(0,32,82,5,6),(2,0,117,0,6),(32,0,87,0,6),(16,0,103,0,5),(34,0,85,0,5),(64,0,55,0,5),(17,0,102,0,4),(66,0,53,0,4)]
def g119A : List (List Nat) := [[]]
def g119D5 := limbs80 #[#[0x18553595315513154531,0xdc7df2eb3dd4731d8553,0x4e8dc53d94e54c7575b9,0x52555225c1c59695cee5,0x20e0b962a50992224059]]
def g119D6 := limbs80 #[#[0x6ef51cc65354d514c453,0x12c03f7dfbf7f5efefaf,0x544a6a7076160b101584,0x293594b2a85e532ea998,0x46b2d6552baa76351a7b,0x3617030b358f2aa79553,0xa90d618d2a365519ec2e,0xc2b0f83c006b2c695232,0x1047a391a8c259279186,0x34994c05c2c14c9c4a23,0x2231700c7833f5e8ec70,0x804840d80a011201bd02,0x10000404000000020080,0x3217008010100004050,0x40402010]]
def g119H6 (j : Nat) := if j=0 then 0xe37cd50260a1024010 else 0
def g119D7 := limbs80 #[#[0xea354798d314a8553fef,0x5402b1600ea794ea9c53,0x988711630c5ae97806b5,0xaa040548202aa100a34,0x280a0e82c06381015444,0x50141980103b00807]]
def g119H7 := limbs80 #[#[0x1801a00718821,0x9d002e030800000,0x1002e9b60000480011c0,0xaa000000000400000063,0x403a0000037b01400000,0x8a0000001640006,0x100000c]]
def g119D8 (j : Nat) := if j=0 then 0x3421017f else 0
def g119H8 := limbs80 #[#[0x4c80a36037240c658f08,0x1]]
def g119L : Nat → Packing
  | 5 => (9,3,4,458758,51,7,1025,g119D5)
  | 6 => (27,2,4,589831,67,9,4102,g119D6)
  | 7 => (10,1,4,131073,16,8,4105,g119D7)
  | 8 => (1,0,4,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 2 13 0 6 4 0 g119H6
  | 7 => lookupShort 6 71 2 7 5 0 g119H7
  | 8 => lookupShort 2 13 2 6 4 0 g119H8
  | _ => fun _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : CutRow g119 5 0 9 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : CutRow g119 5 0 9 := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : CutRow g119 6 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_5 : CutRow g119 6 5 22 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : CutRow g119 6 0 27 := (@joinRow g119 6 0 5 22 g119P6_0 g119P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : CutRow g119 7 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_2 : CutRow g119 7 2 8 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : CutRow g119 7 0 10 := (@joinRow g119 7 0 2 8 g119P7_0 g119P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : CutRow g119 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B8 : CutRow g119 8 0 1 := g119P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : mixedTables g119 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g119 0 0
  · exact mixedEmpty g119 1 0
  · exact mixedEmpty g119 2 0
  · exact mixedEmpty g119 3 0
  · exact mixedEmpty g119 4 0
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := mixedLower (g:=g119) (i:=0) (hints:=1348) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 9 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffffffffffff,0x451d37930c4801f003ff])),(BitVec.ofNat 152 (word80 [0x581400540128029029,0x40141692044042108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc00fffe0003fff800,0xfa255c2e0c903e007c00])),(BitVec.ofNat 152 (word80 [0x90a602980db01320cc,0xea055c220c80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4d2d3ab80000f8000])),(BitVec.ofNat 152 (word80 [0xe13844e089c11bc170,0x3944d293a982d6b5ad6b]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bca0bd9efc000001f])),(BitVec.ofNat 152 (word80 [0x1c017002e005c0180,0x2894809d9898c6318c6]))),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa317cb680000fffe0])),(BitVec.ofNat 152 (word80 [0x98013002600200,0xaa214c1205294a5294]))),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x1522a0402036318c6318]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(4,0,121,0,7)]
def g125A : List (List Nat) := [[]]
def g125D7 (j : Nat) := if j=0 then 0x7f else 0
def g125L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g125D7)
  | _ => emptyPacking
def g125I (_ _ : Nat) : Option (Nat × Nat) := none
def g125 : Forest := ⟨125,7,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : CutRow g125 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : CutRow g125 7 0 1 := g125P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : mixedTables g125 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g125 0 0
  · exact mixedEmpty g125 1 0
  · exact mixedEmpty g125 2 0
  · exact mixedEmpty g125 3 0
  · exact mixedEmpty g125 4 0
  · exact mixedEmpty g125 5 0
  · exact mixedEmpty g125 6 0
  · exact g125B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 8 := mixedLower (g:=g125) (i:=0) (hints:=21764) (before_sound K119 V119) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K119 8 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V119 low125 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00007fffffffff000,0xffffd9eb04f512001c7])),(BitVec.ofNat 152 (word80 [0x82ab50554a05552155,0x61554c9c304b51249249]))),((BitVec.ofNat 152 (word80 [0xfffff80000ffffffff,0xf000063937d0b9800e38])),(BitVec.ofNat 152 (word80 [0x33260666c06664266,0x4266663832d099849249]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000000,0xdf59ba185007000])),(BitVec.ofNat 152 (word80 [0x13c382787057878787,0x87878df59ba1850db6db]))),(0x1df0a8a3bc38000,(BitVec.ofNat 152 (word80 [0x1bfc037f8067f80bf8,0xbf801df0a8a3bcdb6db]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xfffff317fd87b4fc003f])),(BitVec.ofNat 152 (word80 [0x1c0003800078000c00,0xc000103cd0424492492]))),(0x0,0x0),(0x0,0x0),(0xce84a784f5fffc0,(BitVec.ofNat 152 (word80 [0x200004000080000000,0x124924]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(1,0,158,0,6)]
def g159A : List (List Nat) := [[],[50],[16],[16,50]]
def g159D6 (j : Nat) := if j=0 then 0x7f else 0
def g159L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g159D6)
  | _ => emptyPacking
def g159I (_ _ : Nat) : Option (Nat × Nat) := none
def g159 : Forest := ⟨159,6,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_0 : CutRow g159 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B6 : CutRow g159 6 0 1 := g159P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : mixedTables g159 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g159 0 0
  · exact mixedEmpty g159 1 0
  · exact mixedEmpty g159 2 0
  · exact mixedEmpty g159 3 0
  · exact mixedEmpty g159 4 0
  · exact mixedEmpty g159 5 0
  · exact g159B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 7 := mixedLower (g:=g159) (i:=0) (hints:=30532) (before_sound K125 V125) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K125 7 [(159,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V125 low159 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffe0000ffffc000fff,0xfffffd464660f3000e07])),(BitVec.ofNat 152 (word80 [0xa54556a1552955a2aa,0x92aa9d464440f3249249]))),((BitVec.ofNat 152 (word80 [0xfffffff00000000fff,0xf8000c36a319de007000])),(BitVec.ofNat 152 (word80 [0xc98664c599b266c333,0x24cccc36a319de6db6db]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffff000,0x1b94f18362038038])),(BitVec.ofNat 152 (word80 [0xe078701e1c38703c3,0xc70f1b94f08162249249]))),(0x3e3a84ce61c01c0,(BitVec.ofNat 152 (word80 [0xf007f801fe03f803fc,0x7f003e2a84ce2249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xffffe64fd33f27e001ff])),(BitVec.ofNat 152 (word80 [0x800060000000400,0x9033204492492]))),(0x0,0x0),(0x19b82cd0d8fffe00,(BitVec.ofNat 152 (word80 [0x1000080000000800,0x924924]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(1,0,174,0,6)]
def g175A : List (List Nat) := [[],[50],[32],[32,48],[48,32],[48]]
def g175D6 (j : Nat) := if j=0 then 0x7f else 0
def g175L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g175D6)
  | _ => emptyPacking
def g175I (_ _ : Nat) : Option (Nat × Nat) := none
def g175 : Forest := ⟨175,6,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : CutRow g175 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : CutRow g175 6 0 1 := g175P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : mixedTables g175 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g175 0 0
  · exact mixedEmpty g175 1 0
  · exact mixedEmpty g175 2 0
  · exact mixedEmpty g175 3 0
  · exact mixedEmpty g175 4 0
  · exact mixedEmpty g175 5 0
  · exact g175B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 7 := mixedLower (g:=g175) (i:=0) (hints:=21877) (before_sound K159 V159) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K159 7 [(175,[]),(207,[49,33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V159 low175 (by decide +kernel)
def g183MarkBits := limbs80 #[#[0x6284880e182840608080,0x4c49220248901e3868c1,0x8299305ca962a2439428,0xb0d1a2448d3814d8d326,0xa03e7829b1a6c29b2e74,0xf3e9101f4c95223440d0,0x5ab159554a54a8064939,0xe346920a90fac58b162e,0xc868d629d8120a3572f3,0x5ab4369c93356b4aa73e,0xdb3746dcb84edc6b66cd,0x4282c49404efd5be7af1,0xf3f1e3c68a14dc42f0cb,0x132468d7a146c8127cf9,0xa3654a4e365ca972848d,0x346cc94f654a952a50d1,0x4fd19048cd09e6e74e91,0x9053e7c2850a142853e1,0x92241429224142850a48,0x2244891224142b1a4142,0x285249d39]]
def g183Labels : Array Nat := #[0x82040241082420,0x6220a0d02a2320,0x400040209402452,0x62240241022350,0x22040241022150,0x210110c8461130,0x2220a0d02a2320,0x210110c8461110,0x22040241022130,0x2200a0d02a2120,0x880110c84c8451,0x44800a0d02c8230,0x40010a054682143,0x2200a0d02a2130,0x200040205201141,0x602240209203251,0x22040281022110,0x82040281082410,0x2200a0d02a2140,0x283040281083420,0x400040211402442,0x6220a0d02a2330,0x22040281022120,0x400040211402463,0x6220a0d02a2350,0x41040241041231,0x28011288468140,0x443040241043231,0x10010180c9609043,0x22240281022330,0x283040209083441,0x210110c8461120,0x21040241021120,0x28011288468130,0x48018240248241,0x208011208249043,0x283040281083452,0x208001208249042,0x208001208249053,0x283040281083442,0x62240281022350,0x441040241041231,0x200040209201262,0x6220a0d02a2340,0x6220a0902a2330,0x6220a0d02a2360,0x62240281022340,0x48008240248241,0x2220a0d02a2330,0x28011288468150,0x208011288649053,0x1000008049208264,0xa1440241021550,0x22040241022140,0x280110c8468150,0x28010280428140,0x28011280468140,0x44800a0d02c8241,0x1000008045208164,0x208011288649063,0x443040241043220,0x283040281083431,0x602240209203262,0x443040241043261,0x200011288649063,0xa10110c8461120,0x220080d0222130,0x22040281022130,0x23040281023130,0x220402c1022130,0x220082c0222140,0x20011108c641152,0x210110c8461150,0x280440209201652,0x200040209201252,0x602040209203252,0x208000208249042,0xa14110c8461530,0x283040281083432,0x2820110484c2432,0x23040241023130,0x280102c0428140,0x28008240228150]
def g183Mark (j : Nat) := g183Labels[packedAt g183MarkBits (7*j) 7]?.getD 0
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff000ffffff80fe5f3,0xf07c7c000040675b])),(BitVec.ofNat 152 (word80 [0x2a06a04a02916285f1,0x249108484000000211b]))),((BitVec.ofNat 152 (word80 [0xfffff000fffff019b8,0xa00700038061898794a7])),(BitVec.ofNat 152 (word80 [0x4c24c26c232244d9b0,0xab595294942008821407]))),((BitVec.ofNat 152 (word80 [0xffffffff0000000545,0xb0380f8000020e3818c3])),(BitVec.ofNat 152 (word80 [0x700700700bc3870545,0xb6cb318d8c020a1000c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffea2b,0x81c00003ff83f03fe0f5])),(BitVec.ofNat 152 (word80 [0x804804804c0000020a,0x4a6a5292a8aa23cc0e0]))),((BitVec.ofNat 152 (word80 [0x480,0x7e000ffc03fc003fff02])),(BitVec.ofNat 152 (word80 [0x7007007004080000,0x4934c630332820a75e24]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1354,0x4ffff00003ffffc00008])),(BitVec.ofNat 152 (word80 [0x8008008000000000,0x842405145400000]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,8),(2,0,181,0,7),(4,0,179,0,7),(16,0,167,0,6),(32,0,151,0,6),(17,0,166,0,5),(18,0,165,0,5),(20,0,163,0,5),(34,0,149,0,5),(36,0,147,0,5),(128,0,55,0,5),(19,0,164,0,4),(22,0,161,0,4),(38,0,145,0,4),(130,0,53,0,4),(132,0,51,0,4)]
def g183A : List (List Nat) := [[],[33,84]]
def g183D4 := limbs80 #[#[0xa9a878e1826057019543,0xc3326e8c00e2]]
def g183D5 := limbs80 #[#[0x58053dd95314d6454c53,0x4c5535885354d6114d53,0x5c06550d535454154d51,0x54d431c55350d7119543,0x90d7018553dc16550f71,0xdd953d0574d473154d62,0x5935154d43d455458f41,0xc7b1dbd279dc964d4f72,0xd9756d573cce735ccf27,0xb009f17b4ec7a5e8f95,0x704e62c8546c8c43027,0x4ee316f0502286f8a866,0x52a6730eca5ee893aa32,0x4102b12a681aa671aca7,0x370e3870227f02d4702b,0x42c8c3702176e207f024,0x231b1109002ca732aa73,0x736b635b534b433b332b,0xc3bbb3aba39b938b837b,0x20200016308d3cb]]
def g183H5 (j : Nat) := if j=0 then 0x37 else 0
set_option maxRecDepth 32000 in
def g183D6 := limbs80 #[#[0x58853584535805354c53,0x54d31545315452159053,0x99531595315913155131,0x5514154d415454150d41,0x54d43195439954159541,0xd4d439954394d4359543,0x54d5150d51d9543d8543,0x18553d9151d8d51d4551,0xd4d53951535515319153,0x54e43d9153d8953d8553,0x95253d524358a4355243,0x5533154f3150731d4e53,0xd4731997315973159331,0x58f415534154f4150f41,0x54f5150f519974159741,0x58b53587535935158f51,0xdedf3f9f4f6773759353,0xaecf5fa7cfdfafb7cbdd,0x7eef5fabbedeeef6fb6d,0xdc4555530df9fafb7d7e,0x9eb1546e1dc885553662,0xf702825c490d70241dc,0x5305054c0b953522dc4a,0x3e0dd80316400e54c1bd,0x35956e9545a1dca02170,0x4c6b5645f15917257467,0xd595375654cd13766b75,0xc71265dd09b56475158d,0x42b89509e15427bdc49e,0xea5c0915742e65d4ae25,0x59036d530dc5482cf643,0x41f721115903ef710f3],#[0xcf71124dd84117610d59,0x74164dd054f71144dd44,0x67b54d9a6755bb54d691,0xbdc574d766735959ed73,0xd9791765e7dc97a7715f,0x91374633dc589375604d,0x9541b7d4c6e9431a45d1,0x518d5946615319adc466,0xe4dd8727711c5dd46157,0xdc4817731f9dc87eb711,0xda1173224dcc84b72213,0x97756855d5a356569854,0x536e45d9ac5636a9dc5a,0x6f11d5b93756ed551bc7,0x9dc9b47756f19d5bc575,0x4ce1173724dcdc17736d,0xd47633495d0e25733975,0x1733c45d0edf71364dd8,0x1764dd9d1176749dc5d1,0xb2dc9e9374793dc5e5f7,0x5d4c355431154cc13737,0x89af6526b1949a771264,0xe3742781d099b722645d,0x762b11d89db652761949,0x24b5949257124bd94b9a,0xbd94a277128adc0a1276,0xc4a4f712931c4a537028,0xb2f652c4dcca4773284d,0xb54532551491713245cc,0x3507dc9447764fbdc53c,0x465cd52e6550b59541b7,0x550152540345500ad655],#[0x404a540725501ce54053,0xb654091dd80456401bdc,0x62493589226763f3590f,0x49bdcd24f6349bd4d24f,0x3d9124e6449359124c64,0x4924d524845d124d5149,0x24f73493dc924d72493d,0xf5449395124d54493151,0x44939d124d744931d124,0x265d1191744b25492cf7,0x591037644465cd11b734,0x1611724c45c5336644cd,0x91747d3505f19735665d,0x4180d506011747f2509f,0x80dd0a03542804dc6037,0x50001372812dca04872,0xc3b86b0b21241b82e03a,0x88c61762c0528931101f,0x34244450861041e83ac6,0x336634ba96a2ba540a01,0xe810fb1e63bc734da1a7,0x3522a3d46a8b512a1d41,0x42a7d4ea9b532a5d4aa9,0xabd56aab552a9d52aa35,0xd5eabb572add5aab3562,0x6acb592b1d62ac3582af,0xdb5b2b5d6aad35a2b3d6,0x5d2b9d72ae35c2b7d6ea,0x2bdd7aaf35e2bbd76aeb,0x1d82b03602bfd7eafb5f,0x8ab13622c3d86b0b612c,0xb23642c7d8eb1b632c5d],#[0x3662cbd96b2b652c9d92,0x82cfd9eb3b672cdd9ab3,0xd3da6b4b692d1da2b436,0xdaeb5b6b2d5daab536a2,0x6b6b6d2d9db2b636c2d7,0x7b6f2dddbab736e2dbdb,0x712e1dc2b83702dfdbeb,0x2e5dcab93722e3dc6b8b,0x9dd2ba3742e7dceb9b73,0xdabb3762ebdd6bab752e,0xbc3782efddebbb772edd,0x37a2f3de6bcb792f1de2,0xc2f7deebdb7b2f5deabd,0x370f6beb7d2f9df2be37,0xd122840e1180c40e0828,0x34649900454a08b0a3c4,0x4438210058806017a20,0xbaa100200802812c4857,0x9f0764800801002004,0x2b21dc908b610000ba22,0xc3352887486683341934,0x788435c443da0d90c6,0x1db0b01cd877108]]
def g183H6 := limbs80 #[#[0x2c00009218,0xcb00000000004d000000,0x0,0x90000000000d000,0xb0154c1a00000000,0xd6000000000000000000,0x8f000000c82e,0x0,0x0,0x8a000047860000000000,0x18000000000000000000,0x5905f1210000,0x440000000000ce4300,0x0,0x910000c200000000,0x971300001400810000]]
set_option maxRecDepth 32000 in
def g183D7 := limbs80 #[#[0x54d5150d414c52114c43,0xbb7afd4f51d073194e43,0x63bfffdf7efdfbfbebdb,0x4d611458049628198ec5,0x448f6170990416412588,0x854ce551359949565295,0x1a9506966535594d5643,0x665a55969564a854ea75,0x51565475511d43495451,0x596dd54b558edd43b599,0x6654d976269d459665b5,0x53c558b176465d8d9b53,0x1565055931563c6d4f19,0x9562535854d576155994,0x854e1765559955565551,0x41854c56658559615648,0x76179d85e46175994556,0x2635395d91e35375d89d,0x5935562d558755659559,0x6a54ee9534a552a95435,0x655ad4d69535a50f2943,0x29548ad956a655a59568,0x91e8647a951e9547ad52,0xad4d2b54aad50ea549ad,0x36a54da9626a549ab53b,0x963ca54f29646a551a96,0x6b615a5856964ca5532,0x589eb617a585ea541a55,0x7a591eb547ad4deb627a,0xa9936964dad526a64,0x9a08807606404802c017,0x211f10b0f50da0c40ac0],#[0x1b51a018817015d14913,0x5523f22a2141f81e11cc,0x22e82cc2b329a28226b2,0x38236a35434032c31830,0xb3f43e23d03ba3a7395,0xf4ab48e47745f44042c4,0x53351f50b4f94e54d34b,0xd25c05a358b57856554a,0x165864162460c5f85e45,0x6e56d96c06ab69668167,0x8977075773c72c721706,0x27da7d27ca7bd7ad79d7,0x81280a8027fa7f27ea7e,0x4a84283a83282a82281a,0x287a87286a86285a8528,0x1308aa8a289a89288a88,0x9124f20136138c1870ca,0x77088d3164890ca39c24,0x17851d1078c0511d8408,0x10cc20428810a2042881,0xd30234f81054f84122e2,0x1021d8224744067c206d,0x1256090d66190dc7021e,0xd0102bb3810f47121bb4,0x8782233b248e7520911,0x98e24b99246f96822ec6,0xef28414cc864861c324b,0x40cf840d3e304baf0891,0x326cd245d8810f0810f8,0x11f230470608d101ba20,0xf80104c760890c204308,0x778846eb740c1c80c14c],#[0xa4080b6780825338247,0x60a51821110298608406,0x96fc824a582484040a40,0x4204a748448f080de101,0x381081014c20428412ce,0xfb091ddc04096cc3890f,0x52043d211eea119e8492,0x48131011f0a091e3a087,0x490600d8088dc44430f8,0x2119ce909178888777e8,0x5010a01eea11d]]
def g183H7 := limbs80 #[#[0x8144be1c080090200283,0xc82a8140006045817,0x84858ebcb871051d9b0a,0x18d000e6803409311062,0x82144807a04100071800,0x7715418b1dac69f06041,0x241f93c2eb435f64d0,0xf65a8c441a01965788ee,0xbfbc8901240000000126,0x368ac0000034a613037a,0x69e5932e13cd440618ea,0x32da5ce6b98071800057,0x430884a86e24b53acf73,0x16634557198000000cae,0x497d1f03b11c2d30698a,0x1001a974e2d158a236a8,0xb12a8238009040006659,0xc871ae964c0002a48005,0x85258e89dab36b0004bd,0x3eb04fa96c0077c27a22,0xce70c8006389a59076,0xa9718c4a054cf4323228,0xaaea6c986521c90ac65d,0xcb198a8cd01bc34cc2f3,0xdc9e00113f04a6a90a2,0x3814960c11ca588f7110,0x688465215e2814c00242,0x3c88600f07f1e89f57a2,0x1400e5c755c192380008,0x45803ad70bb61e2a152,0xd2ce43f889234139ae2d,0x1500000244074cb221a1],#[0x879aeecd08e4481b459e,0x8000002da0000ff66e16,0x3e624528a600358a81c9,0x3d7b000cb95c00056f8,0x27f11302c00000d5a003,0xe87aa452880013e9e14d,0x521b1a8c750e3ad743a6,0x121d2d97e260000008,0x712c020012f000000432,0xea790018233b47cb9de1,0x82584318e1a5a91c80,0xd8d357648000192571f0,0x6b29c6f6342881291ca1,0x685038205f186338995a,0x4980a714cbe5e87e9839,0x6a3001a752040600b17f]]
def g183D8 := limbs80 #[#[0x7a8aa3a0a8398a6290ff,0x3006a729aa629c86a188,0xabb53250f663270ec4e1,0x92869c860b211380bc1a,0x6b4408f8206f040d427b,0xc020adc020af23046c40,0x3be3020a7c10418411d,0xf6020a308220410f841]]
def g183H8 := limbs80 #[#[0x11140100212001100102,0x31a27201025512100,0x4fb308fc0000,0x33ddb49c44800000001a,0x81f000000017600171bb,0x800000005240009c0023,0x98,0x11100000001c80000000,0x8ee720000003c0000,0xc000024e000000001402,0xce32c8de659a,0x8cc5300000000b722200,0xc000000000000002730b,0x800c90001a40000000c6,0x64a00000000000034bcd,0x398000000000001,0x3325b209000000000000,0x8004a00c002e70000000,0x1d084001400055,0xb5491000,0x63598000000090,0x3500000000008d,0x2b860000000000000,0x17d640000,0x857009e9000004100000,0x2db00000cbf0d0036f82,0x19e8f000000000000000,0x2eb104000000000,0x1550034f00,0xcd40009a000000000000,0x8000000000206000008a,0x16a0000051],#[0x5e0000033c0016d7500,0x1c00,0xc000000000000d772dc6,0x22904f3a4004d9840078,0xc0000000000000005100,0x11ef217c4449800ab,0x40000000150000000000,0xc900000000000000026,0x5d139003530000000,0x8071e838cd0000000,0x5886615571ea48fce00,0x49689d9d03514d7d2,0x1c000003167d5426c,0x7640000000000db80000,0xc000022000007000008c,0xf2a001430000000000cc,0x977754000011a00000a6,0xd6]]
def g183D9 (j : Nat) := if j=0 then 0x2100ff else 0
def g183H9 := limbs80 #[#[0x1b00000000019a80c50,0x800003e3a0066b000000,0xd0000000d00228000024,0xd7000630000027013196,0x1141,0xc79c45401e8000000140,0x1]]
def g183L : Nat → Packing
  | 4 => (2,5,4,0,0,3,0,g183D4)
  | 5 => (27,4,4,1179668,85,8,1026,g183D5)
  | 6 => (219,3,4,1900609,87,11,4120,g183D6)
  | 7 => (120,2,4,720910,68,12,4121,g183D7)
  | 8 => (14,1,4,65537,0,9,4109,g183D8)
  | 9 => (1,0,4,0,0,0,0,g183D9)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 3 1 0 g183H5
  | 6 => lookupShort 8 163 1 8 5 1 g183H6
  | 7 => lookupShort 66 307 7 11 8 1 g183H7
  | 8 => lookupShort 37 379 4 10 7 1 g183H8
  | 9 => lookupShort 6 67 2 7 4 1 g183H9
  | _ => fun _ => none
def g183 : Forest := ⟨183,9,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P4_0 : CutRow g183 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P4_1 : CutRow g183 4 1 1 := by
  apply polarBlock (data:=fun j => g183Mark (j+0)) rfl
  decide +kernel
theorem g183B4 : CutRow g183 4 0 2 := (@joinRow g183 4 0 1 1 g183P4_0 g183P4_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P5_0 : CutRow g183 5 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P5_3 : CutRow g183 5 3 24 := by
  apply polarBlock (data:=fun j => g183Mark (j+1)) rfl
  decide +kernel
theorem g183B5 : CutRow g183 5 0 27 := (@joinRow g183 5 0 3 24 g183P5_0 g183P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : CutRow g183 6 0 18 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_18 : CutRow g183 6 18 21 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_39 : CutRow g183 6 39 48 := by
  apply polarBlock (data:=fun j => g183Mark (j+25)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_87 : CutRow g183 6 87 48 := by
  apply polarBlock (data:=fun j => g183Mark (j+73)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_135 : CutRow g183 6 135 48 := by
  apply polarBlock (data:=fun j => g183Mark (j+121)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_183 : CutRow g183 6 183 36 := by
  apply polarBlock (data:=fun j => g183Mark (j+169)) rfl
  decide +kernel
theorem g183B6 : CutRow g183 6 0 219 := (@joinRow g183 6 0 87 132 (@joinRow g183 6 0 18 69 g183P6_0 (@joinRow g183 6 18 21 48 g183P6_18 g183P6_39)) (@joinRow g183 6 87 48 84 g183P6_87 (@joinRow g183 6 135 48 36 g183P6_135 g183P6_183)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : CutRow g183 7 0 9 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_9 : CutRow g183 7 9 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_57 : CutRow g183 7 57 15 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_72 : CutRow g183 7 72 19 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_91 : CutRow g183 7 91 29 := by
  apply polarBlock (data:=fun j => g183Mark (j+205)) rfl
  decide +kernel
theorem g183B7 : CutRow g183 7 0 120 := (@joinRow g183 7 0 57 63 (@joinRow g183 7 0 9 48 g183P7_0 g183P7_9) (@joinRow g183 7 57 15 48 g183P7_57 (@joinRow g183 7 72 19 29 g183P7_72 g183P7_91)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P8_0 : CutRow g183 8 0 14 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B8 : CutRow g183 8 0 14 := g183P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P9_0 : CutRow g183 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B9 : CutRow g183 9 0 1 := g183P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : mixedTables g183 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g183 0 0
  · exact mixedEmpty g183 1 0
  · exact mixedEmpty g183 2 0
  · exact mixedEmpty g183 3 0
  · exact g183B4
  · exact g183B5
  · exact g183B6
  · exact g183B7
  · exact g183B8
  · exact g183B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 10 := mixedLower (g:=g183) (i:=0) (hints:=1348) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 10 [(183,[]),(187,[50]),(235,[50,100]),(238,[32,48,100]),(252,[32,49,64,16,81,97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff803ffffffffffff,0xffc46d363a10000f00ff])),(BitVec.ofNat 152 (word80 [0x290582802a0250148,0x29c425140a1111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc01fff0007ffc,0xf714685e2000f00f00])),(BitVec.ofNat 152 (word80 [0x2b22914c14c1b60990,0xccf704285e2333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffff8000,0x22278cbfc00f00f000])),(BitVec.ofNat 152 (word80 [0x33c4e2702701380de1,0x7022278cbe8333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffffff,0xfe580f6b35b0f000000f])),(BitVec.ofNat 152 (word80 [0xbc070380b805c02e01,0x80180a6b35a666666666]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000000000,0x24f859c3ef0000fff0])),(BitVec.ofNat 152 (word80 [0xc0000000c006003002,0xd841014444444444]))),(0x0,0x0),(0x19b82850c0fffff0000,(BitVec.ofNat 152 (word80 [0x10008004000,0x888888888]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(4,0,185,0,7)]
def g189A : List (List Nat) := [[],[50]]
def g189D7 (j : Nat) := if j=0 then 0x7f else 0
def g189L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g189D7)
  | _ => emptyPacking
def g189I (_ _ : Nat) : Option (Nat × Nat) := none
def g189 : Forest := ⟨189,7,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : CutRow g189 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : CutRow g189 7 0 1 := g189P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : mixedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g189 0 0
  · exact mixedEmpty g189 1 0
  · exact mixedEmpty g189 2 0
  · exact mixedEmpty g189 3 0
  · exact mixedEmpty g189 4 0
  · exact mixedEmpty g189 5 0
  · exact mixedEmpty g189 6 0
  · exact g189B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 8 := mixedLower (g:=g189) (i:=0) (hints:=21764) (before_sound K183 V183) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K183 8 [(189,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V183 low189 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ff01ffff801fffff0,0x3f4a49db60000f000f0f])),(BitVec.ofNat 152 (word80 [0x522c50150d4250525,0x944241db611111111111]))),((BitVec.ofNat 152 (word80 [0x7fffe03ffffe007fff,0xc067738c1000f000f0f0])),(BitVec.ofNat 152 (word80 [0x64489826098360649,0x2663738c011111111111]))),((BitVec.ofNat 152 (word80 [0x8000003fffffff8000,0xb74ce5200f000f0000])),(BitVec.ofNat 152 (word80 [0x17870e0b80e038178e,0x38b74ce5233333333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffffffff,0xff8ccb2790f000f000ff])),(BitVec.ofNat 152 (word80 [0x1808100c0100401800,0x8c8820922222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00000000000,0x531020ef0000ffff00])),(BitVec.ofNat 152 (word80 [0x200000100200802000,0x44444444444]))),(0xa0a4d80fffff000000,(BitVec.ofNat 152 (word80 [0x400000200401004000,0x88888888888]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(1,0,214,0,8)]
def g215A : List (List Nat) := [[],[118],[16],[16,118]]
def g215D8 (j : Nat) := if j=0 then 0x7f else 0
def g215L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g215D8)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,8,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P8_0 : CutRow g215 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B8 : CutRow g215 8 0 1 := g215P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : mixedTables g215 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g215 0 0
  · exact mixedEmpty g215 1 0
  · exact mixedEmpty g215 2 0
  · exact mixedEmpty g215 3 0
  · exact mixedEmpty g215 4 0
  · exact mixedEmpty g215 5 0
  · exact mixedEmpty g215 6 0
  · exact mixedEmpty g215 7 0
  · exact g215B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 9 := mixedLower (g:=g215) (i:=0) (hints:=1604) (before_sound K189 V189) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K189 9 [(215,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V189 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe03ffff800fffffe03,0xfed3aa41320000f00f0f])),(BitVec.ofNat 152 (word80 [0x458a01506a0940a458,0xa6530a40321111111111]))),((BitVec.ofNat 152 (word80 [0xffc07fffff001ffffc,0x34e5bc281000f00f0f0])),(BitVec.ofNat 152 (word80 [0x891302604c0d80c891,0x334e1a42011111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffe00000,0xd372be2500f0000000])),(BitVec.ofNat 152 (word80 [0xe1c2b82704e0af0e1,0xc0d372be257777777777]))),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf922299d6b0f000f00ff])),(BitVec.ofNat 152 (word80 [0x10200c008010030000,0x20218d082222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(BitVec.ofNat 152 (word80 [0x300300600c0102,0x80c430c04444444444]))),(0x665142404fffff00000,(BitVec.ofNat 152 (word80 [0x40040080100000,0x8888888888]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,8)]
def g219A : List (List Nat) := [[],[100],[16],[16,100]]
def g219D8 (j : Nat) := if j=0 then 0x7f else 0
def g219L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g219D8)
  | _ => emptyPacking
def g219I (_ _ : Nat) : Option (Nat × Nat) := none
def g219 : Forest := ⟨219,8,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : CutRow g219 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : CutRow g219 8 0 1 := g219P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : mixedTables g219 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g219 0 0
  · exact mixedEmpty g219 1 0
  · exact mixedEmpty g219 2 0
  · exact mixedEmpty g219 3 0
  · exact mixedEmpty g219 4 0
  · exact mixedEmpty g219 5 0
  · exact mixedEmpty g219 6 0
  · exact mixedEmpty g219 7 0
  · exact g219B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 9 := mixedLower (g:=g219) (i:=0) (hints:=28740) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 9 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff803ffffffffffff,0xffc44536ba50000f00ff])),(BitVec.ofNat 152 (word80 [0x290582802a0250148,0x29c405148a1111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffc01fff0007ffc,0xf734685e0000f00f00])),(BitVec.ofNat 152 (word80 [0x2b22914c14c1b60990,0xccd724685e0333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffff8000,0x22278dbfc00f000000])),(BitVec.ofNat 152 (word80 [0xb3c4e270a705382de1,0x7022278dbfc777777777]))),((BitVec.ofNat 152 (word80 [0x1ffffffffff,0xfe580f6a35b0f000f00f])),(BitVec.ofNat 152 (word80 [0x3c0703803801c00e01,0x80180a6a348222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000000000,0x24f859c3ef0000fff0])),(BitVec.ofNat 152 (word80 [0xc0000000c006003002,0x20d001016444444444]))),(0x19b82850c0fffff0000,(BitVec.ofNat 152 (word80 [0x10008004000,0x888888888]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(4,0,217,0,8)]
def g221A : List (List Nat) := [[],[64]]
def g221D8 (j : Nat) := if j=0 then 0x7f else 0
def g221L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g221D8)
  | _ => emptyPacking
def g221I (_ _ : Nat) : Option (Nat × Nat) := none
def g221 : Forest := ⟨221,8,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_0 : CutRow g221 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B8 : CutRow g221 8 0 1 := g221P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : mixedTables g221 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g221 0 0
  · exact mixedEmpty g221 1 0
  · exact mixedEmpty g221 2 0
  · exact mixedEmpty g221 3 0
  · exact mixedEmpty g221 4 0
  · exact mixedEmpty g221 5 0
  · exact mixedEmpty g221 6 0
  · exact mixedEmpty g221 7 0
  · exact g221B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 9 := mixedLower (g:=g221) (i:=0) (hints:=30212) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 9 [(221,[]),(222,[16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe03ffff800fff01fff,0xff43a3431a0000f00f0f])),(BitVec.ofNat 152 (word80 [0x458a01506a04a34148,0xa7432242121111111111]))),((BitVec.ofNat 152 (word80 [0xffc07fffff00001ffc,0x34e53ccc1000f00f000])),(BitVec.ofNat 152 (word80 [0x89130a604c16c58191,0x334e53c4413333333333]))),((BitVec.ofNat 152 (word80 [0x7fffffffffe000,0xd37a922500f00f00f0])),(BitVec.ofNat 152 (word80 [0xe1c038070070601e1,0xc0537a02051111111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf92229bd6b0f000000ff])),(BitVec.ofNat 152 (word80 [0x10202c028058000a00,0x2001bd686666666666]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c67ad8f0000fff00])),(BitVec.ofNat 152 (word80 [0x30030060080c02,0x808438884444444444]))),(0x665142404fffff00000,(BitVec.ofNat 152 (word80 [0x40040080001000,0x8888888888]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(1,0,230,0,7)]
def g231A : List (List Nat) := [[],[32]]
def g231D7 (j : Nat) := if j=0 then 0x7f else 0
def g231L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g231D7)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,7,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : CutRow g231 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : CutRow g231 7 0 1 := g231P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : mixedTables g231 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g231 0 0
  · exact mixedEmpty g231 1 0
  · exact mixedEmpty g231 2 0
  · exact mixedEmpty g231 3 0
  · exact mixedEmpty g231 4 0
  · exact mixedEmpty g231 5 0
  · exact mixedEmpty g231 6 0
  · exact g231B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 8 := mixedLower (g:=g231) (i:=0) (hints:=1381) (before_sound K221 V221) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K221 8 [(231,[]),(237,[49,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V221 low231 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffffffff0ffa,0x8a08b0800007c00ffc1f])),(BitVec.ofNat 152 (word80 [0x28140500800220ca,0x2003084210842108421]))),((BitVec.ofNat 152 (word80 [0x1ffffe007fc3fff05d,0x22c7098000f801f003e0])),(BitVec.ofNat 152 (word80 [0x413018260108240259,0x207098c6318c6318c63]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff8003ffff20,0xf2615e001f003e0003ff])),(BitVec.ofNat 152 (word80 [0x824020080a10480020,0xe0604210842108421084]))),((BitVec.ofNat 152 (word80 [0x1ffffffffffc000010,0xad8c6f83e00000007c00])),(BitVec.ofNat 152 (word80 [0xb8140b02c01704410,0xad8c4f39ce739ce739ce]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c03021808804,0x11988421084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201004002000000,0x42108421084210]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,8),(2,0,241,0,8),(32,0,211,0,8),(16,0,227,0,7),(64,0,179,0,7),(128,0,115,0,7),(0,32,82,129,6),(48,0,195,0,5),(80,0,163,0,5),(128,32,82,1,5),(144,0,99,0,4),(192,0,51,0,4)]
def g243A : List (List Nat) := [[],[100]]
def g243D5 (j : Nat) := if j=0 then 0x2f1e057454932 else 0
def g243D6 := limbs80 #[#[0xb67b22a49974d5454932,0x29eee2b2a85cb5515250,0x4b7bb8acaa17cd745493,0x471eda9652017ddc5645,0x2d03f011a0ae22780b61,0x2c98f970104f1e0204e,0x41622]]
def g243H6 (j : Nat) := if j=0 then 0x0 else 0
def g243D7 := limbs80 #[#[0xfefdfcf7efedd5250932,0x55262a80d900b20d523f,0x632019648ec925522b2b,0x2a158e1754910e2ac845,0x183222aa387a1791119,0x80c2060b780c9062043d,0x102bca11840e01067d40,0x1752248e0]]
def g243H7 := limbs80 #[#[0x160000130000a0,0x4400000,0x2400060000000,0x25]]
def g243D8 := limbs80 #[#[0x8a4b807f54bfa85dd32,0x1ca3946081847356838c,0x2a851ca30]]
def g243H8 := limbs80 #[#[0x180000c39a0,0x86000000150065e60240,0x1644e00000]]
def g243D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g243H9 (j : Nat) := if j=0 then 0x46c000000e4800 else 0
def g243L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g243D5)
  | 6 => (7,3,4,0,0,8,0,g243D6)
  | 7 => (9,2,4,458755,50,8,4111,g243D7)
  | 8 => (3,1,4,0,0,7,0,g243D8)
  | 9 => (1,0,4,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 2 0 2 0 0 g243H6
  | 7 => lookupShort 2 41 0 6 3 1 g243H7
  | 8 => lookupShort 2 29 3 7 4 1 g243H8
  | 9 => lookupShort 1 11 0 5 2 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : CutRow g243 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : CutRow g243 5 0 1 := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : CutRow g243 6 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_4 : CutRow g243 6 4 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : CutRow g243 6 0 7 := (@joinRow g243 6 0 4 3 g243P6_0 g243P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : CutRow g243 7 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_3 : CutRow g243 7 3 5 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_8 : CutRow g243 7 8 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : CutRow g243 7 0 9 := (@joinRow g243 7 0 3 6 g243P7_0 (@joinRow g243 7 3 5 1 g243P7_3 g243P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : CutRow g243 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_1 : CutRow g243 8 1 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : CutRow g243 8 0 3 := (@joinRow g243 8 0 1 2 g243P8_0 g243P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P9_0 : CutRow g243 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B9 : CutRow g243 9 0 1 := g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : mixedTables g243 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g243 0 0
  · exact mixedEmpty g243 1 0
  · exact mixedEmpty g243 2 0
  · exact mixedEmpty g243 3 0
  · exact mixedEmpty g243 4 0
  · exact g243B5
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := mixedLower (g:=g243) (i:=0) (hints:=68) (before_sound K231 V231) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K231 10 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V231 low243 (by decide +kernel)
def g245MarkBits := limbs80 #[#[0xb2892071861440c2040,0x44d245030e3cf38e34d3,0x6da65861728a28a59255,0xa286181f79a75965c70a,0x249249249228a38]]
def g245Labels : Array Nat := #[0x100000209108a041,0x82040281022432,0x82040281022421,0x100200a0d022a032,0x280020140a21143,0x100000088502a052,0x280140301201130,0x100000209108a052,0x1000420105808432,0x280140301201140,0x400440205402441,0x400440205402430,0x40800a04468a041,0x82040281022442,0x280120300a01130,0x1000110085408132,0x280140281201140,0x22040281022143,0x100000209108a053,0x82040281022443,0x100400209108a042,0x400440205402431,0x8001180d0e04142,0x400140211402141,0x208000a04229041,0x204000904225031,0x601440211403452,0x208000a04229031,0x80800221088c043,0x800440211804453,0x204040301205021,0x1000420111808454,0x8004180d0e04453,0x82040281082410,0x82040281082420,0x82040281082421,0x82040281082431]
def g245Mark (j : Nat) := g245Labels[packedAt g245MarkBits (6*j) 6]?.getD 0
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffffe1fffffa,0x8241b1000007c00f83ff])),(BitVec.ofNat 152 (word80 [0x28140500440020da,0x2011004210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffe007ffe1ff05d,0x2ccb088000f801f07c00])),(BitVec.ofNat 152 (word80 [0x40b018160280404259,0xc4b080c6318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80001fff20,0xf4695e001f003e00001f])),(BitVec.ofNat 152 (word80 [0x82c020180b08828020,0xe4684a18c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xab846f83e00000007fe0])),(BitVec.ofNat 152 (word80 [0xb0140a02c000b0400,0xa18467b18c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c030110c0804,0x11908521084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201004000100000,0x42108421084210]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(4,0,241,0,8),(32,0,213,0,8),(1,0,244,0,7),(36,0,209,0,7),(64,0,181,0,7),(16,0,229,0,6),(128,0,117,0,6),(5,0,240,0,5),(17,0,228,0,5),(20,0,225,0,5),(33,0,212,0,5),(68,0,177,0,5),(80,0,165,0,5),(96,0,149,0,5),(132,0,113,0,5),(81,0,164,0,4),(129,0,116,0,4),(192,0,53,0,4)]
def g245A : List (List Nat) := [[],[96,82]]
def g245D4 := limbs80 #[#[0xa0221393985954350110,0x7550d40442b232f32a86,0x89caac8a1aa088760e49,0x930c0b]]
def g245D5 := limbs80 #[#[0x50110551404414350110,0x44265501105d54044165,0x995434417050d1059543,0x54110549504414354110,0x44164541105895044154,0xdcd65442655511059154,0xbb2e5b727c9d565c8110,0xf33c4e3778dd364be2f4,0xca0b5510eba83e4f63d4,0x2cadf5911cb127e6507a,0x64ca1c5942bc1c1b8285,0x18b0e4461089c2097831,0x547ae88f55105c2ae782,0x645450e8861d1b42a358,0x3872af0a685d4c5c2b31,0x18479300e3610eac01c,0x9549a451b8a43a120500,0x4ea551a853e9d4da652e,0xe56eb559ac55ead55aa5,0x482d07a1e1b057ebd5da,0xc0980980802020b13408,0x2c223]]
def g245H5 (j : Nat) := if j=0 then 0x40e000035000 else 0
def g245D6 := limbs80 #[#[0x549105411050d1050110,0x59510591105891055110,0xd5110d4910c811099510,0x54140595205492054120,0x2eb3bd81525495059540,0x777b9dae76fb7bbbbedf,0xfcfe3ebf4f77b7d9e4ef,0x4baa64a9258a183f9fa,0x93a9092a9084ba81aaa0,0xc5ba093aa092aa0a0a18,0xc4b82e0b8044b8285b80,0xeaa3d0a9304b8203b99,0xab3282ab282ab2a41b94,0x4ab2966b10eab20aab10,0x14b291cb212332862b28,0xab32a46ba20ab2995329,0xeaba0aaaa0aab90aaa90,0x46bb287bb0c6bb0ebb80,0x6bb12ab8122bb047ba9,0xc7ba986bb2d4b2ac7bb1,0x6b9207ba1e3b99c7b91,0x1eaa3cdb83a9b8368a93,0x41a000ca8497b8449b94,0x4b12808a1e869158470c,0xd5d5152b460f8394d230,0x2137ede3751bd691915d,0xa9ca42889de65952408b,0xae2b6ad2b2ac2aeab2aa,0xb22c6b12c2b02beaf2ba,0xb62d6b52d2b42ceb32ca,0x40981f843f82deb72da,0x8951cb21c3b08b584009],#[0xb123b002a0d0c2c27801,0x11de2324d9a1110093a0,0xc0442022c4040807791,0x346020602210129c823,0xd101039dc2095a2023c4,0x85f82125f111201d6886,0x8825264893253117e084,0x87388286b88486dc09ad,0x16a908b098ab508f57c8,0xb606c8400ec453e2]]
def g245H6 := limbs80 #[#[0x160021115c5,0x3300000000000000000,0x1380003157c,0x4000000024857000000,0x2c0000004400,0x7650cc01d4000000,0x340096241c0000000000,0x2,0x1d00000005b3c0188,0x8036800000000000178,0x1432b,0x1964000000026c00,0x270000000,0x15c0000000c002000,0x8c0000024c,0x1e4]]
def g245D7 := limbs80 #[#[0xc8252549505012044052,0xcfbf5dfdbbfbebdd4b50,0xd50175005f201fffefdf,0x84f526058405600550c5,0xd5061541858863521854,0x29540a26518594616418,0x5032595d952725949952,0xb6244d49115242594e5,0x8a115282d91135444551,0x2582496562d814964825,0x5a59129544a58929524,0x45b0f42805c00ad81696,0xd143f8e8324b3274871c,0x5d36f1a163d7f5b5534c,0x67598e538de258560179,0x2ecb92dcb32b4a9695a1,0xd008070d807e1c12fcbd,0x250ad8eb08c24a9040c4,0x518402b040efa1118e16,0x810f6e043cf8100f3902,0x2401252c8414b01053cf,0xf92009296420a580829f,0x1810436e2814f2d4049a,0xdc7123b6a30560410041,0xd04401057f6010560412,0x34103411fd004198d040,0x18281030104010401046,0x821e5]]
def g245H7 := limbs80 #[#[0xc1041004480086001040,0x29480001b059802f0400,0x522c600237230070c009,0xc701da3ce8b800806623,0x2030a812f416ac0f2d,0x420000000000540064,0xd30032800c80000000,0x9a84dce4548000000000,0x14f130025c1b324c858,0x896d5fa0976d94200128,0xb006d5071f1d8010c001,0x2000025401b400038382,0xa0000339502de20f11,0x18f0380]]
def g245D8 := limbs80 #[#[0xea1542a0720a40443ffd,0xb3b271700ea594aa9452,0x3023c6821b49f8f76634,0x80a060866041444001c8,0xc070340af0060c060841,0x3810c460a0608e20]]
def g245H8 := limbs80 #[#[0x1800918406808139812,0xc00000011f0980018050,0xe10f1001376700000b81,0xb43d6d1522a2cb0071e2,0x6610ec54d456415787b6,0x25411280012658000800,0xc0e2c33a50041a4d5f,0x103538000150853113a,0x7b46000143883d200150,0x1cc09b0c461b92002]]
def g245D9 (j : Nat) := if j=0 then 0x2082013f else 0
def g245H9 := limbs80 #[#[0xa200c8820ebd232808c,0xe90b0c00000022000000,0x473]]
def g245L : Nat → Packing
  | 4 => (4,5,5,0,0,5,0,g245D4)
  | 5 => (32,4,5,1048593,69,9,1031,g245D5)
  | 6 => (62,3,5,1441811,85,10,4124,g245D6)
  | 7 => (40,2,5,720906,68,10,4117,g245D7)
  | 8 => (10,1,5,131073,16,8,4107,g245D8)
  | 9 => (1,0,5,0,0,0,0,g245D9)
  | _ => emptyPacking
def g245I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 17 0 4 2 0 g245H5
  | 6 => lookupShort 9 149 2 8 5 1 g245H6
  | 7 => lookupShort 17 107 6 9 6 1 g245H7
  | 8 => lookupShort 15 79 5 9 6 1 g245H8
  | 9 => lookupShort 3 23 4 7 4 1 g245H9
  | _ => fun _ => none
def g245 : Forest := ⟨245,9,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P4_0 : CutRow g245 4 0 4 := by
  apply polarBlock (data:=fun j => g245Mark (j+0)) rfl
  decide +kernel
theorem g245B4 : CutRow g245 4 0 4 := g245P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P5_0 : CutRow g245 5 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P5_2 : CutRow g245 5 2 5 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P5_7 : CutRow g245 5 7 25 := by
  apply polarBlock (data:=fun j => g245Mark (j+4)) rfl
  decide +kernel
theorem g245B5 : CutRow g245 5 0 32 := (@joinRow g245 5 0 2 30 g245P5_0 (@joinRow g245 5 2 5 25 g245P5_2 g245P5_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_0 : CutRow g245 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_1 : CutRow g245 6 1 19 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_20 : CutRow g245 6 20 14 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P6_34 : CutRow g245 6 34 28 := by
  apply polarBlock (data:=fun j => g245Mark (j+29)) rfl
  decide +kernel
theorem g245B6 : CutRow g245 6 0 62 := (@joinRow g245 6 0 20 42 (@joinRow g245 6 0 1 19 g245P6_0 g245P6_1) (@joinRow g245 6 20 14 28 g245P6_20 g245P6_34))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_0 : CutRow g245 7 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_7 : CutRow g245 7 7 27 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_34 : CutRow g245 7 34 6 := by
  apply polarBlock (data:=fun j => g245Mark (j+57)) rfl
  decide +kernel
theorem g245B7 : CutRow g245 7 0 40 := (@joinRow g245 7 0 7 33 g245P7_0 (@joinRow g245 7 7 27 6 g245P7_7 g245P7_34))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_0 : CutRow g245 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_1 : CutRow g245 8 1 9 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B8 : CutRow g245 8 0 10 := (@joinRow g245 8 0 1 9 g245P8_0 g245P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P9_0 : CutRow g245 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B9 : CutRow g245 9 0 1 := g245P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245T : mixedTables g245 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g245 0 0
  · exact mixedEmpty g245 1 0
  · exact mixedEmpty g245 2 0
  · exact mixedEmpty g245 3 0
  · exact g245B4
  · exact g245B5
  · exact g245B6
  · exact g245B7
  · exact g245B8
  · exact g245B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 10 := mixedLower (g:=g245) (i:=0) (hints:=1284) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 10 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff801ffffe1fff9ae2,0x181cf000000fc003f03f])),(BitVec.ofNat 152 (word80 [0x450940500441101ac2,0x800f145145145145145]))),((BitVec.ofNat 152 (word80 [0xffffe007fffff8390b,0xb483500003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x160181602800213803,0xb40140c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x39712000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x98020180b082400039,0x3171028a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8bc7903f000000000fc0])),(BitVec.ofNat 152 (word80 [0xe02c0a02c00b824628,0xbc6971c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ac8fc000003ffff000])),(BitVec.ofNat 152 (word80 [0x300c03010c044104,0x428c0410410410410410]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x4010040010000000,0x820820820820820]))),(0x0,0x0)]
def g246C : List ColumnInfo := [(4,0,242,0,8),(32,0,214,0,8),(64,0,182,0,8),(2,0,244,0,7),(16,0,230,0,7),(128,0,118,0,7),(18,0,228,0,5),(130,0,116,0,4),(144,0,102,0,4)]
def g246A : List (List Nat) := [[],[65]]
def g246D6 := limbs80 #[#[0xe3c1243e437695254120,0x5]]
def g246D7 := limbs80 #[#[0xf54950bf59520fe54120,0x42a00ff58950bfd8950d,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c70c871]]
def g246H7 (j : Nat) := if j=0 then 0x8 else 0
def g246D8 := limbs80 #[#[0xa38c2461a403faa1fd20,0x1e851c6121c]]
def g246H8 (j : Nat) := if j=0 then 0x4032623000000011 else 0
def g246D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g246H9 (j : Nat) := if j=0 then 0x9b8 else 0
def g246L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g246D6)
  | 7 => (5,2,4,0,0,8,0,g246D7)
  | 8 => (2,1,4,0,0,6,0,g246D8)
  | 9 => (1,0,4,0,0,0,0,g246D9)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 2 0 2 0 0 g246H7
  | 8 => lookupShort 1 17 0 6 3 1 g246H8
  | 9 => lookupShort 1 3 0 4 1 1 g246H9
  | _ => fun _ => none
def g246 : Forest := ⟨246,9,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : CutRow g246 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B6 : CutRow g246 6 0 1 := g246P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : CutRow g246 7 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_4 : CutRow g246 7 4 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B7 : CutRow g246 7 0 5 := (@joinRow g246 7 0 4 1 g246P7_0 g246P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_0 : CutRow g246 8 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B8 : CutRow g246 8 0 2 := g246P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P9_0 : CutRow g246 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B9 : CutRow g246 9 0 1 := g246P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246T : mixedTables g246 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g246 0 0
  · exact mixedEmpty g246 1 0
  · exact mixedEmpty g246 2 0
  · exact mixedEmpty g246 3 0
  · exact mixedEmpty g246 4 0
  · exact mixedEmpty g246 5 0
  · exact g246B6
  · exact g246B7
  · exact g246B8
  · exact g246B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246G : graphValid g246 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low246 : Lower true (varsX 246) (graphGoal 246) 10 := mixedLower (g:=g246) (i:=0) (hints:=287376704) (before_sound K245 V245) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K245 10 [(246,[]),(249,[16,64,82,50,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V245 low246 (by decide +kernel)
def g250MarkBits := limbs80 #[#[0xa141850a142840608080,0x3460b0e284880e182850,0xcb15284c911040880f1c,0xf1d386cc183468c98305,0xa142750200a142850a7c,0x50a1428544142850a142,0xa810230a810200a1428,0x4a54274c6cd9b3695220,0xc582f58b952e5cb562b5,0x5a200a1502040cd9a064,0xb2066cd9a06681ab546d,0x3970819b75c810200ad9,0x540802b40ae5cb66ccd7,0x54a9dba366cd8368d100,0x6cde2040802854081005,0xfdf3e66f5cbd408d9a06,0x1020866211c28f9f4180,0x52a7d1172e2ca9520408,0x3366cd9c540f972e5cb9,0x40cd9b75ccd9a066cd0,0x66cd9a08cdcc3e6ef902,0x6cd9bc40cd9b366cd9b3,0xcd9b3671df3366819b36,0x3366]]
def g250Labels : Array Nat := #[0x200040109205051,0x300824128b01a53,0x200020108a01251,0x100040281102850,0x1000208049208232,0x102040281102810,0x40008140244240,0x204040301205031,0x801001208845052,0x208020300a09051,0x800208240a04243,0x200040301205061,0x300824128b01a60,0x44808140244230,0x308024300b09041,0x41824160841210,0x90080c068b04a52,0x300824128b01a61,0x40800c26070a042,0x40800c26070a053,0x204040301205042,0x200040301205062,0x906040281106831,0x208001208249052,0x303040281103831,0x408024320d0a053,0x40800c22070a042,0x100040281102851,0x208020300a09052,0x100040281102860,0x1001024129909043,0x208001208249041,0x102040281102820,0x40800c06870a052,0x142240281102a10,0x200001108245051,0x100080c069308863,0x41040241041210,0x801040209805042,0x204001108245031,0x200220108a01251,0x1000220109808254,0x41020140841220,0x80800120884c054,0x100000110904c064,0x200240209201261,0x41040241041220,0x410110c9401220,0x48008240248260,0x808011208c4c043,0x408024220d0a043,0x102040281102831,0x100040281102861,0x40008140244260,0x40008140244250,0x141840241041a20,0x140808140244a50,0x14080c160344a50,0x41040241041260,0x48024320948240,0x102040281102821,0x200001108245052,0x142240281102a31,0x14800c240348240,0x200001108245062,0x44040301044240,0x4400c160344240,0x142240281102a20,0x108011288548851,0x80800522894c054,0x4800c260348250,0x48008240248250]
def g250Mark (j : Nat) := g250Labels[packedAt g250MarkBits (7*j) 7]?.getD 0
def g250Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff87fff2310000,0x7e03f80fe988a467cfe])),(BitVec.ofNat 152 (word80 [0x402801102212012845,0x18a142850a08a2024874]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe003ffffff00c80000,0xf800007f002013999b3c])),(BitVec.ofNat 152 (word80 [0x84b08a010420c01ad3,0x4a64c99326221289991c]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe923003f,0x1fc000fec11c21e3cf])),(BitVec.ofNat 152 (word80 [0xc02c20480920518a,0x2142850a140110808389]))),((BitVec.ofNat 152 (word80 [0xfffffff800048807c0,0x7f0101e03e03f1])),(BitVec.ofNat 152 (word80 [0x9013002704408e52c,0xb58b162c5901a03602e1]))),((BitVec.ofNat 152 (word80 [0xa16f800,0x1fff8001fe003ffc01])),(BitVec.ofNat 152 (word80 [0xe01c0438080168630,0xc60c18306122003d1000]))),((BitVec.ofNat 152 (word80 [0x1544ffff,0xffe0000001ffffc00000])),(BitVec.ofNat 152 (word80 [0x100200040000000000,0x10204080d44d400000]))),(0x0,0x0)]
def g250C : List ColumnInfo := [(2,0,248,0,8),(8,0,242,0,8),(16,0,234,0,8),(32,0,218,0,8),(64,0,186,0,8),(40,0,210,0,7),(0,8,82,160,6),(0,32,82,136,6),(128,0,122,0,6),(10,0,240,0,5),(18,0,232,0,5),(24,0,226,0,5),(32,8,82,128,5),(66,0,184,0,5),(80,0,170,0,5),(128,8,82,32,5),(128,32,82,8,5),(82,0,168,0,4),(136,0,82,0,4),(136,32,82,0,4)]
def g250A : List (List Nat) := [[],[100],[83],[83,100],[65],[65,97],[65,83],[65,83,97],[97,65],[97],[97,83,65],[97,83]]
def g250D5 := limbs80 #[#[0x551525091060c6550910,0x5954250120d915254110,0x55152501205095150120,0x50b51501205d55250120,0xd9152541205495154120,0xd935454120dd15254120,0x1d8db16d9ae1176d4520,0xe2ba572ae35b8b696aad,0x685b804ee027c2103245,0xf28d5cb2c72e68c33b70,0x5052f35ba4af070fcb34,0x60808002a8e530573c2,0xe3868c16284880e18284,0x1]]
set_option maxRecDepth 32000 in
def g250D6 := limbs80 #[#[0x50910195424417219510,0x44370509109954244152,0x5c950441525411050950,0x54510509514436254110,0x4436454910dc95144362,0x5ca654437359510dc965,0x501205d76244174d8910,0x48152501205454048142,0x54550483515012059540,0x54120551504815254120,0x4835454120d455048161,0xdc9504837154120d9150,0x54520d45514837454120,0x48176551205955448373,0x595614807558520dd954,0x59520dc1654807459520,0x48171995205c26548374,0x5db5148174d45205c351,0xd51205975448376d4520,0x48176d51205c75448170,0x5495154175d9120d9354,0x54950d91525436254550,0x5437458950dcd6154370,0x5cb5154172d415054b50,0xd49505d35254362d4550,0x54570d45515cb6154364,0x58960d477458b505cb60,0x8fa2fdc960d457258351,0xaeeb7abe7e9f6779be3f,0xbf2fabdaeeb7adaafabd,0xd3f3ecf73bcdf2fcbb1f,0xe3f8edeb76dbb5ed6b57],#[0xf2fcaeebaeeab9ee6f9a,0x4a154292aca4beaf6bce,0x743116c8622590c36ba9,0x80708be0d90e18c11c6f,0xc81ab5482a63a2907804,0xc860c0d2aa022d841126,0x8b58a1132582184b040,0x20c11bad52375aa45ec5,0x2f7d725b5aa47ab548d,0x1b807eb2e500660180dc,0x40d5ee418d614297c047,0x77081cba1c4484306378,0x82ca61052fba0a478012,0x899423032847d52082b0,0xc184c381258202330a11,0x5438c098718a6e830261,0xb84001708442e1480,0xb841a1308356e1002cc2,0x2c7f064c2e107aaa10e0,0x30852c550a16c3164182,0x567e08abfc3947d75296,0x214d1fc19763872b3708,0xc57aa18ad54306f0a68d,0x32987f74313ec8627590,0xfaf74315ae862b5c4c57,0x743efae87ebd50fd6aa1,0x356e866b608ca0c21f7f,0xa876b608e49c319ab843,0x1fe09017439d9b743b36,0x91114c321458042eaa88,0xabb2a2556544aec88955,0x22d63645ac2c8b5fe096],#[0xf845e170cb8261970dc,0x45ea708bd42117b1c02f,0x90ea9c7e11384c3300b8,0x8c3611308c1a64b754e,0x8e01243c223877447270,0x993ea93261804ac2a095,0x9b233138366eaa8c9fe0,0x311d876a3b0ad665c1aa,0x15468c700d21e118c9c0,0x54ef00a94e11b29c2345,0xe8a67dc94a9c32a5265,0xa145c5416c2299b74533,0x5c554dc02a1e8750a6e2,0x528aa2a514154a6e2a94,0xc0aa518154a6a2a94545,0xdaf627a2706b1f5495a9,0x847cfec4f8de11eb8ba3,0x6f240ed5dcdc35b9b71b,0xc50d5d89daab13b69527,0x82e12184c243594286b6,0x11d39aa3a715474fec4e,0x38ba3aaf82755ec4e866,0xa398f82726b08e9cdd1d,0x676482e7010615d2143b,0x178a2c2f1de01e3ba83c,0x130915455233242bc536,0x9247e1240bc1440b848a,0x86a0a60e410012000130,0x41ce374688c916c28c41,0xda5589f9322484407e0f,0x7e8f79d43906a8cb18a2,0x92123a4648a90fa1040a],#[0x127a4e49a93125a4a492,0xba564aa95129a524a294,0x5e4ba9712da5a4b29612,0x4ca99131a624c29812fa,0xa9b135a6a4d29a133a66,0xd139a724e29c137a6e4d,0x3da7a4f29e13ba764ea9,0xa82502a013fa7e4fa9f1,0xa512a2143a8650aa1141,0x22a4147a8e51aa3145a8,0xa614ba9652aa5149a925,0x14fa9e53aa714da9a532,0x3aa654aa9151aa2542a8,0xae55aab155aaa552aa15,0x56aad159ab2562ac157a,0xaaf15daba572ae15bab6,0x1161ac2582b015fabe57,0x65aca592b2163ac658ab,0xad25a2b4167ace59ab31,0xa5b2b616bad65aab5169,0xc2b816fade5bab716dad,0xba173ae65cab9171ae25,0x8c0dee5dabb175aea5d2,0x181161413901c0a00202,0x569284119258f420f63b,0x2c008b0de3e122821648,0x34200908800b0484809a,0x120e7060c0781430d866,0xb105ef88928e1510cb1a,0x8b0a03282009a98b30,0x221ad0758106e6202e62,0x8c80b7d848884a041a46],#[0x37516320213f2b910b64,0x2909b81a43486908]]
def g250H6 := limbs80 #[#[0x1c0000000c240000215,0x300003100000000000,0xc10000000000000,0x20552c00,0x106000460000000000,0x303,0xa0800404000000085c00,0x3800000000000000000,0x2b0d000000024c00000,0xc300015400,0x1a20000080800,0x82c0000000c200f]]
set_option maxRecDepth 32000 in
def g250D7 := limbs80 #[#[0x54110509104851019510,0x59510589105491054510,0x5012019520d891099510,0x58520551205452054120,0xd5120d45209952059520,0x5495054550d9120d8520,0xd4550d41505895058550,0xd4551d8950d8550d4950,0xd4b5058b5058750d8151,0xbebf3f9ecee6f2f58351,0xfefb7bafcfdfefd7dbbd,0xdfdfebefeff577fbddad,0x61dcc70ae60097203fdf,0x35c4a0ae6a4152326a11,0x54830ee708374400ba14,0xc846ec42376405db1071,0x4922e849374193b8048d,0xb22e4413721c8b90045d,0xb6e46595231cb2976548,0x6c863964323aa191550c,0xec9257048fb99a9dd0c7,0xc71176397329cb594e22,0x9ad654d9b22695c1326e,0x1b74413b82045d5522ec,0x374419ba20c1d1076e08,0x52688ba2245d914ae089,0x274fb9b07dcd64ae4d45,0x717b22f1dc174ee0b917,0xc8ba3c6dd192ae8e2f64,0xb83e45ca026e912d648,0xb90795c83ca841937291,0x284f1942baa416142133],#[0x979544b7ec82c95415f3,0x99584ccea266551333a8,0x5dccdc2c26e351373b89,0xdd9252ec929744b2b825,0xc5052e29a8753deb29ea,0x9b7ec4b4952594b8a2ad,0xd92a4ea9726dfb137254,0x7ae522b7291eb148a5c9,0x2ea13f6509eb284fdca4,0xe263e7615e3b0aadd055,0x866574333aa199550cca,0x6bf6435eb21b9994ccee,0xa97635fb29af594d56e8,0xd6549fb224f591256ec6,0x753df3b24f5d927eca93,0x53a9aa1cadc4ecae072b,0x4f2b826fdd8e7aec73d6,0x29ba219dc107aec9bd65,0xeba20fdc507ae283e654,0xb1359589acae08bf7441,0x930fd8987ac4c4952633,0x2f9dc177ec4ebd62755b,0xf259177ec8bcb545e4aa,0x2591c52e8e3f64725b22,0xd899cee0cc974725b239,0xd19a0e8cbf6465eb2337,0x1e7ec8f6770795ba334d,0xe7ae8f3f7179eb8bca5d,0x7ae912b7489eb244fdd1,0x1080ca086032000fdd22,0xb427a2361ee1c2182152,0x3fc3c638c3583202e22],#[0x56653451a4e04ac47243,0xa6d668a64c5fe5d25ae,0xa8908528267ee7a27647,0xa229fe9ba97095692c8d,0xdcb98b68b1ead8a92a64,0x4d66d16cc0c6ac38c0cb,0xf26ecae84e52e24de4db,0xf90b3065018fd6f9cf54,0x526723f2011a517b1350,0x40b3e53af3693292df2a,0x9157f54b50f4d7495451,0xb7156d969b6656175c55,0x88d8518217f17ab76d74,0x3d92d91d90d8fd8df8c1,0xd99d98d97d96d95d94d9,0xa0d9fd9ed9dd9cd9bd9a,0x7da6da5da4da3da2da1d,0xdaddacdabdaada9da8da,0xb4db3db2db1db0dafdae,0xbdbadb9db8db7db6db5d,0xdc1dc0dbfdbedbddbcdb,0xc8dc7dc6dc5dc4dc3dc2,0xfdcedcddccdcbdcadc9d,0xdd5dd4dd3dd2dd1dd0dc,0xdcddbddadd9dd8dd7dd6,0x10c8140d841f81dedddd,0x1c880238a0f442012c4,0x801c7c34806028d1543,0x16c30445822685c54648,0xc64f4b881b0a1805ca46,0x4d108b40948e5c25081c,0x8c4840884286830d02c0],#[0xcb001450f568a03598dd,0x13579b5548c116d61917,0x457e04117fe42d11fe04,0xaa1117cb00145de3c420,0x50c659f0b192974120e2,0x1056f28931d56c4c61f8,0x96fe8f024b516d12af71,0x571132884f8092132c2c,0x420e59981275ea321d58,0xb26f8f408146b7888f62,0xe4444ef10082197bd660,0xbf326326e4fa8d0211d4,0x223bfe83245ebe907116,0x87fbd90e101ebd0896de,0x1156186dc157e8c02859,0x2e4203ce534987fbf12e,0x98689a6a0a1877f80894,0xfb0204280cfcc344c19f,0xc8287ae4284e5bc4485,0xe00051cf5c848b6c023b,0x80d461bed2e0028ea4fc,0x2f11224a3b248655f3e0,0xcc6019e758247c401325,0xf0302a04d203b9988131,0x3cb19fe72c2041fcd041,0x7a40628cbd4f46264ae1,0x83ed0171178be144832d,0xb6e0a6f46c8230f34708,0xcf58c6c8079fd6d2223f,0x26a7a31ee7ca144ee462,0x28a8dcb66c95815e0865,0x1907c2137688631a731b],#[0xa06b26efd8228a5e1d01,0x10e9cc0183d5c4444697,0xe960ca3df88e4801df81,0x3ba033189aff82145039,0x3b431c5c74688b7f8191,0x1a985160e319a26c90b8,0x73077dc44707488707,0x5b22ae4585f231f2]]
set_option maxRecDepth 32000 in
def g250H7 := limbs80 #[#[0xc2055143047040045081,0x46810061d80000010471,0x2c2a150032031c010708,0x5f0815ca081005253000,0x30040c11c70800477801,0x6055c906004108d0b70c,0x30a7000000000003287,0xd4028114000c0b002300,0x317c00000000a6,0x80d110600010538848,0x108980c809544980,0x40c40c1028510bc0cc00,0x1093450e48c,0xa4000000106900000000,0x4000c432446c1ab06fe0,0x10540000000400,0x85840000000,0x88441490424648641800,0xca50000c22300301ae21,0x4276044,0xf70700000621a5f40000,0x4000c22b87bd5e502f00,0x129380e800002e,0x50581ab01c4000c4c4,0x6c403165e62005c41740,0x2090a9028080b000188,0x360aec1e10ad052c0b1,0xe3072000302280a82140,0xa0995287006d06800080,0x4000000000000000402,0x50060000911f0b7816c,0x425f06c00084],#[0x10be0000000d08000,0x7c03cc31d29d60b0000,0x440afc4b715a81614066,0x4000000103e000300b52,0x298000043c405800068a,0x18000143e42af4880003,0x415c0c681486,0x1147c416649604a400,0xa5c809023a29c428a282,0x8021300000ac027a29e4,0x700c00020c4110708555,0x4d000253dd0f4000c09,0x3d110f87882100000003,0x8000105ec09a0a3d1e21,0xc0ec0008068401415a0c,0x2001a6d28e1a2910940a,0xe8000411a01900b70bc8,0x680e429403f426e04b82,0x1b80ac000c048000162,0x74020000508607b0251,0xb819708d023000044094,0xd20c29980800000002a0,0x409010000107d81e447d,0x30489253e5,0x800092cc50000a3a2c00,0xb006a80000003a1f410,0x308f0000,0xd074051c1d8043407c0,0x451a111427082bc12800,0x30902751ba029c04e215,0x3087411c00056040000,0x0],#[0x40db0670000000000,0x9800010b3000105a0000,0x344d024b04100000,0x18c000858a461d6010c,0xb95581142074c027273,0xef44f01f8000026b0730,0x364f01f3081c092077c2,0x4e800241800012c0000,0x14803d00e41200550003,0x8c074000000000083150,0x30680000000a1a182,0x781d505f0000000,0x1a2b51ee0a8471856c0,0x6e000006d283800000,0xa4000000000011a9000,0xa7040f0a6000116a4056,0xc070000c1ff0c340461,0xc18845c0000000025800,0x2066,0x5f0aa000055900840000,0x42fc000c130000c8,0x37000108682c8000000,0xb5c014000000041e413f,0x14b040390504083427e0,0xc05d620906e035902506,0x7800001260bd493c0b4,0x7a0000000022c0000,0x10b80000090000000000,0x64d144000000000086a,0xc2d8050c4f9]]
def g250D8 := limbs80 #[#[0xfbfb7d47505455048110,0x908aa801b1bfffefdf7d,0xb2823283b102b108a888,0xb09aa81aa013b2833282,0x3292b2923293b212b213,0xa924a923b0aba823b293,0xb032b145a942b0c3b125,0xa90ca102b057b1b9a8b3,0xaa1caa1cb09da89ca89c,0xb0ada8aca8ad329cb29d,0xb12cb12da92ca92db0ac,0xca12014000cb05cb14d,0xe4ac878f81c42f450887,0x75011e337466cbf96828,0x742c454ea213925646c8,0xbb4730ddda932f624be9,0x796d25a3543e830fddea,0x85672bed5aa7d4767e4d,0x291208b1641f02fcde5b,0x1348284874b08206ca22,0x146801820b82080c7862,0x6e1e7c2309c59202321a,0x10928fc03510ff42609,0x193dcc4e12bb6320b7fe,0x84a728c15c21053f9291,0xef24b444d3a928897a10,0x2a07d84d423a04a73848,0x550fd041165b9338128,0x53fe09825a13a121f711,0xcfdc8601dea8047fc210,0x30410fb9c81099cf5300,0xe30d64cb9c4e44720b06],#[0x778c2448b3179115462f,0xfc18455c90649ee46689,0xea440691a096e064e197,0xe65013290bbe6501329d,0xc5f9423262f6b21260bb,0x83d45b488a2f2cf8164,0x7f2018277fc21056bfe1,0x2733ff200c25ff90c830,0xde308d229008287f2018]]
set_option maxRecDepth 32000 in
def g250H8 := limbs80 #[#[0x22004a12c9000003001,0x60220006011001106711,0x1100020201220200130,0x128a530510030040210,0x5f401004052242343019,0x3071110d1a600000,0x1e0000665000000,0x307700030300000000,0x144e107016a02db58a0,0x4864494006340a000000,0x19600000000484000c08,0x2,0x5617525e93005600000,0x2011802c00,0x380e0000151c064000,0xc0000c12400000000000,0x1417000101f000000041,0x1087000,0xcad184c00010869068,0x0,0x11f25f000000,0x4688000,0x209c00000000,0x304c0000000000000000,0x50000340c0000000000,0xd098018000102c0a67,0xc0000034000000002b80,0x408a0a,0x494c000,0xd4000000002f01211800,0x81b858d84,0x50c40000001099000],#[0x102ac2a50ba0000,0xaf025000000000000,0x90ae26320db27a000000,0x20c000156000042a924e,0xc0b400000000004,0x0,0x459,0x114650b4,0x4104000000306209180,0x0,0x10b7c15e450,0xd00000000000000227b0,0xc23507d803400081,0x81fc000000,0x55000000000000000,0x181c00031a400000,0x21170003516000000,0x41e80000000000,0x3084c13800080100000,0x58000000144000,0x30680000000ca7,0x7400020320000000a10c,0xa0000000052755d00031,0x594000162300,0x10b400035568100000,0x0,0x7b00,0x22b3000,0x147c100024f017a294,0x46740,0x961800,0x660000c6840000000000],#[0x104a00012620000000c,0x20100000000000000000,0x1a70000120851284b000,0xb500020b205000006925,0x400000ab000000000030,0x9fc19ac68146,0x4f0000000106b0000000,0xfc000000000000000004,0x10c000000000080,0xe124000000,0xa4149960a00000000000,0x20000000000000000000,0x1182000005e022408,0x280000e9ac0000000000,0x2522000000041f80008,0x80000000000000344f00,0x40000000000c24,0x0,0x3c5811a3000303600000,0x8274000000083d826e52,0x0,0x8800095c800000000000,0x90820140a6800012,0x1a6000044ec000000,0x20b10584000866c,0xd41d8000000300e00000,0x80d6153445b03e80c40a,0x25400081e61140000000,0x2e10c000109a0003a6d9,0x400000014360000000c1,0x9f00ba20611960a7801,0x37c9840004147498c022],#[0x1171000000000030,0x403c0000000000000000,0x203c000000061b4000,0x30a180e400000000000,0x4000000240a121706a00,0x96c4380000003002528,0x5dc9f8247c16a57945cc,0xc00000000002156c6732,0xe1200000000000a83f27,0x2291000009ec00c000,0xc19800090380000,0x476c47e49e000000000,0x0,0x14680004148067822c,0x10000000203e0b8c0e00,0x90e40590000000000106,0xa445100001660002199,0x77094000000000002528,0x309000010650000000ca,0xc5d40000000000000,0x329804e0000c048,0x2434863000045400,0xc2cc0000000000000000,0x325100010a3,0xc50b11e0,0xc0000003080413c00000,0x2600008030000842,0x40eda45d624,0x82e400045a743b01a40,0x0,0x980000114b02400010a5,0xc46c1728],#[0x203a8204000000105400,0xd22c0000000000000,0x85eb046e11501d0000,0x810e81ac528d08f49e00,0x455c000c5a000000020a,0x1cc0000002529,0xc16c0000,0x80000000000000000000,0x20a00000000000000029,0x896e06f0003,0x8e000000000000,0x692e1340001033000000,0x15412800000000000000,0x20060161c000410b1974,0x9238000000000046,0x401c0000000000000,0xc44c000562e2654a00,0xc93e05800000,0xc1e0000000000,0x1075020000025e,0x0,0x303d000304d000007200,0x32920003473000,0xc024000846b517c254,0x70a05023817000000000,0x805514d0019162843745,0xe9b807c62a308a,0x2c00000,0x2860002167000006c00,0x91806c000445406d000,0x63000000041100008233,0x21],#[0x186e000000,0xc2880000000000,0x206400000000,0x25c000007000000,0xc00305d09de416000,0x312200000000000,0xd1c800000000,0x0,0x2085000110a0000000,0xc14e14700000000,0x1553045409c00000,0x12710000000000,0x806800000000000000,0xb8220000e1ac00000000,0x325ac1d541,0x404e0af,0x1026000000000000000]]
def g250D9 := limbs80 #[#[0xd51ffa87f543fa41fd10,0x51b0259b138a803fea3f,0x410202544526488f00,0xf1464248a500f1a48a5,0x248a02051539228]]
def g250H9 := limbs80 #[#[0x910433820411040c3,0x961000245020000000,0xa30000004a8c1b00,0xc2403100000089441d,0x4550b41700086e0000,0x5a000011d1b00000000,0x425000e20a1eda0c14,0x9565ea0044000ca14090,0x40f0000004ab88cc2,0x16000000c2802f859000,0x700062d0000008a9000e,0x21f50a000887410d29e0,0xca2000404d28806061,0x2200029f0620,0x21a31418000000d0300,0xdc1511e00002dc05,0x81600042c000c271310,0x140708442b000a1b02,0x2000d62000812057000,0xbd610aa0000009088300,0x481c5100000000000084,0x2e000603000000000000,0x907e2908800c000c,0xe08564856000c0800,0x5000000006d41c000000,0xa41900080b026c0a000c,0x46c47084212086f023c2,0x6000001f000916000,0x3c1e000e28c5512d0000,0x803c0e00000001,0x1a098000000000]]
def g250D10 (j : Nat) := if j=0 then 0x2080513f else 0
def g250H10 := limbs80 #[#[0x35200822,0x160000050908050,0x18900250000,0xc3002400095418028,0x4094000d114002000000,0x2460000]]
def g250L : Nat → Packing
  | 5 => (16,5,5,720909,68,7,1024,g250D5)
  | 6 => (201,4,5,2949194,103,11,4132,g250D6)
  | 7 => (187,3,5,1703973,86,12,4161,g250D7)
  | 8 => (50,2,5,458758,51,11,4132,g250D8)
  | 9 => (6,1,5,0,0,8,0,g250D9)
  | 10 => (1,0,5,0,0,0,0,g250D10)
  | _ => emptyPacking
def g250I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 6 97 0 10 4 4 g250H6
  | 7 => lookupShort 83 499 6 14 8 4 g250H7
  | 8 => lookupShort 98 983 4 14 8 4 g250H8
  | 9 => lookupShort 28 191 6 12 6 4 g250H9
  | 10 => lookupShort 4 53 3 9 3 4 g250H10
  | _ => fun _ => none
def g250 : Forest := ⟨250,10,fun i => g250Y[i]?.getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P5_0 : CutRow g250 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P5_1 : CutRow g250 5 1 15 := by
  apply polarBlock (data:=fun j => g250Mark (j+0)) rfl
  decide +kernel
theorem g250B5 : CutRow g250 5 0 16 := (@joinRow g250 5 0 1 15 g250P5_0 g250P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_0 : CutRow g250 6 0 11 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_11 : CutRow g250 6 11 20 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_31 : CutRow g250 6 31 48 := by
  apply polarBlock (data:=fun j => g250Mark (j+15)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_79 : CutRow g250 6 79 48 := by
  apply polarBlock (data:=fun j => g250Mark (j+63)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_127 : CutRow g250 6 127 48 := by
  apply polarBlock (data:=fun j => g250Mark (j+111)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P6_175 : CutRow g250 6 175 26 := by
  apply polarBlock (data:=fun j => g250Mark (j+159)) rfl
  decide +kernel
theorem g250B6 : CutRow g250 6 0 201 := (@joinRow g250 6 0 79 122 (@joinRow g250 6 0 11 68 g250P6_0 (@joinRow g250 6 11 20 48 g250P6_11 g250P6_31)) (@joinRow g250 6 79 48 74 g250P6_79 (@joinRow g250 6 127 48 26 g250P6_127 g250P6_175)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_0 : CutRow g250 7 0 10 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_10 : CutRow g250 7 10 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_58 : CutRow g250 7 58 11 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_69 : CutRow g250 7 69 38 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_107 : CutRow g250 7 107 48 := by
  apply polarBlock (data:=fun j => g250Mark (j+185)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P7_155 : CutRow g250 7 155 32 := by
  apply polarBlock (data:=fun j => g250Mark (j+233)) rfl
  decide +kernel
theorem g250B7 : CutRow g250 7 0 187 := (@joinRow g250 7 0 69 118 (@joinRow g250 7 0 10 59 g250P7_0 (@joinRow g250 7 10 48 11 g250P7_10 g250P7_58)) (@joinRow g250 7 69 38 80 g250P7_69 (@joinRow g250 7 107 48 32 g250P7_107 g250P7_155)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P8_0 : CutRow g250 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P8_1 : CutRow g250 8 1 30 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P8_31 : CutRow g250 8 31 19 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B8 : CutRow g250 8 0 50 := (@joinRow g250 8 0 1 49 g250P8_0 (@joinRow g250 8 1 30 19 g250P8_1 g250P8_31))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P9_0 : CutRow g250 9 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B9 : CutRow g250 9 0 6 := g250P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250P10_0 : CutRow g250 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g250B10 : CutRow g250 10 0 1 := g250P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250T : mixedTables g250 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g250 0 0
  · exact mixedEmpty g250 1 0
  · exact mixedEmpty g250 2 0
  · exact mixedEmpty g250 3 0
  · exact mixedEmpty g250 4 0
  · exact g250B5
  · exact g250B6
  · exact g250B7
  · exact g250B8
  · exact g250B9
  · exact g250B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low250 : Lower true (varsX 250) (graphGoal 250) 11 := mixedLower (g:=g250) (i:=0) (hints:=288444480) (before_sound K246 V246) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K246 11 [(250,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V250 : Known true K250 := extend_ok (m:=250) V246 low250 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffac00b655592088,0xf2a7c440000fc003f03f])),(BitVec.ofNat 152 (word80 [0x15542c00a615182088,0xf2214041041041041041]))),((BitVec.ofNat 152 (word80 [0x17a9661c24816b,0x3d71450003f000000fc0])),(BitVec.ofNat 152 (word80 [0x26661529261404016b,0x3c614505145145145145]))),((BitVec.ofNat 152 (word80 [0x693c73808d498e,0xa0386b40fc0000fc0000])),(BitVec.ofNat 152 (word80 [0x7878692c728089418e,0xa03849430c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x1ddde832b352a0,0xb684590000003f000000])),(BitVec.ofNat 152 (word80 [0xbf801ddde032b340a0,0xb28459134d34d34d34d3]))),((BitVec.ofNat 152 (word80 [0xffff204b5c8261e496,0x1b7678bf000000000fff])),(BitVec.ofNat 152 (word80 [0xc0000040588261c014,0x116288a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x1164a8fd461e19,0x8548ae4000003ffff000])),(BitVec.ofNat 152 (word80 [0x848441e11,0x540a62cb2cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0xce92030a9a5575,0x608193bfffffc0000000])),(BitVec.ofNat 152 (word80 [0x82920108021400,0x809230c30c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(8,0,119,0,9)]
def g127A : List (List Nat) := [[]]
def g127D9 (j : Nat) := if j=0 then 0xff else 0
def g127L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,g127D9)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,9,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : CutRow g127 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : CutRow g127 9 0 1 := g127P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : mixedTables g127 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g127 0 0
  · exact mixedEmpty g127 1 0
  · exact mixedEmpty g127 2 0
  · exact mixedEmpty g127 3 0
  · exact mixedEmpty g127 4 0
  · exact mixedEmpty g127 5 0
  · exact mixedEmpty g127 6 0
  · exact mixedEmpty g127 7 0
  · exact mixedEmpty g127 8 0
  · exact g127B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 10 := mixedLower (g:=g127) (i:=0) (hints:=21828) (before_sound K250 V250) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K250 10 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V250 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffe4b5a7c4d122,0x4738d80000003e007c1f])),(BitVec.ofNat 152 (word80 [0x5582aa84b5a6849120,0x4318c804210842108421]))),((BitVec.ofNat 152 (word80 [0xffc0001abd58ac9e20,0xb4940d800007c00003e0])),(BitVec.ofNat 152 (word80 [0x9904ccdabd00ac9e20,0xb4900994a5294a5294a5]))),((BitVec.ofNat 152 (word80 [0xcc49dce2249,0x8adaa98000f8000f8000])),(BitVec.ofNat 152 (word80 [0x1e0f0f0cc49dce2208,0x8adaa90c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0x3a6ecfa14b8,0x9b2161001f0001f00000])),(BitVec.ofNat 152 (word80 [0xe017f003a6ecda14a8,0x9b20610c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffe5045955a87e,0xfba61403e000000003ff])),(BitVec.ofNat 152 (word80 [0x180001005951205e,0x82614294a5294a5294a]))),((BitVec.ofNat 152 (word80 [0x20ba0b95b59,0x44b3efc000001fffc00])),(BitVec.ofNat 152 (word80 [0x2000000800214851,0x40116b18c6318c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x19f806032484,0x810c37ffffffe000000])),0x42108421084210),(0x0,0x0)]
def g191C : List ColumnInfo := [(4,0,187,0,10)]
def g191A : List (List Nat) := [[],[50]]
def g191D10 (j : Nat) := if j=0 then 0xff else 0
def g191L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : CutRow g191 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : CutRow g191 10 0 1 := g191P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : mixedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g191 0 0
  · exact mixedEmpty g191 1 0
  · exact mixedEmpty g191 2 0
  · exact mixedEmpty g191 3 0
  · exact mixedEmpty g191 4 0
  · exact mixedEmpty g191 5 0
  · exact mixedEmpty g191 6 0
  · exact mixedEmpty g191 7 0
  · exact mixedEmpty g191 8 0
  · exact mixedEmpty g191 9 0
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := mixedLower (g:=g191) (i:=0) (hints:=21828) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe0000ffff916d07af3,0xa652a02500000f000f0f])),(BitVec.ofNat 152 (word80 [0x415560aaa106d02ad3,0xa6128025111111111111]))),((BitVec.ofNat 152 (word80 [0xfffff00000a0ab2f42,0x2a8e4aed0000f000f0f0])),(BitVec.ofNat 152 (word80 [0x826641333020a02f42,0x2a8e0a6d111111111111]))),((BitVec.ofNat 152 (word80 [0x50e97760d,0x2c231a5e000f000f0000])),(BitVec.ofNat 152 (word80 [0x78783c3c50e97760d,0x2c221a5c333333333333]))),((BitVec.ofNat 152 (word80 [0x2b4d9bd1e,0x3f24b60200f000000000])),(BitVec.ofNat 152 (word80 [0xbf805fc02b4d9bd1e,0x3f24b602777777777777]))),((BitVec.ofNat 152 (word80 [0xfffffffff9408f5244,0x5f5cf5180f0000f000ff])),(BitVec.ofNat 152 (word80 [0xc00060000400f5004,0x50407410222222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xb970ac2d,0xd10301f2f00000ffff00])),(BitVec.ofNat 152 (word80 [0x100008000091008020,0x1010182444444444444]))),((BitVec.ofNat 152 (word80 [0x647048192,0x20a01e05ffffff000000])),0x888888888888),(0x0,0x0)]
def g223C : List ColumnInfo := [(1,0,222,0,9)]
def g223A : List (List Nat) := [[],[16]]
def g223D9 (j : Nat) := if j=0 then 0xff else 0
def g223L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,g223D9)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,9,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : CutRow g223 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : CutRow g223 9 0 1 := g223P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : mixedTables g223 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g223 0 0
  · exact mixedEmpty g223 1 0
  · exact mixedEmpty g223 2 0
  · exact mixedEmpty g223 3 0
  · exact mixedEmpty g223 4 0
  · exact mixedEmpty g223 5 0
  · exact mixedEmpty g223 6 0
  · exact mixedEmpty g223 7 0
  · exact mixedEmpty g223 8 0
  · exact g223B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 10 := mixedLower (g:=g223) (i:=0) (hints:=30276) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 10 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffc0ad46ab3cc5,0xe42250000007c00f801f])),(BitVec.ofNat 152 (word80 [0xaa4555002d46a938c1,0xe0225084210842108421]))),((BitVec.ofNat 152 (word80 [0xffe000010af3f02268,0xa4dfd00000f801f00000])),(BitVec.ofNat 152 (word80 [0xcc8999810af3f02268,0xa496d18c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0x2c6976649382,0x30a4e0001f003e0003e0])),(BitVec.ofNat 152 (word80 [0xf0e1e246956649282,0x20a4c084210842108421]))),((BitVec.ofNat 152 (word80 [0x159dd2d1e2f2,0x4a602003e00000007c00])),(BitVec.ofNat 152 (word80 [0xf00fe0159dd2d1a2d2,0x48602294a5294a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffce08bd2445f5,0xce11807c000000007fff])),(BitVec.ofNat 152 (word80 [0xa0029004524,0x61105294a5294a5294a]))),((BitVec.ofNat 152 (word80 [0x1d70ac2dd10,0x315f2f8000003fff8000])),(BitVec.ofNat 152 (word80 [0x1000009008024510,0x114926318c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x32304919220a,0x1a05fffffffc0000000])),0x842108421084210),(0x0,0x0)]
def g239C : List ColumnInfo := [(1,0,238,0,10)]
def g239A : List (List Nat) := [[],[49,101],[32],[32,49,101]]
def g239D10 (j : Nat) := if j=0 then 0xff else 0
def g239L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g239D10)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,10,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : CutRow g239 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : CutRow g239 10 0 1 := g239P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : mixedTables g239 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g239 0 0
  · exact mixedEmpty g239 1 0
  · exact mixedEmpty g239 2 0
  · exact mixedEmpty g239 3 0
  · exact mixedEmpty g239 4 0
  · exact mixedEmpty g239 5 0
  · exact mixedEmpty g239 6 0
  · exact mixedEmpty g239 7 0
  · exact mixedEmpty g239 8 0
  · exact mixedEmpty g239 9 0
  · exact g239B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := mixedLower (g:=g239) (i:=0) (hints:=21861) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fcdb10b21d4b00c50,0x3f00003f03f03f])),(BitVec.ofNat 152 (word80 [0x8509b00320c4100c50,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0xc0221563760c463470,0xfc0000fc0000fc0])),(BitVec.ofNat 152 (word80 [0x9a21123740c023471,0x45145145145145145145]))),((BitVec.ofNat 152 (word80 [0x19da6f0c07013a20,0x3f00003f000fc0000])),(BitVec.ofNat 152 (word80 [0xe099a4f0c05013820,0xc30c30c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffd206ddb230311980,0xfc0000fc0000000fff])),(BitVec.ofNat 152 (word80 [0x1006dc8230210002,0x8a28a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x311530d553c94310,0x3f000000000000fff000])),(BitVec.ofNat 152 (word80 [0x10300530d112c84307,0x1c71c71c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x4ea124020c6c3ef,0xc0000000ffffff000000])),(BitVec.ofNat 152 (word80 [0x200440000000c4c384,0x10410410410410410410]))),((BitVec.ofNat 152 (word80 [0x280084888c08e40f,0xffffffff000000000000])),(BitVec.ofNat 152 (word80 [8,0x20820820820820820820]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(2,0,245,0,10),(4,0,243,0,10),(64,0,183,0,10),(32,0,215,0,9),(128,0,119,0,9),(16,0,231,0,8),(0,32,82,133,7),(20,0,227,0,7),(48,0,199,0,6),(128,32,82,5,6),(160,0,87,0,6)]
def g247A : List (List Nat) := [[]]
def g247D8 := limbs80 #[#[0x93888e7c05dcd635ca43,0x1]]
def g247D9 := limbs80 #[#[0xfefbfdee6390d6458d43,0x2590398c358c05c9fffe,0x1dd095d9b58d9dd815d8,0x4dd0c5d0c58c1dcd15d2,0x632c52e8033124641c00,0x3499639e1489745df8e1,0x4080b30844a5a839252a,0xd90182160283200c0eff,0xdf00807580a0cb60283b,0xebd0141d3e020380181,0x80e4e0204182e076f008,0x3db80]]
def g247H9 (j : Nat) := if j=0 then 0x2 else 0
def g247D10 := limbs80 #[#[0x64ff98ffd63ff90ffd43,0x49c65026ba1570cc03fd,0x6701cb124e5030e939aa,0x9409216519c0c39a8594,0x2ce629271]]
def g247H10 := limbs80 #[#[0x1359004c04400000021,0x80000e4a000000027074,0x4800000005a0013800]]
def g247D11 (j : Nat) := if j=0 then 0xa8426037f else 0
def g247H11 (j : Nat) := if j=0 then 0x1a0020002400e0060 else 0
def g247L : Nat → Packing
  | 8 => (1,3,4,0,0,0,0,g247D8)
  | 9 => (14,2,4,327685,51,9,4112,g247D9)
  | 10 => (5,1,4,0,0,8,0,g247D10)
  | 11 => (1,0,4,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupShort 1 2 0 2 0 0 g247H9
  | 10 => lookupShort 3 37 3 6 4 0 g247H10
  | 11 => lookupShort 1 13 0 5 3 0 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : CutRow g247 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : CutRow g247 8 0 1 := g247P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : CutRow g247 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_1 : CutRow g247 9 1 10 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_11 : CutRow g247 9 11 3 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : CutRow g247 9 0 14 := (@joinRow g247 9 0 1 13 g247P9_0 (@joinRow g247 9 1 10 3 g247P9_1 g247P9_11))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : CutRow g247 10 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : CutRow g247 10 0 5 := g247P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P11_0 : CutRow g247 11 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B11 : CutRow g247 11 0 1 := g247P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : mixedTables g247 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g247 0 0
  · exact mixedEmpty g247 1 0
  · exact mixedEmpty g247 2 0
  · exact mixedEmpty g247 3 0
  · exact mixedEmpty g247 4 0
  · exact mixedEmpty g247 5 0
  · exact mixedEmpty g247 6 0
  · exact mixedEmpty g247 7 0
  · exact g247B8
  · exact g247B9
  · exact g247B10
  · exact g247B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := mixedLower (g:=g247) (i:=0) (hints:=1348) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2af90d90ae18042800,0xfe0007f01fc07f])),(BitVec.ofNat 152 (word80 [0x227801902608042810,0x20408102040810204081]))),((BitVec.ofNat 152 (word80 [0x351561bb02231a3800,0x7f0003f800003f80])),(BitVec.ofNat 152 (word80 [0x351121ba02011a2850,0xa142850a142850a14285]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc3ba79c203c0dd1000,0x3f800000000fe00000])),(BitVec.ofNat 152 (word80 [0x83ba49c202c0dd1132,0x64c993264c993264c993]))),((BitVec.ofNat 152 (word80 [0xc406c8995858acc000,0x1fc00001fc0000003fff])),(BitVec.ofNat 152 (word80 [0xc006c8011810a080a1,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x5215362ae9a4a1880f,0xe000000000000fffc000])),(BitVec.ofNat 152 (word80 [0x50053628c9242082c5,0x8b162c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x9ca1724506341f7f0,0x1fffff0000000])),(BitVec.ofNat 152 (word80 [0x88016044062415306,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0xb020824406047207ff,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x408,0x10204081020408102040]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,11)]
def g251A : List (List Nat) := [[],[100]]
def g251D11 (j : Nat) := if j=0 then 0xff else 0
def g251L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I (_ _ : Nat) : Option (Nat × Nat) := none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : CutRow g251 11 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : CutRow g251 11 0 1 := g251P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : mixedTables g251 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g251 0 0
  · exact mixedEmpty g251 1 0
  · exact mixedEmpty g251 2 0
  · exact mixedEmpty g251 3 0
  · exact mixedEmpty g251 4 0
  · exact mixedEmpty g251 5 0
  · exact mixedEmpty g251 6 0
  · exact mixedEmpty g251 7 0
  · exact mixedEmpty g251 8 0
  · exact mixedEmpty g251 9 0
  · exact mixedEmpty g251 10 0
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := mixedLower (g:=g251) (i:=0) (hints:=20548) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
set_option maxRecDepth 32000 in
def g253MarkBits := limbs80 #[#[0x7060305040302020100,0x100f0e0d0c0c0b0a0908,0x19181716161514131211,0x222121201f1e1d1c1b1a,0x29282726252524231f22,0x2e042d2c2b2b022a2a1c,0x3505053403333231302f,0x3a313039383736373636,0x3b3e033e033d053c3b03,0x3e042d403f2b322c2c3b,0x42040404042c41410404,0x2c404746453144444343,0x4903034804322c2c2c03,0x4c4c0e0e3a4b0505324a,0x504f3b384e4d2c034c4c,0x3a54533a3852032c5150,0x3257572e562b032c553a,0x5d3a5a5c2e5b5a595958,0x60605e5e3a5f5e5d3a5e,0x67660504656463626161,0x6e6d326c046b6a4d6968,0x535710535054b706f05,0x76797873777675747372,0x7c7b3505043505357a3c,0x15807f7f7e7f7f7e7d7d,0x16168216168216818116,0x7f86047f7e7e85848383,0x7979798a898588838387,0x7f8d32898c7e798b7979,0x32899594939291908f8e,0x9a9b9a2b999898979691,0x52509f9f989e9d339c34],#[0xa12b9a797917949ea038,0x89a33f9a896ca2697f9a,0x8281a516821616a48e8e,0xa8a8059fa7a68e816982,0xad503dac50ab50aaa94c,0x3c7979696969697e83ad,0xae7f7f79767976791717,0xb14169417fb07fb0af69,0x9ab590b43fab46b3b2af,0xb8aeb77905b64a9c3294,0xbebd046ebcbbbab9a405,0x4b81164b7a94c0bfbfbf,0xa9c655c59dc4c39fc2c1,0xc7c97982b9c8c7b9a99c,0xc8c8cb8282cac8cac8c7,0x828a798a79ccc8ccc8c8,0x8705049d878787717979,0xce79828a2679787583cd,0xd0744b79cf26797979cf,0xc98682c8d39dd2d14b7a,0xd75583d6ccccd5d43571,0xb9c816cbc73182828f5f,0x797979791679c8c8c8c8,0x6b0505dbda35d9d86979,0xd90535350505d7d9dbda,0xdb0505dbdc35356bd94b,0x35359add350505050505,0x81163f3f3f7f7f7f3535,0x7f837f86043f693f818e,0xd8e0e0e04b6635dfde7f,0x693505050569693f0584,0x8405693f83694b696969],#[0x95e14b9b4b7f839b9b3f,0x69693f3fe13f69956969,0x6981693f8e818135168e,0xde4bde4b4bdee305e281,0x3535db35dd6969696935,0x3f3f3f3f3f3f3f4b3535,0x693f694b69693f69693f,0x69e44b4b48359583953f,0x5e269e269e2e2e205db,0x4b4b4b4b8ee516e2e24b,0x693f8eb94b35849a6969,0x4b694b3f694b8e4b3f69,0xdbe269696905e5b94b8e,0x3f]]
set_option maxRecDepth 32000 in
def g253Labels : Array Nat := #[0x84040301084410,0x2400a1402a4110,0x24040301024120,0x283040301083461,0x2830241a0983431,0x2830241a0983441,0x902040241102831,0x84018280684460,0x84040241084460,0x284040241084440,0x200124124d01153,0x200124124d01154,0x2820241a0982420,0x210241a0921130,0x210241a0921140,0x21040301021160,0x302040281102821,0x601424130d03462,0x300024104b01151,0x21424160921510,0x200140205201131,0x21040241021110,0x21040241021120,0x400040221402862,0x84040241084440,0x200140205801154,0x21040301021140,0x283040141083441,0x210301c0c21110,0xa1020140821130,0x84040281084440,0x284040241084420,0x288018280688440,0x21020300821130,0x24008240224140,0x288020300888430,0x308018280708831,0x601040221403452,0x21020140821110,0x8000180d0e04453,0x284040301084430,0x308010280508841,0x400024130d02452,0x24040301024130,0x906040241106852,0x220241a0922150,0x21040281021150,0x808030380e0c065,0x21040341021150,0x808008240a0c054,0x2830241a0983461,0x808018240e0c054,0x208030300e09053,0x283040281083441,0x21040241021140,0x21040241021150,0x10000100a1408874,0x240301c0c24160,0x210241a0921150,0x2400a0d02a4160,0x220241a0922160,0x2830240a0983441,0x906040241106842,0x220241a0922140,0x22040241022150,0x24008240224160,0x280301c0c28160,0x24040241024160,0x28020140828150,0x2400a1402a4130,0x24018140624130,0x284040241084451,0x28010280428150,0x208030300a09053,0x8080182c0a0c054,0x906040281106842,0x283040281083451,0x208030380a09053,0x808018240a0c054,0x601840221403875,0x2400a0d02a4150,0x24018140624140,0x1000020111808474,0x808018240a0c043,0xc04840221406875,0x21030140c21130,0xc04040221406865,0x2830241a0983451,0x2800a0d02a8160,0x2800a0d02a8150,0x283020300883461,0x800040211804473,0x801040281805053,0x21040301021170,0x2820241a0982431,0x800040241805064,0x282040281082431,0x28008140228150,0x10040301c140c074,0x2830241a0983430,0x601424130d03473,0x601840221403873,0x2830241a0983471,0x204040301205073,0x208020300a09073,0x2200a0d02a2140,0x28020380828150,0x28008240228150,0x24040341024140,0x24040381024140,0x10000100a1408875,0x208030380e09073,0x200030380e09063,0x40800a25068a053,0x24008340224150,0x218301c0c21920,0x2600a0d02a6140,0x240181c0624130,0x21840241021920,0x601840221403863,0xc04040221406863,0x400040221402863,0x408024320d0a054,0x28008340228150,0x220080d0222120,0x220241a0922120,0x22040281022130,0x220241a0922130,0x84040301084430,0x21040241021130,0x210301c0c21120,0x2200a0d02a2130,0x606040301207053,0x400040221402872,0x283040281083431,0x906040281106832,0x24040241024150,0x400040221402873,0x601040221403863,0x204040301205042,0x21040301021150,0xc02040241807064,0x210301c0c21130,0x8080182c0e0c054,0x208030380e09053,0x204040301205043,0x204040301205063,0x602040301207063,0x208020300a09053,0x240181c0624150,0x906040241106872,0x2080182c0e09074,0x24040281024160,0x10010181c1609074,0x240181c0624140,0x24040301024140,0x283040301083451,0x2200a0d02a2160,0x24040341024160,0x24040281024150,0x210181c0621150,0x240081c0224140,0x8080102c0e0c054,0x208010380e09053,0x21040341021130,0x210201c0821130,0xa1020140821150,0x10010181c1409074,0x21020300821140,0x2200a0d02a2150,0x2400a1402a4160,0x284040241084431,0x200040301205063,0x902040281102842,0x210301c0c21160,0x240181c0624160,0x21020300821150,0x10000181c160c075,0x283040281083430,0x2400a1402a4140,0x283040281083461,0x200040301205073,0x280082c0228150,0x10000301c1c09075,0x210402c1021130,0x21020140821120,0x280241a0928160,0x280181c0628160,0x1000010091408475,0x408024320d0a074,0x400024320d0a064,0xa1020140821120,0x2080241a0b09063,0x210102c0421130,0x601040221403865,0xa1040241021120,0x204040281205053,0x288020300888441,0x22040301022150,0x21024160921110,0x400024130d02463,0x230241a0923130,0x601024130d03463,0x400040211402463,0x906040281106831,0x280102c0428150,0x606040301207042,0x40800022050a053,0xa10301c0c21120,0x40800a25068a054,0x210101c0421130,0x8000180d0e04464,0x408024320d0a053,0x240101c0424140,0x284040301084441,0x906040281106862,0x40800a25068a064,0x808008240a0c065,0x24008140224140,0x24008140224150,0x28008240228160,0x2400c160324140,0x208020300a09063,0x408024320d0a064,0x204040301205053,0x24040301024150,0x21020140821130,0x283040281083471,0x28010280428160,0x21024160921120]
def g253Mark (j : Nat) := g253Labels[packedAt g253MarkBits (8*j) 8]?.getD 0
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xd29111fa4000007c00,0xfc007ff80008188c20e9])),(BitVec.ofNat 152 (word80 [0xd21111780242108441,0x41082080000080400e1]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7d020c29c0000f803f,0xf800000102030d9ff])),(BitVec.ofNat 152 (word80 [0x7d020c28c6c6318cc3,0xc3186180000000009ff]))),((BitVec.ofNat 152 (word80 [0xeebc1120001f00000,0x3f000000020c0431fff])),(BitVec.ofNat 152 (word80 [0xeebc11217d6b5adcb,0x2cb39658000040001fff]))),((BitVec.ofNat 152 (word80 [0x114da6c2403e0003c0,0x1fe20c7077c021f])),(BitVec.ofNat 152 (word80 [0x14c86824c8c631886,0x18610c3224020268891e]))),((BitVec.ofNat 152 (word80 [0x930892001c0000000,0x3fffe073f07f87fe890])),(BitVec.ofNat 152 (word80 [0x28294a5014,0x514428a72e07b679e000]))),((BitVec.ofNat 152 (word80 [0xa4c4241d3e000003ff,0xfc000007c007ff801722])),(BitVec.ofNat 152 (word80 [0x80200531318c6118,0x618630c50804f4821600]))),((BitVec.ofNat 152 (word80 [0x420a5204bffffffc00,0x7fff800000444])),(BitVec.ofNat 152 (word80 [0x220,0x8208410090b800000000]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(1,0,252,0,10),(4,0,249,0,10),(8,0,245,0,10),(32,0,221,0,9),(16,0,237,0,8),(64,0,189,0,8),(128,0,125,0,8),(0,8,85,160,7),(17,0,236,0,7),(20,0,233,0,7),(68,0,185,0,7),(72,0,181,0,7),(24,0,229,0,6),(32,8,85,128,6),(48,0,205,0,6),(80,0,173,0,6),(96,0,157,0,6),(128,8,85,32,6),(56,0,197,0,5),(69,0,184,0,5),(81,0,172,0,5),(144,0,109,0,5),(160,0,85,0,5),(160,8,85,0,5),(192,0,61,0,5)]
def g253A : List (List Nat) := [[]]
def g253D6 := limbs80 #[#[0x65176550535d96455053,0x591545c453591545c053,0x5918014d436196414d43,0x6518614d435918114d43,0x5956458d436408558d43,0x640835954365a6558d43,0xe4187595436448359543,0x59563d4d43e458759543,0x5956458d536408558d53,0x64483595536408359553,0x64483595546408359554,0x5d5801d563e4b815d954,0x59683551636407555163,0x65075595636447559563,0x64483595636408359563,0xe4585dc9646508359563,0x5cd801cd6566275dc964,0xe4584dcd655cd811cd65,0xe4587593535955458e53,0x76c75c5ea76a75a5e879,0x6ce5cd6cd5c7cc7ac79c,0xd95d93d87d56d55d4ece,0xe1ea3e87e17dc6dc5d96,0xe860f4af49f0bf07ee2e,0x887cf2426ba21b7d10a0,0xae2ea4dd873f0c21f9e,0x882ea4516522caa11155,0x82ea5b5842ecaa16b614,0xaea6318432aaa18661cb,0x44723a2353d09a561cc7,0x40f79203dd107fe8823f,0x9ad84496c2212e491ef4],#[0x4d9164fd14bc5d245308,0xd54768aa38461d872e8c,0xa45e2d1b7350da8b4af4,0x358ec9aca60d55b06a07,0x887d242760df3f4301f9,0xb31c6558e33f4518ba4,0x10874321508834120500,0x45208f47235188b45225,0xd26530974b2552893492,0x351285409f4f275389b4,0x8ab552a550a75329548a,0x568b3592c560af572b55,0x2997e0d]]
set_option maxRecDepth 32000 in
def g253D7 := limbs80 #[#[0x590535d95414d6455053,0x14d87590535d96414d74,0x5917014d545c053e0964,0x5d0535917114d545c453,0x50d815c0656117614d86,0x6005350d6414d4355053,0x14d436085350d8114d43,0x50d655514358d5350d86,0x9955450d86551435d954,0x55143a195450e7655143,0x50d5458d432156350f65,0x5d56350d6558d4359163,0x58d439956350d8558d43,0x50f6558d43a156350e75,0x5956450f8558d43e1163,0x591436156450d7559143,0x50e85591439d56450e65,0x5d56550c8359543e0964,0x595439d56550d8759543,0x50d765d543e1d6550f83,0xe117650f825d943e1975,0x98d435526350f855d943,0x50d7598d435966350d64,0x60e7550d84995435d665,0x9d94360e7650d869d543,0x50d64d4d4358f5350d85,0x6135350d76d4d4359753,0xd4d4361f5350d86d4d43,0x50d54d8d43d8f5350e76,0x6176350d84d8d4359763,0xd954360f6550d87d8d43,0x54d85dd94361b7550d84],#[0x5916354d5458d5321563,0x58d5361d6354d6558d53,0x54f8259153dd16354e65,0xe117654f835d95320d65,0x9d9535926354f855d953,0x54d84d95536136354d84,0x60d6455184dd95359774,0x59554e09645528359154,0x552835955460d6555083,0x59573551645cd54e1165,0x5d954e1973551765cd54,0x553835d954e097655381,0x59673551649cd54e1176,0x9cd5461673551819cd54,0x551859d95460e7655186,0x61b7355164dcd5461f65,0x1d5635d47558d83dd954,0x58d841d5636047558d80,0x5955458d64551631d554,0x551639955458d8355163,0x58f7459163dd55458e83,0x20d6558c7559563e0964,0x5d163e0d6558f7559563,0x58d8499563e117558f82,0x60b5458d849d563dd665,0xd516361b5458d83d5163,0x58d85dd163dd75458d87,0xe1573593845956461375,0x9cd64e0d75593815d564,0x591869cd646167359181,0x59772591869d56460e75,0xdc9645d77259173dc964],#[0x59265dc9646177259183,0xa0f7259275dc9649cf72,0xdd5646177359285dc964,0x595801cd655cc7359583,0xe1173595841cd6560473,0x9cd65e0974597815d165,0x59584dcd65dce7359584,0x5d56390d6558e4360f74,0x596435d96590d7559643,0x90d635c643e0d6590d87,0x5915494d635ca43d9571,0x552535d15494d6555253,0x94e86552536195494d76,0x5d16394d5458e53d9554,0x592535d16494f8758e53,0x94d655d253e096494d87,0x61f6494d83d9253e1176,0x552636136594d83d9653,0x98d74552635955498d64,0x5957498f8359663e0964,0x593535d164d4d7458f53,0xd4f8759753e0964d4d87,0x61763d4d84d8f5359763,0x5536359572d5185d9353,0xd8d75553635d154d8d65,0xfc7e8fb1ee3bc5f61d54,0x6babf4ee7dcf79df37e3,0xafb5eebd579aef5d6b7d,0xf69ecfd9eb3b66ecbd8f,0x5aeadcfb6f6dadadb3b5,0xf6debbcf77aeeddbbaf7,0xe5fcbd8ff1ddf6beb7ce],#[0xccf79e73be76ceb9bf35,0x4fa7f4de97d0f9fb3ee7,0xb1b62ec3d7baef5beafd,0xf736e5dbbb6f6becfd8f,0xff17e1fbe779eeddd7b9,0x4ee9bcef9bf35e67cbf8,0xee7db7b5f67eb7d5fa7f,0xfe9fcbf8ff0fdebbcf75,0x8aaa08465503ff1fcbf8,0x84d5903ddb0c1b115411,0x49fb0c1d1d860d98b20,0x206151751eceb28e3f65,0x365c4b0b2e203e44c027,0xa8badf575971873278b6,0x4db590208f240f716406,0x169b28034d760021c90,0x24140997055abb02b15d,0x5965aa8b2ad8ae482c67,0x42c8aea2641751320aa5,0x7bc59661eacb2e0f91e2,0x23ce3251e75918f3cc84,0x251c5d918e30c8471a65,0x398815ebac11465238b3,0x6dc13903e45f41f23da0,0x482662b483235adb9272,0x6ac83235e0998ae21c8d,0xe76ad173b470c20610e4,0x5651307c8de01e62cd9a,0xd4b28ec16190f4aca87a,0x11f658874cea3da5751e,0xcaf0aea5ab1901b3ecb1,0xcaacad912e58c8172764],#[0x565cfd2b2e7695955f4a,0xd2b2c45559782aaed916,0x29965a2742cb0da5658a,0x9a1f30cef2185764cc84,0x241c95916a4cc8351b65,0x984439cca094e6183b6f,0x4eca25b561d0d3f28873,0x2086612d1b2a97a5654b,0x91e42ca8e1d984464c3a,0x2c9215974860c3a2b25d,0x98644d6b2a26de49102f,0x55c92349e61175b288b3,0x408661291b2a948f9546,0x496470a39a1651c9cca2,0xca38c17526aaba8f0765,0xb651cd7328e6a594735a,0x4ecb0e6be1473590a39a,0x2e0dd47702ea3a9f961c,0x4793b2a4b3a8525d4b29,0xea3d65751ed4ca0f5e5d,0xd9421d3c28f692147ace,0xb2ba920f65c86f2ea429,0xfde2147cff2c3f677524,0x8acf2c3f64961fbdc28,0xa369d941b56c88d8866,0xd65394eca11a7e50824b,0x4fcb1ca7658e6730c73a,0x635e60f2f2ea7781753a,0x131930e9921854cd0b2a,0xea9f55754d64baa70766,0xc93144fc98a05e554182,0xbbbb0a5d5d8535f2629a],#[0xd206585eeeec2f757617,0x8543b303435971a4ec98,0x2a2b87921541ca8aa8e4,0xd9318644c0adde5456e9,0x51c90b29e4459032a309,0xb4fe485a87222c9f9316,0xc65912e2d3b93169c498,0xa5b87752d40ca8ca764,0x5752ababa93a7e4c9e7b,0xac4b141be58a06b2e557,0x4a9e44a4db2c575b9628,0xb8db2c589d932c4fc99,0x864d5872ebcba974e61,0x687326ac3995e5d4ca73,0x6bba99355d4ca732864d,0x7d5258bdaeec64d57632,0x4c1d720608d9331abcb1,0x2660d793306fc91839e4,0xb963061ca9832e50c02f,0x65bb1f325d8f82b2666b,0x935dd545aaeaa2c3983d,0x4d0972468cb755264baa,0xc66aba76355dc31a0be5,0xb65355cb29aaed8cd572,0x5cb2a9ae5d901aaec7eb,0xb309d4e1bcea6cbb6553,0x4d9bb0a6cdc8536c3c21,0xa66cdd53366fc29b37a1,0x3533860a99c0d654ddbe,0x6abaa0b0994e182ca70c,0x2309955182caa8c17542,0x6ff1b2b8d9195c4c8b2e],#[0x780d597c36abb61de59,0xb92076bc9e159e0f06f7,0xbabb006ce48032f24139,0x13765c15baec0b759401,0x829bf24096b8203c3c10,0x26b1a59358b5c905e1e4,0x9655b55c92b85e51674f,0xd2ba2c69e1562f70ab77,0xc69651634f08b1a58458,0x9864b08aba49858d3ca2,0xeb8dd875c13c931aae4,0xd765c9532ae4a59571bd,0x6f4bae3765d71beecb8d,0xf89e49924b08bb7b9365,0x17af70abcd7845e64ba2,0xc8bec9545f64a1af8565,0x1546061c230306118192,0x64ba3109e49882b28c0c,0x769d973b02e99cc96466,0x33ef70f9dad84ced6b26,0x29a0d584d0b3b2e7e059,0x986c9bab2e48d65f1c7b,0x40ca66a364f35072990c,0x5dd6532aeaed8fb392c7,0xf311f27969392cb4bc8e,0xeba74563d316cbe62364,0x782d16ecbe9b75db4dba,0x6abaeb37e4b49970ba38,0xcb55d3607f27a81595d7,0x7802b2baac974d913c96,0xe9cac974e613c97330e1,0xd76e394b2f1b05d39eaa],#[0x65c1f0e1e0b85bb2fc6d,0x437e4b89cf23c57565e1,0x6285b29c8c184e460b9f,0x70f77758646cac52b64,0x17487d3c9c3e924e1df7,0xbaba42a56461747290fa,0x5b0e1e2eeae916c18785,0xa2d830d1775948b61c1c,0xd3727759892b2cc30e1,0x3959a7dbaccb06626d83,0x1acac637dd63612cb1ac,0x9425964a8ca725455392,0x649bceb24dd75926e3ac,0x2922d774916bc9ce37dd,0xd948f16ca4830e124043,0xd3bac89f65244fd2f1e7,0xa1965240cd311c65948e,0x20dd2e9042d949561bac,0x31022f94819cc9c2395d,0x3759664ba4b325d24d87,0x64c3ed3255275bf253ac,0xdb2e1b71930db97565dc,0x3787f27bedd75dd60c3e,0x7d8fb83ea65c1f58865,0xb866f81c33739e47b587,0x1fc9b812e49c09f22e0f,0xc50591e174ece2bb8670,0x1de030cece5767896b2b,0x24fcb9767a60bb3c8666,0xb637f5cb1bfdd595fb0f,0x52c8b420e559e7b06d2b,0x54960da83b26da819568],#[0x1b24708d883946b40ca3,0x24e4e7917d40c9b6a065,0x39472a0b239399cdca97,0xcbc139359cdd1bce6e74,0x93960dc9c906e5979272,0x1cb1708e4e783727341b,0xc6e4e6537272a9b962e5,0x593727249b93998dc9ca,0x6e41b9b9e4dc9cd26e4e,0x9b7e0dcdbd06e6dd8373,0xdd1bca6e6dd5373c3c23,0xc6e8d563746b29ba3554,0x1737c6ab9bd8d64dd5ac,0xbec9f4b598e01aac700c,0x492656b4972b518794a8,0xebb0f29524b93a9cbc8d,0x2b5e4b95aa6ec2d51264,0x791ab24c9d612e4e9c93,0x60bacf9264ec09727579,0x2305d68dcaeb44c2759f,0xe7986a762c153b15cbad,0x2940e673a072b9d00764,0x573a56b39d0b55ce8687,0x6b29d93554ec972e74cd,0x98fe52cdcae96ae974b4,0x2ed92e96f2195b66bcc5,0x2578e791bc64ba5d3561,0xd53b8a5c95c3250ef1bf,0x87b1dc4358ee25ea7712,0xc399cee1cae770e473b8,0xee656a7732953b973b9d,0xe772dd73b96e39dcc258],#[0x3c00061cadeb7dcee5bc,0x5d029811806e02d00d80,0x28213509484381f00de0,0xf587403761940bc0574,0x452028513008fc446207,0x81990c5c5e22cb1600ad,0xfc7ae3b91c88e146d234,0xa0244918c8984372100f,0x480a184f126b132c96c4,0x5cb2db9658af255a2a31,0x1990cb064d3159824bd8,0x86b83541a68d1467e339,0xe9c44e0a6f63739b44d8,0xe07613ac9d34e7c72b38,0xf49f54f927ba3d11e38e,0x6682b411a044ffe7f73,0x431a16d0a684b421a0ed,0xd12688b441a1ed0e686b,0xb461a2ed1668ab451a26,0xed1e68eb471a36d1a68c,0x2b491a46d22690b481a3,0x56d2a694b4a1a4ed2669,0x98b4c1a5ed2e696b4b1a,0xa6ed3669ab4d1a66d326,0x69eb4f1a76d3a69cb4e1,0x1a86d426a0b501a7ed3e,0xa6a4b521a8ed466a2b51,0x41a9ed4e6a6b531a96d4,0x566aab551aa6d526a8b5,0x571ab6d5a6acb561aaed,0xd626b0b581abed5e6aeb,0xb5a1aced666b2b591ac6],#[0xed6e6b6b5b1ad6d6a6b4,0xab5d1ae6d726b8b5c1ad,0xf6d7a6bcb5e1aeed766b,0xc0b601afed7e6beb5f1a,0xb0ed866c2b611b06d826,0x6c6b631b16d8a6c4b621,0x1b26d926c8b641b1ed8e,0xa6ccb661b2ed966cab65,0x81b3ed9e6ceb671b36d9,0xa66d2b691b46da26d0b6,0x6b1b56daa6d4b6a1b4ed,0xdb26d8b6c1b5edae6d6b,0xb6e1b6edb66dab6d1b66,0xedbe6deb6f1b76dba6dc,0x2b711b86dc26e0b701b7,0x96dca6e4b721b8edc66e,0xe8b741b9edce6e6b731b,0xbaedd66eab751ba6dd26,0x6eeb771bb6dda6ecb761,0x1bc6de26f0b781bbedde,0xa6f4b7a1bcede66f2b79,0xc1bdedee6f6b7b1bd6de,0xf66fab7d1be6df26f8b7,0x7f1bf6dfa6fcb7e1beed,0xe02700b801bfedfe6feb,0xb821c0ee06702b811c06,0xee0e706b831c16e0a704,0xab851c26e12708b841c1,0x36e1a70cb861c2ee1670,0x10b881c3ee1e70eb871c,0xc4ee26712b891c46e227,0x716b8b1c56e2a714b8a1],#[0x1c66e32718b8c1c5ee2e,0xa71cb8e1c6ee3671ab8d,0x1c7ee3e71eb8f1c76e3,0x46722b911c86e42720b9,0x931c96e4a724b921c8ee,0xe52728b941c9ee4e726b,0xb961caee5672ab951ca6,0xee5e72eb971cb6e5a72c,0x2b991cc6e62730b981cb,0xd6e6a734b9a1ccee6673,0x38b9c1cdee6e736b9b1c,0xceee7673ab9d1ce6e727,0x73eb9f1cf6e7a73cb9e1,0x1d06e82740ba01cfee7e,0xa744ba21d0ee86742ba1,0x41d1ee8e746ba31d16e8,0x9674aba51d26e92748ba,0xa71d36e9a74cba61d2ee,0xea2750ba81d3ee9e74eb,0xbaa1d4eea6752ba91d46,0xeeae756bab1d56eaa754,0xabad1d66eb2758bac1d5,0x76eba75cbae1d6eeb675,0x60bb01d7eebe75ebaf1d,0xd8eec6762bb11d86ec27,0x766bb31d96eca764bb21,0x1da6ed2768bb41d9eece,0xa76cbb61daeed676abb5,0x81dbeede76ebb71db6ed,0xe6772bb91dc6ee2770bb,0xbb1dd6eea774bba1dcee,0xef2778bbc1ddeeee776b],#[0xfe2f0f82f677abbd1de6,0xa4a148485c3015080381,0x19a1024b105b0b63e181,0x34b8a2e492468d8989c4,0x8744a9456444200d1ba2,0x21611578e4e11c231689,0xa4518609d960e6595b87,0x28405bf2210948c86128,0x89425208055fc4004457,0x345208055ea4016e7,0x8070c2019fa0305dfd,0xb02223b648032011013f,0xa3f9880411836c118e6,0x68961fce49bc09d11806,0x6ff20064b21706883e20,0xe17c04114012ff8000d1,0x122afc0e0208a008016,0xc96d23247f8060abf1d0,0x8232014fd01225ff428,0xc01088c7e00192cf1f90,0xcb440177c08208b3e7,0x2affe08088ade4c1103,0x8430046e223706014e88,0x6195b81887e82218fd0,0x3181fc04448e06202f31,0xc91c2c49d7004640ef82,0xa111b2029d260c23ae04,0x3c090080117e8808c81f,0xc869888f02a622321321,0x9908381d3424ec414584,0x801908b8103c85591190,0x544396082afc9858c5c0],#[0x4009b0e4b3159093811c,0x13d214f48]]
def g253H7 := limbs80 #[#[0x478d0054041800010400,0x14a0000ac0031b754a4,0xc320e0012e353a920032,0x951fbcdb400053de00d1,0xe200b800440bcc0010ab,0x890366015601a8000001,0x10e003f0401a6000064,0xe89601999dea4e011a00,0x6015c0001d800000000,0x1a2480000000001]]
set_option maxRecDepth 32000 in
def g253D8 := limbs80 #[#[0x5c4535c0535905355053,0xd90535d8535d0535c853,0x5c8635c4635c06355063,0x5cc655c0655d4635d063,0x54d431954314d435d065,0x595435914358d4355143,0x9954398d435d9435d543,0xd8d43d4d439d9439d543,0x55153dd943dd543d9543,0x5d153595535915358d53,0x9d9539955398d535d953,0xdd153d9553d9153d8d53,0x5cd545955459154dd953,0x9d9549cd54995545d954,0x1d563dd954dcd54d9554,0x5d163595635916355163,0xd51639d563995635d563,0x59564dd563dd163d9563,0x9cd64995645d5645cd64,0xdd564dcd64dc9649d564,0x9cd655d1655cd651cd65,0x5964358e43dd165dcd65,0xd4e435da435ca435c643,0x5925358e5355253d9643,0xd52535da535d25359653,0x5926355263d9653d9253,0x5da655da635d26359663,0x5d353597535935358f53,0x59754d9353d8f535db53,0x553635db545cf545cb54,0xd53635d7635d36359763,0x5d3655cf655d7645cf64],#[0xbceefb7ebfade7f9f67b,0xc7effbfafdbeef7bdaf5,0xdd773dbf5fd7b5dd6f3f,0xe5f7fdfb7ddf37bdeb77,0xf9fdff5fcff1fbfedf9f,0x224b0047fdfeff7fbfeb,0xb0c46355088ec1112181,0x9658ecaeb1d80382321,0x5d8022aa044954069aa8,0xa01c17901825efaca90f,0xc08e4565e80704d01e05,0x19d64220705fd9608736,0x643c130e786610f14c31,0xa370854a618f4ab29e9d,0xca567e10aceb2159d542,0x98dd4ab0ba9587652b0a,0x18d30ba9a9d64353aa86,0x48b29409873e33087ca6,0x314577628aaec524994a,0x55752d4704586e18a0cc,0x1246b00486e14b2bba96,0x330848a60c916c112318,0xe5d45d4b95c197098724,0x45d4d8cc21b0b872e130,0xd00cc220298340130e6d,0x4c19c2d8238170c60261,0x196b82325f0464261909,0x985445306742e14cabc2,0xb6d2cb65cd96c38b2d80,0xecb5a1596b14c35b9565,0x5d45d6b95c1d76175ad0,0x60ee05c3d70987ae82ed],#[0x105c2da0987b882ed70a,0xb203716406eec809d590,0x12f8202a2ec024590039,0x740e130e0505d80aaba0,0xaab0c14261c3a0bb0755,0x8190610305c20656860,0x261d20bc2a481654887,0x95242b2a4956548c6e89,0xcbc2a49485490eca9259,0x2ac816558530ca655954,0x15855a5306b4be0928ac,0x34c130cbd4595784c3ad,0x2b0caa5e0d34a41a62b8,0x8a02e0d431c1a829835c,0x2611805c2a8538550170,0x6f30ba5e9754bd2aa978,0xaba5d6387bd0ecb7a159,0x5f5176c6a2ed764592ea,0x983c8130f7d55d2f97c1,0xca82ed80ae0f004c3e42,0x2cbb02e13120bb652983,0xc605978a0bb6c1785d90,0x5d3697c16d4176e22b0b,0x784c3f21585e4130fb55,0xaa090b84e0a70fb94597,0x8557410d2a82dc55053a,0x841aab0a30261c428ba8,0x6150ef14dd5e40b2bc51,0xeb0e0596194c1c32d828,0x42a1e184c3c3118686a6,0x16297c13f57747a5f04f,0x4241be53757c5706f826],#[0x1c183757d00eafa1e0df,0x358076230d054dd6094c,0x5763308ecb609d98c0bb,0xaae9982612329bac2517,0x7a155d3397c1670987cc,0x55d3b85c26a5175d0570,0x7d84c3f75175ef02cbdd,0x4c3fb1186f6a2ebee059,0xb62d826c6302d82e13d0,0x98672a2cae55591c8ac2,0x6322cac46e0d8d1c1310,0xb0cd64e1190dc2329265,0xd0ce05a04c3b81984702,0xe0da35c1347381685f04,0xa84c1ba15856eaf08d02,0x39cd69739a1707d94597,0xd69839ad4eb35a5d66b5,0x859ad4cb35a5966b541c,0xc230d2cc6065b542cd69,0x324661250dc24709859,0x42e17e04c1cf11869867,0xc830c20f75841c1707f,0x16c1503181a06b014156,0x2546373a633094185ce8,0x983aa5f0548ce06904c,0x42752c64c2e13f05c26b,0x56c67aa58cf4cb293a56,0xc78e618f4cb29ea5643d,0x2594ad2aa15aa763d52e,0x4ad53295a9652a770a56,0x4c295a8852b54ea56a5d,0x1fa96535570a56aa14ad],#[0x56528730a7e2594fd2aa,0x294cec5295d8a53b294a,0xcca5a9594b534314a586,0x5a9614b533a96a5752d4,0x5d4bd5c197a8832f4d0a,0xc3cbb1839863734ea5e6,0xc29d3b8532730c70ee18,0xca9645352c892a55121c,0x824b32ca8e959119cc22,0x7308ba69952ccb2a5af,0xc976a552f1cc22b3b845,0x5e5daecdb2dd9965bb4a,0x970bcbadf9a86bb330d7,0x1cc2717974d8730995e5,0x2bca564795506f2a60de,0x8b657934caf22595e4cb,0x57b12caf66dd5e4c3abc,0x730908ee1201cc2417b7,0xb9de5db34cb2e6a564cc,0x65959d2b2337965d2f2e,0x5b52b2363b8666f2ecce,0x341b1a58362730cda659,0xb29983653106c8ee0d95,0xb83687306e26e0d94d41,0x8e730b2cee1641cc1b73,0x30730ee0e49cc1ca3b83,0x4de5d899cc2533b84a27,0xd94ad2b21579763c730c,0xb52c19479753ef2ea562,0xc2173b832e730e4a960c,0x779762ef6ea5de5d4bd2,0x872e730e5de61cbbdbb1],#[0x6f2ec6e65d4d9dc3977a,0xea80e60d01cc39b7b763,0x1e9d8c1cc3a07b7540f2,0x18c3d4318798630f10c6,0xd3c219af8232f2ec71ee,0x2997a8532f30a65e214c,0xab83af530b5aa596b3dc,0x202f30b69e61ebbcbb57,0xf30819e61c0bcbb01af8,0x891e5d924cb2a43b8448,0xa595255c224a9844952e,0x91bcbb23ab8549530a92,0xdc2a5a5744a770694e61,0xa579874af6ec95e5d929,0x9835a770e95ea1d29cc3,0x4f32ca9ce61d69cc2ad3,0x70898ee193bd3b277976,0x9a6e0d34cc1a679764c7,0xe15455c1a89b844d3308,0x43dc228798450f706a26,0xb2dea984bd52c979ee15,0xfaf82be730d76a616f54,0x75c8f30f7de5daf9dc2d,0x770981ed9709cc2e479,0x9b1e61713cc2627976c,0x5e5d38bcbb6c9965d877,0xdb6ccb2ed3b83db5f05b,0x4cc1ee3983e4f30fb5e5,0x3887984e0f307c266137,0x7b75794ae8f0ee0de3cc,0x778f30ef0ee19e1cc33c,0x32cb0cee1de3d43bc398],#[0x4fce61e19cc3439b7587,0xe1d5fc5b2bf89657f5f0,0x5fbdbabf7a757ef2eafd,0xd3ac579758b12cb14ee1,0xc57a658af2cb14e6162b,0xb847c7706f9ea162bcc2,0x7d1706fa260df3dbabe3,0x10efa2dd5f45c23e8984,0x1aae0e01cc23b8975891,0x61b354c1e679848c7309,0x51dc2687987cc770d98e,0xbaf78965ee7707dde613,0xa8984f11307e1e61fbbc,0x766cf4eccde613d3cc1f,0x96702d296158d2b2b179,0x6d1e20da53c234af826,0xa660f9bdc1b47a8368f3,0xd643cbac8a78490f307d,0x53c249b38192f2eb2de9,0x1fd7983faf50bf1e617e,0x7974a2730941e5d283d4,0x4a6f2e94e6e168bdba51,0xf30950e612a3cba547b7,0x754ee0e957c152b381a4,0xe6135bd41d57983aa730,0xd009c0007985fcf309f9,0x3a00bd027008201b404,0x6d018505a414a04a810a,0x426008fc21c07d41d00,0xc3190c102ea0b0829d0a,0x3cc0edc3a30e103650ce,0x7c118843f10984050fc4],#[0x814184f1135c4b612444,0x16a858a15d455314f852,0x9b46471898601177c5bf,0xec71f1c186ed1b246971,0xc7c61e947901df075e1c,0x89421b885620d88071f9,0x4d248c90c239c8c722a0,0x527d89d326b0986259c9,0x2a8ca8129b8a4c28d0a1,0xd64b402c70b002b70ac4,0xd0c0d2f98bbe2e58b722,0xccdc32ecc9a31c8c5630,0xdbb3650d6d3538d2f340,0x863980e4f38a0e04377c,0x13cc4f183be0ed13a98e,0x3f38fb53e70f833d88f5,0x2350724149037405cff6,0x6d10743b90d543050a14,0x51ad464116d457113f44,0x267494523348491ee473,0x384c492ea4b192a149f1,0xe4f713b74e6d37f4d7d3,0x5255474515943550553f,0x56553254414e853454b3,0x495ea57295b456615795,0xd6db5ad969159b163958,0x79c5de97695d357225bf,0x5460e58155fe97d85ef5,0x463e98de630d8a261e98,0x66cd9a065fd95e64f591,0x9c9a5568eda1567c19cd,0x45aeb6b29ab66a65a866],#[0x5ba56de1b586d09b266c,0xc877189c3a7051bf46f3,0x4c7471d0773c9ccc72b1,0x477f9dd876d1d8f75c5d,0x7af1e9c79dde5078e9e2,0xe3df787d35f297c09ee3,0x660368039fea7f51fb67,0x212783ea0d5829a08381,0x202879e1c5867e17a853,0xb08a6227d898e23e885e,0x88d4a32a8c1e2e48b222,0x8fda3d98f0e39e8e3637,0x2a249a91ee45b910241d,0xce51c94324ef93664c49,0x65a6963a57b959a54b94,0x650988a60797c65d8970,0xd59b0e6b49a7e68599ae,0xd9ce27279c1e6f89b926,0x9f2e7b29e727829dba75,0x16e84ba0e2820a0267f0,0x5e8c7a2c68a1a232870a,0xe948a4b6912a4028eea3,0x9c0a6ba993a5fe96ba55,0x53a8e6a1da8129eba752,0x4ab72abdaa96a8aa9d6a,0xade6b5cad02b30ac4eaf,0x1abebaf4abbaaea2b91,0x4ac77b16ec49b0e2c29b,0x6d08b3cacd3b312ca9b2,0xdbbb676d8cb596d3eb4a,0x65b922e34b87edf1b766,0xbbb56ebfba8ae8eb9d2e],#[0xbdd2f62bd42f35bc62ef,0xe92f9cbe52f8cbe12f7c,0x52fccbf12fbcbed2facb,0x2ffcbfd2fecbf92fdcbf,0x2cc09301cc05300cc01,0x5cc15304cc11303cc0d3,0xcc21307cc1d306cc1930,0xc2d30acc29309cc25308,0x3930dcc3530ccc3130bc,0x5310cc4130fcc3d30ecc,0x313cc4d312cc49311cc4,0x16cc59315cc55314cc51,0x9cc65318cc61317cc5d3,0xcc7131bcc6d31acc6931,0xc7d31ecc7931dcc7531c,0x89321cc85320cc8131fc,0x5324cc91323cc8d322cc,0x327cc9d326cc99325cc9,0x2acca9329cca5328cca1,0xdccb532cccb132bccad3,0xccc132fccbd32eccb932,0xccd332ccc9331ccc5330,0xd9335ccd5334ccd1333c,0x5338cce1337ccdd336cc,0x33bcced33acce9339cce,0x3eccf933dccf533cccf1,0x1cd05340cd0133fccfd3,0xcd11343cd0d342cd0934,0xd1d346cd19345cd15344,0x29349cd25348cd21347c,0x534ccd3134bcd2d34acd,0x34fcd3d34ecd3934dcd3],#[0x52cd49351cd45350cd41,0x5cd55354cd51353cd4d3,0xcd61357cd5d356cd5935,0xd6d35acd69359cd65358,0x7935dcd7535ccd7135bc,0x5360cd8135fcd7d35ecd,0x363cd8d362cd89361cd8,0x718100e150fe2e1e0d91,0x50484166344a32526c31,0x685036586c4116206054,0x26690e3c564a26107244,0x92b838e881423a597892,0x8a160508702432a09c22,0x5284e12a48ca60b27130,0xc99f4840132e7e900a26,0x257d80c14c060b9e9004,0x5261ff8808508c1fdc03,0xfe42d12bd80ad90fcc80,0x2052fdc060a6e7008947,0x2469e80b443f91ce00,0xd00345c2bf280a8ca273,0x7d4eb47643fac02936c7,0xd1b2ee60048c9f852c,0x4e603057d80c147fc80,0x500f3cd70003239fb003,0x310182bd7628077aec,0x20124060a3fe60034511,0x9ffb204041c0e021e2b0,0x7fcc0268a404067c8101,0xb86087902039fe000c98,0x900c18620067fec8141d,0xe38201cc060affd90803],#[0x413d7a80132181015f,0xf9800d14bef20064f7e4,0xfc71280a8c3fc484e228,0x380064c07ff60680c246,0xf0c033b00c19d8060d7f,0x4df801111ffb204042b,0x609afc80064cc0305783,0x74001a43f3d0283df900,0x15982018fd80109a7be8,0xf900325403055ff24009,0x6ee3800832c7e001b25,0xe4080fbff13004233218,0x465bde50151afc801929,0xa01cd9ee02132dfa842c,0x261902077afc0a0cf5e8,0x4f800068a00c14fcc803,0x3267803063f600193,0x63f300042775e0306bff,0xffc001098f8060c7c030,0x563ec2b11a563ec2551a,0x4b1f68588c963ed0551a,0xd1dfb80c14ff500326,0xfd0203c7e400c9b289cc,0x280002b35f3f20042779,0x8d77808c9aef0019337e,0x932d7e0005465afc0006,0x3263f5f002139fdf001,0x721820fe40003463fbe0,0x10a2ff200894ff900082,0x3061fc800068d7f8e700,0x8fff0080cf803067efc0,0x67c01831e7000c98860],#[0x289cc0211db8060cdc03,0x403bd6f02039eb80109f,0x8ff00c14f7e008956d0,0x60ce86097e80084ce86,0x9801933a2023e00c19b8,0xc0064c44047ec18039fd,0xf57a0504effc1805bdf,0x8141effc8010995fbc50,0x182b4060b7f00192aff6,0xfcba0504e6e7d0052730,0xb289cc00d1efcbc0a09a,0x31fbf2020275e78000d1,0xef018297f02831ef0019,0x127d000345bfb301813b,0x7fb40a0e77c0064cfd08,0x64abfda2807bf800c95,0x6477e900879801929e60,0x209cdfd00326ca27300,0xae0064d75c0604e7f794,0xf780c19a03057ce0306b,0x85ed0151a785ec21519b,0x90032618fe350e01090b,0xfe000c9a3ff80064c7df,0x6f3e0019307fc801931f,0x6083fc080c7f03a0040a,0xf73c003262f2f010990,0xf700c1a7c00034573204,0x3463f4060c7fe80064c,0xc967f34000d1a61730,0xc19f681019ec0303979f,0x60064d38f10004477680,0x53cf001931f9800c98f6],#[0x57ffb0060efd01828030,0x2f7391044cbb3fa0944,0x6015d0811bf4060cdd8d,0xe00609900c15f64500e0,0xc15b860930b9802231f,0x6483be00326700c15f78,0x4f7f30807050b8ec3800,0x2277f9e04063f866008,0xc9ace4f000ca2ce4f8,0xde0306bf9e001935fcf0,0x182bd0c137bfa423456f,0xa004265ffde900044760,0x43eb801229fa0064a7ff,0x186fa1003461f8a00345,0x7381014e04051be8404d,0x75fd0801a29ff250032,0x5a2615f9404467f8e0d,0xf20028b857e50211b7f2,0x38e0806dff8420308d38,0x3053f400c94ff928019,0xbcb5004194ffd001099c,0xf54ba8002cdab5c01117,0x5e51de00119f56b801a2,0xae33f40211f60fa00a8c,0xc21fd00b47d83e802234,0xd1e0411b2ec1f4011197,0xf0c10f381120fe80068b,0xe11fd011143e50001b29,0x57a03053ce0448cf8182,0xe7c003264fc29635e030,0x7bb78028996ff2001935,0x188408f43048b7820899],#[0xf1c100ee0402cf22000d,0x7dae60068b867ad0a119,0xf0019337ef01833d8060,0x847754236f26163a888d,0xce54433622a4f6c31876,0x8193b209722a221f5a11,0xaf849730d0914d510c78,0xd722a2252b2483554430,0x21ceb62441fad7201091,0x1622b5c11d9668483a5a,0xc9297221f103ac451a31,0x84bd1025846bb115e486,0xe951241f1650cad08e64,0x234435e20681a30f1510,0x1117103baf423836849a,0x54d823bc3b924b5a119b,0x8973221eda11a7247368,0x3cc2899b5858eba62ae9,0x87d3107d3167d311a225,0x9443ef262ac98b32d0b1,0x1ea8c79cc4631d4a21ed,0xe904bd1520a2c6502c6d,0xcba8c8b8a8863f7850c1,0xb12269fb7444be312368,0x8d18443fa34248e225f0,0x9172423c72462328873,0x2115380a31a81d10cb1d,0xa2464c53b422e453d0a1,0x28678c48e3e6231a1d4e,0x55890fd2a11296225fcc,0x2c2194eb046b67a5945a,0x4b67220e919602ca1d31],#[0xe4d70483ad60a25e4886,0xca62329118fd68e04848,0x8a30e9633e04b1cd4446,0x828b70c91af9519103c5,0xbf0c7446f930b1eff592,0x9390963425f89286]]
set_option maxRecDepth 32000 in
def g253H8 := limbs80 #[#[0x212080510330c080000,0x2071100030f0a010014,0x710090c071206000e00,0x4041200001803000909,0xa2a00130511020000,0x20a032d040d250000,0x1c001e00020600560000,0xe000a16162408180f02,0x400091a131811091100,0x20804082f2c1a012b01,0xe040602113608003d,0x5095a0d1104000f0a20,0x1ea92b00130331000301,0xf17010701302502030f,0x46c242d1308002806,0x35496223d46d735b68f9,0x259a6410005bc97715b8,0x448440e3d91717b0f7cc,0x918a80004b05b7000,0xc40498c0005b25d70ce0,0x97f5cc8d4219c425c451,0x50d1cea3419f000,0x40008ae000582000c640,0x52ee27d47d878b5993cf,0xea000e36000000125875,0x9e60fdd140c96004764,0x1275a20c155d09d00003,0x25a0d818c41df923f059,0x4e0454956c5a0c60e310,0x84887db400000024bd4,0x2bc260004aac90e39000,0x2c5ac3ccf84544b4d012],#[0x53b49b0009ca541935a0,0x4a0004f252c0009715dd,0x74c487d416df0d56000a,0x534dad8f54c7164dd687,0xde04b50bd97df2cbd023,0x456d00008e92a40d0004,0xce781a92f8cdde0ddc03,0x3a5cf000d8614c94e980,0xa857c565a45fc1ac000a,0x9df9eb8e646611196,0x4603f17c000409000000,0xbcdbe1b910dfb1540002,0x8518ad1ef0004d8a05cc,0x12d90d1b5ed6169b9833,0x99857041f159dd288a5,0x513ca75f313dd9e00000,0x17a4c85fce10000dd98f,0x304600009c1390004ab8,0x10ec1492415ed1ac5bcd,0x44f96800089e0000ee,0x848d49492be3207b0000,0x9cb0000005835e99a,0x3a8da9e48ec0d5000121,0x74e99bf13ea339e28d11,0xd960ff6376294801db0b,0xbac47cdf572249dae618,0xf0009f18eb0fc000537d,0xcd211500089314a55,0x6564dcba000000625000,0xf00096100010f4295885,0x41ba4000006f8bb5b80e,0xb3427da3d0893f57554f],#[0xd01193c5fa8858f103a0,0x21700006546ae3b5da03,0x2a55c470000608169000,0x9760d60cfa,0x128c3b0dcc38e1052200,0x4d1a905089a5f50e3daf,0xe21c5260005fecb84b68,0xc7e44c0008bc60f14097,0x6f591d79da1439a06000,0x24a09858360e5000c199,0x953000507dd181000009,0xe800040f820000e47994,0xde20ce406100000b067c,0xc1e449c811c1578d6219,0xa60120d7844613421215,0x30008b1cccc2c00084e5,0xdbb95189f04a0008f,0xd3d1f1e120e1484c8479,0x346e8370005571c04325,0x9ff4a213623c1c700000,0x7120c9508b9d180a1cd0,0xade3000c8319b0a598b8,0x60a8680004c340,0x214c5453df6882469000,0x6d6e8078d98f61311d0e,0x21e1168224fa9000ed90,0x244d92dd90c088f000,0x54b00011dd431e70000,0xd958ac963e2cdbe00,0x8900092387a9c29d4201,0x18457d5ea0050001428,0xc089b116b21400000],#[0x9c5fd801a1d09913361f,0x28431de9f447498a0009,0x24000472cbee0942dc6,0xf85c888b47c8e05c50bf,0xb0a6dab8a4000d5aa43d,0xe2ea12d6722d5a5a24e0,0x352229609ee000000909,0x8c2b23006d00045c81c6,0x98100042f1a717a63,0xc08c8a3145db5974000,0xd6485204fe166c065b39,0x23e132d0307f9aa0fb1b,0x19904088cca0311ec42a,0x59cde260000000002075,0x102d554155d800000085,0x529589498d5241d000,0x58b2000000000d58a450,0xde80000009f749,0xf0203000000000a11486,0xadd545281300006b4020,0x11ec73428d4d00000050,0x5c38e2d2d5e5,0x8dc602e000d0500045e0,0x9c921a22880e85d24287,0x8d93000c0004455384a9,0x69b0cafd99c6303e18ed,0x497000e2f000cc,0x58000]]
set_option maxRecDepth 32000 in
def g253D9 := limbs80 #[#[0x591635515350c6518c53,0xd8f54d4e6598e5390d65,0xfafb7bbbdbebf3fd9764,0xb8a7fffbfbfbfbfbfbfd,0x8b901571032e0045c92a,0x2cb804276002ec025d00,0x422ba849740a2e4155c4,0xc44cb8093723a2e4e19d,0x5d0473988d73122e4255,0xb98c76b18ef531d8a632,0x37dd46eba8e9641d2a83,0xa9b58d37a9a5f761baec,0xec075d012aa01d764bae,0xaca47dd0973192d6323a,0x5ac6a7dd88ebb1266524,0x53aeaa75d153aa2a5545,0x40baecd9595aeba35d76,0x65342ca67dd0ceba85d7,0xd765baeab75d16fba9a3,0x5f732baeaf8595eeba3d,0x15d762ccca59594b4b21,0x91dd7674acae75cdcfbb,0xbac1d7383eea77dccf9b,0xfba21f7343ae8275cc4e,0x2eb9c5d7663ae8c75cd8,0xc7ab18f7531eaa6375d2,0x947b328f5651e8ca3dd8,0x9d87abb0f6751eaea3dd,0xdd901ab2037654eaca9d,0x4d5909aaa1376326ac64,0xc4dd949ab29357426ec8,0xc8ad5915aaa2b67626ae],#[0xec6dd58dbbb2ab56556e,0x6aa86d5503bb2375646e,0x36ee86d5d0dab21b7543,0x536aea6d1d4db329b565,0x655eac8bd5517bba9b67,0x6732eae65dd51faaa3f5,0xf6762eaec5dd94bab297,0x9f6653eaca7d9ccfab99,0x9a3573468e68d9d4faba,0x377446ae88ddcd1b3,0xe0c005302140ca044010,0x585d42b613408903b81a,0xa623110587983881a20c,0x7c0b6c58029e14089a84,0x75838e1b58d386603131,0x22c90dc8304001f08f18,0x89da4d625e92a0924473,0x72c395aca9c52c28b940,0x54c7661b2fd9778b785a,0xfe36f1afcd4068933519,0xf08f407803b01cf4e3c6,0x878430210d04a8033f01,0x24c92268f646b22e1130,0x89e44e226913089674a9,0x5aa9d50ca65521a89140,0xfab605a22ca560eaed56,0x20b07d7fabdb5ddae756,0xa08ce265f3275908c656,0x6d2b611aded5a6a0b485,0xdcdae4b713b82dbd2dc7,0xf7a03c61deaed2758ba3,0x92006fe27e0be81efcf5],#[0xf0866c2b2115064821c0,0x6e232d1738a8c4b221b0,0x28c934c9224431f98eb4,0xc382673316979cb4a563,0x89472386142634c187e2,0x2c48322922c63054b908,0x4252c28a42441c40c04,0xd6084453bf580827bfb2,0x18fbd8084a7fac084b3,0x21498d04030e20066782,0xc8808283fe081498ffe0,0xd040310100eec0403c7f,0x49963d0084537ee01498,0xa4d7ffc102931ffea21,0x100e68201940403dff10,0x495e0607bc3c00c99f70,0x6ee04039f405072a4300,0x213b5e02021dde0506,0x419b6050674f8181ef0f,0x77803063eb80c10d781,0x740a0d70f802133f5c04,0xc40306002021fc70203b,0x20188060c802021f0060,0x8141dbfca08082018310,0x835cf0021335f02831af,0x41fe81419bfce2007401,0xc02833bd71003bbd5040,0x101010fa68c0210060cf,0x1099fe41c043fe80807,0xcff202022f9000c98f70,0x20077fe80807be338084,0x3ef8141abbe004277fe8],#[0xc0f67c00293bef360508,0x87803067eb02831ebc1,0x7c03447f3c04075f3c06,0x28393b01094ce700c977,0x83200c19fd68141df9d0,0xe9a30087fa838087fc02,0x808a7c00426be4003267,0x6f601933fe820077fa80,0x84be758d421f3e856117,0x8060efcfb0e03b73ac02,0x3082e80610e26c08052e,0xef3ec580edf405071760,0x184bcfb0e03b2fc080,0xeb7b12845fb00464efe6,0x3077f880610bedec3a10,0xd6f404025cfe83c10742,0x610cf403087dbd01021,0x1183100c18e8460eff48,0x83badec0a10e7b62e082,0xb1d843b1901014fb7b15,0xff2b1d8437ca4048531,0x60efb7b1983badec0e1,0x6c00612a2de10029ddf8,0x98fe3008bc907c04285f,0x309338a00c2dd7d0303,0xffb0201dd6501012f960,0x1843bca07085ff60183a,0x800c26fb07c1c27737e0,0x37380564ee2fe07087e3,0x806095fe8560edf40607,0x7bf0603d97203a4ed9ed,0x41d9fe0506b1e40709de],#[0x284f79a0f80850f6ff0d,0xf84a0e65f00c26bce0f8,0xffd8100edfaa807097b7,0x421bfd503041ffb00c1c,0x13dc00a4ed3bf8a]]
set_option maxRecDepth 32000 in
def g253H9 := limbs80 #[#[0x81584140000102091182,0x20812c30ca3432812005,0x8311610511318000010,0x7002081041082005000,0x31410400030430011000,0x1c40810805451080030c,0x480c43060c241a006059,0x64104908114000c8430,0x821016c615d0e774200,0x5e1c00c0280087181001,0x550c000f0c09c20020,0x9f743510150228408d50,0x5f3c92d8d0000008fd,0xa070fbe65000cd10,0x62c15100046a077a3d00,0x4ed000cce,0xe5b38aa04805f0000000,0xd11c1955e00094e950a3,0x2478d9000000000000,0x14620000000410701670,0xe695400000013962,0x3000000000020e9a9620,0xc1e8e40cfec3dd1b0001,0x4b002f01f5f14d2cb608,0x6280c0b74a2a0d000202,0x910887000000dec8f3d,0x816a1b92197418a00,0x974b1000000000000c4b,0x57b000c1dc054c18231,0xe119d1978000ce800,0x78000000d42000000d7a,0x40002251982260000000],#[0xcac000000dffe5fc7,0xc8e000000000000,0x3313d5c20000000,0x4645d9ceb260dcc00,0x7dc38a338d7a0cdc7802,0x87e000667000da40001,0x9350009f8000a5700000,0x5f000000dd2018dc9e6b,0x4000000000938000a70d,0x216170a6000000a5,0xeb9a190500060b9d0645,0x6375e200090e0000001,0x5b400000080400,0x2f40a1f600000007d213,0x9cd00049b000d07e15a,0x54159900042500,0xef93753ac73d95616572,0x30000000000008dd0008,0x66c0000da000d3390f57,0x25258785bc2900001a,0x4bcdb88014589b552b0,0x37a1d42e00000000000,0x48b93600000000096b,0xa00045dd180001fa9130,0x5085ed40b0001e90c,0x6c5ce000ca8000524,0x8d0b563a480002008220,0x26e409a2e98ecf082,0x869ce00004e1230114,0x9dd1030320009ea4300,0xcd55f40000000b38de00,0x7c4a3cd60005bc1da8b8],#[0x955244d6244db4a7c8d9,0x5498c2c9f52fda3a5,0x4f100000000000096c,0x1532034df1f90000000,0x7c1c49e50009f200000,0xe2b87b5d50000000ee,0x20000000000000000ec0,0x5d600009500000087261,0x5b65f50000b2000,0x71a8cc8cf80000f799a0,0x188854042000000411c4,0x560000619000000000,0x8e70000009a50d00,0x1d41a200016f1bd00,0x19644f19d000180c10,0x1c654502700f1349270,0xab00,0x5dee140bee6156d000,0x3a5a000000cf51fe4e40,0xe090000000001c00008d,0x9e24900000048a851955,0x893a43c3c168d174,0x54dcc300000000055a00,0x1ac9a6628060000468,0x90008e90001df86d1fd0,0x7aa638e217e00000007,0x85855ce30f2ca59d31fb,0x543e19f00009c915d250,0xd2d000000e56031255dc,0xf5fc000000666000a71,0xc00086e000dcf12cc96a,0xccd5b4bbc2418282a9d],#[0xcda58000000c9d000,0x436067da0605000d560,0x4904b4e2995700095900,0x51000d85883dca1ada6d,0xcbd9925840008125652,0xc0300,0x4811603a0009e000062d,0xf00000000006100065e5,0xa06000920000000000d1,0x3e5e6961db185e0000a0,0x100000098602b5760001,0xd3,0x4e5000000,0x923c000a5c839446cb50,0xcd8c34813c8200061012,0xc7655c24c5af4f6c1b,0xfe620000000000005940,0x1494bc710004a,0xa796e8d42314008c5000,0xac8616a0000f94c02019,0x8cb532593100cfadb791,0x4d000e04000000946a35,0xd64de7c98000e,0x5d80c90009e418c00,0x80e270000a9000a3ac17,0x12e00000000000057f0,0x45c000e5b00,0x91126000c2000821c000,0x1abc9ae50000a1e8264,0xa0a40d189000170a4400,0x80e00018f000246000,0x20005e3d9ed4a000d0c0],#[0x5830000008ea000000db,0x43b4b924e000000,0x50a0000000000000000,0xd588bacc4dba8cf00000,0x4c0a400001ec59000,0x5d77a642088a10000000,0x85600000059b63417,0x9c97000db008f000000,0x1230fc11d000c3f5,0xc0798b63bc6b00,0x4391cc8893fd6954f000,0x5843d3c0008c6a235405,0x81526f000dae000cdc46,0x6a5bf000a5dc81000e69,0x1bb000171522a,0x452a1800084a1d753b1f,0x3200000099052a5ee000,0xc0000005b90509c810d2,0x466c99d4,0x579000000638668000,0xf000000e39000a42cff0,0x24f50622a00018100007,0x9c25324ad66d44044463,0xd00042c000000241d12d,0x947c0600045a00015,0xdb50100041c000000840,0xf0000008f44759cb0009,0x4538459910001e,0x519102000928894000,0xf4849c30494571be0000,0xdaa0000000008b,0x8990400000000004e000],#[0x60ad5e1cc75c1000000c,0xa3f00000021f64be3,0x2221a51e86f42dcae000,0x2]]
def g253D10 := limbs80 #[#[0xc63d4e5354c5390d43ff,0x465d9164d5154d8e6358,0xe25c228bc3000d966559,0x255107cb8196b44fa18,0xc38c61448a1830b6eacd,0x610400c21402021740e3,0x900203800c1d00404000,0xa0e800c200100e00030,0x7401c208020434020200,0x40800403800102500507,0x283a00]]
def g253H10 := limbs80 #[#[0x12c28034c32184002864,0xcb840025610806840121,0x165000961182001c02,0x872365f74b8c942c1412,0x520000048800cf400,0x2841849d27c000003c,0xc380000000,0xe3c00c4c0000107,0xca40058c00cc393,0xc2a0f220000000000290,0x137155153a1111e8dd3f,0xdc80000219003390026a,0x29c000001601780b71,0x34856400de54765c99,0x60400002180022c4188c,0x5cc000035f0011b00331,0x11642c5ee096d0014a,0x92528000385b80000201,0xc2686574000030c94343,0x49e332340000000,0xd01239c27b0035322b54,0x868679f0344a800e5546,0x203565326c1e38e,0x269570000000000,0x6b26368844000012d,0x4da4000009400275,0x13e356258b003609d93e,0xd075ad540000214,0x800060f515fb0d04062,0x287887258b800,0xdde4ed999e5e800,0x126dd000a6d9242000],#[0x13b003850036f00291,0x5fd2bc922fc005b,0x11d992039731f]]
def g253D11 (j : Nat) := if j=0 then 0x3104027f else 0
def g253H11 := limbs80 #[#[0x1800000,0x15000a000470000000c,0x18c000000000000,0x2e00000000000000000,0x560000001a40005e00,0x6a200000000000000000,0x8404,0x200000009a02400,0x28040]]
def g253L : Nat → Packing
  | 6 => (54,5,5,2097190,86,9,1026,g253D6)
  | 7 => (590,4,5,7209198,120,13,4156,g253D7)
  | 8 => (626,3,5,2949248,103,14,4164,g253D8)
  | 9 => (160,2,5,917522,69,13,4130,g253D9)
  | 10 => (18,1,5,65537,0,9,4108,g253D10)
  | 11 => (1,0,5,0,0,0,0,g253D11)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 13 89 5 8 6 0 g253H7
  | 8 => lookupShort 147 727 8 12 10 0 g253H8
  | 9 => lookupShort 156 1009 6 12 10 0 g253H9
  | 10 => lookupShort 40 257 5 10 8 0 g253H10
  | 11 => lookupShort 4 97 0 7 5 0 g253H11
  | _ => fun _ => none
def g253 : Forest := ⟨253,11,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_0 : CutRow g253 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_1 : CutRow g253 6 1 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+0)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_49 : CutRow g253 6 49 5 := by
  apply polarBlock (data:=fun j => g253Mark (j+48)) rfl
  decide +kernel
theorem g253B6 : CutRow g253 6 0 54 := (@joinRow g253 6 0 1 53 g253P6_0 (@joinRow g253 6 1 48 5 g253P6_1 g253P6_49))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_0 : CutRow g253 7 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_4 : CutRow g253 7 4 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_52 : CutRow g253 7 52 10 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_62 : CutRow g253 7 62 29 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_91 : CutRow g253 7 91 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+53)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_139 : CutRow g253 7 139 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+101)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_187 : CutRow g253 7 187 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+149)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_235 : CutRow g253 7 235 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+197)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_283 : CutRow g253 7 283 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+245)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_331 : CutRow g253 7 331 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+293)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_379 : CutRow g253 7 379 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+341)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_427 : CutRow g253 7 427 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+389)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_475 : CutRow g253 7 475 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+437)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_523 : CutRow g253 7 523 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+485)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_571 : CutRow g253 7 571 19 := by
  apply polarBlock (data:=fun j => g253Mark (j+533)) rfl
  decide +kernel
theorem g253B7 : CutRow g253 7 0 590 := (@joinRow g253 7 0 235 355 (@joinRow g253 7 0 62 173 (@joinRow g253 7 0 4 58 g253P7_0 (@joinRow g253 7 4 48 10 g253P7_4 g253P7_52)) (@joinRow g253 7 62 77 96 (@joinRow g253 7 62 29 48 g253P7_62 g253P7_91) (@joinRow g253 7 139 48 48 g253P7_139 g253P7_187))) (@joinRow g253 7 235 192 163 (@joinRow g253 7 235 96 96 (@joinRow g253 7 235 48 48 g253P7_235 g253P7_283) (@joinRow g253 7 331 48 48 g253P7_331 g253P7_379)) (@joinRow g253 7 427 96 67 (@joinRow g253 7 427 48 48 g253P7_427 g253P7_475) (@joinRow g253 7 523 48 19 g253P7_523 g253P7_571))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : CutRow g253 8 0 21 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_21 : CutRow g253 8 21 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_69 : CutRow g253 8 69 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_117 : CutRow g253 8 117 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_165 : CutRow g253 8 165 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_213 : CutRow g253 8 213 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_261 : CutRow g253 8 261 31 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_292 : CutRow g253 8 292 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_340 : CutRow g253 8 340 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_388 : CutRow g253 8 388 19 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_407 : CutRow g253 8 407 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+552)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_455 : CutRow g253 8 455 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+600)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_503 : CutRow g253 8 503 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+648)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_551 : CutRow g253 8 551 48 := by
  apply polarBlock (data:=fun j => g253Mark (j+696)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_599 : CutRow g253 8 599 27 := by
  apply polarBlock (data:=fun j => g253Mark (j+744)) rfl
  decide +kernel
theorem g253B8 : CutRow g253 8 0 626 := (@joinRow g253 8 0 292 334 (@joinRow g253 8 0 117 175 (@joinRow g253 8 0 21 96 g253P8_0 (@joinRow g253 8 21 48 48 g253P8_21 g253P8_69)) (@joinRow g253 8 117 96 79 (@joinRow g253 8 117 48 48 g253P8_117 g253P8_165) (@joinRow g253 8 213 48 31 g253P8_213 g253P8_261))) (@joinRow g253 8 292 163 171 (@joinRow g253 8 292 96 67 (@joinRow g253 8 292 48 48 g253P8_292 g253P8_340) (@joinRow g253 8 388 19 48 g253P8_388 g253P8_407)) (@joinRow g253 8 455 96 75 (@joinRow g253 8 455 48 48 g253P8_455 g253P8_503) (@joinRow g253 8 551 48 27 g253P8_551 g253P8_599))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : CutRow g253 9 0 22 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_22 : CutRow g253 9 22 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_70 : CutRow g253 9 70 20 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_90 : CutRow g253 9 90 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_138 : CutRow g253 9 138 22 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : CutRow g253 9 0 160 := (@joinRow g253 9 0 70 90 (@joinRow g253 9 0 22 48 g253P9_0 g253P9_22) (@joinRow g253 9 70 20 70 g253P9_70 (@joinRow g253 9 90 48 22 g253P9_90 g253P9_138)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_0 : CutRow g253 10 0 18 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : CutRow g253 10 0 18 := g253P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P11_0 : CutRow g253 11 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B11 : CutRow g253 11 0 1 := g253P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : mixedTables g253 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g253 0 0
  · exact mixedEmpty g253 1 0
  · exact mixedEmpty g253 2 0
  · exact mixedEmpty g253 3 0
  · exact mixedEmpty g253 4 0
  · exact mixedEmpty g253 5 0
  · exact g253B6
  · exact g253B7
  · exact g253B8
  · exact g253B9
  · exact g253B10
  · exact g253B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 12 := mixedLower (g:=g253) (i:=0) (hints:=21764) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 12 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe4ec548500e53f11d0,0x1fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x8464548500e12a1050,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x1f2124a33d802e6680,0xfe0007f0003f80])),(BitVec.ofNat 152 (word80 [0xdf2124813c802c2280,0x60c183060c183060c183]))),((BitVec.ofNat 152 (word80 [0xb9686c544f241eac0,0x7f000000001fc000])),(BitVec.ofNat 152 (word80 [0xb9606c504b241e2c2,0x64c993264c993264c993]))),((BitVec.ofNat 152 (word80 [0xe40b175eac0f052aa0,0x3f800003f80000007f])),(BitVec.ofNat 152 (word80 [0xb015aac06052a81,0x42850a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x20af92a4bf84a1b00,0x1fc000000000001fff80])),(BitVec.ofNat 152 (word80 [0x8d92a4348021905,0x8b162c58b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x1d50ac8d518b0552f,0xe000000003ffffe00000])),(BitVec.ofNat 152 (word80 [0x900a004118904526,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x18304911220280a05f,0xfffffffffc0000000000])),(BitVec.ofNat 152 (word80 [8,0x10204081020408102040]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(4,0,250,0,11)]
def g254A : List (List Nat) := [[],[65]]
def g254D11 (j : Nat) := if j=0 then 0xff else 0
def g254L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g254D11)
  | _ => emptyPacking
def g254I (_ _ : Nat) : Option (Nat × Nat) := none
def g254 : Forest := ⟨254,11,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P11_0 : CutRow g254 11 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B11 : CutRow g254 11 0 1 := g254P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : mixedTables g254 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g254 0 0
  · exact mixedEmpty g254 1 0
  · exact mixedEmpty g254 2 0
  · exact mixedEmpty g254 3 0
  · exact mixedEmpty g254 4 0
  · exact mixedEmpty g254 5 0
  · exact mixedEmpty g254 6 0
  · exact mixedEmpty g254 7 0
  · exact mixedEmpty g254 8 0
  · exact mixedEmpty g254 9 0
  · exact mixedEmpty g254 10 0
  · exact g254B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 12 := mixedLower (g:=g254) (i:=0) (hints:=287397184) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 12 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
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
theorem g255P6_0 : CutRow g255 6 0 4 := by
  apply polarBlock (data:=fun j => g255Mark (j+0)) rfl
  decide +kernel
theorem g255B6 : CutRow g255 6 0 4 := g255P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : CutRow g255 7 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_2 : CutRow g255 7 2 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+4)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_50 : CutRow g255 7 50 6 := by
  apply polarBlock (data:=fun j => g255Mark (j+52)) rfl
  decide +kernel
theorem g255B7 : CutRow g255 7 0 56 := (@joinRow g255 7 0 2 54 g255P7_0 (@joinRow g255 7 2 48 6 g255P7_2 g255P7_50))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : CutRow g255 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_1 : CutRow g255 8 1 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_49 : CutRow g255 8 49 25 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_74 : CutRow g255 8 74 18 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_92 : CutRow g255 8 92 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+58)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_140 : CutRow g255 8 140 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+106)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_188 : CutRow g255 8 188 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+154)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_236 : CutRow g255 8 236 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+202)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_284 : CutRow g255 8 284 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+250)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_332 : CutRow g255 8 332 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+298)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_380 : CutRow g255 8 380 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+346)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_428 : CutRow g255 8 428 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+394)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_476 : CutRow g255 8 476 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+442)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_524 : CutRow g255 8 524 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+490)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_572 : CutRow g255 8 572 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+538)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_620 : CutRow g255 8 620 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+586)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_668 : CutRow g255 8 668 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+634)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_716 : CutRow g255 8 716 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+682)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_764 : CutRow g255 8 764 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+730)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_812 : CutRow g255 8 812 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+778)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_860 : CutRow g255 8 860 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+826)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_908 : CutRow g255 8 908 5 := by
  apply polarBlock (data:=fun j => g255Mark (j+874)) rfl
  decide +kernel
theorem g255B8 : CutRow g255 8 0 913 := (@joinRow g255 8 0 428 485 (@joinRow g255 8 0 140 288 (@joinRow g255 8 0 49 91 (@joinRow g255 8 0 1 48 g255P8_0 g255P8_1) (@joinRow g255 8 49 25 66 g255P8_49 (@joinRow g255 8 74 18 48 g255P8_74 g255P8_92))) (@joinRow g255 8 140 144 144 (@joinRow g255 8 140 48 96 g255P8_140 (@joinRow g255 8 188 48 48 g255P8_188 g255P8_236)) (@joinRow g255 8 284 48 96 g255P8_284 (@joinRow g255 8 332 48 48 g255P8_332 g255P8_380)))) (@joinRow g255 8 428 240 245 (@joinRow g255 8 428 96 144 (@joinRow g255 8 428 48 48 g255P8_428 g255P8_476) (@joinRow g255 8 524 48 96 g255P8_524 (@joinRow g255 8 572 48 48 g255P8_572 g255P8_620))) (@joinRow g255 8 668 144 101 (@joinRow g255 8 668 48 96 g255P8_668 (@joinRow g255 8 716 48 48 g255P8_716 g255P8_764)) (@joinRow g255 8 812 48 53 g255P8_812 (@joinRow g255 8 860 48 5 g255P8_860 g255P8_908)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : CutRow g255 9 0 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_48 : CutRow g255 9 48 8 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_56 : CutRow g255 9 56 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_104 : CutRow g255 9 104 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_152 : CutRow g255 9 152 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_200 : CutRow g255 9 200 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_248 : CutRow g255 9 248 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
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
theorem g255P9_344 : CutRow g255 9 344 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_392 : CutRow g255 9 392 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_440 : CutRow g255 9 440 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_488 : CutRow g255 9 488 45 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_533 : CutRow g255 9 533 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_581 : CutRow g255 9 581 23 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_604 : CutRow g255 9 604 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+879)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_652 : CutRow g255 9 652 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+927)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_700 : CutRow g255 9 700 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+975)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_748 : CutRow g255 9 748 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1023)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_796 : CutRow g255 9 796 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1071)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_844 : CutRow g255 9 844 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1119)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_892 : CutRow g255 9 892 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1167)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_940 : CutRow g255 9 940 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1215)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_988 : CutRow g255 9 988 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1263)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1036 : CutRow g255 9 1036 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1311)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1084 : CutRow g255 9 1084 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1359)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1132 : CutRow g255 9 1132 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1407)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1180 : CutRow g255 9 1180 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1455)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1228 : CutRow g255 9 1228 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1503)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1276 : CutRow g255 9 1276 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1551)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1324 : CutRow g255 9 1324 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1599)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1372 : CutRow g255 9 1372 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1647)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1420 : CutRow g255 9 1420 19 := by
  apply polarBlock (data:=fun j => g255Mark (j+1695)) rfl
  decide +kernel
theorem g255B9 : CutRow g255 9 0 1439 := (@joinRow g255 9 0 700 739 (@joinRow g255 9 0 344 356 (@joinRow g255 9 0 152 192 (@joinRow g255 9 0 56 96 (@joinRow g255 9 0 48 8 g255P9_0 g255P9_48) (@joinRow g255 9 56 48 48 g255P9_56 g255P9_104)) (@joinRow g255 9 152 96 96 (@joinRow g255 9 152 48 48 g255P9_152 g255P9_200) (@joinRow g255 9 248 48 48 g255P9_248 g255P9_296))) (@joinRow g255 9 344 189 167 (@joinRow g255 9 344 96 93 (@joinRow g255 9 344 48 48 g255P9_344 g255P9_392) (@joinRow g255 9 440 48 45 g255P9_440 g255P9_488)) (@joinRow g255 9 533 71 96 (@joinRow g255 9 533 48 23 g255P9_533 g255P9_581) (@joinRow g255 9 604 48 48 g255P9_604 g255P9_652)))) (@joinRow g255 9 700 384 355 (@joinRow g255 9 700 192 192 (@joinRow g255 9 700 96 96 (@joinRow g255 9 700 48 48 g255P9_700 g255P9_748) (@joinRow g255 9 796 48 48 g255P9_796 g255P9_844)) (@joinRow g255 9 892 96 96 (@joinRow g255 9 892 48 48 g255P9_892 g255P9_940) (@joinRow g255 9 988 48 48 g255P9_988 g255P9_1036))) (@joinRow g255 9 1084 192 163 (@joinRow g255 9 1084 96 96 (@joinRow g255 9 1084 48 48 g255P9_1084 g255P9_1132) (@joinRow g255 9 1180 48 48 g255P9_1180 g255P9_1228)) (@joinRow g255 9 1276 96 67 (@joinRow g255 9 1276 48 48 g255P9_1276 g255P9_1324) (@joinRow g255 9 1372 48 19 g255P9_1372 g255P9_1420)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : CutRow g255 10 0 9 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_9 : CutRow g255 10 9 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_57 : CutRow g255 10 57 48 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_153 : CutRow g255 10 153 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_201 : CutRow g255 10 201 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_249 : CutRow g255 10 249 44 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_293 : CutRow g255 10 293 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_341 : CutRow g255 10 341 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_389 : CutRow g255 10 389 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_437 : CutRow g255 10 437 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_485 : CutRow g255 10 485 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_533 : CutRow g255 10 533 37 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_570 : CutRow g255 10 570 21 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_591 : CutRow g255 10 591 48 := by
  apply polarBlock (data:=fun j => g255Mark (j+1714)) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_639 : CutRow g255 10 639 5 := by
  apply polarBlock (data:=fun j => g255Mark (j+1762)) rfl
  decide +kernel
theorem g255B10 : CutRow g255 10 0 644 := (@joinRow g255 10 0 341 303 (@joinRow g255 10 0 153 188 (@joinRow g255 10 0 57 96 (@joinRow g255 10 0 9 48 g255P10_0 g255P10_9) (@joinRow g255 10 57 48 48 g255P10_57 g255P10_105)) (@joinRow g255 10 153 96 92 (@joinRow g255 10 153 48 48 g255P10_153 g255P10_201) (@joinRow g255 10 249 44 48 g255P10_249 g255P10_293))) (@joinRow g255 10 341 192 111 (@joinRow g255 10 341 96 96 (@joinRow g255 10 341 48 48 g255P10_341 g255P10_389) (@joinRow g255 10 437 48 48 g255P10_437 g255P10_485)) (@joinRow g255 10 533 58 53 (@joinRow g255 10 533 37 21 g255P10_533 g255P10_570) (@joinRow g255 10 591 48 5 g255P10_591 g255P10_639))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : CutRow g255 11 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_7 : CutRow g255 11 7 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_55 : CutRow g255 11 55 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_103 : CutRow g255 11 103 10 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : CutRow g255 11 0 113 := (@joinRow g255 11 0 55 58 (@joinRow g255 11 0 7 48 g255P11_0 g255P11_7) (@joinRow g255 11 55 48 10 g255P11_55 g255P11_103))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : CutRow g255 12 0 13 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : CutRow g255 12 0 13 := g255P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : CutRow g255 13 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : CutRow g255 13 0 1 := g255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : mixedTables g255 13 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g255 0 0
  · exact mixedEmpty g255 1 0
  · exact mixedEmpty g255 2 0
  · exact mixedEmpty g255 3 0
  · exact mixedEmpty g255 4 0
  · exact mixedEmpty g255 5 0
  · exact g255B6
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
  exact mixedRoot (g:=g255) (top:=13) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_35106

open PEqualNP.Outside.L_meta_35106 in
theorem PEqualNP.Outside.L_meta_35106 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
