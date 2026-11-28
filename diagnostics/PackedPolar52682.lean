import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52682.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52682
open PEqualNP.CircuitLowerBounds
private def w80 (xs : List Nat) : Nat :=
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

def inputs : List Sig := [(BitVec.ofNat 512 (w80 [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (w80 [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc])),(BitVec.ofNat 512 (w80 [0xf0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0])),(BitVec.ofNat 512 (w80 [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00])),(BitVec.ofNat 512 (w80 [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000])),(BitVec.ofNat 512 (w80 [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (w80 [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,0xffff,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000])),(BitVec.ofNat 512 (w80 [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,0xffff,0xffffffffffffffffffff,0xffffffff000000000000,0])),(BitVec.ofNat 512 (w80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0,0,0]))]
def graph : Sig := (BitVec.ofNat 512 (w80 [0xffffffff,0xffffffffffffffffffff,0xfffefffffffffffefffc,0xfffeffeefefaee00ffff,0xffffffffffffffffffff,0xfffffffefffffffffffe,0xfffcfffeffeefefaee00]))
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
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  | 0 => (w80 [0x1000000000000,0x10000000000000001,0x10000,0x100000000,0x1000000000000,0x10000000000000001])
  | 1 => (w80 [0x10000000000000000,0x10000,0,0x1000000000000,1])
  | 2 => (w80 [1,0x10000,0,0,0x10000000000000001])
  | 3 => (w80 [0x10000,0,0,1])
  | 4 => (w80 [0x100000000,0x1000000000000,0x10000000000000001])
  | 5 => (w80 [0x1000000000000,1])
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


structure QuotientSpec where
  a : Nat
  b : Nat
  rev : Bool
  z : Nat
  o : Nat
  extra : Nat
  fl : Nat
  sw : List Nat
  single : Nat

def quotSpec : Nat → QuotientSpec
  | 0 => ⟨0,7,true,0,0,0,1,[48, 65, 80, 98, 118],3⟩
  | 1 => ⟨0,7,true,8,0,0,1,[64, 80, 98, 118],1⟩
  | 2 => ⟨3,7,true,1,0,0,8,[96, 82, 48, 116],1⟩
  | 3 => ⟨2,7,true,64,0,0,4,[64, 80, 98, 115],1⟩
  | 4 => ⟨0,6,false,8,0,0,0,[48, 82, 100],0⟩
  | 5 => ⟨6,7,true,4,0,0,64,[48, 80, 100, 118],1⟩
  | 6 => ⟨0,7,true,24,0,0,1,[80, 98, 118],0⟩
  | 7 => ⟨3,4,false,1,0,0,0,[50, 83],0⟩
  | 8 => ⟨0,2,false,16,0,0,0,[48, 83],0⟩
  | 9 => ⟨4,7,true,5,0,0,16,[83, 100, 118],0⟩
  | 10 => ⟨0,7,true,16,0,0,1,[48, 80, 98, 118],1⟩
  | 11 => ⟨4,7,true,4,0,0,16,[83, 100, 118],1⟩
  | 12 => ⟨4,7,true,1,0,0,16,[32, 83, 100, 118],1⟩
  | 13 => ⟨0,2,false,144,0,0,0,[80, 99, 118],0⟩
  | 14 => ⟨3,7,true,65,0,0,8,[82, 99, 116],0⟩
  | 15 => ⟨4,6,false,4,0,0,0,[48, 83, 100],0⟩
  | 16 => ⟨2,7,true,80,0,0,4,[80, 98, 115],0⟩
  | 17 => ⟨2,7,true,0,0,0,4,[64, 97, 80, 33, 115],3⟩
  | 18 => ⟨0,6,false,136,0,0,0,[80, 98, 116],0⟩
  | 19 => ⟨0,6,false,0,0,0,0,[96, 50, 84],0⟩
  | 20 => ⟨3,7,true,0,0,0,8,[97, 82, 49, 116],3⟩
  | 21 => ⟨0,2,false,0,0,0,0,[96, 66, 101],0⟩
  | 22 => ⟨0,2,false,128,0,0,0,[112, 83],0⟩
  | 23 => ⟨3,4,false,129,0,0,0,[82, 99, 118],0⟩
  | 24 => ⟨4,7,true,0,0,0,16,[33, 83, 100, 118],3⟩
  | 25 => ⟨2,3,false,64,0,0,0,[48, 82, 100],0⟩
  | 26 => ⟨0,6,false,12,0,0,0,[80, 100],0⟩
  | 27 => ⟨0,6,false,128,0,0,0,[112, 82, 67, 100],0⟩
  | 28 => ⟨3,4,false,5,0,0,0,[83],0⟩
  | 29 => ⟨3,6,false,1,0,0,0,[48, 82, 100],1⟩
  | 30 => ⟨2,3,false,65,0,0,0,[82, 100],0⟩
  | 31 => ⟨2,3,false,192,0,0,0,[80, 98, 116],0⟩
  | 32 => ⟨3,7,true,64,0,0,8,[82, 99, 116],1⟩
  | 33 => ⟨6,7,true,0,0,0,64,[32, 49, 80, 100, 118],3⟩
  | 34 => ⟨6,7,true,8,0,0,64,[32, 80, 100, 118],1⟩
  | 35 => ⟨0,2,false,24,0,0,0,[80],0⟩
  | 36 => ⟨0,2,false,80,0,0,0,[80, 99],0⟩
  | 37 => ⟨3,7,true,0,0,0,8,[82, 99, 116],15⟩
  | 38 => ⟨2,6,true,144,0,0,4,[32, 49, 82, 99, 117],0⟩
  | 39 => ⟨6,7,true,4,0,0,64,[16, 48, 82, 32, 100, 118],7⟩
  | 40 => ⟨3,7,true,32,0,0,8,[98, 82, 83, 116],7⟩
  | 41 => ⟨2,3,false,160,0,0,0,[114],0⟩
  | 42 => ⟨3,7,true,64,0,0,8,[82, 99, 116],7⟩
  | 43 => ⟨2,7,true,64,0,0,4,[65, 97, 50, 83, 117],2⟩
  | 44 => ⟨3,7,true,2,0,0,8,[81, 98, 33, 49, 116],7⟩
  | 45 => ⟨6,7,true,8,0,0,64,[16, 32, 80, 100, 118],7⟩
  | 46 => ⟨6,7,true,0,0,0,64,[16, 32, 48, 80, 100, 118],15⟩
  | 47 => ⟨5,7,true,8,0,0,32,[98, 82, 84, 117],7⟩
  | 48 => ⟨2,6,true,16,0,0,4,[112, 32, 49, 82, 99],1⟩
  | 49 => ⟨6,7,true,32,0,0,64,[16, 32, 48, 80, 100, 118],7⟩
  | 50 => ⟨2,5,false,136,0,0,0,[114],0⟩
  | 51 => ⟨6,7,true,6,0,0,64,[48, 81, 16, 100, 118],3⟩
  | 52 => ⟨4,7,true,0,0,0,16,[84, 101, 118],5⟩
  | 53 => ⟨5,7,true,0,0,0,32,[50, 98, 82, 84, 117],15⟩
  | 54 => ⟨6,7,true,12,0,0,64,[16, 80, 100, 118],3⟩
  | 55 => ⟨6,7,true,40,0,0,64,[16, 32, 80, 100, 118],3⟩
  | 56 => ⟨5,7,true,72,0,0,32,[82, 100, 117],3⟩
  | 57 => ⟨6,7,true,2,0,0,64,[32, 49, 80, 100, 118],7⟩
  | 58 => ⟨5,7,true,2,0,0,32,[49, 98, 82, 84, 117],7⟩
  | 59 => ⟨5,7,true,64,0,0,32,[50, 82, 100, 117],7⟩
  | 60 => ⟨4,7,true,32,0,0,16,[33, 49, 83, 100, 118],3⟩
  | 61 => ⟨4,7,true,64,0,0,16,[33, 49, 83, 100, 117],3⟩
  | 62 => ⟨3,7,true,96,0,0,8,[82, 99, 116],3⟩
  | 63 => ⟨6,7,true,36,0,0,64,[16, 48, 80, 100, 118],3⟩
  | 64 => ⟨4,7,true,8,0,0,16,[33, 49, 84, 101, 118],3⟩
  | 65 => ⟨2,3,false,96,0,0,0,[48, 33, 98, 84],0⟩
  | 66 => ⟨2,7,true,0,0,0,4,[65, 98, 33, 50, 83, 117],6⟩
  | 67 => ⟨2,7,true,66,0,0,4,[64, 48, 82, 99, 117],1⟩
  | 68 => ⟨1,4,false,64,0,0,0,[16, 97],0⟩
  | 69 => ⟨1,4,false,40,0,0,0,[32, 97, 50, 101],0⟩
  | _ => ⟨0,0,false,0,0,0,0,[],0⟩

def quotDom (b : QuotientSpec) : Sig :=
  let d := (inputs.getD b.a zero) ^^^ (inputs.getD b.b zero)
  subcube b.z b.o &&& (if b.rev then d else ~~~d)

def quotSteps (b : QuotientSpec) : List Move :=
  let a := inputs.getD b.a zero
  let dest := inputs.getD b.b zero
  let want := if b.rev then ~~~a else a
  let move : Move := (want &&& ~~~dest, dest &&& ~~~want, Fin.ofNat 512 (1 <<< b.b))
  let flips := (List.range 9).filterMap fun i =>
    let w := inputs.getD i zero
    if b.fl.testBit i then some ((~~~w, w, Fin.ofNat 512 (1 <<< i)) : Move) else none
  b.sw.map swapRows ++ flips ++ fixRows (b.z ||| b.extra) b.o ++ [move]

def phaseFree (roots : List Sig) (w : Sig) := freeWord roots w || roots.contains (neg w)

theorem phaseFree_ok {xs w} (h : phaseFree xs w = true) :
    Available true (xs.map observe) (observe w) := by
  simp only [phaseFree,Bool.or_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  rcases h with h | h
  · exact freeWord_ok h
  · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    rw [← obs_neg]
    exact List.mem_map_of_mem h

def signedMap (ms : List Move) (raw : List Sig) (base : List Sig) :=
  raw.all (fun a => phaseFree base (movedWord ms a))

theorem signedSlice {ms raw T base d L} (h : signedMap ms raw base = true)
    (all : movedWord ms d = one) (pr : proper (movedWord ms T))
    (low : Lower true base (movedWord ms T) L) : Slice true raw T d L := by
  have he : restrictRows (movedRow ms) (observe T) = observe (movedWord ms T) := by
    rw [moved_eq_rename, observe_rename]
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [← bit_moved, all, bit_one]
  · intro a ha
    rw [← observe_rename, ← moved_eq_rename]
    exact phaseFree_ok (List.all_eq_true.mp h a ha)
  · rw [he]
    exact observe_proper pr
  · rw [he]
    exact low

def quotientCheck (u : Bool) (raw : List Sig) (T : Sig) (b : QuotientSpec) (q L P : Nat) : Bool :=
  let ms := quotSteps b
  let G := movedWord ms T
  let bs := varsX (q ||| b.single)
  let xs := supportPairs 0 b.single
  u && signedMap ms raw bs && (movedWord ms (quotDom b) == one) &&
    properB G && properB (graphGoal q) &&
    checkLift (fixRows b.single 0) G bs (varsX q) (graphGoal q) xs &&
    decide (L ≤ P+(xs.map Prod.fst).toFinset.card)

theorem quotientSound {u raw T b q L P}
    (low : Lower u (varsX q) (graphGoal q) P)
    (ok : quotientCheck u raw T b q L P = true) : Slice u raw T (quotDom b) L := by
  simp only [quotientCheck,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨hu,hm⟩,hd⟩,pg⟩,pq⟩,lift⟩,hle⟩ := ok
  subst u
  apply signedSlice hm hd (proper_of _ pg)
  intro p bank reach hit
  exact hle.trans (lift_ok lift (proper_of _ pg) (proper_of _ pq) low p bank reach hit)

def fieldDomain (z o : Nat) : Sig :=
  if o < 512 then subcube z o else quotDom (quotSpec (o-512))

def fieldCheck (u : Bool) (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  if c.2.1 < 512 then colCheck m c prior else
    let q := c.2.2.1
    quotientCheck u (varsX (rawMask m c)) (chartGoal m) (quotSpec (c.2.1-512)) q c.2.2.2.2 (prior q)

theorem fieldSound {u m} (c : ColumnInfo) (prior : Nat → Nat)
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : fieldCheck u m c prior = true) :
    Slice u (varsX (rawMask m c)) (chartGoal m) (fieldDomain c.1 c.2.1) c.2.2.2.2 := by
  by_cases h : c.2.1 < 512
  · simpa only [fieldDomain, h, if_true] using
      col_sound c prior low (by simpa only [fieldCheck, h, if_true] using ok)
  · simpa only [fieldDomain, h, if_false] using
      (quotientSound (low c.2.2.1) (by simpa only [fieldCheck, h, if_false] using ok) :
        Slice u (varsX (rawMask m c)) (chartGoal m) (quotDom (quotSpec (c.2.1-512))) c.2.2.2.2)

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
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2)
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
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2)
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
  g.cols.all (fun c => fieldCheck g.mode g.mask c prior) &&
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
        (fun x hx => fieldSound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => fieldSound _ prior lower (geometry.1.2 x hx)) geometry.2
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
    let r := (data 0 >>> (64*j)) &&& ((1 <<< 64)-1)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[3,5]⟩,⟨.or,[1,2]⟩,⟨.or,[8,9]⟩,⟨.or,[0,1]⟩,⟨.or,[6,11]⟩,⟨.or,[0,2]⟩,⟨.or,[7,13]⟩,⟨.or,[7,8]⟩,⟨.or,[6,7]⟩,⟨.and,[14,4]⟩,⟨.and,[16,10]⟩,⟨.and,[15,12]⟩,⟨.and,[5,3]⟩,⟨.or,[17,18]⟩,⟨.or,[21,19]⟩,⟨.or,[22,20]⟩], 23⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 3, 4, 0, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 3, 4, 0, 0, 0, 1, 0] : List Nat).getD i.val 0))

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
private def sampledPair (a b c d : Nat) : Bits × Bits :=
  (BitVec.ofNat 152 ((a <<< 80) ||| b), BitVec.ofNat 152 ((c <<< 80) ||| d))
private abbrev sampleWord (n : Nat) : BitVec 152 := BitVec.ofNat 152 n
def g41Y : Array (Bits × Bits) := #[sampledPair 0x3ff63ff63ff63ff63f 0xf63ff63ff63ff63ff63f 0x492049204920492049 0x20492049204920492049,(0,0),(0,0),sampledPair 0xc7fbc7fbc7fbc7fbc7 0xfbc7fbc7fbc7fbc7fbc7 0x924092409240924092 0x40924092409240924092,(0,0),sampledPair 0xf8fdf8fdf8fdf8fdf8 0xfdf8fdf8fdf8fdf8fdf8 0x248124812481248124 0x81248124812481248124,(0,0),(0,0),(0,0)]
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
theorem g41B3 : CutRow g41 3 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=3) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : mixedTables g41 3 := by
  intro k hk
  interval_cases k <;> first
  | exact g41B3
  | exact mixedEmpty g41 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := mixedLower (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(42,[16]),(74,[16,101]),(98,[16,83,67,100]),(104,[48,16,33,82,66,100]),(137,[117,101]),(138,[16,117,101]),(145,[67,117,101]),(148,[32,16,67,117,101]),(162,[16,83,67,116,100]),(168,[48,16,33,82,66,116,100]),(194,[16,99,67,117]),(196,[32,16,99,67,117]),(200,[48,16,33,98,66,117]),(224,[80,16,33,99,66,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[sampledPair 0xf71fc7ff03fffff8f7 0x1fc7ff03fffff8f71fc7 0x710490a2850401207 0x10490a28504012071049,sampledPair 0xbe838fffc07e3ff0b 0xe838fffc07e3ff0be838 0x4368db4c3260892043 0x68db4c326089204368db,(0,0),sampledPair 0xeee63ffffff803ffee 0xe63ffffff803ffeee63f 0x88724904085124008 0x87249040851240088724,sampledPair 0x193dc0fffffffc0019 0x3dc0fffffffc00193dc0 0x982db6e08306038498 0x2db6e083060384982db6,(0,0),(0,0),(0,0),(0,0)]
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
theorem g27B3 : CutRow g27 3 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=4) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : mixedTables g27 3 := by
  intro k hk
  interval_cases k <;> first
  | exact g27B3
  | exact mixedEmpty g27 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := mixedLower (g:=g27) (i:=0) (hints:=51) (before_sound K41 V41) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K41 4 [(27,[]),(29,[33,67]),(51,[83]),(53,[33,67,83]),(77,[96,16,33,66,84]),(85,[32,16,67,99,83]),(86,[32,99,83]),(89,[48,65,33,98,82]),(92,[32,49,97,81]),(113,[80,65,33,48,98,50]),(116,[96,65,32,50,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V41 low27 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[sampledPair 0xfe7d01c7fc0fc7cfe7 0xd01c7fc0fc7cfe7d01c7 0x51d124928a290a051 0xd124928a290a051d1249,sampledPair 0x3f8b8e38fff007f3f8 0xb8e38fff007f3f8b8e38 0x884b924930c3210884 0xb924930c3210884b9249,(0,0),sampledPair 0x3fe7703ffffff803fe 0x7703ffffff803fe7703f 0x100024924104020100 0x2492410402010002492,(0,0),sampledPair 0xc018ffc0fffffffc01 0x8ffc0fffffffc018ffc0 0x200049248208040200 0x4924820804020004924,(0,0),(0,0),(0,0)]
def g43C : List ColumnInfo := [(1,0,42,0,4)]
def g43A : List (List Nat) := [[],[83],[16],[16,83]]
def g43D4 (j : Nat) := if j=0 then 0x1f else 0
def g43L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g43D4)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,4,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43B4 : CutRow g43 4 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=4) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : mixedTables g43 4 := by
  intro k hk
  interval_cases k <;> first
  | exact g43B4
  | exact mixedEmpty g43 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := mixedLower (g:=g43) (i:=0) (hints:=51) (before_sound K27 V27) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K27 5 [(43,[]),(105,[97,33,66]),(139,[117,101]),(149,[33,67,117,101]),(153,[48,65,33,117,101]),(163,[83,67,116,100]),(204,[32,49,97,65,117]),(212,[64,97,32,50,49,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V27 low43 (by decide +kernel)
def g57Y : Array (Bits × Bits) := #[sampledPair 0xfdb07fff83ffe7fffb 0x60ffff07ffcffff6c1ff 0x92410820400800 0x1248210408010000249,(0,0),(0,0),sampledPair 0x3bcf81fffc0ff8fc77 0x9f03fff81ff1f8ef3e07 0x81c5248a1142821103 0x8a491422850422071492,sampledPair 0xc6940e3ffff000ff8d 0x281c7fffe001ff1a5038 0x16976dac218b14a02d 0x2edb58431629405a5db6,sampledPair 0x66ff03fffffff000c 0xdfe07ffffffe0019bfc0 0x262a4930420c00c24c 0x5492608418018498a924,(0,0),(0,0),(0,0)]
def g57C : List ColumnInfo := [(16,0,41,0,4)]
def g57A : List (List Nat) := [[],[83]]
def g57D4 (j : Nat) := if j=0 then 0x1f else 0
def g57L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g57D4)
  | _ => emptyPacking
def g57I (_ _ : Nat) : Option (Nat × Nat) := none
def g57 : Forest := ⟨57,4,fun i => g57Y[i]?.getD (0,0),g57C,g57A,g57L,g57I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57B4 : CutRow g57 4 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=4) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57T : mixedTables g57 4 := by
  intro k hk
  interval_cases k <;> first
  | exact g57B4
  | exact mixedEmpty g57 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57G : graphValid g57 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low57 : Lower true (varsX 57) (graphGoal 57) 5 := mixedLower (g:=g57) (i:=0) (hints:=3) (before_sound K43 V43) g57G g57T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K57 := extendKnown K43 5 [(57,[]),(78,[96,16,66,49,83]),(108,[96,16,33,66]),(141,[112,66,48,83,101]),(142,[112,16,66,49,83,101]),(147,[112,33,49,16,65,84,101]),(150,[112,16,50,65,84,101]),(154,[112,16,49,83,101]),(156,[112,16,33,50,67,84,101]),(172,[112,16,33,66,100]),(178,[112,16,49,99]),(180,[112,16,33,50,84,99]),(184,[112,16,33,98]),(197,[112,50,64,101,84]),(209,[112,48,100,84,83]),(216,[112,16,33,101,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V57 : Known true K57 := extend_ok (m:=57) V43 low57 (by decide +kernel)
def g106Y : Array (Bits × Bits) := #[(0,0),sampledPair 0xdf7ec03c3ffe0fbefd 0x80787ffc1f7dfb00f0ff 0x820404444444210408 0x8888888420810111111,(0,0),sampledPair 0x1fbf43c3c3fff03f7e 0x878787ffe07efd0f0f0f 0x40808888888420810 0x11111110841020222222,(0,0),sampledPair 0xe03fbc03fc3fffc07f 0x7807f87fff80fef00ff0 0x81011111110841020 0x22222221082040444444,sampledPair 0xffc03ffc003fffff80 0x7ff8007fffff00fff000 0x102022222221082040 0x44444442104080888888,(0,0),(0,0)]
def g106C : List ColumnInfo := [(2,0,104,0,4),(8,0,98,0,4),(32,0,74,0,4),(64,0,42,0,4)]
def g106A : List (List Nat) := [[],[101],[83],[83,99],[99,83],[99],[49],[49,101],[49,81],[49,81,97],[49,97,81],[49,97],[81,49],[81,49,99],[81],[81,97],[81,99],[81,99,49],[97,49,83],[97,49],[97,81],[97],[97,83,49],[97,83]]
def g106D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g106D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g106H4 (j : Nat) := if j=0 then 0xc else 0
def g106D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g106H5 := limbs80 #[#[0x24b894000,0x88000009800000020a00,0x70]]
def g106D6 (j : Nat) := if j=0 then 0x3904f else 0
def g106H6 := limbs80 #[#[0x14000000015008801100,0x5]]
def g106L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g106D3)
  | 4 => (3,2,2,0,0,5,0,g106D4)
  | 5 => (1,1,2,0,0,0,0,g106D5)
  | 6 => (1,0,2,0,0,0,0,g106D6)
  | _ => emptyPacking
def g106I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupShort 1 2 0 3 1 0 g106H4
  | 5 => lookupShort 2 31 0 7 2 3 g106H5
  | 6 => lookupShort 1 17 0 7 0 5 g106H6
  | _ => fun _ => none
def g106 : Forest := ⟨106,6,fun i => g106Y[i]?.getD (0,0),g106C,g106A,g106L,g106I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106B3 : CutRow g106 3 0 2 := (by
      apply checkedRow
      apply cellsBlock (ar:=4) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106B4 : CutRow g106 4 0 3 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106B5 : CutRow g106 5 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106B6 : CutRow g106 6 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=4) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106T : mixedTables g106 6 := by
  intro k hk
  interval_cases k <;> first
  | exact g106B3
  | exact g106B4
  | exact g106B5
  | exact g106B6
  | exact mixedEmpty g106 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106G : graphValid g106 (boundsBefore K57) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low106 : Lower true (varsX 106) (graphGoal 106) 7 := mixedLower (g:=g106) (i:=0) (hints:=17829936) (before_sound K57 V57) g106G g106T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K106 := extendKnown K57 7 [(106,[]),(169,[16,118]),(170,[118]),(202,[101,117]),(226,[83,67,100,116]),(232,[49,33,82,66,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V106 : Known true K106 := extend_ok (m:=106) V57 low106 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[sampledPair 0xe003ffc07ffffffe00 0x3fffff80ffd386b20f0f 0x41a8128d052280541a 0x82502916291304a21111,sampledPair 0xfffc00007ff01fffff 0xc007ffff01a37d4800f0 0x81311b160644c89893 0x136232244d835c485555,sampledPair 0xffffffff80001fffff 0xfff80000003f407df000 0x5c05c18178702e01c 0x380bc38703340753333,sampledPair 0x1fffff 0xfffffffffe663f7600ff 0x160260205808130120 0x2404c00000642314aaaa,sampledPair 0xffffffffffffe00000 0x19dd38dff00 0x1803800060001c01c0 0x38070040808c9308cccc,(0,0),(0,0),(0,0),(0,0)]
def g31C : List ColumnInfo := []
def g31A : List (List Nat) := [[],[33,67]]
def g31D4 (j : Nat) := if j=0 then 0x1f else 0
def g31L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g31D4)
  | _ => emptyPacking
def g31I (_ _ : Nat) : Option (Nat × Nat) := none
def g31 : Forest := ⟨31,4,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31B4 : CutRow g31 4 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : mixedTables g31 4 := by
  intro k hk
  interval_cases k <;> first
  | exact g31B4
  | exact mixedEmpty g31 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K106) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 5 := mixedLower (g:=g31) (i:=0) (hints:=1075) (before_sound K106 V106) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K106 5 [(31,[]),(55,[83]),(87,[32,16,67,99,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V106 low31 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[sampledPair 0xfe007fe1ff0fffc03f 0xffffff0ff9621a00ff0f 0x140501440220028281 0x4040022088420a111111,sampledPair 0xffff8001fff0ffffc0 0x1fe1fff01c1fa90f00f0 0x982609882402130309 0x80842402180f09333333,(0,0),sampledPair 0xfffffffe0000ffffff 0xe001ffff239766f000ff 0x204812004844240402 0x5084800211064444444,sampledPair 0xffffff 0xfffe00001369f8000f00 0xc1705c117088b8282c 0x160170441329f0eeeeee,sampledPair 0xffffffffffff000000 0xcea8c5fff000 0x18060018000c03030 0x1811808846a080888888,(0,0),(0,0),(0,0)]
def g59C : List ColumnInfo := [(0,16,42,1,5),(2,0,57,0,5),(16,0,43,0,5),(1,16,42,0,4),(8,0,51,0,4),(32,0,27,0,4)]
def g59A : List (List Nat) := [[],[83]]
def g59D4 (j : Nat) := if j=0 then 0x5dd4542 else 0
def g59D5 (j : Nat) := if j=0 then 0x108404fd42 else 0
def g59H5 (j : Nat) := if j=0 then 0x4 else 0
def g59D6 (j : Nat) := if j=0 then 0x2c458bf else 0
def g59H6 (j : Nat) := if j=0 then 0x2 else 0
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (1,1,3,0,0,0,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g59H5
  | 6 => lookupShort 1 2 0 2 0 0 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59B4 : CutRow g59 4 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59B5 : CutRow g59 5 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59B6 : CutRow g59 6 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : mixedTables g59 6 := by
  intro k hk
  interval_cases k <;> first
  | exact g59B4
  | exact g59B5
  | exact g59B6
  | exact mixedEmpty g59 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := mixedLower (g:=g59) (i:=0) (hints:=51) (before_sound K31 V31) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K31 7 [(59,[]),(109,[96,16,33,66]),(121,[97,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V31 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[sampledPair 0xf007ff0ffffff007ff 0xff87ffffd45c460f83ff 0xa0500a201000a05014 0x1100082401806108421,(0,0),sampledPair 0xfff8000ff87ffff801 0xfff87fc05373b2007c00 0xc0622c40a122c46258 0x8a012108527132b5ad6b,sampledPair 0xfffffff0007ffffffe 0x7ffcafd11df0001f 0x280b002c20b008060 0x2c220a00a541186318c6,sampledPair 0x7fffffff 0xffff80004d2fe8007fe0 0xb04c08b044c090481 0x30004c100d06c94a5294,sampledPair 0xffffffffff80000000 0x33aa61bff8000 0xc07000c00700e0701 0xc04470211aa6018c6318,(0,0),(0,0),(0,0)]
def g61C : List ColumnInfo := [(0,4,41,16,5),(4,0,57,0,5),(8,0,53,0,4),(16,4,41,0,4),(32,0,29,0,4)]
def g61A : List (List Nat) := [[],[83]]
def g61D4 (j : Nat) := if j=0 then 0x4fd5120 else 0
def g61D5 := limbs80 #[#[0x480e140fd42fe20fd20,0x4088]]
def g61H5 (j : Nat) := if j=0 then 0x0 else 0
def g61D6 (j : Nat) := if j=0 then 0x18989f else 0
def g61H6 := limbs80 #[#[0x20000000000,0x5620,0x501800000]]
def g61L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g61D4)
  | 5 => (3,1,3,0,0,5,0,g61D5)
  | 6 => (1,0,3,0,0,0,0,g61D6)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g61H5
  | 6 => lookupShort 1 43 0 5 2 1 g61H6
  | _ => fun _ => none
def g61 : Forest := ⟨61,6,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61B4 : CutRow g61 4 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61B5 : CutRow g61 5 0 3 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61B6 : CutRow g61 6 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : mixedTables g61 6 := by
  intro k hk
  interval_cases k <;> first
  | exact g61B4
  | exact g61B5
  | exact g61B6
  | exact mixedEmpty g61 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 7 := mixedLower (g:=g61) (i:=0) (hints:=1027) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 7 [(61,[]),(91,[48,33,65,16,101]),(94,[96,16,66,49,83]),(115,[80,33,65,49,48,99]),(118,[96,16,66,49]),(124,[96,16,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g62Y : Array (Bits × Bits) := #[(0,0),sampledPair 0xc00fff0ffffffc00ff 0xfff0fffeea3a5303f03f 0x84a08a210802284a02 0x80220882200a53145145,sampledPair 0xfff0000ffc3fffff00 0x3fffffc009adfd000fc0 0xc42c405090b10c4b 0x11404108092d994d34d3,sampledPair 0xfffffff0003fffffff 0xc000fffd77e88afc003f 0x90130026104c0100c 0x584120152a08828a28a,sampledPair 0x3fffffff 0xffff00012697f4000fc0 0x2e09c08b8227026090 0x26009c11269264b2cb2c,sampledPair 0xffffffffffc0000000 0x39d530dfff000 0x300e000c00380380e0 0x3808e0208d5104c30c30,(0,0),(0,0),(0,0)]
def g62C : List ColumnInfo := [(0,4,42,16,5)]
def g62A : List (List Nat) := [[],[83],[66],[66,83],[49],[49,81],[49,66],[49,66,81],[81,49],[81],[81,66,49],[81,66]]
def g62D5 (j : Nat) := if j=0 then 0x3f else 0
def g62L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g62D5)
  | _ => emptyPacking
def g62I (_ _ : Nat) : Option (Nat × Nat) := none
def g62 : Forest := ⟨62,5,fun i => g62Y[i]?.getD (0,0),g62C,g62A,g62L,g62I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62B5 : CutRow g62 5 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : mixedTables g62 5 := by
  intro k hk
  interval_cases k <;> first
  | exact g62B5
  | exact mixedEmpty g62 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 6 := mixedLower (g:=g62) (i:=0) (hints:=1184816) (before_sound K61 V61) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K61 6 [(62,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V61 low62 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[sampledPair 0x7ff001ff80ffc07ff0 0x3ffffe03ff4b12b0007 0x42a8d4251a148b42a9 0xaa4a8a458a64b1235b6d,sampledPair 0x7ffffe0000ffffffff 0xfc00ffffc068db9401f8 0x4c098362c191204c1 0x306c0c891340d3841249,sampledPair 0x7fffffffff00007fff 0xffff0000000ff00e8e00 0x1702e0b8305e1c1701 0xc0702f0e1c0df00cb6db,sampledPair 0x800000000000007fff 0xffffffffff99af6d703f 0x180300c04060201802 0x80300000190c082492,(0,0),(0,0),sampledPair 0xffffffffffffff8000 0x6754f2ffc0 0x600c0100008000600c 0x300c010202200724924,(0,0),(0,0)]
def g79C : List ColumnInfo := [(1,0,78,0,5)]
def g79A : List (List Nat) := [[],[32,99]]
def g79D5 (j : Nat) := if j=0 then 0x3f else 0
def g79L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g79D5)
  | _ => emptyPacking
def g79I (_ _ : Nat) : Option (Nat × Nat) := none
def g79 : Forest := ⟨79,5,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79B5 : CutRow g79 5 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : mixedTables g79 5 := by
  intro k hk
  interval_cases k <;> first
  | exact g79B5
  | exact mixedEmpty g79 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K62) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 6 := mixedLower (g:=g79) (i:=0) (hints:=16778803) (before_sound K62 V62) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K62 6 [(79,[]),(103,[83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V62 low79 (by decide +kernel)
def g93Y : Array (Bits × Bits) := #[sampledPair 0xf003ff0ff87ff007ff 0xff87fffcd47c560003ff 0xa4280a201120a45214 0x81102080501c1694a529,(0,0),sampledPair 0xfffc000ffffffff801 0xfff87fc35353a20ffc00 0xc0302c40a002c06058 0xa01010a425122318c63,sampledPair 0xfffffff0007ffffffe 0x7ffcafd11df0001f 0x140b002c20b008060 0x2c220a00a741086318c6,sampledPair 0x7fffffff 0xffff80004d2fe8007fe0 0x982c08b044c090481 0x30004c100d22c94a5294,(0,0),sampledPair 0xffffffffff80000000 0x33aa61bff8000 0xe03000c00700e0701 0xc044702118a6118c6318,(0,0),(0,0)]
def g93C : List ColumnInfo := [(1,0,92,0,4),(4,0,89,0,4),(8,0,85,0,4),(16,0,77,0,4),(64,0,29,0,4)]
def g93A : List (List Nat) := [[],[98,67],[32,99],[32,48,64,96],[48,100],[48,66,96,32],[64,50],[64,98,48,50],[96,32,50,67],[96,66]]
def g93D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g93D5 (j : Nat) := if j=0 then 0xc1a0fd20fd10 else 0
def g93H5 (j : Nat) := if j=0 then 0x0 else 0
def g93D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g93H6 := limbs80 #[#[0x7000000,0x330001400000,0x8400008806806c,0x16c00000000000000,0,0,0xb80]]
def g93L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g93D4)
  | 5 => (2,1,3,0,0,4,0,g93D5)
  | 6 => (1,0,3,0,0,0,0,g93D6)
  | _ => emptyPacking
def g93I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g93H5
  | 6 => lookupShort 2 83 0 6 1 3 g93H6
  | _ => fun _ => none
def g93 : Forest := ⟨93,6,fun i => g93Y[i]?.getD (0,0),g93C,g93A,g93L,g93I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93B4 : CutRow g93 4 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93B5 : CutRow g93 5 0 2 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93B6 : CutRow g93 6 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : mixedTables g93 6 := by
  intro k hk
  interval_cases k <;> first
  | exact g93B4
  | exact g93B5
  | exact g93B6
  | exact mixedEmpty g93 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 7 := mixedLower (g:=g93) (i:=0) (hints:=33555459) (before_sound K79 V79) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K79 7 [(93,[]),(117,[98,67,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V79 low93 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[sampledPair 0xfe3fc03f8fcff00f 0xf0fe3ff1e57c00000f0f 0x8a14a2a28520a8a8a8 0xa2848424257c99999999,sampledPair 0xff003fffc00ffffff0 0xffc7fe13ad00f0f0f0 0xc190303064100c0c0 0xc4081040932911111111,(0,0),sampledPair 0x3ffffff00fffff 0xff0007ffc4330f0f00ff 0x102004040802010101 0x100080000022222222,(0,0),sampledPair 0xffffc00000000fffff 0xfffff8002a48f00fff00 0x204008081004020202 0x200100000044444444,sampledPair 0xfffffffffffff00000 0x3996fff00000 0xc080303020080c0c0c 0x8c12609289688888888,(0,0),(0,0)]
def g107C : List ColumnInfo := [(1,0,106,0,7)]
def g107A : List (List Nat) := [[],[83],[97],[97,83]]
def g107D7 (j : Nat) := if j=0 then 0x3f else 0
def g107L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g107D7)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,7,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107B7 : CutRow g107 7 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : mixedTables g107 7 := by
  intro k hk
  interval_cases k <;> first
  | exact g107B7
  | exact mixedEmpty g107 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 8 := mixedLower (g:=g107) (i:=0) (hints:=16777267) (before_sound K93 V93) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K93 8 [(107,[]),(185,[64,49,33,32,117,101]),(206,[32,99,117]),(236,[32,49,97,65,117,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V93 low107 (by decide +kernel)
def g110Y : Array (Bits × Bits) := #[(0,0),sampledPair 0xfe1ff00ff87f87ffc0 0x7fc7ffffd3b94000f0ff 0x1440a0a05101100285 0x2902008418941111111,sampledPair 0x1ffff0007ff87fff 0x8007f1fc231ee00f0000 0x588ac4c5622a012b06 0x2b214491231ee7777777,sampledPair 0x1fffffff80007fff 0xfff801ff9c1f30f00f0f 0x61030101800c220c08 0xc0188201c1602222222,(0,0),sampledPair 0xffe000000000007fff 0xfffffe000be4bf000ff0 0x800c06060430443010 0x300200c20260b4444444,sampledPair 0xffffffffffffff8000 0x6442cffff000 0x1008080040004020 0x40040100000008888888,(0,0),(0,0)]
def g110C : List ColumnInfo := [(4,0,106,0,7)]
def g110A : List (List Nat) := [[],[83],[49],[49,81],[81,49],[81]]
def g110D7 (j : Nat) := if j=0 then 0x3f else 0
def g110L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g110D7)
  | _ => emptyPacking
def g110I (_ _ : Nat) : Option (Nat × Nat) := none
def g110 : Forest := ⟨110,7,fun i => g110Y[i]?.getD (0,0),g110C,g110A,g110L,g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110B7 : CutRow g110 7 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : mixedTables g110 7 := by
  intro k hk
  interval_cases k <;> first
  | exact g110B7
  | exact mixedEmpty g110 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 8 := mixedLower (g:=g110) (i:=0) (hints:=17831472) (before_sound K107 V107) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K107 8 [(110,[]),(173,[16,118]),(174,[118]),(186,[66,118]),(248,[49,66,81,33,98,114])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V107 low110 (by decide +kernel)
def g143Y : Array (Bits × Bits) := #[sampledPair 0xffc00ffc07fe03fff 0xe00ffffe07f469d401c7 0xa0a86a128d0a458a05 0x46a250a4b29029d49249,sampledPair 0xfffff00007fffc07f 0xfff007fff813a68c0e38 0xc1304c1b160c891309 0x84c360c924d1a28c9249,sampledPair 0xfffffffff8000007f 0xfffff800000bc8b47000 0x5c1705c182f0e1c2e 0x70382f1c70bc8b5b6db,sampledPair 0xf0000000000000007f 0xffffffffffe6fe67803f 0x60180602030102030 0x8040300000654212492,(0,0),(0,0),(0,0),sampledPair 0xffffffffffffffff80 0x1911bbffc0 0x80200800040000040 0x10080400000000024924,(0,0)]
def g143C : List ColumnInfo := [(1,0,142,0,5)]
def g143A : List (List Nat) := [[],[16]]
def g143D5 (j : Nat) := if j=0 then 0x3f else 0
def g143L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g143D5)
  | _ => emptyPacking
def g143I (_ _ : Nat) : Option (Nat × Nat) := none
def g143 : Forest := ⟨143,5,fun i => g143Y[i]?.getD (0,0),g143C,g143A,g143L,g143I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143B5 : CutRow g143 5 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143T : mixedTables g143 5 := by
  intro k hk
  interval_cases k <;> first
  | exact g143B5
  | exact mixedEmpty g143 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143G : graphValid g143 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low143 : Lower true (varsX 143) (graphGoal 143) 6 := mixedLower (g:=g143) (i:=0) (hints:=1843) (before_sound K110 V110) g143G g143T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K143 := extendKnown K110 6 [(143,[]),(151,[33,67]),(167,[83,67]),(199,[16,32,99,67,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V143 : Known true K143 := extend_ok (m:=143) V110 low143 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[sampledPair 0xfc3fe00ff87f87ffc0 0x7fffffe3dba15000ff0f 0x288140a05101100285 0x502004842a141111111,sampledPair 0x3ffff0007ff87fff 0x807f1ffc2adc600f00f0 0x310984c26212011306 0x260444812acc43333333,(0,0),sampledPair 0x3fffffff80007fff 0xff801fff949db0f000ff 0x421209048024222408 0x82889001410b4444444,sampledPair 0xffc000000000007fff 0xffffe0000b66bf000f00 0x801c0e070438443810 0x30300e120946b6666666,(0,0),(0,0),sampledPair 0xffffffffffffff8000 0x6442cffff000 0x2010080040004020 0x40401000000008888888,(0,0)]
def g155C : List ColumnInfo := [(1,0,154,0,5),(2,0,153,0,5),(8,0,147,0,5),(16,0,139,0,5)]
def g155A : List (List Nat) := [[],[48,65]]
def g155D6 (j : Nat) := if j=0 then 0x6c09f else 0
def g155L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g155D6)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,6,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155B6 : CutRow g155 6 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : mixedTables g155 6 := by
  intro k hk
  interval_cases k <;> first
  | exact g155B6
  | exact mixedEmpty g155 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K143) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 7 := mixedLower (g:=g155) (i:=0) (hints:=51) (before_sound K143 V143) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K143 7 [(155,[]),(157,[33,67]),(179,[83]),(181,[33,67,83]),(205,[96,16,33,66,84]),(213,[32,16,67,99,83]),(214,[32,99,83]),(217,[48,65,33,98,82]),(220,[32,49,97,81]),(244,[96,65,32,50,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V143 low155 (by decide +kernel)
def g158Y : Array (Bits × Bits) := #[(0,0),sampledPair 0xffc01ff87fc3fff00 0xffff1ffed2e680007c1f 0x222894451108808a4a 0xa02444252268a5294a5,sampledPair 0xffffe0007ffc3ffff 0xffffe11773400f83e0 0x40b018162050082c0c 0x2c140089146346318c63,sampledPair 0xffffffff80003ffff 0xff001ffce8f541f0001f 0x84c120980261113010 0x30588900a8d154a5294a,sampledPair 0xf0000000000003ffff 0xffffe0005f98fe0003e0 0x701c0e0438221c060 0x40600e104b9898c6318c,(0,0),(0,0),sampledPair 0xfffffffffffffc0000 0x3280bbffffc00 0x80201000400020080 0x80801000000021084210,(0,0)]
def g158C : List ColumnInfo := [(2,0,156,0,5),(4,0,154,0,5),(8,0,150,0,5),(16,0,142,0,5),(10,0,148,0,4),(20,0,138,0,4)]
def g158A : List (List Nat) := [[],[66],[33,67],[33,49,65],[49],[49,66],[65,33,50],[65,50]]
def g158D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g158D5 := limbs80 #[#[0x3527f7bbf6f4050110,0x5f405d50654155045435,0x66ad0941001546b525d4,0xc08024050462b13e3bb,0x4040201642000001201]]
def g158H5 (j : Nat) := if j=0 then 0x421668032 else 0
def g158D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g158H6 := limbs80 #[#[0x4838602858100870091c,0xd70000004000c,0xd94914c8a1009300000]]
def g158D7 (j : Nat) := if j=0 then 0x1605f else 0
def g158H7 := limbs80 #[#[0xf40048040014510090a,0x9510d59d3b3]]
def g158L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g158D4)
  | 5 => (10,2,3,262147,34,7,1030,g158D5)
  | 6 => (3,1,3,0,0,6,0,g158D6)
  | 7 => (1,0,3,0,0,0,0,g158D7)
  | _ => emptyPacking
def g158I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 7 0 6 2 2 g158H5
  | 6 => lookupShort 4 29 1 8 4 2 g158H6
  | 7 => lookupShort 3 17 4 7 2 3 g158H7
  | _ => fun _ => none
def g158 : Forest := ⟨158,7,fun i => g158Y[i]?.getD (0,0),g158C,g158A,g158L,g158I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158B4 : CutRow g158 4 0 3 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158B5 : CutRow g158 5 0 10 := (@joinRow g158 5 0 1 9 (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158B6 : CutRow g158 6 0 3 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158B7 : CutRow g158 7 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158T : mixedTables g158 7 := by
  intro k hk
  interval_cases k <;> first
  | exact g158B4
  | exact g158B5
  | exact g158B6
  | exact g158B7
  | exact mixedEmpty g158 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g158G : graphValid g158 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low158 : Lower true (varsX 158) (graphGoal 158) 8 := mixedLower (g:=g158) (i:=0) (hints:=268571696) (before_sound K155 V155) g158G g158T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K158 := extendKnown K155 8 [(158,[]),(182,[83]),(188,[33,49,65,81]),(211,[32,16,67,99,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V158 : Known true K158 := extend_ok (m:=158) V155 low158 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[sampledPair 0x7f01fc7f01fc7e7fc 0x7f1f9fe7ea000f00f0f 0x50a14290a142905028 0x50a414051ea111111111,sampledPair 0x7ffe007ffe007f9ff 0xf801fe7f8b700f00f0f0 0x60c18320c183208430 0x60c821084b7111111111,(0,0),sampledPair 0xf8000007fffff801ff 0xfffe007fe640f00f00ff 0x810204010204010040 0x81004010000222222222,(0,0),sampledPair 0xfffffff800000001ff 0xffffff8001af000fff00 0x20408020408020081 0x2008020000444444444,(0,0),sampledPair 0xfffffffffffffffe00 0x181ffff00000 0x40810040810040102 0x4010040000888888888,(0,0)]
def g171C : List ColumnInfo := [(1,0,170,0,7)]
def g171A : List (List Nat) := [[],[117],[83],[83,115],[115,83],[115],[16],[16,117],[16,83],[16,83,115],[16,115,83],[16,115]]
def g171D7 (j : Nat) := if j=0 then 0x3f else 0
def g171L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g171D7)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,7,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171B7 : CutRow g171 7 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : mixedTables g171 7 := by
  intro k hk
  interval_cases k <;> first
  | exact g171B7
  | exact mixedEmpty g171 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K158) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 8 := mixedLower (g:=g171) (i:=0) (hints:=51) (before_sound K158 V158) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K158 8 [(171,[]),(233,[97,33,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V158 low171 (by decide +kernel)
def g234Y : Array (Bits × Bits) := #[(0,0),sampledPair 0xc0fc0fc0fdf81fbf7f 0x3f7efec0007c00f83ff 0x820820820810410202 0x8204040210842108421,(0,0),sampledPair 0xff000fff01ffe03fbf 0xfc07f7f400f801f07c1f 0x41041041020820404 0x10408080421084210842,(0,0),sampledPair 0xfffff00001ffffc03f 0xfff807f81f003e007fe0 0x82082082041040808 0x20810100842108421084,sampledPair 0xfffffffffe0000003f 0xfffff803e0003fff8000 0x104104104082081010 0x41020201084210842108,sampledPair 0xffffffffffffffffc0 0x3ffffc0000000 0x208208208104102020 0x82040402108421084210,(0,0)]
def g234C : List ColumnInfo := [(2,0,232,0,7),(8,0,226,0,7),(32,0,202,0,7),(64,0,170,0,7),(128,0,106,0,7),(10,0,224,0,4),(34,0,200,0,4),(40,0,194,0,4),(66,0,168,0,4),(72,0,162,0,4),(96,0,138,0,4)]
def g234A : List (List Nat) := [[],[118],[101],[101,117],[117,101],[117],[83],[83,118],[83,99],[83,99,115],[83,115,99],[83,115],[99,83],[99,83,117],[99],[99,115],[99,117],[99,117,83],[115,83,101],[115,83],[115,99],[115],[115,101,83],[115,101],[49],[49,118],[49,101],[49,101,117],[49,117,101],[49,117],[49,81],[49,81,118],[49,81,97],[49,81,97,113],[49,81,113,97],[49,81,113],[49,97,81],[49,97,81,117],[49,97],[49,97,113],[49,97,117],[49,97,117,81],[49,113,81,101],[49,113,81],[49,113,97],[49,113],[49,113,101,81],[49,113,101],[81,49],[81,49,118],[81,49,99],[81,49,99,115],[81,49,115,99],[81,49,115],[81],[81,118],[81,97],[81,97,113],[81,113,97],[81,113],[81,99],[81,99,115],[81,99,49],[81,99,49,113],[81,99,113,49],[81,99,113],[81,115,99],[81,115],[81,115,49,97],[81,115,49],[81,115,97],[81,115,97,49],[97,49,83],[97,49,83,117],[97,49],[97,49,115],[97,49,117],[97,49,117,83],[97,81],[97,81,117],[97],[97,113],[97,117],[97,117,81],[97,83,49],[97,83,49,115],[97,83],[97,83,113],[97,83,115],[97,83,115,49],[97,115,81,83],[97,115,81],[97,115,83],[97,115,83,81],[97,115],[97,115,49],[113,49,83,101],[113,49,83],[113,49,99],[113,49],[113,49,101,83],[113,49,101],[113,81,101],[113,81],[113,97],[113],[113,101,81],[113,101],[113,83,49,99],[113,83,49],[113,83,97],[113,83],[113,83,99,49],[113,83,99],[113,99,81],[113,99,81,83],[113,99,83,81],[113,99,83],[113,99,49],[113,99]]
def g234D4 := limbs80 #[#[0x54d214811050d2148110,0x4c93148110d4d2148110,0xf83d0e62d85093148110,0x11c217642ac846144a98,0x350e5aa395463089d9,0x9101c305080c101]]
def g234D5 := limbs80 #[#[0x481104c5204412148110,0x443534811054d2044143,0x54d52441654c91058132,0xe3f0f58f524436354910,0x76bb1bccf65f1f7aaf56,0xc4c867530954c3f1f0ee,0x21d50875530d50c03746,0x1641bd506d5418585757,0xeb7234dc8cd7528d906,0x5d11f6443dd0df643759,0x65dd18574651d19f7063,0x4391dd2057482dc9c774,0x581c07800774915d259,0xa7d2e8f439ccc259230d,0x73b7daecf63afd6eaf53,0x2f93c7e2f0f83bfdeeef,0x2a48201c19cc24166f,0x4086017488481004a06,0x311803dc043881801d01,0x7e467]]
def g234H5 := limbs80 #[#[0x26070c106420,0x9d23aa0200b240002000,0x6f0e34000553ec28f9a3,0x1e44c18000016c1,0x8000002033e3803a028,0x2f800480000220403003,0x6f0000001e08633c38]]
def g234D6 := limbs80 #[#[0xd4910549104c91048110,0x624484fefcf8dfdebf9f,0x163c6c705955a989532a,0x13b1cd53b2c0e54cca18,0xc7358e732ad655ea8b55,0xfa692b9046a250b001e,0xc15faf576b95a4bd52a5,0xfa1210270610ccc2d286,0x1ea0e4c542834e073081,0xa05365094010a0198029,0x10947a085f0895fe011c,0x1e9820e210ef2]]
def g234H6 := limbs80 #[#[0x70a556000404c022170d,0x21017300428000030,0x496010810c00e005201a,0x40531e2a00480940233,0x235380800011f2ef1000,0xc969e04017010403c806,0x31866e3d30c000008764,0x8154803a000468dcc6a0,0x1a5e78f1c6c782804802,0xf0402a809c90e0006728,0x28001070868e81526989,0x804a0002c2a000000087,0x1c0002036000a01e875,0x2f8704183002018a801e,0xb046a4d200fc035b2320,0x1c36129002f22,0x49418018ae09c0006c8e,0xd1c92d1b82d41e30,0x669c8e06d0c9f0a03800,0xc800100b]]
def g234D7 := limbs80 #[#[0x7f52442faa4887e48110,0x3015007f54910fe99221,0x94301030ba6694235a3f,0xa5011a6690a20e30ba66,0x38da6690a3c8a142a70,0x4]]
def g234H7 := limbs80 #[#[0x41c40000009000300048,0x1a1,0,0x6110000000000000,0x11e08000000671,0,0xbc6e0620,0,0x12840000000000,0x1824000000000018030,0,0x10020000000000,0x1005600000000006186,0,0x601c000000000,0,0x9106441c600000000000,0x40000000000218200066,0x4c8,0xa00000000000000,0,0xe7070368000000002000,0x4045841,0x84000000000000000000,0x7512000000107407,0x61c30018000000000,0x261200060460000000,0x3e086bc700000000d040,0x8078048d8,0x10088001804,0x500000000,0],#[0x4042803800,0xc0c04d03661040002018,0x180000000000bc4e7050,0x6016000000000000019a,0x500e0000000000,0x10180000000401a0000,0xbc78000000205000000,0x82140000002184000000,0x2f180004055,0x49020,0x8000000004a000401200,0x9c3f092843,0x1c270,0x400200000]]
def g234D8 (j : Nat) := if j=0 then 0x2d2720806fd10 else 0
def g234H8 := limbs80 #[#[0x80084800000004900020,0xc0,0x3c00001b001d048,0x10400,0,0x44400000000000000,0,0x885100000000,0xc000000000000000e0c0,0x82,0x14001010000000,0xc0c0000,0x22200]]
def g234D9 (j : Nat) := if j=0 then 0x219080bf else 0
def g234H9 := limbs80 #[#[0x46001,0x12400a100179a4950,0x300100000,0x36b3c0]]
def g234L : Nat → Packing
  | 4 => (10,5,4,262149,35,7,1024,g234D4)
  | 5 => (32,4,4,917514,68,9,1039,g234D5)
  | 6 => (18,3,4,458756,50,9,1043,g234D6)
  | 7 => (5,2,4,0,0,8,0,g234D7)
  | 8 => (1,1,4,0,0,0,0,g234D8)
  | 9 => (1,0,4,0,0,0,0,g234D9)
  | _ => emptyPacking
def g234I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 7 43 5 12 4 6 g234H5
  | 6 => lookupShort 21 101 7 14 5 7 g234H6
  | 7 => lookupShort 17 263 3 14 5 7 g234H7
  | 8 => lookupShort 4 97 2 10 3 5 g234H8
  | 9 => lookupShort 2 29 1 9 0 7 g234H9
  | _ => fun _ => none
def g234 : Forest := ⟨234,9,fun i => g234Y[i]?.getD (0,0),g234C,g234A,g234L,g234I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234B4 : CutRow g234 4 0 10 := (by
      apply polarBlock (data:=fun _ => (w80 [0x40840301400a210404,0x4022104602104040402,0x21046021100020402910,0x82210100220108900a42,0x8002402098042200800,0x80102884482008008010,0x28844820080800120884,0xc0100040820120840a21])) rfl
      decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234B5 : CutRow g234 5 0 32 := (@joinRow g234 5 0 4 28 (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g234 5 4 5 23 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x408100,0xa0440a1000408100a044,0xa1000408100a0440a10,0x40820120840a100040,0x820120840a1000420040,0xa0142250004084022104,0xa1000408100a0440a10,0x408100a0440a100040,0x8100a0440a1001002100,0x88500a50010800120814,0x88300100220108900a50,0x1040403011048200104,0x110814482001040011,0x8144820100200402910,0xa032100200402910a042,0x1040403011048200400,0x24020940223004080012,0x844a020004084022104,0xa431000204029108232])) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234B6 : CutRow g234 6 0 18 := (@joinRow g234 6 0 7 11 (@joinRow g234 6 0 1 6 (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)) (@joinRow g234 6 7 5 6 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x408100a0440a10,0x408100a0440a100040,0x8100a0440a1000408100,0xa0440a10004084022104,0xa100040840221040a10])) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234B7 : CutRow g234 7 0 5 := (@joinRow g234 7 0 3 2 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234B8 : CutRow g234 8 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234B9 : CutRow g234 9 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234T : mixedTables g234 9 := by
  intro k hk
  interval_cases k <;> first
  | exact g234B4
  | exact g234B5
  | exact g234B6
  | exact g234B7
  | exact g234B8
  | exact g234B9
  | exact mixedEmpty g234 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g234G : graphValid g234 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low234 : Lower true (varsX 234) (graphGoal 234) 10 := mixedLower (g:=g234) (i:=0) (hints:=286265392) (before_sound K171 V171) g234G g234T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K234 := extendKnown K171 10 [(234,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V234 : Known true K234 := extend_ok (m:=234) V171 low234 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[sampledPair 0xf8001fffffff00ff57 0xa021d7a224003f03f03f 0x500d40250052161413 0x8001d0a2201041041041,sampledPair 0xffffe0007fffff0029 0x7e9bc066080fc0000fc0 0x604981360464242629 0x2419c066085145145145,sampledPair 0xffffffff800000009d 0x8e48a9b5c00000fc0000 0x820e0838217838381d 0x8a4881b5c134d34d34d3,sampledPair 0xffffffffffffffffa0 0x49c585ccf7f000000fff 0x9002400980000080 0x48800508d4a28a28a28a,sampledPair 0x91 0x75383e5b400000fff000 0x4e013804e00404080 0x75302e4802cb2cb2cb2c,sampledPair 0x4e 0x937660389bffff000000 0x7001c007000808044 0x13662010030c30c30c30,(0,0),(0,0),(0,0)]
def g63C : List ColumnInfo := [(2,0,61,0,7)]
def g63A : List (List Nat) := [[],[83]]
def g63D7 (j : Nat) := if j=0 then 0x7f else 0
def g63L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g63D7)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63B7 : CutRow g63 7 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : mixedTables g63 7 := by
  intro k hk
  interval_cases k <;> first
  | exact g63B7
  | exact mixedEmpty g63 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K234) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := mixedLower (g:=g63) (i:=0) (hints:=1075) (before_sound K234 V234) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K234 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V234 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[sampledPair 0xf8001fffffff00ff1d 0x203397a2ac000003f03f 0x520d4825205216141d 0x2390a2a91451451451,sampledPair 0xffffe0007fffff0063 0x7e8b807608003f000fc0 0x604981360464242623 0x36098066085145145145,sampledPair 0xffffffff800000009d 0x8e48e9a5400fc0fc0000 0x800e00380178383815 0xa48c1a54030c30c30c3,sampledPair 0xffffffffffffffffa0 0x49c585ccf7f000000fff 0x9002400980000080 0x48c0050854a28a28a28a,sampledPair 0x91 0x75383e5b400000fff000 0x4e013804e00404080 0x75102e5802cb2cb2cb2c,(0,0),sampledPair 0x4e 0x937660389bffff000000 0x7001c007000808048 0x81362010830c30c30c30,(0,0),(0,0)]
def g95C : List ColumnInfo := [(1,0,94,0,7),(2,0,93,0,7),(4,0,91,0,7),(0,16,74,5,6),(16,0,79,0,6),(8,0,87,0,5),(64,0,31,0,5)]
def g95A : List (List Nat) := [[],[32,99]]
def g95D5 (j : Nat) := if j=0 then 0x4f77159653 else 0
def g95D6 := limbs80 #[#[0xdd8553bd58453be58053,0x59653fdd8553d7d4e53b,0x4018a1141f3185b2c0bf,0x41082628]]
def g95H6 (j : Nat) := if j=0 then 0xc else 0
def g95D7 := limbs80 #[#[0x47888807f94ffaa7fc53,0x2a5474365a891d90ea61,0x190e]]
def g95H7 := limbs80 #[#[0x1020033000a00014000,0x358800000]]
def g95D8 (j : Nat) := if j=0 then 0x468817f else 0
def g95H8 (j : Nat) := if j=0 then 0x38120022000000 else 0
def g95L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g95D5)
  | 6 => (6,2,3,0,0,6,0,g95D6)
  | 7 => (3,1,3,0,0,7,0,g95D7)
  | 8 => (1,0,3,0,0,0,0,g95D8)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 2 0 2 0 0 g95H6
  | 7 => lookupShort 1 19 0 6 3 1 g95H7
  | 8 => lookupShort 1 11 0 5 2 1 g95H8
  | _ => fun _ => none
def g95 : Forest := ⟨95,8,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95B5 : CutRow g95 5 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95B6 : CutRow g95 6 0 6 := (@joinRow g95 6 0 4 2 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95B7 : CutRow g95 7 0 3 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95B8 : CutRow g95 8 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : mixedTables g95 8 := by
  intro k hk
  interval_cases k <;> first
  | exact g95B5
  | exact g95B6
  | exact g95B7
  | exact g95B8
  | exact mixedEmpty g95 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 9 := mixedLower (g:=g95) (i:=0) (hints:=16778291) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 9 [(95,[]),(119,[83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[sampledPair 0xfffff8007fffffc03f 0xd563031b84f000000f0f 0x148154354254148585 0x1163031904d999999999,sampledPair 0xffffff8007ffffc0 0x3acb2d005c4000f0f0f0 0x260260260360190909 0xba4304004c4111111111,sampledPair 0xfffffffff8000000 0x771cc8d99400f000000 0x382b813813815e0e0e 0x6714c8d994777777777,sampledPair 0xffffffffffffffff 0xc8133847ab90f00f00ff 0x400c00400400600000 0x103802830222222222,(0,0),sampledPair 0xff0000000000000000 0x45c463c762f000fff00 0x3001801801801010 0x40c4004302444444444,sampledPair 0 0x33a4d3e0015ffff00000 0x80c006006006002020 0x1808360001888888888,(0,0),(0,0)]
def g111C : List ColumnInfo := [(1,0,110,0,8)]
def g111A : List (List Nat) := [[],[83]]
def g111D8 (j : Nat) := if j=0 then 0x7f else 0
def g111L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g111D8)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,8,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111B8 : CutRow g111 8 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : mixedTables g111 8 := by
  intro k hk
  interval_cases k <;> first
  | exact g111B8
  | exact mixedEmpty g111 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 9 := mixedLower (g:=g111) (i:=0) (hints:=16778803) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 9 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[sampledPair 0x3fffffffffc1f5dac 0x248f2200000000fff03f 0x290290101008405488 0x4852211451451451451,sampledPair 0xfc003ff83fffe0f208 0xe460b98003f03f000fc0 0x30130020809002f008 0x204039030c30c30c30c3,(0,0),sampledPair 0xffffc0003fffff20ce 0x935842c0fc0fc0000fff 0x400401410120000044 0x93080084104104104104,sampledPair 0xffffffffc000000d45 0x6956a9c000000003f000 0x8258258025c0840945 0x695289eebaebaebaebae,sampledPair 0x1171 0x18b1dc3f000ffffc0000 0x6006020601080120 0x830c408208208208208,sampledPair 0xce93 0x4f80057ffff000000000 0x38038043802100e93 0x44800070c30c30c30c30,(0,0),(0,0)]
def g123C : List ColumnInfo := [(0,16,106,1,8),(16,0,107,0,8),(1,16,106,0,7),(2,0,121,0,7),(8,0,115,0,7),(32,0,91,0,7),(64,0,59,0,7),(66,0,57,0,5),(10,0,113,0,4),(34,0,89,0,4),(72,0,51,0,4),(96,0,27,0,4)]
def g123A : List (List Nat) := [[],[83],[97],[97,83]]
def g123D5 := limbs80 #[#[0x54521549414854250521,0xe6759ba6d95495148542,0x9b291652aa95551f27a9,0x3d930c2c9754f0a1614,0x400220b962a50992220]]
def g123D6 := limbs80 #[#[0x54921545215092150521,0xd9121595215912155121,0x50951d854258542d9521,0xd9deeef3f7dbdd7e7f1f,0xab0a9152841f9f5fa7bb,0xaa832aa1628458a9006e,0x13ac84fb283aca09b8ad,0xba8b6ca2cb28e6e22fb2,0xa5baa8aec8db219eea26,0xeae3baaaeeaaa3aabee2,0x16eb23bb58ae903ba30a,0x238f46a2d0f038002bad,0x9345a0cf6733598cb651,0xb6d365b0d76b355a8d36,0x1a4e4238c0df6f375b8d,0x5c223a0408178040e16,0x80a0280800]]
def g123H6 := limbs80 #[#[0x84270000000028,0x52f700471300,0x85830000c6000000,0x4100000048a28200]]
def g123D7 := limbs80 #[#[0x49413fff7eefd5150921,0x1650d901641548542254,0x61750ad6435503614d94,0x521e8a43000d653d85d,0xe33027335988aa491f4d,0x898a3ad192ac98e444b,0x880c8a0a17b4ba8780c5,0x2039ce01dea019e00aff,0x31e6012b3c01cf2048fc,0x1f239327024f0841ce11,0xa58495da9038]]
def g123H7 := limbs80 #[#[0x9180000480000005304,0x800000000,0,0,0,0x31800000000000,0x16f0000000,0x3871bcd474000000000,0xca0060c0000000,0x1950000000000,0xb1e00000000000,0x13200488011c51000000,0,0x3280000000000000,0x2139e89,0xf4280000000000000,0x60000048000,0,0x7004580000b2002a0000,0x18b00002012400000010,0x490000000810000,0,0x45000000000,0x30200000000000,0x14ea126,0x10018d0e000000043000,0x12e00168000000007]]
def g123D8 := limbs80 #[#[0x879aa407f50bfaa3fd21,0x90c3ac69238d145aa324,0x11b4ca4]]
def g123H8 := limbs80 #[#[0x10000000000000052644,0xc1720024002c0049619,0xc0000d60000808a71000,0x4000,0x700004e0000000,0xa28d8800c600030,0xc5ede8cb00c20]]
def g123D9 (j : Nat) := if j=0 then 0x1654321bf else 0
def g123H9 := limbs80 #[#[0xac000000600840500000,0x4]]
def g123L : Nat → Packing
  | 5 => (9,4,4,393220,50,7,1025,g123D5)
  | 6 => (30,3,4,851980,68,9,1033,g123D6)
  | 7 => (15,2,4,262147,34,9,1047,g123D7)
  | 8 => (3,1,4,0,0,7,0,g123D8)
  | 9 => (1,0,4,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 3 41 0 8 4 2 g123H6
  | 7 => lookupShort 11 239 2 9 5 2 g123H7
  | 8 => lookupShort 6 67 2 8 4 2 g123H8
  | 9 => lookupShort 1 17 0 6 2 2 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123B5 : CutRow g123 5 0 9 := (@joinRow g123 5 0 2 7 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x220280e8a2,0x21200400820028c02832,0x400220028c022320102,0x20180900a4308008100,0x28c04832004082012084,0xa430800204028904232])) rfl
      decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123B6 : CutRow g123 6 0 30 := (@joinRow g123 6 0 3 27 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g123 6 3 5 22 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x10200108814,0x28420040004120144261,0x1020010881428420040,0x820120840a2100408100,0xa0440a2100220281c0a2,0x21400040820120840a21,0x408100a0440a210040,0x8100a0440a2101002100,0x88500a61040000110844,0x606400408100a0440a21,0x220281c0a221300400,0x820120c0285304040041,0x20506043004082012084,0xa510044004120144241,0x8002100a0c042430022,0x281c0a2213001020010,0x88142831010022010890,0xa510104001108144841])) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123B7 : CutRow g123 7 0 15 := (@joinRow g123 7 0 9 6 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g123 7 9 5 1 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => 0x220281c0a22140) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123B8 : CutRow g123 8 0 3 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123B9 : CutRow g123 9 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : mixedTables g123 9 := by
  intro k hk
  interval_cases k <;> first
  | exact g123B5
  | exact g123B6
  | exact g123B7
  | exact g123B8
  | exact g123B9
  | exact mixedEmpty g123 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := mixedLower (g:=g123) (i:=0) (hints:=16777267) (before_sound K111 V111) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K111 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V111 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[sampledPair 0xffffff83fffff242e8 0x44f46d0000000fe03fff 0x80a4010808040240a0 0x4444d42850a142850a1,(0,0),sampledPair 0xffffc1ffe06b488 0xfcbc20003f8001fc000 0x12c08a00410822b088 0x78b40162c58b162c58b,sampledPair 0xfff000001ffffbd84e 0x91211a01fc07f000007f 0x3002c10805001804c 0x1121120c183060c18306,sampledPair 0xffffffffe0000804f6 0x691ab3000000001fff80 0x240930001260480456 0x6810b2a952a54a952a54,sampledPair 0x91711 0xa28774fe0007ffe00000 0x3801c0210380881601 0xa282203060c183060c18,sampledPair 0x4e917 0x7e4005fffff800000000 0xc00e00421c01044912 0x484005c183060c183060,(0,0),(0,0)]
def g125C : List ColumnInfo := [(1,0,124,0,7),(4,0,121,0,7),(8,0,117,0,7),(16,0,109,0,7),(32,0,93,0,7),(64,0,61,0,7),(0,4,41,80,6),(0,16,104,5,6),(1,16,104,4,5),(4,16,104,1,5),(17,0,108,0,5),(20,0,105,0,5),(64,4,41,16,5),(68,0,57,0,5),(5,0,104,0,4),(5,16,104,0,4),(9,0,116,0,4),(12,0,113,0,4),(33,0,92,0,4),(36,0,89,0,4),(40,0,85,0,4),(72,0,53,0,4)]
def g125A : List (List Nat) := [[],[83],[96,66],[96,66,83]]
def g125D5 := limbs80 #[#[0x50940483aa5954250120,0x30eab65]]
def g125D6 := limbs80 #[#[0x50920505205012050910,0xd9120595205912054120,0xd8142d9121d8121d9520,0xfb77b7d7dfa7f2fd8950,0x6e8d0a10febd7eaef6,0xa1236ca2cb28a6c605b8,0x8db2232c88eaa256e494,0xca6ab29caa867b2116e8,0x2ee4c2bab8eeaa2baaae,0xa60ae903ba31ee8c63a3,0x2bad8ae142ba48ee982b,0x98887868584838281800,0x39291908f8e8d8c8b8a8,0x85c9b9a9998979695949,0x8ce0900]]
def g125H6 (j : Nat) := if j=0 then 0x1000080007000020 else 0
def g125D7 := limbs80 #[#[0xedd50509314c12148110,0x5aa05a8046c63fffbeef,0x8eca4aca4ec84ac85284,0x62840ec14ec88ec08ec5,0x62a862c2628522a26282,0xa2c5a285a284e2ca62c8,0x962f0c0022c362c166c5,0x3659117b355829f4099c,0x671379b4d66931b79b35,0x10640386f6793b9d4e,0xc3242322208512a48432,0x5114ae54e0b0c6c4442,0x24b672c4a2c6931d8d00,0x92fc49262c719272c3,0xdfff5400abfd0009d7bc,0x47233229f87080a17801,0xfb6110be7b204ebdc491,0x15b418c3c18bb8314]]
def g125H7 := limbs80 #[#[0x2040c8,0x4800000000000,0x14000000000001100,0x2602c00000000115,0x8a003d6,0x62c,0x7e120200000022600000,0x7000000000c1800018a8,0x59c00603040000000018,0x112000000001240d8002,0x23800000000000000000,0x3880000000011900,0x1a460000000006340000,0x225717000020d,0x14a0000000]]
def g125D8 := limbs80 #[#[0xd21fea87f4c3fa41fd10,0xd210c024007f50bfa63f,0x10882640e230f161cea5,0x2259222891464009648e,0x98c23071648a3221300,0x18040899222cc2059018,0x1c65258e]]
def g125H8 := limbs80 #[#[0x420000020014,0x78300000000000000000,0x49c28000000564c,0xc00000000087d1,0x11265800000000,0xad0c0030a00,0x3700000,0,0x1cc006440000000,0x304000000112000,0x4e00000005800400000,0x28000000,0x3800000000,0x9b800015400,0x8f10002a00002880000,0x29986004c8000d,0x13280000003470b00000,0x1b60000001160ba,0x1f03100680000000]]
def g125D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g125H9 := limbs80 #[#[0x20004400000000403600,0xc40600001a4301400008,0x25000000000,0x48000000006400000000,0x1c000002600000000167]]
def g125L : Nat → Packing
  | 5 => (2,4,5,0,0,3,0,g125D5)
  | 6 => (29,3,5,720909,68,8,1028,g125D6)
  | 7 => (26,2,5,327687,51,9,1059,g125D7)
  | 8 => (7,1,5,0,0,9,0,g125D8)
  | 9 => (1,0,5,0,0,0,0,g125D9)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 17 0 4 1 1 g125H6
  | 7 => lookupShort 8 127 3 9 5 2 g125H7
  | 8 => lookupShort 11 167 2 9 5 2 g125H8
  | 9 => lookupShort 3 59 0 7 3 2 g125H9
  | _ => fun _ => none
def g125 : Forest := ⟨125,9,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125B5 : CutRow g125 5 0 2 := (by
      apply polarBlock (data:=fun _ => (w80 [0x810209448a,0x141000810209448a1410])) rfl
      decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125B6 : CutRow g125 6 0 29 := (@joinRow g125 6 0 2 27 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x810209448a,0x143104830209448a3431,0x210120d04a11300081,0x209448a143100810209,0x448a143100810209448a,0x143100810209448a1431,0x810209448a14310081,0x209448a143100810209,0x448a142100810209448a,0x143100810209448a1431,0x810209448a14310081,0x209448a142100810209,0x448a142100810209448a,0x142100a04060b01a2560,0x810209448a14200081,0x209448a142000810209,0x448a142000810209448a,0x142000810209448a1410,0x810209448a14100081,0x209448a142000810209,0x448a142000200060701a,0x11600180412094580d61])) rfl
      decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125B7 : CutRow g125 7 0 26 := (@joinRow g125 7 0 12 14 (@joinRow g125 7 0 1 11 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)) (@joinRow g125 7 12 4 10 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x210060701a11300081,0x209448a143100810209,0x448a143100810209448a,0x143100810209448a1431,0x8400c1603844510081,0x209448a143100810209,0x448a143100810209448a,0x143104040029144a6054])) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125B8 : CutRow g125 8 0 7 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125B9 : CutRow g125 9 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : mixedTables g125 9 := by
  intro k hk
  interval_cases k <;> first
  | exact g125B5
  | exact g125B6
  | exact g125B7
  | exact g125B8
  | exact g125B9
  | exact mixedEmpty g125 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 10 := mixedLower (g:=g125) (i:=0) (hints:=33555459) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 10 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0,0),sampledPair 0x3fffffc1ffff60ac8 0x4caee8000007f01fc07f 0x280280084044060880 0x400ce80a142850a14285,sampledPair 0xfc003ffffffe021c2c 0x13d9d30003f800003f80 0x304b04500208221c28 0x3c941264c993264c993,sampledPair 0xffffc0001ffffbf0cb 0x81210b01fc000fe0007f 0x400c0160809009404a 0x12103142850a142850a,sampledPair 0xffffffffe0000824f7 0x691ab200000000003f80 0x8290298014e04820d7 0x6812b2d9b366cd9b366c,sampledPair 0x93710 0xa28774fe00000fffc000 0xe00e010700803700 0xa2821060c183060c1830,sampledPair 0x4c917 0x7e4005fffffff0000000 0x30030021801008015 0x1c000481020408102040,(0,0),(0,0)]
def g126C : List ColumnInfo := [(0,16,106,4,8),(16,0,110,0,8),(2,0,124,0,7),(4,16,106,0,7),(8,0,118,0,7),(32,0,94,0,7),(64,0,62,0,6),(10,0,116,0,4),(34,0,92,0,4),(40,0,86,0,4)]
def g126A : List (List Nat) := [[],[83],[49],[49,81],[81,49],[81]]
def g126D4 (j : Nat) := if j=0 then 0x1a2b6460b5454120 else 0
def g126D5 := limbs80 #[#[0x54120549404814250120,0xb6970d5120d515048152,0x3caa1f2baae6b8ed6b2e,0x28b224ba9bb28ab280c1,0x404003b247b235ba29b2,0x244070c142030]]
def g126H5 (j : Nat) := if j=0 then 0x3 else 0
def g126D6 := limbs80 #[#[0x59120551205412050120,0xd9120d51209952059520,0xd49505895054950d9520,0xeb7d7e7f2f58b50d8950,0x420fd7abbddadf6bf3f7,0x6d521b54803744854869,0xc15370445c1a75419550,0x7d941d65025d2d370945,0x524dd05f64175906f721,0x56566d918776215d8956,0x10f74415d5c775315d99,0x5d9477446dd1187447dc,0xa5d92d76499dc2457481,0x21f07800774d15d30f74,0xd0e7a37184a84c220d85,0xb3d8ebf5babd4e9f4ba3,0x8bc3e0eff7bbbdcedf6b,0x5fabd3e8f3f9bcbe4f1f,0x38411cc2820c92171e1,0x6020d04026304600a0,0xda0d90cd0568200]]
def g126H6 := limbs80 #[#[0x8000000059a4e3500a00,0xa800000f08000006289,0x13800000000000290004,0xd2000000402880002100,0x4380020041,0x790000]]
def g126D7 := limbs80 #[#[0x9403fffb7eff5054120,0x5524d941650d90164254,0x653d50d54058a3625d49,0x3590f627589d527994d,0xa28f86e2e9307a260a0,0x79747a1efc7436586b25,0x450230085915531ce218,0xadc8025640612e07d49,0x4950054411cc08620648,0x87dc033e011aa09780,0x2d88cf01bc9052f8247]]
def g126H7 := limbs80 #[#[0x3046404d489042b00c00,0x400102c0000000000042,0x726c0d2031100000022,0x23101700011a42c1dd,0x68f50c00187819038,0x3600326408d1a00,0xf00098f2b007027a840,0x92003402800001818002,0x93480000080400110800,0x8800000c2b2300000002,0x8ad9821c0040ec318,0xe0cdae09b6281058e000,0x943e00202200c2435022,0x2c0012680083c8940008,0x42f29620c8680661c118,0x4a24a308f05000c13]]
def g126D8 := limbs80 #[#[0xc79aa407fd43faa1fd20,0x98d13568298d131ea414,0x1ad046]]
def g126H8 := limbs80 #[#[0x60000000000148602,0x2e00400000000,0x10c003400,0x40000321ca40082d020,0x15280c00000226000005,0xa8000000f410470000d0,0x220700000c90001,0x20e000000031040e2f0,0xa002090,0x18700000003270,0x300dac11000000]]
def g126D9 (j : Nat) := if j=0 then 0x1542317f else 0
def g126H9 := limbs80 #[#[0x3190a6200200418a0803,0x92]]
def g126L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g126D4)
  | 5 => (10,4,4,458757,51,7,1024,g126D5)
  | 6 => (39,3,4,786446,68,9,1036,g126D6)
  | 7 => (18,2,4,262147,34,9,1040,g126D7)
  | 8 => (3,1,4,0,0,7,0,g126D8)
  | 9 => (1,0,4,0,0,0,0,g126D9)
  | _ => emptyPacking
def g126I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g126H5
  | 6 => lookupShort 5 53 3 8 4 2 g126H6
  | 7 => lookupShort 18 107 5 11 6 3 g126H7
  | 8 => lookupShort 8 83 3 10 5 3 g126H8
  | 9 => lookupShort 2 13 2 7 2 3 g126H9
  | _ => fun _ => none
def g126 : Forest := ⟨126,9,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126B4 : CutRow g126 4 0 1 := (by
      apply polarBlock (data:=fun _ => 0x810200e85c1410) rfl
      decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126B5 : CutRow g126 5 0 10 := (@joinRow g126 5 0 2 8 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x1000201,0x8d42851010000108814,0x28510044010180440a43,0x408100a0440a430400,0x20402850223204002200,0x28c02232008401816868,0x44200800204028904232])) rfl
      decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126B6 : CutRow g126 6 0 39 := (@joinRow g126 6 0 3 36 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g126 6 3 9 27 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x10401018050,0x48520042020180842240,0x1000010881428620044,0x1018044425000440101,0x80444250040020412050,0x224300840181c0684451,0x40820120840a200040,0x8100a0440a2000408201,0x20840a20004082012084,0xa200100220108900a61,0x8000010888460640040,0x8100a0440a2000408201,0x20840a20004082012084,0xa200040820120840a20,0x400040a01422600404,0x110844605400408100,0xa0440a20004082012084,0xa200800210088c04254,0x100210088500a510102,0x108814283104008201,0x8c0284200840181c068,0x44400104001108144841])) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126B7 : CutRow g126 7 0 18 := (@joinRow g126 7 0 10 8 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g126 7 10 7 1 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => 0x840181c0684451) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126B8 : CutRow g126 8 0 3 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126B9 : CutRow g126 9 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : mixedTables g126 9 := by
  intro k hk
  interval_cases k <;> first
  | exact g126B4
  | exact g126B5
  | exact g126B6
  | exact g126B7
  | exact g126B8
  | exact g126B9
  | exact mixedEmpty g126 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 10 := mixedLower (g:=g126) (i:=0) (hints:=17962032) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 10 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[sampledPair 0xff000ffffff80fe5f3 0xf07c7c000040675b 0x2a06a04a02916285f1 0x249108484000000211b,sampledPair 0xfffff000fffff019b8 0xa00700038061898794a7 0x4c24c26c232244d9b0 0xab595294942008821407,sampledPair 0xffffffff0000000545 0xb0380f8000020e3818c3 0x700700700bc3870545 0xb6cb318d8c020a1000c3,sampledPair 0xffffffffffffffea2b 0x81c00003ff83f03fe0f5 0x804804804c0000020a 0x4a6a5292a8aa23cc0e0,sampledPair 0x480 0x7e000ffc03fc003fff02 0x7007007004080000 0x4934c630332820a75e24,(0,0),(0,0),sampledPair 0x1354 0x4ffff00003ffffc00008 0x8008008000000000 0x842405145400000,(0,0)]
def g159C : List ColumnInfo := [(1,0,158,0,8),(2,0,157,0,7),(4,0,155,0,7),(8,0,151,0,6),(16,0,143,0,6),(9,0,150,0,5),(10,0,149,0,5),(12,0,147,0,5),(18,0,141,0,5),(20,0,139,0,5),(128,0,31,0,5),(11,0,148,0,4),(14,0,145,0,4),(22,0,137,0,4),(130,0,29,0,4),(132,0,27,0,4)]
def g159A : List (List Nat) := [[],[33,67]]
def g159D4 := limbs80 #[#[0xa9a878e1826057019543,0xc3326e8c00e2]]
def g159D5 := limbs80 #[#[0x58053dd95314d6454c53,0x4c5535885354d6114d53,0x5c06550d535454154d51,0x54d431c55350d7119543,0x90d7018553dc16550f71,0xdd953d0574d473154d62,0x5935154d43d455458f41,0xc7b1dbd279dc964d4f72,0xd9756d573cce735ccf27,0xb009f17b4ec7a5e8f95,0x704e62c8546c8c43027,0x4ee316f0502286f8a866,0x52a6730eca5ee893aa32,0x4102b12a681aa671aca7,0x370e3870227f02d4702b,0x42c8c3702176e207f024,0x231b1109002ca732aa73,0x736b635b534b433b332b,0xc3bbb3aba39b938b837b,0x20200016308d3cb]]
def g159H5 (j : Nat) := if j=0 then 0x20c0 else 0
set_option maxRecDepth 32000 in
def g159D6 := limbs80 #[#[0x58853584535805354c53,0x54d31545315452159053,0x99531595315913155131,0x5514154d415454150d41,0x54d43195439954159541,0xd4d439954394d4359543,0x54d5150d51d9543d8543,0x18553d9151d8d51d4551,0xd4d53951535515319153,0x54e43d9153d8953d8553,0x95253d524358a4355243,0x5533154f3150731d4e53,0xd4731997315973159331,0x58f415534154f4150f41,0x54f5150f519974159741,0x58b53587535935158f51,0xdedf3f9f4f6773759353,0xaecf5fa7cfdfafb7cbdd,0x7eef5fabbedeeef6fb6d,0xdc4555530df9fafb7d7e,0x9eb1546e1dc885553662,0xf702825c490d70241dc,0x5305054c0b953522dc4a,0x3e0dd80316400e54c1bd,0x35956e9545a1dca02170,0x4c6b5645f15917257467,0xd595375654cd13766b75,0xc71265dd09b56475158d,0x42b89509e15427bdc49e,0xea5c0915742e65d4ae25,0x59036d530dc5482cf643,0x41f721115903ef710f3],#[0xcf71124dd84117610d59,0x74164dd054f71144dd44,0x67b54d9a6755bb54d691,0xbdc574d766735959ed73,0xd9791765e7dc97a7715f,0x91374633dc589375604d,0x9541b7d4c6e9431a45d1,0x518d5946615319adc466,0xe4dd8727711c5dd46157,0xdc4817731f9dc87eb711,0xda1173224dcc84b72213,0x97756855d5a356569854,0x536e45d9ac5636a9dc5a,0x6f11d5b93756ed551bc7,0x9dc9b47756f19d5bc575,0x4ce1173724dcdc17736d,0xd47633495d0e25733975,0x1733c45d0edf71364dd8,0x1764dd9d1176749dc5d1,0xb2dc9e9374793dc5e5f7,0x5d4c355431154cc13737,0x89af6526b1949a771264,0xe3742781d099b722645d,0x762b11d89db652761949,0x24b5949257124bd94b9a,0xbd94a277128adc0a1276,0xc4a4f712931c4a537028,0xb2f652c4dcca4773284d,0xb54532551491713245cc,0x3507dc9447764fbdc53c,0x465cd52e6550b59541b7,0x550152540345500ad655],#[0x404a540725501ce54053,0xb654091dd80456401bdc,0x62493589226763f3590f,0x49bdcd24f6349bd4d24f,0x3d9124e6449359124c64,0x4924d524845d124d5149,0x24f73493dc924d72493d,0xf5449395124d54493151,0x44939d124d744931d124,0x265d1191744b25492cf7,0x591037644465cd11b734,0x1611724c45c5336644cd,0x91747d3505f19735665d,0x4180d506011747f2509f,0x80dd0a03542804dc6037,0x40001372812dca04872,0xc3586009e10017826032,0xf8b51562844b8860f81c,0x1c2163f47a8ed1bc3545,0x2fc5c0ae1512884dc941,0x8784e99c43786b0cb98a,0xa91121a424829011fa3d,0x3125a4a49292123a4648,0x29a524a294127a4e49a9,0xa5a4b29612ba564aa951,0x24c29812fa5e4ba9712d,0xd29a133a664ca99131a6,0x9c137a6e4da9b135a6a4,0x13ba764ea9d139a724e2,0xfa7e4fa9f13da7a4f29e,0x8650aa1141a82502a013,0x51aa3145a8a512a2143a],#[0xaa5149a92522a4147a8e,0x714da9a532a614ba9652,0x51aa2542a814fa9e53aa,0xaaa552aa153aa654aa91,0x2562ac157aae55aab155,0x72ae15bab656aad159ab,0xb015fabe57aaf15daba5,0x163ac658ab1161ac2582,0x7ace59ab3165aca592b2,0xd65aab5169ad25a2b416,0x5bab716dada5b2b616ba,0xab9171ae25c2b816fade,0xb175aea5d2ba173ae65c,0x370f25e2bc177aee5dab,0xd122840e1180c40e0828,0x34649900454a08b0a3c4,0x15c221c21005806017a0,0x4012e90802008020258a,0x17488027c1920040100,0x9a0c942b21dca116c200,0xd06c863619a943a43341,0x39b0ee42001e421ae21e,0x3b6160]]
def g159H6 := limbs80 #[#[0x60040,0x4f0000008a00828000,0,0x5a4e00002100000000,0xec0000000000001100,0x59920000000000000000,0x95160000000000d00900,0x83000000848d,0x870000300000000000,0xb000000000094000c,0x8697,0xd83100000000000048,0xaec10093000500000000]]
set_option maxRecDepth 32000 in
def g159D7 := limbs80 #[#[0x54d5150d414c52114c43,0xbb7afd4f51d073194e43,0x63bfffdf7efdfbfbebdb,0x4d611458049628198ec5,0x448f6170990416412588,0x854ce551359949565295,0x1a9506966535594d5643,0x665a55969564a854ea75,0x51565475511d43495451,0x596dd54b558edd43b599,0x6654d976269d459665b5,0x53c558b176465d8d9b53,0x1565055931563c6d4f19,0x9562535854d576155994,0x854e1765559955565551,0x41854c56658559615648,0x76179d85e46175994556,0x2635395d91e35375d89d,0x5935562d558755659559,0x6a54ee9534a552a95435,0x655ad4d69535a50f2943,0x29548ad956a655a59568,0x91e8647a951e9547ad52,0xad4d2b54aad50ea549ad,0x36a54da9626a549ab53b,0x963ca54f29646a551a96,0x6b615a5856964ca5532,0x589eb617a585ea541a55,0x7a591eb547ad4deb627a,0x800a9936964dad526a64,0xc0fc1c03105407809009,0x163e0748d918e2c85008],#[0x61cbb1632a44f89511b2,0x9051f73ca74ce11b0330,0x329650c9d12f24846687,0x1a610be575adc590ad95,0x73ee2db9364692cd9943,0xb03e00bf37caf5de4bb2,0x7a43c738c91561f42b83,0x8b5039d9362644ba9592,0x58db055b6ae54ba754ae,0x7c2f80af6dd6b956fed4,0xdd99b2f656c9d90b1b62,0xa9b4f696d1da1b3f676c,0xb6f6d6d9db1b5f6b6d5d,0xf716e1dc1b7f6f6dddb9,0x138c1870ca130e5dc9b8,0x890ca39c249124f20136,0x78c111d8087708d3164,0xcc042810a04281178511,0x1b7408d3e054f8122e10,0x37008780876091d019f0,0x43d0486e04958435984,0x8233b08e752111d00aec,0xb9824b9846f9022ec087,0xbc247bc814cc84861c24,0x43c043e033e034f812e,0x11c023406e80c9b09176,0xf80131d8243010c047c8,0x384777846eb74072014c,0xa602100a402d9e0253,0xfc24a5848402900a5021,0xb3904a74848f00de0196,0x6cc090f0108053010a04],#[0x3dc8467a24bec4777009,0x1023e1123c410ea087a2,0x24103602237110c3e113,0x84744673a245e221ddfa,0x502103dc]]
def g159H7 := limbs80 #[#[0x439110903000905011e,0xb0900010003063e0702,0x6071325032106040052,0x1e120045150400260b08,0x8801131f0303001a0204,0x32100300661b0006cbd5,0xd669e7c016d371c5400,0xa3162db021a85fa51078,0x718644dde23b65f90f16,0x2771e2380003f934000c,0x194829c57b0629b650,0x68d302495e7acb00044e,0x6234ed4000311498288b,0x44a8d0ba00321f4b6941,0xc6441600160c468f4b57,0xb201f548ecc85d03052,0x199f2a860d960032000,0x82b918000019c5a8b490,0x16348f27811d96c1f447,0x40d088bd606ce1e11723,0x825620000062945e1085,0xc734bc67f9a00180c007,0xf96731a82d732622829f,0x870c2d60000035bcb8da,0x4bb001c9161d9d16c4,0x615b339268e80086e000,0x100000349207039c2400,0xac2b3a82a30018422421,0x635373c7c3a1ddbd8000,0x31002cc9725b4da6642c,0x338e7abd486a481da0,0x4a5a5a804280055d1e40],#[0xb2288718c7b9119b04ca,0xd2a65957c00de5135f64,0x242f03d8f09ff26aa107,0x64c9e89facc000656af0,0x800726002126c8539af0,0xe184ab4004228541f90b,0x1eaf41900096ba18007c,0x6c000008609d583e54c,0xf5d1c6000834004cd1b1,0x90ce69ea5162ec787725,0xbc8e1864006a2d801113,0x14e9d0000088041be30d,0xaad158641e5c0d80069d,0x714244cda2015b5cbe84,0x5506d0018e04521a7151,0xe3acd1b6a090abd02d8c,0x105109c8370a0af00]]
def g159D8 := limbs80 #[#[0x7a8aa3a0a8398a6290ff,0x7806a729aa629c86a188,0xe53c9c13a30a79f178f8,0x9ee4a1a72182c86be4d,0xc811b01ad023e01bc035,0x29f0106047700adc02b,0xf6028c088043e103be3]]
def g159H8 := limbs80 #[#[0xe4070e0040305060d600,0xa8c80731029308541000,0x81083618a002205a8006,0x6b4868009b19c00041a0,0x13980009107f2919eb4,0xcdd20000882a7cc4522a,0x35c00646009ea000b157,0x80093e9123e34000d600,0xa51a500000041348001e,0x89f9bc27b780083abfcd,0x65e2a800000ba36a2fab,0x5b0f0011700120ce3a6,0x6cc0061ca8000f1dae00,0xc81d0010886400,0x639818edf90018aa4231,0x69cb0d3ca6dd285cb64e,0xae0764569a001e641401,0x66b091131c07cb983f99,0x47200001ba0012b00000,0x431a2aeb73c4a006a304,0x801a48bccd7b61d9b836,0x20d02c1fb29d55869731,0x1d6000ce66c08988018a,0xf92ead90a1689a180195,0xc3a002799251d3be8dac,0x4b8b9001b04584ca368c,0x1a8b50010b4018600013]]
def g159D9 (j : Nat) := if j=0 then 0x2100ff else 0
def g159H9 := limbs80 #[#[0xe90003500db6c2005084,0x864000653400000b8011,0x18b673020300016d136,0x7725172d9395]]
def g159L : Nat → Packing
  | 4 => (2,5,4,0,0,3,0,g159D4)
  | 5 => (27,4,4,1179668,85,8,1026,g159D5)
  | 6 => (219,3,4,1900609,87,11,1048,g159D6)
  | 7 => (120,2,4,720910,68,11,1049,g159D7)
  | 8 => (14,1,4,65537,0,8,1037,g159D8)
  | 9 => (1,0,4,0,0,0,0,g159D9)
  | _ => emptyPacking
def g159I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 5 0 3 1 0 g159H5
  | 6 => lookupShort 8 127 3 8 5 1 g159H6
  | 7 => lookupShort 66 307 8 11 8 1 g159H7
  | 8 => lookupShort 37 191 7 10 7 1 g159H8
  | 9 => lookupShort 6 37 5 7 4 1 g159H9
  | _ => fun _ => none
def g159 : Forest := ⟨159,9,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159B4 : CutRow g159 4 0 2 := (@joinRow g159 4 0 1 1 (by
      apply checkedRow
      apply cellsBlock (ar:=5) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => 0x81040221081420) rfl
      decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159B5 : CutRow g159 5 0 27 := (@joinRow g159 5 0 3 24 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x200,0x4021120144202000402,0x11201442018184024108,0x1c2000210060701a1120,0x210060701a11400021,0x4024102111000210060,0x701a1120008104024108,0x14100021040241021110,0x301240209101a510100,0x4020510094100210060,0x701a1130020010603438,0x114302480060701c8230,0x880090682c84510021,0x60701a112000210402,0x21021130002080906826,0x91000212060701a1320,0x208090682609300021,0x4022102115000612402,0x21021350020004020920,0x145200612060701a1320])) rfl
      decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159B6 : CutRow g159 6 0 219 := (@joinRow g159 6 0 87 132 (@joinRow g159 6 0 18 69 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g159 6 18 21 48 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x612402,0x41021350006124022102,0x135000210060701a1140,0x181840241081c420020,0x80906826092000208090,0x68260920018184024108,0x1c520020840221020920,0x208090682609200108,0x120814885301080012,0x8148842018184024108,0x1c520108009208148843,0x4800c2201482410061,0x24022102135000280092,0x48268130002084022102,0x9200020809068260920,0x181840209081c410020,0x80906826093002418402,0x21041a3100210060701a,0x11300241840221041a31,0x208090682609300241,0x840221041a3102000402,0x11201463002124024102,0x13300021040241021120,0x210060701a11300021,0x60701a113000210060,0x701a112000210060701a,0x112000210060701a1130,0x100080c0693088430020,0x80906826093002418402,0x21041a3100210060701a,0x11300040840221040a31,0x280092482681400020,0x80906826093000408402,0x21040a3100612060701a,0x13500200040211201463,0x612060701a13300021,0x4024102112000612060,0x701a133000210060701a,0x11200020809068260910])) rfl
      decide +kernel
))) (@joinRow g159 6 87 48 84 (by
      apply polarBlock (data:=fun _ => (w80 [0x280092,0x40268140018184024108,0x1c420028008240228140,0x210060701a11300028,0x906826815000280090,0x68268150002104022102,0x11400021040221021140,0xa0c40221020d500241,0x840221041a3101818402,0x41081c4200210060701a,0x11401000004029108264,0x612060701a13400061,0x2060701a136000612060,0x701a1330018184024108,0x1c420020809068260920,0x1080092483488530021,0x60701a113000210060,0x701a1130002800924826,0x81500181840241081c42,0x212060701a13300021,0x60701a114000208090,0x6826093000210060701a,0x11300061240241021340,0x480042201482410020,0x80906826092000210060,0x701a113000210060701a,0x113000210060701a1140,0x208090682609300181,0x840241081c5200208090,0x6826092000612060501a,0x133000612060501a1330,0x612060501a13300061,0x2060501a133000612402,0x4102134000612060701a,0x136000612060501a1330,0x612060701a13400061,0x2060701a133001000402,0x9100a62024084022104,0xa310240840221040a31])) rfl
      decide +kernel
) (@joinRow g159 6 135 48 36 (by
      apply polarBlock (data:=fun _ => (w80 [0x1000402,0x9100a52018184024108,0x1c4200210060701a1130,0x301040209101a520100,0x40209100a5203010402,0x9101a52010004020910,0xa5200210060701a1120,0x210060701a11300021,0x60701a112001804402,0x9100e5200210060701a,0x113000210060701a1130,0x181840241081c310020,0x80906826093000210060,0x701a1130002080906826,0x95000210060701a1120,0x208090682609200020,0x80906826092000208090,0x68260920002080906826,0x920010010904c340952,0x10010904c3409520021,0x426012114000210402,0x61021130002080906826,0x9300241840221041a31,0x218402410219300200,0x4021120146300210402,0x41021130002104024102,0x11200021004070121130,0xa08090682609200028,0x924826815000210060,0x701a1140010000924834,0x88630181840241081c42,0x241840221041a610061,0x2060701a134003012402,0x9101a62018184024108,0x1c310241840221041a20,0x1080092483488631000,0x402910826410000040,0x25108164024184022104,0x1a3102480060701c8241])) rfl
      decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x20809068260930,0x208090682609200020,0x80906826092000208090,0x68260930002080906826,0x9300020809068260930,0x208090682609300020,0x80906826093000208090,0x68260930002080906826,0x9200020809068260930,0x208090682609200028,0x826022814000208090,0x6826095000210060701a,0x11400040840221040a31,0x218402210219300181,0x90282c143202418402,0x21041a31018184024108,0x1c320181840241081c32,0x2080906826095000a0,0xc09068260d3000210060,0x701a1130010800020814,0x88420100040209100a52,0x181840241081c310100,0x40209100a5201000402,0x9100a52010004020910,0xa520100040209100a52,0x100040209100a520021,0x60701a113000210060,0x701a113000210060701a,0x11300100040209100a52])) rfl
      decide +kernel
))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159B7 : CutRow g159 7 0 120 := (@joinRow g159 7 0 57 63 (@joinRow g159 7 0 9 48 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=3)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)) (@joinRow g159 7 57 15 48 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g159 7 72 19 29 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x20,0x80906826093000208090,0x6826093000210060701a,0x11400181840241081c42,0x181840241081c420021,0x60701a114000210060,0x701a114000210060701a,0x114000210060701a1140,0x210060701a11400021,0x60701a114000208090,0x68260930002080906826,0x9300028009248268150,0x280042201281500020,0x80906826093000208090,0x6826093000210060701a,0x114000210060701a1140,0x208090682609300020,0x80906826093000210060,0x701a114000210060701a,0x11400020809068260930,0x208090682609300020,0x80906826093000208090,0x6826093000210060701a,0x114000210060701a1140])) rfl
      decide +kernel
))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159B8 : CutRow g159 8 0 14 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159B9 : CutRow g159 9 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : mixedTables g159 9 := by
  intro k hk
  interval_cases k <;> first
  | exact g159B4
  | exact g159B5
  | exact g159B6
  | exact g159B7
  | exact g159B8
  | exact g159B9
  | exact mixedEmpty g159 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 10 := mixedLower (g:=g159) (i:=0) (hints:=1075) (before_sound K126 V126) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K126 10 [(159,[]),(183,[83]),(215,[32,16,67,99,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V126 low159 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[sampledPair 0xe03ffff800fffffe03 0xfed3aa41320000f00f0f 0x458a01506a0940a458 0xa6530a40321111111111,sampledPair 0xffc07fffff001ffffc 0x34e5bc281000f00f0f0 0x891302604c0d80c891 0x334e1a42011111111111,sampledPair 0x7fffffffe00000 0xd372be2500f0000000 0xe1c2b82704e0af0e1 0xc0d372be257777777777,sampledPair 0x7fffffffffffff 0xf922299d6b0f000f00ff 0x10200c008010030000 0x20218d082222222222,(0,0),sampledPair 0xffff80000000000000 0x98c67ad8f0000fff00 0x300300600c0102 0x80c430c04444444444,(0,0),sampledPair 0 0x665142404fffff00000 0x40040080100000 0x8888888888,(0,0)]
def g175C : List ColumnInfo := [(1,0,174,0,8)]
def g175A : List (List Nat) := [[],[83],[16],[16,83]]
def g175D8 (j : Nat) := if j=0 then 0x7f else 0
def g175L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I (_ _ : Nat) : Option (Nat × Nat) := none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175B8 : CutRow g175 8 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : mixedTables g175 8 := by
  intro k hk
  interval_cases k <;> first
  | exact g175B8
  | exact mixedEmpty g175 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := mixedLower (g:=g175) (i:=0) (hints:=1843) (before_sound K159 V159) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K159 9 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V159 low175 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[sampledPair 0xfffc01ffffffff0ffa 0x8a08b0800007c00ffc1f 0x28140500800220ca 0x2003084210842108421,sampledPair 0x1ffffe007fc3fff05d 0x22c7098000f801f003e0 0x413018260108240259 0x207098c6318c6318c63,(0,0),sampledPair 0x1fffffff8003ffff20 0xf2615e001f003e0003ff 0x824020080a10480020 0xe0604210842108421084,sampledPair 0x1ffffffffffc000010 0xad8c6f83e00000007c00 0xb8140b02c01704410 0xad8c4f39ce739ce739ce,sampledPair 0xe0000000000000000e 0x11ba877c00003fff8000 0xc0180c03021808804 0x11988421084210842108,(0,0),sampledPair 0xc1 0x4514407fffffc0000000 0x100201004002000000 0x42108421084210,(0,0)]
def g187C : List ColumnInfo := [(1,0,186,0,8),(2,0,185,0,8),(16,0,171,0,8),(8,0,179,0,7),(32,0,155,0,7),(128,0,59,0,7),(0,16,42,129,6),(24,0,163,0,5),(40,0,147,0,5),(128,16,42,1,5),(136,0,51,0,4),(160,0,27,0,4)]
def g187A : List (List Nat) := [[],[83]]
def g187D5 (j : Nat) := if j=0 then 0x2f1e057454932 else 0
def g187D6 := limbs80 #[#[0xb67b22a49974d5454932,0x29eee2b2a85cb5515250,0x4b7bb8acaa17cd745493,0x471eda9652017ddc5645,0x2d03f011a0ae22780b61,0x2c98f970104f1e0204e,0x41622]]
def g187H6 (j : Nat) := if j=0 then 0x3 else 0
def g187D7 := limbs80 #[#[0xfefdfcf7efedd5250932,0x55262a80d900b20d523f,0x226019648ec925522b2b,0x2a158e11cfcd0ae84684,0xf403222aa387a1791119,0x19f500c202de0241810,0x175248e00af28040e]]
def g187H7 := limbs80 #[#[0x60400000000001,0x1000003000000000010,0x896d400]]
def g187D8 := limbs80 #[#[0x8a4b807f54bfa85dd32,0x1ca3946081847356838c,0x2a851ca30]]
def g187H8 := limbs80 #[#[0xe4000001280431b18409,0x11c0000002174004]]
def g187D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g187H9 (j : Nat) := if j=0 then 0x17018001d9 else 0
def g187L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g187D5)
  | 6 => (7,3,4,0,0,8,0,g187D6)
  | 7 => (9,2,4,458755,50,8,1039,g187D7)
  | 8 => (3,1,4,0,0,7,0,g187D8)
  | 9 => (1,0,4,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 2 0 2 0 0 g187H6
  | 7 => lookupShort 2 31 1 6 3 1 g187H7
  | 8 => lookupShort 2 19 4 7 4 1 g187H8
  | 9 => lookupShort 1 11 0 5 2 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187B5 : CutRow g187 5 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187B6 : CutRow g187 6 0 7 := (@joinRow g187 6 0 4 3 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187B7 : CutRow g187 7 0 9 := (@joinRow g187 7 0 3 6 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g187 7 3 5 1 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187B8 : CutRow g187 8 0 3 := (@joinRow g187 8 0 1 2 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187B9 : CutRow g187 9 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : mixedTables g187 9 := by
  intro k hk
  interval_cases k <;> first
  | exact g187B5
  | exact g187B6
  | exact g187B7
  | exact g187B8
  | exact g187B9
  | exact mixedEmpty g187 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := mixedLower (g:=g187) (i:=0) (hints:=51) (before_sound K175 V175) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K175 10 [(187,[]),(237,[96,16,33,66]),(249,[97,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V175 low187 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[sampledPair 0xe007ffffe1ffff91e0 0x9c1ae000000fc0fc0fff 0x40500a0044001010c0 0x8c006041041041041041,(0,0),sampledPair 0xfff800fffe1ff8310f 0x7c85500003f00003f000 0x84612c228044213107 0x7c0542cb2cb2cb2cb2cb,sampledPair 0xffffff00001fffda3d 0x31312000fc003f00003f 0x80300b0881400a3d 0x11110186186186186186,sampledPair 0xffffffffffe000462a 0x8b87903f00000003ffc0 0x902404c0009824628 0x3829514514514514514,sampledPair 0x4984 0x67ec8fc000003ffc0000 0xe038070110e044100 0x62ec8618618618618618,(0,0),sampledPair 0x2651 0x42404fffffffc0000000 0x100400800010000000 0x820820820820820,(0,0)]
def g189C : List ColumnInfo := [(1,0,188,0,8),(4,0,185,0,8),(16,0,173,0,8),(8,0,181,0,7),(32,0,157,0,7),(128,0,61,0,7),(40,0,149,0,5),(136,0,53,0,4),(160,0,29,0,4)]
def g189A : List (List Nat) := [[],[83]]
def g189D6 := limbs80 #[#[0xe5c5243e0372d5454942,0x5]]
def g189D7 := limbs80 #[#[0xf55152bf59542fb54942,0x42a00ff59152bfd9152d,0xc70187cb1570186ae8a5,0x481c5cb15308c82071b2,0x81c60d4c72c071]]
def g189H7 (j : Nat) := if j=0 then 0x1 else 0
def g189D8 := limbs80 #[#[0xa3946061a403faa5fd42,0x1e851ca301c]]
def g189H8 := limbs80 #[#[0x872034000000000000,0x8c0e]]
def g189D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g189H9 (j : Nat) := if j=0 then 0x4000d000003 else 0
def g189L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g189D6)
  | 7 => (5,2,4,0,0,8,0,g189D7)
  | 8 => (2,1,4,0,0,6,0,g189D8)
  | 9 => (1,0,4,0,0,0,0,g189D9)
  | _ => emptyPacking
def g189I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 2 0 2 0 0 g189H7
  | 8 => lookupShort 1 17 0 6 3 1 g189H8
  | 9 => lookupShort 1 11 0 4 1 1 g189H9
  | _ => fun _ => none
def g189 : Forest := ⟨189,9,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189B6 : CutRow g189 6 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189B7 : CutRow g189 7 0 5 := (@joinRow g189 7 0 4 1 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189B8 : CutRow g189 8 0 2 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189B9 : CutRow g189 9 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : mixedTables g189 9 := by
  intro k hk
  interval_cases k <;> first
  | exact g189B6
  | exact g189B7
  | exact g189B8
  | exact g189B9
  | exact mixedEmpty g189 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 10 := mixedLower (g:=g189) (i:=0) (hints:=1027) (before_sound K187 V187) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K187 10 [(189,[]),(219,[48,33,65,16,101]),(222,[96,16,66,49,83]),(243,[80,33,65,49,48,99]),(246,[96,16,66,49]),(252,[96,16,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0,0),sampledPair 0x1fffff87fff2310000 0x7e03f80fe988a467cfe 0x402801102212012845 0x18a142850a08a2024874,sampledPair 0xe003ffffff00c80000 0xf800007f002013999b3c 0x84b08a010420c01ad3 0x4a64c99326221289991c,sampledPair 0xfffc0007ffe923003f 0x1fc000fec11c21e3cf 0xc02c20480920518a 0x2142850a140110808389,sampledPair 0xfffffff800048807c0 0x7f0101e03e03f1 0x9013002704408e52c 0xb58b162c5901a03602e1,sampledPair 0xa16f800 0x1fff8001fe003ffc01 0xe01c0438080168630 0xc60c18306122003d1000,(0,0),sampledPair 0x1544ffff 0xffe0000001ffffc00000 0x100200040000000000 0x10204080d44d400000,(0,0)]
def g190C : List ColumnInfo := [(2,0,188,0,8),(4,0,186,0,8),(8,0,182,0,8),(16,0,174,0,8),(32,0,158,0,8),(20,0,170,0,7),(0,4,42,144,6),(0,16,42,132,6),(128,0,62,0,6),(6,0,184,0,5),(10,0,180,0,5),(12,0,178,0,5),(16,4,42,128,5),(34,0,156,0,5),(40,0,150,0,5),(128,4,42,16,5),(128,16,42,4,5),(42,0,148,0,4),(132,0,42,0,4),(132,16,42,0,4)]
def g190A : List (List Nat) := [[],[83],[66],[66,83],[49],[49,81],[49,66],[49,66,81],[81,49],[81],[81,66,49],[81,66]]
def g190D5 := limbs80 #[#[0x551525091060c6550910,0x5954250120d915254110,0x55152501205095150120,0x50b51501205d55250120,0xd9152541205495154120,0xd935454120dd15254120,0x1d8db16d9ae1176d4520,0xe2ba572ae35b8b696aad,0x685b804ee027c2103245,0xf28d5cb2c72e68c33b70,0x5052f35ba4af070fcb34,0x60808002a8e530573c2,0xe3868c16284880e18284,0x1]]
set_option maxRecDepth 32000 in
def g190D6 := limbs80 #[#[0x50910195424417219510,0x44370509109954244152,0x5c950441525411050950,0x54510509514436254110,0x4436454910dc95144362,0x5ca654437359510dc965,0x501205d76244174d8910,0x48152501205454048142,0x54550483515012059540,0x54120551504815254120,0x4835454120d455048161,0xdc9504837154120d9150,0x54520d45514837454120,0x48176551205955448373,0x595614807558520dd954,0x59520dc1654807459520,0x48171995205c26548374,0x5db5148174d45205c351,0xd51205975448376d4520,0x48176d51205c75448170,0x5495154175d9120d9354,0x54950d91525436254550,0x5437458950dcd6154370,0x5cb5154172d415054b50,0xd49505d35254362d4550,0x54570d45515cb6154364,0x58960d477458b505cb60,0x8fa2fdc960d457258351,0xaeeb7abe7e9f6779be3f,0xbf2fabdaeeb7adaafabd,0xd3f3ecf73bcdf2fcbb1f,0xe3f8edeb76dbb5ed6b57],#[0xf2fcaeebaeeab9ee6f9a,0x4a154292aca4beaf6bce,0x743116c8622590c36ba9,0x80708be0d90e18c11c6f,0xc81ab5482a63a2907804,0xc860c0d2aa022d841126,0x8b58a1132582184b040,0x20c11bad52375aa45ec5,0x2f7d725b5aa47ab548d,0x1b807eb2e500660180dc,0x40d5ee418d614297c047,0x77081cba1c4484306378,0x82ca61052fba0a478012,0x899423032847d52082b0,0xc184c381258202330a11,0x5438c098718a6e830261,0xb84001708442e1480,0xb841a1308356e1002cc2,0x2c7f064c2e107aaa10e0,0x30852c550a16c3164182,0x567e08abfc3947d75296,0x214d1fc19763872b3708,0xc57aa18ad54306f0a68d,0x32987f74313ec8627590,0xfaf74315ae862b5c4c57,0x743efae87ebd50fd6aa1,0x356e866b608ca0c21f7f,0xa876b608e49c319ab843,0x1fe09017439d9b743b36,0x91114c321458042eaa88,0xabb2a2556544aec88955,0x22d63645ac2c8b5fe096],#[0xf845e170cb8261970dc,0x45ea708bd42117b1c02f,0x90ea9c7e11384c3300b8,0x8c3611308c1a64b754e,0x8e01243c223877447270,0x993ea93261804ac2a095,0x9b233138366eaa8c9fe0,0x311d876a3b0ad665c1aa,0x15468c700d21e118c9c0,0x54ef00a94e11b29c2345,0xe8a67dc94a9c32a5265,0xa145c5416c2299b74533,0x5c554dc02a1e8750a6e2,0x528aa2a514154a6e2a94,0xc0aa518154a6a2a94545,0xdaf627a2706b1f5495a9,0x847cfec4f8de11eb8ba3,0x6f240ed5dcdc35b9b71b,0xc50d5d89daab13b69527,0x82e12184c243594286b6,0x11d39aa3a715474fec4e,0x38ba3aaf82755ec4e866,0xa398f82726b08e9cdd1d,0x676482e7010615d2143b,0x178a2c2f1de01e3ba83c,0x130915455233242bc536,0x9247e1240bc1440b848a,0x5b0900d00f811000130,0x91983085b0ae13822838,0x8c4d49111520e3d0708d,0x704db19f3285e8b515f2,0x504a013f27c4f31d7398],#[0x4a414728c514a2143284,0x814f29c534a614b29452,0x572ac554aa1532a4544a,0x2bc574ae15b2b4564ac1,0xc594b21632c4584b015f,0xb4b616b2d45a4b41672c,0xba1732e45c4b816f2dc5,0x17b2f45e4bc1772ec5d4,0x3304604c017f2fc5f4be,0x14624c418730c614c218,0x644c818f31c634c618b3,0x4cc19732c654ca193324,0x19f33c674ce19b33466,0xa734c694d21a3344684d,0x35c6b4d61ab3546a4d41,0xc6d4da1b33646c4d81af,0xf4de1bb3746e4dc1b736,0xe21c3384704e01bf37c6,0x1cb394724e41c738c714,0x33a4744e81cf39c734e6,0xb4764ec1d73ac754ea1d,0x784f01df3bc774ee1db3,0x8c0de73cc794f21e33c4,0x181161413901c0a00202,0x569284119258f420f63b,0x2c008b0de3e122821648,0x14200908800b0484809a,0x963241ce0603c2186c33,0x3562cc1882f7c251c2a1,0x6202ec40116140650401,0x10940d2310d683ac0837,0x213f2910b48c816fb09],#[0x84dc0d21a434841bab19,0x14]]
def g190H6 := limbs80 #[#[0x201e,0x2090000000,0x315000004040c0000000,0x81,0,0xc398200,0x800c3400000020000000,0xd3000e8b550000081,0x10700,0xd00c3c000000bc5c0000,0x52c00002460011080,0x5000084280000]]
set_option maxRecDepth 32000 in
def g190D7 := limbs80 #[#[0x54110509104851019510,0x59510589105491054510,0x5012019520d891099510,0x58520551205452054120,0xd5120d45209952059520,0x5495054550d9120d8520,0xd4550d41505895058550,0xd4551d8950d8550d4950,0xd4b5058b5058750d8151,0xbebf3f9ecee6f2f58351,0xfefb7bafcfdfefd7dbbd,0xdfdfebefeff577fbddad,0x61dcc70ae60097203fdf,0x35c4a0ae6a4152326a11,0x54830ee708374400ba14,0xc846ec42376405db1071,0x4922e849374193b8048d,0xb22e4413721c8b90045d,0xb6e46595231cb2976548,0x6c863964323aa191550c,0xec9257048fb99a9dd0c7,0xc71176397329cb594e22,0x9ad654d9b22695c1326e,0x1b74413b82045d5522ec,0x374419ba20c1d1076e08,0x52688ba2245d914ae089,0x274fb9b07dcd64ae4d45,0x717b22f1dc174ee0b917,0xc8ba3c6dd192ae8e2f64,0xb83e45ca026e912d648,0xb90795c83ca841937291,0x284f1942baa416142133],#[0x979544b7ec82c95415f3,0x99584ccea266551333a8,0x5dccdc2c26e351373b89,0xdd9252ec929744b2b825,0xc5052e29a8753deb29ea,0x9b7ec4b4952594b8a2ad,0xd92a4ea9726dfb137254,0x7ae522b7291eb148a5c9,0x2ea13f6509eb284fdca4,0xe263e7615e3b0aadd055,0x866574333aa199550cca,0x6bf6435eb21b9994ccee,0xa97635fb29af594d56e8,0xd6549fb224f591256ec6,0x753df3b24f5d927eca93,0x53a9aa1cadc4ecae072b,0x4f2b826fdd8e7aec73d6,0x29ba219dc107aec9bd65,0xeba20fdc507ae283e654,0xb1359589acae08bf7441,0x930fd8987ac4c4952633,0x2f9dc177ec4ebd62755b,0xf259177ec8bcb545e4aa,0x2591c52e8e3f64725b22,0xd899cee0cc974725b239,0xd19a0e8cbf6465eb2337,0x1e7ec8f6770795ba334d,0xe7ae8f3f7179eb8bca5d,0x7ae912b7489eb244fdd1,0xe00aa07202a000fdd22,0x482161de1a217e14611e,0x435c3323002d42a426e2],#[0x48a4604464143e83ba38,0xf05c458454e50c4e84c6,0x873a7086e46b467463e5,0x89887683e8007e67be77,0x69ce9a696892e8f48ce,0x2b50b0cac2a78a4ea2aa,0xcc8c78c3ec18bf2bbab9,0x52e18dd6d96d5cd2acee,0xaf94f6ef38ee8ec0e86e,0xff0db0ad07303affcfc,0x5123f2131df1af17513d,0xb39d3693333052c327d2,0x4df4ab48345b4213eb3c,0x8357356355354352750b,0x35e35d35c35b35a35935,0x6536436336236136035f,0xc36b36a3693683673663,0x37237137036f36e36d36,0x79378377376375374373,0x37f37e37d37c37b37a3,0x38638538438338238138,0x8d38c38b38a389388387,0x439339239139038f38e3,0x39a39939839739639539,0xa13a039f39e39d39c39b,0x10c8140d841f81a33a23,0x1c880238a0f442012c4,0x801c7c34806028d1543,0x16c30445822685c54648,0xc64f4b881b0a1805ca46,0x4d108b40948e5c25081c,0xd84840884286830d02c0],#[0x5917cb01143d5a28198d,0x447f804d5e6d48c116d,0xc045de3c4115f8045ff9,0x67c264a5c4838aa445f2,0x15bca2c755b3187e1319,0xcb096fe8f12d4592af70,0xa8875615c44a213e0484,0x235bc47b1420e59989d7,0x7880432f7acc64df1e81,0x6464dc9f51a08ea72227,0xf11dff4122f5f4822d7e,0x804cc3fdec8203d7a4b6,0x1fefc41156186d82afd1,0x430eff04a174203ce526,0x5019f98260cfcc134d4,0x8050f5c8272de242fd81,0x49f9c008e7ae245b411d,0xcabe7c10230df697011d,0x123e2019297891251d92,0x540901dccc263980cf38,0xd8cff396083f8083e060,0x5af480c65ea7a3325709,0xe68d107da028bc5f0a26,0xfd6d28fedb0537a36461,0x3e52277262cf58cc8079,0x96d92b02bc329353d8f7,0x1f109bb4318d398d151b,0x7a0326efd82297874064,0xdf810e9cc083d5c44469,0x81140e7a5823df884801,0x488b7f8113ba03189aff,0x718d13650b83b31c5c7],#[0xe0efb88e0e90e0e3528b,0x2d22ac8b0be63e400]]
set_option maxRecDepth 32000 in
def g190H7 := limbs80 #[#[0x200000101020000012,0x10018010211001000,0x15000110101001000,0x40030000010010200101,0x4070000000010,0xbf0000000c2240000000,0x50080,0x302b0000000000000,0x9564000c11604a,0x98800020bd000107b0,0,0x24a10000000000,0xa700000000,0xd2460a9000000000000,0x80440000000000000000,0x305f00000000000000,0x3c0000a6400000000000,0x346e0000000000006f01,0xa2b00030aad220000000,0x3,0x13dc4b714300000,0,0x20a600000000000000,0x402c00000000000,0,0x213000,0x68117000000000000000,0x3c194000000000000030,0xc28d441000000,0x304800000000000000,0x129e000107a00020140,0xc15800000],#[0xbbc588000000,0x20710000,0x202d00000,0x44400000000000801c00,0x2580008400000511c000,0x5c000000107600000009,0xa,0,0x106dc22c0000000,0xa0000000000000000000,0x841809a0000000000101,0xf11ee0210000000,0,0x40000000000000000000,0x41980000000000a0a,0xc200,0x1a4000000247d00000,0x40100000000218000000,0x44000004bc27e083,0x209c00000000,0x96000000000,0x80ec00000020a2000,0xc02400000000000000,0xa1f00000,0,0x81700000000000,0x20a500000000,0xa2180b200,0x7f00000000000000000,0x40bc0000002094406f,0xc4c4000000250200000,0x20930000000c04000],#[0x151051403000015b2013,0x2a2c00000008,0x3047000000000,0x106a000,0,0xb000000e885400000000,0x114187,0x2350c10000000,0x380b000004241335000,0x2a0e000000000,0,0x40e000000000000000,0,0x2126000000000022c,0x4300000000000,0x3102d0f40000,0,0,0x10001231418193c,0x258181780,0xc1640000000000502800,0,0xbc000000000040e40a40,0x10c40000000110800082,0,0x6a000000090240000000,0x2478000000000001,0x8a740000000000000000,0x34611118000,0xf800000031a900000000,0x80a24908a61053d0,0x20ac000],#[0x25f400000000000000,0,0x823000,0x1441e00020490000000,0x1610b113c0705,0x314101b800000,0x1a200031a60000000000,0x42fa,0x300d629b430c00000000,0x2180190000000000110,0x1600000,0,0x5400000,0xc20000000000,0x43805800000000000000,0x168000000000000f90,0,0x21a8417502a82a0000,0x103700000000,0x400000020ade02400000,0x46ac000000000040a,0x8848,0x9c000000000000900,0xca4c00,0x153e00000000001091,0x20b60,0x400000010c8c0c944d00,0x468018000851aa29013,0x2,0x70000000025400000000,0x452c000000000000011a,0x9400000000000000000],#[0x204ec0600000,0x82cc000000000000,0,0x73000000000000000000,0x82e4000c0c000018610,0x20b0000000,0x24f,0,0x4000c140621810000000,0x2878c03,0x820800000000000000,0xc1ac000000000000000,0x81600000000000000000,0xc0d00000000000,0x13e000000000000000,0x400000,0x2081000,0x63000000000000000000,0x30,0x107d0000000000000,0xc314000,0x1057000000000000000,0x257900000b10003a0b00,0x9d000209ec1d4000000,0x2,0x30000000958000000000,0x14210000000000127,0x7008700000000000000,0x1401c26400000000000,0xc08c000000000000,0xab60a,0x31c00000000000000],#[0,0x78214000000,0xd28c000,0x44000000000000000000,0x5018000c2e800011,0x41b000003f00030ae000,0x201d407f,0xc214064029e868c0cc0,0,0x25890000000,0x308a000000000000000,0x10b8000000000,0,0x200031c600000000000,0xa0000000000000000020,0x8280000000129442d341,0x4302092816d47c,0,0x3a000217c00,0,0x823c,0,0,0xd076111,0x202e00000000,0x8000c238000414800000,0x7e0000000000000001c,0x1,0x4c05c000000000000000,0x309bd05b1aa000307,0x2800000000000000000,0xc],#[0x84a400000,0,0x83e07f03600000000000,0xca0b224831955800004,0x8104000826000040c400,0x343c000307701e0000,0x9400000030b500000000,0x880001060825c000c5,0x26910c000000,0x61818400002400004020,0x988301200021,0x3d81b000,0x28582c00000000000000,0xb000000000004,0xc000c1f0000c1e400000,0x52c,0x554b0400000000000000,0xe0af0,0xc85c0000000000000000,0,0x603800000000000,0x20220000000000000000,0x3c00000000000000000,0x5218000000000082dc,0x108400000,0x818800,0,0xf115a94f400000020670,0x34200000020c2]]
def g190D8 := limbs80 #[#[0xfbfb7d47505455048110,0x908aa801b1bfffefdf7d,0xb2823283b102b108a888,0xb09aa81aa013b2833282,0x3292b2923293b212b213,0xa924a923b0aba823b293,0xb032b145a942b0c3b125,0xa90ca102b057b1b9a8b3,0xaa1caa1cb09da89ca89c,0xb0ada8aca8ad329cb29d,0xb12cb12da92ca92db0ac,0xaa0f011000cb05cb14d,0x23c46d8ca17426c42871,0xdcd11892cc5349b92421,0x2e23e44e838fe1e63986,0xb025d8b45592954f89a9,0x17acef1cc3746a8ce58e,0x6124a3cc5c88d0ae083f,0x291208b1641f026dccd9,0x1348284874b08206ca22,0x146801820b82080c7862,0x25b879f089c59202321a,0x2dff80128fc0110ff42,0x70053f92904f73112bb6,0x4b134ea4a25e844a7205,0x82a0793508e4a7388ef2,0x87dc0550fd04596e4ce2,0xa811ff0053fe089684e4,0xfb9c82673d40cfdc8077,0xe30932e71111c8063010,0x189778c222cc5e44462f,0x6e13865ff0455c9027b9],#[0x42ef9940a77a91011a09,0xe50262f6b0982ef9940a,0xe00f516d0a2f2cf81317,0xe40307f2009dff0056bf,0x40287f2009ccffc8097f,0xde3088a]]
set_option maxRecDepth 32000 in
def g190H8 := limbs80 #[#[0xa0a0048c49080000010,0x60d0588406000580c06,0xac020b03004040a03004,0x106816090001d0802000,0x404040303412010,0x607020700400028c8001,0xc1c0f000781800018301,0x840ca071b83014010005,0x220208014060b02,0x61008545451048446c0e,0xc2009e01c00040300830,0x8cc511523611402fc59c,0xf41b009d8586120c2250,0x36980003443c09403,0x3039c51c002ca0648b,0x4a01f410400021905880,0xb07f0001434000258602,0x106d010c53629a811,0x41ba28000030838158,0xbc035198ca7004382980,0x1210000836000200,0x1c129d450000090b500c,0x141701d825114960af4,0xc06d82e7062000000000,0x81c826520645c524ec9d,0x34561c000845819682ac,0x384341f0000c66b0,0x101d045d4a3525400,0xc2cc298401c11a,0x8f20a0000000412d55d0,0x258b0000000827c000c6,0x69b80006924517002],#[0x97000005a00021724204,0xe00022470ace80f89860,0x106545eb440c5d608,0xe8055c9f005841a8077,0x204e513c0a181331a6c,0xe52900184a241a200e01,0x52843b0b880ec86dc24,0xb1c2d402e0120023427b,0xb44f0000c11400080550,0x40f501b42ba2b4851902,0x1d4000c0a927e955100a,0xca41a417c000e0f54514,0x324f894041c094b09102,0x73c55013500dc0b0c14,0x57c20a10c046c25ac187,0x484d30a5011e80e81bd4,0x8667080103341685471a,0x4e01131994022c134431,0x96024c2d847280f10208,0x21a0c04705c503925362,0x6b85cc1570005004c9e,0x6ac9770694051168005f,0x3c06058a00d60aa00e11,0x1638222086000026,0xcc0004a44000c98003e,0x3084d0e4019a9321698,0xc07401c7188029000000,0x1624024005000009aa1a,0x2d0000000000151f06b2,0x24270066054fa4b805b0,0x847c0000000078022a18,0x2dc10a000058d8674000],#[0x452149828e026c,0x18a8404a1568108a4500,0x46550d927b0001556000,0x561705900000008253,0xd822f476000112200000,0x60000000000000a,0x1200008174165c23c0a0,0x3000156127f0a66849e,0x3180469c51a81fa09500,0x11500035791075128000,0x64442f498424210d0001,0x40c004f000e0,0x498a265962686e421400,0x97a08780b2516a9ac000,0x95c800084004640,0x718c019c000000019b00,0x811048e521400041f,0xf8150000c97c1a2829c,0xe428b0360002a6d404ca,0x84ed09b806a44ec9e905,0x5d2452c918000007000f,0x720490001029000204a0,0x40a000243bc25819746,0x6389c629282b160a000,0x5b50eb49e42350510001,0xe914316000030a800840,0x305780a1164068401,0xd0ae07b908211e,0x9d84b000003242630a90,0x616601c952291cf15080,0x426d4984a102e914240c,0x5bc14c07ae13128681e5],#[0x2d12]]
def g190D9 := limbs80 #[#[0xd51ffa87f543fa41fd10,0x51b0259b138a803fea3f,0x410202544526488f00,0xf1464248a500f1a48a5,0x248a02051539228]]
def g190H9 := limbs80 #[#[0xe0838204040052028400,0x206be022411a2610a8e4,0x8008107021292000a0a,0xe80480b09400048c000e,0x82f42d0008150000a111,0xc05c18429c2e000c1f,0xb445c6d0424a2d20020c,0x129d62000e2daa006084,0x80fc81030807401,0xc000c0341b02286c8140,0x86fc8782680e831000c1,0x1b06181900000000041e,0x41662800085180cc5a9,0x8ab825503006a2000,0x2d00040a000565000000,0x6000c500624280000009,0x1dc56c13d0a4a3c88e1,0x1bc8416460702702a059,0x3c170a88704aad6102be,0x42cd0801012810b844c2,0x2485561f80d203e3169f,0x2000a1e0004091a00004,0x2290000004124a900,0x46e000531000000811,0xc5789891600001a0]]
def g190D10 (j : Nat) := if j=0 then 0x2080513f else 0
def g190H10 := limbs80 #[#[0x8,0xd1000000,0x80000000000143e00000,0x240000000120000000,0x3840000,0x8400250000000002a000,0x1400000000001,0x54e0d,0x21281000,0x8a80046000,0xc0000000000000]]
def g190L : Nat → Packing
  | 5 => (16,5,5,720909,68,7,1024,g190D5)
  | 6 => (201,4,5,2949194,103,11,1060,g190D6)
  | 7 => (187,3,5,1703973,86,12,1089,g190D7)
  | 8 => (50,2,5,458758,51,11,1060,g190D8)
  | 9 => (6,1,5,0,0,8,0,g190D9)
  | 10 => (1,0,5,0,0,0,0,g190D10)
  | _ => emptyPacking
def g190I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 6 97 3 10 4 4 g190H6
  | 7 => lookupShort 83 1237 4 14 8 4 g190H7
  | 8 => lookupShort 98 487 9 14 8 4 g190H8
  | 9 => lookupShort 28 149 7 12 6 4 g190H9
  | 10 => lookupShort 4 97 1 9 3 4 g190H10
  | _ => fun _ => none
def g190 : Forest := ⟨190,10,fun i => g190Y[i]?.getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190B5 : CutRow g190 5 0 16 := (@joinRow g190 5 0 1 15 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x400040a01422400081,0x4024108141000810402,0x41081410008104024108,0x14100081040241081410,0x800402410814500081,0x4024108141000810402,0x41081410008104024108,0x14100081040241081410,0x10002040291082320080,0x4024108145001000100,0x88500a51018041209858,0xe530100040089102851])) rfl
      decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190B6 : CutRow g190 6 0 201 := (@joinRow g190 6 0 79 122 (@joinRow g190 6 0 11 68 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g190 6 11 20 48 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x810402,0x41081410008104024108,0x14100081040241081410,0x810402410814100081,0x4024108141000810402,0x41081410020800603838,0x90520208006038389052,0x800402410814600081,0x4024108142000810402,0x41081420008104024108,0x14100081040241081410,0x810402410814100081,0x4024108141000810402,0x41081410010800120814,0x88411000812099488843,0x800402410814600108,0x1028050885200800402,0x41081451018184024108,0x1c310181840241081c31,0x2080062103890420208,0x621038904202080122,0x90689053018184024108,0x1c310181840241081c31,0x1080012081488520483,0x4024108343101000402,0x81102862010204028110,0x28420208006230389053,0x2080062303890420180,0x412098580e6101000100,0x88500a51010001008850,0xa510480406038582652,0x40c120b0440a100188,0x1228058884100424040,0xa0142230018041209858,0xe600100040281102861,0x1020402811028310400,0x20422050224301080102,0x80508851040080120844,0x28520102040281102831])) rfl
      decide +kernel
))) (@joinRow g190 6 79 48 74 (by
      apply polarBlock (data:=fun _ => (w80 [0x810402,0x41081410008104024108,0x14200081040241081420,0x810402410814200081,0x4024108143100810402,0x41081431008104024108,0x14200208012210689043,0x40800920864a0430048,0x422014826000408090,0x69200a20100000108904,0xa0640040840221040a20,0x408100a0440a200040,0x840221040a2000408402,0x21040a20010024020910,0xa61100000108904a064,0x40800120844a0540040,0x8100a0440a2010002100,0x89408254010021008850,0xa510102001088142831,0x4008402094028420080,0x4024108145100800402,0x41081451008004024108,0x14510080040241081451,0x40840221040a101000,0x40603918846300810402,0x41081420008104024108,0x14100081040241081420,0x810402410814200100,0x108814285100810402,0x41081410008104024108,0x14200081040241081420,0x810402410814200081,0x4024108141000810402,0x41081410008104024108,0x14100081040241081410,0x810402410814100081,0x4024108141000810402,0x41081410008104024108,0x141000c1240241081610])) rfl
      decide +kernel
) (@joinRow g190 6 127 48 26 (by
      apply polarBlock (data:=fun _ => (w80 [0x408100,0xa0440a2000480122904c,0x82400040840221040a60,0x800402410814510080,0x4024108145100800402,0x41081451008004024108,0x14500080040241081461,0x800402410814610081,0x4024108142000810402,0x41081410008104024108,0x14200081040241081420,0x810402410814100080,0x4024108146100810402,0x4108141000c04060b01c,0x265000c04060b01c2650,0x400040a01422500040,0x40a014225000810402,0x41081431004084022104,0xa2000c04060b01c2650,0xc04040a01426500081,0x4024108142000810402,0x4108143100c0c4022104,0xe200040840221040a20,0x810402410814200081,0x4024108142000810402,0x41081420008104024108,0x141000400040a0142250,0x400040a01422500081,0x4024108142000810402,0x41081431008104024108,0x14310081040241081431,0x810402410814200081,0x4024108143100810402,0x4108142000400040a014,0x226000400040a0142260,0x1000010881428510040,0x40a014226000800402,0x41081461008104024108,0x14200081040241081410])) rfl
      decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x42040281042240,0x10000108814286200c8,0x62201c824000c12402,0x4108163100c124024108,0x16310081040241081431,0x10000108814285200c0,0x4060b01c265001000010,0x88142852008104024108,0x14200100001088142851,0x810402410814310081,0x4024108142000810402,0x41081431008104024108,0x14310081040241081421,0x810402410814200081,0x4024108142000810402,0x41081420008104024108,0x14100081040241081410,0x810402410814200081,0x4024108142000810402,0x41081420008104024108,0x141000408100a0440a20])) rfl
      decide +kernel
))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190B7 : CutRow g190 7 0 187 := (@joinRow g190 7 0 69 118 (@joinRow g190 7 0 10 59 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g190 7 10 48 11 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=3)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))) (@joinRow g190 7 69 38 80 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=3)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g190 7 107 48 32 (by
      apply polarBlock (data:=fun _ => (w80 [0xc12402,0x4108163100c0c4022104,0xe2000c1240241081631,0x810402410814200081,0x4024108142000810402,0x41081420008104024108,0x14310081040241081431,0xc0c40221040e200040,0x840221040a2000810402,0x41081431008104024108,0x14310081040241081420,0x810402410814310081,0x4024108143100810402,0x41081420008104024108,0x14310081040241081431,0x810402410814310081,0x4024108143104080032,0x184ca054008104024108,0x142000c1240241081631,0x40840221040a200040,0x840221040a2000408402,0x21040a20004084022104,0xa2000408100a0440a20,0x408100a0440a2000c1,0x24024108163100880092,0x482c8451004084022104,0xa200040840221040a20,0x4830402410834310040,0x8100a0440a2000408100,0xa0440a20008104024108,0x14200081040241081420,0x810402410814200081,0x4024108142000810402,0x4108142000c124024108,0x16200181840241081c31,0x420060b01c22400108,0x1028050885201020402,0x8110284200c124024108,0x163100c1240241081631])) rfl
      decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x8104024108,0x14310081040241081431,0x810402410814310081,0x4024108143100810402,0x41081431008104024108,0x14310048004220148250,0xc12402410816310081,0x4024108143100810402,0x41081431008104024108,0x14200081040241081431,0x810402410814310081,0x4024108143100810402,0x41081431008104024108,0x14310081040241081421,0x810402410814200081,0x4024108143100810402,0x41081431008104024108,0x14310081040241081431,0x810402410814310081,0x4024108143100810402,0x41081431008104024108,0x14310081040241081431,0x810402410814310081,0x4024108142000480062,0x301c825000c0c4022104,0xe200181840241081c31])) rfl
      decide +kernel
))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190B8 : CutRow g190 8 0 50 := (@joinRow g190 8 0 1 49 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g190 8 1 30 19 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=3)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190B9 : CutRow g190 9 0 6 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190B10 : CutRow g190 10 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190T : mixedTables g190 10 := by
  intro k hk
  interval_cases k <;> first
  | exact g190B5
  | exact g190B6
  | exact g190B7
  | exact g190B8
  | exact g190B9
  | exact g190B10
  | exact mixedEmpty g190 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 11 := mixedLower (g:=g190) (i:=0) (hints:=269620272) (before_sound K189 V189) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K189 11 [(190,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V189 low190 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[sampledPair 0xffc07ff800fffffe03 0xfecb2a2ba20000f0000f 0x148b21526a4948a458 0xa6cb0a2aa25555555555,sampledPair 0xffffffffff001ffffc 0x34edb8091000f000ff0 0x191202604c0d80c891 0x334e5a00111111111111,sampledPair 0x7fffffffe00000 0xd372d62500f000f000 0x5e1c0b80700e02f0e1 0xc0c372d4253333333333,sampledPair 0x7fffffffffffff 0xf922299d6b0f000f00ff 0x60200c008010030000 0x202195082222222222,(0,0),(0,0),sampledPair 0xffff80000000000000 0x98c67ad8f0000fff00 0x8000300300600c0102 0x10842ac04444444444,sampledPair 0 0x665142404fffff00000 0x40040080100000 0x8888888888,(0,0)]
def g207C : List ColumnInfo := [(1,0,206,0,8)]
def g207A : List (List Nat) := [[],[32,99]]
def g207D8 (j : Nat) := if j=0 then 0x7f else 0
def g207L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g207D8)
  | _ => emptyPacking
def g207I (_ _ : Nat) : Option (Nat × Nat) := none
def g207 : Forest := ⟨207,8,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207B8 : CutRow g207 8 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : mixedTables g207 8 := by
  intro k hk
  interval_cases k <;> first
  | exact g207B8
  | exact mixedEmpty g207 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K190) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 9 := mixedLower (g:=g207) (i:=0) (hints:=16778803) (before_sound K190 V190) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K190 9 [(207,[]),(231,[83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V190 low207 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[sampledPair 0xe007ffffe1ffff9164 0xdc16e000000fc0000fff 0x44510a204404101144 0xcc00e249249249249249,(0,0),sampledPair 0xfff800fffe1ff8318b 0x3c89500003f000fff000 0x80602c028040213083 0x3c0140c30c30c30c30c3,sampledPair 0xffffff00001fffda3d 0x31312000fc003f00003f 0x80300b0881400a39 0x31110186186186186186,sampledPair 0xffffffffffe000462a 0x8b87903f00000003ffc0 0x902404c0009824628 0x3861514514514514514,(0,0),sampledPair 0x4984 0x67ec8fc000003ffc0000 0xe038070110e044104 0x42ec8618618618618618,sampledPair 0x2651 0x42404fffffffc0000000 0x100400800010000000 0x820820820820820,(0,0)]
def g221C : List ColumnInfo := [(1,0,220,0,7),(4,0,217,0,7),(8,0,213,0,7),(16,0,205,0,7),(64,0,157,0,7),(128,0,93,0,7),(5,0,216,0,5),(9,0,212,0,5),(12,0,209,0,5),(17,0,204,0,5),(24,0,197,0,5),(65,0,156,0,5),(68,0,153,0,5),(72,0,149,0,5),(80,0,141,0,5),(21,0,200,0,4),(25,0,196,0,4),(73,0,148,0,4),(76,0,145,0,4),(84,0,137,0,4),(129,0,92,0,4),(132,0,89,0,4),(136,0,85,0,4),(144,0,77,0,4),(192,0,29,0,4),(0,512,224,3,6),(0,513,224,1,5),(0,514,224,1,5),(0,515,224,1,5),(0,516,232,0,7),(0,517,224,1,5),(0,518,224,0,4),(0,519,232,0,7),(0,520,232,0,7),(0,521,224,0,4),(0,525,224,0,4),(0,526,224,0,4),(0,527,232,0,7),(0,528,224,0,4),(0,530,224,0,4),(0,535,224,0,4),(0,537,232,0,7),(0,538,224,0,4),(0,540,224,0,4),(0,541,224,1,5),(0,542,224,0,4),(0,543,224,0,4),(0,546,224,1,5),(0,547,224,0,4),(0,548,224,0,4)]
def g221A : List (List Nat) := [[],[98,67],[32,99],[32,48,64,96],[48,100],[48,66,96,32],[64,50],[64,98,48,50],[96,32,50,67],[96,66]]
def g221D5 := limbs80 #[#[0x4c9214c1105495048110,0x551514c11054d514c110,0x54921501104c92150110,0xd4d51501105515150110,0x54d32541106107254110,0x54951541105494254110,0x20974541105895254110,0x54a515411054a4254110,0x551518c11060b5354110,0xe1d51901105d5528c110,0x55151d011054950c8110,0x60b535412054a3154120,0x5515150610e0d71d8950,0x5a5b3c65cc67732cd58d,0x33a571ade1ba36c6ccd3,0xe47c4f31e33b8758ea9d,0x815550b650c915d03f83,0x42b614315d4305c68c5d,0x23450e2e5d06f5d04be1,0x8c2650f05d4b04864e5d,0x96e5c2a455268e08d2d8,0x94d5d14661933589f358,0xd87e0d87619c9605c761,0xe0758a0a4850c5d181e4,0x2e761ac0e5b25dc5a6d8,0x58240e03000354b0759,0x1d0d8642e15098441e0d,0x5e2d158a44e25118843e,0x47e3d1d8e46e35198c4,0x4240301a59248e45219,0x38140102540811081962]]
set_option maxRecDepth 32000 in
def g221D6 := limbs80 #[#[0x54c20591530816354c20,0x837054c205d95308165,0x9d5630817558c205d163,0xd4c20dcd650817359420,0x8165d4c205935308163,0x5442044121081105db53,0x109105c0424417508110,0x44150481105d84244175,0x48530441764811054520,0x4c11054530441324c110,0x441544c11054d3044152,0x59132441754c1105d130,0x50110dc132441764c910,0x44151501105414044121,0x94540441655011054940,0x50110d41404426550110,0x4436250110d494044351,0xd8d424415250910d9540,0x54110109504436550910,0x44132541101c95044071,0x54550441435411050950,0x5411054d504415254110,0x44163541105895044154,0x5d150441725411059150,0x54110909504417654110,0x44254541109495044251,0x9c950442645411098950,0x54110d09504427454110,0x4436254110d4d5044352,0xdc5504436454110d8d50,0x54110dcd504437254110,0x44176549101c15244374],#[0xdd9524437054910d5152,0x58910dcd624416558910,0x4437359510dc96544375,0x54a30441518c11048630,0x901105d630441548c110,0x44175901105524044151,0x5c6424415290910d5240,0x941105da424417590910,0x441649411058a5044154,0x4c72044172995105c652,0xc81105432044132c8110,0x44153c811054b2044151,0x5d72044171c811059720,0xc8110d432044265c8110,0x44151d01105434044353,0x5cb5044171d41105c740,0xd49105c75244170d4910,0x44170d4d105db5244174,0x5d36244363d4d105cb53,0xd95105cb6344175d8910,0x48151541204c55048172,0x90550482315412054950,0x54120949504825154120,0x4837654d20d855048353,0xdcd654837159520dc165,0x995205da31481518c520,0x48361d45205c35148171,0x5c76548176d4d205cb53,0x54950dc1515417118950,0x54373585501cd6154370,0x5c65254361945505c251,0xd85505cb615417198950],#[0x54171d89505d36154173,0x5454184174d89505cf62,0x54210591418415450610,0x84162542105495084141,0xdd950843525421059150,0x54610591518415454610,0x8416554a105895284165,0x5c5648416455210dc152,0xd46109d5648417559210,0x84165d46105935184154,0x5975284174d46105c351,0xd52105935484170d4a10,0x881615422054d5088170,0x55151883535422058d50,0x546205d9518816154620,0x88164552205d95388376,0x549618837655220dc954,0x59620551638815458620,0x88176d46205c35188374,0x5c35388171d4a205c352,0xd52205c35488176d4e20,0xd4372587505db5488171,0xdcd62d437458750dcd61,0x9f27b9ea3f8df7458b50,0xaf6bbadeafa7e979fa7d,0xbf2fabdaf4bbadeb6abe,0xcef37cdb2fcbb2bc7f1e,0xdb76cd7b5dd7358cfb3d,0xdf37ade778ddb74dc36e,0xeafa7e7b9de6f9ae5b8f,0xf33cbef3baedbaeeb7ac,0xfc3ecf73daf5bd4f3bcd],#[0x3eba87265cc3bf8fd3f2,0x7a35d03d3ae61ea5750e,0x85d03022013870f40ba8,0x6bcb9651b7ea98cc44c,0x3834009c3b13c550908f,0x5db1a5ae58ce57ac4700,0x200e0e0c0706a8d7414e,0x3157ac5661d858635b1c,0xc80869630430b2651859,0xb838d5ea9499559410c2,0x5cb1e58e60a48730b223,0x617593541301aa0383d1,0x5c60aa4e305521401c1d,0x842e19877a58bab7a25d,0x3851758ba0bc654c5e3a,0x50ba0c42550663264325,0x214e048d12eabf09545e,0x48a3aa4451d32227aaa1,0xa64909532421c2123ad9,0x5547c58b8bd90e109a16,0x84a92142548dd0aeaf8f,0x88f614c4a30263015334,0x9060aa46a1987311ac31,0xc4710562381ec2a0c154,0x184331ec2a28f6150e0c,0x44c00913208fc7b04964,0x78f601549306a6ed542e,0xa2cdaea0acd83017aaa5,0xa51905528e80a9c5c154,0x964cb64a9664154a420a,0x58ba879bd928d8aa9a0c,0xb1d5d854f2ec28b18110],#[0x5e4a702e2b1717103c28,0xeaf24d827982a93c9460,0x952760bc3b90661de512,0x28c2b7c654dbe3aa4dea,0x94254dca3aa4e51d3272,0x5c8a706e4b1737285a9b,0xe6e6ad75708aa9b82c5d,0x1737457c3b993e0dcd5a,0x26c13d14605e86f0ce8a,0xc06e1dd49706ea4f8275,0x85c3706ee19877826c13,0x43251851758ba8bc754,0x1741985aa0cc654c64a7,0x25c10d86e1c6942ea30b,0xe14e0471c2ca36a1741b,0x97437083c1b851d4aba0,0x4bc53855d58baaec754,0x1745e85aa2f46e0d78a7,0x4aba3014e0580370ebeb,0x114604a43708c28b5261,0x891f2a848b1752274b29,0x648b3732429c1123ad8,0xb5424872a124355090a7,0x58ba9243e10921908490,0x5146149d66ea4eb37524,0x4ac370e4a89752520c21,0xc5689752b20c2159460,0x5852c3cba960661cac6b,0x1bc1130de049897064c3,0x142551886b045a418428,0x594a702c6b1756285aa3,0xeaf6b1816444bab29460],#[0x1547d0bc3be0561df112,0x38b12830588e02b049e9,0x114e08ddd6c46ee96237,0x109d2c88451824274b12,0xa49e51823284a9192cdd,0x1744f28c127ac9c93e12,0x1ac31a38d8cd20aa468b,0x8d618d52ae86a1a8731,0x9252ae89235864128c0a,0xc4701a87490cc3a48d61,0x9633883b91c32d88e1ca,0x64b21c0fe0ce196c670c,0x1946050d16e870cb6438,0x92992c49435864372b12,0x694cb634a64b1a532d8,0xb744a65b22532591287b,0x73b91db91c8ec7f0a768,0xd8de0ced96a676c9533b,0x4ec6f08767b743b3cba1,0x8987b744c65c29db221,0x3813e21421994604cc6b,0x71b19b14e04d8a3028e5,0xe0fe08e4350e6ca37336,0x135c6e69a35824d70a99,0xe88853813a0cc2288d61,0x7823d1fc29e8d619112e,0x1ec2a332e14f5910a7a3,0x413e08fca7027e35824e,0x5496302a451815228c0a,0x2d47b876b0cc1a92ca0,0x7827e3ab13f1ee1db0a7,0x3cb2109c589fceac8fc1],#[0x161c7c5f043e198421,0x448f6ca2207852003c21,0xe5e0785132d430916d9,0x7656754a9338161cc00b,0x3c2b486e01a0e2eccc7,0xa1ed95583308ac7b6256,0x600eecada05805703c0a,0xc7007b62805918c02c4c,0xb83800cc1c01ed8e00f2,0xdc2401ed9200f2c9001,0x9dd8a05646102b13081,0xe042b07027763813ab1c,0x3047764813ab24085e0,0xf825803c24199592082f,0x37a9ac96995685706b02,0xd16d4568b6a0b4058459,0x2100f091065548702c1a,0xa5126f63850dc04286e1,0x3805c50a82e01e1624e2,0x3c22d9c4856ce240b6a,0xe1b50170da40b86f705c,0x9b8daa4b86d425c37c02,0xed66dd64b23929451c58,0xd81b572a95a32586d996,0x13c35836592bc6b056ed,0xc88e1ae16ac9706575b1,0xee56d0b72b585b96cc0d,0xc58a5b72ba3343dc9961,0x585c35ab2611e59314f2,0x2cb9621959318cb0f86b,0x416dc6f0e6e3767965bd,0x728cee37c5971c73cb0e],#[0xeb7e6571c95aa8e49e58,0x581c113c0e009e16fcca,0x37ba001e59410f2c8082,0x196dd008cd0e02677401,0x30cb0e166d740a03c20,0x80c2b850502c206965d,0x3840802c2048a6101c57,0x1ac3478d61a384308122,0x6c154e35cee526e55293,0x63608e31b06618d82b0c,0xed3104878d83c1c6c1dc,0xd329b3db0cd81e1664ea,0xcc24d9e58e6d12a736a,0xe81612500b032821859c,0x658eac32c07819e56a04,0x212c7510963db8ca9d98,0x5619a36a1cb9d94658ee,0x3cba6632d4b30eca33e7,0x83854f3592c99c7b74cc,0x3496ac99ec754d03bb96,0x9b67964db3cb16d8161,0x780d702c16e1e5037033,0x3ab0ef1e587746703b03,0xc9e50380f2c9be0784d3,0x7541b03aaad50d517c16,0xe7a8d372d45ba8ea1c59,0x963e13cb0f08160758ce,0x2c1ed0160f8ceac3c47,0x33154a98f6c94a1984a1,0x2a4dec948a240a418c15,0x43527121a93dc0549e20,0x542ab3699551c4caa4e6],#[0x32a1d581e0aacce85566,0x38660688f6c3440783ab,0x2b0e6c550b180a039b15,0x435c0784ad38a95681e1,0x582e502c1f201e06b8e2,0x32217319d03980b09ca0,0x3816079c0b07cc6642e6,0xa00280006641e802c27,0xa004601e00c805001e0,0x6e833415c09b04281b8,0x26612b08f042c1f60e5,0xf0c305e82d21560a6850,0xcc3c81d30e206cc34218,0x5012108d044220f10387,0xa7051627413609904b82,0x2f11728b405882b61570,0x8d4869433b18e8c445fa,0xc39e1c50df86e436a1ae,0x8fd07c23cf1e38ed874,0xac44221a10a084041420,0x53124890647b23511888,0xa144f827213409904bb2,0x2aa1520a6e52a28f1458,0x4b225892c095e4ad655c,0x92e096e4b625a92d0966,0xe4be25e92f09764ba25c,0x293109864c2260930097,0x964ca264932098e4c626,0x68934099e4ce26693309,0x9ae4d626a93509a64d22,0x26e93709b64da26c9360,0x9c64e227093809be4de],#[0xa27493a09ce4e6272939,0xc09de4ee27693b09d64e,0xf627a93d09e64f227893,0x3f09f64fa27c93e09ee4,0x50228094009fe4fe27e9,0x9420a0e5062829410a06,0xe50e2869430a1650a284,0xa9450a265122889440a1,0x3651a28c9460a2e51628,0x909480a3e51e28e9470a,0xa4e5262929490a465222,0x29694b0a5652a29494a0,0xa6653229894c0a5e52e,0xa29c94e0a6e53629a94d,0xa7e53e29e94f0a7653,0x462a29510a865422a095,0x530a9654a2a49520a8e5,0x5522a89540a9e54e2a69,0x9560aae5562aa9550aa6,0xe55e2ae9570ab655a2ac,0x29590ac65622b09580ab,0xd656a2b495a0ace5662b,0xb895c0ade56e2b695b0a,0xaee5762ba95d0ae65722,0x2be95f0af657a2bc95e0,0xb065822c09600afe57e,0xa2c49620b0e5862c2961,0x40b1e58e2c69630b1658,0x962ca9650b265922c896,0x670b3659a2cc9660b2e5,0x5a22d09680b3e59e2ce9,0x96a0b4e5a62d29690b46],#[0xe5ae2d696b0b565aa2d4,0xa96d0b665b22d896c0b5,0x765ba2dc96e0b6e5b62d,0xe09700b7e5be2de96f0b,0xb8e5c62e29710b865c22,0x2e69730b965ca2e49720,0xba65d22e89740b9e5ce,0xa2ec9760bae5d62ea975,0x80bbe5de2ee9770bb65d,0xe62f29790bc65e22f097,0x7b0bd65ea2f497a0bce5,0x5f22f897c0bde5ee2f69,0x97e0bee5f62fa97d0be6,0xe5fe2fe97f0bf65fa2fc,0x29810c066023009800bf,0x1660a3049820c0e60630,0x89840c1e60e3069830c,0xc2e61630a9850c266123,0x30e9870c3661a30c9860,0xc466223109880c3e61e,0xa31498a0c4e626312989,0xc0c5e62e31698b0c5662,0x3631a98d0c6663231898,0x8f0c7663a31c98e0c6e6,0x6423209900c7e63e31e9,0x9920c8e6463229910c86,0xe64e3269930c9664a324,0xa9950ca66523289940c9,0xb665a32c9960cae65632,0x309980cbe65e32e9970c,0x40060480f990cc66623,0x6c05054222040001c11],#[0x4001a6001407e4502042,0x5ec4801013118209206,0x42601274090600b48426,0x7018950b12a4460c44,0x8415141c03181c1520,0x9802008020080200802,0xc6c51c831af18433f199,0xd6d82801e1101ec2c460,0x5872c200e022f2c57844,0xc4013215c216c64300e,0xaca47b908ca47583156,0x87a5b105e84003c08739,0x9f98c000002505b024d,0xd0f505b61002d58a4684,0xe22ea097a314a0ea0ed1,0x41001a0b0100870206fc,0x1bb421c42002fe62941d,0x879c414d075c41362c40,0x941265826c0a50400c,0x3e24317882d702003b42,0xdbd09d96081ee0803682,0x250634c4b41b2100b21,0x16c32684]]
def g221H6 := limbs80 #[#[0x38104020380100010112,0x1900000000000000042,0x88000d17000000000000,0x41cc020000004570,0x8000170005d9c8e418d0,0x80b000548000000000,0x507c240000000000000,0xc0962200000000000000,0xf000016000dd8822000,0x860003c83000404000c,0x40d000807000813c2,0xc2000000000000000406,0xd1b8421040000000004,0x40a81d00000000000,0x11e005000,0x200040c0000000000000,0x81b11dd1a00009,0x408c1100084b44910c,0x81a0000000000000000,0xc5041400,0x58120000000000210ce,0xf0000000000000000005,0xc1581ed1501fc4,0,0xe0000000000008010000,0x80]]
set_option maxRecDepth 32000 in
def g221D7 := limbs80 #[#[0xd48105941054c1054810,0x5842054c2054420d4c10,0xd4420984205942058c20,0x81105885058450d4c20,0x4c110481101491010910,0x5411050910501104c910,0x595105891054d1054910,0x9411090910901108c110,0xc8110995109891094910,0xd4d10d4910d4110d0110,0x14520d9510d8d10d8910,0x54d2054520541204c520,0x941208c5205952058520,0xd4120995209852094520,0xd9520d8520d4d20d4520,0x54950545501895018550,0x94950945505895058550,0xd8550d49509895098550,0x546105421050610d8950,0x59210586105521054a10,0xd4a10d4610c821059610,0x54a205462054220d5210,0x58e20586205522054e20,0xd4e20d4a20d462059620,0xa7f3758b5058750d5220,0xdfafb7bbbddadf6eafd7,0xdfefb7bbbdbebf5d9fbf,0xf8fbfdbdfdfef777b7da,0x31ee2423ffdfdfe7eff5,0x6e66c25d4788ba0f197,0xa010588028a92d356494,0xc594183bb0005760062c],#[0x8098b2813d63020aec0c,0x2bb043165080eec0415d,0x8f7d511e0ee6081dc810,0xd31464ae28c15d8914ba,0x46eaa48dd4c91bea8a37,0xaa24df484994baa32973,0x4ca5d09b4a993693226f,0x544e3e909c29752692ca,0xa94ba9c49653852e871f,0xb1157e512afaa255f484,0xd7d513a96ca552594aa5,0x714852ea752594e94ba1,0xefaa25c15d8b93b89725,0xa45dfdc4bbe38977e512,0xd2d88ba4b1175f522eba,0x8cba4b1975f532ebaa65,0xa5b21749642e56e65d2d,0xa1f49643e92c47cadd0b,0x2b70284ae294a5d4f94b,0x5201aea40a5c0802bb14,0xaec7895c4f02bb100e7,0x84455d0892b891297022,0x15d8c15b8180576222ce,0x902ba9202571400eec60,0x2bb2625714c52e09815d,0xa80574500eea681dccd0,0x5763262ca64f58cc82ba,0x4e7ec69ca5c1383bb190,0xaeaa415c9482bb273165,0x6c1dc0da5b81b1f73360,0xdccd9fb99b3c73360ee4,0x514bad17552a20ae4a81],#[0xb24a496294bea529754a,0xb39649296ed28add2524,0x70a462cb2ce99259cb24,0x862cb48e99291cb25229,0xcb30e992620b14c2b709,0xca5c2983bb4c05769862,0x92682bb533165a674c94,0x14b85407769a0aed34e5,0xacf39719e0aed50e592a,0x774a00ee540e9d679cb,0x50a7cc614f58c2a2b085,0x8ac22c1dd8282bb05316,0xc2cc59459f318b3d6316,0x154c5233a8745750e0ae,0x31eb1862b700c8ea629,0x2bb0631650c74c818e59,0xc3964187ac6301dd830,0xd74100aec30c59461d32,0x120ee224f9d441eba883,0x2e624cdc4498b8890773,0xb48dc96aaa92d3373126,0x9496baa92d4b615a0aec,0x6bbb92d74725abea4b5d,0xbab32b745abea6b5754d,0xb2970560aecc885c9b94,0x51680eecb815d958eb9a,0x40aece0a5c1c02bb345b,0xe4e4a5c1c83bb2f05757,0x41dc18a5b83105767242,0x86a82b8bb0773620ee2c,0xaea9d55f52aabaa55525,0xa554964aa92c7557d4ea],#[0x576ac8ac3592ddaa95b,0xae0aed74a5c2e83bb56,0x62cb78a5c2f18b2d72b7,0xd6015dac18b2d83d63b0,0x15daf98b2df2970be0ee,0xac82bb593964b246e564,0x3b8dc0576c052e1801dd,0xd45721a0ee9701dcee0,0x9708456e0f905c4722ba,0x8038e7011585e23b0c22,0xae51c89ca210b9441f73,0x1c15ce399a9c731538e0,0x5c21afb83f2b707e0ae9,0xe86b9c60d758686c50ca,0xba3d1e737a4ce2f495c5,0x805719086c51459d1e8a,0x73c20ee58415d2402b9c,0x40ee7881dc7103ba6107,0xa44a0544942a8120774c,0xe05451c3a823855046f2,0x4d1c2a9a32d7546f2a48,0xc2a1138665470aca8e1d,0xa1c8552390aa84e15489,0x81512b0ea0561540ac2a,0x22b0a64561d44ac2a895,0xcca561594ac3a915855,0x2921541243aa1d85543b,0x8548b96baa465544902a,0x8b97ba174d642e5ee45d,0x3211785422f08845e14c,0x1786522f0aa45e1d08bc,0x5722f08e45e1988bc2b1],#[0x2f0a865e1dc8bc339178,0xcc85e1590bc32a178554,0x5e19d0bc2ba1784742f0,0x5492c2aa1f85523f0ee8,0x826b2142d744a5ae4958,0xb2964f632cf2a458b5d4,0x88470305aea79e548f27,0x5430f4c461e588c43b81,0x45ae898b5d5031aa1861,0xe49cb5d5097ba9a4d653,0x61506516b9222f72365a,0x525a6b14b65549302a32,0xa6b2062d74a4c2a94985,0xad85415b0c62b614c56,0x8551670ca2b615456c32,0x15c5aeaca0545916b8b7,0x5aead18d4d730a9ae4f6,0x2d8bdc5896b8b94f6170,0x354ad31aa566154ac5ae,0x2da6b2582d71bc9aa969,0x7b13e61527c5ae381355,0x404f64805ae909854a12,0xf71825ae30cb5d2217ba,0x49aca053594016b8c52,0xaea493594926b9824d72,0x721d48e43aa138752265,0x588ac2b8954d652b0ea8,0xba6b11763522f02a25e1,0xb99785532f0ee25e15c4,0x4d644a9ac4961dccbc2,0x652c9ac658b5d8827b29,0xc9eca78b5d8b16ba964d],#[0xe260bdc0c16bb112d763,0x13d8cc26b1984f62305e,0xd0c27b2184d64305ee66,0x16bb184f65309aca60bd,0xb204f6540f2c480bdd8c,0x4f624c5ae298b5c1316b,0x44c5ae6993d8d326b1a6,0x9ac868b5d9327b2264d6,0x66935ccd27329a2f7434,0x39d4d26ba9a4c75349ee,0xda6b2992f72329eea69,0x2a94a4f7036dee66e1dc,0xc98574950aa92a15ca54,0x354965ee52cb5d64a6b2,0xa49acb2cbdd25a6b24b6,0xea5393592916b9524d62,0x34b5c69a6b2cc2f71989,0x5c6816b8d44d659a5ee3,0x326b2854d74a09ae5413,0xba0c4d64189aca18bdd0,0xd2f715a9ae62535c4496,0x715b0cc2b615856bca92,0xb0aa8b6154d6c3b8ad84,0xecad3595926b2ac87745,0xa0985740b0ae2f705c5a,0xd9727b2ae4d655c5ee6b,0x26b2b48161685eecb8b5,0x9b82d70705aecd13d95a,0x4d65605aece0b5cdc30a,0x56a9acad4bdd582732b0,0x9acabcbdd1797b8af2d7,0x2c531c58c3b8312d7472],#[0x154eac2a9558551aa9ee,0x2b26b2562f72ad0aa956,0x6b95d4d62ba9acb58bdd,0x5a2d74ba9ac9758552e9,0xd65ae5ee35d3d52d27a9,0xbe9ac97d3596c17ba584,0x6e564bdc6ca7aa5b2d74,0xf8b5cf026b2d92f73b2f,0xd8df30a9be2f727c5ee0,0xe27b2422d72849ec5093,0xba3c2d72789ac4f18549,0x74d628ec2a51d3d92216,0x638ec2a71cb5ca3a7314,0xe9aa51cb5d2396b9c74d,0xe91d39ca3a6b9474e528,0xd3d8df97b83f4e748e9a,0xc3097ba412d717ac0ecf,0xa6b9e14e72c29ae58535,0x3c00780009ce98535d30,0xa05280f002c807801680,0x9a823a08281de06b017,0xdd83480c682f40b18298,0x44c10683fc0f583a80,0x57014c050c133049e12,0x6c219b064c18285cc165,0xa1f687a41d8072c1bc8,0x6248090c237889421408,0x2980a2427c89c8263896,0xe78b702ca8aea2b10a98,0xa0cb63248c5030d0bd82,0xde43658d6034b8d0233,0xefe3b38eac3a10e5c386],#[0x7a410900e3f38f763cc8,0xe45d114644590e642b90,0x4b892a249b121447991a,0xf13ee4eb937e4d39314,0x9156e553152453b14805,0x9678590961857c95ca56,0x7d25e5976e5cc96fc5ab,0x2663d98b061c984c6099,0xa68699da670998c65419,0x6d51b326c21ace6a41a5,0x119c286fe9bda6ec1b7a,0x41d287381cba7231c6e7,0x1e2a77d9dca7641d6a75,0xf7a7d11f007b21e92798,0x9481d203c8049fec7eb1,0xa85aa13284220de82d20,0x89ea242882a1da86aa18,0xf423988d723208baa2b0,0x924f092d2478911240a8,0x262497b25cc965a56094,0x7069bba6d09a6a664991,0x1e9f8a7c89e5274c9cd2,0x4a32a8b0a22286ea1228,0xa70a980a582940a4828f,0xc0aacaaa72a4aa83a9e2,0x92bf8af4aba4ad82b3aa,0x2d44b4b2d00b312c96b1,0xe1eb792dceb662d80b5a,0x6cbceaefebb3ae92b9b2,0xec01afeebf22fb0be62f,0xc3ab0bec273082c17b02,0x8231ccc65317ec523120],#[0x9b2f8cb1b294c98b22ac,0xb420cf63398cd9b346cc,0x54ad48b50cd3ab48ad15,0x6ed90361ad80b5ced66b,0xdd83738dc136d0daa36,0xe2cb868e0e37fadebb79,0x7739b8e64b964e4938e8,0x2ba9ae9fba5ee8e3a0ee,0x3b8cedb3b44ec4baf2eb,0xc96f1abc3ef04bbeeeec,0xb0f613d3cf443ce4f30b,0xcfa5be66f8cbe00f753d,0xff9bfb4fe1bf52fc7bed,0x5040fb034408f0144014,0x2c241081c1d706c41850,0xc3830d543290bec2cb0a,0x4dd126446310a43ed0ed,0xf5170459915d4541145c,0x51bbc6c31a2c65f18b45,0x1fd47cb1e847751d0471,0x3fc8cf228c86f2114821,0x849e126e499325ac92b2,0x4ae12aeca9529c4a4928,0xbb92e7cb8b2d94b3f2c6,0x9931a4c413094bfd2f8c,0xd359cd3d343cce7332cc,0x39c4e3f3834df136f4d8,0xe74f5d3cacf093b44ea9,0x4d069411501b3fccfcf3,0xd12b446d10b43ed0cb42,0x18b45ed16b456d14b44e,0xeb476d1cb46ed1ab466d],#[0xb48ed22b486d20b47ed1,0x4a6d28b49ed26b496d24,0xbed2eb4b6d2cb4aed2ab,0x6d34b4ced32b4c6d30b4,0xd3ab4e6d38b4ded36b4d,0x40b4fed3eb4f6d3cb4ee,0x6b516d44b50ed42b506d,0xb52ed4ab526d48b51ed4,0x546d50b53ed4eb536d4c,0x5ed56b556d54b54ed52b,0x6d5cb56ed5ab566d58b5,0xd62b586d60b57ed5eb57,0x68b59ed66b596d64b58e,0xeb5b6d6cb5aed6ab5a6d,0xb5ced72b5c6d70b5bed6,0x5e6d78b5ded76b5d6d74,0xfed7eb5f6d7cb5eed7ab,0x6d84b60ed82b606d80b5,0xd8ab626d88b61ed86b61,0x90b63ed8eb636d8cb62e,0x6b656d94b64ed92b646d,0xb66ed9ab666d98b65ed9,0x686da0b67ed9eb676d9c,0x9eda6b696da4b68eda2b,0x6dacb6aedaab6a6da8b6,0xdb2b6c6db0b6bedaeb6b,0xb8b6dedb6b6d6db4b6ce,0xeb6f6dbcb6eedbab6e6d,0xb70edc2b706dc0b6fedb,0x726dc8b71edc6b716dc4,0x3edceb736dccb72edcab,0x6dd4b74edd2b746dd0b7],#[0xddab766dd8b75edd6b75,0x622840281107ddcb76e,0x2a1c21068441f0f04836,0x140e0104010320b0b014,0xd882441284890140d,0xc62c0004268104d3a180,0x3050b88e424a049044e0,0x90628832030b44aed0b0,0xa11405d52e0e4067100b,0x92e0a3ba16e8ab402b74,0xbcea1861a5b48c41a2c,0x5a0a12a2aca69308385f,0xc223844708946858190c,0x7b85ca32a75a9590e111,0x1220f69226fe53788492,0xf09220fa4863e02441f0,0xc7dc118f7ef21ef09226,0x9c198f38331f7662ee08,0xc2299087dc118d7c0489,0xa887088f330258df8129,0xd399487234d474e65994,0xb50655cd604521c8d351,0x6e067bc221f854023477,0x52f2283237083197c8b8,0x7c00648ef7a8198f9302,0x989947f1ca823370831c,0x23c38491ada81a662fac,0x6a0c9870875c65d69940,0x1fe064cf883199c090bb,0x2c7c23df410f7fb0111b,0xf410e7a5fd8234695843,0x5ffc4580892430e88c9b],#[0xa0c77c11f79416994904,0x1170fa089b9c21a80e3c,0x6fd0448a7ec8b4cd3ad4,0x3bf023bf0238e9d92995,0x8032ef5608a76d04cfc0,0x3cccb12fc11a80ce14f0,0xf22f7583322e1dc8ade8,0x94491bf44a31ea48aaa6,0x60cc95f02264bf94487f,0x58bff8ab0a48bf9449dd,0x3ccd12b7cd3632ed7494,0xa7fc4491bf44b5f02264,0x6651fd888a88e5dbc50c,0x55e3e348624152cbf6aa,0x8e0893842d98435f2c04,0xba8af4122ba4147c23df,0x880cdbf1c1137e38226d,0x81e562b24dfe5446fd82,0xf7c69a23cf1d508a5b64,0x571c0c22d3c238f846bf,0x47a4867f84481e9c6819,0x132881cfe02445e38091,0x508fe2237e9813277038,0x6f210e728f08abe79011,0xf210e6a3c225b8241c21,0x7bec86d40e789225c11e,0x2c009957321cf12446a0,0xae914e512140f7d90e3f,0xe0141aaef4893e521ca5,0x3c0191766122a4be9119,0x112d7732646f5dcc9943,0xe421ec8431fecc245bee],#[0xc8437a037a034efde64d,0x1a77ef326f210f79087b,0x207e03187e031bd01bd0,0x1f20418837fa20837fa,0xf8cc193a9c4b207a5a59,0x94193a10a5903965064c,0xc1905478440f19832365,0x4518f41103972064cf8c,0x36aae0c9d4da5934f958,0x647a037a031e3d0447a0,0x88206941177e82275369,0x1244ce7c0226610393a4,0x10798861ff023204137e,0xbe512041218a0860679c,0x195b80db80db80e6c844,0xe48c969612b701b43d23,0x25efa249e7b1ab0a4775,0x91b632187c0332272eb3,0xd297321acc9441f4b11,0xf449cc12835c79e631b1,0x41033f08906b9d045bd,0x452043fc091080c80de6,0xc7c23acbb4340cc857cc,0xf9aa08ade40c73c75422,0xc40c40cfc224e7c141c,0x4095f8cc7b3086407b81,0x88d220157447823301be,0xc24520487c691340d0e7,0x661229e08e7cd50455ec,0xbe00c7df0063ef8031af,0xbd20c7704730845c158f,0x20fd14334a151fc20211],#[0x1df06a1a4c7e00c7afa0,0x680b323a412023c11ceb,0x818e156880ec941f7d35,0x143da08c85f0896e1120,0xc4163f00638fc018dec4,0xfec47488ed40e7d1111e,0xd2319b77a9117eb77228,0x6595385d1538a8322700,0xe98a21b1283e446f9a6c,0xa8470c8d72a871c3a630,0x9d915e591807d3196452,0x7b2629542efa626c03b1,0x686dd631f42c53c6d4d1,0x24daa15336494cd9248c,0x63d72b58085a66c9097b,0xe315136b8433d88db11,0xc7ecc0ca37aa892b71a2,0xe2a243e95062f54c084c,0x8d3ac73e14444e74c73a,0xcc0cade602196b2f0864,0x995bf8e0432efc90d3e3,0x28870c8e9c324cfc472,0x2f7e888819bbfcc0c8a7,0xf7ae21c36c41872a2e3,0x10c8bf00a2074a631f15,0xa2261c2193bf66064eda,0x1fda4644687f81947231,0x2c8f3a62dc71512d9649,0x3bb2502bbb83dc71512f,0x50f541030f541d744c75,0xac63862b20e29a630e2c,0x98aba263c754129d50db],#[0x977a122fae4896cb24af,0x27bd8654257c64957e64,0xef6ea1200e0b2ca18789,0x30826d58b7650c1c2080,0x6c55cd8993e259218414,0xb0ce450f2c280d7362ae,0xb9558f69d0eb61da743c,0xf3ac7b4e872c0f05960d,0x5830ed963b7d05a2b438,0x3b554c9b585449605d16,0x9301b5915d20a6be6d1,0xc634fea64656fc63185d,0x62dd3a1ea5c105e84df8,0x649b18722e320d550f93,0x6]]
set_option maxRecDepth 32000 in
def g221H7 := limbs80 #[#[0x400400010000ca081102,0x20480490000430c00081,0x3c600600609300008,0x300338f1c00001810c0,0x200344c2020461440450,0x30b0c63802c11c114610,0xc30821021ca0c100b140,0xc08125200b0c31c00961,0x254930140c908800440,0x1100908010304008b1c4,0x600100400b2025410000,0x4d50000100208c08620,0xc320404e3c420a080083,0xd3410012411407c60710,0x29c0020498c750004a00,0xc0107586182285141041,0x150002d82803070,0x1052a41ac000000,0x3472b80b40001040800,0x4a038702f0000312dc00,0x90000180dc000104d806,0x251497332d05dc021214,0x108,0x1128c000121dc00,0xc9063422af042000ec00,0x10002607810477214406,0x1b0784007d06d4000248,0xf2059b05ce05a5251871,0xfd046c00010754014320,0x8f01e8035a012101b907,0x20234000325a8000301,0x2707b61e40001084800],#[0xd112d10383711213f800,0x127c8000004f8000110,0xe8000000000000000000,0x2f04c3060c0000710d71,0x24000043400001215307,0x23800000000000247,0x210e8000000,0xca00a4227401b0234800,0xc077c00001390060801,0xd203e805ff06ed130301,0x100000211a2476004406,0x1036c034502fb06,0x3028400e0000000,0x12800,0xcc234c00000000000000,0x5405380002070b069203,0x2b07e000000000000208,0xaf7500000200a1818f10,0x1501a374fd05f8000102,0x6880000000221,0x204140002081800,0xe40001124230ef013400,0x861bc00020230000302,0x305ca8408000102,0x50000000000000000000,0xa100ad0668000202bc00,0xec000000000003082923,0x19f037a7388000386,0x304b8000000,0x1c0002235d00a906a000,0x71421c06b00308000223,0xd1525b015c0834000007],#[0x494387113f078f21ff32,0xdd011300d80722008571,0xf5052c000222bc000232,0x58000102580000000207,0x1012544131148e017a07,0xd10520065b0572055403,0x301b40003076d03e103,0x5b02e102a4027c822800,0x5e062a816904b5125b08,0x5800e64594068d016104,0x225b8000301,0xc5063c025e04ac103400,0x7b25d0000004e8000264,0x104a00001124d05,0xb80003450c0002045800,0x990742047000b907ec41,0x3d42640000000100d400,0xf00000000302d4456205,0x330b40000000207,0x113200001544701ec00,0xf80003056632b8000000,0x9c655f210c0000000306,0x4e0542027306a8000205,0x2400001023c000004,0x31070e07b80000000005,0x75007f87394000121,0x33056b013214a6032000,0xb9711c00010424000100,0x13066108400003017363,0x104cc00000000000004,0xec01fc0000000101d523,0x221c50229022432],#[0x3e04e40000000065a400,0x2e228000000000000003,0x4c07a800000151007100,0x11016400000003226d08,0x6c00000000069c014b22,0x439106c606b600,0x44000107977124440c00,0x855f02,0x302b400020574000000,0x341a800000000000000,0xb800000000737f204000,0x24000205ea401532d640,0xa0000000000000000101,0xc707d507600003031841,0xfd04de205701fa02ba05,0xdd638003940000000100,0x2804ed418e02d8000040,0x49231110d932bd333250,0x51458c040206ad10c503,0xbe05ed33f3059500e906,0x8b20b6035103d8000105,0xa6035c0000054d058424,0x105d302b313cd41ec01,0xd8000271c80000000000,0x260bc051601dd20,0xa702d2026c12a8000000,0x20641128807,0x125dc03e62468000000,0x340a30680000000,0xb507de41f72350000000,0x20005503006384223425,0x8000000000000000202],#[0xa8043d90b44538000305,0x7912cd0468000000c603,0xd404290014080c000012,0xb000000001215630f820,0x1027b55a225ca80,0xd000000001062c000000,0xdd028000000002075e47,0x202dd245422b421bc43,0xc80003077a0013063800,0x8c0000524c00b6006710,0x325407480000000321,0x540000000103f0000000,0x58000000000000000392,0xc8000000000000000123,0x1855400000002069512,0xfd06c3073e472c029400,0x213f022a00000000003,0x61071a93a0000103f400,0x107d90844036607af05,0x20000120c80000000000,0x68000000000002047808,0x84000005126451061b41,0xc2002b03bc000207b273,0xcd063200b202ca93a800,0xc20798000321c2410307,0xd000000000000341d686,0x4100f707d00114454704,0x344c00000000202c111,0x44036800030790039c00,0x1055c000261c3018552,0x44b606d8000000,0x5ac000207c000],#[0x3400030398000113e400,0xd0000241982239044904,0x1008f440346e6524b46,0xd702770489739b066c00,0x7105c00003080641a605,0x22b9068721c8000014,0xc000205917144000000,0x201f7083203,0xd4000000000003062000,0x3544806e00000000221,0x120ec00,0x2826000020494000000,0x1415b05ab046400,0x70000000010100000000,0x2065e04380739821903,0xeb404d1290000301cc00,0xb0000000000000000030,0x32044605e40000000203,0x979c00000000024f04,0x21b046104aa01d000,0x32a441c00,0xc1000400030698000000,0x500002835502ff026622,0x8a03a000024223222e22,0x1e14640003502603d402,0x244201da202f40,0xf404820174017c000000,0x330,0x240,0xb4000000000000000000,0x88000302c40000000207,0x303540000000114be00],#[0x306e906700000000207,0xb112b40000000204f400,0x71605,0x1033400,0x32b40000000000,0xf407062224826b012c00,0x2,0x333900000000000,0xb00389257d0604000000,0x640003045233c424ac04,0x2050e01ad036212ec06,0x4507c800000000000000,0x34000000000003067807,0x61005c00000001049105,0xe600de04a40079033342,0x5932c210cc0000000071,0xfe02a324bf000b031e00,0x452025026a43b6065730,0x1c000207bc0002028e01,0x40000025d574c906f600,0x41f80000000100,0x1229c00000000000000,0x46df032d06f203dc00,0x4e346910407114019133,0xef006a233b038f20de54,0x94015500bf014e071c10,0x3040f008101,0x2c000008140000081000,0x4d741fc000204,0xf80002440a2104000000,0xce30e40000000205b920,0x2037c000222c400f214],#[0x1141f000004018000000,0x7c03f9135e1285203040,0x3f34cd05a322a422fc12,0x45220c08530118058815,0xc605b402cc4104221b20,0x48c129f46c4147b13,0xfd03b80000000060a400,0x22019b05f5202907e506,0x4040001822582,0x1701bc23200000018800,0x1031645180000000206,0xc0058c00010254000000,0x55834b02a80000000120,0x2484000304,0x305d8000306e400,0x3076400000000000000,0xc7009f06bd1378000000,0x26c7145606cd067d12,0x2c0774000106a7153400,0x937151061d04fe570315,0x2414d908e049d21,0x213ba054643d400,0x20108000000,0x92211300180000050400,0x3801e4033b46f4000000,0xc000203c5083c076810,0x371230104024b00,0x25102f66fc0003525c00,0xb0220232e2230a03c913,0x30096020c124b22,0xcd82100000047f32e400,0x18000000003083a25],#[0xd3034c08080003026000,0xb904c4000220eb440721,0x2277400010800000380,0xc0000000000000000000,0x3078b01,0x121cc0003246104f000,0x333370340000000,0x2502ef125c0000000000,0x302000002504207,0xbd10830293030574f400,0xe3079c22d10138074c20,0xc4052400000002039101,0x1d05f2053112b9002301,0x16407a056d0728000204,0xd350c00000235703c313,0xdc000305580000000141,0x3d329c22d4434704cb06,0x3a0549041b409c051b00,0xf0000342050440000100,0x22e057c016b07e901,0x3c00012100756f03ec00,0xd0051c000004e0000201,0x5064d06740627082e00,0x14000000013478000002,0x1c0003029d004d00c802,0x330710000306b8000308,0x120e66160000007,0x74000304bc000007c400,0x2000011310003400f900,0x980003353c0374000140,0x304,0x13338000000],#[0x1146c03a4021c000000,0x980000000107a3025306,0xce12966042048402eb02,0xe10048011c5454000100,0x6003b7073540a8000146,0x23334200000041,0x20647231400,0xc0000000000000000000,0x1006000000002247373,0,0xb4000303240003058000,0x20550851a01a8000241,0xe0356503ac0000000300,0x6c000000000001357005,0x1]]
set_option maxRecDepth 32000 in
def g221D8 := limbs80 #[#[0x88210541204405008010,0xfdebfbdbbb7af9fd4250,0x451611199185646fffed,0x99441651298c49631498,0x839888d6224984916120,0x20355941563055881b50,0xe140388c0e13038c80e0,0x88d56238940e15038900,0x5d94d56535d8cd56335d,0x465589956168541a3206,0x5651558c556115595956,0x5156545d852250485411,0x58dd56275585e15075d9,0x55588956125595d56475,0x6185d895f52575495761,0x15629558655658558a15,0x80e7530954c275209548,0x9540e74039500e720394,0x239508e442394c8e7503,0x75239948e55239148e64,0x4e7533954ce66239588e,0xd45a55169505a6653959,0x19d51a55469d49a55269,0x5049d4c655319d446551,0x2451498c5253149d4125,0x85256149d45265149545,0x9995256549d4d2553499,0x379d49e55279d45e5517,0x55159d51e55479d4de55,0x56661595856461599456,0x589646259949655259d8,0x3c01f0009d89666259],#[0xe00c80b50a208907606,0x6514c13812811a1070f9,0x41f21d91b219f1871761,0x2ad28727125b24622821,0x5433a32230d2f62d92c5,0x63df3cc3b539237f3643,0x48447745c44542e41640,0x4e5305144ea4c04a949c,0xe5fa5e05bc5985795625,0x6a468066b65463e62a60,0x9777674c72a7066e56c8,0x38538338127fc7db7c27,0x92f90e8f68d28b289187,0xfd9e19c29b198f97294e,0x8a9ca6fa5ea49a31a1c9,0xb6fb55b3cb13af9ae1ab,0x2dc16bf7be2bc7baeb8b,0x4d25d00cd7cadc78c59c,0xe0ddf1dd4db1d99d69d4,0x1412014400054510110f,0x61308841a8581424102,0x1c22191f5d0421a01b82,0x16239d0ba12043831503,0x29616524a5070c181d1e,0x452827802f172c252669,0x8ea08460fe4c132f5f80,0x137a8a88b7812e6b245f,0x7e22269f004459c0ab78,0xd443690420156702900a,0x9c1297810fc067d12265,0x508833f585011cf811d9,0x80273e0249afe8811978],#[0xdfd0497f4123db014dfd,0x38486bcc0883f92f3023,0x12e444a7e40917f0c48b,0xd7044b423bfb40967c01,0xf8449357c0091c6f02af,0xdc41073d3e01241e224b,0x443fc449bc0111f7201,0xc448c037dd806601efe9,0x6c4209246bad8c30493f,0x8efba2228bece226de2,0x7047bfe9004e77c890fc,0xe6e2261e1788247de56d,0x967110d2d75116f0892,0xe680463f01207e0258f8,0x1be8e0451cecca0489f9,0xe89cff8b920a2bd3e005,0x1197fa42602480fcec,0x5f089aca49593d160f5c,0xda011afe0240f777d13d,0x35f6d9213d7b6ea140cf,0x9a01164fd6408cbc5902,0x918bc90962ee9ac1207f,0xc7e491f7eb0122efd1a0,0x91ff84213cc7e49150c,0x4506de484c66df509cec,0xc2495c904d5c225bfab0,0x643d08e7e8695bc016c,0x5f844b382d4466496f84,0x306df5b1182246fd0089,0x2146fd0122ddb844cd7b,0x96f17113dbc9096b87e1,0x493792096bf7d413d708],#[0x32d13d6a48c3a91b0fa,0x9f9ed24285573fe8f728,0xb3e488c94793e3201824,0x49539e4030488cc340c,0xb1c450af920e17f5d4a1,0x28b7d9e44a539be263fb,0xdc60]]
set_option maxRecDepth 32000 in
def g221H8 := limbs80 #[#[0x60381000020003c200b,0x1e010200002020386402,0x200e030a808700f00018,0x305804050105c0e0e058,0xc140143a1216008001a0,0xf004020113800020,0xc3000000000003000606,0x80010010383824010200,0x1089c40031603c000105,0xb020000a020109c0a02,0x4000906c1a010185454,0xa8020200004100607810,0x800041b0d0080005018,0x109210060309980180f0,0x228000141406048502e0,0x13c1004008060a0282c0,0x8800602198081205060c,0x2004340000000b80706,0x10109800070c000e61a,0x22244a8080a240000400,0xf4003817bd47c0d0000c,0x304c562b120400006038,0x112800180d01828202a0,0x80000008060112830601,0x501909008d052050000,0x68363f0081000170400,0x4800e606098081a3204,0x48080601018340000,0x20d070002212048a818,0x4000708004102a000f4,0x708659008ac004d068,0x58a01800000a81400190],#[0x98000034721c00818600,0x2a02f0110410a001290c,0x806e000062d9e00904c,0x451c8000208f800026f,0x800d800004d1560b2800,0x181310000630be01260a,0x721288074e0cb0a37021,0x48000000008310000011,0x605aa414c093c0cbe2b,0xcc0484ccb60db4039800,0x40a024bf0000409,0x4022e4bb9115c0af000,0x940b7e100209560f5000,0x4286f800000006412c03,0xb212a04d9608d60ce90c,0x22df631a0042082,0x74411612e8000682f000,0xc489720baa079ac6d286,0x5802bc044489900ce206,0x94072000000d78000607,0x6862a6b3411a206,0xbe07c80000827049b000,0x720a28000602f8000610,0x824a2e6c1e29ce8d46b0,0x468006e880000000406,0x88000402901230000000,0xd291a000022d28000411,0x607500000000083,0xc04bfe0f981030000000,0x6c01c271e0ca7c10f630,0xe02d40e64099c69e811,0x400b3c057c82e40eaa51],#[0x7010900004266602aa4a,0xb0000000000002c0ca0c,0xa2910404ee4e88000488,0x2439a0fd80006f1a40f,0xa84c4851fc6c4a0ca00b,0xa221098000485,0xbf0fc4416000060df000,0xa60c8c90d00c04a1244f,0xf8101000062340000006,0x944e4408e221be4c0207,0xd082c80000000612088f,0x1e8c628500906c007810,0x4a4be68e06856205680f,0x780000000685b6104e0c,0x20e9200c40e400006ea,0x5000020ec6002008c000,0xde85360bfa0c3a03b813,0x490820a1a01a4130710,0xf40e00080ca888000000,0x32417ae29a05d2901803,0xaa32f8094623ff00fa42,0xa0caa04ae12da06f213,0x5410c608de831c09840a,0xa8424ca3480006103812,0x7800000000088004bc07,0x60000291b2d1a00002eb,0xb00000000408ca217042,0x4800000006067c830a41,0x48000000000000000008,0x5e727e2162e2a40d9003,0x1fecf6b0e70000443,0xf6131cee980510000000],#[0xc0000004500fe000064e,0x4e073800000590000612,0xc7039a0990000409f013,0xe048ea9c2e2c64f7807,0x3c05b6914f0ef611b844,0xd60ad811180000000208,0x40b88c6c03cc11,0x6911ec113e0ff40ad000,0x5000026aea0278000210,0x5c05caee26097602c06a,0xfe46aa071046880c1440,0x2684788d7e86ba288809,0xc2ad9008bea3400b9a03,0x7c4118122e0a68000446,0xcc10700e4a12780006e2,0xec0bde88ac0fea0b6604,0x780000000033244b6005,0x622520008c0da42,0x86090a400413a2421800,0x34ee80217a4c6e9370ea,0x96ce760cfc2ef002640b,0x4086a09368c5404,0xa002180000863a870800,0x80000000000d1c010a0b,0xa8a20085b80002e29205,0x980890000209d0000061,0xa60b12cef6897e90e80c,0x320b90139000040a4643,0x3401862f7021a212d407,0xde0fc0000000044b300c,0xd62a1002e613446c2642,0x60f8e0de60d120d9e80],#[0x24ccf27e249ac11c800,0xc207600302ebb8419007,0xb800040d300004070e13,0xc68c5a0b747030000452,0xee025c018a04b000060d,0x3a0318079643c0000400,0x512cc0910410489820a,0x5d3286ebae0600000000,0xe605f649f04a3246a00e,0x3a2e760d4800040b540e,0x8a80c0000000004bb60f,0xa24eaa01e0071c80e44f,0xbf328c04a0009a879449,0x2000040870b320000401,0x8e1008000000020f6e41,0xd2a10000042a08861e08,0xa68e58000003b6b25682,0x4fe27506cca04d003,0x212fa0e74023a864000,0xba0b844ae00000425800,0x60bf009b800048b9446,0x270ea0044a072c442800,0xe6a44035e0b1a115413,0xf61028c6e6037c0d3e06,0x9229f0216e0d76617e4a,0x320f4e22220b220a148c,0x500c6e04d80dba05004f,0xa0019b0ff6937c0f78a3,0xf411ac0c180004236c90,0xd80042068a11900f1601,0x2ee2be8e6428cc6bfc05,0xc40d54111029e888bc05],#[0xd207de2fa8000000040a,0xcc2df89152e28605300c,0x5880140aae0c900c2402,0x9e616c615ac212b1a24c,0x106fb80fb009e44d1640,0x18000000000d280e3c04,0xe44f140e8a092c49d600,0x600a560ed4054a0a7c07,0x2206bc497e52a209620a,0xa0ea88e28a006800062e,0x670c40afa6c0a05,0x60248a73000024bc800,0x2800063378273411d800,0x960476eb80ade8000204,0x800060d048bbc0e1886,0xec01680000422821880d,0x38000008300000000207,0xd690c40566878acbe622,0xea03700430000629c200,0xe8000603280006af7208,0xa00bc206a811f64f6c4a,0xba4a4a2dae12984a202f,0xb2138211e62a2e4c5432,0xba07d642080000000602,0x6021844efa2d9011f813,0x35121081e42b26e6fa13,0x224dd803842dbe107a2a,0x4e9b0000412200ae20d,0xa4020806562b0e86f000,0xf6868ca6e80006924208,0xd440480000289641cc69,0x8a588f3e4fd8057006],#[0x292484cd60740499800,0xe8000461660e10000000,0x6038c225a0aa608f080,0x4800022120124e01af11,0x9d0c7813380004420223,0x4b19a036c050e0f2a90,0x34013ad1900006108250,0xa00ddc08102206416c41,0x6c6ec4ecc4a9800028e,0x5228000402d800,0x6e49928c3012e0000000,0xf0053a8c4885e80ea4c2,0x9807b4123882a810b412,0x5acb528b8a52ad12aa0a,0x40918000609240a5ea3,0x9000aa10ae130a00880f,0x28b2a0080855a12620a,0xa4813000060a300000ef,0xfa4a1a867e857e2f0e00,0x7c013087200d58858482,0xae040006760a70120204,0x8e484e07a2eb5c13580f,0x8e086610180e6810582d,0x6a4dc202060bb6062602,0x9e09b20ed80e200c0802,0x8cebb600b40628034013,0x480002219e033c121089,0xac86102af00000899801,0xb41146721a049e8f4012,0xda4f0e05b800000000b2,0x13329e04c4ebc00dd403,0xeae26c13680004801c01],#[0x780fd200bc0550418a49,0x8606d810400ef200508c,0x504d20007001e80cf441,0xee32b0b1de82ea0bd608,0xf0054210e24da2b26806,0x2000060d8807be03f880,0xf800052a9c2e8c022644,0x4e4198a6d0082e29bc0f,0x7401640036a65e6d0200,0xe211340408000606684e,0xeae8d0000204f44ca60b,0x4410c80004114a00f402,0xaa0df8000490d84c1893,0x7c0cc60c5609c409784d,0x7c015aa1288aa000000e,0x580000a56c0c66437a13,0x700eb812ce10ea08ae00,0x5602800f2064b4059e07,0x10c964bee6a16860821,0xee0e8710d031e60b4c93,0xb4061e40428ee600cc11,0xb02a700806064a05e64e,0x16a11e0fb80236031012,0x1c41ac138a055e063ca1,0x3c4dee052608b650e82b,0x8a096a2668000229b627,0xa332c10508240221405,0xec13320f0831de0bbe4d,0x9c116049c4cc90017e03,0x8e2a26a7ca1270ee3608,0x582dec0250000492da85,0x106960c780e0c06c812],#[0xd830c80140082680a800,0x100cd8119c896c6a0a10,0x5c0e50b05a0f6240ce2b,0xf0000601d800060b0c04,0x8c11c00bee6fa24a8a07,0x1ca33800044b52eb6607,0xfa83cc124212be8b3e05,0x880f800e98000000004a,0xd6129484480000132c10,0x40c420acc4390267632,0x600006cc380a8e8edcca,0x28cee08464d6e06,0x5a0de891d000020f4000,0x20000001740a4c041e08,0x5683002624094a126a11,0xb0000280fe0b8c859603,0x20cc84db4030c265e0a,0xb4081c001490940e324b,0x340f9480b000068dd411,0x1a13b60da269f800020f,0x36b0bed0d001d02aee12,0x80043a015203aeea9406,0x8049f80f7622080aee0c,0x80c2805fe81f602a10c,0xb1ac90,0x460e2c0bc89158000000,0x4000000782aae000000d,0x5e03664fe4ee2e006648,0x21020024249,0xa000da46b000000d6000,0xabe4e,0xc8000000000004027000],#[0x3a11280002702000020d,0x46640800064d5c215e21,0x1000000000000000020b,0x62a1800064e90000606,0x3000000002110e0ee800,0xaae2f4065a0768000603,0x9c40a84d78077e895c09,0xe6046c1060000405c687,0x1800060b5e6a3e128204,0x429d6469c01,0x40c5e4a680000000000,0xe8000200380000000000,0x440d28d802da0000609,0x203e000,0x40f80002421000,0x7c89624e0a84fe019000,0x7e09000000000606fc11,0xab068206400104098c08,0x4a9064137000020f5c6d,0xfc477e046410f800e251,0x4a6d800000000000629,0x40d6e83d821408c9800,0x201cc09de852800,0xc800064a8000f8000000,0xb60b6a002a860211580f,0x9e09a24270000701340e,0x403c00000000602,0x9c6a4ce0de4fc806b000,0x60ef8021201b0000606,0x3c03d0214a0958000000,0x864e7800020dac0eca41,0x2212811]]
def g221D9 := limbs80 #[#[0x284409004108220087f,0xd34a91e1389806a1282a,0x220018202142574ec5b,0x3b00093a490a5268079,0x2f4a021ec0087c803a72,0x80180012f00300024001,0x7]]
def g221H9 := limbs80 #[#[0x2020601390001040004,0x10100081d0512050002,0x131b0302cf024d4a02,0x6a003d010a220200030f,0x913131b10060a290724,0x30021805e2b1f0b580c,0x642766180604625393b9,0x4c44e0216c0a574d6c35,0x9091a058510703ac0310,0x45e06b0029355c1d504,0x132135c10304b1010180,0xd7211c1852771df624d5,0xc000c1b5019656e0540d,0x74b118826ec07c863093,0x4a04a103191f6016d97f,0x3099424a00d6459d1ac0,0x41e5442442501a010703,0xdc001b04b00740000000,0x6991c021240c37711,0xc148076847e01055,0x5bc0d0000c4a921540b,0x4ec448176c8f82565cd8,0x9000326f44da07a44ef2,0x3020c0e3267000000,0x7444e00000006568000,0x14000090401c415502d8,0xd0f4000000000009,0x139c08d243c118000000,0x118c000000107e84cf,0xe50a023d000001300000,0x4651280e4045407805,0x14e01511ab8564168066],#[0x35471049e67281082144,0x40328468077093105c51,0x3b0000000000073dc1c,0xd000000005ee0500003,0xb0000000146b17a00000,0x1ee748d0db134401110,0x9d66a0834067c0bf07d,0x1021418a43ea15c000d,0xa0175d27410099808000,0x44bc17c87784f141e5d2,0x6a418e028dcf955e803a,0x15d300004dd105d01a30,0xc45b072c11317c897055,0x4b0184190065c60406f,0x62025c1e024bc0f80260,0x786e01bb00fc138255d1,0x7f05fd07c40a9673451,0x70458556a518275819ae,0x4415d25d25d34611d390,0x94fd001000055f85f702,0x17f1320089000801a160,0x1357205e000045df405d,0x6425c85e411802c11c8d,0x86f0205264013d247086,0x3fc134000c00e07384de,0xe00000475d6701404570,0x15ae002c0dd027d54817,0x913051c95f2420003113,0x6102b484397540d910ac,0xc14681b2005d97805988,0x7117a03cc02103d95c,0x130d6d35a00030604940],#[0x880b9043415904845e42,0x10]]
def g221D10 (j : Nat) := if j=0 then 0x3f else 0
def g221H10 := limbs80 #[#[0x41b450c20c90050050cf,0xca5460d41150b10,0x322c9465e1b0544134,0xa5400c10000002800066,0xa1d3351f89c000000154,0x301c98750033114800,0x4c00008d060000000062,0x1551200000c081319d70,0x82785020000507200288,0x40f45d24002480000151,0x890481a371e0b3245553,0x89c5041e69]]
def g221L : Nat → Packing
  | 5 => (37,5,6,1507354,85,9,1032,g221D5)
  | 6 => (535,4,6,4718825,120,13,1075,g221D6)
  | 7 => (633,3,6,2228323,103,14,1123,g221D7)
  | 8 => (130,2,6,655370,68,12,1083,g221D8)
  | 9 => (10,1,6,65537,0,8,1039,g221D9)
  | 10 => (1,0,6,0,0,0,0,g221D10)
  | _ => emptyPacking
def g221I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 16 163 4 12 6 4 g221H6
  | 7 => lookupShort 223 1427 6 16 10 4 g221H7
  | 8 => lookupShort 291 1433 9 16 10 4 g221H8
  | 9 => lookupShort 72 331 8 14 8 4 g221H9
  | 10 => lookupShort 15 83 6 10 4 4 g221H10
  | _ => fun _ => none
def g221 : Forest := ⟨221,10,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221B5 : CutRow g221 5 0 37 := (@joinRow g221 5 0 3 34 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x20,0x60701a114000810209,0x448a141000a410c16038,0x45200021002051821120,0x2004402052014300080,0x209448a145000a410c1,0x60384520030044020520,0x14200181820944881c10,0xa018028348a58420081,0x8209448a141001818209,0x448a1c10082054022180,0x4551008400c160384420,0xa041402052051210100,0x128144b00931082050c0,0x70b04531082050c070b0,0x45310180540301100d50,0x1801203009009400300,0xc40211201c210300c209,0x10a21c31018054030110,0xd300300c40205201c20,0x300c402052019200180,0x540301100d5001805209,0x44920d20008800c16032,0x84420180540241100d50,0x210402210811420021,0x4022108114210001080,0x45208121082054022180,0x455100a410c160384520])) rfl
      decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_0 : CutRow g221 6 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_2 : CutRow g221 6 2 36 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_38 : CutRow g221 6 38 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_86 : CutRow g221 6 86 11 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_97 : CutRow g221 6 97 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x3050021,0x101a5831100010804520,0x814303050029101a5820,0x1040029141a48200104,0x29141a4810100040c0,0x653084430108002a0412,0x88300208000a04229031,0x8205402218045510305,0x21101a58310108000a,0x4128841020014022520,0x114101040021101a4831,0x10000008450290630800,0x80603498485210008060,0x35188853100040804520,0x81430200040205201162,0x3050021101a58210200,0x1402052011410a018402,0x218058520a0180203488,0x58520a01806034985862,0xa018060349858410200,0x14020520114110004080,0x4520814303050021101a,0x5820082040c260b04452,0x82040c260b044520200,0x1402052011300a018060,0x34985841020800220422,0x90310820440241804451,0x10008060351888420820,0x54022180455201040029,0x141a48310108000a0412,0x88410180400a04120d61,0x2001402252011410108,0x62301a885402001402,0x11201141020044020520,0x14410300c40205201c41,0x208402210209200300,0xc20914a21c5201818209,0x448a1c20010404030110,0x48200104040301104820])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_145 : CutRow g221 6 145 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x1805402,0x5100d51100000205108,0x90630181840241081c20,0x181820944881c200808,0x2a1088c0430088020b,0x8884400a0414020520,0x5142100400603518c053,0xa041402112051410108,0x203009088410a041402,0x5205142018054030110,0xd510a04140211205141,0xa041402052051410a04,0x1402052051410a041402,0x52051410a0014021120,0x11310a00140211201131,0xa041402112051310180,0x540301100d4001805403,0x1100d40100040805120,0x844303050029101a5820,0x300c40211201c410300,0xc20910a21c5101805403,0x1100d410300c4020520,0x1c411000106025108143,0xa041402112051410a04,0x14020520515201040029,0x141a4831018054030110,0xd61080800221088c032,0x108000a041288410a04,0x14021120514101040029,0x141a4820010404030110,0x48100300c40211201941,0x300c402112019410300,0xc4020520194108205402,0x218045510a0414020520,0x51520305040301105831,0x180540301100d610808,0x221088c03201040029,0x141a4821018054024110,0xd6101040029141a4821])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_193 : CutRow g221 6 193 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x3050403,0x110583100a410c16038,0x453000810209448a1420,0x800802a108a48520181,0x8209448a1c2000a410c1,0x603845200a0414020520,0x51520808002a1088c043,0xa041060343851521000,0x128145a0814301818209,0x448a1c200300c4020520,0x1c4101818209448a1c20,0x1000128145a081430104,0x4030110483100810209,0x448a142000a410412038,0x45200a01802a108a5862,0x2004402052014410200,0x44020520144102004402,0x5201441020044020520,0x14310200440205201441,0x2004402052014310a04,0x1402052051410a041060,0x343851410300c4020520,0x1c410300c20914a21c51,0x300c40205201c410104,0x403011048200300c209,0x14a21c5100818209448a,0x142100a410c160384531,0x80040c070b044531004,0x2091502c05301040029,0x141a4831080800221088,0xc0430180520300900d51,0x1040403011048200104,0xb041248310a041402,0x11205141080800221088,0xc0320104040301104820,0xa041402112051310a04,0x14021120513102080062,0x30389042018054030110,0xd510181840241081c20])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_241 : CutRow g221 6 241 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x1080281,0x44b088410108028144b0,0x884101818209448a1c20,0x2080060343890520180,0x528144b00d5110000060,0x3598c063020044020520,0x14410808002a1088c043,0x180528144b00d510104,0x4030110482100a410c1,0x6038453001040029141a,0x482101040029141a4831,0x10001080452081540180,0x520944920d6101805201,0x44900d41030500091412,0x58200300c40205201c41,0x2004402052014410104,0x4030110486101040029,0x1412482001818209448a,0x1c200181820944881c20,0x2080060343890420208,0x60343890420a041060,0x34385152018182094488,0x1c200181820944881c20,0x3050029141a58310181,0x8209448a1c2000a410c1,0x6038453000818209448a,0x141000818209448a1410,0x2080060343890520a04,0x1402052051420a041060,0x343851420180528144b0,0xd4101040029141a4831,0x1040029141a48310104,0x29141a483101818209,0x448a1c2001818209448a,0x1c2001818209448a1c20,0xa410c1603845200300,0xc40205201c410a041402,0x52051420a0410603438,0x51420a04106034385142])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_289 : CutRow g221 6 289 48 := by
  apply polarBlock (data:=fun _ => (w80 [0xa041060,0x343851520180528144b0,0xd5101040029141a4831,0x1040029141a48310104,0x29141a483101040029,0x141a483101818209448a,0x1c2001040029141a4820,0x1040029141a48200808,0x423090c04300810209,0x448a143100a0c4022102,0xd200180440205100d51,0x1040403011048310181,0x820944881c2000208402,0x210209200108000a0412,0x884101818209448a1c21,0x8205402118045530820,0x54022180455202080062,0x30389053020800623038,0x905300a0c40221020d20,0xa0c40221020d2000a0,0xc40221020d2001805402,0x5100d51002084022102,0x92008250060701a5130,0x20828160a209200084,0x816038443110001281,0x45a081540180428144b0,0xd5100a410c160384531,0x8250060701a51200300,0xc40211201c520300c209,0x14a21c52010802030090,0x88410200440205201441,0x2080022102890420208,0xa042290420a041402,0x52051410a0414020520,0x51410104000914124820,0x8004402058044420800,0x4022180486202004402,0x52014410a0410603438,0x51520180520300900d51])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_337 : CutRow g221 6 337 48 := by
  apply polarBlock (data:=fun _ => (w80 [0xa0c281,0x60a20d10008104024108,0x14200180528044b00d41,0x810402410814100104,0x29141a483100810402,0x410814200180528144b0,0xd410208000a24229042,0xa410c1603845310020,0x60701a115000200402,0x4102115001040029141a,0x48320080040241081451,0x800402410814510104,0x29141a483201818209,0x448a1c31002800422012,0x8140008800c260388441,0x1040029141a48210104,0x4030110482100208402,0x2102092000a410c16038,0x453100200060701a1160,0x108000a041288411000,0x128145a0815401818209,0x448a1c3101818209448a,0x1c31080800c260b0c054,0x208402210209200181,0x8209448a1c310208020b,0x4a2905300200060701a,0x115000200062301a8150,0x10000008450290640181,0x8209448a1c2108250060,0x701a513000a0c28160a2,0xd20080800221088c043,0x8250060701a51200825,0x60701a512001040029,0x141a483101040029141a,0x483101040029141a4831,0x1040029141a48310104,0x4030118483101040029,0x141a482001040029141a,0x48200a04140205205152])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_385 : CutRow g221 6 385 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x1818209,0x448a1c2000810209448a,0x14310825040241025130,0x810209448a14310081,0x209448a145108250402,0x41025150082504024102,0x515000810209448a1431,0x810209448a14310081,0x209448a143100810209,0x448a1451082504024102,0x51300825040241025130,0x8250402410251300825,0x4024102513008250402,0x41025150020004020520,0x11520200040205201152,0x1040029141a485200a0,0xc28160220d2000a0c281,0x60220d2000a0c2816022,0xd2001040029141a4852,0x1040029141a48520104,0x29141a483100a0c281,0x60a20d2001040029141a,0x484201040029141a4831,0xa0c40221020d200081,0x8441a142101804402,0x5100d5100810008450a,0x143100a0c28160a20d20,0xa0c28160220d2000a0,0xc28160220d2000a0c281,0x60a20d2000810402410a,0x142000810402410a1420,0x181840241081c310025,0x60701a113000a0c281,0x60220d2000a0c2816022,0xd2000a0c28160220d20,0xa0c28160220d100021,0x60701a113000a0c281,0x60a20d2000a0c28160a2,0xd2000210060701a1130])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_433 : CutRow g221 6 433 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x1040403,0x1124831080800221088,0xc04301080022141a8841,0x810209448a14310081,0x209448a142000810209,0x448a142000810209448a,0x142000810209448a1420,0x20828160a209200825,0x60701a513001040029,0x141a48310300c4021120,0x1c520084040301084420,0x810209448a14200a04,0x1402052051520808002a,0x1088c04301040029141a,0x48310208000a14229042,0x300c20914a21c520020,0x84022102092000208402,0x2102091000a104024102,0x15200108002a141a8841,0x180440205100d5100a0,0xc080702a0d100300c209,0x14a21c5200a0c4022102,0xd2000810209448a1410,0x20828160a209200104,0x29141a484200a0c402,0x21020d2000810209448a,0x1420008400c160384430,0x8400c1603844300084,0xc16038442000810402,0x410a1420002084022102,0x9200300c20914a21c52,0x810209448a14100081,0x209448a1410008400c1,0x60384420008400c16038,0x442000a410c160384520,0xa410c1603845200084,0xc16038442000810402,0x41081410008104024108,0x141001818209448a1c20])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_481 : CutRow g221 6 481 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x210060,0x701a11300020828160a2,0x92000210060701a1130,0x20828160a2092000a0,0xc28160a20d2008250402,0x41025120082504024102,0x5130008400c160384431,0x8250060701a51300020,0x4022102096001040029,0x1412482010000028350a,0x88640200106034381152,0x180440205100d5100a0,0xc28160a20d2000a0c402,0x21020d2000810209448a,0x143100a0c40221020d20,0x810209448a14310084,0xc160384431008400c1,0x6038443100810008441a,0x14210028004220128140,0x8400c1603844300084,0xc16038443000800209,0x448a145100800209448a,0x1450080040c070b04453,0x20040c0711814420a04,0x14020520515201001281,0x44b00951008400c16038,0x4441008400c160384441,0x1040029141a48310084,0xc16038443001040029,0x141a483100210060701a,0x113000250060701a1130,0x810402410814210081,0x209448a143100810209,0x448a1421080004022180,0x48630081040241081410,0x8000402218048630081,0x209448a142000810209,0x448a1420082504024102,0x513001040029141a4831])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_529 : CutRow g221 6 529 6 := by
  apply polarBlock (data:=fun _ => (w80 [0x100040301104852,0x810209448a14310021,0x60701a113000208281,0x60a20920008004030108,0x44510080040301084451])) rfl
  decide +kernel
theorem g221B6 : CutRow g221 6 0 535 := (@joinRow g221 6 0 241 294 (@joinRow g221 6 0 86 155 (@joinRow g221 6 0 2 84 g221P6_0 (@joinRow g221 6 2 36 48 g221P6_2 g221P6_38)) (@joinRow g221 6 86 59 96 (@joinRow g221 6 86 11 48 g221P6_86 g221P6_97) (@joinRow g221 6 145 48 48 g221P6_145 g221P6_193))) (@joinRow g221 6 241 144 150 (@joinRow g221 6 241 48 96 g221P6_241 (@joinRow g221 6 289 48 48 g221P6_289 g221P6_337)) (@joinRow g221 6 385 96 54 (@joinRow g221 6 385 48 48 g221P6_385 g221P6_433) (@joinRow g221 6 481 48 6 g221P6_481 g221P6_529))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_0 : CutRow g221 7 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_7 : CutRow g221 7 7 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_55 : CutRow g221 7 55 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_103 : CutRow g221 7 103 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_151 : CutRow g221 7 151 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_199 : CutRow g221 7 199 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_247 : CutRow g221 7 247 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_295 : CutRow g221 7 295 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_298 : CutRow g221 7 298 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_346 : CutRow g221 7 346 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_394 : CutRow g221 7 394 33 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_427 : CutRow g221 7 427 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x208000a,0x422905300a414030108,0x45410208000a04229042,0x108000a041288520108,0xa0412885200a41403,0x108454100a414030108,0x45410108020300908852,0x8250060701a51300825,0x60701a513003050403,0x110584200a410c16038,0x454100210060701a1130,0x1818209448a1c310108,0x2a141a88520108000a,0x412885201040029141a,0x48420208000a04229053,0xa41403010845410208,0xa0422905301040403,0x110484200280062301a,0x815000210060701a1130,0x108000a0412885200a0,0xc40221020d2000a0c281,0x60a20d2001818209448a,0x1c310104040301104831,0x1040403011048310104,0x29141a483101040029,0x141a4831010404030110,0x483101818209448a1c31,0x1040029141a48420104,0x4030110483102080022,0x10289042010802030090,0x88410088020b048a8451,0x1040029141a48310104,0x29141a483101040029,0x141a483101040029141a,0x48310108000a04128852,0x88020b048a84510020,0x828160a2092000210402,0x410211300020828160a2,0x9200021040241021130])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_475 : CutRow g221 7 475 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x210402,0x4102113000a0c4022102,0xd200081040241081431,0x1040029141a48420104,0x29141a484200a0c402,0x21020d20080800221088,0xc05401040029141a4842,0x810402410814310108,0x2a141a885201040029,0x141a484200a0c28160a2,0xd20008400c160384441,0x8400c1603844410104,0x29141a484200880203,0x88845100a0c28160a2,0xd2001040029141a4842,0x181840241081c310084,0x4030108444100a0c402,0x21020d20008104024108,0x14200081040241081420,0x810402410814200081,0x4024108142001040029,0x141a4842010404030110,0x483201040029141a4831,0x1040029141a48420104,0x29141a484201818209,0x448a1c3101818209448a,0x1c3101818209448a1c31,0x1818209448a1c310808,0xc260b0c05408080022,0x1088c05401818209448a,0x1c310208020b04a29053,0x208000a042290530104,0x29141a484208250060,0x701a513000a0c28160a2,0xd2001040029141a4842,0x1040029141a48420104,0x29141a484201818209,0x448a1c3101040029141a,0x484201040029141a4842])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_523 : CutRow g221 7 523 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x810209,0x448a1420010404030110,0x483100a0c40221020d20,0x208402210209200081,0x209448a142000810209,0x448a1431008400c16038,0x44410208020b04a29053,0x2080022102890530181,0x8209448a1c3100208402,0x21020920018184024108,0x1c3101818209448a1c31,0x1818209448a1c310081,0x209448a1431008400c1,0x60384441008400c16038,0x444100810209448a1431,0x208000a042290530020,0x84022102092000208402,0x210209200208000a0422,0x904201818209448a1c31,0x8800c2603884510020,0x84022102092000208402,0x21020920008800824028,0x84510300c20914a21c62,0x300c20914a21c6200a4,0x14030108454100810209,0x448a1431002084022102,0x9200020840221020920,0x810209448a14200081,0x40241081420008400c1,0x60384430008400c16038,0x4430008400c160384430,0x1818209448a1c200181,0x8209448a1c2000810209,0x448a1421008400c16038,0x4441008400c160384441,0x210402410211300081,0x209448a143100810209,0x448a1431008400c16038,0x44410825040241025130])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_571 : CutRow g221 7 571 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x8400c1,0x60384441008400c16038,0x4441008400c160384441,0x810209448a14310084,0xc160384441008400c1,0x60384441008400c16038,0x4441008400c160384441,0x8400c1603844410084,0xc160384441008400c1,0x60384441082504024102,0x513000810209448a1431,0x8400c1603844410084,0xc160384441008400c1,0x60384441082504024102,0x51300181840241081c31,0x280042201281500104,0x29141a484201040029,0x141a4842018184024108,0x1c3101040029141a4842,0x8400c1603844410081,0x209448a143103050403,0x1105842008104024108,0x1421080800221088c054,0x8400c1603844410081,0x209448a143100810209,0x448a1431008400c16038,0x44410208020b04a29053,0x810209448a14310081,0x209448a143101040029,0x141a484201040029141a,0x484200810209448a1431,0x810209448a14310081,0x209448a143100810209,0x448a143100810209448a,0x14310104040301104842,0x880203008884510825,0x60701a513001818402,0x41081c31008104024108,0x1420008400c160384430])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_619 : CutRow g221 7 619 14 := by
  apply polarBlock (data:=fun _ => (w80 [0x20,0x828160a2092000208281,0x60a209200020828160a2,0x92000210060701a1130,0x210060701a11300104,0x29141a484200810209,0x448a143101040029141a,0x484200810209448a1431,0x8400c1603844410081,0x209448a143100a0c402,0x21020d2000a0c4022102,0xd20008400c160384441])) rfl
  decide +kernel
theorem g221B7 : CutRow g221 7 0 633 := (@joinRow g221 7 0 298 335 (@joinRow g221 7 0 151 147 (@joinRow g221 7 0 55 96 (@joinRow g221 7 0 7 48 g221P7_0 g221P7_7) (@joinRow g221 7 55 48 48 g221P7_55 g221P7_103)) (@joinRow g221 7 151 96 51 (@joinRow g221 7 151 48 48 g221P7_151 g221P7_199) (@joinRow g221 7 247 48 3 g221P7_247 g221P7_295))) (@joinRow g221 7 298 177 158 (@joinRow g221 7 298 96 81 (@joinRow g221 7 298 48 48 g221P7_298 g221P7_346) (@joinRow g221 7 394 33 48 g221P7_394 g221P7_427)) (@joinRow g221 7 475 96 62 (@joinRow g221 7 475 48 48 g221P7_475 g221P7_523) (@joinRow g221 7 571 48 14 g221P7_571 g221P7_619))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221B8 : CutRow g221 8 0 130 := (@joinRow g221 8 0 61 69 (@joinRow g221 8 0 13 48 (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=3)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)) (@joinRow g221 8 61 48 21 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=3)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221B9 : CutRow g221 9 0 10 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221B10 : CutRow g221 10 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : mixedTables g221 10 := by
  intro k hk
  interval_cases k <;> first
  | exact g221B5
  | exact g221B6
  | exact g221B7
  | exact g221B8
  | exact g221B9
  | exact g221B10
  | exact mixedEmpty g221 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 11 := mixedLower (g:=g221) (i:=0) (hints:=33555459) (before_sound K207 V207) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K207 11 [(221,[]),(245,[98,67,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V207 low221 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[sampledPair 0xfe7fc01ff0ff1ffc75 0x77e00001f0000007c1f 0x5229148a242410905 0x77e94a5294a5294a529,sampledPair 0xffffffe000ffe3ff83 0xf5420003e0003e0f83e0 0x8030180c404081023 0xb5401084210842108421,(0,0),sampledPair 0x7fffffff0003fff2 0x1a4007c0007c1f003ff 0x100402010008002000 0x2108421084210842,(0,0),sampledPair 0x7ffffffffffc000c 0x16000f8000f801fffc00 0x200804020010004000 0x4210842108421084,sampledPair 0xff800000000000000d 0x6897f00000fffe000000 0x4030180c086091824c 0x48968421084210842108,sampledPair 0 0x8859ffffff0000000000 0x804020100080020000 0x10842108421084210,(0,0)]
def g235C : List ColumnInfo := [(1,0,234,0,10)]
def g235A : List (List Nat) := [[],[117],[83],[83,115],[115,83],[115],[97],[97,117],[97,83],[97,83,115],[97,115,83],[97,115]]
def g235D10 (j : Nat) := if j=0 then 0x7f else 0
def g235L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g235D10)
  | _ => emptyPacking
def g235I (_ _ : Nat) : Option (Nat × Nat) := none
def g235 : Forest := ⟨235,10,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235B10 : CutRow g235 10 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : mixedTables g235 10 := by
  intro k hk
  interval_cases k <;> first
  | exact g235B10
  | exact mixedEmpty g235 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 11 := mixedLower (g:=g235) (i:=0) (hints:=16777267) (before_sound K221 V221) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K221 11 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V221 low235 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0,0),sampledPair 0xf87ffe01ff8fffffe4 0x13c7300000f8000f83ff 0x110014140520200420 0x11c13084210842108421,sampledPair 0xff87fffe000ff1fe09 0x4badd0001f0001f00000 0xa01158185641444889 0x4badd39ce739ce739ce7,sampledPair 0x7fffffff001ffc7 0xaa986003e0003e007c1f 0xc22060201801881007 0x82184108421084210842,(0,0),sampledPair 0x7fffffffffe0012 0x6c4f807c0007c0007fe0 0x44180406002006110 0x6c068210842108421084,sampledPair 0xfff800000000000029 0x84009f800007ffff8000 0x200808004008000 0x421084210842108,sampledPair 0x10 0x51304ffffff800000000 0x401010008010000 0x842108421084210,(0,0)]
def g238C : List ColumnInfo := [(4,0,234,0,10)]
def g238A : List (List Nat) := [[],[118],[83],[83,118],[49],[49,118],[49,81],[49,81,118],[81,49],[81,49,118],[81],[81,118]]
def g238D10 (j : Nat) := if j=0 then 0x7f else 0
def g238L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g238D10)
  | _ => emptyPacking
def g238I (_ _ : Nat) : Option (Nat × Nat) := none
def g238 : Forest := ⟨238,10,fun i => g238Y[i]?.getD (0,0),g238C,g238A,g238L,g238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238B10 : CutRow g238 10 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238T : mixedTables g238 10 := by
  intro k hk
  interval_cases k <;> first
  | exact g238B10
  | exact mixedEmpty g238 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238G : graphValid g238 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low238 : Lower true (varsX 238) (graphGoal 238) 11 := mixedLower (g:=g238) (i:=0) (hints:=286266928) (before_sound K235 V235) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K235 11 [(238,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V235 low238 (by decide +kernel)
def g250Y : Array (Bits × Bits) := #[(0,0),sampledPair 0xfffc01ffffe1ffffba 0xc261b0000007c00f83ff 0x482402024400209a 0x42011004210842108421,(0,0),sampledPair 0x1ffffe00fffe1fff25 0x3c4b188000f801f07c1f 0x409008140480404021 0x1c420808421084210842,sampledPair 0x1fffffff00001ff058 0xf5694e001f0000000000 0x8ae1309857088a8258 0xf5694e3def7bdef7bdef,sampledPair 0x1fffffffffffe00010 0xaa846f83e0003e007fe0 0x30040201800030400 0xa0046390842108421084,sampledPair 0xe0000000000000000e 0x11ba877c00003fff8000 0xc0180c060110c0804 0x1b88421084210842108,sampledPair 0xc1 0x4514407fffffc0000000 0x100201008000100000 0x42108421084210,(0,0)]
def g250C : List ColumnInfo := [(16,0,234,0,10)]
def g250A : List (List Nat) := [[],[101],[83],[83,99],[99,83],[99],[49],[49,101],[49,81],[49,81,97],[49,97,81],[49,97],[81,49],[81,49,99],[81],[81,97],[81,99],[81,99,49],[97,49,83],[97,49],[97,81],[97],[97,83,49],[97,83]]
def g250D10 (j : Nat) := if j=0 then 0x7f else 0
def g250L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g250D10)
  | _ => emptyPacking
def g250I (_ _ : Nat) : Option (Nat × Nat) := none
def g250 : Forest := ⟨250,10,fun i => g250Y[i]?.getD (0,0),g250C,g250A,g250L,g250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250B10 : CutRow g250 10 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=6) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250T : mixedTables g250 10 := by
  intro k hk
  interval_cases k <;> first
  | exact g250B10
  | exact mixedEmpty g250 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g250G : graphValid g250 (boundsBefore K238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low250 : Lower true (varsX 250) (graphGoal 250) 11 := mixedLower (g:=g250) (i:=0) (hints:=286724144) (before_sound K238 V238) g250G g250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K250 := extendKnown K238 11 [(250,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V250 : Known true K250 := extend_ok (m:=250) V238 low250 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[sampledPair 0xdb5234b66000000000 0xff00ff00ff300801c 0x9b5034a06414141414 0x14141414141411000008,sampledPair 0x8f6559482000000ff0 0xff000000ff0002105fb 0x8b6019482050505050 0x505050505050500005fa,sampledPair 0x1b10894360000ff000 0xff0000000587a05 0x1b1089436131313131 0x31313131313130082a05,sampledPair 0x226e4444800ff0000f 0xf00000000ffff8866347 0xe400480a0a0a0a0 0xa0a0a0a0a0a0a0026205,sampledPair 0x75af08991000000000 0xffff00003187018 0x64af00181acacacaca 0xcacacacacacac2105010,sampledPair 0x4899322a1ff000000f 0xfffff00000000c1f8c60 0x408102020303030303 0x30303030303001d8800,sampledPair 0xa4808320fffffffff0 0xfe00f80 0x240000201c0c0c0c0c 0xc0c0c0c0c0c07e00000,(0,0),(0,0)]
def g127C : List ColumnInfo := [(1,0,126,0,10),(2,0,125,0,10),(4,0,123,0,10),(0,16,106,5,9),(8,0,119,0,9),(16,0,111,0,9),(32,0,95,0,9),(64,0,63,0,8),(0,4,43,80,7),(66,0,61,0,7),(40,0,87,0,5),(72,0,55,0,5),(96,0,31,0,5),(41,0,86,0,4)]
def g127A : List (List Nat) := [[],[83]]
def g127D6 := limbs80 #[#[0x7654f8f3a15d9801d953,0x61761d953c3dea576604,0x31830f7a1e]]
def g127D7 := limbs80 #[#[0x1d9536007654d761d953,0x54d6558d531d96354d81,0xe057654f765d953e1563,0x5956361e7654f835d953,0x6d6d63ec3fe057558f83,0xbd75ee7dc7f8fb1edb7b,0x4cd903f2fdd7abf3de6f,0xe464398055d899761264,0xce4412983fdd97f7641,0x836ce05a3767ae4ddf98,0x23967ce59fb937ee0def,0x5aeb93bfdd6a3919de16,0x645c54493d2d1d0e009e,0xb4aca49c948c847c746c,0xdf1f00bf3dcd4ccc4bc,0xac80a60144050c19f2,0x6024067]]
def g127H7 (j : Nat) := if j=0 then 0x4010200 else 0
def g127D8 := limbs80 #[#[0x9d9535d95358d531d953,0x9fe7dd95635d56359563,0xddf3fbfefebf6fbbdebf,0xff7f7f5fbfedf97dff7d,0xb17f0a5eb29070298b29,0x8c102b020cc006eec5a3,0xc87c1a2f028343842ec0,0x6ecc6c1b4f0695c0a46e,0xd150f9bc1c1f0702c3b4,0xc1a8f02a1bb1170d4bc0,0x61c1d8f034ec3b5eeca1,0x6c420ac17000fc35770d,0xf91f410ec32cae244741,0xf5e8721b7671865c9594,0x8a9aa4a8aa0a5f8f61d7,0xe4e7c7970b0abaacaaaa,0x4189a224635858acc5fa,0x8e0ebb230646b3261698,0x9008744073f20109f387,0xbe7010fcf0075ef8039f,0x209bf210139fc0089db,0x287fd600efb640c7fff,0x3de6009a9b6013dfd82,0xb0063da804e7e0123a2,0xff1c009d3e00f7bc3005,0x28bfc3080a2ffb0009c,0x5ff0c0]]
def g127H8 := limbs80 #[#[0x9401c3560101a592300,0x822b5d1613188a0,0x10e2de000a801af1e0,0xc09055fa122000001900,0x600400d269a9]]
def g127D9 := limbs80 #[#[0x9633fff7dfdff6358d53,0x758dd5765559537605d8,0x57595f7639d8d7631d81,0x82c91c6a250a803dd5d7,0xc7080b9d9cb852a48f46,0xd51842ca1d7996935cf2,0x10800e800ee60089cc4,0x6b002d8008000ec00430,0x60029ac0094801290024,0xb4012fbc004bd]]
def g127H9 := limbs80 #[#[0x4001a45454084000a000,0xc641d13c880188000001,0xcda7d2909c60033c8487,0x60400000b8000103,0x150e00001d0ec000a6,0x4a9e164800117984ef31,0x2e1cb5866a42a100006c,0x6800002e]]
def g127D10 := limbs80 #[#[0x45c5c03ff63ff58ffd53,0xd5992518107accc49460,0x6acc928c0e41e]]
def g127H10 := limbs80 #[#[0x26ba8a510010000262a,0x6e000a8380cb0f080014,0xb1]]
def g127D11 (j : Nat) := if j=0 then 0xc8a64203ff else 0
def g127H11 (j : Nat) := if j=0 then 0x58000a970000 else 0
def g127L : Nat → Packing
  | 6 => (3,5,4,0,0,4,0,g127D6)
  | 7 => (24,4,4,1048588,68,8,1032,g127D7)
  | 8 => (33,3,4,1179655,83,10,1055,g127D8)
  | 9 => (14,2,4,262147,34,9,1042,g127D9)
  | 10 => (3,1,4,0,0,7,0,g127D10)
  | 11 => (1,0,4,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 11 0 4 2 0 g127H7
  | 8 => lookupShort 7 47 3 8 5 1 g127H8
  | 9 => lookupShort 10 59 6 9 6 1 g127H9
  | 10 => lookupShort 4 23 2 7 4 1 g127H10
  | 11 => lookupShort 1 11 0 5 2 1 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127B6 : CutRow g127 6 0 3 := (by
      apply polarBlock (data:=fun _ => (w80 [0x210060,0x701a113000210060701a,0x113000810209448a1420])) rfl
      decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127B7 : CutRow g127 7 0 24 := (@joinRow g127 7 0 6 18 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x210120,0xd04a113000210060701a,0x112000210120d04a1130,0x210060701a11300021,0x120d04a113000210060,0x701a113000210060701a,0x113000210060701a1120,0x210060701a11200021,0x60701a113000210060,0x701a113000210060701a,0x113000210060701a1120,0x210060701a11400021,0x60701a113000210120,0xd04a113000210120d04a,0x113000210060701a1130])) rfl
      decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127B8 : CutRow g127 8 0 33 := (@joinRow g127 8 0 2 31 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g127 8 2 22 9 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x21,0x120d04a114000210120,0xd04a114000210060701a,0x113000210120d04a1130,0x210060701a11400021,0x60701a114000210060,0x701a113000210060701a,0x113000210120d04a1130])) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127B9 : CutRow g127 9 0 14 := (@joinRow g127 9 0 7 7 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=9) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127B10 : CutRow g127 10 0 3 := (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127B11 : CutRow g127 11 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : mixedTables g127 11 := by
  intro k hk
  interval_cases k <;> first
  | exact g127B6
  | exact g127B7
  | exact g127B8
  | exact g127B9
  | exact g127B10
  | exact g127B11
  | exact mixedEmpty g127 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := mixedLower (g:=g127) (i:=0) (hints:=16778291) (before_sound K250 V250) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K250 12 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V250 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[sampledPair 0x2af90d90ae18042800 0xfe0007f01fc07f 0x227801902608042810 0x20408102040810204081,sampledPair 0x351561bb02231a3800 0x7f0003f800003f80 0x351121ba02011a2850 0xa142850a142850a14285,sampledPair 0xc3ba79c203c0dd1000 0x3f800000000fe00000 0x83ba49c202c0dd1132 0x64c993264c993264c993,sampledPair 0xc406c8995858acc000 0x1fc00001fc0000003fff 0xc006c8011810a080a1 0x42850a142850a142850a,sampledPair 0x5215362ae9a4a1880f 0xe000000000000fffc000 0x50053628c9242082c5 0x8b162c58b162c58b162c,sampledPair 0x9ca1724506341f7f0 0x1fffff0000000 0x88016044062415306 0xc183060c183060c1830,(0,0),sampledPair 0xb020824406047207ff 0xfffffffe000000000000 0x408 0x10204081020408102040,(0,0)]
def g191C : List ColumnInfo := [(1,0,190,0,11)]
def g191A : List (List Nat) := [[],[83]]
def g191D11 (j : Nat) := if j=0 then 0xff else 0
def g191L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g191D11)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,11,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191B11 : CutRow g191 11 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : mixedTables g191 11 := by
  intro k hk
  interval_cases k <;> first
  | exact g191B11
  | exact mixedEmpty g191 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 12 := mixedLower (g:=g191) (i:=0) (hints:=1075) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 12 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[sampledPair 0x23b30db0ae1b440800 0xfe0000001fc07f 0x23b20590260b440912 0x24489122448912244891,sampledPair 0x3c55619b02231b1800 0x7f000007f0003f80 0x3451219a02211a1850 0xa142850a142850a14285,sampledPair 0xc3b879c203c09c3000 0x3f800003f80fe00000 0x82b049c202c09c3030 0x60c183060c183060c183,sampledPair 0xc406c8995858acc000 0x1fc00001fc0000003fff 0xc004c8011850a080a1 0x42850a142850a142850a,sampledPair 0x5215362ae9a4a1880f 0xe000000000000fffc000 0x50053228c9242182c5 0x8b162c58b162c58b162c,(0,0),sampledPair 0x9ca1724506341f7f0 0x1fffff0000000 0x90a16244002414306 0xc183060c183060c1830,sampledPair 0xb020824406047207ff 0xfffffffe000000000000 0x408 0x10204081020408102040,(0,0)]
def g223C : List ColumnInfo := [(2,0,221,0,11)]
def g223A : List (List Nat) := [[],[32,99]]
def g223D11 (j : Nat) := if j=0 then 0xff else 0
def g223L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g223D11)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,11,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223B11 : CutRow g223 11 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : mixedTables g223 11 := by
  intro k hk
  interval_cases k <;> first
  | exact g223B11
  | exact mixedEmpty g223 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := mixedLower (g:=g223) (i:=0) (hints:=16778291) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[]),(247,[83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[sampledPair 0xfc03fed580945955ca 0xa0000003e00000007c1f 0x485852c580145855c2 0xa25294a5294a5294a529,sampledPair 0xfffc01eb1610463481 0xd000007c00003e0f83e0 0x909099e90010043481 0xd0421084210842108421,sampledPair 0x9dee9b8ce003 0x88000f800007c0000000 0xe0e0e099ee9b8ce003 0x81ce739ce739ce739ce7,sampledPair 0xfffffc2064f72202eb 0x1f00000f801f003ff 0x64e1020208 0x842108421084210842,(0,0),sampledPair 0x115b023d8614 0x303e00001f0001fffc00 0x10100101a02218014 0x1084210842108421084,sampledPair 0x34ea124c08824 0xafc000001ffffe000000 0x20202060104400820 0x2a108421084210842108,sampledPair 0x2800849007910 0x47ffffffe00000000000 0 0x4210842108421084210,(0,0)]
def g239C : List ColumnInfo := [(1,0,238,0,11)]
def g239A : List (List Nat) := [[],[83]]
def g239D11 (j : Nat) := if j=0 then 0xff else 0
def g239L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g239D11)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,11,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239B11 : CutRow g239 11 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : mixedTables g239 11 := by
  intro k hk
  interval_cases k <;> first
  | exact g239B11
  | exact mixedEmpty g239 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := mixedLower (g:=g239) (i:=0) (hints:=16778803) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 12 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[sampledPair 0x6764100472c4000000 0x3f800000000fffc07f 0x2240100470c4448912 0x24489122448912244891,sampledPair 0x81081ecda070000000 0x1fc00001fc07f0003f80 0x100040da0700c1830 0x60c183060c183060c183,(0,0),sampledPair 0x3087a5c03a0200000f 0xe00000fe03f800003fff 0x100621c00a00102040 0x81020408102040810204,sampledPair 0x512dcc7a88e80007f0 0x1fc000 0x512dcc7a8828b972e5 0xcb972e5cb972e5cb972e,sampledPair 0x5cd0cb21810c03f800 0x7f0003ffffe00000 0x4c90ca000008204081 0x2040810204081020408,sampledPair 0xaa4930220d2bfc0000 0x7ffffc0000000000 0xa24910220502c18306 0xc183060c183060c1830,sampledPair 0x212401e4411ffffff 0xffff8000000000000000 0x1020408 0x10204081020408102040,(0,0)]
def g251C : List ColumnInfo := [(1,0,250,0,11)]
def g251A : List (List Nat) := [[],[83],[97],[97,83]]
def g251D11 (j : Nat) := if j=0 then 0xff else 0
def g251L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I (_ _ : Nat) : Option (Nat × Nat) := none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251B11 : CutRow g251 11 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : mixedTables g251 11 := by
  intro k hk
  interval_cases k <;> first
  | exact g251B11
  | exact mixedEmpty g251 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := mixedLower (g:=g251) (i:=0) (hints:=16777267) (before_sound K239 V239) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K239 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V239 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[sampledPair 0x9b01000000001fc000 0x3fc03fffd056c3cc 0xb0142850a14284848 0x4848484848485042c10c,(0,0),sampledPair 0xe08c0000000fe00000 0x3fc0003fc0000060fc8c 0xa088162c58b162c2c2 0xc2c2c2c2c2c2c040548c,sampledPair 0x6220000007f000003f 0xc03fc000003fc18900d7 0x60200c183060c18181 0x818181818181808900c1,sampledPair 0x70760003f800000000 0x3fffc0220e0f30 0x5076a952a54a951515 0x151515151515200c0a30,sampledPair 0x956b01fc0000003fc0 0x3fffc000000400002b 0x904a3060c183060606 0x6060606060600000002,sampledPair 0x506fe000000003fff 0xffc000000000380ff030 0x504c183060c181818 0x1818181818183006a030,sampledPair 0x8d8ffffffffffc000 0x3ff00000 0x2020 0x2020202020200f300000,(0,0)]
def g253C : List ColumnInfo := [(8,0,245,0,11),(32,0,221,0,11),(1,0,252,0,10),(4,0,249,0,10),(16,0,237,0,10),(64,0,189,0,10),(128,0,125,0,10),(5,0,248,0,8),(65,0,188,0,8),(68,0,185,0,8),(80,0,173,0,8),(0,4,41,208,7),(0,16,104,133,7),(21,0,232,0,7),(84,0,169,0,7),(129,0,124,0,7),(132,0,121,0,7),(144,0,109,0,7),(192,0,61,0,7),(1,16,104,132,6),(16,4,41,192,6),(64,4,41,144,6),(128,4,41,80,6),(128,16,104,5,6),(69,0,184,0,5),(81,0,172,0,5),(129,16,104,4,5),(145,0,108,0,5),(192,4,41,16,5),(196,0,57,0,5),(133,16,104,0,4)]
def g253A : List (List Nat) := [[],[83],[96,66],[96,66,83]]
def g253D8 := limbs80 #[#[0x59510595614416154110,0x541815815058d604c187,0x60375587835c56060576,0x1edbce71dcef7dabbc77,0x99856393e39351753565,0x72482200d75c793ab93,0xc248886f87c14304d0a,0x358b4dc245a342188d2f,0x3c963dc96309c1e1e0fe,0x4700344da48f35323465,0xff0031f9c063ce031fc0,0xff02800bf605007d8133,0x7]]
def g253D9 := limbs80 #[#[0x59510585105811054110,0x59530581305d9105d510,0x5855058150585315d930,0x5cd605c56058d605d950,0xdd560dcd60dc5605d560,0x9fe77dd561dc1615c161,0xdf777d7effbfafdbdedf,0xf7bbfefbbdedbb5dff7e,0x1a5ab1981c197ffffbfc,0x3014bb022b2824b0818b,0xa89cb288bc2854ba84ac,0x3102c38ceba8c9c08d2b,0xa83c2a03c2951c1943c,0x1b83c0b05c2adeb1a8bc,0x1cc2c0cc2c2c82c2c47c,0x2842c0582c2d47c1d02c,0x1aa6c0a96c39e6c29a6c,0xab56bab97c0b16c0b26c,0xc28c0c0dc0c16babe0b,0x613e1fc300430440029c,0xba4fc969122083b4668b,0x82cf49d637a690c296f2,0x168abc5249f534249454,0x93996fcd599f327620bc,0x8f90f1ba22c207faf65d,0x352c4058e2686c6f070c,0xb728d328a8433630607d,0x9024383088a610f0da40,0x2980992a49928072661a,0x78e8c0c8b884831d1e2a,0x3c04f619eb8144889524,0x1b7ae40232cfa0116cf7],#[0x4677b00d5d809b789801,0x4c04cc025dc0251cee80,0x18ac061f3c0114ac063e,0x67edc0304fbf0267ae0,0x11773cc80476e80af5f8,0xf8dc0455fea008a37f80,0x99f0c60527f8057dc02c,0xf0022efb5c045376035f,0x6f804aef6018dc812cf3,0x253fd404c37c7820090,0xfa1004603f1e2008f7f6,0x5fe1700236fd4f80465f,0xfd204b3fa24e0048]]
def g253H9 := limbs80 #[#[0x14067000000001c0000,0x63238000000000000,0x414c00000840000000,0x44000]]
def g253D10 := limbs80 #[#[0xf7f7f58560541314c110,0xac222c022a03fffefefd,0x2ec52c662c042ec02ea1,0x6e70ac706e302ece2c0c,0xac746e142ec9ac286eb0,0xac2eaca6aca06eb46e74,0xae76ae16aeb2ae72ae32,0x6914c3608412002aeb6,0x11d418e8344bd2ac911e,0x9d26d59b6296c559454d,0x61a3277986468ae0b7a,0x8b253440e23953101e37,0x20c4c496cc68d8c4a14a,0x390067e010e9e6120e0,0x88033f0010179c0277c4,0xa03ba00c7f8804bfd601,0xff0053f84009dff8028e,0xf8025340332018cf012b,0x36fa008ae8053f86009e,0x1fdc802873dc06be8781,0x1f4073fe60117ff0004e,0xfe1a409dcd00eff0033f,0x1]]
def g253H10 := limbs80 #[#[0xc54403b83858c0020002,0x3a4ca10d0028b22400,0x101f21b0800393c7000,0x205000008840083e17,0x1870000086c008488a,0xc611900384655a349800,0x23000c9d2a0000000116,0x31449301030008a620,0x80b09c7400c40000001e,0x2e0e42b070011101a23,0x6b8d04d00000a088a25,0x40c00]]
def g253D11 := limbs80 #[#[0x31ff583fd50ff4c3fd10,0x5c6a272482400ff587fd,0x2069a58603459a582134,0x4f0a51a084d1e498d821,0xce1a180d1c680e84d1,0x1]]
def g253H11 := limbs80 #[#[0x38110007098001,0x1920000000000040000,0x100000000,0x5f8c000045a1c98000,0x2a82c00000,0x8000,0x40000a381000000021c0,0x339940026926000046,0x30300244018fe7,0x9ab000000000054001b,0xa88a4643401484280087,0x1960083001]]
def g253D12 (j : Nat) := if j=0 then 0x3148310023ff else 0
def g253H12 := limbs80 #[#[0x62018f013a0972210001,0x7522000]]
def g253L : Nat → Packing
  | 8 => (8,4,5,458760,51,8,1054,g253D8)
  | 9 => (43,3,5,1376279,85,11,1077,g253D9)
  | 10 => (29,2,5,393222,51,10,1054,g253D10)
  | 11 => (6,1,5,0,0,8,0,g253D11)
  | 12 => (1,0,5,0,0,0,0,g253D12)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupShort 2 37 0 7 3 2 g253H9
  | 10 => lookupShort 14 83 5 10 6 2 g253H10
  | 11 => lookupShort 9 101 3 9 5 2 g253H11
  | 12 => lookupShort 2 17 1 7 3 2 g253H12
  | _ => fun _ => none
def g253 : Forest := ⟨253,12,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253B8 : CutRow g253 8 0 8 := (@joinRow g253 8 0 4 4 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253B9 : CutRow g253 9 0 43 := (@joinRow g253 9 0 30 13 (@joinRow g253 9 0 3 27 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)) (@joinRow g253 9 30 11 2 (by
      apply checkedRow
      apply cellsBlock (ar:=9) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x1020028941a,0x28420102020180902842])) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253B10 : CutRow g253 10 0 29 := (@joinRow g253 10 0 20 9 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=9) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253B11 : CutRow g253 11 0 6 := (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253B12 : CutRow g253 12 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : mixedTables g253 12 := by
  intro k hk
  interval_cases k <;> first
  | exact g253B8
  | exact g253B9
  | exact g253B10
  | exact g253B11
  | exact g253B12
  | exact mixedEmpty g253 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 13 := mixedLower (g:=g253) (i:=0) (hints:=33555459) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 13 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0,0),sampledPair 0x4c2000000001fc0000 0x3fc03fc03fc03049ccf 0x4c00a142850a141414 0x141414141414010008c5,sampledPair 0xbe00000000fe000003 0xfc000003fc000c0b03f0 0x2e0264c993264c4c4c 0x4c4c4c4c4c4c04090150,sampledPair 0x200000007f000003fc 0x3fc0003fc3030e30e 0x200142850a14282828 0x28282828282810102308,sampledPair 0xc170003f8000000000 0x3fc00400303f1 0xc17d9b366cd9b1b1b1 0xb1b1b1b1b1b0000202a1,sampledPair 0x46101fc0000003fc00 0x3fffc000180c3fc00 0x2160c183060c0c0c0 0xc0c0c0c0c0c080435000,sampledPair 0xb1bfe000000003ffff 0xfffc0000000200fc0001 0x91a810204081010101 0x1010101010000a40000,sampledPair 0xbcffffffffffc0000 0x3ff000000 0x20202 0x202020202036a000000,(0,0)]
def g254C : List ColumnInfo := [(4,0,250,0,11),(16,0,238,0,11),(64,0,190,0,11),(2,0,252,0,10),(8,0,246,0,10),(32,0,222,0,10),(128,0,126,0,10),(10,0,244,0,7),(34,0,220,0,7),(40,0,214,0,7),(130,0,124,0,7),(136,0,118,0,7),(160,0,94,0,7),(42,0,212,0,5),(138,0,116,0,4),(162,0,92,0,4),(168,0,86,0,4)]
def g254A : List (List Nat) := [[],[83],[49],[49,81],[81,49],[81]]
def g254D7 := limbs80 #[#[0x40483ea9a75916250120,0x496458120faa61994589,0xa5d18260164483ea9746,0x483ae9766098059120ee,0x8759120f2e601765d164,0x91e612306039eb92e41]]
def g254D8 := limbs80 #[#[0x50120589404814250120,0x48164581205896048176,0x5d964481745912061160,0x5912061d644818059120,0x481765d120e1d6448287,0x5d162581845d92061974,0x57baddd7eadf4fe7f47f,0xab9d72fdfdbeb5d67ebf,0xdf7baf5deabbf76feddd,0x82edd81cbb07fafddfab,0x86ddd0daba1a586192c,0x728546186cca0d97604f,0xa32494610e8ba1bf9423,0x762ecca60a0fc92cd744,0x4a472121e4247ca4b394,0x94c0b216066284cb50d9,0x5974c33025e4bc9c870f,0xaf9098729355da2eba45,0x1601f01f0011e43a3c86,0x89610b1d43305b0950e4,0xc20d3d671cd19892ce53,0x1c5f4b81602a050c9911,0x7b6f4de5ba6702d8da0b,0xc1e1f14037f6fcdf5be3,0xb0124be242b07a503a23,0x1e990f4483a294ae5050,0x90422e116506499cd25e,0x289a183586a662598164,0xda809862901c1007c2e1,0x93d6c026efdc0139f7,0xff2f004f779e000a5e79,0xbe6c024bb380282fe018],#[0x18ff3d00277e76f804bf,0xb8fe011779e00142fde0,0x13999c26014df384a014,0x2c2991df8805961efe0,0x987f2200463b0c33d8,0x69fc800469d780046bbb,0x7800471f720011eeec02,0xf87f0022cf390008e07d,0xdd4f8011c7cc1c008]]
def g254H8 := limbs80 #[#[0x722e818c046000715509,0x1]]
def g254D9 := limbs80 #[#[0x5d120591205812050120,0x58960dd920dd1205d920,0xcfeffbfa7fdc9605c960,0xfebeffabbfefbbadff7e,0x82d620658865420ffffe,0xdd05174175905376045d,0x50e18c187235d8878414,0x8493dd1c18460e110186,0xb1802c61071741c5d801,0x1c89872561ca1762a5d0,0x2e111586355d8cb8725a,0x4855d2217475e1115844,0x8c00d61235844d61c8b8,0xc8e3340ba270841a4470,0x718359d545052f4790b3,0x1e7293233859fc779be6,0xab44cb70abcedcade9ea,0x70ae1e0e2ee7b1ea792d,0xb082c0ea6a50dc3c4650,0x4838b8709a44b0f47660,0x94c0c4a10e5e6488a884,0x404987de0014d09cf802,0x85de8076fb4012fd9ef,0x4003bc0076a2025fef90,0xef402be0101c042f4c02,0x801297f0013be8056300,0x28fcd600a1fb75e00abf,0x3f29e024cfb009773e40,0x9e020fce01402a52b805,0x3486014bbde01ade0128,0xfd86029ba8041ec0253f,0xb0ccd7e002a6f8010ef],#[0xdf201eccabb80]]
def g254H9 := limbs80 #[#[0x58e0004d33a8010,0x800d49878000a3000000,0x207001c7241,0x2c030000250000032000,0xa9931042868b8,0x52ea8d00180c00000000,0x296982a080021b001a9,0x22001046000000000000,0x408a840020fc3a000004,0x4006c389285c0060b,0x98060000000000000,0x6db0000380a800c240,0x2c8001068,0x50008800000088981400,0xa3a2d800c860000069,0x870080000000000061f0,0x3390c00090d,0x190000000000000000,0x938000000000000000,0x4c0000000000,0xa6a23800000c910a000,0,0,0x22151082147800001024,0x60000000000000000000,0x14000000000462800071,0x80800000001b4506e24d]]
def g254D10 := limbs80 #[#[0x581280ffffb7f7f58120,0x372ab14dd82ec3740ba2,0x89c2a00d72ebb35d1ac8,0x823a9a4b44da14d8591f,0xc2f2a64b1218a0f87062,0x2064758187051235208c,0xfa004c4e201650041cc0,0xcce4043fbc01840051,0xa27500a1ff8402dbfd,0x7678025f8c]]
def g254H10 := limbs80 #[#[0x41403d405f5010052c0,0x262284a002500009400,0x651d840690fa0a001850,0xc00121a44904a1000,0x3001d8300000020e0800,0x8096ba0b88502043820c,0x400000c3c00030000c90,0x8682c0000680004706,0x327008000000000,0x5258380000c400000000,0x60309f21400212,0x628005238850980000,0x12000c8a0010e4150920,0xa0f000000006d4022000,0x980a8740048f00000229,0x30d80082eb0e4a00]]
def g254D11 := limbs80 #[#[0x3860888d80ff583fd20,0x2a59060e08a12079a51]]
def g254H11 := limbs80 #[#[0x4db111600000000f2011,0x410000060000d,0xad721830400f8000,0xb45c9c8e047c2000]]
def g254D12 (j : Nat) := if j=0 then 0x3148310403ff else 0
def g254H12 := limbs80 #[#[0xd40002000c00,0x2400000000000260000,0x4]]
def g254L : Nat → Packing
  | 7 => (7,5,5,0,0,6,0,g254D7)
  | 8 => (38,4,5,1638416,84,11,1069,g254D8)
  | 9 => (38,3,5,917514,68,10,1058,g254D9)
  | 10 => (12,2,5,262146,33,9,1046,g254D10)
  | 11 => (2,1,5,0,0,6,0,g254D11)
  | 12 => (1,0,5,0,0,0,0,g254D12)
  | _ => emptyPacking
def g254I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupShort 2 11 4 7 3 2 g254H8
  | 9 => lookupShort 19 193 2 11 6 3 g254H9
  | 10 => lookupShort 16 107 6 11 6 3 g254H10
  | 11 => lookupShort 5 37 4 8 4 2 g254H11
  | 12 => lookupShort 1 31 0 6 1 3 g254H12
  | _ => fun _ => none
def g254 : Forest := ⟨254,12,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254B7 : CutRow g254 7 0 7 := (by
      apply polarBlock (data:=fun _ => (w80 [0x8104024108,0x14100081040241081420,0x810402410814100081,0x4024108141000810402,0x41081410008104024108,0x14100081040241081410])) rfl
      decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254B8 : CutRow g254 8 0 38 := (@joinRow g254 8 0 7 31 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g254 8 7 23 8 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x810402,0x41081420008104024108,0x14200081040241081420,0x810402410814310081,0x4024108142000810402,0x41081420008104024108,0x14200081040241081410])) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254B9 : CutRow g254 9 0 38 := (@joinRow g254 9 0 17 21 (@joinRow g254 9 0 2 15 (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)) (@joinRow g254 9 17 18 3 (by
      apply checkedRow
      apply cellsBlock (ar:=9) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x810402,0x41081431008104024108,0x14310081040241081431])) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254B10 : CutRow g254 10 0 12 := (@joinRow g254 10 0 8 4 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=9) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254B11 : CutRow g254 11 0 2 := (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254B12 : CutRow g254 12 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=7) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : mixedTables g254 12 := by
  intro k hk
  interval_cases k <;> first
  | exact g254B7
  | exact g254B8
  | exact g254B9
  | exact g254B10
  | exact g254B11
  | exact g254B12
  | exact mixedEmpty g254 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 13 := mixedLower (g:=g254) (i:=0) (hints:=286397488) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 13 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[sampledPair 0x3fe00ff80 0x3fe00080300008580001 0x482412090482412090 0x48200000100000080000,sampledPair 0x1ff007fc0000007f 0xc0000100c08631b7fffe 0x40a05028140a050281 0x40a00000400200b1fffe,sampledPair 0x3fe000000001ff0000 0x8a180d19f6260237 0xc26130984c26130984 0xc26088180c09e2040227,sampledPair 0xc0000ff8000000007f 0xfff02c030e61c7c658cb 0x8140a05028140a0502 0x81402801082087440001,sampledPair 0x1ffff80 0x93063f07e07f8ad48 0x158ac562b158ac562b 0x15892063e07605f0ad48,sampledPair 0xffffffe000000 0x11c07c007ff801318c 0x6030180c06030180c 0x6018030005d28000000,sampledPair 0xfffff0000000000000 0x1e007fff800001c1f0 0x180c06030180c06030 0x180a0046b38000000000,sampledPair 0 0x1fff8000000001fe00 0x201008040201008040 0x20045780000000000000,(0,0)]
def g255C : List ColumnInfo := [(1,0,254,0,13),(2,0,253,0,13),(4,0,251,0,12),(8,0,247,0,12),(16,0,239,0,12),(32,0,223,0,12),(64,0,191,0,12),(128,0,127,0,12),(20,0,235,0,11),(34,0,221,0,11),(65,0,190,0,11),(0,16,106,133,10),(6,0,249,0,10),(12,0,243,0,10),(18,0,237,0,10),(36,0,219,0,10),(40,0,215,0,10),(68,0,187,0,10),(72,0,183,0,10),(96,0,159,0,10),(132,0,123,0,10),(24,0,231,0,9),(48,0,207,0,9),(80,0,175,0,9),(128,16,106,5,9),(136,0,119,0,9),(144,0,111,0,9),(160,0,95,0,9),(0,4,43,208,8),(44,0,211,0,8),(129,16,106,4,8),(132,16,106,1,8),(192,0,63,0,8),(8,16,98,133,7),(32,16,74,133,7),(64,4,43,144,7),(64,16,42,133,7),(76,0,179,0,7),(100,0,155,0,7),(128,4,43,80,7),(140,0,115,0,7),(164,0,91,0,7),(196,0,59,0,7),(56,0,199,0,6),(88,0,167,0,6),(104,0,151,0,6),(112,0,143,0,6),(136,16,98,5,6),(152,0,103,0,6),(160,16,74,5,6),(176,0,79,0,6),(192,4,43,16,6),(192,16,42,5,6),(108,0,147,0,5),(168,0,87,0,5),(194,4,41,16,5),(200,0,55,0,5),(208,4,43,0,5),(224,0,31,0,5),(204,0,51,0,4),(228,0,27,0,4),(0,549,224,15,8),(0,550,236,0,8),(0,551,224,7,7),(0,552,224,7,7),(0,553,211,0,8),(0,554,224,7,7),(0,555,233,2,9),(0,556,224,7,7),(0,557,224,7,7),(0,559,224,7,7),(0,561,224,7,7),(0,562,211,0,8),(0,563,224,3,6),(0,564,234,5,12),(0,566,224,3,6),(0,567,224,3,6),(0,568,224,3,6),(0,570,224,7,7),(0,572,232,3,9),(0,573,232,3,9),(0,574,224,3,6),(0,575,224,3,6),(0,576,232,3,9),(0,579,232,1,8),(0,580,238,0,11),(0,581,236,0,8)]
def g255A : List (List Nat) := [[],[83]]
set_option maxRecDepth 32000 in
def g255D8 := limbs80 #[#[0x595634c9975d56558d32,0x4c9b25d975595326c975,0x5d5655cd326597559573,0x5cd325d995595734c9b2,0xec5a9595734c99665565,0x6557350fb16a5655cd43,0x54fb7695965cd43edda6,0x65d6558d536d18759563,0x58d536d1765d56354db4,0x6d1875d96354db465d75,0x5d96354fb26917658d53,0x54fb16a1765915361fa4,0x619765cd536d1865d573,0x5d953ec9a45d97354db4,0x693a16617654d98e8994,0x6617654db4e85985d953,0x54fb3e85985d953e9fa1,0xe85985d953edba166176,0x61953e9fa36617654fb7,0xe8fa165d8654fb165d92,0x65d8654fa6e859761953,0x54fb6e859761953ecfa1,0xe859661d5365ba065187,0x54d62edfa16598754fb3,0x5d9a25cd5358bb25d973,0x61d53589b9e897654d62,0x589b35d9535c9626e7a2,0xe89765cd626e97654d72,0x5cd636d1a75957358db5,0x6d3a55d97358fb269176,0x5d97558db45db955cd63,0x58fa5e85985d563ec9a4],#[0xe85985d563e9fa166175,0x61d63edfa16617558fb5,0xecfa16558758d95e8994,0x6558758fb6e859561d63,0x5cbb25d96354d72edfa1,0xe897658d726e7a25d953,0x9cce5b995e653b93e5b5,0xce6b33ac5eadda3f28f9,0xdae17b64ed53b4ced17a,0x7275c97723dbc4ee96b8,0x333cbd72d5caf72b5c9f,0xf1ce4f375cd5f353ccdf,0x9d3574b5d1f7475d0f73,0xdccf713d8f7637d8cf4f,0x44fad5ead7a5de8f7a37,0x2cbc203265c1fc4fd93f,0x9c598af06badb5aab6cc,0x5e84f0ec03c1a43f0684,0xc4f0fc07c6ec2f07b49c,0xf1cc3bc230ff1cb47c02,0x502fc638df08e4bc234b,0x3fc53d0f00fa18742069,0xc5528619575a554ff193,0x6a6ed5a4fb76c5f0563f,0x5f0971bc05e3edda97b6,0xd6117c2606f0188bb76c,0x467b5906f0635fb6859e,0x3c2c08f16d27c2b55ede,0x7d09f0af6fa5b9b696e3,0x15edf75fb6dc5f07653b,0x7085d3c20f465844fb7e,0x676bc81e1f087cfc21b4],#[0x73a625a32087fc723471,0x6466af1d2a7cb45ee94a,0x7a4ed1cb564756ed1cb9,0xece0c3b67f1ed5f9fc2,0xca261b28b0eda1c7b587,0x2b193c6c656e5bb4958e,0xdc2d2f55331fc2c8770b,0x5702b0005bb4e56ed351,0x51471271010eb0bc0890,0x22a2061dc1c019c17b16,0x4731b2f02ca2a5279255,0xe4344103e03ba3973723,0x4f54e14d24b149547444,0xae59158156054352f51a,0xf68e67b64a6215f45cb5,0x74a74272b70d6ef6d56a,0x8277a77276a76275a752,0xa7b27aa7a279a79278a7,0x7ea7e27da7d27ca7c27b,0x2281a81280a8027fa7f2,0x3f8084a84283a83282a8,0xda04d041784bc46e07f0,0x337080223843033b0840,0x1ab06d82781be4300810,0xb0dd87ec2a04b1266982,0x809304bc07f05f43f043,0x441b785f42fa0fc11019,0xfe82e083024398c08012,0x1213e498408066204019,0x1330c9840d3de86c4c76,0xc0c82490f784003ec1b8,0xa14d08ec18b21014908b],#[0x6453223035860c0b7b07,0xf19fd090e7c73c011b48,0xd6e1390e19e645306502,0x30033c4f184be0668640,0x130120d0ba107c292705,0x809404fc2f7809027e3d,0xfe00f90202501bfe2409,0x356604a000bfd73e1206,0x808a01ffc0c91e05ef03,0x196018fd08d1d8128dfc,0x2a8899c4ff011013ff00,0x43e00671fa590047afcc,0x65c8033c9fea4023b786,0x8f480474271fa0239781,0x20200cf5fc3218019e0f,0x9004706fe79444ce19fd,0x12380475feea008c27fd,0xd40118033f8e0401a27f,0x5bfc03206502fc18c0ff,0x90328dc682287e84819,0x70602042ef821d5a1ec3,0x12bd640c9be0862e682c,0x648f990326dd08bd5102,0x8019dbd3c7200cd5f320,0x68af0faf003377fac10,0x6c00847b8095f6d20d60,0x8a05f831e3c008810a4f,0xb9f048de190324f0fa0]]
set_option maxRecDepth 32000 in
def g255D9 := limbs80 #[#[0x5d563549325956354932,0x5d573549325d96354932,0x61976549325d97354932,0x5d973589325d57358932,0x69573589326157358932,0x61d76589325d97558932,0x695765893268d7658932,0x6156558d325d56558d32,0x69d6558d3265d6558d32,0x6157558d325d97558d32,0x6897558d3265d7558d32,0x61d7658d326997558d32,0x6957658d326897658d32,0xe899758d326959758d32,0x68975595325d97559532,0x68976595326a17559532,0x6a197595326a17659532,0x5d9635c932595635c932,0x5d9655c932615635c932,0x68d765c932619765c932,0x5d5655cd32695765c932,0x655655cd325d9655cd32,0x69d655cd32659655cd32,0x615755cd326a5655cd32,0x689755cd32659755cd32,0x619765cd32699755cd32,0x695765cd32689765cd32,0x659955cd325d9955cd32,0x661765d532e89965cd32,0x6a1765d532689765d532,0x5d9925d532ea5865d532,0xaa197595435d97559543],#[0x655655cd435d5655cd43,0x69d655cd43659655cd43,0x659755cd436a5655cd43,0x5d9955cd43e19755cd43,0x699955cd43659955cd43,0x5db855cd43695965cd43,0x65d6558d5361d6558d53,0x65d7558d535d97558d53,0x6917558d536897558d53,0x61d7658d536997558d53,0x6917658d536897658d53,0xe897658d536957658d53,0x6898758d53e917658d53,0xe898758d536918758d53,0x6919758d536899758d53,0x68d765915361d7659153,0xaa587591536a17659153,0x5d9645cd535d5645cd53,0x659755cd53619755cd53,0x689765cd53619765cd53,0x695765cd53691765cd53,0xe91765cd53e89765cd53,0x5d5925cd53691865cd53,0x5d5945cd535d9925cd53,0xe95945cd535d9945cd53,0xaa5865d153691865d153,0x689875d953691865d953,0xe89875d953691875d953,0x661925d953e99875d953,0x655935d953651935d953,0x661945d953e51935d953,0x689985d953e89945d953],#[0xe85985d953691985d953,0xe91985d953e8d985d953,0xe9d985d953e99985d953,0x64f925d95361f925d953,0x68f925d953663925d953,0x61b945d9536a3925d953,0x663945d95361f945d953,0x65d92619536a3945d953,0xe8d946195365d9461953,0xe9d9461953e999461953,0xe8d9761953e859761953,0x65f9261953e999761953,0x6599261d5365f9461953,0xe819461d536599461d53,0xe599661d53e8d9461d53,0xe8d9661d53e859661d53,0x65b9261d53e9d9661d53,0x65b9461d53e5b9261d53,0x6939661d53e5b9461d53,0x5d97354d625d57354d62,0x6a17354d626897354d62,0x68d7654d6265d7654d62,0xe897654d626a57654d62,0x6a19754d62e898754d62,0x68d765c9625d9535c962,0x695765cd62661755cd62,0x5d9925cd62e89765cd62,0x5d9955cd62655925cd62,0x68b955cd625db955cd62,0x68f9261d6268f925d962,0x69187595636898759563,0xe958759563e8d8759563],#[0x69d655cd63655655cd63,0x691755cd63689755cd63,0x689765cd63699755cd63,0x695765cd63691765cd63,0xe91765cd63e89765cd63,0x595925cd63e95765cd63,0x5d9925cd635d5925cd63,0x595945cd63655925cd63,0x5d9945cd635d5945cd63,0xe95945cd63655945cd63,0x5d9955cd63e99945cd63,0x5db925cd63597925cd63,0x5db955cd63697925cd63,0x691765d56368b955cd63,0x691875d563689875d563,0xe95875d563e8d875d563,0x661925d56364d925d563,0x651935d5635d9935d563,0x661945d563659935d563,0xe85985d563e8d965d563,0xe95985d563e8d985d563,0xe9d985d563e99985d563,0xe89945d96368f925d563,0x697925d963e8d945d963,0x6559261d63693955d963,0xe899461d636559461d63,0xe999461d63e8d9461d63,0xe859561d63e559561d63,0xe999561d63e8d9561d63,0x6579261d63e9d9561d63,0xe579261d636979261d63,0xe579361d636579361d63],#[0xe579461d636579461d63,0x655935d9646939561d63,0x5d96354d72695935d964,0x68d7654d726597654d72,0xe897654d726a57654d72,0x6957658d726a19654d72,0x68f925d972e897658d72,0xe8d76591736957659173,0x68f95591735d98559173,0xe95865d573e8d865d573,0xe8d945d973e89945d973,0x697945d973697925d973,0x5d98560973693955d973,0xe597661173e557561173,0xe5976615735d98561173,0xe859661573e8d7661573,0xe9d9661573e8d9661573,0xe8d9561973e859561973,0xe9d9561973e999561973,0x65793619736979261973,0x69176e1573e579361973,0x69195e197369196e1573,0xe859560d76e898460d76,0xe9d9560d76e999560d76,0x65583e0976e578460d76,0x69593e097665593e0976,0xe8994e0d76e8984e0d76,0xc9fe3ef0fd69195e0d76,0x73779afcbf65f72f795f,0xbcfd67e73d79ddcede6f,0xfb4fba7bd37e97f47f9f,0xbed5eeaef55fa9fd3fa9],#[0xbeb5f3aebd6f6b775b7a,0xb3bd97ecaf63fb1dd8de,0xed6f6afb4fda5ecfd67b,0x5b79db9edbf6d7b5edae,0xeee6f733b8fdc5eded6f,0xb3bcbdddeee7757b9fdc,0x2fefeb7f3bebdef6f6f7,0x8ffc7f63f71f78f7c6fe,0xe65f2ff97bcbbe4ef26f,0xf9fdcfbe75f37f9bbcdb,0xfe9f74f7a77d2fe8ff46,0xafabfd5eeaef56fa9fd3,0x8bebf75efaf5d6feb775,0x6efb73dabed4f677b37d,0xdebeedf767b97dc9edef,0xf8bfc57e1ff0ef7ebbf3,0xfe5ef2df92fc7fe3ef1d,0x5f9fbcfbe7bf3d79afcb,0x73eabf4ffa77d37e99f4,0x85fbe7dd7edbf6cfb2fd,0xe53f1ff8efc6fe33f0ff,0xfaf7d6fe97f49f9cfcaf,0xff33f8dfc5fe27ef5f6b,0xbfe4fee7f57fa9fcefe6,0xb9b4e009f61c01fb3fc,0x29861c04dcd380695760,0x8ddd300e718601c5b2e0,0x9e99702c5b2c04986180,0x11f6a0b985d81138c281,0x23ed44d30bb0927d8511,0x2cbb04e059707c532e0e,0xf396179176a177c65c27],#[0x2b6a464e5d97245da8cd,0x2ec8a655d913165a6259,0x1d8a288bb23312f64642,0xfb560a6aecd852695ac0,0x764c64d5d9b46ddab11a,0x6d8029abb4453576761c,0xbb02641b90355b4c03ae,0xa805543660aa86d40f50,0x6a239a61c1aead283269,0x1850e0d289ea1b312d43,0x904281b807573640e9a6,0x808bab641191ed42125d,0xe15756982b50bb05587b,0x2550d904a81a609c832,0x85243b20a30b5016996a,0xdccb0e1975694311fda,0x291ced83443d886881b5,0x574cbb0ae999614d5b64,0xb5c1b216d43642a91658,0x8cf30c310eec45cb9dc0,0x9d6585ee0d30c643961,0xc4fdc0c8f3b5181ef643,0x5c1a51a3674c36996186,0x53aec1d0d6d47132c30d,0x976a0394cd98729db20e,0xead187cafb60f4bb701c,0x4bb5108af62212bed440,0x83463a9a6187a23db084,0x26dc784dda8ec93b61cb,0xad2ac5b5ba5854366b00,0x1765455aeaa83aed562d,0x36aa7a8ec94f3ad429aa],#[0x65d5a80d9ab4c3b554d3,0xd92a9d1a5558eb72ad8d,0xb95719b66ae1eec5591a,0xecb613ecd5e2bd8abc51,0xd5691bd92e09bb55946a,0xaaec2fb55d1cf66b33a6,0x384d336b05a8eca0a0bd,0xb071a6e6131acb424f5b,0xa1037d8c2235b28337b4,0x4284fb3850af630a17ed,0x869cf670b3a6d61823db,0x41a65d8834ccb10027b5,0x881dd891170b821c8b2c,0xf9b3a6239e76a4508edc,0x60836e3f97ae07d2f540,0xca06d09941d913281b22,0xb23d913645b226d07684,0x299762848f684d916d09,0xd32ec518f65ca0e8d314,0xa66c89d1ecb945d1a628,0x4dda13a99b427537644e,0x3db427c7f644f8f6c89f,0xcb0e5474694a91fda13e,0x961cae7eda95dd1a52bc,0x2c3955d1a52aa0764559,0x5872c1fb6a5874694b13,0xb685399ec8a732d914e6,0xed8b2c3d316667b429cc,0xda968d7b02d30f4c5b2d,0xb52e13f6e5a2ded8b461,0x6c5d1fed4ba41d91747f,0x58db3ac31b467b72e8e7],#[0x498a6586371e76c6d8f6,0x637ceb0c6fa66d4c6dfd,0xc713ced8dedfd31be3d9,0x8e018db1c5599638b7ae,0x19275b2323674c709961,0x32cef68649d6d0c93bd9,0x6a99618ceded299cf3b2,0xd132c31a8f1b53537b4a,0xae65863437b4a683dec8,0x34cb0c6b3c6d4d6ded29,0x6996d0cd33d919a65b23,0x85bdb1b0c3b5364cf686,0x9d1a52f93f6e6c5ce9cd,0x9276e602fec4c0f65c97,0x2ced8e465d99c841b730,0x2bd89e445b63989b6673,0x1bb1450af6288566950e,0xb76a89566951207db228,0x8ecd1495d8a2857b1452,0x4c31f87db53e107647a4,0x7b13ea4b307e5d61cfcc,0xf667403ed91c2bd8a345,0xe98ea49db9d16ba73a16,0xd81d96ba63b9276c755a,0xb23c1276c7627eccec53,0x6c815ee9d02c7d320491,0x9d04c3d32097bb740b1f,0x120529a240ad74e845ce,0x440c37668186e8d0295d,0xc8183e990295d220529a,0x902ffdba05ffa740c1f6,0x20529b440a5764814a6c],#[0x3f89f667f15ec4fe95da,0x8282e99050bd2a0847b6,0x2bd8a005bb0403f74e,0x47b64009f668014ec9,0xb8af628f7be9d0821dba,0x161e9922cbd2a4457b14,0x2bd8a400db7490236e9,0x18fa64a347469415ec53,0xb2f4a9563ed928d1d9a5,0x15ec5422bd8a6587a64a,0x97cb26d2d964da334ca2,0x57b1518af629a046d938,0xf74e9e68e8d3c8cd3290,0x5e953ebddba79a3b34f2,0x5d3a7573a74fb0f4c9f6,0x59565d32eacb16ec14ab,0x76cce8c5d99c72dbb2e4,0x5d59f18dab5ce7b5668e,0xd2b40e5b767c8b2acfa6,0xa669462ecd26ce99a0df,0x6ad439ed5a2d8bb34d4f,0xd182d9d9305b1b260853,0x330db1a66136768c16c6,0x26cc6364d9a6ed588d8d,0xac58ced1b318da36633b,0x58c72dab21b1a5643634,0xb24e7b5633674ac66c69,0x651cf64c7396d592d8d2,0xbda0e957c57daaf1b1b4,0x7a57daaf4b7b35e97764,0x8283b35f95b64bf24edd,0x1462ece315ec5c318bb3],#[0xb15ec5cb23dab929bb57,0xc6fdab6ce7b36d9d764d,0x677a56f1376adc74e95c,0x9376add27ecdba51d937,0x9decdbe4cd937c93b66e,0xcddab9d7ba773b374ae7,0x73a77432f4ae85eeddce,0xd74eea5be9dd2c1d33a5,0x4e55daa8cabb42bb377a,0xbd93c029b57729b2aee5,0xda57e8af62fb15ec5e23,0xf6cfe34ec5fc09d9bf11,0x655e6cad2bfc9fb77f16,0xd8bc811b57a24f2af349,0xa5808af6300036d5ea2b,0x4ef763e99eed1d1bdd1d,0xddeec7db3dda3b37baf7,0x3be187a67c32f4af85ee,0x77cadf4ef660e99ecb9d,0xb0f5ae9a3229d94096ba,0xa3473d9c38e5b587b634,0xc6def968e0c36d1a7d61,0x8983b65136fe96242eda,0x2a28eca5319cb479bfb3,0x28a0cac5023b38b0a765,0x5c21b58aa7b2b1550e56,0x380f67261aeca3011d9c,0x819ede4e39db49c87b19,0x48fd2cc45bb095ab34b2,0x12795960af633313ece6,0x24b2b3549656688ed2cc,0x3eedc947ddb92453b29b],#[0x77dbc12a7b38857b4a5f,0xe7b117587642cafed856,0x4f702e76ed85cf1d90b9,0xd6c86d5bd90c2b59618b,0x7d30de57b21bd4f4c36a,0x9b55aa236a3878694712,0xf6a42afed88355d92dea,0xed888efda911e7b12257,0xd311eb3b522b8f6e4476,0xb124c9f4c4894ed49153,0x6c4a45ec49487da92517,0xd0ad5fda14abfb22920f,0xb1beb1b5375636c6dafe,0x432d676465ac6d4e158d,0x260afed4bf59da1a6b3b,0x90d37db98287b3305176,0x2326fb745ca7487b9bed,0x46c4f628d5fee91937db,0x8e4cee91b01dba3613b6,0x8d5da205aba440b276c,0x1591b442323648464e91,0x144f688189e9102bfd22,0xf80e9d0709d320e1fa44,0xf0fd9a3e23b247c4f628,0xe1fb34bc4f629784ed91,0x3232e926965d2309db25,0x84ed9210fd9a4227b148,0xfd9a6227b14c2fb2e93,0xaba24a353449484ed931,0x534894a4ecd2949d1a51,0x2ed92945d3251aba44a3,0x4ca251abb24a3536494a],#[0x5a24ab5768946a6d128d,0xf4895696912ad3d1255a,0x6512b43d32568fa54ab4,0xd125991a24b34b689569,0xb24b3274896646912cc9,0x62a1646d12cc8ca25991,0xcd4713d8a8e1fb350c4f,0x2279aba24f4076ea387e,0x44f357649e6ae493cd5d,0x89f69e893ed5da279ab9,0x140d3ca27da7924fb4f4,0xb36a5b6662ff28a05fe9,0x6054b6ad1a96d9a152da,0xd5a9ed18953d9312bfb4,0xab53d2356a7b26ad4b64,0x8aa7b463d4f68d5a96d1,0x154f48e2a9ec9c552d93,0x493ec9c953da38aa5b47,0xed5d139e4fb47249f48e,0x5abb473b5764e76ae91c,0xb3f48e9316c9d2cfd13a,0x89ec600bfd23ad9db474,0x1dbc0213b68043f6700,0xabb47bb5728f76ae91ef,0x2748f969e51f0d3d23e1,0xfe51f4bfd23e993947cb,0x29947e3ba48ed4f670e5,0xfb29007b652058e523ef,0x30b1451e5242afca4803,0xe4a44f2994895fb39339,0xca48d5f9291ac7292258,0xb381a8f2925764ca48af],#[0x92d42ec60927d9c0d07,0x525cc9c24b9639496b57,0x1479497aff092f55e,0xc01c2030c0488066005a,0x1581e9034a061c0a7810,0xbd016c02aa04fe09641,0x507ac0ea01c8835c0658,0x7f04c50924118021a840,0x17402de058c0aba14a42,0x80d741a2832b06220be4,0x987d50f3e1da439606f,0x249847c08bb1120215c4,0xa147627c84df899412ca,0xb18b4116182b545538a7,0x31a06208c05178a2e605,0xa1aa834a86758cbe1914,0x2d0e221be0371c6d18d7,0x3dc07a38f1d1dd63a787,0xa213641488140fed1f50,0xf091b522f444ec88790c,0x4ba8955127924a4486c8,0x427c04ec89bc9357263e,0x8b94df296051c4a21141,0x5914af615bb2afe5514a,0xa2ea25c68b6d16a92cf0,0x4f186230685fc0bdb978,0x66a8cbf994d32286378c,0x235906a34d2b9a2533c2,0x199bf937746e00da31b1,0x7530e8c1cd4392e71b0e,0x63cc07880ef71dbc3b06,0xe49f833e847c18f649e9],#[0x83910592072406a8000f,0x1440c87290c72156422c,0xb7a32d45e48add13c224,0x9285230242747cc8e951,0x54b9096452aa250e49b8,0x9ba6f54d5c99f9320a60,0xa12140327cc4f329d953,0x752eca4f948528bf5126,0x50aa6c5494a8914fca9b,0xadcd5a22b1455e6ab055,0xf5898b0815f1abc05744,0xd92d785a72b3c965e2c7,0xbac173dae5c5c5cb7f96,0xf5fb0be297af2f225dde,0xa9b12561c6c275830300,0xca4992432026378c6198,0xb6788cdd19a4330a6588,0x7bb4be691cd145a1433f,0xd849aedb5a16ae4d4e1a,0x56e38db55b53b67b6c94,0x13b8016faade69bb8374,0xe525c8438c1711ae189c,0x274c8e8e9cff39d17320,0xcfbb71767cec01d67ba9,0xf28de3dbc3b780aef6dd,0xe7ab8f4cde86bcec797e,0x383e347c24f7c1ee83d8,0xfc51f7a3ed27d5afa31f,0x8801eff51fd5bf727ea4,0x8e40e0817b0282041c04,0x8ee0fd41c8832d055a0,0xf86450bd6164429f84bd],#[0x26c41b87d30eea1c0c34,0x141a26d44b6892711b62,0x28c0117622d045688a89,0x7146c08d431a1632fc63,0x1e7e3b8c74e8e471c0a3,0xf916921fe427c80f8fb7,0xf249ae92f52512487c8d,0x2bd65544a869499287e4,0xf98312f565c64b529645,0xc24d539a3f337a64bcc5,0x3a5672d4e1c9bc136d26,0x69f873e3279ccf1c9dbb,0x6850b3a10741768144fe,0x473a8c55159a24543fe8,0x6a5d74ae693f5249a3f9,0xf7d3c4a7334dce9a8532,0x536ea51d479a88d50869,0xaab6b564aaabd539aa19,0x5bd67eacb158a6b0055d,0x5e76bb8d740ae2f5baab,0xb13361cac1557fcaf7d,0xe9d9a6b2bd6472c7358c,0x6a8ad3fda54b44f6812c,0x4b6976caed835ae1b58b,0xd5bf7b7a96ee6dcb5b7,0x7556e8bdcd3b9417156e,0x1bc7f782eef05db0baf9,0xd2df70be7f7bf6f5dde8,0x82db037e034c0177f7af,0x4c35585d30a6e11ec1cb,0x8162bbc50d892310261d,0x8fe71e8639ac6db8d031],#[0x4c97992d3242e45dc845,0x7664e4c9b9935326664c,0x94532866504c9f993d32,0x4ca7994d32966524ca39,0xb66564cab995532a6654,0x96532c66584caf995d32,0x4cb7996d32d665a4cb39,0xf665e4cbb997532e665c,0x98533066604cbf997d32,0x4cc7998d33166624cc39,0x366664ccb99953326664,0x9a533466684ccf999d33,0x4cd799ad335666a4cd39,0x7666e4cdb99b5336666c,0x9c533866704cdf99bd33,0x4ce799cd33966724ce39,0xb66764ceb99d533a6674,0x9e533c66784cef99dd33,0x4cf799ed33d667a4cf39,0xf667e4cfb99f533e667c,0xa0534066804cff99fd33,0x4d079a0d34166824d039,0x366864d0b9a153426684,0xa2534466884d0f9a1d34,0x4d179a2d345668a4d139,0x7668e4d1b9a35346668c,0xa4534866904d1f9a3d34,0x4d279a4d34966924d239,0xb66964d2b9a5534a6694,0xa6534c66984d2f9a5d34,0x4d379a6d34d669a4d339,0xf669e4d3b9a7534e669c],#[0xa8535066a04d3f9a7d34,0x4d479a8d35166a24d439,0x366a64d4b9a9535266a4,0xaa535466a84d4f9a9d35,0x4d579aad35566aa4d539,0x81f845c46c47c0fc06ac,0xcf43782f43e09019bc47,0xd090150103097c270440,0xdec2a0cd06e085843c2,0x3209d085c2b080180222,0x40901a14c01c74281ef8,0x6ec3014744189dc0820,0x681cec3b8401380ca093,0xc0d82481b21041060ce0,0x4c0cc050449c4c108016,0xa81f816022e098c9a49a,0x64c019741a1510901481,0x42dc340824dbc301da89,0x680ec4db4c10d8158213,0x1704c343783c14489f0,0x10287c1500dc0ea1ad88,0x8812c89011ec230c7811,0xb0cb09e0ab8294881d28,0x4a5c3d0ca8990e507ac0,0x8684009026c87813089a,0x643817ccc701a4809064,0xc3827542fc12c7188208,0x2cc9ac284f90a98888cb,0x249548488c1288e02311,0x4d02670810e9cc0a0e0c,0x7949b08bc130de8800e2,0xcc3808a0aa8b60a48cb0],#[0xca0ee08d4318900804d,0x3c8a348115649e4298e1,0x44d44a5c10cf818d0c68,0x81c5028848dd0a828893,0x26c1d0db81860dc2000d,0xc88049a8da0a30e212f8,0xe2c82c3386906c0a087,0xfa4c825c4cd8881e6832,0xf0c649449409e8894809,0x87c8b08da48b8a8c2f03,0x8a43c0aa4be4318b44b9,0x14fd4414394d443ccbcc,0x16e0e9c0943214414a0d,0xb9c7ccb4c7c4f216d09c,0xe1538844fa86d89647c8,0x8948f942f4140fb45981,0xbf08c08908913007a068,0x88a208d08a0184bfc298,0x4d81ba03c06c1ac20820,0x344809f5c1b43892a8e6,0x80a58398a40e14dc8358,0xc330d10c0aa58a28a483,0x2acb8cf0c3c4894b8838,0x8c885f2c5c0d009cc358,0x8e886e48843a8ce6a8cb,0x484f1ab28220b88a823c,0x612ac600594f1c700621,0xacc5f093c04cd4ca613,0xde89109d4b28b9cb301b,0x2cb4c41c2ec1383144e0,0xc081c8d48c095042d0a,0xfa4b18f28c68c10fa8ac],#[0xec004310be45f4261018,0xc47f2c128a000a737cc1,0x62f5280087874b3b0010,0x29e8d800861f55011658,0x29dde0a62fae3ec00448,0x91f5501166f875995800,0x8904be181dfd9d8008,0xb58002969f4f5edb7858,0x160021bbffaa00653bf6,0xa022a7dd7edc00cecf6e,0x3423b3b722ac00446ea,0xcfdad88004457c8576a0,0xf5ffc04a0033dc9025b6,0x7c0b400684fb7eac800c,0x120043c09fe100086eeb,0x7a7df90720010f0d3e11,0x760010d37a227984000a,0x8701bf9eea00087e43b,0x78f97dc0033fb8f5b200,0x2000cf3e3900230ed037,0xfd87fb695800d01fe1e6,0x9610010e0d7f9a4c0010,0xfbffdfc0636001114f85,0x560005423e4efb400043,0xff4b352800876b8bfdb4,0xa8961d2cd4a002225,0x862760022b2e265fc196,0xece64a280029fdbb2f80,0x696002253e34d50033f1,0x356fd0d5003473d9c822,0xa0067f5dfc00ab2b0011,0x1a53e34d5003397f0faa],#[0x83db0011445fd282280,0xd30646c002249fff664c,0x8019e3d7e08800cfcf93,0x72edd23ca0069cfd28de,0xfa00650ff8b372d00347,0xa02467e9f9215401a03a,0x21c00a4000a8dff803a,0x4737f27160a10008843e,0x10e3f9c80230fd42d40,0x3fae71400cf2ff6e8420,0x808f1c787fcc191001ab,0x80915f82200336ffd45a,0x4019f238d9819a4f389c,0x11af74c0e80043e6a3cc,0x53200112cfcf09762001,0xc0468200116cfeefc367,0x7fea10a0021fdfff0f59,0xebd10019bb66e5a00675,0x4545ff1ecd30c053c7,0x224008800b17ae8c1a34,0x14de728d0033e3fae5c0,0x19cdfe5f1dbb0142001,0x7a8963c800d8da7837a4,0x226b3c37d0019d0bff5,0xdbc800d72f87f23c1c40,0xa76fe485a00678e692ee,0x24e002216ff515104000,0x868fe24c00cdafd510,0x9fe6042001124e5ffef8,0x2225fc936420010e4e1c,0x260f002125f24d880400,0x30010d6fc5ca49280088],#[0x38137b3e00c05303bbc7,0x16fc2c00cfdf5bf0b003,0x3401c78a850de000a8ce,0x4abc040021ebe9442d00,0xa70a47fc10019c1fe,0xb8317600220eff4b8004,0x468187e558002989d38,0x717c02ffcb6294420280,0xd92000535be0e10d8008,0x111cc7d9924008773d2,0x7fd8010e007f2ffe9cf0,0x17f7e7104000a717f402,0xa709002211b65fc8010d,0x5f3292b52000548b659f,0x2001110d0f6a9803445d,0xb0f28be00d4057bffa64,0x46bfe4b3da9810ede18c,0xa24008700b87fe13c004,0x10ff697a860297de847,0xbac25000a907f6cbc5c0,0xf9a22f6900087038fca4,0x27000892a6fdf0b00029,0x6512a2480045eb8a7c40,0x6e0e7fc28010f0ff4da,0xe800539b853f7fc28011,0xefce20800150f667024d,0x9c10e2fec4240088832b,0x6a9803381f7edb590002,0x481d9bfe8c8400222139,0x604393ffd7c6fb2f6004,0x41dcdc800441bf93896a,0x43813706efdc6029ddb],#[0xd3137c0010eedb407f00,0x446bd7bbe8013800449b,0xdbc28010f8cdefe84800,0x32e8e78529900089a66f,0x2001138ed77675320011,0x470640022414fff8d04b,0x67d39a6180a797f8bf63,0x8863eb4ce20005300,0xb308001500fd3c1e489,0x3395a2f880014c37ddb9,0x80015156af0220005,0xf66126240011137f6227,0x1122fe3f8eea4001108,0xcc2400113af542192240,0xa7c3b16c980069d7f25a,0x225b6fae4030d40035,0x60a4001138f838a2b88,0xfd9c516ab080089c7f5e,0x80089f7b38aac2002209,0xd561001124ff0ff44ab0,0xfafb2d34801a59ffe202,0x6a37ff87a255840044a7,0x46c003427f11e8050800,0xffd4cd4964001121f88f,0x88e7ea46414900044b3f,0x8440035e3f30a6a2000,0xf51ae1088006aaede403,0x93cfe40c8a52000894f,0x20b881001133d7e63190,0xc98a88488008987fff93,0x80087dfe48b8a01255ff,0xbaff35b0008727eac468],#[0x1131ffb6881c10034f,0x86040045abff9b20b881,0xfc1e8a01211f2c5fb084,0x777f24840a608002ab7,0x100014e247f26240010f,0x58b7e445000d51617c45,0x87ff55a29848002263fe,0x8163e0042c72bf3f0066,0xf81a47041534bb380108,0x9fe8b20068a79400849b,0x68e3e0043011f0021020,0xf0019fdb7fe580043437,0x790032ef7d008b1fced4,0x33d3fe9d4c640002273b,0xc4fcb28003457b05b800,0x5353fe9d4c640002273,0xd8d2000112005f99e000,0xf0025980008907bfffc1,0x149ef2350db800350bf2,0xd0047e5ecffa0b20001,0x7e940e000cf890e76e00,0xfd1d9250021d7dae022f,0x21c5f978012cc0004483,0xda4b4001132e6e5c2000,0x1182fa4b40010dcf5cf,0x4413b3f944b08e7640,0x7419480022ddf2179d90,0x749184004433fe2f9b24,0x2be0704c02000a967ff8,0x957ff262a2122002258f,0x1e5a20021d6bf249e804,0x456bdfc0429801104fc],#[0x100113efff2660845440,0x86040045e3fe1ffce121,0x3a062400d1aedfe0e084,0x8f6ff16384844004537c,0x432376937a4b400112,0x14ad2e75000460be92d0,0xdf6d2e7500044139b17a,0x12a7803323e8c9300219,0xd00a7fff9840800886f,0xb7b667200d2197e63040,0xebc65e2168c3002249bf,0x18010c97fb46fc410053,0xe3b5ff12000a7178b66,0xc0014f576f345380029c,0xdfd18370010c67a99a29,0x96c0403169a306e0021a,0x1f9c0708c300000a9cde,0xd2d9080a53192e080627,0x4c00011099ffe0003321,0xa48fff42e0066664eefc,0xfeb000c4102210e07080,0xcc000a60fe801c00ce8f,0xa91300202000a9bbd3f3,0x923fce18fa9c00449dff,0x544df1006a901d2000a9,0xc04086abfd28a0103000,0x67f42364081014f2d127,0x128790033a67ff8000cc,0x1a014fffeda81001119f,0xaad1c40044372eede080,0x861be169840014d2fdd9,0x30080820a9ddcba38800],#[0x20069a425e2002190ff5,0x60bc520002a0a12fc382,0xc3820f3be7e2019b4dcf,0x60bb0426bfd0798021a9,0xbf2f8002144ff3000a4a,0x40151d7c6d4c000537,0x231fc0861399ffb80002,0x10053af380308cbce00c,0x42313ea041a1fed600c0,0x81108c1d70680665f718,0x10080445bea50422f3,0x2010e7f02184f8ffff8,0x457fc182019b5ffebc06,0xe00220dfff800184404,0xf926018c004423fc9200,0x659f1a022afad01149f,0x5ffd4010104153e7a710,0x1132ffe5c020440440,0x2a080010ead1fe454083,0x1512fc8ca0c0043cbf2,0xe9c40196afd8f50040c0,0x3100036c05bf2e101519,0x6176cd4e00433c8cf040,0x9bec08010c2c5cb9c008,0x104088c3e523800029b9,0x81d06882018a8d18fe04,0x2c1c029b0fd2598700a6,0x28780852b639065abc4d,0x9087e00ca010fc01949f,0x40620811137f2dc1014b,0x153b5ec8005223fd5f6,0xb610200153e9f7b61020],#[0x82043bb93e20042e9f7,0x198af42b61014b0ea37a,0xd88065e917064cfe1000,0xcb6fa94109b6878c2317,0xca37e3e000297a9ee00,0xa9c5f5cbe00086cf4e20,0xc74001a66ff5b0060820,0xff74042a2000225bc245,0x21dbd25d64001a0d,0x21bbf6ae3803323ffc73,0xff8514001a19ffa24000,0xd2df3eea1e80034d75,0xfb64fa000d252d3a87a0,0x19e2fc0f8e0000053b7c,0x8897588003577f56c400,0x760000454e0fc008cdf3,0x961d0006787f097b3fc5,0x4001105f9783a000d05f,0x22c80900045ebf98de02,0x5d82de120008ac7f0f4c,0xff13401b04400054abf4,0x22a6ef7956080029de,0x4c001140ffff3aa642c2,0xffeaaa001a1de31ed240,0x4003437fcab6a001a2b0,0x53a75fdd40033d7f6d55,0x604004421ff8a1341000,0xf4889d0400d5efffd445,0x7fff55288e408008acff,0x3213ffe0ece40800882,0x8bc1fb150c08008bcd38,0x1a507f07204004403fa3],#[0x12d1c11000151baf8101,0x85866e2e3d80043b9ff,0x92dff44ac002185e68c0,0x19729b73c1003436bc01,0x97dd7e005001119dbc80,0x970001126fc60ce00087,0x7b5e1014a0f64cee0f,0x2bfed09084a4c1000550,0x760014e2f8b85e4c0087,0x8ff2b7e080a6a3f148b1,0xe00cc075ff9cc040029c,0x5002175e2e004216df34,0x480334202f880086276f,0x85d7e815260021cb6e3f,0x2f6e4564400d3aecac00,0x480200029cbfb7b20066,0x431bd5ea180021eafd7,0x8029d68dc0a367323d28,0x4b76eec10847fb386c18,0x624397c0010b7737000a,0xd3f36ae000865df70000,0xf320300014fae5f00042,0x14a27b6f46c0029909b,0x43b22f17002140e3faa0,0x383d1000a567cf078000,0x583081015120fd1047d,0x153cf9b470004355f56,0x99014807fc994d0041c0,0x558033474d370066c3f8,0x44b1ffa98980014ddf5,0xc001524fff9da0c68c0,0xc1e00010c05dff80c243],#[0x70023f3eb23a41021d5f,0xc004359e856c202957a3,0x720cb1f20e4196983a4,0xc1f434106697ca0838f9,0x216df5282103e86820c,0x200cb9fcf0032d30fc10,0x63e388032f3c0083cf4e,0xff63263001119e9c4019,0xf65de56a2594000aa562,0x400224917f29a80043e5,0xc29500221dfd1fc1510d,0x43878297006677f47fe,0xfe1e4a004303feb0e4a0,0xf740021d3e0bc58033b3,0xe17c6d1420002a15f353,0x2a05e6fd56ce000884b,0x1000a8008ea6c75e040,0x9bc80400298affa2e209,0xa7b7fde1a40004395,0x6ebfaa0014a76b7c5392,0x2c0000053ed871400294,0xfdbc389000002a6cffb7,0xa76df07400018a039,0x5e1c232018b37c2e2400,0xa955000532dc3f000a4b,0x8162fbe4f60010b97fd,0x2fc5e71700044a0fd21c,0xf4fff6e427300044019e,0x888002a4dfd5f244c410,0x5bd0000151a7fb121065,0xa57bfa2a80052a983e4,0xb7fd6f80014cf7f45500],#[0xf973aa5fa86cdb85281,0x7c4ebf85b4e98e414ff5,0x6ec04e9abac5c98550b]]
def g255H9 := limbs80 #[#[0x3de82000c0810420606,0x10000b481c103409b0,0x2d8132c93690e0848e04,0x939247d1ee030dc5fcae,0x68ad11210135646812e,0x310f80fa9a0a15c58aae,0x50a1e44c10638cb40000,0x8b8712fab464dda00002,0x4e0050a006350366e5f8,0xa0a26742348295017dea,0x214000110a47a4672002,0x1968af4d2532629c9b2,0x6600000cfa7055ca8a88,0x8029503860012569a024,0x10006391f94e86c3a006,0x4000399e280000536000,0x6b0b88ee00019da26552,0x1f052978900008e9e462,0x44800e522848a609e2,0x5288f25c4c8]]
set_option maxRecDepth 32000 in
def g255D10 := limbs80 #[#[0x549325cd524c96354932,0x4c98754932619524c976,0x5d9624c975589325cd62,0x5893261d624c98558932,0x4c97558d32595634c997,0x61d634c98558d325d963,0x595325d5654c99758d32,0x4c9635c93265d654c976,0x615724c9765c93259572,0x5cd32595734c9865c932,0x4c9855cd325d9734c975,0x659734c9955cd3261973,0x5d532619754c9765d532,0x4c9985d532659754c992,0x61d764c9865d932e5975,0x5d93264d764c9925d932,0x4cb955d932661764c995,0xe55874cb9561932e6176,0x595435d96550d7559543,0x50d755cd435957350d97,0x6597350d955cd435d973,0x5d143e197350f855cd43,0x50f955d143e197450f85,0x6597550d765d543e5974,0xe15436557650f865d543,0x50d97e154365b8550d76,0x5956354d97e194365786,0x58d535d56354d7458d53,0x54d9758d5361d6354d76,0x5917354d87591535d964,0x5cd535d97354d755cd53,0x54d945cd536497354d86],#[0x6197654d865d15365973,0x5d9536497654d875d953,0x54d985d9536517654d93,0x6498654f945d953e4976,0x6195365d8654d9461953,0x54f9761953e518654f92,0x6598754d9461d5364987,0x61d53e518754f9261d53,0x5897654d625cd5358b96,0x54d725899754d6261d53,0x5cd625d573589765c962,0x589955cd626497358976,0x64d7658b955cd6266173,0x61d62e498758b925d962,0x58d655cd6361d6558f93,0x6497358d765cd635d573,0x5cd636557358d945cd63,0x58d765d563e557358f92,0x64d7558d925d56361d75,0x5d5636597558d945d563,0x58f945d563e497558d98,0x6557658d945d96364976,0x5d963e4d7658f925d963,0x58d9261d63e557658f94,0xe498758d9561d6365187,0x61d63e518758f9361d63,0x591935d964e4d7459395,0x5db8359174e0d64e4d76,0x54d7265f8359195e0d64,0x5c99654d725d9535c963,0xe49765c9935d9725d963,0x591735d9645cd7559173],#[0x5cf9559173e15645cd85,0x651765cd925d97361975,0x5d973e49765cd955d973,0x5cf955d973e51765cf93,0x615825cd76609735d582,0x611735d5845cd8660973,0x5cd8661173615845cd76,0x5d9855cf9661173e5584,0x61573651855cd8661573,0x5cd9461973e51855cd96,0xe4d865cf926197365586,0xe0973e55865cf9461973,0x5cd96e0973657825cd76,0x5db855cd96e117365784,0xe197365b855cd92e1573,0x5d196e0d74657835d195,0x611835d9836097664f86,0x60d76651835d98560d76,0x5db9260d76e11835d995,0x60f825db9361176e5183,0xe0d76613835d993e0976,0x3f593e1176657835d994,0xfe7fe7ee7de7be6fe3fe,0xabf6beebdebbeb7eafe9,0xdfedeedded7ecdebfebf,0xcef7ef5eefeeeeedee7e,0xf1feffeffaff6feefdef,0x4df3ff3f73ef3df3bf2f,0xdf65f5ff5df57f55f4ff,0xf7ff7ef7df7cf75f6ff6,0x9ef9df97f95f8ff8ef8d,0x5faffaefadfa7fa5f9ff],#[0xfbf7befbdfbcfbbfb7fb,0xcffcefcdfccfc7fc5fbf,0xffdefddfdcfd7fd5fd4f,0xfeefedfecfe7fe5fe4fd,0x403fdffcff6ff5ff4fef,0xe0f357605a2ba80d859,0x9850b6ec30b4d5d851bb,0x6cc30db961469b30e1af,0x4cb5d925732e8ef98747,0x941cb0ca0d9874a54cba,0xed0403a15c6cc328aae5,0x1768320d3be4b5d5f142,0xb6bb005f5d400874afca,0x9b69c01932e01198700,0x805932c03198601a8bb0,0x5004f1870282c3011be9,0x3a60419d381a565c0c63,0x9ebb034661416a2ea0a3,0x4db68c1d2b2e11057608,0x452daca2817a50a19d28,0x462cf176179ebb0ac661,0x1870bb2ba858ce9462a3,0x86c2861669c2d7b2e170,0x7405d839632e1939760c,0x43cb74a1b6da20d48cb8,0xec3349751965d1080be9,0xd861aa8d10d1269c6672,0x76bb0e12e9869672c34e,0xe92e946ea3443693961c,0xc4a62ec226fa21f17d28,0x444ae1862003d409b861,0x1a32c0ad1163264ca02b],#[0xfd29388e94980b50581,0x78169cb80b4a5a07a52b,0x5ae7b46e13d766f02d31,0xece6a5976c9cbb35d25d,0xfa27252bb3b05689da7a,0x2d2bd0c68de4bb46f13,0x2a965a8e72ed456565a2,0x8ce92ea664da3a79fd15,0x4c68ef863424d399ce5d,0xba53516d31c3b5d8e097,0x14d31d23e58e85b4a724,0xe8a694ec1b4c788f863c,0x9084b4a8131763006d29,0x4e8a07a64403d3a1a265,0x5a649b2b2a401e95180f,0x81d3258be892ecb4a956,0x7d25d53e92eaa6c7a54c,0x940cf4aa94975549cbb2,0x4ea42fa252a4d2a8d265,0x1a35d70c3a699e9555df,0x8d1af31655680b50ba1,0xc38e9d5c4744ae05a85e,0x9706f42b8e3a6580fd12,0x44b89ba15c0fd3ae08e9,0x7a75c45d32e24e8d700f,0x11d3300be8d800b4ec48,0x408e99845f46c237a161,0xd985f46cc3ba06602d33,0x4ece2fa3671bd0b387e9,0x1a5825eb2c14e5d9fc3f,0xb2cabe16e9a0272ed001,0x196e9a0672ed0339a67d],#[0x1fa7744fd39a27e08d14,0x4afd39a57e9dd23f4e69,0x1a38b7fd2bdc0e8dee77,0x2d4458269a2d4aed161,0x60468e317b2d0f397687,0x61277470805a88c04d34,0x4b0aefa3852bd2c4cce9,0xfa78a13d2c50de8629d7,0x2fd14716696457b2b221,0xc016965cb7471e5ba38e,0xa545f472a33a29516d2c,0x472c37a1960fd3ca88e9,0x5a29a0fd3cb08e9a585f,0x70bb5581e97310aed960,0xccee8ea54aed5811a3ac,0x7380f4d9aa796ba57cad,0x2d7e47a5ad25d1d681e9,0x195b203d168a15db414f,0x25d1d793e8abc934b64b,0xf2365678234b8e4ba3b0,0x6840f4f408976a015d2c,0x4ba807a6d306d2cd81e9,0x3a2d703d2f001e97540f,0x3d1718ce8b886745c23,0x36269417134c0207a5e4,0x45aeb4a0ed1a90690d40,0x501971a60cc4d1065669,0xfa51066d2885c694363b,0x38d48cdc65867032a32c,0xf4765872ab4c3555961a,0x8799b2c3d1d861eaabb0,0x4a3f8ba21faad28d9ce9],#[0x5a21288d408e168844e7,0x68d109c26a04ae346257,0x1565d8893f50269da813,0xc82b34440d1962290c31,0x5242f5a8207acc105568,0xfa6241fd411a76608c7f,0x84c31533654a5a32a503,0x58fe94ad3b3054f5872a,0xdb2ef44d91da86bc4d13,0x44dd23a26d60d4b65c68,0x19573acbab9a76a1b9a3,0x4ecc3a505d9d1eb30e2d,0xbdde89dc7f4aeb41a572,0xe8eb7454663a57760cab,0x5148d1a2a45ad4d1d568,0x595a6add15350696953b,0xb8cb19e0654cca74b4cb,0xc55698d2ab2c6871a933,0x8da3f0c6d5576368ecb1,0x4a6f55a53539d31b3365,0xca832855418c4aa0c0e7,0x7b541f3da60f93d50649,0xa76a5093d307e3da940,0x92b03489381a2494f4c2,0x489571a44ab9d1255c68,0xda44b8fd125c76892ee7,0x67d12633689323f48971,0x9d55d94d9f4898cda44c,0x950e7529ecd96538ec32,0x4ca8cd96548ec32a555d,0x5a451abd128d568944e7,0x8fd129476894aaf48a35],#[0xa9ce89563f48a51da452,0x53a13509b71a34dc1d2a,0x52ad15a4564f54a7272a,0x5875984c32cb364d653d,0x38d1aeb364d753b30b2f,0xea766175eb0ebb09865d,0x1693b50bacda35d1ed42,0x4ab581955a67ca2d3365,0x5875b84c32d9de896f07,0x84c32f1c68d793b30b6f,0xb8f6a1793b30bcf5875e,0x15e1348af0ba25784d12,0x48b0f7a2587ad12c42e9,0xfa35c93d0ae3de9161eb,0x4ed12e3de9d72174cb91,0xfa7e91713b48b89fa25c,0xd807b4ec49d97624ecba,0x2ec09d976085d33047e8,0xda7634ecbb18fe9d813f,0x8fd1b08fe89864f42c23,0x20f69192174cc23fa461,0x9953f2cca9d96654ed23,0x4cd09f96684ecb340fe9,0xfa6664fcb3327659987b,0x1ed334a7e59a53b2cd23,0x3c7e8d9c7f44cf27a167,0x9a87b44d4f7a76785cb3,0x48d49da46a4fd1352768,0xd957faababfdc595fd3f,0x66cac0555d602e2cb00c,0xd5691f6ab44fa73a580,0x1ee1744f709a27bb9d34],#[0xed0ccd938685d23dc269,0xd98867ac3c33065a1a82,0xa0bb445ce9a1d9b290e9,0x22766221eb0f10c19688,0x21283490943a284a0d14,0x450b6ba589b9d1c4d0e9,0x7a4857ad242bde8a15eb,0x8fd1c50fe8a2a4f4314f,0x6bde9e2a174d1513a58a,0x638c34b20c1959060cac,0x2b2463a58e61cac73065,0x3a38f31d147986964983,0x4ecaca48e4a518349277,0xba76565c7f4b289f9594,0x6613b4b2e3da5974fcac,0x2b2a9d95958fcacc4765,0xf95994ecacc8fe96553f,0x1fd14b49e86587b4b329,0xb42e9a5a272b2d1fa396,0xa6a3f47343da29a7bd3c,0x49349da49a4fd14d2768,0x576b729d35abd61ad53f,0x91d15c14e96d87f4d6ef,0x42769731eb4b943fa5b8,0x2b13f31554176aa5bcc5,0xd7343a5a9a0d2d4866a,0x576bb29d35cade5ae5eb,0x5abb5e8fe9aed3f2d76f,0xe14e96e8334d7a9d86bd,0x7393b4d9a19a5be1fd2d,0x4b5b57a3ad29d156a769,0x3a7c139d1e09fe83069f],#[0x1fd16050e5afeaf477e5,0x142e5b02274b811fa3c0,0xf08d74b8473a3c23dd0e,0x499ef7a2cf7ad16794e9,0xfa2d14ed168bde933deb,0x5acad727e93453b49a29,0x7ad656bca34b62b595b1,0x6cd6b2b6653a5af5bcad,0x496957a3b029d1581469,0xf95c766cae386697196b,0x39d1e21de8b10e34b8ec,0x29ce8f14f7438a53a7c4,0xf2433459253a7c531d36,0x49a49da4d24ed16933e8,0x3959c60cace426967d3f,0x91d16b1869674c74b38c,0xfe977d3b2bbe3fa5d6,0x7807f4bc09d95e00dd2f,0x4bb89d85dc4fd2f02769,0xfa5d74fcaeb9de8b5c33,0x3bd16c8f6976d3f2bb63,0xc1ce8f60a74fb263a6d9,0xf68c74db47ba1da8fd1e,0x45c69d95e24ecaf094e9,0xfa4e34ed271a7e8b8d3b,0x4ed2f206e9790334bbc9,0xe5e656731b4a6f8da636,0x47f1f4c3d8da61ebcd2c,0x44ab8fa537c7d31b6369,0xba45cc7d22d63e91571f,0x95d130ca68986532ec12,0x4ca659a25748c329a461],#[0x2065748cf2ba26794cb3,0x49137ba289c7d243e3e9,0xba48f95d2454ae8a2af7,0xaed35acae925a532b337,0x6d7696eabb4d735da5b6,0xb0ebaed875fa4adafd15,0x457e81a6c36acb61ca61,0xfa4bfaed25fd7e8afebb,0x41d1614ae93025745815,0x32069719ab2b8d5fa4b0,0xb15034b90d595c86ad2e,0xbbb2995dbbdd2ce20e8,0x5a5e440d2eeb56577653,0x1aa013a00d200640000d,0x390032402d2027a02180,0x5a6054404ea047803fc0,0x7b4076c06e6069006000,0x94208fc08ae085808000,0xb2c0ace0a6a09fe09a80,0xd1a0cdc0c7c0bf00b820,0xf000e900e3a0dc00d580,0xe21080102c0fc20f660,0x2e0128e122611d411641,0x4dc147e141c13a0134c1,0x69e164615f4159615321,0x87a181417a2174016ec1,0xa0c19ba1964190e18b61,0xbc21b661b1c1ad41a781,0xd981d4e1cfc1c961c241,0xf741f1a1ebe1e7c1e261,0x11c20c82088205c20021,0x268222c21e621a821682],#[0x4b2243a23cc235222f62,0x6be264625d2257425142,0x8f828742800278627382,0xb442acc2a5429e6295a2,0xd542d022c742c042bb42,0xf762f122eac2e482de22,0x174311230aa303a2fd82,0x34c32fe329c323c31d83,0x54c34fc34ac345633c43,0x74636ee3676360835b03,0x9503904389c383637b23,0xb583afa3a663a1a39c83,0xd9a3cfe3c983c283bc43,0xfc83f7c3f0c3eb03e143,0x190411240c6408840323,0x382433842e8428a420e4,0x598453044ba445c43fa4,0x76846f64690463445e44,0x97a492e48a2484647c04,0xb364aec4a5c4a1249c84,0xd1c4cbc4c644bfe4bb84,0xf244ea04e284dca4d704,0xec5094504a4fe24f804,0x300527a52245184512e5,0x4a6544a53ea539a53385,0x664561655a2556655185,0x84e57fe5788571856ba5,0x9e2598e593858dc58905,0xbd25b725b125ac05a445,0xe145d7c5cfc5c945c345,0x305faa5f485ed85e825,0x25661e2617c611060886],#[0x4606402639e634062e26,0x64c65ee657e651e64bc6,0x83067ba675c66fe66aa6,0xa2669a6695a690a68946,0xc326bca6b766b1a6aa46,0xe226db66d566d006c9e6,0x72700e6f7e6ef46e7e6,0x25271f47184712a70ca7,0x44a73f0737a732072c47,0x66475f475967500749e7,0x884781e77b6773c76c47,0xaa27a3079b4794878d87,0xcb47c387bd27b4c7af87,0xf0e7e9a7e167d8e7d1c7,0x15e80ce80507fda7f6e7,0x36c831e82c0823881be8,0x5a6853684b8844683de8,0x7d4876286f6868c860c8,0x9c6895088f4888e88388,0xbc28b6e8b188aa68a328,0xe008d928d208cb08c3e8,0x108fac8f3a8ece8e6c8,0x25691d8915090da90769,0x45493e09362931692a29,0x6589606957a951894b69,0x85c97ea97a2972096b89,0xa809a0a99b0996898de9,0xca29c3e9bde9b709ae49,0xef49e8a9e189d869d2e9,0x128a0b2a0349fc89f589,0x394a30ca29aa224a1a4a,0x5a4a54ea4eea486a416a],#[0x79aa71ca6a2a63ea5f0a,0x9f2a992a90aa880a7f8a,0xbf4ab8eab20aac8aa56a,0xe34adc0ad52acc8ac64a,0x5cb010afa2af1eaea4a,0x200b1a2b14eb0f8b0bab,0x3aeb354b304b2a8b258b,0x5c4b55eb4e4b490b408b,0x7d4b76ab70ab698b610b,0x9feb968b904b8b8b836b,0xc16bbb6bb50bb0eba82b,0xe3cbdcabd72bd00bc92b,0x1abfdcbf8cbf2cbeb4b,0x1f2c19cc13ec0fec0acc,0x3eec37ec30ac2aec262c,0x5fcc58ec50cc48ec436c,0x816c7aec74ac6e8c670c,0xa1cc9bac95ec8eac886c,0xc44cbeccb62cb00ca72c,0xe50cdf0cd7cccf6cc96c,0xdcd052cfdacf58ced2c,0x292d23ed1dcd192d148d,0x478d424d3b6d34ad2e0d,0x658d5eed5a2d51ad4bcd,0x82ed7d2d780d702d6c0d,0xa26d9a6d930d8f6d888d,0xc5edbf0db7adb1cdaa2d,0xe3cddf2dd7add24dcced,0xfd4df52df14ded4de7cd,0x186e130e0cee094e054d,0x39ee342e2b6e262e1f6e,0x59ee530e4d4e458e400e],#[0x7ace756e6f6e688e624e,0x9fee99ce91ae898e82ee,0xc18eb96eb32ead8ea78e,0xe4aedcced62ecf8ec98e,0x76effeefa0ef2eeebce,0x2caf268f1def16cf0faf,0x4c4f478f430f3aaf324f,0x6ccf686f628f59ef53cf,0x894f828f7bef766f708f,0xad0fa34f9daf98af90af,0xce0fc66fc10fb9efb44f,0xefcfeaafe42fdd8fd58f,0xf100af004effdaff74f,0x2f10299023901f5016d0,0x51304ad045703e7037b0,0x71d06bb065f05cd05750,0x9190899085f07f907910,0xb410aef0a990a1f09a50,0xd5d0ced0c8f0c390bcb0,0xf250ec10e7d0e1d0dc10,0xc9106b100f0fcf0f890,0x2cf1271121311a9112b1,0x3b313a31393138313231,0x40313f313e313d313c31,0x45314431433142314131,0x4a314931483147314631,0x4f314e314d314c314b31,0x54315331523151315031,0x59315831573156315531,0x5e315d315c315b315a31,0x63316231613160315f31,0x68316731663165316431],#[0x6d316c316b316a316931,0x4781f01170316f316e31,0x12d0e0ab81c19711c22c,0x433617440208240cdc2a,0x1e101a612c100700cf88,0xf44d89807fa174358707,0x1da10051619c3036c200,0xe0d821e1783035080108,0xda2086cc9e8304fc170c,0x240c01f3089260e50982,0x28012c1b03610d885122,0x98682302424f0c49b08a,0xc03a83044dc3f0708c06,0x190594200ec0d5300ae4,0x52646ccc03c030055069,0x2c460ef8205e0c888312,0xa58c03108f84c10a1808,0x86c2070202e0aa90b060,0x18b09b86c1221592183e,0x202921e09a1151f46e15,0x23e198ae072400b82602,0x25d8998609702d4d8102,0x406c1442883ccb18f04c,0x9918c064528889943b84,0x28440a442204902f21a8,0x50e04c08c11a30a5c4d4,0xec3c9505224a47c240aa,0x528cf04708c0c8ec9132,0x60a860a24558a09221b8,0x94455a40a0a8b13ea14,0x293224281b0b87ca5944,0xe1388ba48f0e42c5fc9],#[0x948311c44a43ccdc176,0x64bd0f534a524d494507,0x2c961528a0c0c2932240,0x8432110f4208b835854c,0xb2021f8680543889ac15,0x449091292a29c51c1f11,0x3c07c4184207c4f43595,0x2804f28741e8313e40f0,0x994e204145f053122458,0x531123d148c385a668c3,0x72368a91ac902188f08,0x3b24008712c20e4ab1b0,0xd1617333c89002205faa,0xb38500111dec5fce3400,0x727c20b385001104fd26,0x4fc2400cfcfef0da8008,0x442002237cfe39008f9e,0x8bfef96f26006847b6d8,0xd00694b7f508f842401a,0x3f4ecdc00cedfd372e0c,0xe06602427e5c19b801a1,0xc8df4c86e318008b0bf9,0xd8c00455632e1d006737,0x1c7c634a11b5e6ecd226,0x70fe20c900671f8d0801,0xe3f8770033673e0c9006,0x7b018648010fbc456011,0xb6120043d3bb84800861,0x43f3ec2d848010e6ff46,0xaa3e120021b5c5dc2400,0x24008a8648f0d0480111,0x7f54c019c18ecd5b76e8],#[0x839e6604c73ccc09abb2,0xc32400896ffcb0118006,0x87876d648010c88210ee,0xf940008737fff68d2000,0xd08fc741200430bcc0,0x674e1200218bfcb0f1d4,0xd09001144f2fa0140087,0xe8040c8002209f171449,0xa920043cf0206301205f,0x880e1f6e00334bf865,0xb6ae120021b5f7221c28,0x21b3fe7e0bc585006a,0xf38b0f0900340bfe1805,0x39f8ad00939c6f848019,0xc8019b0b87c3100342ef,0x40242f5fd56402447f62,0x68cf6fcb8019a7f165,0x78c06500111dd7f46a2,0x1808a8ff0a0c20021cdf,0xc740242f3ed85c024cf3,0x90091a23f8f201234675,0x7c8e30f6fd801a0675c7,0xc67f3a011b3e93e56006,0xdf2fc710033ce3f92011,0xd89801a403e52e2400d0,0xd1ff51084004397c3ebd,0xa0c6bb003377f8a08019,0x33819ffd80463908008,0x43059f980a1381fb10,0x2c3afb93800d16fa89d4,0xd10feda2564084a002,0xd3c6028b780943cf8d98],#[0x706200214abf28200673,0x329cfc602739f46028b,0x658008a1fda01153f690,0x57aa6a024bbf6410742b,0x223593fea77c1001103c,0xe91001128c1c78e4200,0xa11edb3150010e0b7086,0xbede20021abfd5db3001,0x44bbc9f72b5b001100e,0x605400442bf6f86a19c0,0x4443f3080085a7ff6f8,0x79080088f62cbfbadc40,0xbe5e102e20022410f871,0x114aeafedd8008627f,0x70400445bf17dbe19c4b,0xfcfdbb414801a59d9cdb,0x1a73fa87dbe4c801a73,0xbf8e88019a3b7ae99488,0x20022ab2fe58114801a4,0xca6400cd4ffc92ec4b10,0x6ffdc8e9089020022abf,0x8cc006700e3ff19800d1,0xf59fcbab7001a1bfcff,0x7e59800439bd9d104001,0x1106f77cd200087377,0xfdd2810010f2fb09d841,0x8019c3e3f956400cfef,0xe5f88920800872fffe8d,0x4d08019fdfa40820021,0xce002247ef790023f7ff,0x76f3001401b3de4fb498,0x124bd6c1a0033e78ffa2],#[0x21e2fdccf40a45777760,0xfa59ee004877f4016000,0x8003503f9304a0000889,0x7af938003387cfeebc9e,0x4c00d738fe9cc6da025f,0xbf6c8004387fb513b6c5,0x1219d1fcc3c0021c569,0x1bd5483e6000894378ce,0xfaf58008fbfe66a00470,0xe6ff6c82d00210c00458,0xcb26000684ff1974000c,0x88e7de6b640021d3f7f,0x47d900087043d7e45540,0xbe797d4cd4830036d397,0x309f83fbcb08381119fe,0x8614d07f8348a4048002,0xe8c202502231fcb8a400,0x21c00691f91d4011c1d1,0x45d5198d080921e34c8,0x1123f23e0023af57c,0x5b600008907cdd7f5ac,0xffc29ec318104423ff71,0x77740486fd9bddc00d08,0x19a80511bf9ac00471f7,0x1bf9746a000d1cffec7b,0x9c838113dda58d4001a,0x70f3c8b0ec0069a6c57d,0x1a578d0801216bd99c04,0xc8e700008787f9880002,0x67cfef5c60e0003543f,0x90aa0350008aef5dbc00,0xd695f8f3300345bf5f],#[0xeec02407fc3edc1521dc,0x8a100476fd12a00cc2bb,0x30040022d7f122008f3f,0x5afe244011f9fec875e0,0xd4047efe194f6c413003,0x1253c3f064d00346a89,0x81f57c2000219743ee13,0xd7d3a000674ffce00019,0x78008987fae100010dd,0xa9530218008a97fbfb56,0x67eff94e80019e5ffc,0xcffa64c000d19ffd3260,0xf0a27501223c33400cdd,0x7fe1a6a02467ce801967,0x3fe5ff917035b01801b4,0xb14400115579cb600295,0xa00684c70064f33fea33,0x14d3f858a808edfce058,0x3f94d70010d2705ccc00,0xc00488f0e9fd1060034e,0x329001105f1a8144f8d2,0x122798f3a023cbfe421,0x8efa72aa000d13e723c8,0x642404b0757c26131c08,0x23599fac38148ff7fe60,0x21a7f4a500485ecce0,0x43327f6680067e737578,0x9e9ae0c0010fe161f000,0x86cfdb863d03a001aa,0xd09d0ec7e200d1086d2c,0x4fb7d000ce1e063fa200,0x6801a23f9fd9a0019fbf],#[0xe9242db9801afbffa832,0xf0cff97aa2b5801b03f0,0xceafd5659e00021f30,0xec76e1926006a2ffa248,0x10001531f6e192600682,0xdbee790067abe0d42413,0x87ee1d0bc4200c5006c0,0xb75d0021c5fe1e0e2800,0x553f9b55bae801108bba,0xceeff187c792584004,0x87fc0eb200670ff89da4,0xbda400cfca306a920043,0x8019e3b7af7200678edc,0x27a7b7608033953d3fcc,0xca00436bc35c8a9a0044,0xcfae6f54b0021b5cdea,0xe3a7b7608033b7ccf280,0xf30480113ae2ee120021,0xa51eaede240087878191,0x84a00cc987fe81e3a801,0xd9a0044ceb181808e5c3,0x29b11840044839fda20c,0xeff17e49c2002221fe5,0xe4fc0f014aff7f035009,0x2400d0597b7818400d27,0x5f195f8b4024c7d7f11e,0xdf165402529a2f8e8049,0xce2bf19e7d240256f9,0x9c12f7040044d7fe8d44,0x43fe1184998420022bde,0x2523fa7f028d82840045,0x38f4a900923e058dfa40],#[0xfe500901f54db8c00d03,0xa3cf23001640029f7e4e,0xc665001115dba4f8801,0x8048dd78fd6a0120df82,0x8f0c23ed400d2bde3f18,0xfc400cf11cd7e200688f,0x8b8fb6ffc40033c463,0x40043eb076a714e429bc,0xbfc36bf5a801a59c85be,0x5c2002227f98c56a0124,0x70f2082002255eefea2,0x43abd7d17440043f3f,0x888e3dc8019cdfca4b84,0xf6a00682783475c88008,0xb2fe5c288801abbac2df,0xce57e26d382000a7ee,0x22a231fe200672cba7c4,0x98010f2f4dd8f9f98200,0x46023a4a000a8160eb44,0x2239cdcf77b0021e6e,0x304544004480df0f1dc2,0x373ddad94004503ff07b,0x43f071cb44d1600d56c9,0x327960004403af2b4400,0x89f63293934280113e96,0x440045d3ff4f29172800,0xf9c10033f3460e32544a,0xa37c1e893984004407df,0x86e2bfb8f02b608008,0x2217fbe14023e3ff6428,0xeef60043f3f7640c4200,0x801bf9f638400445b679],#[0x600440bff76ad9088008,0xf0f2a1000536bd7361e7,0x21d1f0f601dcc2002262,0xf2ee100345bf83044600,0x1f5f9335501001101dbf,0x65f120067679a2f02002,0x8801a19279bcc4004393,0x78576f8322006ace7d2a,0x10011311fff05510034f,0x94121910034f3f63cbdc,0x390033972e1a200678ff,0xf78576f83c4400d71197,0x2000a7afc75f69610034,0xc585902000a753f8a344,0x68b7f02fc4100110b7,0x2fc1220021e3c7f9d132,0x1115fccbf099003463,0x1c59220021fdfbaeb9d1,0x4004387c7efbb20068c5,0xfe276412001108fc0b24,0x89be30116c804000a9f7,0x2003319e0f980304000a,0x347e5e39b7c800d29edf,0x64a1812001129edf2003,0xa09d3fd2d010008837fe,0x2de82003467f1560d001,0x800d6bfda4719004a2fd,0x47d802417fc7ffb01b80,0x87affcdc0400689f6,0xf35a6200008937f885a8,0x14f925fc008e4fc3,0xe1f244f4001a80f3637d],#[0x62ffa4976b00004557f9,0xc395700067d9f0a00471,0x87b41ff4540200111d,0x5b44ec1001af5e4e9010,0x57fd3d3b040068ad7ffc,0x5a200053365e07b20034,0xaa49f987ae20011717c8,0x800454178f6a00339b,0x2306000a787966ff9097,0x1c1e52f60b0011127f0b,0x24b600088f41cdf78002,0x275e1ee9a600088e7a7b,0xc001108668fdc0b6c002,0x9c804000089e59a3f82b,0x5ffa1d8f580002271fac,0x11069393e4f4000220,0x3731800022a9fc5c28a0,0xf42b73180002261ebfcd,0x43b3fe31eb0000442bf,0xfb3940004333ff89e800,0xfac0019a021cb80033b3,0x7b32003441797000668a,0x79ffb6d9802001131fa7,0xc00ce8f9f6c8cd860022,0xf83b966a000892b7f2f8,0xfe0ddbc60500008a37c9,0x91ee6cdf3865a0001144,0x7c6a000d13fe7adf800,0x480fdbe06fe0003487c,0xbfc7d2fc004a9afc5ae0,0x9001a035e1e9d8003400,0xbe42d1000298bff2f03d],#[0xe5f6af8570efe4006b8,0x4a90008857feb9072001,0x9cdc9b404002205f0792,0x3527edfc546c9001ab,0xa4e3810e5fff8a6c9182,0x1a100fa400855783fc,0x500498c5600cb1e9c64a,0xd13d4cd28024aac647,0x68f8db2400678fec3648,0xeff240000a58fac30006,0xfadf00019c3c57c00198,0x3000089ef06fe0003387,0x3ad3f00066f7ff86a44d,0x53378d427e94c001a9,0x89864e0002160ff09200,0xa7b7ff0523d821220,0xfeb4abc00d177f78a704,0x7801a0b4ffe306800d1d,0x9c27f8c1a0035e7c1b95,0xa68001a2183900085296,0x4f478ad4500008b6ff46,0x6f279bc8ca800044809e,0x2363ffa9c26446000114,0x417f68057000680b8f00,0x909800044a7c503b0003,0xef6dc1774000d4afc9e0,0x10cafc9ea93000088,0x23fed0044e000d20f839,0x9001a9de0f17921c7022,0xf93767001a23fe9406a5,0x4bd5f0117df8b500217b,0x1249c9f87f16a8620011],#[0x3425e780236ede6940,0x11ef16240021a3f9a392,0x3cf4008ece3dbcc40001,0xc8000d2bfe4f3d00244f,0xf75f2770003577ef997e,0xaf4f00033adc750023e7,0x1a9dd583f0f0080044f7,0x4c0043b69fc7f8774100,0x9764c611001a95ffd0ab,0x688d3ff20d844006a0f,0xbfc8bc800d1df4f31e40,0x43cbfdf5b400043c6,0x7d09600005373fc9eca0,0x3399f5ba04000014ee,0x83e7edec800cf1d7d218,0x30d000115efa5a60021,0x51d75fa0006867b3c44f,0x19d9fafdc1a15a000114,0x3e5ffbe4011e8bf21c00,0x2d4080045739bdc08004,0xf985ea04002239ff237a,0x9a006a460fb9d80087d7,0x34022001149ffd1bcf81,0x597430004006b97f88d0,0x14df5f249464800d4dfe,0xc821c5fff44410202001,0xb18f340066f2bffae56,0x87c5edcac01a01f53801,0x4f4e5600cd81ad738033,0x4000110cff2e44000087,0x3d3a57e480034f28e987,0xb23f00065a87c680019e],#[0xe14c000d6afd82cd0021,0x342ffb34008e987e09c3,0xb3d80087efd25f2e200,0x14001509df400658747,0xc7ef9f540290bfe432d,0xfa5fc1002473f2410001,0xee01353fd1a23000088d,0x449bffb282500008833,0x20c0044abff660211800,0xdbd848300113af2d1c91,0xd3de98d98001a35e5,0x79f34a004a6ffef4c6cc,0x4337ff7965b000340ffa,0x3c509e801269fd38000,0xa6008eef97fa04a63811,0xcce800294ef61c09c7eb,0x12bd5f0114ef61c09d6f,0xe002271ffe3518c42001,0x9a7e9c0118dffc005014,0x862f90709200341d3e40,0xfcc23700043d3f0a1000,0xcf2f8fa6c0c00444bf,0x7ff1a4d888035c714ae2,0x436bfd8230010ddf7a,0x997c9460008657fe6b32,0x58019d1da183e6418008,0x5ba5d8f0600088cf1fa8,0x21c5e5c948c92700045,0x61e1fe80068b74fb5780,0x30033843f8603003457c,0xff76af101800224bef87,0x894f0fa16f8803413],#[0x880c001128ffb1dacd72,0xb7fe137c4019e5fe2f47,0x100688fff6f4e8740034,0xd15e16fd100670fa16fd,0xe31900044c71da36e200,0x933026320008907fdf8e,0x80068ef71fcc1006887f,0x1fcfecd000d098fa7dbe,0xd519fc8b1af81001ad3,0xe180029e3f9c4019340,0x53ec6619d00153f1fc2c,0xce800044037f24f00067,0x83f0c448200448bfff6c,0x1a4aff915b0c0014fee8,0x68020045477fe805c100,0xffd98040086f777bb962,0x6a0c8227df8b008010c0,0x119cce001142ffa6ae39,0x9c047885570066b7ddf7,0xd2d8fffeac1001a56bd9,0xa8080044ebf354040021,0x3f27010008677fca6fdc,0x67833c011870678023c,0xa7ff582003327fdeb040,0xa00008867f9722000043,0xe56e03d38001ab947aab,0xcd2ffda5f8c60001131,0x2c38e063e00ce5e47e00,0x6a67fe11faab218c0002,0xff4c01222c1f80fc6000,0x66d7e120b8ac00446fb9,0xd89d980004417e9df400],#[0xaf6bf73d1418008967ff,0x60069f6bf2bf7a418008,0xff513290010fdfe00582,0xab40002223f9cfc00cc8,0x40fc726448821f1fff62,0x5f0033f75ffd80c5c00d,0x2400695ecce02327feb3,0x314e0022a3ffcb0fe0,0x400679333c011fdafabe,0x8a6ffe30400664fc3e30,0x1108f9b245abaa8800,0xc202010005393fd0c101,0x94801a0bf94110033c5f,0x182f370140014c5fea57,0x3900900022a5f2518002,0xe2ff91a0004363fc7e6a,0xc430401a93fe3e9a200c,0x89bfd2190000a6cec9e5,0x833a781327a7d6ac1006,0x8abbc40395400000a,0xb0d0022198bf8813c328,0xfff2a5f000349bfe1ae2,0xf000334bc21340086ae3,0xfffea91c470000894ffa,0x66c7febc3290010fe,0x2213fa7aa80033d7ff1c,0x3f96002189805fd98e00,0x8019f1cbd912208667f8,0xa61c66701183ffe3ab,0xba394f400299ae8e53d0,0x33d7e20032affe900466,0x8ff95e800cf9fd657a00],#[0x20001504c16f1c00087c,0x24ed3400088014ff2ec3,0xd57886374759aac70d4e,0xb14ccffe860c429ba3ac,0x1a66d0d72]]
set_option maxRecDepth 32000 in
def g255H10 := limbs80 #[#[0x6000416143891a0c404,0x840102081000c3400d0,0x3090c54084000070302,0x308945070000004000,0x8704002820c342160010,0x302100890200082021c1,0xe1c3800200080040c18,0x1000003020c007,0x1800e14106020e0c1810,0x818400005000404a860a,0x7140d5810c58900020,0x800000c980a081480800,0xd06303871a1008006485,0x16ac30414282811a0081,0x21898112006a14004083,0x8383061000400003960,0x82052218000001014702,0x11c4c044022625301306,0x300002b96c001832208,0xf12a4901060800010700,0x3e800005f8d1c0028,0x102b4491168,0x33d0001c510003470000,0x40000020002536000000,0x2b02b31ea82d1e80a525,0xd591700000008680004f,0x1c000125b89565f00033,0x13790b8a0800352c0004,0x12b68000000910000000,0x3056085912e11e82cd24,0x56594ea000a40000,0x1983812000357623800],#[0x44f400099543180,0x56588b86b01715180,0x497000000280c0000ac8,0xa990001d92000000113d,0xf54400000000018172d4,0x64ac000000548f26d14,0xf7c4ec93252c00000000,0x169586191400023a31,0x10ad00000003a42490,0x1264a54510000a2608a0,0x40000e42f0000084550d,0xcc47a10192bcaa000062,0x17263402ca358e922222,0xcb44a00003c6000011d7,0xae600087ca2c73920,0xa1a00000034224880000,0x809296007c0000003819,0x963110e2d0000289921,0x1800000089c842000000,0x1a84eb1800098a12890,0x3cf0cf44f43502b87e00,0x8089920002900000000d,0x922d8dcc2eab60a7e0f3,0x40e19a93910a2533cf1,0xf0004928000000c29800,0xf5b2a05d000041ea2a42,0xe84d080003ac0004a705,0x755230000000240f2dc1,0xc1e80012640000000,0x80031819cc2ad1270000,0x129e00057da49c000691,0x7e3bf3b286a1558a8c00],#[0x10e0c46f8c943800054,0x9024cc0f4a58000407c0,0xd604200008bb8e34360,0x304ec26805e293,0xeb47ac33b9df28a,0xc4d56a70000000d23800,0xe400112f00021480015d,0x85ea4a7de4f600000070,0x6bd3b400000022c80009,0xcadce47071273cea8621,0x136ea7d2c3,0x4c0000000000488,0xf25804a140fc3602a800,0x83400c0984d306a83f0d,0x1500034a709200426663,0xbb5849000612a9fecb1c,0x8b2855837a251030a5a8,0x1472000c53000000117f,0x900049ea3500000bb800,0x3fa00093a000000149,0xb44a406232fc00006380,0x2423d98c31,0x80a0102650a1816f55a0,0x24d0000d2f689a4cc,0x10830005854378929000,0x3257f1bedf942a09f800,0x3c0008dc80023080008b,0x4600020d0a35ab964f38,0x1072d0365e4000070c,0xf20000828000,0x67a6185a19,0xe00028794b88d0000000],#[0x21200000019ec80,0xee01b800000101b00000,0x1a83d4d00030c80,0x20de60474400142e11e0,0x2618002560,0xe0000000002c0d5ac000,0x200012d000008fc8c2b1,0x5680002570491216c8,0x40c397600000000000,0x96400049c573c33a0000,0x199000000088b0241,0x1f100021f99734f3,0xd00023780019b6432800,0xb93052a14e726b74bbc6,0x21000261f82727c15541,0x774000000ca18002380e,0x85180ec7e5c861ed0002,0xd174b55980000000109a,0x209e34469c3700db51f,0xd73240004cd547000000,0x1ddf84ce7817447176d2,0x254e52e45710245c32,0xe822d80014f20,0x4d12787a50000089472c,0xc000000000628b320000,0x4b1000036e0000002a9,0xe987c00049280004ae00,0x42b45,0xcd8bd893d1a6223c120,0xa6f263613305f135a25c,0x15380000000d8c0241a2,0x51678a8d3334c40004cc],#[0xc53b11c6231c62800192,0x5628c000047,0x3864000142e1180,0x2039f32d3e9800000000,0x47355e085a074ac88000,0x39e000c7b8000001218,0x6728201005000000,0x164707a671608a00,0x8b000062ea0399e00000,0x62897820f95300024762,0x7e0000000d9cc1db,0x800055f1ec00055851c4,0x200000066d42f0000c44,0x73214f050e00005d524,0xeaddd000698c00053900,0xa29c1d00000,0x8c6000000613c001a900,0x3083166154c52c4fd,0x4d18000000000,0x54c555518d3453000000,0xdd14290f8bde08a47047,0x454090830202167471,0x56f0f600000044269140,0x4fd0001102c010004,0x52b00000002b48003386,0x83b88210de95e000,0x8c07106888a000300c00,0x8b8814614000110215,0xef851f341a228fd81fc0,0x4a94f9473c3512d3e082,0xa5ea03fa97a15401d0a5,0x800100cc4313280009b2],#[0x4d4c68cd1fb09607d44f,0x17f44857,0x19cf17448680,0x190800000011f40000,0x4a206ac37594a02c8,0x293045f25f8994c3c,0x75f4e150a4c3b7aa54ad,0x2e01fb4d2a0520e67d1a,0x112700061f746c00020,0xe980022a1108954c3c40,0x209c4230,0x2ed80000000000000000,0x4b3a528dfe95726d897,0x350f1b0956000,0xe323c08781cc6a5b5a00,0xd70003380000d3555a94,0x83a34a000629000349e0,0x91acf90003bd0000c39e,0x9d7c89000082d9eb,0x64b8001cb3000,0x630c3a9593000000000,0xd41cd89122b808200000,0x18ff4154af93380031,0xc5d85140009640,0x5d291816e00013ea490,0x342f971000000000095d,0x5203800000000046aa18,0xd515e98388ec36b00091,0x93a55c9a42a4a1400047,0xa1a0b68ddab164e88121,0x8c1951444d43798e400a,0x3cae14dd5229fc173],#[0x1aad0f38001997878000,0x2a4ec1d2cb8000265800,0xe01ef274c55c0aa202c1,0x3b66361939c7c66a3671,0x11c0e575773709b36628,0x24a00000000000000710,0x6bb0003ab109a,0xa0000000524000000000,0xb2214000000000000123,0x1d000000000000006926,0x7700019d80a616ac001a,0x67c2594f74e05cdc8ca,0xa4401b40c6100,0xc8cc80f209b4dc000c16,0xbe3181c288227769b23f,0x660008330000001604a6,0x57e70800000000000015,0x9ad806c1680004d6930f,0x246e0fe0088003,0x5028ff0f58000000000,0x2fba525984b6800,0x441535040c8e81725800,0xe2076800000000050810,0xaa001a00000000000011,0x8ab9156431247c4f0004,0x811355d8bca620001895,0x29da09000295d9fccb5,0xf010e3ede07276800000,0x6489d02d046fb67414d1,0x3b8a011b855e0be217b4,0x84e59ab24514132ea019,0xe2a675f4d48f3263e618],#[0xc4e621f27801a72abd75,0x41268a5307d9af40d477,0x5c0c5949c4ca1c502101,0xb312f833f3ff019836b6,0x5dd13e97305a96224961,0x28dcf012e80010c80003,0x671989ba0c00007bb158,0x11e4000000,0x29869a60002b525c800,0xcd5000000000000000,0xf2000000000000000000,0x1b0000ccda9da2d802ec,0x216345e016401228c,0x117b4c2cd23216810000,0x9bb3e00001e623a47c,0xac4411a6458000319400,0xe3993611d800092d88,0x62426000000000120c0,0x3200000012841bb0006,0x73dc4e21400006630001,0xe1d028035c1de000]]
set_option maxRecDepth 32000 in
def g255D11 := limbs80 #[#[0x5953258d325893254932,0x5d9325d5325cd325c932,0x5514361d326193261532,0x5d1435cd435954359143,0x61943615435d9435d543,0x5915358d53e1943e1543,0x619535d9535d1535cd53,0x5cd625c96254d6261d53,0x5cd635956361d625d962,0x61d635d9635d5635d163,0x54d72e0d645d9645d164,0x5d573591735d97258d72,0x6157361173609735d973,0xe1573e1173e097361973,0x60976e1974e0d74e1973,0xe0d76e09766117660d76,0xddf7bdf6febfcffe1176,0xffdf7bdf77ebfcff7fef,0xeffdefbbf57e7fcef9be,0x7fbfeffd7f7feefdbf97,0x594b39763dffffdff7fe,0xc06d6300d5d91c175314,0xed7302b61c02d8601b5c,0x9702b61c0d97602b6140,0x925d822d8509b58c215,0x55d81298505559412d86,0x142c5750a465c1298705,0x193960aa6182c5760aa6,0xd870e8618381980c0660,0x7120e54483980e066039,0xf5d8f8396140e545039,0x5d96039342be490db924],#[0x872b851d15d474b925af,0x2785189e185ab861d15d,0x861e3e547a7851e3e546,0x280658a0396243e587a7,0x65ca81952a0e5498197,0x5cb29872d55d8b61752c,0xd139630a618c45763046,0x398340660d1d87348618,0x6380e48e0397360e48d8,0x715d51d565464e491839,0x61d2bd764a861d113954,0xd383924e2e55357934c7,0x9d766a0655a83954eae4,0x966c0655b3d765c0659a,0x6e75d9b81926e7e19781,0x4e4da0795611e4d80196,0x5552574540655c019270,0xc8f9350065d521765406,0x1937c064dd0196720655,0x3805e49e81957e0649f8,0x5d5942757503d5d80019,0x6582f1950bc5942f1750,0xc1b1870775d81e57507c,0x31860d35d8375920c665,0x920ec5d8431980c6e583,0x3cc66039b950fc64c3f5,0xc61cedd763bc5ccef553,0x54fcd753fd648f99973a,0x5f16357764d031983e6e,0xd935b7595619965735d9,0x51fc658771951dc59474,0xace1c6dd761b95d46e96],#[0xe58833862135d8819971,0x89b9522c5d8a3298206,0x716431c648c71742cca6,0x762fa5d0bf19631c650c,0x32c618c9b972ec61cbdd,0x6e50d7193346e48d1b96,0x50db39236c648db19834,0xe339736c65cdb39436c6,0x39438c650e339238c648,0x447c6491b39638c658e3,0xa6e5525d6549c6551f19,0x65929b944bc64d29b924,0x135f924d7649331984b7,0xdf954d765535f944d765,0x944ec6513b3924ec6493,0x6335d58b3954ec6553b3,0x35d5731866335d98b185,0xd591b985c6e55733855d,0x94d76646e55931856535,0xd7667361979b9664c619,0x261364981b9666c6199c,0x1365584f9461365184f9,0xe55a7393686e49a4f956,0xdf3183777e4d4dd93526,0x1b9278c64df19937cc60,0x8578c615e338478c611e,0x7e6655fb1847e6e55e33,0x664e01b937ac655fb194,0x58879953fe6543f9960c,0xd7b9235e648d799523e6,0x9944be6492fb9435e650,0x467e6519f99267e61577],#[0x9e649a7b9667e6599fb9,0x655a7b9469e651a7b926,0x1e7b9279e649e7b9569e,0x798579ee51e799479e61,0x2d805e0007b9579e655e,0x25a07d819605181080,0x847e10783c60dc03200b,0x64217e05b815b8520133,0xf61eb07581c306c01a30,0xc260891c23688a021787,0x2df0b302be0aa229589e,0x5b8d103310c6c3048bb4,0xb0eec3aa0e5e3868dc63,0x107640d8ff23ec0f683c,0x28848311d045e910242f,0x4250113c44db132e4b79,0xa58295a255514ec52c94,0x60c18085e697505b6166,0x7c19aa65298ee6301884,0x51b8a6cb9ae469e1a306,0x1dda75b1cfe7259c346f,0xf8e7d11efa7ab9e74788,0xae853a0d281fa0167f79,0x48da23128ae225e88221,0x9662542935a47290423c,0xea27569c0a69e994a5f8,0xf299aa4ba8cea19a80a9,0x2bf0ae42b1caa9aa52a7,0xe3cb74ad72b402ca4b16,0x90c0cafdabdeaf1cbaa2,0x8c9e3222c6cb144c39b0,0xd28b45ecfa33a4cd5b2e],#[0xa3b64ad793594d5234e8,0x5b846e0337aadda36fad,0xba70e803984e48b8d8e2,0xce4f1a3c14eeabb28eb2,0x4afbe3e76f893daef4eb,0xd047c0cb01bc016fedbf,0xdb42f70aac253078c17,0x63c535136c46510643b9,0x447131b9466f19045f11,0xc961242c8b1213c7df1e,0xb672c04ac129b4a1926c,0xa9354cce131dcc132f04,0x93eacf513b94e893854d,0x489d1a3454d101423501,0x28d4414f6535b4c2d293,0x8d68f58e55c1559d50d5,0x58d761dd8075e557315b,0xaed6a4da4d67e599f651,0x9b745dc9970adbd16d75,0x57f3df597bdde777835d,0x896e1d785e60ff82c604,0x2de4478fc637f8c9e2b5,0xd66df99b65ed961650d9,0x1c2e11c0f019ff679f9c,0x1096061f432157100cb1,0x143b0e21d10c330a0c04,0x1c302508017430684dc1,0xa892300d1270c1300a85,0x68807e1d86741f0942c1,0x1c02e12a320a0850d83,0x68681b880828db060e82,0xa1ce0e0280dc38222011],#[0xe4b921832268407a1b61,0xe09f068a8a0279328888,0xb888a62460a4942908c1,0xc4d3261aa164390d8905,0x94812309a28038381808,0x81140611874229550ae2,0x6e50a503853498421384,0x5c112c501284a91a1789,0xa07c400f85c020561660,0x2cc04d6511018c16c843,0x8d22f24064479522698,0x25db800676f29e2c400d,0x3f39404fa3d79180486d,0x58f08300682f9e530066,0x4c01a0bad831d300682e,0xc9cadcb2400d11cba53e,0x5feea790091dc3d3a00c,0xa7b1a0068af4e9810067,0xe9e00666f9e530066efc,0x97e00659ee3b900901e1,0x37fa8c008d977c008c9f,0xc005259e0135f73f400a,0x1400907d9cf20145f7b3,0x8200683ffbd00142ff56,0xc00c83eb800464976ff0,0x5f931003437e400195bf,0x346782f9580001a429e,0xa3f2e000664ffe978870,0xcddfc00c95fa7b40019,0x344e70022b7d5a00,0x33a425f848019c2bfbb,0xce9cfc000332439fb10],#[0x4f69e1200670fbfec000,0xa8fc3b00a07ac8d80049,0x235fc66005073c1e002,0xfcc1808cb27602368e76,0x273edd3c09ce867e04eb,0xd00239f4ccf0273a5bf0,0x9cb6fe97eac4001a97d4,0x351e1b804f94fea4001,0xf52000ce5b7865f41680,0x7bb30278bfe444047cb7,0x7bb28146afc288c0248,0x6cbe140a001aaf8b2814,0xbc3c2a40034de79409bb,0x412001a46f598c02447,0x1a79fbe88a0021fbf83,0x1809000d71c3feb0210,0x2001ababf4800cc1efe1,0x25000cef980bdfe08a01,0x676f380cfcbce0457f1,0xbf957b2001a33ffcd060,0x8fbd3a808c979c6011c,0x47afc2100400d3bfb808,0x3f886680068bf4ff5014,0xff09110033f77d040198,0x2200690fff0291003397,0x7f9e9c4c10069aff7448,0xc60118bf2ff046100348,0xf8c022cfc73c6008e3af,0xdfcfba80a0fcfb250285,0x55fde758047df3802023,0x70ff0a4e06006998f004,0x8a43b4001aa34e683006],#[0x671f35fea000492dba7,0x74e30b2600ce1f31e900,0xf72e2000ce5f3a6d0006,0xff0d009194c79c0019c3,0xd2880925fba200334ed7,0x69033c15e20021e67f3a,0x6ec54019e3f8dafd1200,0x3c00ce1ff4812200d0df,0x68bfc24f00a1a5ff5,0x29db8d7e00122bf8650a,0x7f738364009477df9e00,0xa1900068dfeb8d080123,0x88dff3834200496ff9c,0xef96880128907b58d940,0x440019d632beba0246fc,0x4f7f48b40bc0006acfb1,0xff90092dfff992260003,0xcc3c05d7940009639b91,0x2b1ec7780024d7f90000,0x70001a33f0ce5e9dc00d,0x4d7af8e930001a62ddf8,0x8364009689ebeb940003,0xa2a294c3900340f97cff,0xdfe300019e39e5e34001,0xfd40055bf1f9eb201223,0x34c710ff9000670fe7,0x2fe7b0001a903feb2428,0x4000951e7f5c0019bb11,0xa7f9768000d23ff8df5a,0x67ff00138fe5f80047ce,0xa0047b60f34010800112,0xe12000cf5f7d700a14e7],#[0x8ae01544e1fb80535f9f,0xa06ff95f5300249fcb,0xa75c46faa000088af677,0xebdb80515cbf59014001,0x9998023017f0940001a0,0x52779e90275fe2e70047,0x2fe301d46012896fbc20,0x200d4dffa60658e08035,0x508f333809211f8dd588,0x613200d6be7fd4830120,0x987f040401a63f6e3f10,0x940c00d6bff4a5802427,0xaa2ffc358024353fd2b9,0xf840069ac7e041b46001,0x6b8f5fc2003307e5e56e,0x6800cdd9718f5e11c400,0x682fbbff322001a63e7b,0x2bc6cf0049ae7ab78300,0x43f4012471fd0fd00489,0x420256fcf10fd004913c,0x589c574a101307f38ae9,0xfcd840a57f1ea0201207,0x330ffaa1c4f11804b21,0xcb55cff8a200d11fd4c8,0xff875c830034f7f86800,0xcc003387e65e50019c3b,0x8ed1fead4800680fbf5,0xc02006a4fd80dbffcd20,0x82001ad3f60347f0d0b0,0xc1913f280901fcf88279,0xf01202b1fd1c7a940804,0x1267fd9cc1009279ffe],#[0x12f73191080923fb3982,0xcf13438091be73142210,0x57cbd4050b9389ce0246,0x9420c0491fd666079009,0x20e01250fd943809123f,0x49f94fe8520068d3fff4,0x39e0126bfae9241cc00d,0x3537fb12481a00d239bd,0xd6690092dff4d0171100,0x92dfed102290034aff0,0xf53d6a46012b7d4bf230,0x25cf1fac459e300973f,0xfd0810091bc6b8deb942,0xc258201327ffd82011c7,0xff0226020069dfebff5a,0x123bfed4d0802001a83,0xfea080180801ac771885,0x80953c7dba74900975f,0x7ff8a840001a04f9fa11,0xff3d602a8b9f1ea60241,0x929ff4ac4d82400d5659,0x20d7f8680488b33f0d00,0xfd7c4c100927ffb8c80a,0x404c6ffe7823010034af,0xfb73814049598fb27888,0x80242d6785fc88404bdf,0xce1f43b9a0068dfa823f,0x1206fb2a023b78ae0400,0xd77400900348f87ef5a0,0x90deede96940003567f,0x8cc3b70001ab7fb31ac0,0x6c6a61f80413c000d716],#[0x9001a73e79402012e000,0xaf2f8d2003416c1f875e,0x676e61c54f91a4006c2f,0xbfdb0800d3dfe9dba400,0xd79eb3f843400690ad3f,0xf7e008e21791decce025,0x931c3f506c364006a92b,0x18b03c006bdf9ca1fa00,0x354f8deb990122b8fe1f,0x404080498fb7a2992200,0x925ea15e9464006adff,0xfdd8a34c00691fb9cc10,0x1a200356f9fa1240488f,0x7fa63a32003417e9f81b,0x34857fc21f9a3200356,0xdce6080494fc31f4a320,0x240491e3ed278920258f,0x27fcfd0920246efed3f]]
set_option maxRecDepth 32000 in
def g255H11 := limbs80 #[#[0x11c0401000112020402,0x5310c0700000004000a,0x60005000300000e0c07,0x10804040201010206,0x1060209040707330005,0xa220210110006130700,0x200000800100c070000,0x104000b06190c070609,0x3900110804031002004c,0x107090002040f030401,0x3000000220107011000,0x2e010309010c0a010a0c,0xa06030000111a0b0001,0x70c0000040004041611,0x220a071b0307054c0721,0x201010f1c0107011402,0x1340d000a020a010500,0x4f140208130005040001,0x20610280a05140a40,0x3170d02000341050203,0x14021c000b05000e1202,0x1b13052a040f4c2c0000,0x4030a00120e01110f2e,0x15440000010103041093,0x4107020500031d01030f,0x90000000000000198ca,0xadbd5c00031ae0000006,0x214a0008c20000000,0xd22d0000146c04000c91,0x12400027d279fa4,0x1b232c1c54a8000861ed,0x65e1401a9dfd88749999],#[0x22abd914a4c12e4809f,0x162731f1fa03585527fb,0x34e34cf0fa34c2065936,0x78c1d85f8d1078c45246,0x8a15c000d0b800000048,0x1100037902ddd58c2dc2,0x250b1c10ded080000001,0xcb546b7a733860002146,0x17401e8dd819a1cd,0x1277c3dcaa12e6000cee,0x23800006b2fe000000,0xf60c59468733b14a2300,0xf300012b892b8bfa5d93,0x15e96054008d40000008,0x55b2774001a0120e8001,0xd12a04e935e8e4a37cd1,0xe66768364712a24ec28b,0xc02628484ba62995b2ac,0xd4e285f954a00000035,0x10400092690e0197d0c4,0xab9a6201a70998a34a88,0x800333213ba9683bd835,0x2ec1c3680000001f2c19,0xe800033e000000016089,0xd149c0ff1553b4df483,0xa4f3c0064304ab061,0xc1eab0cbe80032d20000,0x53080001ce8e83425b8c,0x8d30000115e31206e08f,0xb00001c31f78c0c53952,0x34000d1900037e0000df,0x319e49900029],#[0xb32000a0c57b31fe0,0x4aa338a85c6e8,0x2b12ad50007367478,0xac08002b0c192000,0xd02221eb1b6722a69000,0x899b0c60864451200081,0xa931113f116c00000022,0x40c9940006876aef55c0,0x44e417e3bc0638ede7b2,0xd0d19f3a5583d15ad439,0x87d06df49000000065a,0x5b440000000412c00000,0x64865c55c001211463a0,0x2b0f119e1220080001,0x91400003cf992000b068,0x814c000cd742000034ea,0x9a3446e355949692c3c,0x33222aae3e5c94e000,0x19e44e2000033400000,0x4566836e6dcf0c9580,0xc2a000b0b6b3c0e9a6a0,0xdaeb608cf48944d8000,0x23fa0000000003518000,0x234c000000000,0xefab5c224b7800000055,0xb215332c240000002a,0x4c91a1588d3900032ea0,0xa1800000000009fa0026,0x63e02215e789f00004ec,0x27c0004b168a4d28000,0x9c1042028545c5e189,0x69d48d500000018a800],#[0xbc22f08c9b800008850,0xaaee38b440000000c,0xe9641cc0012a7cc5299c,0x85e9ce2ee710bce19ee,0x7c91807400127dafb000,0xda1234c8012e961b305f,0x6c23e8000001104c8b01,0x22c001cdb2858000057e,0x971e01f9bcc828c90749,0x1f60006700001,0x127c00000000115dc58,0xa248199445f00002d400,0x9e300029e00018300d,0xfb80000012ab02484cc0,0x1d4000884847ba0f27b4,0x50956a000000000062df,0x1168d6614731f2000,0x4b8a0400042183a800,0xd8000000d28011406c89,0x73c03000119400006423,0x3bea0000002558001c,0x14f236d2e84f4000d1d0,0x97af32e000d04c724001,0x7ab401a238c492022297,0xc28c40008540001b6829,0x9694cd3f706630dc2940,0x2269398df082525e2643,0x26a166361e392216a0b0,0x8968b76281067d48886f,0xb40a00000009cfbffaac,0xa00028dc00010700053a,0xb8000000edb000000195],#[0xb20fc8b480011120e7a3,0xabf87918723d8001085a,0xadfa0700012262cd41c8,0x626916c1c788e4b42203,0x2000000215d40e00086f,0xd027b9d600012f638a31,0x10a945fc037a1b43115,0x2b7a9e40,0xd6a45940000000,0x923431a53b117f000000,0x228b1c2c30315c3ab106,0xe0ac0b8514269000000,0x60000585470800000000,0x674443352e8e0ea,0x2f600000000000000,0xcd2407a54d0b587a6b90,0x39400118844c03464b9,0x89c81200001187a10563,0x526553e3c90531d15a41,0x498fcc0e058f04e43895,0x46098a8a8bd501690c2,0x1a8f00065a94a32849,0x4361552d73c9774c4,0x53b3a1300000038a6000,0x11ac996000532497,0xa04029220517800,0x120dc800307a0004df80,0x82aaca06bebe40,0x6110dd04328460002218,0x5960316ba40422c2,0xc2c0000089d43e170459,0xf44de1be00000000008c],#[0xf8a82a9d038000019e4d,0xce80000000000004af13,0x4a6055000000186da4a8,0x22d0336c8e00da77f,0x20b9a6da062b2b15b903,0x70000057a4fa9cd30000,0xc13411280002b7942aa5,0x8096ba0500000006bb08,0x11210a0b1298418,0x9a88160a90000a1ac100,0x3a2d0e36107352403272,0xcaa600074de300ac7292,0xf474a0df085c588001b3,0x161412101fca0ddc982,0xd0e4a400125200046380,0xefc85184149e84,0xca1eaf8000000000724c,0x7094000266c01686a11d,0xf24467345321ed0000a8,0xca8e11d0107aac685ca9,0x4fb09e6b9b160004d603,0xa4a8170b9b39a8912350,0xd34de8000001a444bba,0xaa7892307228743aea64,0xc83f000050a2580b38e9,0x464c0009c6d27800217,0xb8967cac000052900700,0x64a52888b0ec89d00035,0x29da59d4d80003c4486b,0x244bd39294c8ed,0xa1419b395aaa224014fd,0x1ab7000217193cc4611b],#[0xc5a6b9a252f8b4f29080,0x9d8418001b092c395066,0xb1919c0000c2e8f71e3e,0x4d23080020275340007,0x10f897a4f50001113,0x4000c697a58000d2be49,0x775d75cca5be28000103,0x90000d51800125f99093,0x59800335b1f0014d0455,0x46c00000020200004109,0x4460004b94,0x32bedfe000427e5c4a34,0xac05036f55a66b0aa000,0x3a811ff00040efd859c,0x23e0f800000000013a00,0x7c00000000000008,0x33ea0000000,0x643c27a80bd4180011da,0xc0001688000000000000,0x498f705a4e3000096b44,0x19e9227a9140018a196,0xcb24e0a3000000000000,0x4d0000d266428a1f9a74,0x861018b9f0a0e94d4275,0x400145100075c4001a62,0x24c102ec43da86a59641,0x6f23e000523800000196,0xcd000000237800004264,0x2bf480c33880033180,0xa16c840000001c300000,0x8b840000009155a52cd2,0xe000532d0792bc955cd5],#[0xc9494302000254236431,0xdccf68a805f0000000cb,0x1dc12d85990a00020,0xd4000000000208e0000,0x20e00010ba0000002159,0xf58587e6f9f340c16d3b,0xfb3917005c090215b821,0x5c459019eaa751d84ea3,0x5055c56d31a8f04d294,0x758001043a3f67944d84,0x60112a275c52a93f2bec,0x262c29a92500026ca5b5,0x7a90c7f59ba15800046e,0xb9157e9eb13fd56712,0x43dccc20bc450c9600,0x26a4000a8e00000000,0x1d96d81e00003de0000,0x119e2904de0000000001,0xc268a87307000000022e,0x546d68880d98f7f1ae51,0x1a03000000152da5,0x347dcaf14b80]]
set_option maxRecDepth 32000 in
def g255D12 := limbs80 #[#[0x5cd72591635895350d32,0xfeff7fbfbfdfeff5d974,0x22c615720ab1055483ff,0x5c8c30e018600c2845cc,0xa0c5cc4aecc18734bb1d,0x11c2886145ae82d6416a,0x17328b190e1c470c2186,0xec896548b9a061c830c5,0x5caeae38471c13861d12,0xb5d14706a38672bb38e1,0xc148e1a0707038754bb2,0x60cba865940709238391,0x39636ca9b65ccf2a6797,0x2e859642cbb0e5d472ca,0x91f304f9754cba265d8b,0x4e60a730cf9857cc23e5,0xdc24e612770739839dc1,0xb709307a061044026000,0x11941771501301120e40,0x27524d23120f1f51db1c,0x513393162f02ce2af292,0x83fc3db3b83a238a3723,0x4d74b549147245043941,0xc559f57e55b5375154f6,0xb6b668365e63960d5e95,0x7e47b878e76673e7086d,0xe28c18a288a85b83a80c,0x88461703809599349058,0xbc1e1e0687c40670c1,0xc2a14428a8100d092191,0xc1c36100388034118320,0x98a07d104dc340cca0b],#[0x250e83e24348a2422293,0x174a8ac2d24990280c86,0x71fc28e011f08488ca5d,0x3df803b3ff601ce5dc02,0x943fe29008cfe9008,0x27988f9700012a6b9a36,0x3dc00a6ce4c00a29b3c0,0x8f8000012576fe0107f6,0x66c0437bd80d5cc8134f,0x23c79d013dfde6404ef,0xf000273d380138ff8884,0x122ff8010283f33604d7,0x140417fa0502998f1450,0x38087e6807df18a0233f,0xa0507f86900a1f98066e,0x9f9c500a1fbc701efbe0,0x86c0283ef9c009d79c03,0xf7fce0013ddfce001459,0x1e0141f37002727fc004,0xde07805072d9980534df,0x40779f34052bbf280463,0x2489fb94023dfed9801,0x461bc7a4023ce7aea00,0x90bf3fe7c5c056bdff00,0x2ff3399800557f5f4202,0xe10d02a0ffe87f845c0b,0x8ca0049b77cc0902aa7b,0xe100a5722e624012879d,0x8029df8f18500126ffa4,0x28079fc0f80200936e70,0x290df1e01458e3c0287f,0xa878f8cba0024df37280],#[0xfe3c013995f1e00]]
set_option maxRecDepth 32000 in
def g255H12 := limbs80 #[#[0xc0000004100800218182,0x18508001c28000186860,0x2840a585051e4018700,0x2090a0c384020460c400,0x1a122021d08000220024,0xc08000800860e20343,0xc0000e38600001c00,0x47018028043010410329,0x3428e5810b800200c8b1,0xc00338341c00337b1eb4,0xba43de0304008f721846,0xe8cf8c51730afbd22a8,0x3a6e3f31c282c00209cc,0xbf02d8a682d134000000,0x23200012c4000000,0xb48511d474002c380000,0xbbb2b72e1b36a7e9d29a,0x12442979980000220e9,0x1b0002a780078aeac80,0x117400035000000000,0xdd25e2680020c22ec000,0x2408001a70001bd80039,0xc1400020c0011f813400,0xf616f2fe0910e4003a47,0x202985d214000003c742,0x4380010a294609800200,0x2e410000002058003234,0x30f80009a00000000002,0x21ab14400000000,0x700003000033081f128c,0xbaa193c0000000031972,0x222400000214004],#[0x238800243c000,0xf28800208340400238c0,0x12200018161101c,0x83e87eb39260b14,0x8003a9135d4411581bc0,0x7000035800000000047,0x1c1c0001dc000001422,0x29353874600000000,0x22800000015c00337505,0xc99b734407d23c0d4010,0x442c36118a0ce06b9063,0x44c07b1d50b606c2f12d,0x1933444a052879c8002,0xc0018f80013e014e2e40,0x18472b303af0f0003b5,0x5a1ee849b3c0028a4096,0x98a39540e2,0x230c0032c80001d,0x53183c358ff9e8bcb088,0x40b90d00023569032774,0x483a1012a8780340029d,0x14c0905f3353980001e3,0x800139c9b80020440604,0x89400000385b117b18a5,0x38000b970669fe9f4bdf,0xf46a812be43e405703c0,0x26531f04fb219eda0901,0xeb3cc3060b20432a3bac,0x82ac3c7240b7db2c0ed2,0x4540030a80000023170c,0x14003326121430000206,0x40000000000000032a50],#[0x252b43bcd0741261b736,0x28000b1f0842553b0002,0x3db19d1993f800336ab,0x12d4652b13e800000,0x8208000000000000000,0x30d80000002780009f01,0x1050de2398a331b3fc00,0xa127d1c62111adbfb34f,0x42df16116b2bc16542b3,0x24fa192f89f833a37015,0x1311130000002a5c001,0x841c131e41852331780,0xbeb29800314a1a0000bb,0xaa24847ec20001328943,0x13d73913,0x87400000015000283000,0xfe1000000001a510f34b,0x33013c0001ca0,0x11d80000000a400,0xc000000096826e8bc000,0xa3b700a81c2810f40002,0x8184240030bca4800213,0xfe0263efbb40000031f7,0x3883844003bd41,0x119320245f8d400000,0x29c00133c00100cba8,0x69752bb29000117c0000,0x18c0000000000000003a,0x2828000000,0x1a242cc3d00033c18f2a,0xa1d3f5a9844800000000,0x18000003a8732d0c40e2],#[0x337d11800000108c4884,0x194f36c00302c00000,0xb821c000003b273bc000,0x245b1b8000b753]]
def g255D13 := limbs80 #[#[0x2e6b1aa6a1ae4b1265ff,0x4f0bc8a5a2c00bb2e8b2,0x70f0c110b0301bd975d2,0xa28221a0c160e0710950,0xfc803bf800e2e3224202,0xcfe6603bd50029fe801d,0x7f388053fc3404de4804,0x51c0432008]]
def g255H13 := limbs80 #[#[0x61c00018180820018007,0x38226001460300c81893,0x9b98f400c18270012380,0xda1c0021ab44411c80,0x61b01643003190023186,0x8400012400000c8bc2d1,0x4008f33a45f15a5725e0,0x83947e28c982e4cd204a,0xa14aa82a673354c236c5,0xc00827a72f3210012b0f,0x20f4052f68c4402,0x681ec9aeec000828378b,0x80e00000cfd120011e68,0x1346b000e6c0080db5d0,0x311a3907002ba8209281,0x1adcec000001d0000043,0xe964cb13400000022d00,0x8ff0f1a904000e0006c]]
def g255D14 (j : Nat) := if j=0 then 0x70c1418802007ff else 0
def g255H14 := limbs80 #[#[0x4b84030ea4db000085,0xc400000ce000,0x119444008c000000248]]
def g255L : Nat → Packing
  | 8 => (88,6,7,3473469,102,12,1122,g255D8)
  | 9 => (695,5,7,11600183,137,15,1421,g255D9)
  | 10 => (743,4,7,6553829,120,16,1329,g255D10)
  | 11 => (291,3,7,2031681,87,14,1180,g255D11)
  | 12 => (70,2,7,458762,52,12,1086,g255D12)
  | 13 => (10,1,7,65537,0,8,1045,g255D13)
  | 14 => (1,0,7,0,0,0,0,g255D14)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupShort 29 137 7 10 7 1 g255H9
  | 10 => lookupShort 233 1381 7 13 10 1 g255H10
  | 11 => lookupShort 249 1361 8 13 10 1 g255H11
  | 12 => lookupShort 102 607 7 12 9 1 g255H12
  | 13 => lookupShort 24 127 7 10 7 1 g255H13
  | 14 => lookupShort 3 37 3 7 4 1 g255H14
  | _ => fun _ => none
def g255 : Forest := ⟨255,14,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255B8 : CutRow g255 8 0 88 := (@joinRow g255 8 0 48 40 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=3)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (@joinRow g255 8 48 6 34 (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply polarBlock (data:=fun _ => (w80 [0x601,0xc06870327403010281,0x48b01a7200210060701a,0x1130100000c068708265,0x180410088500e720021,0x60701a113002000209,0x14a214720200020914a2,0x14720a0100c068b05275,0x210060701a11300021,0x4024102113000210060,0x701a112000210120d04a,0x112000210060701a1120,0x210060701a11200021,0x120d04a112000210060,0x701a112003030281c0b0,0x384210000180e0e08865,0x3010180c8701a721000,0xc068b0826501020000,0x8814284200210120d04a,0x113010000281c0b0a086,0x10000181c070c0860021,0x60701a112004040001,0x844604300210060701a,0x112000210120d04a1120,0x210120d04a11100021,0x120d04a112000210060,0x701a112000210120d04a,0x112000210120d04a1120])) rfl
      decide +kernel
)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : CutRow g255 9 0 40 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_40 : CutRow g255 9 40 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_88 : CutRow g255 9 88 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_136 : CutRow g255 9 136 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_184 : CutRow g255 9 184 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_232 : CutRow g255 9 232 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_280 : CutRow g255 9 280 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_328 : CutRow g255 9 328 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_376 : CutRow g255 9 376 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_424 : CutRow g255 9 424 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_472 : CutRow g255 9 472 23 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_495 : CutRow g255 9 495 5 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_500 : CutRow g255 9 500 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x210060,0x701a114000210060701a,0x114000210120d04a1130,0x210060701a11400102,0x4028110285300208090,0x68260980010204028110,0x284200220090c8262150,0x210060701a11300021,0x120d04a113000210120,0xd04a1130018184024108,0x1c320181840241081c32,0x210060701a11300021,0x60701a113000210060,0x701a113000210060701a,0x113000210060701a1130,0x840091482c44820400,0x20108c0229300220090,0xc82621800800010088c0,0x429400440180e0644281,0x220090c82621700044,0x422014428100220090,0xc8262170040404030140,0x605400840091482c4482,0x220090c82621800404,0x4030140604300220090,0xc8262170004404028104,0x427100210120d04a1130,0x210060701a11300021,0x60701a112000210120,0xd04a112000210120d04a,0x113000210120d04a1120,0x210120d04a11300021,0x120d04a112000210120,0xd04a112000210120d04a,0x112000210120d04a1130,0x210120d04a11300021,0x120d04a112000210120,0xd04a112000210120d04a,0x11200021040241021130])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_548 : CutRow g255 9 548 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x210060,0x701a113000210060701a,0x113003030281c0b03842,0x181840241081c311000,0x402910828600210060,0x701a1130002104024102,0x11300021040241021130,0x210402410211300303,0x281c0b0384201818402,0x41081c3100210060701a,0x112000210060701a1120,0x210060701a11300021,0x4024102113000210402,0x41021140002104024102,0x11300021040241021130,0x181840241081c420104,0x1018050489301818209,0x448a1c3201818209448a,0x1c310104010180504883,0x1818209448a1c320021,0x60701a114000210060,0x701a113000210060701a,0x11300021040241021140,0x210060701a11300021,0x60701a113000210402,0x4102113001080182c070,0x889303050181c0705893,0x601828160e038840303,0x281c0b0384203030281,0xc0b0384203030281c0b0,0x385300840091482c4472,0x210060701a11400303,0x281c0b0385303010180,0xc8701a8203010180c870,0x1a8200210060701a1140,0x210060701a11400021,0x60701a114000210060,0x701a114000210060701a,0x113000210060701a1140])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_596 : CutRow g255 9 596 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x210060,0x701a1130082504024102,0x513000810209448a1432,0x210060701a11300021,0x60701a113000210060,0x701a113000210120d04a,0x11300825040241025130,0x810209448a14320021,0x120d04a113000210120,0xd04a113000210060701a,0x113000210060701a1130,0x810209448a14320181,0x840241081c3201818402,0x41081c3200210060701a,0x113000210060701a1130,0x810209448a14420303,0x4028110385300810209,0x448a143200210060701a,0x11300601840221403884,0x210060701a11300a01,0xc068b0528500810209,0x448a143100210060701a,0x113000210060701a1130,0xa0100c068b052850021,0x60701a113000810209,0x448a144200810209448a,0x143200810209448a1431,0x210060701a11300021,0x60701a113000840091,0x482c4472010401018050,0x48830021040241021140,0x3050181c07058830104,0x1018050488300210060,0x701a1140002104024102,0x11400020809068260970,0x1818209448a1c320021,0x60701a113000210120,0xd04a11300601828160e0,0x38840181840241081c32])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_644 : CutRow g255 9 644 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x210120,0xd04a114000210120d04a,0x113000210120d04a1130,0x4000040285022940020,0x80906826097000208090,0x6826098000210120d04a,0x11400021040241021130,0x210120d04a11300021,0x60701a113000210120,0xd04a113000210120d04a,0x11300021040241021120,0x210060701a11300200,0x20914a2148300810209,0x448a144200810209448a,0x143200210120d04a1130,0x210120d04a11300081,0x209448a143100210402,0x4102112000210120d04a,0x11400020809068260950,0x210120d04a11400305,0x4030110586300210120,0xd04a1140030504030110,0x588300210120d04a1130,0xa018402218058850601,0xc06870328400210120,0xd04a1130060100c06870,0x328400210120d04a1140,0x210120d04a11400021,0x120d04a113000210120,0xd04a113003050181c070,0x586300220090c8262170,0x3050181c07058530021,0x60701a114000210120,0xd04a11400301028148b0,0x1a820180412098580e82,0x301028148b01a820180,0x412098580e8200210060,0x701a113000810209448a,0x143200210060701a1130])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_692 : CutRow g255 9 692 3 := by
  apply polarBlock (data:=fun _ => (w80 [0x210120,0xd04a114000210120d04a,0x114000210120d04a1140])) rfl
  decide +kernel
theorem g255B9 : CutRow g255 9 0 695 := (@joinRow g255 9 0 376 319 (@joinRow g255 9 0 184 192 (@joinRow g255 9 0 88 96 (@joinRow g255 9 0 40 48 g255P9_0 g255P9_40) (@joinRow g255 9 88 48 48 g255P9_88 g255P9_136)) (@joinRow g255 9 184 96 96 (@joinRow g255 9 184 48 48 g255P9_184 g255P9_232) (@joinRow g255 9 280 48 48 g255P9_280 g255P9_328))) (@joinRow g255 9 376 124 195 (@joinRow g255 9 376 96 28 (@joinRow g255 9 376 48 48 g255P9_376 g255P9_424) (@joinRow g255 9 472 23 5 g255P9_472 g255P9_495)) (@joinRow g255 9 500 96 99 (@joinRow g255 9 500 48 48 g255P9_500 g255P9_548) (@joinRow g255 9 596 48 51 g255P9_596 (@joinRow g255 9 644 48 3 g255P9_644 g255P9_692)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : CutRow g255 10 0 24 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_24 : CutRow g255 10 24 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_72 : CutRow g255 10 72 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_120 : CutRow g255 10 120 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_168 : CutRow g255 10 168 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_216 : CutRow g255 10 216 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_264 : CutRow g255 10 264 3 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_267 : CutRow g255 10 267 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_315 : CutRow g255 10 315 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_363 : CutRow g255 10 363 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_411 : CutRow g255 10 411 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_459 : CutRow g255 10 459 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_507 : CutRow g255 10 507 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_555 : CutRow g255 10 555 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_603 : CutRow g255 10 603 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_651 : CutRow g255 10 651 31 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_682 : CutRow g255 10 682 4 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_686 : CutRow g255 10 686 48 := by
  apply polarBlock (data:=fun _ => (w80 [0x210060,0x701a114000210060701a,0x114000210120d04a1140,0x210060701a11400021,0x120d04a114000210120,0xd04a114000210120d04a,0x114000210120d04a1140,0x8250402410251400021,0x120d04a114000210120,0xd04a114000810209448a,0x144200810209448a1442,0x810209448a14420081,0x209448a144200210120,0xd04a114000210120d04a,0x11400181840241081c42,0x181840241081c420021,0x60701a114000210060,0x701a1140030504030110,0x586300210120d04a1140,0x210060701a11400305,0x181c070586300210060,0x701a114000210060701a,0x114000210060701a1140,0x810209448a14320081,0x209448a143203030402,0x8110385300210060701a,0x114000810209448a1442,0x210060701a11400303,0x281c0b0385301818402,0x41081c4200210060701a,0x11400021040241021140,0x1818209448a1c420303,0x281c0b0385300210120,0xd04a113000210120d04a,0x113000210120d04a1130,0x220090c82621400084,0x91482c445200210120,0xd04a113000210120d04a,0x113000210120d04a1130])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_734 : CutRow g255 10 734 9 := by
  apply polarBlock (data:=fun _ => (w80 [0x21,0x120d04a114000210120,0xd04a114000210120d04a,0x114000210120d04a1140,0x210120d04a11400022,0x90c826215000210120,0xd04a114000210120d04a,0x114000210120d04a1140])) rfl
  decide +kernel
theorem g255B10 : CutRow g255 10 0 743 := (@joinRow g255 10 0 363 380 (@joinRow g255 10 0 168 195 (@joinRow g255 10 0 72 96 (@joinRow g255 10 0 24 48 g255P10_0 g255P10_24) (@joinRow g255 10 72 48 48 g255P10_72 g255P10_120)) (@joinRow g255 10 168 96 99 (@joinRow g255 10 168 48 48 g255P10_168 g255P10_216) (@joinRow g255 10 264 3 96 g255P10_264 (@joinRow g255 10 267 48 48 g255P10_267 g255P10_315)))) (@joinRow g255 10 363 240 140 (@joinRow g255 10 363 96 144 (@joinRow g255 10 363 48 48 g255P10_363 g255P10_411) (@joinRow g255 10 459 48 96 g255P10_459 (@joinRow g255 10 507 48 48 g255P10_507 g255P10_555))) (@joinRow g255 10 603 79 61 (@joinRow g255 10 603 48 31 g255P10_603 g255P10_651) (@joinRow g255 10 682 4 57 g255P10_682 (@joinRow g255 10 686 48 9 g255P10_686 g255P10_734)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : CutRow g255 11 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_4 : CutRow g255 11 4 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_52 : CutRow g255 11 52 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_100 : CutRow g255 11 100 15 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_115 : CutRow g255 11 115 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_163 : CutRow g255 11 163 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_211 : CutRow g255 11 211 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_259 : CutRow g255 11 259 1 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_260 : CutRow g255 11 260 31 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : CutRow g255 11 0 291 := (@joinRow g255 11 0 115 176 (@joinRow g255 11 0 52 63 (@joinRow g255 11 0 4 48 g255P11_0 g255P11_4) (@joinRow g255 11 52 48 15 g255P11_52 g255P11_100)) (@joinRow g255 11 115 96 80 (@joinRow g255 11 115 48 48 g255P11_115 g255P11_163) (@joinRow g255 11 211 48 32 g255P11_211 (@joinRow g255 11 259 1 31 g255P11_259 g255P11_260))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255B12 : CutRow g255 12 0 70 := (@joinRow g255 12 0 44 26 (by
      apply checkedRow
      apply cellsBlock (ar:=9) (rows:=0) (d:=3)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
) (by
      apply checkedRow
      apply cellsBlock (ar:=10) (rows:=0) (d:=2)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255B13 : CutRow g255 13 0 10 := (by
      apply checkedRow
      apply cellsBlock (ar:=9) (rows:=0) (d:=1)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255B14 : CutRow g255 14 0 1 := (by
      apply checkedRow
      apply cellsBlock (ar:=8) (rows:=0) (d:=0)
      simp only [cells,boxes]
      repeat' apply And.intro
      all_goals decide +kernel
)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : mixedTables g255 14 := by
  intro k hk
  interval_cases k <;> first
  | exact g255B8
  | exact g255B9
  | exact g255B10
  | exact g255B11
  | exact g255B12
  | exact g255B13
  | exact g255B14
  | exact mixedEmpty g255 _ 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 14 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact mixedRoot (g:=g255) (top:=14) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_52682

open PEqualNP.Outside.L_meta_52682 in
theorem PEqualNP.Outside.L_meta_52682 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
