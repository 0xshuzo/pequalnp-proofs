import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52262.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52262
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffeefffffffefffffefe,0xffeeffeeeeccaa00ffff,0xffffffffffffffffffff,0xffffffeefffffffeffff,0xfefeffeeffeeeeccaa00]))
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,6]⟩,⟨.or,[1,3]⟩,⟨.or,[2,4]⟩,⟨.or,[4,8]⟩,⟨.or,[1,7]⟩,⟨.or,[5,7]⟩,⟨.or,[3,7]⟩,⟨.or,[8,14]⟩,⟨.and,[15,0]⟩,⟨.and,[13,9]⟩,⟨.and,[12,11]⟩,⟨.and,[6,10]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 6, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 6, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

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
def K41 := extendKnown [] 4 [(41,[]),(82,[16,67,101]),(137,[117,101]),(146,[16,67,117,101]),(161,[83,67,116,100]),(162,[16,83,67,116,100]),(168,[48,16,33,82,66,116,100]),(193,[99,67,117]),(194,[16,99,67,117]),(208,[64,16,33,99,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := [(2,0,41,0,4)]
def g43A : List (List Nat) := [[],[48]]
def g43D4 (j : Nat) := if j=0 then 0x1f else 0
def g43L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g43D4)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,4,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P4_0 : block g43 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B4 : block g43 4 0 1=true := g43P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact (rfl : block g43 3 0 0 = true)
  · exact g43B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K41 V41) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K41 5 [(43,[]),(83,[16,67,101]),(105,[48,97,33,80,66]),(114,[64,81,32,99]),(139,[117,101]),(147,[16,67,117,101]),(153,[65,33,117,101]),(154,[16,48,32,66,117,101]),(177,[65,33,83,115,99]),(184,[48,65,32,82,114,98]),(202,[16,48,32,98,66,117]),(216,[64,49,32,97,33,117]),(232,[48,97,32,82,65,114,66]),(240,[64,81,32,99,33,114,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V41 low43 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2fc38ff01fff1ff02,0xfc38ff01fff1ff02fc38])),(BitVec.ofNat 152 (word80 [0x42ccdb2a5451240242,0xccdb2a5451240242ccdb]))),((BitVec.ofNat 152 (word80 [0xfdcbc7fffe07fe3ffd,0xcbc7fffe07fe3ffdcbc7])),(BitVec.ofNat 152 (word80 [0x1448490c1860408414,0x48490c18604084144849]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b06085892808,0xa7b6b06085892808a7b6]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x893124c08106003089,0x3124c081060030893124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
theorem g51P3_0 : block g51 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51B3 : block g51 3 0 1=true := g51P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g51 0 0 0 = true)
  · exact (rfl : block g51 1 0 0 = true)
  · exact (rfl : block g51 2 0 0 = true)
  · exact g51B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 4 := lower_forest (g:=g51) (i:=0) (hints:=65605) (before_sound K43 V43) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K43 4 [(51,[]),(58,[48,32]),(75,[16,67,101]),(89,[48,97,33,32,80]),(106,[48,32,100]),(113,[64,16,33,50,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V43 low51 (by decide +kernel)
def g163Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0)]
def g163C : List ColumnInfo := [(1,0,162,0,4)]
def g163A : List (List Nat) := [[],[117],[16],[16,117]]
def g163D4 (j : Nat) := if j=0 then 0x1f else 0
def g163L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g163D4)
  | _ => emptyPacking
def g163I (_ _ : Nat) : Option (Nat × Nat) := none
def g163 : Forest := ⟨163,4,fun i => g163Y[i]?.getD (0,0),g163C,g163A,g163L,g163I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163P4_0 : block g163 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g163B4 : block g163 4 0 1=true := g163P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163T : checkedTables g163 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g163 0 0 0 = true)
  · exact (rfl : block g163 1 0 0 = true)
  · exact (rfl : block g163 2 0 0 = true)
  · exact (rfl : block g163 3 0 0 = true)
  · exact g163B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163G : graphValid g163 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low163 : Lower true (varsX 163) (graphGoal 163) 5 := lower_forest (g:=g163) (i:=0) (hints:=85) (before_sound K51 V51) g163G g163T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K163 := extendKnown K51 5 [(163,[]),(170,[16,48,32]),(178,[64,81,32,50]),(195,[101]),(201,[48,97,33,32,80]),(225,[80,97,33,50,67]),(226,[80,97,32,50,67,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V163 : Known true K163 := extend_ok (m:=163) V51 low163 (by decide +kernel)
def g169Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g169C : List ColumnInfo := [(1,0,168,0,4),(8,0,161,0,4),(32,0,137,0,4),(128,0,41,0,4)]
def g169A : List (List Nat) := [[],[117],[83],[83,115],[115,83],[115],[48],[48,117],[48,80],[48,80,112],[48,112,80],[48,112],[80,48],[80,48,115],[80],[80,112],[80,115],[80,115,48],[112,48,83],[112,48],[112,80],[112],[112,83,48],[112,83]]
def g169D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g169D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g169H4 (j : Nat) := if j=0 then 0xe else 0
def g169D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g169H5 := limbs80 #[#[0x10000280c49030031720,0x104]]
def g169D6 (j : Nat) := if j=0 then 0x3904f else 0
def g169H6 := limbs80 #[#[0x280000000000000000,0x80202d0280000]]
def g169L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g169D3)
  | 4 => (3,2,2,0,0,5,0,g169D4)
  | 5 => (1,1,2,0,0,0,0,g169D5)
  | 6 => (1,0,2,0,0,0,0,g169D6)
  | _ => emptyPacking
def g169I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupShort 1 2 0 3 1 0 g169H4
  | 5 => lookupShort 2 13 3 7 2 3 g169H5
  | 6 => lookupShort 1 23 0 7 0 5 g169H6
  | _ => fun _ => none
def g169 : Forest := ⟨169,6,fun i => g169Y[i]?.getD (0,0),g169C,g169A,g169L,g169I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P3_0 : block g169 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B3 : block g169 3 0 2=true := g169P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P4_0 : block g169 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B4 : block g169 4 0 3=true := g169P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P5_0 : block g169 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B5 : block g169 5 0 1=true := g169P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169P6_0 : block g169 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g169B6 : block g169 6 0 1=true := g169P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169T : checkedTables g169 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g169 0 0 0 = true)
  · exact (rfl : block g169 1 0 0 = true)
  · exact (rfl : block g169 2 0 0 = true)
  · exact g169B3
  · exact g169B4
  · exact g169B5
  · exact g169B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g169G : graphValid g169 (boundsBefore K163) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low169 : Lower true (varsX 169) (graphGoal 169) 7 := lower_forest (g:=g169) (i:=0) (hints:=3) (before_sound K163 V163) g169G g169T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K169 := extendKnown K163 7 [(169,[]),(210,[16,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V169 : Known true K169 := extend_ok (m:=169) V163 low169 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,16,41,2,5),(16,0,43,0,5),(1,0,58,0,4),(2,16,41,0,4),(8,0,51,0,4)]
def g59A : List (List Nat) := [[],[48]]
def g59D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g59D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g59H5 (j : Nat) := if j=0 then 0x4 else 0
def g59D6 (j : Nat) := if j=0 then 0x18989f else 0
def g59H6 (j : Nat) := if j=0 then 0x1208000270005 else 0
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g59H5
  | 6 => lookupShort 1 11 0 5 2 1 g59H6
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
theorem g59G : graphValid g59 (boundsBefore K169) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=65603) (before_sound K169 V169) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K169 7 [(59,[]),(91,[16,67,101]),(121,[48,97,33,80]),(122,[64,81,32,99,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V169 low59 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff00ffffc3fff007fe,0x1ff0fffff85e060f00ff])),(BitVec.ofNat 152 (word80 [0xa0a05008800a05014,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff007ffc3ffff800,0x1fff0ff01cb4b9f00f00])),(BitVec.ofNat 152 (word80 [0x2c0c16050082c06058,0x81402042189431333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff80003fffffff,0xe0000fff23b56600f00f])),(BitVec.ofNat 152 (word80 [0x301018261113048260,0x984448021b064666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff,0xfffff000134bf800fff0])),(BitVec.ofNat 152 (word80 [0x40a0a0482224090480,0x12000904024988888888]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0xcea8c5ff0000])),(BitVec.ofNat 152 (word80 [0x80c0c07000380e0701,0x1c088e084628c4cccccc]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(2,0,105,0,5)]
def g107A : List (List Nat) := [[],[80,97]]
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
theorem low107 : Lower true (varsX 107) (graphGoal 107) 6 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K59 V59) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K59 6 [(107,[]),(115,[16,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V59 low107 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(1,0,154,0,5),(2,0,153,0,5),(8,0,147,0,5),(16,0,139,0,5),(9,0,146,0,4),(18,0,137,0,4)]
def g155A : List (List Nat) := [[],[65],[16,67],[16,48,64],[48],[48,65],[64,16,49],[64,49]]
def g155D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g155D5 := limbs80 #[#[0x3527f7bbf6f4050110,0x5f405d50654155045435,0x66ad0941001546b525d4,0xc08024050462b13e3bb,0x4040201642000001201]]
def g155H5 (j : Nat) := if j=0 then 0x10240028000c40032 else 0
def g155D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g155H6 := limbs80 #[#[0x800000000c241,0x84001100c90046004700,0x970000000000008543d9,0x54002100000000009300]]
def g155D7 (j : Nat) := if j=0 then 0x1605f else 0
def g155H7 := limbs80 #[#[0x116007402129320006,0xca00002518ea]]
def g155L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g155D4)
  | 5 => (10,2,3,262147,34,7,1030,g155D5)
  | 6 => (3,1,3,0,0,6,0,g155D6)
  | 7 => (1,0,3,0,0,0,0,g155D7)
  | _ => emptyPacking
def g155I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 11 0 6 2 2 g155H5
  | 6 => lookupShort 4 41 0 8 4 2 g155H6
  | 7 => lookupShort 3 19 1 7 2 3 g155H7
  | _ => fun _ => none
def g155 : Forest := ⟨155,7,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P4_0 : block g155 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B4 : block g155 4 0 3=true := g155P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_0 : block g155 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_1 : block g155 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B5 : block g155 5 0 10=true := (@block_merge g155 5 0 1 9 g155P5_0 g155P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P6_0 : block g155 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B6 : block g155 6 0 3=true := g155P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P7_0 : block g155 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B7 : block g155 7 0 1=true := g155P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact g155B4
  · exact g155B5
  · exact g155B6
  · exact g155B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 8 := lower_forest (g:=g155) (i:=0) (hints:=65603) (before_sound K107 V107) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K107 8 [(155,[]),(248,[48,65,32,82,97,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V107 low155 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(2,0,169,0,7)]
def g171A : List (List Nat) := [[],[117],[48],[48,117]]
def g171D7 (j : Nat) := if j=0 then 0x3f else 0
def g171L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g171D7)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,7,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P7_0 : block g171 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B7 : block g171 7 0 1=true := g171P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact (rfl : block g171 4 0 0 = true)
  · exact (rfl : block g171 5 0 0 = true)
  · exact (rfl : block g171 6 0 0 = true)
  · exact g171B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 8 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K155 V155) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K155 8 [(171,[]),(233,[48,97,33,80,66]),(242,[64,81,32,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V155 low171 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff007f87f87ffc0,0x3fff8ffc48be5000f0f0])),(BitVec.ofNat 152 (word80 [0x5442a1505109100a8a,0x85092009489a53333333]))),((BitVec.ofNat 152 (word80 [0x1ffff8007ff87fff,0xc07ff1ffbb19600f0f0f])),(BitVec.ofNat 152 (word80 [0x1880c0606202010303,0x6020410290941111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0582802c222c0c,0x82c48a01416b6666666]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06030430443010,0x103000c20264a4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008040040004020,0x20400100000008888888]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(1,0,178,0,5),(2,0,177,0,5),(16,0,163,0,5),(32,0,147,0,5)]
def g179A : List (List Nat) := [[],[64,81]]
def g179D6 (j : Nat) := if j=0 then 0x4689f else 0
def g179L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g179D6)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,6,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P6_0 : block g179 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B6 : block g179 6 0 1=true := g179P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact (rfl : block g179 4 0 0 = true)
  · exact (rfl : block g179 5 0 0 = true)
  · exact g179B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 7 := lower_forest (g:=g179) (i:=0) (hints:=65605) (before_sound K171 V171) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K171 7 [(179,[]),(186,[48,32]),(203,[16,67,101]),(217,[48,97,33,32,80]),(234,[48,32,100]),(241,[64,16,33,50,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V171 low179 (by decide +kernel)
def g185Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff0ff87ffc0,0x7fff8fffdcb91000f0ff])),(BitVec.ofNat 152 (word80 [0x244121202209100489,0x20920084c8901111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff000fff87fff,0x80fff1ffb31f200f0f0f])),(BitVec.ofNat 152 (word80 [0x488240414412010902,0x14120410311602222222]))),((BitVec.ofNat 152 (word80 [0x1fffffff00007fff,0xff0001fc0c1ef0f00000])),(BitVec.ofNat 152 (word80 [0x710b8585805c222e0c,0x185c48a10c1ef7777777]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060860443010,0x206000c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080080004020,0x40800100000008888888]))),(0x0,0x0)]
def g185C : List ColumnInfo := [(16,0,169,0,7)]
def g185A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g185D7 (j : Nat) := if j=0 then 0x3f else 0
def g185L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g185D7)
  | _ => emptyPacking
def g185I (_ _ : Nat) : Option (Nat × Nat) := none
def g185 : Forest := ⟨185,7,fun i => g185Y[i]?.getD (0,0),g185C,g185A,g185L,g185I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P7_0 : block g185 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B7 : block g185 7 0 1=true := g185P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185T : checkedTables g185 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g185 0 0 0 = true)
  · exact (rfl : block g185 1 0 0 = true)
  · exact (rfl : block g185 2 0 0 = true)
  · exact (rfl : block g185 3 0 0 = true)
  · exact (rfl : block g185 4 0 0 = true)
  · exact (rfl : block g185 5 0 0 = true)
  · exact (rfl : block g185 6 0 0 = true)
  · exact g185B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185G : graphValid g185 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low185 : Lower true (varsX 185) (graphGoal 185) 8 := lower_forest (g:=g185) (i:=0) (hints:=458755) (before_sound K179 V179) g185G g185T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K185 := extendKnown K179 8 [(185,[]),(218,[16,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V185 : Known true K185 := extend_ok (m:=185) V179 low185 (by decide +kernel)
def g227Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fe1fe01fe1fc3ffc,0x7ffe3ff1ecd460071c7])),(BitVec.ofNat 152 (word80 [0x141441414144088028,0x50a04802424506249249]))),((BitVec.ofNat 152 (word80 [0xfe001fffe001ffc3ff,0xf80ffc7fe17493038e38])),(BitVec.ofNat 152 (word80 [0x181881818188100830,0x60c08104095412249249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffe0003ff,0xfff0007ffcc2f51c003f])),(BitVec.ofNat 152 (word80 [0xa0a10a0a0a00a11140,0x810512280082e1492492]))),((BitVec.ofNat 152 (word80 [0xffffe00000000003ff,0xffffff80003b4be00fc0])),(BitVec.ofNat 152 (word80 [0xc0c00c0c0c10c22181,0x2060030902a49492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffc00,0x30628fff000])),(BitVec.ofNat 152 (word80 [0x10010101001000202,0x4080040000000924924]))),(0x0,0x0)]
def g227C : List ColumnInfo := [(1,0,226,0,5)]
def g227A : List (List Nat) := [[],[101],[16],[16,101],[80,97],[80,97,16],[96,81,16],[96,81]]
def g227D5 (j : Nat) := if j=0 then 0x3f else 0
def g227L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g227D5)
  | _ => emptyPacking
def g227I (_ _ : Nat) : Option (Nat × Nat) := none
def g227 : Forest := ⟨227,5,fun i => g227Y[i]?.getD (0,0),g227C,g227A,g227L,g227I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227P5_0 : block g227 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g227B5 : block g227 5 0 1=true := g227P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g227 0 0 0 = true)
  · exact (rfl : block g227 1 0 0 = true)
  · exact (rfl : block g227 2 0 0 = true)
  · exact (rfl : block g227 3 0 0 = true)
  · exact (rfl : block g227 4 0 0 = true)
  · exact g227B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K185) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (graphGoal 227) 6 := lower_forest (g:=g227) (i:=0) (hints:=85) (before_sound K185 V185) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K185 6 [(227,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V185 low227 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff72ac9,0x182ea80003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044032080,0x180ca80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe03d528,0x15d8c201fc000fe03f80])),(BitVec.ofNat 152 (word80 [0x300b00500008235028,0x150840060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8ce,0x83211e000007f000007f])),(BitVec.ofNat 152 (word80 [0x410c1160889000d84e,0x81201654a952a54a952a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x691ab3fe000000003f80])),(BitVec.ofNat 152 (word80 [0x8050058002e04804c4,0x2812b33870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x91711,0xa28774000007ffffc000])),(BitVec.ofNat 152 (word80 [0x26026011300880711,0x228300a142850a142850]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0x38038021c01048913,0x424004c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(2,0,121,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,8,82,33,6),(8,0,115,0,6)]
def g123A : List (List Nat) := [[],[16,67,101],[80,97],[96,81,67]]
def g123D8 (j : Nat) := if j=0 then 0x2c6881bf else 0
def g123L : Nat → Packing
  | 8 => (1,0,3,0,0,0,0,g123D8)
  | _ => emptyPacking
def g123I (_ _ : Nat) : Option (Nat × Nat) := none
def g123 : Forest := ⟨123,8,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 1=true := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact (rfl : block g123 5 0 0 = true)
  · exact (rfl : block g123 6 0 0 = true)
  · exact (rfl : block g123 7 0 0 = true)
  · exact g123B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 9 := lower_forest (g:=g123) (i:=0) (hints:=65603) (before_sound K227 V227) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K227 9 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V227 low123 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff801ffffe1fff9ae2,0x181cf000000fc003f03f])),(BitVec.ofNat 152 (word80 [0x450940500441101ac2,0x800f145145145145145]))),((BitVec.ofNat 152 (word80 [0xffffe007fffff8390b,0xb483500003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x160181602800213803,0xb40140c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x39712000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x98020180b082400039,0x3171028a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8bc7903f000000000fc0])),(BitVec.ofNat 152 (word80 [0xe02c0a02c00b824628,0xbc6971c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ac8fc000003ffff000])),(BitVec.ofNat 152 (word80 [0x300c03010c044104,0x428c0410410410410410]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x4010040010000000,0x820820820820820]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(2,0,185,0,8),(16,0,171,0,8),(32,0,155,0,8),(1,0,186,0,7),(8,0,179,0,7),(128,0,59,0,7),(9,0,178,0,5),(129,0,58,0,4),(136,0,51,0,4)]
def g187A : List (List Nat) := [[],[48]]
def g187D6 := limbs80 #[#[0xe3c1243e437695254120,0x5]]
def g187D7 := limbs80 #[#[0xf54950bf59520fe54120,0x42a00ff58950bfd8950d,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c70c871]]
def g187H7 (j : Nat) := if j=0 then 0x8 else 0
def g187D8 := limbs80 #[#[0xa38c2461a403faa1fd20,0x1e851c6121c]]
def g187H8 (j : Nat) := if j=0 then 0x18010032003021100 else 0
def g187D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g187H9 (j : Nat) := if j=0 then 0xb0000001000000 else 0
def g187L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g187D6)
  | 7 => (5,2,4,0,0,8,0,g187D7)
  | 8 => (2,1,4,0,0,6,0,g187D8)
  | 9 => (1,0,4,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 2 0 2 0 0 g187H7
  | 8 => lookupShort 1 11 0 6 3 1 g187H8
  | 9 => lookupShort 1 17 0 4 1 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 1=true := g187P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_4 : block g187 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 5=true := (@block_merge g187 7 0 4 1 g187P7_0 g187P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 2=true := g187P8_0
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
  · exact (rfl : block g187 5 0 0 = true)
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=65603) (before_sound K123 V123) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K123 10 [(187,[]),(219,[16,67,101]),(249,[48,97,33,80]),(250,[64,81,32,99,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V123 low187 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff003ff87fe1fffffa,0x261b1000007c1f003ff])),(BitVec.ofNat 152 (word80 [0xa02805100440020da,0x2011004210842108421]))),((BitVec.ofNat 152 (word80 [0xffffc0007ffe1ff05d,0x3ccb008000f83e007c00])),(BitVec.ofNat 152 (word80 [0x2c0301620280404259,0x3c43000c6318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80001fff20,0xf4791e001f00000f801f])),(BitVec.ofNat 152 (word80 [0x302409801308848020,0xf4780218c6318c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffe00010,0xab842f83e000000fffe0])),(BitVec.ofNat 152 (word80 [0x404812002400090400,0x1842da1084210842108]))),((BitVec.ofNat 152 (word80 [0xe,0x11bac77c00003ff00000])),(BitVec.ofNat 152 (word80 [0x80701c0438110e0804,0x1b8c7318c6318c6318c]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x8020004000100000,0x42108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(2,0,233,0,8),(64,0,171,0,8),(1,0,234,0,7),(32,0,203,0,7),(66,0,169,0,7),(8,0,227,0,6),(128,0,107,0,6),(3,0,232,0,5),(9,0,226,0,5),(10,0,225,0,5),(33,0,202,0,5),(34,0,201,0,5),(40,0,195,0,5),(65,0,170,0,5),(96,0,139,0,5),(130,0,105,0,5),(192,0,43,0,5),(41,0,194,0,4),(67,0,168,0,4),(98,0,137,0,4),(129,0,106,0,4),(160,0,75,0,4)]
def g235A : List (List Nat) := [[],[80,97]]
def g235D4 := limbs80 #[#[0x9822139398595434c110,0x7550d30442b232f32a86,0x89caac6a1aa088760e49,0x822171193a154354110b,0x750d50442b2726c3a86a,0x81c6564cb0c056464e8,0x5282000014a094a]]
def g235D5 := limbs80 #[#[0x4c11054d30441434c110,0x442654c1105d53044165,0x995434417050d1059543,0x54110549504414354110,0x44163541105895044153,0xdd95244176549105cd50,0x54d105d9534416354d10,0x4437459510dd95344265,0x5db5244265c811059720,0xb727c9e6759b576d4d10,0xe5778db364be2f4bb2e5,0x9a12ba83e4f63d4f33c4,0x3d90c158dc2551c155aa,0x285eb286332822b2806c,0x390ec190dc208fc189f3,0x9a09c2ae0b1257c10c6c,0x2a1cc2a22b9a22b1a22a,0x2b1eb1a9543a14c3a1d4,0x2383c1b87c0391c1349c,0x2994ba981c25c6c03c1c,0x2c0ac19ccc01c1c394dc,0x2445c1447c0448c0498b,0xc1d01c2606c04c1c,0x2b12c803416090381406,0xac5026114803b1b8cc5e,0x2f0f83bf1e8e36db2d76,0xa6c359a6512792f93c7e,0x3eaf4799c8e270379b8d,0x805e0a042e0889846254,0x19083400a5400c0148,0xc050159080000000,0x116a0801a4480a020000],#[0x908001d08026108bc8ae,0xb0800065840000000002,0x1010000000000000000e]]
def g235H5 := limbs80 #[#[0xb9d03c4fb014000000,0x8400000000000004850,0x3600]]
def g235D6 := limbs80 #[#[0x549105411050d104c110,0x5951058d105891054d10,0xd4d10d4910c811099510,0x54130595205492054120,0xedb3b58d505495059530,0x76badbedeeeefd7dbe5e,0xfb7d7e9edf6793bdddee,0x9a2a4972860fe7ebf3f8,0x25aa421aea08aa601aea,0x25ea625aa627a8625ea4,0xb7ae011ae0a1ee031ee6,0xf52a4c1ae080ee871ae0,0xbcca9baca906e504aa6,0x2bac42baa42bcca0baca,0x3bae62bac62baa62bae4,0xa26ec322ec3aac43bee0,0x182ca126ea53aca522ec,0x492c64bae0482ec184ca,0xb26ec422ec464ca462ca,0x726ea63aca622ecb62ca,0x822e4886e8726e6726e4,0xf46e0eb6e0db2a4c22e6,0x26ee112ee1136e509aa6,0xb1784b1002d0640016e5,0x2358c32c4a42608b1dc6,0xd5fd6b565414a51a414f,0xb819f2781d26f9b06858,0xa367c9a65a94a438ba1,0xcc5305bf6efb7ac8ac6a,0x4e1f75d9355d0f37ca31,0xffcbe5f5fcaef3aee879,0x8848c943c50981f8447f],#[0xc2c202708b0b98418000,0x3510142a0b823d1e121,0x126a8e1104c493d0b0f0,0x88047d80800ef911df1,0x7811a0100110093b0860,0xeb1bf40491238457e808,0xb16d60226d60222904cc,0x8c911c4925245612499e,0xc4436e188b611c443348,0x2e45a3e430f8c5d18639,0x93ab14ad0a0f219b2200,0x53e429ac50c231b1d798,0xa826c8ac840239100564,0x68350b106c8ed910d685,0x303b412d86981da0ad05,0x1b419a0d]]
def g235H6 := limbs80 #[#[0x10802013c08232b20,0xb00000ea8020000000,0x594138001ed3e5c010d7,0xe000021d030a88948c20,0xc01a90000056a50d003a,0x409f000008e83c968,0x69809aa4a8000089cc,0x994e86c0000001524800,0xa98001d,0x1a20022e0c0000000,0x78034356c9800291c000,0x196067192182c]]
def g235D7 := limbs80 #[#[0xc8252549504c12044052,0xcfbeddfdbbfbebdd4b50,0xd50174c05f201fffefdf,0x84f526058405600550c5,0xd4c61531858863521854,0x29540a26518594616318,0x5032595d952725949952,0xb6244d49115242594e5,0x8a115282d8d13534454d,0x2582496562d814963825,0x5a58d29534a58929524,0xc490c42205000ad81696,0x4dc32cba284901fc6d16,0x5715794b4fd32499103d,0x5e4761cb6ddab679915f,0x657926358a21682dfe7c,0x10038629808e1a367f9a,0x8574758152a32b086261,0x15c03bcc23442878b12,0xd608b7022d608179c4a5,0xa7014f9a04a9c054e02a,0xe05b96184d7cd0254e02,0xe810f9028022010010ed,0x3002201000afe00a0087,0xa0110088040044023f00,0x1da456ca488045a81401,0xd62876914f6c881e9]]
def g235H7 := limbs80 #[#[0x200f0130340020208180,0x26082760801838c0f0,0xdc000f33003528c5d865,0x8b6c8e008f251270757a,0x40d46f9ab490001ca2c5,0x1848ba376b92cf8fa73c,0x703a292428013ccc0866,0x5b74a715ef61d2d9524,0x446cd470200003500064,0xb60e0ca124e000e35dc3,0x92c55070605c15d1]]
def g235D8 := limbs80 #[#[0xea154298720a40443ffd,0x72b1d1100ea594aa9452,0x30244682184756956493,0x84028021981435001c8,0xc0280238807002bc00c0,0x10]]
def g235H8 := limbs80 #[#[0x422018400020100021,0x300000000045e302e000,0x6000000000a4528031f1,0x10c0062000ac00820014,0xd20000,0x1218500030c800,0x50201960053b280109,0x7c38000000000,0x59c50300000018200000,0x742cea600074a908000,0x19800008d00000000,0x1500234000000000000,0x98fd700047b400005140,0x664001408000830e0007,0xdf0066fa2a200,0x7840092000000000,0x15c8380000000020400,0x8500000000000000]]
def g235D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g235H9 := limbs80 #[#[0x45000000000000024020,0x4e821040000300420005,0x2400000000100000051,0x11405586000000]]
def g235L : Nat → Packing
  | 4 => (7,5,5,0,0,6,0,g235D4)
  | 5 => (45,4,5,1179673,85,9,1040,g235D5)
  | 6 => (63,3,5,1572883,85,10,1059,g235D6)
  | 7 => (40,2,5,720906,68,10,1048,g235D7)
  | 8 => (10,1,5,131073,16,8,1035,g235D8)
  | 9 => (1,0,5,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 2 29 0 6 3 1 g235H5
  | 6 => lookupShort 14 97 4 9 6 1 g235H6
  | 7 => lookupShort 18 83 7 9 6 1 g235H7
  | 8 => lookupShort 15 151 5 9 6 1 g235H8
  | 9 => lookupShort 3 41 2 7 4 1 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P4_0 : block g235 4 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B4 : block g235 4 0 7=true := g235P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_2 : block g235 5 2 43=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 45=true := (@block_merge g235 5 0 2 43 g235P5_0 g235P5_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_1 : block g235 6 1 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_20 : block g235 6 20 43=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 63=true := (@block_merge g235 6 0 1 62 g235P6_0 (@block_merge g235 6 1 19 43 g235P6_1 g235P6_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_7 : block g235 7 7 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_34 : block g235 7 34 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 40=true := (@block_merge g235 7 0 7 33 g235P7_0 (@block_merge g235 7 7 27 6 g235P7_7 g235P7_34))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_1 : block g235 8 1 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 10=true := (@block_merge g235 8 0 1 9 g235P8_0 g235P8_1)
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
  · exact g235B4
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=83) (before_sound K187 V187) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K187 10 [(235,[]),(243,[16,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V187 low235 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3f80007f80007,0xf807f8041181934687b9])),(BitVec.ofNat 152 (word80 [0x850a14282828282828,0x28282804100091028388]))),((BitVec.ofNat 152 (word80 [0x1fc0007f80007f8,0x7f800009e020d89f9fc])),(BitVec.ofNat 152 (word80 [0x83060c181818181818,0x1818180094000581a8e8]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe0000000007f800,0x7fa08e01c6e311e3b])),(BitVec.ofNat 152 (word80 [0x2a54a9515151515151,0x51515208800c6e111c31]))),((BitVec.ofNat 152 (word80 [0x7f000007f800000000,0x7f8004f0060703e1fc6])),(BitVec.ofNat 152 (word80 [0x1c3870e0e0e0e0e0e0,0xe0e0e04c0020303e1704]))),((BitVec.ofNat 152 (word80 [0x80000000000007ffff,0xf8000470007f803fe003])),(BitVec.ofNat 152 (word80 [0x50a142828282828282,0x828284400073002c4002]))),((BitVec.ofNat 152 (word80 [0x7fffff80000,0x780007fffc00004])),(BitVec.ofNat 152 (word80 [0x60c183030303030303,0x3030600005b4a000000]))),((BitVec.ofNat 152 (word80 [0xfffffff80000000000,0x7ffff8000000000])),(BitVec.ofNat 152 (word80 [0x40404040404,0x4040122490000000000]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(2,0,249,0,10),(8,0,243,0,10),(16,0,235,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,9),(3,0,248,0,8),(9,0,242,0,8),(18,0,233,0,8),(33,0,218,0,8),(66,0,185,0,8),(80,0,171,0,8),(96,0,155,0,8),(0,8,82,161,7),(0,16,41,194,7),(10,0,241,0,7),(17,0,234,0,7),(34,0,217,0,7),(41,0,210,0,7),(48,0,203,0,7),(65,0,186,0,7),(72,0,179,0,7),(82,0,169,0,7),(129,0,122,0,7),(130,0,121,0,7),(160,0,91,0,7),(192,0,59,0,7),(1,8,82,160,6),(2,16,41,192,6),(24,0,227,0,6),(32,8,82,129,6),(64,16,41,130,6),(128,8,82,33,6),(128,16,41,66,6),(136,0,115,0,6),(144,0,107,0,6),(11,0,240,0,5),(19,0,232,0,5),(25,0,226,0,5),(26,0,225,0,5),(33,8,82,128,5),(35,0,216,0,5),(49,0,202,0,5),(50,0,201,0,5),(56,0,195,0,5),(66,16,41,128,5),(67,0,184,0,5),(73,0,178,0,5),(74,0,177,0,5),(81,0,170,0,5),(88,0,163,0,5),(97,0,154,0,5),(98,0,153,0,5),(129,8,82,32,5),(130,16,41,64,5),(137,0,114,0,5),(146,0,105,0,5),(160,8,82,1,5),(168,0,83,0,5),(192,16,41,2,5),(208,0,43,0,5),(43,0,208,0,4),(57,0,194,0,4),(58,0,193,0,4),(89,0,162,0,4),(138,0,113,0,4),(145,0,106,0,4),(161,0,82,0,4),(161,8,82,0,4),(162,0,89,0,4),(176,0,75,0,4),(193,0,58,0,4),(194,0,41,0,4),(194,16,41,0,4),(200,0,51,0,4)]
def g251A : List (List Nat) := [[],[16,67,101],[80,97],[96,81,67]]
set_option maxRecDepth 16000 in
def g251D6 := limbs80 #[#[0x54540442a8591414c110,0x4418655151501105d954,0x59151501105956454540,0x50110695645454044176,0x5955458540441a55d954,0x58540441a65516150110,0x44195591615011059564,0xe4563501106956458540,0x50110615655914044164,0x6957659140441a35d964,0x50550443a164d6450110,0x4418655141541105d954,0x5514154110a195450550,0x54110595645055044386,0x69564505504417659141,0x58550442a85914154110,0x441a6551615411059154,0x59161541106196458550,0x54110691655855044386,0x6917659550441a25d965,0x61d54443a26617655110,0x441a1591545811065896,0x65954581106158455160,0x581102999755160441a1,0x5d164585604416455161,0x61160443a164d6458110,0x44193e49875911059792,0x60d825d9106579261d64,0x5d910617946097644394,0x65d655855148185e4984,0x6195148197e4d8654520,0x48198589315812069f93],#[0x58951581206596254560,0x58120685655496048198,0xe8d91595604819264565,0x585414c187e4d8558520,0x502975914158130a1d64,0xe49765454061b925d951,0x581406a3925d95150198,0x66164545605019659151,0x61561503a36456558140,0x54297591415815061f93,0x5954158150a5d6550560,0x58150e5d655056054396,0xe898460560541a1dd161,0xdc560543a26118358150,0x541a15977258150e8984,0xd19e8b703f6139360576,0x553aa9754b6a3d49ea39,0x65ab2b995b2ad35672b3,0x4d71cb8d5c5ae1d70db6,0x27de92f2578cba65cb2e,0x62db0cd4d66cb34d873c,0xe8d7333699b2cd8e6c6b,0xa603f0cf647a33c1dd2c,0x32b4c04e6d8040d31181,0xec0e6658157d90297ba0,0x2a6183d9da84b1760b62,0xdc5b5d98aa98513276e2,0xc8bb105fb10d42ec316e,0x88f47b51cb7623a95d86,0x97ba232b4c455ecc7add,0x826bb6e4e6e5894ccb12,0x62ec566e58a1adc933db],#[0xc64e6d8c59da96b1762f,0xeed0dc7db9aab8633530,0x8fa3da1e53b73a736870,0x1daa25bb54f234e993ec,0x2821b24a576a90fec51b,0x3ba42e7468275d54c8ba,0x5adf4ab03ecd583daaa0,0x766cc9ed5907d9ae0bb3,0xddee8db33d9b533b3686,0xed1885da3043b45f0aea,0xf0cdcb959b1741768e02,0xd9bc7594805f66fcbecd,0x20fb2821f66f43ecdd87,0xb1862b6f1076e612cd8c,0x31acb1846e228adcc351,0xcb212ece53eb2c789659,0x2908018034000fb296fa,0x861f8711a05b1383f0cc,0xc8300b62b8a627896238,0x9404f93c4e8380d8340,0x4f51d3f4d92e48519445,0x9461d7f5dd6f59d5f55d,0xd9745c9705b96c5a4671,0x1984609805f97c5e9785,0x6396e5392e438da29886,0xa3a6e93a2e839ee739ae,0xe3b6ed3b2ec3aeeb3aae,0x407006801f03beef3bae,0xea11b07682341645f427,0xd600dc1001b308e82203,0x45642010040081041180,0x9a08056823410e],#[0x10100000000,0xda0800000000000004,0x1,0x558400022c2,0x0,0x1d61cb08]]
set_option maxRecDepth 16000 in
def g251D7 := limbs80 #[#[0x5d9414c110591414c110,0x591614c11058d614c110,0x645644c1105d9644c110,0x649764c110a61644c110,0xa61764c910651764c110,0x59151501105515150110,0x61951501105d95150110,0x61954501105d95450110,0x58d61501105516150110,0x59561501105916150110,0x64d61501106156150110,0xd8d61501106556150110,0x5916350110d956150110,0x5956450110e456350110,0x61564501105d96450110,0x64d64501106456450110,0xe5564501106556450110,0x61565501105d96550110,0x65165501106456550110,0x64d76501106616550110,0xe5176501106557650110,0xa5985501106598550110,0x655865011064d8650110,0x65f6350110e498650110,0x65365501105db6550110,0x551415411065f6550110,0x5d941541105914154110,0xa1941541106194154110,0x5d95254110e194154110,0x5d954541106195254110,0xa1954541106195454110,0x58961541105516154110],#[0x59561541105916154110,0x61161541106096154110,0x64961541106196154110,0x66161541106516154110,0xe116154110d916154110,0x5956254110e196154110,0xe6162541106616254110,0x5d964541105956454110,0x61964541106116454110,0x65564541106456454110,0xa6164541106616454110,0xe616454110e196454110,0x64565541105d96554110,0x65165541106496554110,0x6497654110e516554110,0xe5576541106517654110,0x59584541105958254110,0xa1984541106198454110,0x65186541106498654110,0x6628654110e458654110,0x5db645411065f6254110,0x65f64541106576454110,0x5d965549105978454110,0xa6176549106416554910,0x65176551105978054910,0xe6176551106617655110,0x65987551102598755110,0xe453258110a598755110,0xe4543581105914358110,0x5955258110e614358110,0x59554581105915458110,0x61554581106115458110],#[0x65d54581106595458110,0x55161581106615458110,0x59161581105896158110,0x58d62581105d16158110,0x5c962581105956258110,0x60d62581105d56258110,0x59163581106156258110,0x5956458110e456358110,0x5d564581105d16458110,0x64564581106156458110,0x655645811064d6458110,0x64565581105d56558110,0x65165581106496558110,0x6117358110e516558110,0x64d74581105957458110,0x65974581106557458110,0x6497558110d957458110,0x59582581106517558110,0x61183581105918358110,0x5958458110e458358110,0xe4984581106158458110,0x5d76258110e458558110,0x66175589105d76458110,0x58f8058910a617558910,0x61d65591105978058910,0x655745911064d7459110,0xa6175591106617559110,0xe617559110e597559110,0x655765911064d7659110,0x6058059110e517659110,0xe45835911060d8059110,0x655875911064d8759110],#[0xe498759110e418759110,0xa61655c910e518759110,0x619855d110619835d110,0xe41865d110a19855d110,0xe51865d110e49865d110,0x60d825d910662865d110,0xe0d825d910615825d910,0xe41845d910e51825d910,0x617825d910e49845d910,0x64f845d910e17825d910,0xe17845d910657845d910,0x66175d911066175d8910,0x5d985d911065576d9110,0x59561545205896154520,0x619625452065d6154520,0x619765452065d6554520,0xe4d865452065d8654520,0x58531581206456554920,0x66131581205893158120,0x58951581205855158120,0x60551581205955158120,0x66151581206595158120,0x60d53581205955258120,0x58d625812054d6258120,0x60d62581205d56258120,0x59563581206156258120,0x64565581205d56558120,0x64d65581206496558120,0x59581581205898158120,0x61d63585205958358120,0x65d655852061d6558520,0x61d8358520e617558520],#[0xe4d855852061d8558520,0xe4d81595206098159520,0x591615053058d6150530,0xa1d6350530a1d6150530,0xa5d6450530a1d6450530,0xa1d8650530e617650530,0x6116354130a5d8650530,0xe6164541306616454130,0x65186541305958454130,0x60541581305914158130,0xe614158130a5d4158130,0x61564581305916358130,0x61181581305918158130,0x6137158130e498458130,0x59774581305977258130,0xa5d6458530dd16358530,0x5977458d306477258530,0x65a8759130a1d8559130,0x661765454059563dc930,0x5855158140e497654540,0x60551581405915158140,0x66151581406595158140,0xe4563581405956358140,0x64565581406456458140,0x591815814064d6558140,0x60d81581405958158140,0xe4d81581406158158140,0x5918358140e518158140,0xe4583581405958358140,0x5978158140e518358140,0x61d63585405d96358540,0x61d65585405d96558540],#[0x61d83585406158058540,0xe4d855854061d8558540,0x65f83585406438358540,0x65f85585406438558540,0xe09815d9405db8158d40,0xe51815d940e41815d940,0x60f825d940e41835d940,0x64f825d940647825d940,0x661765055061d7650550,0xe1d7650550a617650550,0x61e7650550e617650550,0x58541581506427650550,0x59541581505914158150,0x65d41581506054158150,0xa5d41581506614158150,0xe5d4158150e594158150,0x5c56158150e614158150,0x60d6258150dd16158150,0x64564581505d16458150,0x589715815064d6458150,0x59571581505917158150,0x5d171581505c97158150,0xd917158150d897158150,0x58981581505917358150,0x59581581505918158150,0x61181581506098158150,0xe558158150e518158150,0x591835815060d8258150,0xdd183581506118358150,0xe498458150e518358150,0x593715815058b7158150,0x60b71581505977158150],#[0x65371581506137158150,0xd937158150d8b7158150,0x64772581505977258150,0x61373581505937358150,0x59781581505938158150,0x61d64585505d96458550,0xdd96458550a1d6458550,0xd9171585505917158550,0x61d745855061d7258550,0xe457658550e1d7458550,0xe4d8758550e458758550,0x65a8758550e558758550,0x65f84585506438458550,0x65d625c55065f8158950,0x609815d950663625c550,0xe4d815d950e09815d950,0x60b815d950e55815d950,0x653815d95064b815d950,0xe45879d950647825d950,0x65187d855066174d8550,0x64986dc55064587d8950,0x5d5645c560e418159160,0xe15655c560e11645c560,0xe49745c560591735c560,0xe11645cd605d3835c560,0x5d3805cd60e49745cd60,0x5d7825d1605d3815cd60,0x653835d560653815d560,0x65581dc96064d81dc960,0x64d81dd16064585dc960,0x64585dd16065581dd160,0xf8fe8df87f64185dc562],#[0x9de9be97e97d96f95f93,0x6fa5fa3f9fc9fa9f69ee,0xfa9fa9ea7ea7da7ba77a,0xafaaf6af3aeeadeabeaa,0x37b35b2fb2eb1fb1eafc,0xdb5eb5db3eb3db3bb3ab,0xb9cb7cb7ab76b75b6eb6,0xbabb6bb4baebacb9eb9d,0xfc3fbf4becbdcbd3bbcb,0xcd7c7ec7dc7bc77c6fc5,0x1ed17cfccfacf3ceecde,0xed3dd3bd3ad35d2fd2ed,0xd6dd6bd5ed5dd57d4fd3,0xacda6d9ed9ad7cd7ad6e,0x7decddcdbcdbadb8daed,0xe6be5ee3ee2ee1fe1ee1,0xb4eaeeace9ee9ce7ae6e,0xceeaedceceeccebcebae,0xf2ef2df2cf1ef1def8ee,0x8cf6cf4ef4cf3cf3af35,0x2facf9cf9af99f96f8ef,0x384013faec00fccfb8fb,0xb0c0a855d8146dd2009d,0x5942068d205dfd7605bb,0xd2849c985091a34c1088,0x96071a34818706142669,0xec234d5d842d4bb07535,0x18670abb0cd357618b42,0x20f9fd761a3bf0c33776,0x52498b4a48316987d10b,0xc6a4c6587663d2105c16,0x10a98bb171a17636262e],#[0xa25439544b12c4777f5d,0x3e302c8794c655564bd2,0x904de552098cb9f53597,0x3442d228131955610f4a,0xd097a1780ff48964c5d5,0xeaff29164c656383fd0b,0x4236863c9eb1c8131958,0xa3ed2e092d9590b3b0b2,0x93165c08fb4b834d652f,0x262cb8515e93123fd25f,0x7baa000bab2ded3594c3,0x954c015daa801c3f4801,0xb3a4038c34c0681e9008,0x8b4a0b91594165fd1020,0x66a416cccb02e1d7605c,0x4cb035f3a206c3f480c6,0x9640abb30c118e590229,0xb0c10916542122b28423,0x614251cb2848f1a6083d,0xd284a39950947346127b,0xa809bb30c1379614271c,0x4c14766a0271cd204c79,0xd834ccb2068f7a30b0f7,0x20be05760ca530c1a5c5,0x9072d32c0e866941cb5d,0xa1e6664c3cf5d103d6ba,0x43e79d287999950f3db0,0x6de1850dc0aec1f3ce8,0x1040aec206e5d83b02bb,0x1c81e8c3902d1870b3a7,0x48ccca09207a50e40b4a,0x8e057612a53302479614],#[0x33f74a2281e9044d8bb0,0x647e904c93d10992ba11,0x4b5d20ca07a4182274e2,0x86ba4150ef442a1ee845,0x8d3482b1e6845629d38a,0x26a45628d38ac65a515,0x55d289cb3a4139874227,0xbba31418742282c69452,0x4b2a2e4964c5c59d20a0,0xee845a35d20b07ba1162,0x2c30cc53a7168d7482d1,0x5a51a48aca3491a18672,0xf0c347b618690ebb0d24,0xe906af7540d1eda81a3d,0xd20dd2b961b2532c3687,0xa81b9834e373b6946e78,0xca3f4ae58701ad48dc79,0x948b1ab2909d9861fc6a,0x30fa45941f48ac83e8d5,0x5201db4c3e79e187cf2c,0x84076e1880ecc3102356,0x80ecd410235a5204730,0x125e56524c6aca4376aa,0x20c6b44418d5948c3cd3,0x471e690943dd211235a4,0x7477d08e95ca91c9df4a,0x3437a1263f2ec4b79e84,0x2bf4a680769c9a1ad09,0xb57658770cd20edf9763,0xaf3d08f0efa11e2bf523,0x865a81e9534e3d3b6847,0x25530524a660a4caca94],#[0x7e5d8a6fcbb13a057628,0x35d2145fba527c0f484f,0x33a22a06f42541a690ac,0x6b425718698aa0fd3950,0xee94d20ed395c25a52b8,0xdd0989f97630abf4a6b7,0x1a7318cb4a631e684c63,0xb24596c5d8d8f2d09b05,0x5d8b6fcbb16995942cb2,0xd1161f9a22c1574e5b7e,0xa42ebf748587e690b0fd,0x4a5e2fe88bc55d2974b3,0x50cc1ad2198a9a42f957,0x9947ba1320f348664a6,0x4338a74e651de88ca3dd,0xc838e5910708baa100ba,0x50d08baa14c1a7419cb4,0xa20e7a143c6b427b30e9,0x4641b448a39e8516fcba,0x7a8e684f0fcbaa8ce7a1,0x1ac8b223821a63d06b42,0x9991645317f449b815d1,0x2b0f28a4815d14894c22,0xe8e684f8b4cb9f077a25,0xeaecb9f5e1853f44aca7,0x191a14003f4e803be84f,0x29f4c815329902a7d3a0,0x2ce952102b2a4037a141,0xc8caa4d919349bf2ea8f,0x5744a1cf429439e9526,0xb2a90816152102d1a42,0xe6552302d224605a5484],#[0x1d3a54d7a4491cf42927,0x9954e40b489c28e993a5,0xacaa92ce913e51d3279f,0x5d54e92c2aa56d7554b1,0xc925caba44b0f742a87e,0x754cbf2ea98646512ec8,0x48967e6892c51d3a65f9,0x915451d3288a3a650bf3,0x89b9e5a1380734c090d6,0x6378a3406f692a0dacac,0xad6b5d9603dd0abc39a,0x55a21d22b44fa1568a74,0xab84da1570a340ae0fe9,0x619ff4ad60fe95ac1ed2,0x7254654e259d01c439a6,0xe489d01c83ba6390a740,0xcc03a6391f74c7242e88,0xa9f32c7412688e880d21,0x614680ec25d11d453a03,0x83dd2aec01a93b1f72c7,0x549765eacae8bd1ee857,0x9174cb322e996486c3af,0x14e81680ad22d83fa558,0x1fd2ad04ba25a09f42b4,0x4da15a8a340b503e9968,0x2b4aba036996e1ed2ad4,0xe957045d22e09fa15c0,0x9d1ae49fa15c9134aba2,0xb946037f24c022e91724,0xf28c142e4d8284c9b05b,0xe817c85cab05099560b6,0xd2af843a45f09f42be14],#[0xa05f8834ac20ee997c1f,0x48bf11e8d7e27d0afc53,0x95ae1fd2b5c3ba65f887,0x13103ba86c34f4ad93fe,0x1630a340c612e898a25d,0x4c73ee598c20d23184da,0x592b1ca3216b9463adf2,0x3350394658074aca0569,0x662070ace406159c81ca,0xcf3f655a423d1b4447a3,0xa00ed2b3d6b9467adf24,0x4c41a46aa170ad042615,0x1a0f46d411e8da81fd2b,0x463659c91eb1b9241627,0xd20b139827a572b1b30e,0xe356574c82c4e98d595c,0x31b30e763659cf18b2b9,0xbe8dd617d1baa31a274,0xeac2be18f937c3ab06f8,0x31a1762f72af963e55f0,0x62caee8f58ddd18d1bb2,0x8e95de71d0bbce1a6774,0x1d0bc4e1a87747b06ee3,0x3a1791c74af175615e27,0x72af38a595da71d1bc8e,0xe8deac6c93d57b957d2f,0xbabdd8d937b3f2eaf537,0xa26dbeaecdb8b595b4fc,0x48dc7d69db6facbb6e2d,0x85bc37d1b74a7a56e15f,0x3b8505977088f46df29e,0x57008748e013e85c082d],#[0x8ff22e91f61dd33803fa,0x5fa41d2bf08ba47e0874,0x40105878081b4cfe27e8,0x81a4727023ae8dc421d2,0xe8a5961a82c3c0d5575,0x22fcbb44025a58786745,0x52069789472c9131de8a,0xc17f451b0869a2a60d0c,0xa35e922e3bd146587948,0x892c2c696f758d31acb1,0xa02a782c050f0582a1e0,0x16b4307066a60c4ed341,0x2b6861244d3420ada184,0x26d0c2c19a1851134d09,0x9da18f89b430c0e69a16,0x1f43230e69a441cd447c,0xd596531cb24a63964938,0x7d1ca985989430b2d288,0xd6499857492b0be8e561,0xb0b31615926a35d24cdc,0x6966cc2b2cd9879598b9,0xd24ec6ba49a2f72b320a,0x649caf72b2c615925ae6,0xcb3a61e566ee6c2cdd85,0x8e5cbdcace029a59d30a,0xa4bcdfa3979af4b2e35e,0x69321331266165260c2c,0x72514e824a84d4499098,0xa7839d1d003ba69288f4,0x5104ba2a0937453d26e8,0x9f207494542e8a8a8fd2,0x4320e967e4dd14fc9ba2],#[0x8e8fd25184ba2a120b0f,0x284ba2a4207494742e8a,0x4a1727495ae5294dfc15,0xd056969685cad25b794a,0xc84c9d384ba1a6b7f414,0xc4ba5a72132b4e12e8e9,0x83b434c5ae529825d0d3,0x8d596b51cb256a3964ab,0xbccb5660697ac40b2f58,0x7997acbf32f595ee5ab2,0xf331595ee5eb2fd4bd65,0x8e9ab60ed3d797b98aca,0xed4d74b1a4ae983435d0,0x9a8af8434d5f09696be0,0x34d6009696c013d2d700,0x596c460d0d8a3565b084,0xb2da8cda5b641ae5677e,0x65b599b4b6d815d2d0fc,0xcb7c33e92d267d15a5f9,0x96fab4ca5f5f965bfbf2,0x2e05f965c017f45807e6,0x5b7bf3497e7e68afcaeb,0xb7061e52e0e2b2dc97b9,0x6e8e2b2dcc77a2b9af72,0x62025a4ba99f49715e59,0xc23f3438433e96c6e6ba,0x87815d2dce2b2dd9f9a3,0xf2bdcaddd8794bb97f45,0xe9c565bc0ef457857e56,0x22f32b665e656cabcb2d,0x314682a61dd35422595b,0x429d05440ba0a88734d5],#[0x51187ab033435414682a,0x1934b8f805d31c1dd355,0x276871a4fd0e2847a3c8,0x6d4e3089a4c6117498b,0x3da5c90a3419211e8f22,0xff4b9901e97328dd2e60,0x5e572aadcae5019a4c99,0x5d06980fa4cb80b49964,0x7a5ce03f419b14e834e0,0xf4ba842e8b3429d06a40,0xe4f3a03d2e900ba0d187,0xc267d5795cfa0f279e41,0xa0d082349a041e133e82,0x4ba414e83440fd068c53,0x8b609dca6b801a4d2827,0x2ebc8ba4d58bb4bac12e,0x5dc0b349ad42e175ea2b,0xbba11e8f7423d1ee43fa,0x76225d16d0bfa2d987f4,0xec94565d90bb4bb11768,0xda89743b5086975485c2,0xbd11e8f781fd2eec4ba3,0x6e05d06d83fa5de88f47,0x804a00009745be02e83,0x81be05f813604080c402,0x3160b58296097022007a,0xbe125044c0ff03b20da0,0xa173059815b052213d84,0x1e407401bc069e197061,0x4a08e0226885620507ca,0x48a8a2938a0826f09702,0xc0e2f58b8c2d50b1a2b],#[0xdce3618d463400cac319,0x803d00ef03ad0e6a38b8,0x6429909641290143f08f,0x45f115a452911a43e10d,0x9a122c48411ee470119e,0xd13444bf12cc4a7927e4,0x143450113ee4f493a24d,0x51e53e94dc52d9490515,0xd257095b256895705529,0xe59e163e58b95fe57895,0x5ce171c5be96d05ac168,0x17d45ea979a5da1748,0x71904631988461018246,0x1a3668319e866b998065,0xadc6af9aae6a01a66693,0x5a6d09b326c51b046bd1,0x26f49ba26e29b7a6da9b,0x7199c4870e1c207009be,0x4d9d1a73e1cdc72b9c7e,0xf1dda76e1d8c75a1d467,0x9e7c79b1e3c78b1e1c77,0xee27b49ec27ac9ea27a4,0x847d71f327c49f027bc9,0x48011ff47f91fc47e91f,0x829208a81a205880ea01,0x4fa120844210083720cc,0xca1d687021b0868217c8,0xa2928a0a272892221887,0x3528cf232c8ba22ba8aa,0xca8eea3aa8e6a38a8dba,0x491aa45090aa4088fe23,0x93a24ca92ea4aa926a48],#[0x57a54894c25209442500,0x925c896e25a8966256e9,0x26ce9a32654989261497,0x8229f7a7889d8a70c9bc,0xcca2f2896a202860a10a,0x8a542932a48a906a3aa8,0xa8faa24a7aa9a4a5e296,0xccab0cab8aabca9caa58,0xbabdeaf3abaaae2ab64a,0x2caab232c64b10ac1aaf,0xd80b572d3eb412ce4b32,0x5eb8e2dfcb792dd4b692,0x2bc0aedcba8ae92b9e2e,0xbf52facbe32f78bd3af3,0x3eb0d8c2d3072c13302e,0xeb196c5c3150c4cb116c,0x323ac86b1f8c7a31d2c6,0x34ccc732e4caab284c99,0x50d0eb41ccf6b388cdbb,0xed4734ecd28b472d1834,0xd6c359ed633562d50352,0x86b608d7db5e4d74b5c0,0x236b6da9365ad92b638d,0x3758dceb72adc636e6db,0x7bcdeb379ade2b778dda,0xa0e203860e103820e003,0xe4bb91ce42b8f8e3438,0xe663986e5d3962e54394,0x943a32e81b9dee6f39aa,0xc3b02eb8babcea7ba82e,0x3becef73baeedcbb62ec,0xcb0f25bc76f15bc2cf03],#[0x42f4c3d1ef403ce0f33b,0xaf6abd9af62bd7af583d,0xf943e3af86be0af7abdc,0xb73ec2facbe92fa0be72,0xabf5afcebf1afc2beecf,0x3fe4ff53fa4fe53f7afd,0xd9023406b0104014ffd,0xfd06d4185055c12703e4,0x30b1c2a70a1425b08841,0xffc3c30ea43710cd430,0x3bc4d712fc4a7117442f,0x845f716e457d152451b1,0x46e11abc69519ec64b18,0x7e91f2c79b1d7c7371bc,0xf323448b3224c861205c,0x72614973254c92124448,0x2924a2b28249eb27249a,0xba4ad92adca972a14a67,0x44b812d84b3b2cacb092,0xcc47309cbf72f64bb92e,0xce53354cb73254c77315,0xcb36acd8134dcd1733d4,0xd38f4e2d3874e0d37acd,0x3b84ec13a84e8f397ce4,0xec4f933d9cf293c64ef9,0xed07b418d041407cfd73,0x519d461d13343dd0cb42,0x23748651fb47651c946d,0x414c953034b9d2af49cd,0x550153d34ebd39f4d7d3,0x533d4bd526d479515d43,0x5fd55f553d52d543d4f1],#[0xfd61d57ed5dd56fd5a15,0xd6c15a8569159bd64f58,0x7835d457375c9d6f75b9,0x13600d7f35f157b55e4d,0x9635d8ab623584d60f58,0x6685977655d937646590,0xa0da6d6935a2b674d9b1,0xf5add6b35abd6a8da936,0xdb8d6dcdb336c8db136b,0xc9f71d5c55708dbf96f1,0x8f7575d3f7455ce972fd,0xd795de1977cddcb76edd,0x7c55ef37b75ec97aade8,0xfe0217ffdfcb7e75f4f,0x9614984e60ed82c60758,0x626b88761c7869618185,0x31b8c262ef8b762ab8a2,0x8d8df63638d4633f8cb6,0x7902e3fb8f7e3cf8eae3,0x927e47f917e44f90de42,0x49650593d64e593064af,0x9e59595f656b95665499,0xe60b97e65e1973e5b796,0x69d99e6669992e62b986,0x219c166f59b566c59ab6,0x79ea67999dde75b9cc67,0xa15e827a01e7f79f9e7d,0x3de8dba32e8a9a21e867,0x66947a4de927a45e907a,0xe054032001a646971a5,0x6f0613400221c03005e0,0x90136a1c03400c06942],#[0x1c08a42a40f70601b826,0x780170406c092d04b072,0x3770980e42722e80e08,0x431de03b0861c61e08c,0xec2702790204807004af,0x6ec0006140080206aa1,0x890c82a830430a2e088,0x302b02e01000a01fb05d,0xb02004046147908f0bb0,0x3a62e04540fa2f11ae08,0xda03306504e0a437c260,0x51f82fe07e04085d0a04,0x26f0882e02562e22e224,0x881503002b21e02370a8,0x9402ce0300e07291a12,0xa20560105401c006148,0x4609c00008e0070b2053,0xe2f42ea0ad0607a21a01,0xa11b509d07415a2642e,0x812c10440208e217505b,0x56c0f80241683841530,0xbc04854438062c0c058,0x392e41080c7068106043,0x209303608125a07b0717,0x1fa0ab0410c702626065,0x607853650c328d0b8231,0x50614483a61be0004033,0x2583a27320303a800c3b,0xb01409611e13d6020290,0x821d0460380d12d90a90,0x7270403c21fc2e50a508,0xd022a05805404042b0a1],#[0xe0632492e04fa0040b41,0x34a09e09c08c08c1e20c,0x607ce05a08a271197024,0xc0a20b60a40dc0a30845,0xc60a82381803842de0a,0x93e4cca23811cc2e8171,0x4202d079a12d278a0f3f,0xff822265ec03d8f5811a,0x7d0d12ed4a29d4fda458,0x4284efb20b207aca4c89,0x87c021669d4fda45c7ca,0x3a7032215116dcc50a0d,0x47fc02132842deb09333,0xa15ceaa2e7a0183e7ec1,0x28b27d064c5c173a6210,0xf420bf468a101e000314,0x50b98c3e05d66162c9,0x1c8c82f92a68b0aaff62,0x67ca054213ee141a163f,0xccbdcbdc29969f896c84,0x4a88f2667a1548d87daa,0xda890837fa12a238dfe8,0x1b0fb559940ff644577d,0xc3257e391926c6fb1a9,0x51bf1a447797a0542807,0x311f64cd524bf07d00a8,0x8402bb3f109997d3c0d3,0x1a86036daa3a4d732ba,0x502a913be12646707e4b,0x809f5450a9df093239e3,0xa1940f19f09c01a2f09e,0x4176141f0541cb6f0ab2],#[0x23c30de1f986c2006653,0xbc131e098f0403f62b0a,0xe9851c3027bc173fd446,0xcb0e15df0a2bba1a4327,0xe5d16ad3611dd6e99525,0x91e8515219604ef4a8a2,0x61620cac4356c4d19dd0,0x79858bdee824cd8bed0e,0x5c29604000000013a66c,0x33e42a42afd088300c16,0x82011b0cb7841a305774,0x72517bc20800018f8573,0x422a281df089b0ac6855,0x7fb13357c3886447cee1,0x2a6a3ebcd4437a134781,0x41b11521c64c16c68597,0x8000190cd4200a9a5853,0xa8b504000003504025c0,0x4200643f6874e84018f3,0x5b0c4c9c26dc9c2321fb,0x1406c4bd42002d867bc2,0x6dd09cf056782b755,0x2908053ab418,0x8c16dda892e840000000,0x42e0e5d0f1d0cb,0xc175857782014685beb1,0xea357020000bda100532,0xad81a420001deb119e97,0x400035db057607458d60,0x1bd134909240e880350,0x88000000003610d86908,0x8bac30fa0a8bc20197ca],#[0x1a832e0400000290d8,0x1264a200603a82000,0xd60db1803de95126c200,0x3374297ad88c27d81351,0x4beb60adfcb9831c2a6c,0xe865f8842843be539309,0x8007462603b7438e076,0x1a832e04031810d86dc,0xf21a8f8f70c152137704,0x111cf4a922c35618b0f1,0xbe18f1ac15bf20b1ac16,0x20000e85894e871ac117,0xcbcc155784dce0b8e1a,0xbf0c51e5d0f303ce06dc,0x378b1d66c559b11e222,0xb02ceac4654e951ea080,0x58f1c4145f6428c01604,0x16ae0a020d1828d84395,0x1238100bed7719434a8c,0x2e847891a7bf09196d84,0xb6105a7428e043610d85,0x2705e78201484c84f123,0xb06d931c4101d093ea0b,0x14ba129a9d17d81351a6,0x7bf091961fc806770b56,0xa91ef4a880200c071c0a,0x3c20100f6db615578cf4,0x80402000100ebb60ac,0xc7e44a900003a6840201,0x27b2dc28b42010081,0x7c200004000200016e04,0xb837382074207420a721],#[0x402eed04071f441743a,0x4020100804020001008,0x7f6862fca297982b8f08,0x704a1b17da10d8759030,0xab28c01563b853df10f8,0x105d085d08025d2a223c,0x18b43341a3a1a3a1f0bc,0xc45a68402018b4347420,0x4e844e844e84000002,0x2870400021782c078704,0x97077704021c0802d040,0x800048f961002d040003,0x25f7868dd452fe416ce0,0xc263b945d74257237265,0x575215f5d10ddda2f913,0xde082f119465e3155f67,0x20cebd63a3eba189e0f1,0xc3af1d90675eb1d1eb9b,0x5eea2b3dca2b3c84a8f2,0x2941941941e287957521,0x8e1d7e78c737328befaa,0x9058ec8285f81987ea97,0xf1c63cb0e584afae8b1d,0xda3e6c8203ef34d4800d,0x737b45ae06c797080fb9,0x76e84b2bec797fc031a4,0x5b66b8401668743c38e0,0x69783a9e1a5e0805ae8,0xeb81d703ee06a783ee,0x1e783cb82015bc16ba1,0xe7435a6c401e743db588,0x33a100f3a1e1e4c2db43],#[0xd8f080003381b1e0c9a1,0x878a34407dcb9ba49ba1,0x800000005af07f7066e,0xa831743e74201fbd8a20,0x5dea82b911db86002743,0x1e19bc2988a420ec5b68,0x880026d02f0cc878bc3c,0xcb578a15cd163a3b39a,0xce079bc20080990d21b6,0x37287c28d8cdb9a3e703,0x703cc0e2f07981cb4b9a,0x88f0b1b6200c50182c36,0xb3c22bc115e0e457d160,0xfb81f703dde10094f07,0xb81f70393c15ba100a9e,0x15ba100ade0f87872d0f,0xf2c2004e6c5c3820193c,0x66f040007e58534100fd,0x1807a2e08000357ae100,0x96c2832a8b6d080e901e,0xe4829142adc15702018b,0x850def4b012974782000,0x458400018089d0ff7,0x4b486b70c00018089d08,0xcd05df28631bd2151c58,0x1429734148a1767ed8e5,0xb819375113c9052e3829,0xb1c60801dfa82d1cc616,0xea2ab8395c8dd879c58,0x5651ecf0690a03ae069c,0x92e251632736a2854b9,0xa3d7283a702bbc101e13],#[0x9e4d2416b874706aee51,0xe0857c3cc0f30200b667,0x5dd0dc2b9c16bb78a5d9,0x1009efbb092782ae0652,0x8045840201008040316,0xd84003610010f87dc,0x7c20100fdc1fdc100d41,0x4020029f0fce0800009,0x3a8201d410000ea08,0x800b7c2016e07e70400,0xce94401cc0802dd0806a,0xe9958401cbc10d86,0xc1c1c1002db1c2ddc100,0xa60403978223,0x1b383a820100]]
def g251H7 := limbs80 #[#[0xc00090604c0000041040,0x170000000000502402,0x8c8000000000000,0x10e000000000000000,0x0,0x21e8009780000000000,0x0,0x110400000850000,0x4000000000000000000,0x806050000000000000,0xa4000001114000000,0x0,0x0,0xa5916000000000000000,0x954000006,0x7af1510c624000,0x400064655809c0000000,0x2a000000000000000018,0x3,0x0,0x0,0x1858000000,0x62e00000119800000,0x87c0000000000000,0x68d7240000,0xca200000000000000000,0xf4c0051500000000000,0x1c000000000022380000,0x71f00000000000001c,0x363800000000,0xc6af200000000000000,0xd28000000000000],#[0x436000000000000,0x406000,0x25763,0x91c0002660c0000000,0x0,0x388800f5000000000,0x22a8000000000000000,0x44800000000000000000,0x14314329800000000,0x8040000063a00000000,0x10fc000000000000000,0x0,0x20280085ed4800000c08,0x63900000000000c3000,0x0,0x1e98000,0xc0000000000000000000,0xa,0x2148000000,0x1a7000000,0x0,0x0,0xc5a000000000,0x615000,0xc760000000000000,0x19000000118000000000,0x340005d8,0x0,0x0,0x0,0x122000000000,0x388],#[0x0,0x56434000000,0x195c00000000,0x8100021e00000000,0x1080048000000000,0x420005d7be000000000,0x6800000000,0x142c0000000,0x0,0x0,0x3400,0x6d9100,0x0,0x10740030e000,0x92c0000082400,0x7d20000000,0x0,0x2c600000000000,0x0,0x23c005080000,0x49a0014800042486e000,0x9307800,0x0,0x298bd0484535970000,0x225288000,0x3a4f0000000000054000,0x1283e002058000010460,0x12700044a000005,0x3df800c540000060e,0x2400000000000000,0x4a900000187800d200,0x258000002de800660000],#[0x1290000004b400,0x104eeb0000000c00e00,0x79b000000000000,0x110c00000000,0x0,0xc28000000000000000,0x52f000000000,0x83c00000,0x133c0000000,0x55e2cb64001110000000,0x1a2b1304d000001,0xc0600000]]
set_option maxRecDepth 16000 in
def g251D8 := limbs80 #[#[0x4c11050530441214c110,0x441644c11058d3044161,0xe1130441864c1105d930,0x4c9105d932441624c910,0x443874c910e013244186,0x58540441545011054540,0x50110591404416350110,0x44185501105d94044165,0xd9540443635011061940,0x54110549504414154110,0x44162541105855044154,0x5d950441655411059150,0x54110611504418254110,0x4436254110a195044186,0xe19504438454110d9150,0x54910595524416254910,0x44380549106195244176,0x4c96044187551105d954,0x58110549604414358110,0x44162581105856044154,0x59560441645811058d60,0x581105cd604417258110,0x44182581105d56044174,0x61560441845811060d60,0x58110d91604436258110,0x4438458110e0d6044365,0x595624416358910e1560,0x589105d5624417258910,0x443805891061d6244176,0xe1d624438558910e0d62,0x591105d1644416559110,0x44180591105d96444175],#[0x61564441835911060564,0x59110e0d644418759110,0x443855c9105957244385,0x61974441855d11060d74,0x5d110e1574442865d110,0x441845d9106097644386,0x5d762443845d910e0976,0xd89106076244180d8910,0x44175d911061f6244183,0x6076444180d91105db64,0xd91106176444183d9110,0x481764c5205893148187,0x59551481625452058551,0x54920619514817654520,0x48176549205955248163,0x5456048131581205d953,0x5812054d604815258120,0x48163581205896048161,0x60560481755812059560,0x58120615604818358120,0x48162585205496148365,0x5d561481655852058d61,0x58520615614818358520,0x481635892054d6248187,0x5956348380589205d562,0x59520e15634838158d20,0x48182595206056548175,0xe0575481875952060d65,0xd8520e1576483815d920,0x4c161505306036348180,0x5d9414c1645053058d41,0x54130a1d414c18650530],#[0x4c16354130549504c132,0x611504c1655413059150,0x58130485604c18654130,0x4c14358130505604c132,0x58d604c1625813054960,0x58130605604c16458130,0x4c18558130611604c182,0xdc9604c37158130d9560,0x58530e05604c37458130,0x4c37258530591614c163,0x591634c38358530dd161,0x58d30e09634c37458d30,0x4c181591305d9644c384,0xa1d644c1875913061564,0x9d930e11764c3825d930,0x4c163d853061e764c183,0x61f614c183d853060361,0xd953060f654c374d8530,0x4c186dc53058f714c187,0x607724c165dc93058f72,0xdd13061b744c165dd130,0x4c9761d93261b754c365,0x61b704c962dc1321d962,0x58140545605017654540,0x501645814058d6050161,0x60d60501815814059560,0x58140d95605018558140,0x501655854058d6150381,0x60d6150180585405d961,0x5854061d615018558540,0x5038358540d956150363,0xe05635017658d40e1561],#[0x5d94060d76501815d940,0x50187d8540e097650381,0x61932541624c95061f63,0x505505d941543874c950,0x54287505509d94154187,0x505605413258150dd941,0x58150589605416158150,0x54171581505916054163,0x6056054173581505c960,0x5815060d605418258150,0x5436458150d896054184,0xdcd605437258150dc560,0x58150e05605437458150,0x54164585505896154383,0x5d16154172585505c561,0x58550601615417658550,0x54187585506116154182,0xdc9615436458550a1d61,0x58550dd9615437458550,0x5438758550e116154382,0x61d62541765895058d62,0x58950e05625437658950,0x541625c550e1d6254383,0xd8971542765c5505d971,0x5d95060576541765c950,0x543825d950e057654182,0x6036154174d855061e76,0xd8950dd36154187d8550,0x54186dc55058b7154187,0xe0532581624c960d8b71,0x589605cd625816358960,0x5838058d60e016258175],#[0x589715818159160e0563,0x5c56059571581645c560,0x581745c5605cd7158172,0x61171581835c5605d571,0x5c560e0d71581855c560,0x581735c960e157158384,0x59573581645cd605d572,0x5cd605d573581745cd60,0x583845cd60e057358380,0x60575583825d1605d574,0x5d560e0575581845d560,0x58165dc560e117558383,0x6077258185dc56060f71,0xdd1606077458185dc960,0x58183dd5606077558185,0x6077058963dc16261375,0xdc56260f7158985dc162,0xff855cb60e0572d8185,0xe7f4fd9ef37e3fc7b8df,0xf57daf75deb7d5fa7f3f,0xbab6f6bed759fb3d5feb,0xbed7baefddeb7f6faddd,0xf8feff5fdbf97eefd5f7,0x7b3fe7ecfb9ef3be6fcb,0x6f6bfd7daef57eaed3fa,0xefadefbdb77eeedcfb7f,0xfe5dc7f8f6fedfbbf37d,0xddd7faf73fe7dceb9bf2,0xdfbbef7cef7ddfbb76fe,0xbcff9ef3be73cdf9af2d,0xafb4f65ebfd77adf59e9,0xccf7def7de7bbf75edbd],#[0xfc9f7beefdcfb7f6be97,0x3fe3fb7f4fe7fc3f77ec,0x6a8601e099003fe7faff,0xb2b203f32a80dbcb180b,0xaa2ca1bccaa0620aec11,0x782ba0da22e4347ebb07,0x17245803ca12dfaea3,0x8388b9a0cb32c80a4b2a,0x229faea852dcaa0e22ea,0xcaea2b2ab33aa4aa2cc9,0xa2e2c2c8b4bab12c9fae,0x28f15cb23c81724ce82b,0xb2c7417250505c94109b,0xacb1e22cac6d62cb217e,0x5c95f48b2b1c58b2c89f,0xa2c40001cc390b320e50,0x79c3001e30c009cbb003,0x672ec01dcb200792c601,0x142cb005e70c0178c300,0xde70802c6b20090f2c0,0x43bca00dc708033bc90,0x183b2c0754bb01e2aec,0xc0d9cbb03772c80d0fca,0xa03f1ec60fc6b183de30,0xca0fc6b283f72c80fdca,0xc303d0f2a0f78c283f1e,0x3281642c88590f221078,0x2bb0383b30161ecb858e,0xb30a11dcc8845b30c0e9,0x66c284a4aec1139ca845,0xd0b22170ecc04a2aec12,0x71ecb85e2aec1738ca05],#[0x4c3f2c1454bb0503b301,0x180fca855d7241593ca0,0x61e30c189cbb06372c8,0x81b43c906f52a41b79c3,0x206f1ec81bc6b206f52a,0xc1bd4b286d0f281b79c,0xbb06742c41979c306de3,0x32c1967c30659b0c198e,0x2c88903f301c35cb064d,0x3b30241ecb890d32a244,0x67c30699b0c1a8ebb068,0x4d32a2542c88962aec1d,0x60ecc0947b2e258abb09,0x783b2c2654bb0999aca2,0x1e35ca078d7241ed4c88,0x8890f22228fca87e3aec,0xa2342c888c3f282279c8,0xa09c3b30231ecb88cd32,0xe833c6b20cf1ac4330ec,0xb10c70ac42f43c88be72,0xae63430cb0c6b2ca31c2,0xaba900c72a348aba8d22,0x7f2a388ab28e0c32a408,0x43c88d6dac83043c88c0,0xd0f223d1fca0e62ac839,0x2acb28cadac8320eca10,0xda4ae8361ecb8c8c32c3,0x4131ca8da2aea36c6c88,0x8ea2aca3a30ca9062aea,0xa443fc90f87f2a3a8bb2,0x90df1b22378eba8dc3b2,0x284230c9108c7283731c],#[0xca1150f223f1fca0ecc3,0xb2c0b70b182dd2c40b0e,0x7cb8283f200a51c38203,0x9aca2c74b10b01b2c0c0,0x1bcb8a0ff20280ecb0b1,0x1f2e2b0fc80ae02ec29,0x851c292152ec4c0eca93,0x381b2e4d0cc89346f2a4,0x4f07ca92c1b2e4e0cc89,0x9a94aea6954ba9a01b2a,0xa6b06cc19d2b0a670dc8,0xc0b5230c2d06cb1701f2,0x25407cb0b81f302d06c,0xcb9643322590ec8165e3,0xb205a17ca945370a5106,0x6cb96922ec5a0cc89683,0x57205885ca14c5f28530,0x7ca96137285851c9161,0x37227052ba9bd52ea6e,0x248bb1c41b306c4ac29b,0x7c7f205f06cb1841f2a7,0x601ec81805f285f1bc91,0x9881b306016ca1807322,0xa6517ca18c7f206306ca,0xa9986f24641fc81901b2,0xca7fc2b11ff0ac47e06c,0xb1a0f0ac487c2b120ab2,0xb0683c2a9a0f0aca83c2,0x2c9216b2ca81c2c2a0f0,0x2f2679aab29d47f2286c,0x17ca24a02ea8ea6b2a2c,0x46f227ca6b29e98acaa2],#[0xa62b2a8e02ea971bc8a5,0x801b2c9f07c8a7857229,0xabd0b12ac1b22a106caa,0x2b0ef24ac66c32ae3aec,0x4beb6b22cf0ac4b13bca,0xa3058ac8c18ab22fa2ac,0x2cb5acb2ad70ac4b555b,0xcaada2eeab6c0b1ad8c3,0xb2abf8ab2afc7b22bf31,0xbca2de5ee8b7c0b22dc7,0xc72ab88bbaae30326b83,0x8bb2b022acac01ec8b00,0x4c324bd3fc92ec7b2ac0,0x7b4b2292fac6a430ca2f,0x107322c41cc8aa41f30a,0xc287ba3081b30c486b1b,0x3147322c50aca318af28,0x8d455ba3558ac8d506cc,0xa3593ee8d62bca3521ee,0x28db07ca35c1b30d80bc,0xb2b753ac6df07ca37067,0x30cde4ac2b793b0add86,0xbc231c2b2ac906cc3792,0x1ecac886b2b206322c86,0x17ca32c2b2aca18cab22,0x1230ce04ac2b804b2ccf,0x218c9b887b20e206cc38,0x841f22e106cc389230ce,0xe307ca3682f28d907cab,0xb441b2ad006c8b401f28,0x8d30bca3481b2ad106c8,0x23aab2cae9b6b23a41f2],#[0xcaf239ca3badac8eeb6b,0xca3bedac8efb6b23ad8a,0x728f0b6ca3b6db22ec39,0xec83f0a328fa1bc93a0e,0x3b20fd28ca3ec1b2efc0,0x1bc93e46f24f506cbbf4,0x14705001fc84006f24fe,0x350c1c0c1b2b0217ca40,0x3c7f210150c9c0d43230,0x14acb2c42b2cb0fb6b24,0x4762ec51d8ab1476b2cb,0xb1d1eca4762ec91d8ab2,0x2484d72b17acb2c5e3ac,0xcb0ec2b143956e92162b,0xb9c470ae511acb2c46b2,0x2cb181ec8c7ab2cb158b,0xcb2c647b291f8ab247eb,0xb32b13b6ba44cd72b19a,0xacb2c68ff251a1ec8c82,0x73230c06cc4341f3109,0x206cc4bc73232f06cc43,0xc0932b2e06cbcc83b213,0x330ec84cc1b31301cc8c,0xcb07323311dc8ca01b2f,0x13412cb4b4272b2c0bc9,0x2d2556e94708cacd03b2,0x213e07ca5201b31494ac,0xcad347b214d14cacf87b,0x70f0607ca5301b314d14,0x8cace41b2d0807cbc1d4,0x1b2f3a08cace81b2f390,0x6c8cec3b213b0fc84dc],#[0xc572b4119c9d041f234a,0x506c8d107f214206ca50,0x646f255c5fc25601f234,0x7613ca5d01f29755bc2d,0xd39870b4e60b153c1f29,0xb7731c85418acb532fca,0xa5518ac95407c8de01f2,0xb671bc95a17f09660ec,0xbadb982cb6e31c85596f,0xf297b07c8de81f2b7950,0x6c8e101b2b8307ca5f01,0x1f2ae707c8b9c6f2ae60,0x7c86041f238007cadfc,0x41f298207c86081f2981,0x57d4c013bb2204eecb00,0x16832805a1c901683240,0xfeec983fbac60fa1ca0,0x43bf2210eeca83fbaca,0x6117cc304282ec10deb2,0x884b7b2a11deb28477b2,0xc12a0bb04b7b2812eec,0x4b051f32c147ccc049f3,0x32a13a1c984e8326137d,0xcca855f32615a1ca84e8,0xbac41bef43063bb0c187,0xeeb206fbb241beec106f,0xfbb0c1beeca06fbb081b,0xcecc1073630c19eecc06,0x71f30c1ca0bb07362ca1,0x2447cc0711b301c7dc30,0x8282ec20d8b28811b30,0x21dd94306b630c1a7cc3],#[0xa87762ca1ddec2077bb2,0xc1d7cc307682ec1dd8c,0x4c0751b301d7ccc075f7,0x2ca2146cc0951f301d7d,0xd43085f30c21a0bb0876,0x83241fd8ca07b63241e7,0xa1ca07e83281fa1c907e,0x9f3242247ca0891f2422,0x37dca089f328227dc908,0xd3baa83346ca08d1b242,0x34a0ba8d32aca34cab18,0x8f282e63ccac28d32b06,0xa3ca0ba8f32aca3c7cc1,0xa0d72ac83547cc0c1f30,0xe83dcab20f6830839a0b,0xb20c91f283d7cc20f682,0x30a32d8b28cb7b0832de,0xab28d91b303246cb0cb6,0x2b0a36cac98da82ea36c,0xa0b28ea83263acaca8db,0xa832c3aa0ca8ea830a3a,0x77cc28fa82ea3ecab28f,0xee83243bcaca0df2b243,0x9564c0251f283fa0ca0,0x8a75b2229d8c80a55d30,0x64c574c0a959302a90cb,0xa91e32ec467cb2931f2c,0x244920cb91e32ec4790b,0x4c1255b304921cb1266b,0xb2a6b56cc19c872a4a57,0x4ca0b55d305b57ca9ad5,0x5f302d56cc0b55b0c2d9],#[0x574b0b95b2c2e564b0b9,0x5f30a547cc19515f2c2e,0x645ca955eb0a557ac195,0x5a32ec5694ba15917225,0x5194b294653265156c39,0x94232ec5094ca946530a,0xc5290c294a53285256c3,0xc14883305256cc148872,0xe578cbb15c873052574,0xca94e57285321cb95d5b,0x32a538dc994e33265321,0x1ca9625728588dca94e3,0x5b2a5857c99615b26582,0x8cca9b55b306c57ca961,0x55f2a7256ca9ca372a6d,0xe56c3178872c5d56c317,0x7e87205f21cb1795d0c5,0x5f95ca17c87265f9bc91,0x98c832a6020c9980872a,0xa6356c298d5f066356c1,0x29955f066521ca98d5f0,0x206420ca9955f0a6556c,0xc29925708649bc919287,0xf0a6621ca9915f0a6456,0x7c99995b266620ca9995,0xbac27e57ca9995b2a665,0x46cb1fb9ac67eecb11fb,0xfbb027feeb09fd1b307e,0xf46cb1ff62ca7fecb11f,0x1f2aca82cab1a091b307,0x87cab2a1d1f26877cc1a,0xa07b2a68347caa1df30a],#[0xc81d8b2a079b0681e6b1,0x2a111f228446cc2051b2,0xca8847c8a211f2a84cab,0xc8a151f2a887cc2a232a,0xf268947c8a272b2685ca,0x6c31cf8ac673edc81cd1,0xaac47556c31d28720747,0x9ecb9d67aec75d6b29d7,0xddb0c76d2b29dbb72076,0x890cb9de42ec77d2c91d,0xe5cf267956c31e287207,0x8dc4b2a3312c68c56cb9,0xa3727228d8cbb2351722,0x48e8cbb2395b0e908cc3,0xc23e332e8e8cc3a3b132,0x2a9256c3a44f7269121c,0xa9a5b4b267bd2c89ec87,0x7229440cb24f8ac693ec,0x1c81f5072a94c4b2a510,0xa70a9756bb2615b0c7da,0xafc2a5f1324978cbb25d,0xddb049b56bb266332e97,0xc56c3a6e42ea9b3dc9a6,0x795b0e9d90baa75db069,0xaddec22b79b08ac21c8a,0xabd1f30ad46cc2b7632a,0x8b07cc32be82ecafd8b2,0xa2c1f724b07cc92c11f2,0x2eb3eec0acdf728b07cc,0xc12f91f30b346cc2ce85,0x304b9cab12e68308bea0,0xcc22e686e8b9cab22e5f],#[0x2acabacac2ad91f28b97,0xcac8ae1f30abaa1baaeb,0xe830ac0cacaae32b0ab8,0xc7cc2aee86eabbcab2ae,0x9a650ea59f43a911f28b,0xa821cc29e552ea69543a,0xb0c832ca9574baa15d0e,0x2cf5743b355d0ecc8d4b,0xab855b22e120cab3c832,0xc2e956cab455b22d156c,0xb2ba77ac8e9eec0ba7ba,0xac6ea46cc3a51b2ce9d8,0x7c9bb9f306eecab2bab2,0xf30aeecab2bbb7f28ee4,0xcab2bad1f22eb47cabb9,0xf2acaef47c8bbd1f2aeb,0xdcac8bb51f2aef7cc2bb,0xa11f26f047c8bc32b26e,0xf656cc3a15b0ce89bc93,0xbdb7f28f67cc1bdb2ac6,0xcf345c8bcdf30af6cab2,0x3bde330ef3c9c8bce32e,0x26f88cc3bd232ecf456c,0xca3e66f24f956c3be0f7,0x7210056bb3fc872af995,0x5ca40087270056c1c028,0x87210121cac015b0b009,0xeec0c3fbac30f21c8c06,0xd1b2d0fd8b2c3f7ac90f,0xf46cbc3e832f0f47cb43,0x3d1b310f47cbc3e852f0,0x10cab1443bae31047cc4],#[0x4532ac514a1ba4432ac9,0x914cab245282e514cbb1,0x147762cb14a0ba4532ec,0x91da0b247683051da0b,0xb245df30517cab145e83,0xf29177cc245e86e917ca,0xab1c45f2e921d9cac5d1,0xf30718a1b9c632b0711c,0xcab245a86e912cab2449,0x72ac919a0c247e82e916,0x247ca465f30919a1ba46,0x4f2b2313deba44df2e92,0x957c3c255b0f09cac9c,0x4255f0d0956c34244331,0x10b21cc4255d310956cc,0xbc2d5b0f0b44c8c2d1b2,0x310d57c343443310b20c,0xb8ca4832d0c21cb42883,0x6e929cab24a5f30529ee,0xeb9497672b297cc24a68,0x7ae925c9b249722c9259,0x56c3c9a32ed239ebb496,0x95b0f2a20cc4bd5f0f26,0x48cbb490432f325743ca,0x9e350f248cc3c9236ed2,0x3020cb4c15f0f2756c3c,0xccd5d0f2b56c3cac8331,0xb2c20ca4c487292810cb,0xacb087292c9fc8cb0df2,0x2b2c11ca4b1cf272c91c,0xba51c43293420ca4b5a7,0xb0f4668c2d19bb09467c],#[0xab94f15b294810cc5195,0x1b213f21cbcf0832f3c9,0x20cbcfcdb2b3f44c8cfd,0x887293d21c94f443313f,0xc56c352c83293e20c94f,0xd4432f3956ca5315b254,0x3720c8ce08723368cbb4,0xd015b234a10c8cec4723,0x94337cad04f7274121c8,0x150443234447c8508432,0x94199c9d055f054156c,0xcad0487294157c25055b,0xb254320ca50d5b054391,0x6c1d0887234256ca50d5,0x5b234520c8d115f07425,0x8cbad5d9707578cb9d5d,0xa32cb5a57c1d69970b57,0xb57c256e32c95b57c2d6,0x8592c96137cad7887295,0x58b9c256043296156ba5,0xd7257095c65c2d6232eb,0xb6247c857d5f0b5c8cb2,0xa564432b6256bad8992c,0xb5d21ca576bf0b5933c,0xca5d84329633dc9d8247,0xf215133cad40cf235056,0x3cad4632eb5133c8d472,0x87216433c9d48cf23523,0x21cad9232cb6421c8d92,0xd5b277721c9d94872365,0x857caddd5b2b7757c9dd,0xa992c95556c9de15b237],#[0x6b46ca5aa82e96acab25,0xd9a32eb6656ba5ad92c9,0x36c57c2da232cb6865c2,0xadb15aeb6c64b2db0432,0x2b5633c9d5887296910c,0xc9de487276d21c8db4cf,0xf2b7956cade55f277956,0xdc9dbd5b277a56c8de95,0x43297210ca5c4df2b6f3,0x56ca5ec43237347c85c0,0x8872b7e21c8df95f297b,0x9000015b298256c860,0x37c02c4022c01a40120,0x6c405fc057004cc0428,0x98408f8086807dc0748,0xc6c0be00b300a8409f4,0xefc0e7c0e1c0d8c0d00,0x11f81150109c10100f80,0x153c14981404135012a0,0x17d8174816c8163815a4,0x1aa01a08197018d0186c,0x1d501cbc1c241b981b34,0x1fcc1f581ec81e441de8,0x2284220c217c20e82078,0x24bc243c23b4232c22cc,0x2790271826982620254c,0x2a0c29a8292428b02808,0x2cbc2c242b842ae42a68,0x2f542ef42e7c2d982d28,0x31a8314c30ec307c2ff8,0x3488340433ac33143250,0x373036a4360035a03520],#[0x3a0c396438ec384c37c4,0x3d243c8c3bc83afc3a74,0x3f803ef83e983e143dac,0x423441d0415440c04008,0x453044c0441c4350429c,0x477c471446b0464045c4,0x4a4849c4492c488447ec,0x4d244ca84c184ba84ac8,0x500c4f684ee04e744dd8,0x52c8524051c4513450a4,0x557854ec546853a85338,0x582057a057245698562c,0x5b545ad45a14598058d0,0x5e3c5d785cb45c745be8,0x61a06104605c5fa05ec0,0x644c63b4632462a8621c,0x678866dc6620656864cc,0x69e8697468f8687067f8,0x6c6c6c046b8c6b2c6a78,0x6ea06e406dcc6d546cf8,0x717070d8703c6fdc6f34,0x7464740c738072c4722c,0x76e0762c75a0752874d4,0x79ac793c78a478087760,0x7c9c7bbc7b207ac07a3c,0x7fc87f4c7e887dd87d04,0x82b481ec817880c8803c,0x859c84fc849883f0832c,0x883c87a086e0869085ec,0x8b308ac88a24899488d4,0x8d7c8d348ca88c508bc0,0x90488fbc8ed48e6c8df4],#[0x9358929c91fc917890d4,0x96909600956094b09400,0x99b09910985097b8971c,0x9cc09c149b949ae09a40,0x9fe89f589e909df49d6c,0xa2dca24ca1b0a140a0ac,0xa598a51ca4a0a40ca374,0xa81ca7c0a734a6c8a644,0xaac0aa70a9d8a92ca8b0,0xad40acbcac38abd8ab40,0xb040afa8aee0ae4cade8,0xb2c4b22cb1c0b134b0b0,0xb588b4f0b454b3c8b334,0xb868b7dcb754b6d0b648,0xbaf8ba78b9f4b974b8e8,0xbdb8bd18bc84bc00bb88,0xc0b4c010bf94bef0be4c,0xc314c290c228c194c12c,0xc5a0c554c4d0c450c388,0xc81cc77cc70cc68cc624,0xcab0ca34c9e0c93cc8a8,0xcd90ccfccc68cbb0cb50,0xcfeccf74cef4ce74ce10,0xd268d1d4d16cd104d080,0xd590d504d460d3a4d308,0xd850d7acd734d6dcd630,0xdb4cdad8da00d948d8e4,0xde04dd80dce8dc78dbf4,0xe114e070dfc4df18de74,0xe38ce2f4e284e224e18c,0xe674e5d0e560e4c0e418,0xe988e900e874e7dce720],#[0xecccec44eb84eac4ea14,0xef04eea0edf8ed6ced0c,0xf1ecf15cf0dcf04cefb8,0xf508f424f3a4f2d0f26c,0xf82cf794f6e0f638f5c4,0xfb38fab4fa3cf964f8dc,0xfdecfd4cfcb8fc40fbb4,0x94ffb4ff48feecfe58,0x30902750201017d0119,0x5d5054104c9043d0399,0x88507f9075506f10669,0xb190a9909f909790905,0xd810d290c950c2d0b99,0x1135109d10090f390e89,0x148d13f51349128d11e5,0x178116d9164515ad1521,0x1a29199d1911188917fd,0x1cfd1c7d1bf51b311a9d,0x206d1fd51f311e8d1dc5,0x22c12269220d21992125,0x24f92489241923992319,0x2769270926952621258d,0x2a8129ed2939288d2819,0x2cdd2c612bf52b612ae5,0x2f892f012e8d2df92d5d,0x31e9316930f930a5301d,0x342d33b1332932a13255,0x36b136593601358134d9,0x38dd386d37ed376d3711,0x3b393ae13a5139cd3951,0x3d713d053ca93c313bb1,0x3f253ecd3e713e193dd9],#[0x415d40ed409140213fb5,0x4375430542ad422141cd,0x44ed44a14461442943f1,0x476d46e5461145b94561,0x4a0549a149114889481d,0x4c394bd54b694b0d4a7d,0x4ef54e594d854cf14c9d,0x5191513950a550254f79,0x53ad532552b9524d51ed,0x561d55a1554d54ad5401,0x586d57fd578d570d5681,0x5b115a715a01597158dd,0x5d655d155ca15bf95b9d,0x5f915f295eb55e695dfd,0x624d61ed615560ad6051,0x64c16415635562bd6285,0x66f9664d65d96541651d,0x697d6921688d68016771,0x6bb96b2d6a9d6a416a11,0x6db16d1d6cc96c3d6c09,0x70496fb56f756f096e4d,0x72a5724171cd715970e9,0x757d74d5742973997321,0x77f1775d76f9766175f1,0x7a6179b5792578e97875,0x7c357b9d7b097aa17a81,0x7ee97e517ded7d3d7cb5,0x80d1808180257fe17f69,0x82e5828981fd816d8129,0x854584dd843583c18371,0x874186fd86858635859d,0x88fd8861882d87e98791],#[0x8b6d8aed8a6189dd8959,0x8d7d8d058c998c2d8bc9,0x8f918f3d8ec58e598dd9,0x9149911590d1908d903d,0x93bd933992d5925991a5,0x964195b9953994899419,0x987598059789973596c1,0x9b459ad19a21998998f5,0x9d8d9d199ca99c359bb5,0xa0299f999f159ea59e1d,0xa28da21da1ada14da0c1,0xa46da40da3c9a385a2f1,0xa659a615a591a55da4e1,0xa871a805a7d1a75da6d1,0xaaadaa35a9a5a92da8b5,0xad01ac5dabe9ab91ab3d,0xaf7daf11ae6dade5ad75,0xb1a5b10db099b011afb1,0xb3c1b355b2e9b26db225,0xb5d5b575b511b4adb441,0xb841b7c5b745b6a9b631,0xbab1ba49b999b935b8a1,0xbcd5bc79bc11bbc1bb2d,0xbef9bea9be51bdd1bd61,0xc145c0d9c031bfb5bf59,0xc3e1c34dc2e9c291c201,0xc66dc611c56dc4c5c439,0xc90dc889c7f9c789c709,0xcb39cab5ca59c9e5c969,0xcda1cd31cca1cc41cbbd,0xcfe9cf95cf01cea5ce31,0xd1a5d151d121d0c9d025],#[0xd36dd315d2cdd279d215,0xd59dd551d4d1d435d3dd,0xd805d78dd709d6b1d631,0xda75d9cdd955d8e9d871,0xdc8ddc3ddbc1db85daed,0xdef5de89de25ddaddd15,0xe161e0d1e051dff9df71,0xe391e33de2f1e28de1fd,0xe5d1e52de4bde44de3e5,0xe83de7a9e741e6c1e649,0xea51ea01e989e921e8b5,0xeca9ec29eb91eb41eaf1,0xeee5ee65ee19ed99ed25,0xf10df085f019efb5ef75,0xf2d1f261f221f18df12d,0xf4f1f489f3fdf391f325,0xf701f689f63df5d5f55d,0xf969f8c1f84df7e1f781,0xfc1dfb75fb05fa79f9dd,0xfe8dfe2dfd85fd05fc95,0x1160091ffb5ff61ff05,0x37e031a02aa0236018a,0x56a051204b2045e03da,0x79e070a06b6066205c2,0x8fa089e083e07de07be,0xac20a4e0a0209ae094e,0xca20c4a0bf60b960b22,0xe8e0e2a0dae0d2e0ce2,0x109210460fda0f4a0eda,0x126e11f611a2115610d2,0x147e144213ca136a12e6,0x165215de15a2151214d2],#[0x1876181217a6171616be,0x1a2e19f21972191e18c2,0x1c2e1be21b661aea1a6a,0x1e721e1e1dc61d2a1c9e,0x20b2203e1fea1f6a1eea,0x22b22266220a21b6213a,0x24b2245623ae2356230a,0x26be264a25be2566250e,0x28de287627fe27ae273a,0x2b522aea2a6629e6295e,0x2d362cc62c762c362bb2,0x2f3e2eca2e862e062d86,0x3222317e30f23096300a,0x34ce343e33963312329a,0x372a36c2363235c2354a,0x397a3906389a382e37a2,0x3c163b7e3aea3a7e3a22,0x3e323dba3d7e3d063c8a,0x404a3fee3f863f323eca,0x430a42b64216417640ea,0x458e4516448a442643b2,0x473e46fe46b2466e4602,0x499248f6489a482647a6,0x4c2e4bb64b124a6a49ea,0x4e9a4e0a4da64d324ca2,0x5122507e4ff24f9e4f0e,0x530a52c6527a523651ca,0x55b2555e54ea54565372,0x57ae575a56de5676561e,0x188260da590658ae582e,0x8a0840700f06f84d098,0x601dc2838a2e0bc24407],#[0xf38081505445e0b81970,0x4d61740ec5e0c02242a0,0xd847056088709b068860,0x502600ec1a1708781fc1,0x35a11c202490c43ec0d8,0x61b8000203a044c281b0,0x811919a261180e415132,0x7b81d0a11009313d02a1,0xe07e082480d8220204,0x608181018330860980e,0x3c080311309609941d01,0x90891202e21b8291590,0x40b0292e02819082094a,0xf85302c0d05683d05c11,0x11b8098008e02c0d412,0xac101c892a0641fc201,0x65c4183d08e25e0c997a,0x10778108407a050a3437,0x6841e2f20c8350090482,0x8517240881c084028764,0x23b8661530751b42942c,0xa02d0002b90986182911,0x5c421002094100a02e20,0x86e0a52f42203118a0fa,0xa20211c2281400241854,0xb9320144b0a2148e5c0f,0x1ca110102c1284270d91,0xc4d0c98dc0a83d0188c8,0x48841d216c6d0e11ac23,0x540b00222ec59890740c,0x1242465013c1f10a82c8,0xa1ec3f07216871096834],#[0x9a1a8ab0d07e0f8cda9b,0x150213962a86a0e00423,0x46402113a25c65898028,0x40f44464a0de03840033,0x662d03385289053a2f02,0x228409e932318c2e1791,0x2e34542e3a63e04283b1,0x9a1fc98684a7d004426b,0xa5fc4e9002864f2d2099,0x3fb87350ccc81dcde521,0xd6f2640526df8ae7511d,0x22b76147b7fa10808561,0x9afb2dc211ac1e40d49,0x8064d7f1801086fc1801,0xf8030285d3e4c80a48d3,0xfa024233c773240437bf,0x8b1cc45263a32a82161f,0xd11963ec18c5fe8e2212,0x7288ff328ba24aa13a34,0x3ec3590121b1f5665423,0xd1e52dd0aef4794b742b,0x784204363f90ac64433b,0x508010abf817c24637f4,0x8bf817c2461b7c1141fc,0xcb48051e5f47321f31d4,0x3f40965e584810af7b8a,0x6f9380042a3d58a00429,0x5879608542829f41850a,0x20c2856fc30c4ca4f922,0x9286142abc7a30a14df8,0x80cb1e1826653cea484f,0x45021a963ea4cc85fd22],#[0xbb9076c4ccbce048b57c,0x4e439af3591679af3c91,0x5a865ef4d3199627c496,0xf48c1a93bcbaa19431e,0xf2d4321be6f4b9161a1e,0x43268ad9c8dde5d50cb5,0x1ec322b86818250d5f2d,0xc49278bc899c2558656e,0xa7f27ac285a790090867,0x3bc9ad6266d7e8a4d285,0x4f00510393f4891911d9,0x9f12599a1f914dfe7b85,0x3384ab0cb1f28b5a6678,0xce67c490cbc4946bd791,0x7f525116143a17ceb608,0x9d841f390dbe8b99266c,0xcb0a4237f7028acc2c1f,0x65cfcae0093395f912c3,0xc665e7d984042d7e8212,0x871993dedfc61a15be81,0x551b3914be1f0ec666cf,0x2a3af61c90221be81c66,0xd448216bdb1e83c40d1,0x655af0110388d306557,0xd719600cb178089dd0b0,0x13c40c0ac50c9f4c8032,0x12268c73a452e38c1933,0x3fa92428a1a78c244dee,0x1220a951fe852020143e,0x2e38c19336d2e122c9e2,0xee1220e6e122a51efa45,0xdc9988b8c99278c244d],#[0x788215bfa15052672ae4,0x5d67accadf2916653330,0xca0c99f2dbc143a40d3,0x6857cd01081c712dacb9,0x4ab3718e0cc45fd0a8e6,0xa5010ddc139032f36b06,0xc2a0476fa2e4599b5eae,0xe7111665d8fa284471fe,0xe20c909e20c8dc298032,0x4da4cb47b53480014d09,0x5010f34919e001c9973e,0x45de20f348cdac49937f,0xe5013356cde132aaafc2,0xeaa3c9fa0e0c152e7f87,0x66577cdf1338a86d5367,0x8734ca2fc4804858ea25,0xd8ffd0e00ba86cb42cf6,0xaa0bf691a2f9412d2054,0x4915b387cf944a414934,0x9a47ef22087499c3ff5c,0x41e6918702fd22ef8087,0x65fd331a46555f848bbc,0xb6153d440997bd192126,0x43effde4618491ef6416,0x6f14000821b9ebb09c68,0x28232acaebc8b338bc8b,0xade104641af5888b9f4,0x8d0be772208d008b842d,0x9179c044c87c019335c1,0x39760649fc087d7e0002,0x8005266b831c5f2228d,0x735c18c8bfb99006773d],#[0x333f3e1810aae4c2a8a1,0xfe30ca1969f10b36404,0x5cfe00426bf36ee80086,0xc9381430f9c264df290f,0xe1221b1fd5244227c030,0xa84452efb290a313f16a,0x8bc885d41d1a450b57b0,0x35f66b2217a3f61939f4,0x562442c7dc31dbe26221,0x51014fede9012a2221e2,0x8d19cae47b810c6a9f08,0xab3f21c3154d95c8f7a1,0x86194ba7b0c90c591a12,0xb64c927e2193054b92e5,0x3d864a7c92b1d69a1e13,0x39433e9f02200e22983d,0xf98511a143b6cc7c5944,0x72183f3c56ca176b90ed,0x469142c791e9570634ed,0x91e367e7d22f2217507,0xf26e66d7d9ac8852fc65,0x52471f33133e24b9fac,0x7d2549abf21b4b3a8633,0x38642f82d9917e4282e,0x6989b104888115f910be,0x207c01495ceb8319adfe,0x638f258ca2faf06b2859,0xfaf0015821a9fafa4d61,0x3efa024347197b018ce2,0x3a64429ba3efa02431ba,0x1fe70236523d43331bf1,0x7869584cc1fc82b09984],#[0x208803361dffd0601437,0xf13a644287f2a803287f,0xafa0265a7e835483431b,0x3c6f2652cdc58d490a52,0xbcdfa508567f32c212c9,0xc25094801980adcced30,0x4c0a9006bc1a3d114db7,0x5e6fa5842957e1326de7,0x6e6ef3942176f84a1290,0x3297d2bca1943a36f2c6,0x652014a55f8a1952bf14,0x58dfe04a6f140084cbf0,0x38c02154df2267e9d406,0xdfb93d791d75fb222cb9,0x23425e09257ca7c4cccb,0xba78088b7ff300525bf5,0xb933774d801973b4da4c,0xf6e809972c7488dfdf00,0x50050ac7d28836815377,0x4ee990232ccf4222f3cd,0x8c8a1749f922c3f24468,0xdff340265990fa45a780,0x287bd330266ceb64e4cb,0xa6275886ed4dcf32a014,0x8844f128232e27ca08ca,0x4e7cca597d499971f7c0,0x5a5917084562ec370949,0xd154949356109d9eca16,0xd73966c2379eb4c83792,0xa5e1a767ccc5fb257a65,0x2dbf193692143f9b768c,0x642c611db641bc037535],#[0x13e60e3af1c6437e8eb8,0x532cbe9506014f30c662,0x3af114d1ed686406f99,0x7ec644213ec64420df4a,0x996083d7d064421d3236,0xd4e1ab95e9921e24aa11,0x607e8d025a94e1650252,0x49eb21cb77b8586157d1,0xc31bb67b4c8c2bb95288,0x90090a1fd2434d733b70,0x3e704425377a122169f3,0x63e65a4c63e65e70441f,0x8053cc319a3af1c64a4c,0x66c20d19b08306f41f32,0x7c5e1fa8e01c632a664,0x601445fe6827235c2f0a,0xbf15a88437262e0242d5,0xff1f035336cc1f3e2239,0x9f11202f084a31f390f3,0x9af6635822ff5a34820f,0xb1891b34378dbc8ac4cf,0x3ca5ba17a9f6cc8dfe1e,0xcace1af06ce0e578477a,0xd78367072bc267d257fc,0x951b4b49928f0c67670,0xc7842c3d7cf31b854315,0xf908b6921e6268417866,0x85ea444f4c64afa6639b,0x846214a1fcb309964f85,0x40bab203ddca4342cdf0,0xe974bd0482fee4581334,0x899599b9db589d6043ce],#[0x18d32b32d07e5046584e,0x6bfca4004a5a0fca08ca,0x39384087d73971594487,0x79132d09bca0a965e64c,0xc9e48010b8ffdc02116d,0xcee66c516d8658e02213,0x914e83c00293be01764c,0x8959978f60002937fe50,0x7fbeec590340eb11123a,0xa942312188cf41a3654e,0x264f733bcd7a50f8d1f,0x2dc943415a346ed4ade5,0xe0319d350f60c66b7f33,0x750c6977d8ce2123ea98,0x62c65cebb05903974d76,0x548b3e765e45cf3091f7,0x251e3f64ce2cad8d4fb2,0xdf67cca0f9e60d755f8c,0x14387ccce2c99db58f3e,0xd0775dca0a407bff3403,0x580c13d1c28f9e613126,0x8cda92d4a70a6c64da48,0x82c801c3e3196b82475f,0x5e334651bfd0c852572d,0xc6746bcc1c161e26ca5f,0xc0848bf0001489cc0f60,0xd0f54910917c88a38794,0x1084f5491095f4afc50c,0x7a1a0e2bf6deccb0f041,0xa2c50790c7df3af2865c,0xb9082d4ba01b8ed251b6,0x410bde0944d6c18d3379],#[0x18ea52f8dbcb1940afa8,0x821acd0e0a74a53bfea0,0x580ac05bdb4aaf0c1895,0x3281cca9da909f9340c8,0xa4d72e2012140387c6,0x803265d4d80014a47ec0,0xef63428ccf7f20211bfa,0x46c476f9212b87c1432e,0xab0437dd6a09690c23e7,0x65996ad0830a4a7f0cdc,0xa6004adf9a07a9bbd7,0x3a8eef7a25208d5f5098,0x193340e3c66ed707b063,0x14627e48a37727e4d032,0xf821efe0873f010c4fc9,0x30697fd608ba3fd608bb,0x300f5f8cacedd306cedd,0xa83003f541e601ebf197,0xd1cfa6790d935d85607e,0xd2f9f5eb4a1b1e8c1068,0x5e21d8a925d0dc9e890,0x8831520dee13a3d483e1,0x70c7772b6191d6f838bd,0x645488fae7b6e1640eda,0xaf894ec265cdfa8cec0f,0x82d7c4a76104ede0c549,0x88cf96a509a07e506e47,0x8cdda3f4217b62cb5d6,0xc121a9268c42738b00b,0xf132235797b850bce2c4,0x5e05131e545956b197fd,0x4396122e0f028f4e5d13],#[0x2421b103e0e2ceca8c16,0x7ef5832bbe815212dc59,0xac061a5c681478c7c104,0x1c834b8145871a051f29,0x151234438855e5db1abe,0x328fddb4652a6e8a472e,0xd4c2d162c27c18b1d98,0x52631e0b4d4ba8cdcc4e,0x467c9d839a66884e6bd6,0xb10e2176c3db0d38b528,0x50b45142d101bde68d39,0x429d84b4183bbe99043c,0x6d1820e5d6aa3d021a9f,0xc1c9e134252429f5a50a,0xc6fa872153de1464974e,0x7de1463cb5d6895cc18c,0x43e13425275ba8a5d3b0,0x1e6810bafc5a24802087,0x80062814a5d5bdd65e7e,0x514acec1a4c45360846b,0x20f4c6e8aba831a3f90,0xa1f356a840723b068fd,0x7d119a83b1350ad2881e,0xe0f9aad94269268a23d4,0x5e16ca123e671a32a252,0xec060fb45cd93b98d193,0x647d93bb2a7e01cc1941,0xa32a95f9202c2b17eeb2,0x8bb9cd54b49dd8e3f7ad,0xda1885c6582af73db20d,0x11a3a6505bcc2d10dc9,0xbf4751ba04373a650797],#[0x88563f545d629693bb1e,0x5e02780b1a5a0cdc9da1,0x2951f3022a657d00a821,0x60e051724f786d8867,0x2974c9814757cecb152,0xb4052056a37473527bc8,0xfa636291ad9c8752798d,0x6a085b3b86e912e75131,0x9aa996cd61b5a922e751,0xeffeb4a10683078875fc,0x2aa336310f40217ac145,0x45470cb9ac64621e232f,0x8b0b0ebda1885fba1cb3,0x4c19547b7a2547047664,0x8933c3864f41d4574e8e,0x4af50d19549b33b2618e,0xc6c5dce6aa5b3cce4899,0xed0c4299d9f51d9ecfa8,0x211fc184290b4eec66e4,0xa4a34277209a367ed0c4,0x33023ff58854b60ad5,0xd9a689f5c1496c9ec180,0x47e840bf784a34e3b3c0,0x7b698d9bb26292a185e5,0xc85e91c8ca8e4c44c42a,0xd0a1d663251ba127db4c,0x6cd61b5a926285599924,0x26aa659078895fc9aa99,0x834a50eb3e3241e21d7f,0x2160b9a282ebd8c6c5c1,0xa4d4d2a3dae43841f08e,0x867285eff416d721ce50],#[0xccb4b330bbe51f063375,0x7e0e4223d7cba10324cb,0xfcc6778a885f10321257,0xd2a387da5063fa611138,0x707a9248b0996958e4d4,0x53382ce0b93f5d6464b4,0xba14e5090e50f03f9a05,0x7d65908da59ba145d615,0xd3708230bc2a52dc1865,0x1b4b0d98307374288c8c,0x33708e86ce10827acb21,0x2663f841c89d9c422b94,0x43619b836b31cf468f08,0x86cad6635c0a486cfc08,0xd1bdd9dc846d2b71b69,0x37632708476077832332,0xdc337074c73707ee19b8,0x83f60dc6e105a3f9c213,0x7558148ec0ce0843619b,0x9fb7084236d836decb47,0xd866e0cd866e0d6f4289,0xbc1ddf265ee256c0f08,0x51b976de8da42f0ba783,0x3c1c6ba7e4265858b9e8,0xe8e9f88f7427a9d7b870,0x3e9e09acfc83cb08534a,0x163a4c3b5ee8d6a3dba,0x9983f54210c99d0a36b6,0x2160cea14726e514a6e0,0xd5083e3ae651d24c1c5f,0x3c43f542155d9d508427,0xdc2781de10d04d67e41e],#[0x2f8a91df83906efa92,0xe9768c73e10b026fa39b,0xa842291ee83523dd0627,0x1e128f4f0948f74198de,0x94851e0c4c275f2c24df,0xe47b90c3abd01bb94897,0xb1a7527eaee14ac69cc3,0x258ec4e1b4b3911e24b7,0xa23691cb9e751e26b706,0xb0b45cb7e41c7e3140c7,0x9422dc3851e5f576ca48,0x6e74505ec4060d1101b3,0xd9e42ea4d6484930b440,0xba33b286b68c1078fdd6,0x85d4d31d1fa8225223fe,0x8060d1207a78c196a697,0x155c58b92b85a3e237b4,0x4212164ee516bc72f282,0xbb7b25460a3069096d1f,0x418fdf2941081e13b86c,0x544aff408313c05f475d,0x151764309afd099840b9,0xb8c8d21272b1cbe0d5a1,0x187842f9b2fbe9941c56,0x3a10f2d221e5a2a10f2d,0x8b45e08785cb434e9820,0xba34a3a74c1590dbd504,0x5a24f58bdd30533dcc28,0x20cc4072e085fca60e4a,0xe93a1b108ed376192c4e,0xcf7c15ad0fdc269ce5b0,0xe4839b27128e5613f108],#[0x4a3fbe4546f5cabd1a34,0x957a3c7f462d12172f81,0x24d1c9a134be207a15eb,0x48541a5c9e1196e092f2,0xd4b837ad6ce8ddc08f6,0xbb3c22dd937a316d8b06,0xdd26eae90e1fd8344832,0x712910f47905d2483706,0x3920834b170c2f0ae62c,0xf0efca0db13f63eb1515,0x65183e01d9ca169b09e0,0x7bc369424d23a54724ee,0xf4a8c4c2035b489b1de1,0xe5864eaf41c3ed28332c,0x1e79413a6336d721d0e8,0x47ae2829942ed721cd0a,0x4ac8a323e50d4797ea11,0x21fb84e86c437892747e,0x3acc203a1b4387998505,0x800da79958467471061,0xc1c6e0f0da6882174647,0x4c1a34e483c704153e00,0x18b8a90601c3925959e0,0x85c54834e792592593c4,0x720f4dc26b90a9091c58,0xd326ae0f9e2bc195ee51,0x216ced014696085c4052,0x92a347a306909ec9e2d1,0xbe0528f6de810a0a5fbd,0x40a516eca0848b3b2a3a,0xe3da028def728acb30b1,0xc526330a7103c145f0a2],#[0x4c9ab83d45c85c241fe9,0x47746a5a3f78aa55490d,0xb09161689129707f7b25,0xdd10097d1135e0a02eec,0x510325907bc2f07745c1,0x306f37410b06ca2836,0x427ee8b64070befb2880,0x38b141b2882c0e8aded0,0x39b051adeb5155e8628e,0xd08f66874e48283c0a20,0xa0530c37d51b0c34b101,0xd1b3071c589f72985b3,0x7e6267c5d0621d478149,0xc147e62f7e2254261a14,0x84bb685e8ce7bafa3f7b,0xeda1c9469b0b85af958a,0xf5c05520da14bda099c0,0xa9b7b41cd39ee8d9c081,0x3eb8834332a60a4562e0,0x60a152e16b882cf06b1f,0x4736866d0f3ea0b42032,0xa427a3ad43598687cce7,0x4ba41945c3de0e9b4149,0xa0846f8223f9b0b1491d,0x46e7e65947278d951ebb,0x24d39ee8e5ed0527e841,0x6ee82d5282f08adb4774,0xdac51675147e6263ab45,0xea29a971ee02979fc82a,0x49ee82914e8ace75159c,0xc7e8c2d48b4705fe5359,0x85d915ee0a6ed2d46e4c],#[0xa123d9bf9929149834ed,0xb52b84d5a459c3970cdb,0xc0b426af3611aeb707ec,0x2abe8ea377682f9c147d,0x17c40c84255e2e847768,0xcc2005a9a5fd010683c1,0x26df4a22ba4d8149976b,0xd1a3f9df75214ae93605,0x425f74251ed014605a0b,0xea5d332936d959ecaa5e,0x1a518df743460d6b2e10,0x468834c18db5b4ad23dc,0xe0cd1129b955d23d5bed,0xb470be7d12a307a6507b,0x4839cdd1292bb1bbf44c,0xaa3b7876d6217aed48e7,0x75eb768495ad6d86b72a,0x2c00c2ac28df74347768,0x8bd96183fa4d122eed07,0x558149b5ebbe934b0702,0x5db59a5daf71a49a5631,0x18ace9f9890b774a2daf,0x784fdd090f4083c8ed9d,0xe324587768c699dda3e,0x55a0f75096da1ce50bb2,0x8c70fc6a83dde20cc387,0x86e5c15777e76466cf6,0xc2a5e33052b4bce06d5,0xf44a8f8e825a393bd58f,0x633354cd1c73ac47b2f9,0xc2333472f464d90814cf,0x7125203a60a0b08f3293],#[0xd82652cd052bd7696cf0,0x5b6873942ec838c81750,0x34ca14053c3aad063c42,0x9be546e4c274ba4030fe,0x3cab58c9834c1f3ee0aa,0xc1c9051d63c1921cb88,0xe7f20ab758d70c06a7c3,0x121bae2]]
set_option maxRecDepth 16000 in
def g251H8 := limbs80 #[#[0x408320301830c04283,0x1c108020001d14040200,0xc5041c00584001d40008,0x12e080409c124438a003,0x400007002e240020000,0x10cac009000400100043,0x284840400015062858,0xa3420106246060e34180,0x8583100510020017810,0x4d0006282050a080810c,0x1020a100811c14104680,0x2080001a1401e0254,0x5047400e08082861c0c5,0x8781812e34b152a3828,0x6d515241c0054218601,0x485801644092085000b3,0x8029000058200780104c,0x78724301080004280100,0xd0e4020b04540020409,0x1262c600001cc24241c1,0x270080001008d040401,0x80c509040814e0a10509,0x3c707100808300100860,0x80a068470130101811f,0x1316181823e24404120,0x7914080062a601cc02c8,0xd00804976c0438004108,0x8130251a7c03408,0xdc00402001430060b80,0x11100018678000244820,0x1072800001d259719c10,0x2e072701836806b00002],#[0x4b1d1434ca582,0x9bc49f701ee0c8000000,0x5800045ee000555e0007,0x7050800002c133c08340,0x416f8d6800181b58b,0x56800152eb9560000000,0xde5a60000001933841f1,0xdbeb97700011168104a0,0x85702144011684254f45,0x1ef6c49e2e1000092bd,0x68ce00058c18cc00,0x6b2e000249a00024d,0x52800100de41275e30e4,0xa7231a24459212ea41b8,0x52e70e6e156698706091,0x34105a20000001a16,0x8fa80801a8eef9eea340,0x606b859b05f828594d04,0x25d0001509fbedc31489,0xb8e207a0ba15a0004459,0xd0000000098649bf9794,0x80008716020eb9ba1060,0xb1f1490000c46dd624bb,0xde8b30e8114ad08c522,0x684865e5058641000000,0xa8be42f973d871558458,0x20d78bd00010d9eca9,0x6a34e0007d2f909623c0,0x2b6e8e8a4f710763ef53,0x115bcb7502822f3abf,0x1210dc265802c1260000,0x4c1e861d09a2a8c0],#[0x8a18b89874c5318aa000,0x41833b04e80c900d443c,0x19a9b6c0612a918a3013,0xe0b85f201ea1d867,0x7570e7b3983b7506,0x720000454437a3bc0828,0x80007237031f104a8759,0x8258967ae783e109661b,0x22fd6a06c624d1013d60,0x18001039914b63de473d,0x24ec0003997c04e1fc68,0x30a000598a8a29a59089,0x49045a138a3354dde5b6,0xea7d4b9784b2cf222be5,0xf52cb1a00079ae000225,0x88000000049e9872e8aa,0xb02a7015c5e77476a380,0x80010b06173e1ec3b5ea,0x2fa6b88001c51c3750a7,0x2cb00002a170bb0,0xd0fb01f0f5074e310b00,0x1f15a09b89a4b8,0x3d1e24942d77020000,0xb23a628d000000061880,0x25980000001018201882,0xbaa00000008919d26000,0x5b2b580ef83341ff6787,0xe7880008a88c,0x7e0510000000000003f,0x5103038e4752290000,0x4dc148a5cb5106163b00,0xc5c811f25a4962d87397],#[0x9c0006c5d85ed096924,0x62ae86541ee6b45,0xb809c56903f800000000,0xe6b000167b000000002a,0xf05c0a079454c0006260,0xf30db076a08613020d48,0x20b4000550000022bad1,0xbe04280000000000a7e,0x98000000000000002da9,0x603e800109a800000062,0x10c8000000624a438094,0x5a800081201100002109,0x21780000001a5e80002,0x4250000000089d108e00,0x45a00041c3425428c05f,0xd60002201d1e0000242b,0x5ea644640002067b2765,0x96544e60000000c0923f,0x6276cb508ca0000000,0x98b820006007b3c45520,0x483c00003b90def106f5,0x42040000134000,0xda06d0000000209d8e60,0xf0e968486f5c37269485,0x1ae03203ce1dc802422,0x10601a0320,0x58001178457c00061e00,0x800081969440ca800121,0x65b90900f443ebc96,0x96167ecb503680011408,0x38e5a51e6f1a51674285,0xf05a38c000000188084a],#[0x63d60003aaa,0xd1d20adca1b784763440,0x4243677249600069f68c,0xb0a10fe1e6807c8a6000,0x7588ab98810aa484812b,0x22a780421256bed0ffbc,0x510933d847982a5a1,0xe028c393e800097c24f0,0x39a5620d425793848160,0x23acf3f64fc49514ff8a,0x9be91c431b2e1dd6e108,0x44e55419120504a6cd47,0x10af0562a39097c2f7c0,0x6a940000000657000,0xe42ae200000010e8614e,0xe000103c000000000008,0x413d227e0dfe5ac0cb88,0xad482931348c5dc0e139,0x70ba0000000c3ef,0x88fee03e0d81bcda7a80,0x36442f600000006b343c,0x8fa96016b00016798447,0x532180bfc54e073248a4,0x7db5eeb619c69de1ea90,0xc2000000000a63dc000,0x9d059041609490d60004,0x307384b00000000ea705,0xc0a80a380c6430000619,0x68ad815548c0000000,0x20f589ce25c92924b60,0x55ea4003ccb16590800,0x3da09e000084fa8fa6f4],#[0xf5f80012a90001c4d8,0x400068b0000089800000,0x6e6800185763ca00044c,0x7d597b84363a80002b16,0x6000070480018d2fbe59,0xf710e0000a508000f4,0x35003e0000000,0x4514ee4800151a0,0x725000000,0xbf2160001d6c000000,0x1136f0928d58001,0x2e27000045f68ef80000,0xe8bcc2e3c8c0ca0137f2,0x24f94b0bd6000000012a,0x14e10a480000007,0x6e60a9a6000211400000,0xac800000008f800062e,0x14a02a00479988488000,0x20e00000000004adcb,0x1a40004aded40880a00,0x1135fa218d1e3cf8c9,0x520000001c0559c42348,0x110a11392e3800000060,0x4c680000000159110800,0x58a5916e621b8518000,0xf8d68c2b30ca00008298,0xc55714df9b51373a970c,0x9872dec215608040a28d,0x9200005cd08981120347,0x48c480010698000915ea,0xf5f419785539cb33d63e,0x43879162000484b9a25],#[0xb6d888c3c72e468b24,0x43548b4e4b4000000000,0x1252833983f244a000,0x168ebe971f6eb2f20000,0xe000411beebcab6428b1,0x96000b80000000000040,0xc648c60000000000248d,0x34ad188b00018b6682d0,0x570e7225aa000609236,0x31c00040ceadda426c2d,0x8cd80012e2a804c446,0xf92821666a3cb6365800,0x2b5202c49a000013be38,0x40aef3780000000000,0x7800061be5ca00000000,0x1892000000041a0e7,0x32e0001bd200045ba000,0x828d07278e7c644c2a58,0x400000018c789ec88ca5,0x8870000000000188eb9e,0x8f11e00000010a20001,0xe8000e5c381709f2520a,0x50f5c2b8001900e56bc4,0x103c3ae2080003d70000,0xe414a008c654e5be0006,0x255b0001132c4482a66b,0x231483e0004827af7639,0x2c9382394f60968379,0xd00008f66a8292e03220,0xa5b20b6c51812a1bd481,0x2341021bd8000397422e,0x87e800183861620000],#[0xc0938001359800181180,0x6ee3130aa002e28c2514,0xc4093c8f7910e2068564,0x4213163800089e80008,0xab9c00005de000000000,0x989060418a9420001acc,0x52000000000042a1a064,0x722f45003,0x95d000155b8000000000,0x3c39da00000bc0000001,0x781de0000000f2380017,0x84681be55c000245c0b,0x133099c5840006362000,0xe84060bf95de962c994,0x6809609174b6bd88ae5d,0xee54afa413800001da1f,0x404016a24cc6a50000,0x823e3854a4818fc80000,0x80000523a48000000022,0x63c52ee7ae34d016,0xd6866626f497429a0000,0x5d51428840001579a1,0x4074810000312e000000,0x717486952a3850dd853b,0x4acfc00065e31468a571,0x2f98b165670131d5ec4,0x808000000000000014bc,0x19265151a04a0c00002,0x8073bcf06a800181f00,0x149800000012f5a4310b,0x146ae680f438ba288001,0x64500000000000002180],#[0xca1507200018b700010d,0x492ba556688001c91,0x5ef3e85600dae3830220,0xeac8d27000004e993e0c,0x210c54006c99d112c99c,0x78948971e63f9d14a4c7,0xb9981a7c443b300837e0,0x2923144a326805636d0b,0x4c800025c1860e118000,0x62e10c083e6942e,0x82a180000000000a4f80,0x9001d0000630cc57a8b,0xd011158e72a6197b7be8,0x85258d32f8e2aa804d8a,0xa151c86c4f4a6f48b624,0x10d200015327bb016d,0xe0001049f4541bc89f8,0xca14d496000000089128,0x65da081d152a23e73680,0x37c09e008c2c98ad892b,0x7e4d2039000053322953,0xe44f14aa2c2a7b94f584,0x4fe753c4bd03a8283938,0x55117e07fc4700c507b2,0xf885c49000062b4921ac,0xf25a3e90630001253a46,0x6c0001174623e0006830,0xc8001b1842fc8b4051d6,0xaa9b0eae10e65ff967a5,0x4bf33a00008afe54506f,0x2eb1540001287a,0xf683815eeeca85400000],#[0x4be869464f2000030,0x510000aab240d11840b2,0xc007803a0001066c1c0c,0xb4d80006881ef7800084,0x30bc0003964498,0xda97645ea00000000000,0xb14199e990d00018b56c,0xf5000093a80000e23bb,0x1d257b956000023f8001,0x31d7320ae92c06ef994e,0x22318d0800085d800168,0x62ac00023b316f,0x50000698a00001f20000,0xdc360000000054600024,0xabd48b405b00000b1c0d,0x5912ed48c833c00030a7,0x65f987d646794380013,0x435d94f814c25b000000,0x39b9800658c000,0x3d401800197a24820000,0x633226a25b50a045,0xd72839e446680,0x9a8000000403a27cc21e,0xb00000005c5c95c8000c,0x842391ec07014ca46c15,0x17000064de000000151d,0xa80e180010b280000004,0x22a4000000010621,0x8000000000,0xdf149e000616a0000000,0x847600002630ff005c0,0x333a851000034090dc97],#[0x89388a49528c50000000,0x2800060ec02a89298348,0x800079aa0004b202e621,0x6365f4c632c00062e,0xf128a98bc597c0002554,0x8e0b600008bf8c160ba0,0x306000000e96439d3c3,0x35e00000000004894141,0x9c0000000000657f6754,0x800041c7130d8fd0f48a,0x232309f91fe0d8175057,0xa4604f91aa0952cea5b0,0x4a8a94e61e98,0xe0ec5ae0b3812400,0xbea0b3000049ead940ac,0xd514890aa92b43f70dba,0x1494ace5d3f008232e64,0x17031d480006d0,0xe5605e6f25256868a3c2,0x2216942a45428507ab00,0x226c92748f52c5000112,0x628dc00000006968026,0xd5b5d000000000010b96,0x7e6ddcf300e000000054,0x1d23a29c000023,0xe56b0b3029f9ba,0x444060002b12000183c0,0x4ae443e6440a8,0x500a000]]
set_option maxRecDepth 16000 in
def g251D9 := limbs80 #[#[0x54110501104c9104c110,0x58910581105511054910,0x5d9105d1105c91059110,0x545204c520d9110d8910,0x585205812054d2054920,0x5cd205952058d2058920,0xd8d20d85205d9205d520,0x505304c93048530d9520,0x58130549305413050d30,0x5913058d305893058530,0x5d9305d1305c93059530,0xd9130d8930d85309d930,0xdd130dc930dc530d9530,0x589321d932dd930dd530,0xdd932dc1329d9325d932,0x58d40585405814054540,0x4c950d8d40d85405d940,0x58950585505815050550,0x9d9505d9505c9505c550,0xdc950dc550d8950d8550,0x58960585604c960dd950,0x5c9605c5605916058d60,0xd89605d5605d1605cd60,0xdc960dc560d9560d9160,0x58d62dd560dd160dcd60,0xdc562dc1625cd625c562,0x5cb6058b604cb60dcd62,0xb7ebf9fe7b5cf625cf60,0xd7f3fbfefebf6fbbdeef,0xedfaee7b7fdfb7bddf6f,0xfbbdff7bdbeffbeeefba,0xff7fcfeffafdff6fcfef],#[0x5012591ea8b112ffffe,0x22504044908045658a07,0x8c03ca18079320112c20,0x1ebb00238400430801e5,0x82895104470c0086180,0x218504dac809b550144b,0x10712820c861811ebb02,0x47080d95501b2a903896,0xc0c861819ebb03656506,0x6d8832cb10689610c470,0x311c1863d730c7ae419,0x1c2063d740cb6c819659,0x863d750cb6ca19659431,0x787020b0e048e00091c2,0xe0b0e10e5c8211c0040,0xf0e1c161c39cb9072380,0x24161c60ec08c2180180,0x61c283c3090785120f06,0x682c38829761062e8201,0xc38d29761a3b02348600,0xb0786140f0a281e0c502,0x622502a4481e10583c10,0x4b6ca49659491eb99281,0xe686608d10c01a3d752,0xe5d8830b2903973200b,0xcca41c0141b8620330c4,0x82c3911b852872ea50e5,0x1b07872a0b0e54d5cca,0x3f802e0b0e6c6608d90c,0x52c0f0c5c1e14b83c097,0x3304708600e02c3962d7,0xc601e0cc03c098058738],#[0x1e0cc83c0993f80320f0,0xd0b2a9217932420f0a64,0xebb21656542f2c685e50,0xa3238642430c84fdd909,0x96246f2648c8e0519fb8,0x46f2868cfdc91adb1235,0xae88d6d911acb2237963,0x8d6d951acb2a33f74467,0xdc8eba991d2385467eea,0x68bc1a44d63482f067ce,0xc3ad15835a9ac6b48601,0x13563626a86c41609882,0x523cf700781619882c23,0xc6aec785e14f3ab11e75,0xe945e18f0ac31e37763,0x4161d70ac1ae21805c0f,0x1591ab1b20581644700a,0x1bbb203576400b0cc816,0xa2635744c2f0499ee013,0x4f654c9aca985e1131bb,0x5e0b0e9c5e1531bbaa6,0xf02a8161d78ac1af218,0xccc1615982c0b3078654,0x560d810c0302976500b0,0x1a02c13405876052ecc0,0xfc02b2380560b0cd0161,0xab0784560f04ac1e0559,0x587582b06b08601603c2,0x6a0b08d41609a82c0b50,0x2caf5b591e91c0bd0585,0x44612090c0415b657ab,0x61e110c04207877e0b0f],#[0x283c1c03b82800f03001,0xb14559628a470314fdc6,0x523838a7ee714fdca2ad,0x658a7ee9156d922acb24,0xc0b0f303616610c04c65,0xf0c161a702c24e05829,0x43616690c04d07878e0f,0x1a782c1cf05819e0b0f3,0x90c04b0782940f032816,0x15e0582a00b0340161e5,0x584bc52c978160ef02c,0x7a2aac5441616f14b2de,0x170b4d6e02991c053078,0xb7c160ef82c0df0985b6,0x160b002c0e02380a80b0,0x6e02c2e02965c00b0980,0x2c1e10581c2370564261,0xe20984ba130574161708,0x584c40b0788160b102c0,0xd26ae7a4e5cb4aab1690,0xf03ac2e17503c3e90587,0xb01e07603c2eb0783d60,0x605d03c2ec0784d80f05,0xd02c2ba35637472c4e81,0xc1b775636e3702dc1619,0x621806caeecdd51d9bbb,0x76703704e01a1db14bb3,0x23304e4ee09c03c0382b,0x3981601d82c3b92b767,0xc1603382c2e60583cc0b,0xb182c2e70584ce0b079,0x82c0e80580d0170d946e],#[0x2009162000f03b41e036,0x91650526c60a458c148b,0x20726c40e45881c9b282,0x23080e4d901c8b203918,0x41a44c83494303918607,0x450c348c10691620d22a,0x348aa0691830d22c61a,0x8c28691650d23081a459,0x125860282ec0615880c,0x17608d2ca121588213c3,0xf27001c9e18212c3044,0xf0a1d05d4393c1874173,0x3105d4612c18c41760e4,0x600420bb054165124b0a,0x420ba882783111b02224,0xc18d41871082ec209e14,0xa4183144b0a3505d4692,0x8216850c290618520c28,0x487082d06105a1c10b41,0x24a4584948a89291312,0xa460c948b19291532523,0xd8742b10e91852522ca4,0xb4b28f85621f1ac23d05,0x1138552264b0c3d05d87,0x278326bec64d758c9c2b,0x52682ea4d7d949aeb293,0xbac669061c9a0bb13278,0x6409614d2eb29a258334,0x1594a42b1948553290ac,0x4aaeb29527812a82ec46,0xbb1527852a82ea557d9,0x96258536baca6c9604da],#[0x1762c4f065a1608b13c0,0x424b06709604e20c3964,0x30c8646110c8b2219162,0x8e46051c8a0a39121472,0x5911c8c12391624722a4,0xec2b11d91854723088e4,0xb19f8d613e86ec7505d8,0xf43763e82ec7dc590fbe,0x873e830e7c9e18f92c31,0xa86e8917591221b92442,0x8b50dd16aeb22d25825,0xa1589120b2314162624b,0xd52beb1a527814a82ec8,0x21bb2541764a4f0a950d,0x2267d644cff049905959,0x43754efb069c9e053bfc,0x74e86ec9d05d9393c2a7,0x86cacd05959a143a7418,0x8ac9e09592c230258260,0x9609621c22b4382564f0,0x5ec8b0bd91517a4b08b0,0x8b2bd91837b22c6f6460,0xbe91807c82ecf24615ec,0xd657c4f06f97d8df2eb1,0x7c82ecf89e15f2fb2be5,0xb0b04960e0aeb1c14187,0x9606120bb3f27817e4,0x5862c8a0c54183808303,0x2c8994591818b22e3164,0xb1c591828b22e516458a,0x591648b23071645ce2c8,0x768882ed1246122c8ba4],#[0xd2301190a1e220c3c443,0xc9189e0a321b9468d718,0x89e12321ba465f648cba,0x1e320c3c643768c82ed1,0x12c14c27878c850f1896,0x9482587984b09310dd26,0x42769082ed2105d2420b,0x6870ac50d0d8a720b14e,0xae51c9e06392c343417,0xd1d05da393c1c743738f,0x9606693c3c725878e86e,0x6520bb4925879a4b0734,0x1c0ca4181944f05289e0,0x4b258196870529060a52,0xd62acbac949758a912c1,0xac4f075905ceb20b9565,0xacb589e12b20ba565d64,0x449e06893c2d64175acb,0x5969aeb1d32785a2bacb,0xba0b9d75d75a6bae74d7,0xb2542781a882eb5d7596,0x89380b04f0b509e12a2e,0x84b082e9617592c13c0d,0xa4f0b6105d6c2eb2d827,0x36905d6caeb2d95d81a,0xa1e05b93c25a2783b44f,0xd7213c1e44373c882c79,0x92c1e74173ce4f0b910d,0x2e74183ce82c79c96173,0x95630e4b03a09e072a0c,0x5112aca22560c44ab287,0x2aca4e560c9cab193958],#[0xa565e04acac095958527,0x5604b4bc29595852b2ac,0x53cac0a795863f2b065a,0xab2be95837d2ac6fa561,0x4497817f2b02fe5615f4,0x5628d2b0f1259da24abb,0x8d2ac91a560a34ab9469,0xb0f1a55da34ac2469574,0x1e5d8a44ab1489574992,0x60a54ac0ca95768f2ac7,0xb4ac2569783ad2b075a5,0xc0da9785ad2b0b5a5e12,0x3000012b096a560ed4a,0x808680e2015c020c02b8,0x4606300be8164028e04a,0x22f041407c40ec01c403,0x16b02b2052409c01278,0x480e1c1b7834b06480c0,0x451086c10381f783cc07,0x827084c1095612242350,0x2015ac2aa85390a4013e,0x6170bec17602e385a60b,0x435586850ccc18e43140,0xd41d2839b87160dec1b4,0x82b10121f943dc078a0e,0x846488b6112a21c04280,0x1225944a109201210239,0xa23141627a44e509a813,0x45520a7d14c4294451d0,0xbc2d005908b0215bc2b0,0xbd5177a2e8c5c70b7016,0xc62a0c431850300c5f60],#[0xf833946668cb5192a31c,0xd8f1ae0353c6980d1c19,0x87090df81bbe37146d30,0x683a6c7400e671c9438b,0xf331e443bd47720ed41d,0x7d80f921ed03d5c7a30,0x7e40b88090ffc1fd63f3,0xc4213841fc834905820,0x8a69139222a43dc86d9,0xce47388d6918c22fa459,0x25b248a48a890a11fe23,0xc96692b5253a4a3093b1,0xfa4d9c9a99332261e4bb,0x40f27d04f489d8939826,0xca50948828de514ca1a9,0x5c544ca7c14e0299052d,0x5ca2b665658ab7954e2a,0xb2396372c4457f8af41,0xf05b44b5f169d2d0259a,0x7952eea5d40b9997192d,0xc1718032fc85f10bda1,0xe46360c59188f30de614,0x98532dc6520c98190f31,0x4d189a0e33d066fccd01,0x146b58d5d9a9534d8693,0xb9a36f86dacda41b2836,0xce1a9c1537f06f54ddb9,0xae72fce4d9c8238de714,0xd6c3aaa74d8e8a9cf439,0xefd9dde3b76767cec39,0x867a8cf441e623c76786,0xf4f3e747c5cf7c1ee23d],#[0x8feb1fb63f3e7df8fb31,0x2281b9027202f40327fe,0x11241f6835905da0a441,0x10dba19742f2856509ca,0xe0895911e221a43f4876,0x2df459e8ae114d228a44,0x11c5236c46968c9117ea,0xa690bd20723ed47928ea,0x4f749ae92e924d247148,0x52c6256c4a9894d928b2,0xcc992531226004ba096b,0x6f34db29ab134926784c,0x13cb27674e989cc538b2,0xd4a10d40f27fc4fb49ee,0x9235218a3a545f289450,0x54f2a9c3532ea5bd4a0a,0x80aa7953baa555456a82,0xb8756caacf1586aaea55,0x161bac0c57dcaf3d5d4a,0x2eb3c966a2cb05910b16,0xde35b74b6716b6ad485a,0xd752ae815cb2b8a9700a,0x42bdb57a4af255deebb0,0x5a607cc0897fc2fcb5f,0xd87bb0d56168c26183c3,0x78c65d8bfb15b626cc45,0x25b6470c8998fdb1d763,0xd96832be6546ca2d93cb,0x4cdc19af332e6616cbc,0x40067becee19d3339467,0x1a48347e68bed115a10b,0x3ed435a7db4e9698cd2b],#[0x5d06b44d5fdab2353a6a,0xdb29b62e6c2ad7d1af13,0x32dbd1b69b6ae6d28d9c,0x7ce6f56de1dbb1b73e6e,0x1c3fb85c7074e06dbfab,0xa8e4c5c8638ea717ee28,0x9dd7384e695cc3396672,0x5d44ba5d7476e865cfe3,0x64ec6dd803ae1758eeab,0xbb97740ede5db03b4276,0x9e2d3c3b783aeff9deb3,0x1ef3c9e6abcb77922f1a,0xd937afaf59dea8bd2c7a,0xdf0e3df97bb6f70ded5b,0xfefb65f58be8c7cdaf8f,0xf777ec4fd1df993f1d7d,0xe01240087fd8fef5fc63,0xc502fa04d408580ab00e,0x19c82f7054e095c10181,0xa128422d841707a60e64,0xb30cd2183c2de855d09f,0x41587f10f4e1d7438686,0x224ac47d88b7111e216c,0x49160a2b0c5338a11135,0x6468c2d17ca2ec45ba8b,0xe38946f68da71a963364,0x9f1ec23c6c7758ea91cc,0x88a90d5212640d47eb8f,0x6493c90591c5230a451c,0x2727c64e8c99f92f9253,0xae395712a465304a3894,0x65d84b8696ab2cca588c],#[0x3131da631cc41982f2f7,0xd509a4d340a670ccbb99,0xa7074df49b9336766b9c,0x193b9275a4e8e9cd138e,0xff49f8f3e567b54f389e,0xe857d092a0db4132814c,0xd3452e896d10fa1e3434,0x202a3cf47328d6518da2,0x2960d294a4d749029105,0x294dae9a3d323a6094b9,0x44ba84b4fe69ed53b5a7,0xea7cd4d5a969525aa3a5,0xb156ceac95568aa91548,0x689acc55916b0d55fcab,0xebadd72cae0b5b6ab58d,0x8b608ebfcd7d3af535e0,0x8fdb19f62dac455869b0,0xecded98bb2c56512c8dd,0x11785c130dc1844c3684,0x2281c380771325c210f,0xe970440e2641ce0f1708,0x42405d858608603c1560,0x981e11152684826f85e0,0xd076182f0184565e15e0,0xa850644108e8306e8101,0xa86c1e82c0f008441f0a,0x51b0e492c14344443d07,0xe8409c30058430698286,0x519128460af08461840e,0x90d0c800048254182623,0x9030083528c2822c89c0,0x301258108030a20cb940],#[0x80344a0b2321b4050511,0x90ac1116410490b43a81,0x28d6344b0cc054420a43,0x1088349411d1a0520f0b,0x9999bff48563a99c4224,0x10c2fd4142130c1f0ac4,0xd3f2969cca6897845310,0x42cbb0325bc858408868,0xeebc110b0e10c8587086,0x917fe8408bba1510781,0x460650fe031def5096f5,0x7883028d2f6095099e1f,0x647cf1040652fa70a995,0xc197576ca42a861f88a5,0x4150b5f8485899b3f135,0x19b0cd708b3d0a892e8a,0x40ca3f9ec811b3f13d10,0x12f52751ffc080478d3d,0xaa4234fd2f24520fa930,0xa932f106b231ec04bb8e,0x2863d49b76f34b54720f,0xf9ba908e7b012ef9d02,0x90d8466f0c0a843d8096,0x8c9647cf0c0a846ebe81,0xd2e5458fdb80465339b0,0x3cb00410a8fc1d0042cf,0x65cef460651fc292b23d,0x4e68d8084d90871f1040,0x9cbd290afa06797ba008,0x2cce7af0233785299169,0x81947f0a4ac8f10c2183,0x882032947c41019b3bd1],#[0x8430656c7e0326c8438f,0x2658f0a351947b3110ad,0xc1122cc2e3b2a397c7b6,0x30fbd6045d11f1811b7f,0x45b3888ba8888875d792,0x6542ef818442d91ad9c4,0xef5083277a84192dfb18,0x2a2e71408654c2211a66,0x311439238f6381954fd7,0xa222239c907a4c44dfe9,0x88d94ccb671116ce222e,0xfa80212b8466f5220cbe,0x22474ae232ae788988cc,0x902116ce22653e222ea2,0xac8eafa80210ef08c18b,0x65ddb088918c41944e0e,0x1330f4c623e2a2452310,0x4cebe064cebe06411f15,0x63d481163e58c71f2a06,0xc1198126b3cc11a3e58c,0x486c7044bf1d25ab24b1,0xbfa74b5921c80ac704de,0x90c99bd02191bf408644,0x55c4845ba9094ec09667,0x9c83192c8f47e4887604,0x4973fb507359a3a790c9,0x33413a968d270968b648,0x5117ea219349277082c6,0x6532d7960a195581ece4,0xe0639c0289a3f2448fa3,0x61be122bcc8830df092b,0x6c2231c1037c24579910],#[0x1085fa048b2cf6c224f,0xe8d8084dffa2908d8d1b,0x12de644186f849a30862,0x9837924eedb0132cf971,0xb24637e448ccdfd48891,0x13670689262968b1d340,0x7b61118e081be124f60d,0xb7991078f2220e7b6112,0xc0cc2e8d8084c68d8084,0x6b2424bdf42c648fe02c,0xe1058c6633349209d4b4,0x12bca858cb524733444e,0xaf2b2432cf86222cf971,0x5039963f80b12336cc43,0x359864c368d74f092d79,0xff62324bcc674207d430,0x7f881179e633a12c48e3,0x447c60460f8550a4ccf2,0x28cabfdd888a3afb8117,0x73920e3fa0d3b650e5fa,0x9d8c9dc6bb08ddb04644,0x22eed844923c1a26143a,0xfeb6ac8ebff201166ea4,0x7e4562654fd850999a75,0x499997fe40228eaa422a,0x96a8a9fb0a133357f09b,0x802452fe1c306200689a,0x73ef8c491a389949967f,0xc8bcb1945cebd9190d24,0x1c5917a5c21832b75f40,0xc8bc63022c6386032ef,0xbda8c3d1844d908611f8],#[0x91ee79844c3d9889bebc,0xfec4642fb2b732ead592,0x4df6c62b139156ce2237,0x52456fe1844cb41a76c9,0xe0fde48211b96c4c9be2,0x9366171f2479e171d248,0x3cfc08bc5f080cb1ec41,0xe004cb239f81169e4248,0xe6fb635b38883f5058af,0xf8406530f44bdf02c265,0x241e7e045af8543265e2,0xeedd046591cfc08b4f21,0xab671103d1227ddb0465,0xc0289cec091d851589c8,0x24bcd60420bfc1008859,0xc7c0cb0f500424bcd604,0x577e6b0211727fe08a58,0x3920dba6009652c63e06,0x47c039c44d111ce48347,0xc8f8074ec0953ed626,0x6620a153ff52303327fa,0x4caf22d9203ca5ccb8f3,0xec8b2dbc774a132bc8b6,0xdf64c465b78ee94267d7,0x2b327f204c91f2bf22ca,0xf9164afc8d1656faf464,0x458ffd88c95f91a2cb95,0x4783f011437c24838fc0,0x1a3283e6052127e2e711,0x6d951f8dce20521f3e69,0x54a3247c2f66d9738eaf,0xe781344473920cb3236e],#[0x8d7b8192d7fd2380219,0x3be603277cc0645f5a19,0x46afe3b51c14d1df3019,0xe8546cfdf82994779e85,0xc69e0a661de7a1518779,0xeb29e82675a8b9ecc911,0xf1c262668ffca0989993,0x64d4bd896cfa5c31427f,0x945231ff5cc09245bcf0,0xc8f2ff4c108d0d1cfb9c,0x9c923ae7c30323c9f0c0,0x802132ad45ce72492b6f,0xbfa800650c3e4800cddf,0x57bf062658fbfc900198,0x387e00199713df17e024,0x2bbf40010819fc0032a6,0x6064cf5d80cb407c1854,0xf580cb315bbaf21233f4,0x63211cbdf97850019c3b,0xe9f0193a5d5f019a7fd3,0x9edc740cf0e18980856,0x2532583465ce38191fbf,0xe9757c0672f1f019333e,0x899c9d71024178f80c89,0xffa6c6423c70b1729906,0xd0dd3e03274babe0334,0xa4a15f80cf9f86e5cfd8,0x96394c83344b96a83317,0x6290133a79f960090134,0x14919f71d73e5a8919f9,0x6aa61064aa61064cf82b,0x98419138cc019474d604],#[0x8cb143e0232c675811aa,0xc934655c4f808a971ac0,0xca785e489fcb928cb5f1,0xb928cb3e02d12be39268,0x18392387f0080290c9fc,0x81791e9d0268da7f9d31,0x11942f235c6268806268,0xd3fce988c0626899b7c3,0xbc8c2f232ff12804c468,0x2882143c230bc8c2f230,0xae786119633c308c6f92,0x268d3c09a227f2e4a328,0x44d1077131142f239a62,0x85e461791e5bff4c469c,0xe5586c4671d626881791,0xc48538fe988c3ac4d10b,0x9942f230bc8e7fe97534,0xe3ef0a651e82a217a482,0x4953fc4c4cb9ae48cca9,0xfc4c4cbaa7f812473fc1,0x4bf9fb92357d50109993,0x8e594a774cdbfbf80646,0x854fc20c4ca871e324,0xec0c94edd0004283f520,0x1f5c021973f8b6065cf2,0xc0cedfc981915f118108,0x981973fd26065e87d7a4,0x656ac111bf93032c57fc,0xa0fa2337f224648d7224,0x3d11503fb2320f8f4441,0x53e448ca14f91232af2,0xb7f2c0032e3dbc806143],#[0xbf860325fd204a7d9a12,0x64b4231f60887987094,0x9fb4c2242cf97110bf0c,0x98c0855e79822cf97110,0x8bae242297f0c064f717,0x3b798c085b4232fecc0c,0x3217e180c95d003c8332,0x9791e88a341f4466e7e0,0x6f2481bc9229ff99711,0xc73cb8893cb8881bc92,0xe79d710230e1dc08d56e,0x6ffd42a7c091a847b811,0x242e5c37181212f37023,0x268d38e970223c3b3351,0xc6268831343189a1e9d0,0xedd9f45a062686313435,0x4d163c4b12a2a34043b,0x268998258f09c4d174e,0x6189a18043f62a6fb3cf,0x54587207a0858b564b06,0xf5491dde38b11338f17a,0x4c4cb212f1f2491052e2,0xd89927e31188cc9263c2,0x761e144ca9dbf3132c69,0xdf0b75c6492725aa8733,0xc9854a68afe1aa542668,0x8f40ce1c8b3d4a676e9e,0x7d033e7e58e8194a92f2,0xe6478fb947a0664e694e,0xd191920ad5cf48fa80f5,0xabe887bafa220afa2247,0xaa11358afa22043cec8c],#[0xe5f61d609a1b0e5a6259,0x3b1d8d09eb051d319db0,0x1e07946407ce4a307e09,0xcfd110be7646459d1110,0xd430cf64675a83f8a469,0x758fe292d830cf6466ef,0x88c54dc837a63404a969,0xf20626584f646451df3e,0x224796001963e5000cb1,0x9ebb019738d3b132ed64,0x7497ff71800cfdf580c9,0x58d368032a4bffb8c006,0xfc380c823c8448e35106,0xa3175af00658bac60460,0xd13441638868ccb537de,0x4d0b537ea9183f04991,0x52345d6a12357c7eb114,0x1a091c63811588e12f1d,0x123ae8893ff8112445ff,0x4d01b47824099c45bfe6,0xe464b1e19a315373ed48,0x6703f6ae2b58a4cd73e9,0xf5d6fe949233e0a80d4,0x6192ce9405efa1fd2926,0x655f8095fd20032f7228,0xc808fa867b011ebf2c00,0xc67c04658cf60234e798,0xfeb401967eb19ec0479a,0xf20aa4437728a5a00ce5,0x473920e7e4bf7e223ea0,0xadd7c1248d41e4145086,0x62a8f3664f2c8ea19a7f],#[0x16d1994f325cb5fd25b,0xa149247eb7da14920be0,0x34a79605a41674bbdf9f,0xb2aac7c0d098ce4a0dd8,0xe39a32d69724a3b8d2d1,0xe4cc1e23a58f0cd196a6,0xac912c6600cd01ede649,0x57840ac95e102b257840,0x244b2d7840ac95e102b2,0xd3fd2a19212e4a4227fa,0xbc2056427929064f2520,0xc31de56b892184f25212,0x15ee566a21b9eb08d850,0xa1259444e13ba49bcb28,0x85250aed73bb10b4e6a4,0x9ea461380f235250c0e8,0x37a0c328427b8dcc42b9,0xd4f10a80c28307220194,0x64060f0ca1380f235250,0xdb70b2a577de1952bf78,0xc7bb10adff646e8b3575,0x43de46461a5f9a46104e,0x949ee37310ae67a9184f,0x73c86f7b2b61125dc9bd,0xedf62858b7693243174a,0x983b1b382dfd961428be,0xc3b1b37b68b605186097,0x972cd2f0c0b809a1fa5a,0xd437b69a5570a5e654,0x9e13333c06a790b6fd55,0x30d0c2971eda4cb1f0c7,0xc07c23d67572ead42439],#[0x67e0eb74e4cf96b144ea,0x212d0e4c3430d0b7ae42,0x6a4d1687261a186a60d7,0x4ef35df139345699747c]]
set_option maxRecDepth 16000 in
def g251H9 := limbs80 #[#[0x3040e002870208103,0x1019902000060c000830,0x4e84083820106000030c,0xb0c10140070000081020,0x4020008536107832000,0x14c00083100c60902250,0x120300062c10b002410,0x46c08004142800040082,0x800c08900022c0800,0x700c800704040811a,0x10010084800008187060,0x810a004871a080010404,0x42c2c0801054010042c7,0x4641865420488100000,0xa0451002100090020302,0x4205000c68020001862,0x41010010284080051800,0x104545800e04102120,0x8002040940e5018f0014,0x3040828108006010800d,0x4006861c07b8f0c2468,0x20118704003b6000c682,0x10b000e30181020ca020,0xcb851200b080e1030300,0xb8008100130e18280325,0x560c21f14001810a34,0x40a04210008c39700286,0x1008d0e08b00003800,0x65403b06040000414085,0x2419d0e7003514200102,0x89800a48389220008318,0x60302105810e0800306c],#[0x1a1418619080441f1010,0xc08184041c31e1e601,0x4044020a06c81002c81,0x63c90e0224101181c580,0x246130004080260001d3,0x40030a70b84043c20810,0x18a08100840e68b00022,0x1438096ab200d0062454,0x2004018c107408602141,0xf7d66f241ad140018,0xc0d080005141879c0000,0x700001097c40c114620f,0xbc4d085ac00041f7d6,0x40000000010c0001881e,0x470019c8ce845d0d78de,0xc1142b2aeb2155022547,0x30b99183e57702571eff,0x12f26940ca4c436d44f,0x394c67407084e1c17f00,0x115961bc000000012128,0x5e00020a2c2655159ea7,0x46708f840006b36d6,0xc5c0000,0x38cc0000096,0x43694638464196800000,0x16d740006,0xe2000000043a60000000,0x3ae557f63740005864c7,0xc8b925ac,0x16ac0380000000000,0x36700000000000000000,0x906c0000000000000002],#[0xc2e48a4,0x3bc415c000145c000000,0xf61b0fb70e58,0x1229705d4c220000011,0x300f7b1f4449c00,0x39ca00000000074c0000,0x50cfda0af88be0000000,0x14ed0000322144,0x2b3134fe0d980000,0x150a3400000000000000,0x323000100a020b800098,0x2d8c00003653878c0004,0x7b86a60aa0181c5a5708,0x3c3019aa0bb200824d87,0x2cd880005571c9c7813a,0x107ec000228bd43a699,0x842c58309e7511000000,0x22428ae600008a19c09c,0x8b345e23950000000,0xdc8000014300,0x0,0x21ca764c000,0xa2b000000025fc413a00,0x38a500007618ab03c55a,0x84ec000,0x3460001a6371c581b300,0x30ad787044108a0a8cde,0x45c00000000000000,0x11071099800000,0x61e70bc6c1658ec80000,0xe6000341c438f98550ec,0x43290b800020a4000094],#[0x30d6d8de07d208680178,0x1899c0001c1d443e000,0xb936579c64f03619bc00,0x6c8c09c4f12587b48586,0x15415d0000c177e3d,0x5a87e01058095000000,0x510b8000d59892b4575b,0x18eea0cc4497338e929,0x41964f983840005be600,0x23cd579092450a62,0x72e6ba50800fbf374000,0x871d50a0000000604b34,0x51bdb190063807100007,0x480002142305683198f9,0x88490ff5419633b01,0xb800c866c792ea6adad0,0xb71156000021d7603,0x3d552e6d33d8ca1c900,0x2445000080400f4dc67c,0x828cf61ed000043e8000,0x43347cf8c8b1186a94c3,0x9ae09c819e0002874a,0x3aa4168268000f6be000,0xd7f384fc0b55a5e40,0x116ec39e96cce93e90f8,0x876418480000000000,0x8a464fc10d0000388d00,0x840c00032226,0x1e1f8c2b0a1b83ac000,0xc4d805e4000000000,0x8000393556388ae20108,0x818800059d6d002a52],#[0x3ea00008d2c0c5f8f900,0x25643,0x3600029e5000002ea000,0x29f0000000000003adc3,0xf194608908f600004532,0x606dc29408d,0x89a77b80002238800000,0x795c0000f654ef580001,0x5f83080000000443a2bc,0x80b07610720000613031,0x4446852aacac0002,0x860db004a238c0000000,0x489826400029d64406d6,0x1c4624e00000d200006,0x3226000021cfac9,0x85f71052dd15c0a00,0xc000000051a543980000,0x3c87800004108038aa15,0x95104fe00021f9800084,0x13481fc071c00031a26,0x820b9000041680000000,0x6778000000002c980,0x8cd9f81100000003c3d0,0x9e82635817c61464c6fa,0x84c08f4a8a40b03921c6,0xf1958235c34010bc0006,0x854a10053000096468e4,0x4b0942c86622dc34544,0x205ee275946cea50462f,0x7e8d970730b30c1a262e,0x3ebb3b60c2c1d6223904,0x606b633577b3860e0b8c],#[0x1811a19a0151404801c,0x7700000000241800000,0xc959b865c8dd11c00006,0x4cfa481e304691,0x88e80000000000000,0x3226000000020c00,0x8a00000000000953c000,0x2b691bc82f8069000004,0xe069a3a10000c8910cee,0xa08c595dc2a1ac4628c9,0x12b47c1ce88108800001,0xe210689b0000806f03d8,0x1f0b3a1ea2040165b035,0x893f84e09ce635645,0xd1f30bb00001883ac390,0x18558000413c071,0x82c38000b8719b883300,0x8000000006fd00520d32,0x10bcd12b312e495d81d,0x1ab027c0268074e00700,0x3dd1d21c5053050a0a4e,0xd269390c402155788289,0xb343b9647a167e46a10,0xf045617648f310ac0004,0xd43bb01ac1a20712236,0x5700018140000041307,0x685bc9370bfb08c1,0x1546a32ec2e0000,0x1d2000080b314c000000,0x80000000c0b8439457e0,0x9200030a080000001063,0x254448886d71f90c1341],#[0x800000000831052c0000,0x15fba33000008b7,0x86f40000c7c243000,0xa075800062cc0001ce30,0x7e00000001bf40000865,0x247c2cca19c000000007,0x520122b380dc92c00002,0xcdaa2e1778000d76c831,0xc3c8066701b044a08,0x1083000004fd2b978290,0xa7838025322d6c8ce804,0x84000020bfc6,0xb004019504cc00035150,0x280000000620c041a0f4,0xa1840600001236018717,0x459100000000c16c0004,0x4b407005198247349107,0x3600000000000021e130,0x62217250ac100002,0x649dc478000,0x3dc895207020fb000000,0x31390000d0d800021766,0x107bc000000044b6000,0x15500000000c37a16c00,0x46ee8f580007,0xb28351060603a015e000,0xb6300010fbd13ee382c8,0x7b62000188060849,0x18f4222909190000000,0x2562031e13b837400,0xa1a0a342000012890de8,0x6c0559c3398742440071],#[0x14d00d58df7c11f886b3,0x92318a6b734381158220,0x662f301800000f81e044,0x80b0844108446139a7a1,0x85c783b5000108600df1,0xdd698400024073620104,0xa6242fc00000000000c3,0xdcdf8000000181c917af,0x80c0000000c6e7858,0x2b500000000c42ca9a00,0x1cf4eaa18372a8bc0006,0x832d1aea384831501f,0x17652d9c4e4216d00,0x3206a3990000900f04e8,0x738624012c2a20556000,0xc13964a032800068da09,0x314b0b9200004b19246f,0x4606b8000215c0000000,0xabec28801081b800b703,0x40005b0f00018e04116f,0x14059d8219b2ec7e8c15,0x2d8042742b4000182185,0xc0f59b5b0001826d23ae,0x11df605d0001a40,0x48b496c8b8c000000000,0x89d00000,0x8750000000047ea000,0x193002e0c47c2e622900,0x208e0dfe40e40f70584,0xc7d8000,0x85577da0000000000000,0x2243fa51d642c8880000],#[0xe0ed780000000583887b,0x1040000aec7cdcfa58a4,0x59bb239782caef46021a,0xab212b02c99f360a7302,0x91d0000021021b843b95,0x3156c3aa000000011d4f,0x2c00010e88000c1bb890,0x186000067d40000a2649,0xe1c1c495000101d51540,0xbe00000007b1207af8f3,0x66e2c8d9a5544,0xb0588000c3cb84580000,0x122562538000c173a9c,0x656000039d7800000,0x62a004688c7c0000,0x7912551180000000000,0x8249882a0b2000000,0x30e61916d0b08f040db8,0x74ee44d1853ba0001100,0x94ae0002098800008,0x274494000001630010,0xb321b517be0db9004000,0x1f283bd8a30000484744,0xb50e00009086000048c0,0xd4000303c41f0c7ff216,0x41500000000000000087,0xd1680000c4de00030490,0x8b1623461270001aa7,0x60b1e46a1d0211100,0xc00000000000843f0d20,0x58aa49027800000016d3,0x3870000807213d241a71],#[0x434d9666917fc40c,0xbb019800000000000000,0x807474f84d322a443d04,0x2550000052e000117a6,0x226d700000000458e000,0x38a065481e506f010c81,0x2029a4b8d527605944b2,0x56a7d90a7c03b34a186c,0x9520001a2e6c4cc24150,0x421467468bb40006,0xbe64240834c355067,0x5cc71a87c4600a0f300,0x6a1e865e0da718f7,0x6a0003d29b820c8ca000,0x28e1300003213e000048,0x41f3000085400002,0x154702000649615,0x26544e2092f42cc2f600,0x81a561d077aec1772473,0xbfc8a00ee800000d7066,0x14601d08b00d2b8000e0,0x71840000060f85391e34,0x6e841c0004182c0688d4,0x34e42d28b6ec66a35f02,0x822e68c406ff0ca4205e,0x5ee582e1f9c50a0d4,0x55180000000000000,0x70dc247f07506ed00000,0x1402800000004766803,0x44520000000068bd00,0x43f7000000000003,0xd4000000000000000000],#[0x8940001e244000433e04,0x15e800052b084f40004,0x5ee05e236ea710000120,0x84607a3ed4c0006105c3,0x889a1103,0x21004400004880000000,0x35c07aa00001048000d3,0x2861000000000000,0x800020ec0000865920c,0x312d000080,0x253f898f000101330608,0x3ac0140000158f738000,0x298e05,0xb23c0000c4e0488e0898,0x400041a500018a7,0x2f800000ce51acebca00,0x48dc800032ee12091b08,0xb48da000020b47484710,0x84e00008dbd9ba8000d2,0x30660a3085f48ac2957c,0x9a00030dd80000000000,0x34000000,0x5b27039e000303f0,0x112480000000f194000,0x46358ab9d961b4b00,0x6039c0128dd40000,0xab9f83000007340000,0x4a007778943101013600,0x458982640006,0x7000664024a170846000,0x1978241aebe06a815547,0x7cdaca2c9607c3b0052a],#[0x92918420dc1db0001881,0x11c866c0bc916bc4a806,0xd0a923caf49609901548,0x183ea8f08000e4fb114,0x184003ce4ce828800000,0x1d2940000,0xe00025da01fe8154000,0xd9c537e33a117800005,0x1af00ac47f200021872,0xc400fd1aa322746b4000,0x559668ef21c7bf683,0xa5750355313000009e38,0xf58b690785b50091e038,0xc07d8238257c00f95,0x8c4a1c30001001418a8,0x60000000000040c6000,0x192d1423644806,0x205b242d43290f8c4688,0xe02b505022ee979a000,0xf571060001029239bc1,0xf1c28a8444bd221a19fa,0x4990220b12378f19702a,0xa8405202341175c3f45,0x909b039d20f0,0x5982d780e807dc05409e,0x431000000000000000e1,0x40007a4c00010b7dcd28,0x867d226f8b932d6117,0xa20f1ec0001144fb4200,0x21a38000000000000f30,0x39c50258000,0x84668df35d5e49a00],#[0x30722049813e4e761058,0x1863509110a37110000,0x2644af00ba090c43c00,0x38a0825342f810fb9576,0x4e0000000010a1322000,0x69360000000430a01,0xb10d82bc01de00000000,0x1067605414b0694,0x29c488e0000000411000,0x1e20b0348,0x96000207521280000000,0x1f040000000088,0x98cb224a000000000000,0xff03fd111e11e00018b0,0x3f8144a000000001b4c0,0x40000000000000000004,0x8a00000002260000003c,0x63b0bc0da2388fc7,0xe457fb4a36a400002390,0xd00003248082f82a6913,0xc47720b7cc5000003,0x410b0000118a0408,0x822d140e3c0c110000,0x1ae38000000000,0xc0ae00000000,0x318c0b3c0000000,0x37100000002d24800000,0x3d464,0xfd8a8de4169f2c070850,0x31b00000000000000055,0x4c0c000000015d6e,0xb0000018900000000000],#[0xb51441ff070000000086,0x6137242ec4c6621c0007,0xc9462a45d000095fa864,0x96f102647d000006,0x70b7848a3616893e4200,0xab0d8c0006b2c83650c0,0xa7e0001c7e6081606504,0xc9481ac00ad6d2722f0,0xf50ebe08ae31303fa0e6,0x46f0855887387ba012c7,0x5a526061c1008e58d608,0xc8063e2288a6648f884b,0x17de589cf23c3ec06700,0x21a621ea7468ab2501e6,0x69ea49df651f4976a926,0x85950b960514a89c5,0x11e620fcd12601280000,0x36007c000202d33508a2,0x49e0001465d072e30d02,0xe02de45600010a840004,0x811c00002bf692a0b4,0x12e981a1028000000000,0x1207c30280c1828711ec,0xaa00031e160f60000000,0xb49a22cc0876a6876,0x52420000000000010188,0x50000582e0bc,0x13b61d00000000000000,0x108d00000001242c0002,0x1c87800032b2000190b,0xb35f112000000060e300,0xa9506c0000d9f2],#[0x8c909e0000a33a000,0x190a03200,0x23c4002a00028280,0x66091a5d500000000000,0x97052706fc00062b117,0x307a3b3700000002e3d6,0xba6ffc0001b54d432000,0x44150f581c0000221607,0x43fb05c400000000,0x168d0015dc949c28e000,0x32087488abc041a06f35,0x6cda0000000000000000,0x8e08e0000239216c8a4b,0x187c6330736da6a90887,0x4000430537978cc814cb,0xbd01e8000000046af857,0x83240000466e90000,0x22842cb00010b980000,0x0,0x362f0ffec04000000000,0x70f4800088ec000259a4,0x4c900f20001a3c,0x47dc33d09b40001c2600,0x1c95a43f044400000000,0xf400021fe648cd112000,0x2b542afc7811cf800053,0xc1c00331e1ae07571fb1,0xb9128c0000000658ba2e,0x84900000000610084,0x6ba9000041080000,0x420800088b0000,0x12500008144000780fd6],#[0x174c863002c28d0019e,0xeb87380002b32d594000,0x8a200010d6c000426294,0xa06d000088d6000322a8,0x8783e5d9f8000113c715,0x439000001ce11d61fa04,0x8432a01a000000af2136,0xa06f610ba0000975d2f3,0x3c2082000000006b39c6,0xc109217800000000da2b,0x1ba2d208a00004791840,0x27bf69c644a187828382,0x1912a2e847b770940006,0x78a21f183104e0000000,0xc3fe0ed9063630c55,0x400022be000000000000,0xcaa725fd80000000821,0x960000000016ca0fd09,0x74d060f8d492110c0002,0xe1a3252647ea31be32,0x7be3d900,0x9480000000ca080000,0x598e6a05c00000000000,0x44200018a6800062c6b2,0x4da31b36766108f80000,0x898ff800002490001d1c,0x3e448d2ed0000030d6c1,0x25944058500a7140246,0x6fa27000063b906dc000,0x161c1da00014324429c5,0xa0ed000083f089cfdace,0xbd2cbb20ff873a27f05b],#[0x2e790930d0c000445a42,0x400002cc51fa00020ad8,0x18b4621380000001cae,0xed2046000000,0x3c045a4a36b182f3dfa8,0xa942880002074f45f910,0x10a94175000045,0x1d58,0x7e00012020000b0c6e1b,0x47715a9a11308ebc1e60,0x4593c0c8076e081e0484,0x25652b6f5308c9,0x4b1765b659557f801300,0xe23980004363e9232146,0xd78865222e4930000c9e,0x3a2074b86e9148e1a833,0x213080000000a8cd02f8,0x11ce0000c044000,0x2700000000d4da22a00,0x6280000259c,0x1c9e400000000000000,0x39000018498000000000,0x211b01df401c00000006,0x3a000000061390000000,0x80900018f2f164410107,0x38bb000000000000,0x8a9800000000001918,0x9324e4a3e200,0x31b6f90d000003b155e8,0x322d0000000,0x3404000000,0x2294000112640000],#[0x59dda7cc2ee081,0x46d68ae7166c25100,0xd940000000000000000,0x1f09ac00000000000000,0xa93a5000002011800041,0xd188040e000000011703,0x83830f0bd690c10d0875,0x185844e000244461f5a7,0x358fdb5734ad8e46c914,0x2a9822b8123c1dc064,0x1fe61db4f33e2f800000,0x8667a0f401b9,0x18f61830bb220000000,0xa9d0001847c19e000000,0x117ea0dcc4492bed1294,0x10a9c1bb23ee0000000,0x2d5150ea2c558f000000,0x410000000000000006,0xd60003d9cc2ff14dc000,0xaa6c000000085,0xc23262c3000000000000,0x22320495a38c80001024,0x84b000088ae255800017,0x95a40000578e11380004,0x630400010da,0x8ba434e000017e20fe00,0x1]]
set_option maxRecDepth 16000 in
def g251D10 := limbs80 #[#[0x58960541404c93048110,0x3fffefdfdf7f7fd8b60,0x5c822c0115008a0044c,0xb10b54862c0217600ba0,0x28a8105d842ea217316,0x494321b9124c886e2516,0x2ec437521ba105d092c6,0xc562c0a17648b020dd88,0x30dc586eca17651b928d,0x2b230dcd86e4c76262b1,0x7563b2b159586e8c7646,0x9017380b94158a02e303,0xc2ec6d6231b8185d602e,0x5c246e6e37171b838dd8,0x1055482a64017390b8c8,0x1bb2055902aa817620ab,0x5531bb08d5846aa23531,0x4257651ab28dd8c6ac63,0x8aae257612ab095504aa,0x5590aae457622ab11554,0xba95d94aaca55742bb21,0x14ab0a55452cec55762a,0xb5615aa0add8d2ac6976,0xec4b5625a992d5c56ec2,0xc5aac2d6765abb2d5c96,0xb558daae4d5626a99355,0xabab5595aae8d5646ab9,0x763a3b1ddc0eae075328,0x2f7707ab83ddd8ecec75,0x2ee6f5737ab1bddc5eae,0x1046019409603300d800,0x9827612107f03841980b],#[0x110fd07943941a80c485,0xae453228413a89384682,0x35c1a28cc06242ec16b8,0xff07ce3d21da8e6c6fe,0x849823e117489043320a,0x91554a70515278933896,0xa86333091788b785962b,0x911bd4d9a6aa34799e8c,0xfe07d83dc1e44ed874c3,0x44e22150c0848417a020,0x52ee95849e24491c08c5,0x952228553f09e34dfa67,0x6d5fcadf55caa694f6a5,0xda5d8ae6d6ecb5a599ac,0x2c591ac686253095804b,0xd696a8b4d1a2ecff669b,0x38d9c20df16e1b685b0c,0x4f1976e3b0dd44e8172b,0x3bfa5f86fa07bebd61e7,0x81830978984e09f02e80,0xc28f30217c18dd0d1708,0x81830e03900418842a36,0x370320a1445020e8640e,0xec1c2382858482083868,0xc8a04e3a0a048201f8a8,0xd01921240f4d2088b114,0x9b46a58801e180a84a2,0x4668440008862f190992,0x8ba2b088bc50887f1309,0xc9819b7df2b5823af240,0xe822d590943fcd12f630,0x90f76503cf9487047dda],#[0x134f94960471feec4d20,0xf88626bfc3110a2fcc66,0x7fa504235e142556f02d,0x7024ebf203048ba2189c,0xfd8b135fbb15142f3414,0x20459f3d25811eac84a7,0x1c491c3ea129d98917c7,0x3045cf844abe8148aa3c,0x9f0896ac84b564253eaf,0x3559096ac84b3d258118,0x798091579809162e7012,0x3823cf5487047bbec895,0xf486116f387f11381fa4,0x48efde260661d56122c,0xa4adf6d6429237dd64b,0x848d3d5218461fb89b59,0xb56425bfb276c8a17c97,0x724241e5cfe227aff644,0x2848def3687242485f68,0x53019b7c00a11a78e168,0xc00a11b789f41423f76a,0xb81091efcc892fcc8937,0x1091afcc892efc44a3f4,0x7a7620099cbf112cf5eb,0x1f2bf21c4212b7b4122a,0x89eb78d89c567e6a0848,0x8842387da30c4cc7d661,0x115d9c0b7870c18533b3,0x38162f4bc4404254ade2,0x273fb8ec4d395bc4233b,0xd248c5f6c431331f5986,0x848f7e644835eb24595b],#[0x7ac424619c42451fa5c0,0x489cdea324245e64493d,0x1334fc1a2a47d1eb062a,0x2dcb0a35464846cff425,0x2b89a423e5f821423dcf,0x44e5e7a0d3d54e0e2493,0x413e412879f089aed98,0xab930123d9564277caf3,0xe7a4b0232fffc5880491,0x2483fe3c2269f3d25811,0x8468fb330328fe0e260,0x13d5568534bea0c631ac,0x6bbd45d1acd8a3001703,0xe7ca4b023a63294a19b4,0x228dd29178913d521c11,0xbc46370f2fc452bd6ea,0x6f83a88bbca]]
set_option maxRecDepth 16000 in
def g251H10 := limbs80 #[#[0x42040101100205007000,0x422012940400800c43,0xc305300900118204304,0x8504708044a1521010cd,0x300018000400000104a5,0xa8004824108340008310,0x5d049042281045440,0x820801c20012442430,0x4000c10020800810031c,0x4030c90c70800c2002,0x10400830003c50002580,0xc00dc1030151c004100,0x4a2440400c0380240049,0x14301d0052812801950,0x1ce1cd04300b2c314,0x148d0c528814000c8c3,0x60410150083810450000,0x3c40030430037c330200,0x87401141040040145006,0x200400730d00d5006001,0x4b00d04e28000108004,0x430409410073055c026c,0x4181dcc08504209a1550,0xb690000ea9000009,0x0,0xfb58f107231cc0d51764,0x2000224147080007998d,0x10333af2176a850a1,0x1a1040c2441d7000125d,0x3409c7a8000000217f4,0x11784a416165a621f300,0x1c057740000000000000],#[0x36000219783e0db1f939,0x4a2b0ab000305700000,0x4b066aa83ac00,0x313800010130000000,0x1f0001844d8b80210,0x262c5b8000000000000,0x80f9b400045de253000,0xb14c00044c800a0001,0x30cf37280,0x1b2817000048ac00,0x8b880bcdbe0000000,0x289f700002a300000000,0x1dbc00030acb1ed13744,0xd14a080001370000000,0xc77d90a0002e200a70,0xc653c55000000000000,0x15740000003ea0000000,0x62e2b3c97a45f41f3257,0x24dc0024b127985001ad,0x800095bce43024d69bc8,0xa85e9b125455cddc4da6,0x52000000058c80000001,0x6c636009000209042044,0xd76110e0001886d28497,0x2aa93009ec8810fc18f,0xa5a46713ea960001a895,0x345d499318290,0x80f00020e500000004ae,0x5c4,0xc30800043c8000d6e00,0x793521f45a305318b400,0x4aa8000],#[0xe21b6000000000000000,0x495200010f500025b031,0x1d833fd0c90818000e2e,0xe591564873e04a17bb,0xbf3e800046a0000e8200,0x87f30f,0x8b72584000d848000,0xfc031f3f3dbf0a371550,0x8052d6a400003c724c4a,0x1c79744000f6ed59a330,0x7a38261070e0e22271,0x800000005ac400000000,0x7908000b284000000203,0x362162000322ac4a1288,0x7a073c41400021d4000d,0x901400032ae789ee3951,0xad1097d69400031e,0xb3046c060000053dd8e0,0x9001318500000000003e,0x10ce0002286000159,0x210c00000000000000,0x34f20ff00010a80,0xf2b11660000a09400000,0xc10,0xeef8cc00006580000000,0x100020e300018160003d,0xd6cc000b82212e27c88a,0x4be90b00022980003124,0x98000b5d523ec578a8eb,0xe17b40451580002a8683,0x1ca0033cfe0000000847,0x37871329d01951c80000],#[0x4e70d293bb0f000015,0x77016b00029e0000000,0x317e00000007a890dc,0x4597a000000000000000,0x219b968a0fd000000096,0x1bb3679a92356544098b,0x7972d4000c116c5ebaf7,0x50015230402c00088821,0x967559bc5150a,0x741a524823e5a0003173,0xf800000f3035000202b5,0xc2c40003aa5c7b804e0a,0x61dc255a270002154037,0x93ca9922e719c000499b,0x9a1906701880000000d,0xa164000467c0e8d4e800,0x2ab0002c6267c4082,0x7000000032bb00000cd0,0x76b800000002c042,0x25b00000000000000000,0x1b023c00000001ff0002,0x2121000000088b44,0x2865192b70b167241c00,0x7d11ba00000000000000,0x1896000000089280002,0x35368410000000326900,0x2278706c000b41,0x64540000003e762290,0x9435f2130002e5bda380,0x6f400000000000a1224,0x2f557b17511d40000de5,0xae5540000aa396b40004],#[0xe42d13650a14848056d8,0x2ba62ae188833314188b,0xebb5c00000000000c7e0,0x6ca680000000000da735,0x121dc7f4000823ae4,0xad00002618000c99d11e,0x1eb5e5fc00000001b31,0x286a58d00,0x46000000094f3d9f000,0x92c2662050001e9ec0a9,0xca04c00000000000af64,0x1320000062ea0d4a251b,0x51801780b704c000065d,0xa96adb7c00890a800004,0xdc5a518214c0002d7133,0x3984c29bcc3704,0xc0002541c0e415c0000,0xa000295102b800000026,0x18b,0x8c75aad1440000000000,0xa000015df0d45549170c,0xa26a537617a000317d0a,0x485d0c5a3d5c76008,0x13b5931a55042de60800,0x55abc00067d406d4725d,0x202c0000000000125,0x10aad614e4f,0x24a0852b40800032320,0x792e0003d5eb13400000,0xe86707800089bb08b14d,0x3d7a86613a60b06c73ef,0x3e9a6aadcb385d01],#[0xc4714910002042848c00,0x321100c250000c61d0f4,0x3d16f00010a4413c000c,0x2fb1842418000c5,0x19a2054000401c000000,0x8b81f4000183e0410001,0x20633560a,0x48df0b727bc000361400,0x64c000428b1fe000110b,0x1c2939f3e5c00002100,0xe1c6000215741b800000,0xdb0e5a705d32ffe2402c,0x47000103a0002133c946,0x67a8000192156278f42,0x10880000000450000000,0x126000115b0000000,0x1020512400000000000,0xd1891520001ca000,0xd346dc00000031e0000,0x5e00020c7000207f79b1,0x9000110804f000000016,0x53b323d478827,0x2a660e980c0004540000,0xf800040ca11000004ed0,0x8000000220b280f144c9,0x411000396c64f0000844,0xc1000219d8a6761140b8,0x7670000ea5515d00000,0xf6b393715bb0eec4e800,0x4fa1e300032239ac8000,0x32c2e280000429fdc58,0x2808893c0005aaf5c800],#[0x5608086464400086c,0x1dd59c245b0c80000000,0x36bc0000003c,0x3071000229f000000,0x2a1700000e1000183e,0xdf058000314085680000,0x32020003025c66000043,0xdb700000000002270000,0x1802131f964c80000003,0xc71400000031b4e3710,0xf0c4000000000,0x8da07400020f34464000,0x6c000b1740eaca9c181c,0x21640002238000000088,0x41e388488101f747d,0x6980000000,0xf5b800007920e7b6e80,0x1789443a497deb963800,0x2e5700001a90000000,0x4400004b663300031890,0x1d9b0af361c76e208304,0x8d7f8a21e743f1c6b000,0x100000000ca4c0000001,0x9c3662830000000c3b50,0x8805079c7641d0eaa961,0x27526f68739b801d4000,0xb8277283156998db2adb,0x229580a3978052208c12,0x82280f647c06a3000,0xe40997d8688,0x172ca5c95400000,0x19cfce9d0ab414432803],#[0x59400000000000000000,0xc8848a258d510de,0x141d02bd01b95e701200,0xd1854940002ebb000,0x9e0a9400000000000000,0x6f068000c6c607702831,0x923ce55000324b000000,0x30c0004190256ca84000,0x3626c0001cc089a0000c,0x4000f6cb23a360000010,0x40684da16d450edc1c9c,0x6ac1aa0784000000b,0xbca8b1e5543c285a9300,0x1a79000000083421e,0x18fb20dfa7fcae,0xb3183868fa7f39ac0000,0x7d6dda9d09b00020010a,0x13f0001047a98c000275,0xc6d6852460000000c425,0x20279694504ed41b41dd,0x882849e3adc000000181,0xc774003486b175,0x5860a000322900000000,0xc8d11db489c000b1,0x21ec0002db6000,0x194c44880000000,0xe8671407000097e00000,0xdc09f00010a3367694,0x2ca0b40000000d0c78f6,0x8000070c10bf485314d7,0x4294844e5d26379186c4,0x3417f1a9215f6d],#[0xe00000008381235f46c,0x2c5460b100001b985672,0x7d716a000027489e927,0x141ec570000000,0x6150,0x258f000108700008f300,0x24e417ad1a569000048b,0x3e9421022390003,0xe0001180000304844600,0x889a42bd4bf2c3432c03,0x32b90000000497303b,0xf0decb18da60002d370,0xf13546b509d000321ef8,0x69b894000f1285a840f,0x25000000000021039241,0x1f6ca3b5a048662,0x21600000000000000,0x2b400086e011557a280a,0xa060001287c9b62af0,0x11ac00008a5276400000,0x17c8a59015c2e4000c73,0x43a400000000002178,0x455860b635800041ac0,0x99b36a6d6435a3000000,0x348d0000000d71de80,0x64000c1bfa9100000000,0x24ad78dd12c000000081,0x169c0000001258000,0x2275a52de710000,0x90000000000003d0a900,0xc6649530002216a5ace5,0x1066000104b4450000],#[0x74000000011d83b3ce80,0x114b42c10989a,0x252445acb10000000000,0xdc4ac9dd49ac2b20001,0x183770b808ed05500000,0xa840000daeb034e7ae55,0x369a5e81261dac2ed024,0x900000003280f658de80,0x68410000000000128f03,0x630000493,0x3358e1c558604d0000,0x306fa044845c00000000,0x88f36ac89fc125000015,0x1ab1d35aa01de42360db,0x3bdbd4302d5a00001a18,0x5a42f11d5000025f00,0x190c6bf00800036a9000,0x67a7a05750000000862a,0x248e000140c0002d,0x0,0x2e4b0000000,0x0,0x553000000000,0x15f00029d889f0000000,0x4270000e7596e6,0x13405271bf00000,0x408c243006400,0x358000000000081da147,0xcc107000101e0000000c,0x143270631cb00021aec9,0x8e84a0507e0000000000,0x832208000865520c81ef],#[0x89ec233b9599,0x3e36000000,0x27b20389640000000000,0x50000000085bc6380003,0x800000022220000000f1,0x2131c2eb94198a,0x898f161c4c212f0000,0x6482448507000000000,0x7ed94d00030ef40a400,0x2595d683e52b7a6c0169,0x20000174c1a0f57212a8,0x4000000153e000200f82,0x5840000000000071a,0x9b82db0c68599a970000,0x14912218817d29109f42,0xc738000c3e80000597c6,0x3691cd0001061443d4db,0x14198890699c81c000d,0xb1a11420a3310200,0x1a7490829e59a4000000,0x54a4961704a400002d4,0x11a40000000d67b4,0x87b400081412c5000224,0xc74416c00025da,0x15c0e54098014e0,0x9a50d0000000000000,0x974210a98100031e8000,0xcd124fdb4016f1060000,0x560000087cb26544ec9,0x1811163000000,0x4685df4aa423fd52460d,0x9b28b0000000000197c8],#[0xf1d2000301d88a021c73,0xb5b,0x3400031e96a99a870000,0x1fa0001c77c073e,0x908c000000000,0x92000000015ab44041b5,0xe9211c3f8000356c0000,0x21f10000000000105401,0xd79000000000030d801c,0x260000000c05a20fd633,0x14425a82c8e5800000,0x50d71d662b21e609d800,0x1085000000037f0000,0x430c4000063187040000,0x40000000c5f0000000c9,0x47bc00000032b60ad,0x83f00000004ac0,0xf3040]]
def g251D11 := limbs80 #[#[0xb60581505013048110ff,0xe574134201300d89624c,0x1785818306139e8e7d6,0x80618150511820703020,0x39f380c005694070029d,0x80198018b80a8019fd00,0x1]]
def g251H11 := limbs80 #[#[0xe04481082410a3208303,0x7c604000c68124b40020,0x45091c00a050a048850a,0xa86060a405040c400060,0x8f8428d8100040830c08,0x80e84e818084c4,0x3cc15a7f06686c30dc17,0x640d019000622148d701,0x71c81187576d63875836,0x4a932563458201000057,0xc83f07161905e41387d3,0xb76403000c30c4027d14,0xc55e36000a77081276,0x65d069d17000000d5e0,0x65402a83e00060900046,0x4442ec0283343bb77842,0x7be67965000a5e0009,0xc7700091387c940c3500,0x4f44c93e000853e40437,0xd41e4c0008074,0xd0281c00000000000,0x1a578147000050748000,0x5000000e5116001241fc,0x1ba8086d02d00000084,0x2c235000441d4ec56b62,0xd278c4887f610c49c748,0x820000063a6ed6d50563,0x78073f0a101482f1004a,0x8072c5c34342200084dc,0x87e467000000177c59c3,0x10065c5100010376783c,0x100a825c340004280004],#[0xb7800bc5d42be0a77022,0x1d82f931004829e39162,0x5026a55000000d040360,0x83e7e000000a05363d4,0x3183241406400070b079,0x200000084b0000000006,0x846427241f57000861f0,0xa6643d016000031,0x443100000000000b490,0x50ac5f55d00000,0x10f31000000000000a2c,0x8b1705a00000046bc765,0xe2613d80f000f1b005c6,0x64c6a000000c39000444,0x8000000000408000e527,0x80c000c8000000070,0x47c62c5b83ac23000000,0x2400000020c3688013,0x63e00600000000000000,0x44766dd5f000f3c000,0x9f1305400023b07a0,0x40054dc6fb29d4301e47,0xc52021000b1dd7686e]]
def g251D12 (j : Nat) := if j=0 then 0x5080c1010037f else 0
def g251H12 := limbs80 #[#[0x44028,0x80198000000000314000,0x10fc,0x188000000000001080,0x2c4942001840,0x24800000002d750000,0x2640000000,0x30000000000000,0xc0000000004000000000,0x4,0x31800000000000,0x160000000001c03100,0x540000000000000,0x15825d802800]]
def g251L : Nat → Packing
  | 6 => (89,6,7,2949196,103,10,1040,g251D6)
  | 7 => (765,5,7,9568703,137,14,1292,g251D7)
  | 8 => (1210,4,7,7864709,121,16,1319,g251D8)
  | 9 => (711,3,7,2490478,103,15,1170,g251D9)
  | 10 => (132,2,7,393226,52,13,1100,g251D10)
  | 11 => (10,1,7,65537,0,8,1039,g251D11)
  | 12 => (1,0,7,0,0,0,0,g251D12)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 37 773 3 11 7 2 g251H7
  | 8 => lookupShort 335 1823 7 14 10 2 g251H8
  | 9 => lookupShort 474 2819 7 15 11 2 g251H9
  | 10 => lookupShort 308 1979 6 14 10 2 g251H10
  | 11 => lookupShort 60 331 7 12 8 2 g251H11
  | 12 => lookupShort 6 139 1 8 4 2 g251H12
  | _ => fun _ => none
def g251 : Forest := ⟨251,12,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_2 : block g251 6 2 87=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 89=true := (@block_merge g251 6 0 2 87 g251P6_0 g251P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_63 : block g251 7 63 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_159 : block g251 7 159 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_255 : block g251 7 255 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_351 : block g251 7 351 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_447 : block g251 7 447 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_543 : block g251 7 543 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_639 : block g251 7 639 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_735 : block g251 7 735 30=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 765=true := (@block_merge g251 7 0 351 414 (@block_merge g251 7 0 159 192 (@block_merge g251 7 0 63 96 g251P7_0 g251P7_63) (@block_merge g251 7 159 96 96 g251P7_159 g251P7_255)) (@block_merge g251 7 351 192 222 (@block_merge g251 7 351 96 96 g251P7_351 g251P7_447) (@block_merge g251 7 543 96 126 g251P7_543 (@block_merge g251 7 639 96 30 g251P7_639 g251P7_735))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 41=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_41 : block g251 8 41 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_137 : block g251 8 137 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_233 : block g251 8 233 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_329 : block g251 8 329 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_425 : block g251 8 425 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_521 : block g251 8 521 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_528 : block g251 8 528 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_624 : block g251 8 624 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_720 : block g251 8 720 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_816 : block g251 8 816 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_912 : block g251 8 912 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1008 : block g251 8 1008 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1104 : block g251 8 1104 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1200 : block g251 8 1200 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 1210=true := (@block_merge g251 8 0 528 682 (@block_merge g251 8 0 233 295 (@block_merge g251 8 0 41 192 g251P8_0 (@block_merge g251 8 41 96 96 g251P8_41 g251P8_137)) (@block_merge g251 8 233 192 103 (@block_merge g251 8 233 96 96 g251P8_233 g251P8_329) (@block_merge g251 8 425 96 7 g251P8_425 g251P8_521))) (@block_merge g251 8 528 384 298 (@block_merge g251 8 528 192 192 (@block_merge g251 8 528 96 96 g251P8_528 g251P8_624) (@block_merge g251 8 720 96 96 g251P8_720 g251P8_816)) (@block_merge g251 8 912 192 106 (@block_merge g251 8 912 96 96 g251P8_912 g251P8_1008) (@block_merge g251 8 1104 96 10 g251P8_1104 g251P8_1200))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_4 : block g251 9 4 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_100 : block g251 9 100 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_196 : block g251 9 196 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_292 : block g251 9 292 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_335 : block g251 9 335 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_431 : block g251 9 431 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_527 : block g251 9 527 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_623 : block g251 9 623 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_659 : block g251 9 659 52=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 711=true := (@block_merge g251 9 0 335 376 (@block_merge g251 9 0 100 235 (@block_merge g251 9 0 4 96 g251P9_0 g251P9_4) (@block_merge g251 9 100 96 139 g251P9_100 (@block_merge g251 9 196 96 43 g251P9_196 g251P9_292))) (@block_merge g251 9 335 192 184 (@block_merge g251 9 335 96 96 g251P9_335 g251P9_431) (@block_merge g251 9 527 96 88 g251P9_527 (@block_merge g251 9 623 36 52 g251P9_623 g251P9_659))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 59=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_59 : block g251 10 59 73=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 132=true := (@block_merge g251 10 0 59 73 g251P10_0 g251P10_59)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 10=true := g251P11_0
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
theorem g251G : graphValid g251 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 13 := lower_forest (g:=g251) (i:=0) (hints:=65603) (before_sound K235 V235) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K235 13 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V235 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 13 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K251 V251) (4, 0, 251, 0, 13) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_52262

open PEqualNP.Outside.L_meta_52262 in
theorem PEqualNP.Outside.L_meta_52262 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
