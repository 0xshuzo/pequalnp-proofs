import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9825
namespace Engine
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 1024
def zero : Sig := 0
def one : Sig := BitVec.allOnes 1024
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
def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
theorem bit_zero (i) : bit i zero = false := by simp [bit,zero]
theorem bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
theorem bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
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
theorem get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
theorem extract {u target} (gs : List Gate) (w : List Sig)
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
abbrev Row := Fin 1024
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
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0c0fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff0c0fffffffffffffffffffffffffffaf0f0ffffffffffffffffffffffffffeaf0c0fffffffffffefcfcfffffffffffaf0f0ffeefeeeffeefcccffeafaeaffeaf0c0
def sample (r : Row) (j : Fin 10) := bit r (inputs.getD j.val zero)
def edge (x : Fin 10 → Bool) : Bool :=
  (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 10 => inputs.getD j.val zero) = inputs := rfl
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
abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 1024-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(1024-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 1024 (1024-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 1024-d.val <;> simp [shifted,h,r.isLt]
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
  (List.range 10).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def varsX (m : Nat) := vars m
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 9) ||| (x 5 &&& x 7) ||| (x 7 &&& x 9) ||| (x 6 &&& x 9) ||| (x 6 &&& x 8) ||| (x 5 &&& x 8)
def subcube (z o : Nat) : Sig :=
  if z &&& o != 0 then zero else
    (List.range 10).foldl (fun w i => if z.testBit i then w &&& ~~~(inputs.getD i zero)
      else if o.testBit i then w &&& inputs.getD i zero else w) one
def fixRows (z o : Nat) : List Move :=
  (List.range 10).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 1024 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 1024 d)
def supportPairs (_t mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 1024 (1 <<< i))
def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 1024 r,Fin.ofNat 1024 (r ||| (1 <<< i)))
def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 1024+1024*(c.1/1024)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 1024) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/1024+80) s
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
  let free := colFree raw (z % 1024) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/1024+80) s
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
abbrev Bits := BitVec 320
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals
def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 320 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 320 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 320 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 320 → Row) (x : Decor) := x.2 = pairSig r s x.1
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
    let a := ws.getD (bits &&& 31) defaultDecor
    let b := ws.getD ((bits >>> 5) &&& 31) defaultDecor
    decodeBank k (bits >>> 12) (ws++[dbin ((bits >>> 10) &&& 3) a b])
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
def asRow (cols : Nat → Bits) (i : Fin 320) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 10 => (cols j.val).getLsbD i.val))).toFin.cast
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
theorem coordinate9 : ∀ r : Row, bit r (inputs.getD 9 zero) = r.val.testBit 9 := by decide +kernel
theorem input_coords : ∀ (j : Fin 10) (r : Row), bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j
  fin_cases j
  · exact coordinate0
  · exact coordinate1
  · exact coordinate2
  · exact coordinate3
  · exact coordinate4
  · exact coordinate5
  · exact coordinate6
  · exact coordinate7
  · exact coordinate8
  · exact coordinate9
theorem asRow_bit (cols : Nat → Bits) (i : Fin 320) (j : Fin 10) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 10 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<10 ∧ a=inputs.getD j zero := by
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
  (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 9) ||| (x 5 &&& x 7) ||| (x 7 &&& x 9) ||| (x 6 &&& x 9) ||| (x 6 &&& x 8) ||| (x 5 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 320) (j : Fin 10) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 320) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<10) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide),pos 9 (by decide)]
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
    if (rs ||| column d z.2) != BitVec.allOnes 320 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 320) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 320 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
  by_cases hj : j<10
  · let i : Fin 10 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 1024 ≤ 2^j := by
      change 2^10 ≤ 2^j
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
abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.mode (g : Forest) : Bool := !(g.1.testBit 12)
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 320) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 320) (hq : chartSamples m q = 0) :
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
def forestRecord (tab : Packing) (_raw i : Nat) :=
  let (_,_,_,_,_,_,_,words) := tab
  words (2*i)
def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 12*storedDepth g depth
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
    let more := chosenSteps bank (ops >>> 12) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 10 2,(bank.getD (ops &&& 31) defaultDecor).1,
        (bank.getD (getFieldV ops 5 5) defaultDecor).1) :: more
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
def decodeHints (cw d : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,x => (x % (1 <<< cw),(x >>> cw) % (1 <<< d)) ::
      decodeHints cw d n (x >>> (cw+d))
def forestHints (tab : Packing) (_raw i : Nat) :=
  let (_,depth,cw,_,_,_,_,words) := tab
  let data := words (2*i+1)
  decodeHints cw depth (data % 256) (data >>> 8)
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 320) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))
def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2
theorem baseKnown : Known true [] := by simp [Known]
theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)
def lanePlace (v : Nat) (upper : Nat) := 2^321*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^321 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<321 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 320) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (321*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^321)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 321*(i+1)-321=321*i := by omega
      have ge : ¬321*(i+1)<321 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 320 = (a==BitVec.allOnes 320) := by
  by_cases h : a=BitVec.allOnes 320
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^320-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^320 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (321*i) =
      (f xs[i]==BitVec.allOnes 320) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^321*u+x+(2^321*v+1)=2^321*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^321 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬321*(i+1)+320<321 := by omega
      have di : 321*(i+1)+320-321=321*i+320 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 321) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (321*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 321) (i:=i) (by simpa using hi) _ ok.2
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
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
def validSwap (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 10)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem swap_table : ∀ v : Fin 160, validSwap v.val=true → ∀ t : Fin 10, swapIdx v.val t.val<10 ∧
    wordMove (swapRows v.val) (inputs.getD t.val zero) = inputs.getD (swapIdx v.val t.val) zero := by decide +kernel
theorem swap_input {v t : Nat} (hv : validSwap v=true) (ht : t<10) : swapIdx v t<10 ∧
    wordMove (swapRows v) (inputs.getD t zero) = inputs.getD (swapIdx v t) zero := by
  have lt : v<160 := by
    simp only [validSwap,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact swap_table ⟨v,lt⟩ hv ⟨t,ht⟩
def idxOf (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => swapIdx v t) t
theorem idx_move {perm : List Nat} (ok : perm.all validSwap=true) {t : Nat} (ht : t<10) :
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
  | n+1,bits,ws => force (zN ((bits >>> 10) &&& 3) (ws.getD (bits &&& 31) 0) (ws.getD ((bits >>> 5) &&& 31) 0))
      fun z => decodeN n (bits >>> 12) (ws++[z])
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
  let len := 12*depth
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 320 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 320
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

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n
def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩
def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
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
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
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
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve
theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega
theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
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
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨kwFork d01 ha hb fresh H⟩
def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v
theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw
theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)
def kwWord (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let a := ws.getD (value % 16) zero
  let b := ws.getD ((value >>> 4) % 16) zero
  let row := fun i : Nat => Fin.ofNat 1024 ((value >>> (8+10*i)) % 1024)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a (row 0) (row 2) && kwWireB ws T b (row 0) (row 3) &&
    kwWireB ws T a (row 4) (row 1) && kwWireB ws T b (row 5) (row 1)
theorem kwWord_sound {T ws k v} (h : kwWord T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
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
def kwTest (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all fun j => kwWord (targetOf g) (stateSet g k (a+j)) k (data j)
theorem mixedCut {g k a n data} (mode : g.mode=false) (h : kwTest g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh
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
structure FreeRooms (S : Finset Sig) (T H : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false →
    (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

structure SingleFactor (S : Finset Sig) (T : Sig) where
  inner : Finset Sig
  outer : Finset Sig
  pivot : Sig
  cover : inner ∪ outer = S
  apart : Disjoint inner outer
  inside : KWRooms inner pivot
  outside : FreeRooms outer T pivot
def freeFrom {S T} (D : KWRooms S T) (h : Sig) : FreeRooms S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect
def freeHide {S T h} (D : FreeRooms S T h) : FreeRooms (S.erase h) T h where
  owns v p n := v≠h ∧ D.owns v p n
  total := by
    intro p n hp hn
    rcases D.total p n hp hn with yes | ⟨v,hv⟩
    · exact Or.inl yes
    · by_cases eq : v=h
      · exact Or.inl (eq ▸ (D.valid hv).2)
      · exact Or.inr ⟨v,eq,hv⟩
  valid := by
    rintro v p n ⟨ne,hv⟩
    exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
  unique := fun h1 h2 => D.unique h1.2 h2.2
  rect := fun a b => ⟨a.1,D.rect a.2 b.2⟩
def factorOfTree {S T} (D : KWRooms S T) : SingleFactor S T where
  inner := S
  outer := ∅
  pivot := T
  cover := by simp
  apart := by simp
  inside := D
  outside := {
    owns := fun _ _ _ => False
    total := fun p n hp hn => Or.inl ⟨hp,hn⟩
    valid := fun h => h.elim
    unique := fun h _ => h.elim
    rect := fun h _ => h.elim }
def freeFork {h : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : FreeRooms (insert (bin d a b) U) T h) : FreeRooms (insert a (insert b U)) T h := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    rcases H.total p n hp hn with closed | ⟨v,hv⟩
    · exact Or.inl closed
    right
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
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
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
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve
theorem supportSide {A B U : Finset Sig} {a b z : Sig}
    (e : A∪B=insert z U) (disj : Disjoint A B) (za : z∈A)
    (freshA : a∉insert z U) (freshB : b∉insert z U) (freshZ : z∉U) :
    (insert a (insert b (A.erase z))) ∪ B=insert a (insert b U) ∧
    Disjoint (insert a (insert b (A.erase z))) B ∧ a∉A.erase z ∧ b∉A.erase z := by
  have hb : z∉B := fun h => Finset.disjoint_left.mp disj za h
  have allmem (w : Sig) : w∈A∨w∈B ↔ w=z∨w∈U := by
    rw [←Finset.mem_union,←Finset.mem_insert,e]
  have aout : a∉A ∧ a∉B := by
    have h : a∉A∪B := by rw [e]; exact freshA
    simpa using h
  have bout : b∉A ∧ b∉B := by
    have h : b∉A∪B := by rw [e]; exact freshB
    simpa using h
  refine ⟨?_,?_,fun h => aout.1 (Finset.mem_of_mem_erase h),fun h => bout.1 (Finset.mem_of_mem_erase h)⟩
  · ext w
    have m := allmem w
    by_cases eq : w=z
    · subst w; simp [freshZ,hb]
    · simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at *
      tauto
  · apply Finset.disjoint_left.mpr
    intro w hw hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact aout.2 hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact bout.2 hwB
    exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB
def factorExpand {U T a b d} (hd : d=0 ∨ d=1)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : SingleFactor (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := supportSide F.cover F.apart inn freshA freshB freshZ
    have old : KWRooms (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,kwFork hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := supportSide ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : FreeRooms (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      freeFork hd ha hb (by simp [z]) old⟩
def factorKeep {U T a b d} (hd : d=0 ∨ d=1) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : KWRooms (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  let z := bin d a b
  have za : z≠a := by
    intro eq
    apply fresh
    exact Finset.mem_insert.mpr (Or.inl eq)
  have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have set0 : (insert z U).erase a = insert z (U.erase a) := by
    ext v
    simp only [Finset.mem_erase,Finset.mem_insert]
    by_cases eq : v=z
    · subst v; simp [za]
    · tauto
  have H0 : FreeRooms (insert z (U.erase a)) T a := set0 ▸ freeHide (freeFrom H a)
  have H1 := freeFork hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : FreeRooms (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,kwLeaf a,freeHide H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp
theorem oneShare {T k S} (r : Live false T k S) (budget : k≤S.card) :
    Nonempty (SingleFactor S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨factorOfTree (kwLeaf T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := kwWidth tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        exact ⟨factorKeep hd01 ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        have comm : bin d b a=z := by
          rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
        have H' : KWRooms (insert (bin d b a) U) T := by simpa only [comm] using H
        have fr : bin d b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := factorKeep hd01 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨factorExpand hd01 fa fb zU F⟩
theorem factorForced {S : Finset Sig} {T : Sig} (F : SingleFactor S T) (p n : Row)
    (hp : bit p T=true) (hn : bit n T=false)
    (none : ∀ v∈F.outer, bit p v=true → bit n v=false → False) :
    bit p F.pivot=true ∧ bit n F.pivot=false := by
  rcases F.outside.total p n hp hn with h | ⟨v,hv⟩
  · exact h
  · exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)
theorem factorOuterOwn {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a p n} (ao : a∈F.outer)
    (one : onlyWire S T a p n) : F.outside.owns a p n := by
  rcases F.outside.total p n one.1 one.2.1 with hpivot | ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := F.inside.total p n hpivot.1 hpivot.2
    obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
    have eq := one.2.2 w ws wp wn
    rw [eq] at wi
    exact False.elim (Finset.disjoint_left.mp F.apart wi ao)
  · obtain ⟨wo,wp,wn⟩ := F.outside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := one.2.2 w ws wp wn
    exact eq ▸ hw
theorem outerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (aout : a∈F.outer) (bout : b∈F.outer)
    (different : a≠b) (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (factorOuterOwn F aout A) (factorOuterOwn F aout C))
    (F.outside.rect (factorOuterOwn F bout B) (factorOuterOwn F bout D)))
theorem innerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (A : onlyWire F.inner F.pivot a p na) (B : onlyWire F.inner F.pivot b p nb)
    (C : onlyWire F.inner F.pivot a pa n) (D : onlyWire F.inner F.pivot b pb n) : False :=
  different (F.inside.unique (F.inside.rect (kwOwn F.inside A) (kwOwn F.inside C))
    (F.inside.rect (kwOwn F.inside B) (kwOwn F.inside D)))
theorem innerSource {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {v p n}
    (hv : v∈F.inner) (only : onlyWire S T v p n) : onlyWire F.inner F.pivot v p n := by
  have h : bit p F.pivot=true ∧ bit n F.pivot=false := by
    apply factorForced F p n only.1 only.2.1
    intro w wo hp hn
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := only.2.2 w ws hp hn
    exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
  refine ⟨h.1,h.2,?_⟩
  intro w wi hp hn
  exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn
theorem hornRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b c p n pa na}
    (ar : onlyWire S T a p na) (br : onlyWire S T b pa n) (cr : onlyWire S T c p n)
    (ia : a∈F.inner) (ib : b∈F.inner) : c∈F.inner := by
  have ah := innerSource F ia ar
  have bh := innerSource F ib br
  obtain ⟨w,hw⟩ := F.inside.total p n ah.1 bh.2.1
  obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
  have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
  exact (cr.2.2 w ws wp wn) ▸ wi
theorem parityRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (hs : a∈S) (ht : b∈S) (ne : a≠b)
    (h1 : onlyWire S T a p na) (h2 : onlyWire S T b p nb)
    (h3 : onlyWire S T a pa n) (h4 : onlyWire S T b pb n) :
    ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False := by
  rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
  · exact innerCannotCross F ne (innerSource F ia h1) (innerSource F ib h2)
      (innerSource F ia h3) (innerSource F ib h4)
  · rw [←F.cover,Finset.mem_union] at hs ht
    exact outerCannotCross F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
def colorPoint (v : Fin 10 → Bool) : Row :=
  (BitVec.ofBoolListLE (List.ofFn v)).toFin.cast (by simp [List.length_ofFn])
theorem color_bit (v : Fin 10 → Bool) (i : Fin 10) :
    bit (colorPoint v) (inputs.getD i.val zero) = v i := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn v)).getLsbD i.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def colorField (d j : Nat) : Fin 10 := Fin.ofNat 10 ((d >>> (1+4*j)) % 16)
def colorRow (d j : Nat) : Row := Fin.ofNat 1024 ((d >>> (13+10*j)) % 1024)
def colorWire (ws : List Sig) (names : Nat) (j : Fin 10) : Sig :=
  ws.getD ((names >>> (4*j.val)) % 16) zero
def colorRule (ws : List Sig) (T : Sig) (names d : Nat) : Bool :=
  let a := colorWire ws names (colorField d 0)
  let b := colorWire ws names (colorField d 1)
  let c := colorWire ws names (colorField d 2)
  let r := colorRow d
  if d.testBit 0 then
    (decide (a ∈ ws) && decide (b ∈ ws) && decide (a ≠ b)) &&
    (kwWireB ws T a (r 0) (r 2) && kwWireB ws T b (r 0) (r 3) &&
      kwWireB ws T a (r 4) (r 1) && kwWireB ws T b (r 5) (r 1))
  else kwWireB ws T a (r 0) (r 2) && kwWireB ws T b (r 3) (r 1) &&
    kwWireB ws T c (r 0) (r 1)
def constraintWord (d : Nat) : Sig :=
  let x := fun j => inputs.getD (colorField d j).val zero
  if d.testBit 0 then x 0 ^^^ x 1 else ~~~(x 0 &&& x 1) ||| x 2
def colorTruth {ws : List Sig} {T : Sig} (F : SingleFactor ws.toFinset T)
    (names : Nat) (i : Fin 10) := decide (colorWire ws names i ∈ F.inner)
theorem parity_bit {A B : Prop} [Decidable A] [Decidable B]
    (h : ¬ ((A ∧ B) ∨ (¬A ∧ ¬B))) : (decide A ^^ decide B) = true := by
  by_cases a : A <;> by_cases b : B <;> simp_all
theorem horn_bit {A B C : Prop} [Decidable A] [Decidable B] [Decidable C]
    (h : A → B → C) : (!(decide A && decide B) || decide C) = true := by
  by_cases a : A <;> by_cases b : B <;> simp_all
theorem bit_xor (r : Row) (a b : Sig) : bit r (a ^^^ b) = (bit r a ^^ bit r b) :=
  BitVec.getLsbD_xor
theorem rule_valid {ws T names d} (F : SingleFactor ws.toFinset T)
    (h : colorRule ws T names d = true) :
    bit (colorPoint (colorTruth F names)) (constraintWord d) = true := by
  have bits (i) := color_bit (colorTruth F names) (colorField d i)
  by_cases flag : d.testBit 0 = true
  · simp only [colorRule,flag,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h
    have rule := parityRule F (List.mem_toFinset.mpr h.1.1.1) (List.mem_toFinset.mpr h.1.1.2) h.1.2
      (kwWireB_sound h.2.1.1.1) (kwWireB_sound h.2.1.1.2) (kwWireB_sound h.2.1.2) (kwWireB_sound h.2.2)
    simp only [constraintWord,flag,ite_true]
    rw [bit_xor,bits,bits]
    exact parity_bit rule
  · simp only [colorRule,if_neg flag,Bool.and_eq_true] at h
    have rule := hornRule F (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
    simp only [constraintWord,if_neg flag]
    change bit _ (prime true (neg (prime false _ _)) _) = true
    rw [bit_prime,bit_neg,bit_prime]
    change (!(bit _ _ && bit _ _) || bit _ _) = true
    rw [bits,bits,bits]
    exact horn_bit rule
def colorSet : List Nat → Sig
  | [] => one
  | d::ds => constraintWord d &&& colorSet ds
theorem color_set {ws T names} (F : SingleFactor ws.toFinset T) (ds : List Nat)
    (h : ds.all (colorRule ws T names) = true) :
    bit (colorPoint (colorTruth F names)) (colorSet ds) = true := by
  induction ds with
  | nil => exact bit_one _
  | cons d ds ih =>
    simp only [List.all_cons,Bool.and_eq_true] at h
    change bit _ (prime false _ _) = true
    rw [bit_prime,rule_valid F h.1,ih h.2]
    rfl
def colorCheck (ws : List Sig) (T : Sig) (k names : Nat) (ds : List Nat) :=
  decide (k ≤ ws.toFinset.card) && ds.all (colorRule ws T names) && (colorSet ds == zero)
theorem color_sound {ws T k names ds} (h : colorCheck ws T k names ds=true) :
    Impossible false T k ws.toFinset := by
  simp only [colorCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
  intro n le run
  obtain ⟨F⟩ := oneShare run (le.trans h.1.1)
  have ok := color_set F ds h.1.2
  rw [h.2,bit_zero] at ok
  contradiction
def colorRange (g : Forest) (k a n : Nat) (ds : Nat → Nat × List Nat) :=
  (List.range n).all fun i =>
    colorCheck (stateSet g k (a+i)) (targetOf g) k (ds i).1 (ds i).2
theorem colorCut {g k a n ds} (mode : g.mode=false)
    (h : colorRange g k a n ds=true) : CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have eq : a+(j-a)=j := by omega
  change colorCheck (stateSet g k (a+(j-a))) _ _ _ _=true at hh
  rw [eq] at hh
  exact color_sound hh
def neighbor670 (i : Fin 10) : Nat := [4, 2, 1, 2, 0, 0, 1, 2, 5, 4].getD i.val 0
def absentRow670 (i : Fin 10) : Row := Fin.ofNat 1024 (1 <<< neighbor670 i)
def presentRow670 (i : Fin 10) : Row := Fin.ofNat 1024 ((1 <<< i.val) ||| (1 <<< neighbor670 i))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem requiredInputs :
    (∀ i : Fin 10, bit (absentRow670 i) graph ≠ bit (presentRow670 i) graph) ∧
    (∀ i j : Fin 10, i ≠ j →
      bit (absentRow670 i) (inputs.getD j.val zero) =
      bit (presentRow670 i) (inputs.getD j.val zero)) := by decide +kernel
theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) (small : C.size ≤ 16) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 15 else 16) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 16 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 15 else 16) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode
  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 10, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow670 i) (presentRow670 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩
theorem directSplit
    (m : ∀ k, k ≤ 16 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 15 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 edge 16 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def orderLaw (S : Finset Sig) (T : Sig) (f : Sig → Nat) :=
  (∀ {a b p n na nb pa pb}, a ≠ b →
    onlyWire S T a p na → onlyWire S T b p nb →
    onlyWire S T a pa n → onlyWire S T b pb n → f a ≠ f b) ∧
  (∀ {a b c p n na pb}, onlyWire S T a p na → onlyWire S T b pb n →
    onlyWire S T c p n → f a = f b → f c ≤ f a)
theorem only_value {k S T v p n} (run : Live false T k S) (h : onlyWire S T v p n) :
    v∈S ∧ bit p v=true ∧ bit n v=false := by
  obtain ⟨w,hw,hp,hn⟩ := mono_row_difference run rfl h.1 h.2.1
  exact h.2.2 w hw hp hn ▸ ⟨hw,hp,hn⟩
def gateList (a b : Sig) (U : Finset Sig) := [a,b].filter fun t => decide (t∈U)
def gateMap (a b z v : Sig) := if v=a ∨ v=b then z else v
def gateColor (a b z : Sig) (U : Finset Sig) (f : Sig → Nat) (v : Sig) :=
  let kept := gateList a b U
  if v∈kept then kept.idxOf v else kept.length+f (gateMap a b z v)
theorem gate_kept {a b v U} :
    v∈gateList a b U ↔ (v=a ∨ v=b) ∧ v∈U := by simp [gateList]
theorem gate_mem {a b z v : Sig} {U : Finset Sig} (h : v∈insert a (insert b U)) :
    gateMap a b z v ∈ insert z U := by
  by_cases eq : v=a ∨ v=b
  · simp [gateMap,eq]
  · simp_all [gateMap]
theorem mono_bin_bit {d} (hd : allowed false d) (a b : Sig) (r : Row) :
    bit r (bin d a b) = if d=0 then bit r a && bit r b else bit r a || bit r b := by
  rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
  · simp [bit,bin]
  · simp [bit,bin]
  · contradiction
  · contradiction
theorem gate_only {a b d U T v p n} (hd : allowed false d)
    (unused : v∉gateList a b U) (h : onlyWire (insert a (insert b U)) T v p n) :
    onlyWire (insert (bin d a b) U) T (gateMap a b (bin d a b) v) p n := by
  refine ⟨h.1,h.2.1,?_⟩
  intro w hw hp hn
  rcases Finset.mem_insert.mp hw with rfl | hw
  · rw [mono_bin_bit hd] at hp hn
    have sep : (bit p a=true ∧ bit n a=false) ∨ (bit p b=true ∧ bit n b=false) := by
      by_cases op : d=0 <;> cases u : bit p a <;> cases v : bit n a <;> cases x : bit p b <;>
        cases y : bit n b <;> simp_all
    have eq : v=a ∨ v=b := by
      rcases sep with ⟨x,y⟩ | ⟨x,y⟩
      · exact Or.inl (h.2.2 a (by simp) x y).symm
      · exact Or.inr (h.2.2 b (by simp) x y).symm
    simp [gateMap,eq]
  · obtain rfl := h.2.2 w (by simp [hw]) hp hn
    have ne : ¬(w=a ∨ w=b) := fun eq => unused (gate_kept.mpr ⟨eq,hw⟩)
    simp [gateMap,ne]
theorem gate_share_eq {a b z U f v w} (hv : v∈gateList a b U)
    (eq : gateColor a b z U f v = gateColor a b z U f w) : v=w := by
  have bound := List.idxOf_lt_length_of_mem hv
  by_cases hw : w∈gateList a b U
  · simp only [gateColor,if_pos hv,if_pos hw] at eq
    exact (List.idxOf_inj hv).mp eq
  · simp only [gateColor,if_pos hv,if_neg hw] at eq
    omega
theorem gate_cross {a b d U T k p n na nb pa pb} (hd : allowed false d) (hab : a≠b)
    (run : Live false T k (insert (bin d a b) U)) (prev : Live false T (k+1) (insert a (insert b U)))
    (ua : a∉gateList a b U)
    (A : onlyWire (insert a (insert b U)) T a p na) (B : onlyWire (insert a (insert b U)) T b p nb)
    (C : onlyWire (insert a (insert b U)) T a pa n) (D : onlyWire (insert a (insert b U)) T b pb n) : False := by
  have Zp := (only_value run (gate_only hd ua C)).2.1
  have Zn := (only_value run (gate_only hd ua A)).2.2
  simp only [gateMap,true_or,ite_true,mono_bin_bit hd] at Zp Zn
  by_cases op : d=0
  · simp [op] at Zp
    exact hab (C.2.2 b (by simp) Zp.2 (only_value prev D).2.2).symm
  · simp [op] at Zn
    exact hab (A.2.2 b (by simp) (only_value prev B).2.1 Zn.2).symm
theorem order_live {k S T} (h : Live false T k S) :
    ∃ (count : Nat) (f : Sig → Nat), count+S.card ≤ k+2 ∧ (∀ v∈S, f v<count) ∧ orderLaw S T f := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,properT⟩ := h
    refine ⟨1,fun _ => 0,by simp,by simp,?_,by simp⟩
    intro a b p n na nb pa pb ne A B C D
    have e := (only_value (Live.stop (u:=false) properT) A).1
    have j := (only_value (Live.stop (u:=false) properT) B).1
    simp only [Finset.mem_singleton] at e j
    exact (ne (e.trans j.symm)).elim
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,fresh,tail⟩ := h
    let z := bin d a b
    let kept := gateList a b U
    have prev := Live.binary hd ha hb hab fresh tail
    obtain ⟨count,f,mass,bound,law⟩ := ih tail
    have hzu : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem hzu] at mass
    have size : kept.length + (insert a (insert b U)).card = U.card+2 := by
      by_cases x : a∈U <;> by_cases y : b∈U <;>
        simp [kept,gateList,x,y,hab,Finset.card_insert_of_notMem] <;> omega
    refine ⟨kept.length+count,gateColor a b z U f,by omega,?_,?_,?_⟩
    · intro v hv
      by_cases u : v∈kept
      · have m := List.idxOf_lt_length_of_mem u
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_pos u]
        omega
      · have m := bound _ (gate_mem (z:=z) hv)
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_neg u]
        exact Nat.add_lt_add_left m _
    · intro v w p n na nb pa pb vw A B C D eq
      have uv : v∉kept := fun u => vw (gate_share_eq u eq)
      have uw : w∉kept := fun u => vw (gate_share_eq u eq.symm).symm
      have same : f (gateMap a b z v) = f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_) = (if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      by_cases ne : gateMap a b z v ≠ gateMap a b z w
      · exact law.1 ne (gate_only hd uv A) (gate_only hd uw B)
          (gate_only hd uv C) (gate_only hd uw D) same
      · have vS := (only_value prev A).1
        have wS := (only_value prev B).1
        have vz : v≠z := fun e => fresh (show z∈_ from e ▸ vS)
        have wz : w≠z := fun e => fresh (show z∈_ from e ▸ wS)
        have pair : (v=a ∧ w=b) ∨ (v=b ∧ w=a) := by
          by_cases va : v=a ∨ v=b <;> by_cases wa : w=a ∨ w=b <;> simp_all [gateMap] <;> grind
        rcases pair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact gate_cross hd hab tail prev uv A B C D
        · exact gate_cross hd hab tail prev uw B A D C
    · intro v w t p n na pb A B C eq
      have ident (e : v=w) : t=v := by
        subst w
        exact (C.2.2 v (only_value prev A).1 (only_value prev A).2.1 (only_value prev B).2.2).symm
      by_cases uv : v∈kept
      · rw [ident (gate_share_eq uv eq)]
      by_cases uw : w∈kept
      · rw [ident (gate_share_eq uw eq.symm).symm]
      have same : f (gateMap a b z v) = f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_) = (if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      change (if t∈kept then kept.idxOf t else kept.length+_) ≤ (if v∈kept then _ else kept.length+_)
      rw [if_neg uv]
      by_cases ut : t∈kept
      · rw [if_pos ut]
        have lim := List.idxOf_lt_length_of_mem ut
        omega
      · rw [if_neg ut]
        exact Nat.add_le_add_left (law.2 (gate_only hd uv A) (gate_only hd uw B) (gate_only hd ut C) same) _
def rankRule (d : Nat) (f : Fin 10 → Nat) : Prop :=
  let v := fun j => f (colorField d j)
  if d.testBit 0 then v 0 ≠ v 1 else v 0=v 1 → v 2≤v 0
theorem rank_rule {ws T names d f} (h : colorRule ws T names d=true)
    (law : orderLaw ws.toFinset T f) :
    rankRule d (fun i => f (colorWire ws names i)) := by
  by_cases flag : d.testBit 0=true
  · simp only [rankRule,colorRule,flag,ite_true,Bool.and_eq_true,decide_eq_true_eq] at h ⊢
    exact law.1 h.1.2 (kwWireB_sound h.2.1.1.1) (kwWireB_sound h.2.1.1.2)
      (kwWireB_sound h.2.1.2) (kwWireB_sound h.2.2)
  · simp only [rankRule,colorRule,if_neg flag,Bool.and_eq_true] at h ⊢
    exact law.2 (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2)
def layerCovers (lo : Nat) (f : Fin 10 → Nat) (t : Nat) :=
  ∀ i, f i<t → lo.testBit i.val=true
def layerBits (lo : Nat) (f : Fin 10 → Nat) (t : Nat) (i : Fin 10) :=
  !lo.testBit i.val && decide (f i=t)
def layerRule (lo d : Nat) : Sig :=
  let x := fun j => inputs.getD (colorField d j).val zero
  let pair := neg (prime false (x 0) (x 1))
  if d.testBit 0 then pair else
    if lo.testBit (colorField d 2).val then one else prime true pair (x 2)
theorem layer_rule {lo d f t} (h : rankRule d f) (cov : layerCovers lo f t) :
    bit (colorPoint (layerBits lo f t)) (layerRule lo d)=true := by
  have eval (j) := color_bit (layerBits lo f t) (colorField d j)
  by_cases flag : d.testBit 0=true
  · simp only [rankRule,flag,ite_true] at h
    simp only [layerRule,flag,ite_true,bit_neg,bit_prime,Bool.false_eq_true,ite_false,eval]
    cases x : layerBits lo f t (colorField d 0) <;> cases y : layerBits lo f t (colorField d 1) <;> simp_all
    simp only [layerBits,Bool.and_eq_true,decide_eq_true_eq] at x y
    exact h (x.2.trans y.2.symm)
  · simp only [rankRule,if_neg flag] at h
    simp only [layerRule,if_neg flag]
    by_cases old : lo.testBit (colorField d 2).val=true
    · rw [if_pos old,bit_one]
    · rw [if_neg old]
      simp only [bit_prime,ite_true,bit_neg,Bool.false_eq_true,ite_false,eval]
      cases x : layerBits lo f t (colorField d 0) <;> cases y : layerBits lo f t (colorField d 1) <;> simp_all
      simp only [layerBits,Bool.and_eq_true,decide_eq_true_eq] at x y
      have le := h (x.2.trans y.2.symm)
      have ge : ¬ f (colorField d 2)<t := by
        intro lt
        have hit := cov _ lt
        simp [old] at hit
      simp [layerBits,old,show f (colorField d 2)=t by omega]
def layerWords (lo : Nat) : List Nat → Sig
  | [] => one
  | d::ds => prime false (layerRule lo d) (layerWords lo ds)
theorem layer_words {lo f t} (ds : List Nat) (h : ∀d∈ds, rankRule d f) (cov : layerCovers lo f t) :
    bit (colorPoint (layerBits lo f t)) (layerWords lo ds)=true := by
  induction ds with
  | nil => exact bit_one _
  | cons d ds ih =>
    rw [layerWords,bit_prime,layer_rule (h d (by simp)) cov,ih (fun e he => h e (by simp [he]))]
    rfl
def cubeParts (mask : Nat) : List (Fin 10) → Sig
  | [] => one
  | i::is => if mask.testBit i.val then cubeParts mask is else
      prime false (neg (inputs.getD i.val zero)) (cubeParts mask is)
theorem cube_parts {x : Fin 10 → Bool} (mask : Nat) (is : List (Fin 10))
    (h : bit (colorPoint x) (cubeParts mask is)=true) :
    ∀ i∈is, x i=true → mask.testBit i.val=true := by
  induction is with
  | nil => simp
  | cons j js ih =>
    by_cases hm : mask.testBit j.val=true
    · rw [cubeParts,if_pos hm] at h
      intro i hi hx
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hm
      · exact ih h i hi hx
    · rw [cubeParts,if_neg hm,bit_prime,bit_neg,color_bit] at h
      simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true,Bool.not_eq_true'] at h
      intro i hi hx
      rcases List.mem_cons.mp hi with rfl | hi
      · simp_all
      · exact ih h.2 i hi hx
def cubeWord (mask : Nat) := cubeParts mask (List.finRange 10)
def layerUpper (lo : Nat) : List Nat → Sig
  | [] => zero
  | a::as => if lo &&& a = lo then prime true (cubeWord a) (layerUpper lo as) else layerUpper lo as
theorem upper_choice {lo f t} (as : List Nat) (cov : layerCovers lo f t)
    (ok : bit (colorPoint (layerBits lo f t)) (layerUpper lo as)=true) :
    ∃ a∈as, layerCovers a f (t+1) := by
  induction as with
  | nil => rw [layerUpper,bit_zero] at ok; contradiction
  | cons a as ih =>
    have follow (h : bit (colorPoint (layerBits lo f t)) (layerUpper lo as)=true) : ∃ v∈a::as, layerCovers v f (t+1) := by
      obtain ⟨v,hv,cv⟩ := ih h
      exact ⟨v,List.mem_cons_of_mem _ hv,cv⟩
    by_cases sub : lo &&& a=lo
    · rw [layerUpper,if_pos sub,bit_prime] at ok
      rcases Bool.or_eq_true_iff.mp ok with hit | tail
      · refine ⟨a,by simp,?_⟩
        intro i hi
        by_cases old : lo.testBit i.val=true
        · have z := congrArg (fun v : Nat => v.testBit i.val) sub
          simpa only [Nat.testBit_and,old,Bool.true_and] using z
        · have ge : ¬ f i<t := fun lt => old (cov i lt)
          have yes : layerBits lo f t i=true := by simp [layerBits,old,show f i=t by omega]
          exact cube_parts a (List.finRange 10) hit i (by simp) yes
      · exact follow tail
    · rw [layerUpper,if_neg sub] at ok
      exact follow ok
def layerStep (ds : List Nat) (lo : Nat) (hi : List Nat) :=
  (prime false (layerWords lo ds) (neg (layerUpper lo hi)) == zero)
theorem layer_step {ds lo hi f t} (laws : ∀d∈ds,rankRule d f) (cov : layerCovers lo f t)
    (ok : layerStep ds lo hi=true) : ∃ a∈hi, layerCovers a f (t+1) := by
  have eq := beq_iff_eq.mp ok
  have chk := congrArg (bit (colorPoint (layerBits lo f t))) eq
  rw [bit_prime,bit_neg,bit_zero,layer_words ds laws cov] at chk
  apply upper_choice hi cov
  simpa using chk
def finalPair (lo d : Nat) := d.testBit 0 && !lo.testBit (colorField d 0).val && !lo.testBit (colorField d 1).val
def layerScan (ds lo : List Nat) : List (List Nat) → Bool
  | [] => lo.all fun a => ds.any (finalPair a)
  | hi::tail => (lo.all fun a => layerStep ds a hi) && layerScan ds hi tail
theorem layer_scan {ds f} (laws : ∀d∈ds,rankRule d f) (ls : List (List Nat))
    {lo t} (covered : ∃a∈lo,layerCovers a f t) (bound : ∀i, f i<t+ls.length+1)
    (ok : layerScan ds lo ls=true) : False := by
  induction ls generalizing lo t with
  | nil =>
    obtain ⟨a,ha,ca⟩ := covered
    obtain ⟨d,hd,yes⟩ := List.any_eq_true.mp (List.all_eq_true.mp ok a ha)
    simp only [finalPair,Bool.and_eq_true,Bool.not_eq_true'] at yes
    have top (i : Fin 10) (no : a.testBit i.val=false) : f i=t := by
      have small : f i<t+1 := by simpa using bound i
      have big : ¬ f i<t := by intro lt; have hh := ca i lt; simp [no] at hh
      omega
    have diff := laws d hd
    simp only [rankRule,yes.1.1,ite_true] at diff
    exact diff ((top _ yes.1.2).trans (top _ yes.2).symm)
  | cons l ls ih =>
    obtain ⟨a,ha,ca⟩ := covered
    have both := Bool.and_eq_true_iff.mp ok
    apply ih (t:=t+1) (layer_step laws ca (List.all_eq_true.mp both.1 a ha)) _ both.2
    intro i
    have z := bound i
    simp only [List.length_cons] at z
    omega
abbrev OrderPage := Nat × List Nat × Nat × List (List Nat)
def orderCheck (ws : List Sig) (T : Sig) (k : Nat) (book : OrderPage) :=
  let (names,ds,start,ls) := book
  decide (k+2 ≤ ws.toFinset.card+ls.length+1) &&
    (List.finRange 10).all (fun i => decide (colorWire ws names i ∈ ws)) &&
    ds.all (colorRule ws T names) && layerScan ds [start] ls
theorem order_sound {ws T k page} (ok : orderCheck ws T k page=true) : Impossible false T k ws.toFinset := by
  rcases page with ⟨names,ds,start,ls⟩
  simp only [orderCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  intro n le run
  obtain ⟨count,f,mass,bound,law⟩ := order_live run
  apply layer_scan (f:=fun i => f (colorWire ws names i)) (fun d hd => rank_rule (ok.1.2 d hd) law)
    ls (t:=0) (lo:=[start]) ⟨start,by simp,by simp [layerCovers]⟩ _ ok.2
  intro i
  have use := (ok.1.1.2 _ (List.mem_finRange i))
  have less := bound _ (List.mem_toFinset.mpr use)
  have size := ok.1.1.1
  omega
def orderRange (g : Forest) (k a n : Nat) (pages : Nat → OrderPage) :=
  (List.range n).all fun i => orderCheck (stateSet g k (a+i)) (targetOf g) k (pages i)
theorem orderCut {g k a n pages} (mode : g.mode=false) (ok : orderRange g k a n pages=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp ok (j-a) (List.mem_range.mpr (by omega))
  have eq : a+(j-a)=j := by omega
  change orderCheck (stateSet g k (a+(j-a))) _ _ _=true at hh
  rw [eq] at hh
  exact order_sound hh
def padColumn (n v : Nat) : Bits :=
  BitVec.ofNat 320 (v + if v % 2=1 then (1 <<< 320)-(1 <<< n) else 0)
theorem lowerHint {u raw T a b} (h : Lower u raw T a) (le : b ≤ a) : Lower u raw T b :=
  fun p bank hr hit => le.trans (h p bank hr hit)
def treeData (p n v : Nat) :=
  let row := fun base i => (base >>> (10*((v >>> (8+5*i)) % 32))) % 1024
  v % 256 + (row p 0 <<< 8) + (row n 1 <<< 18) + (row n 2 <<< 28) +
    (row n 3 <<< 38) + (row p 4 <<< 48) + (row p 5 <<< 58)
def ruleData (p n v : Nat) :=
  let row := fun base i => (base >>> (10*((v >>> (13+5*i)) % 32))) % 1024
  v % 8192 + (row p 0 <<< 13) + (row n 1 <<< 23) + (row n 2 <<< 33) +
    (row (if v.testBit 0 then n else p) 3 <<< 43) + (row p 4 <<< 53) + (row p 5 <<< 63)
theorem countFace {u m L} (hints : Nat)
    (hp : properB (graphGoal m)=true)
    (ess : checkEssential (graphGoal m) (varsX m) (graphPairs m hints)=true)
    (enough : L ≤ (List.map Prod.fst (graphPairs m hints)).toFinset.card - 1) :
    Lower u (varsX m) (graphGoal m) L :=
  lowerHint (lower_count (proper_of _ hp) (graphPairs m hints) ess) enough
theorem dropFace {u m q a L} (fixed hints : Nat) (prior : Lower u (varsX q) (graphGoal q) a)
    (mapped : checkLift (fixRows fixed 0) (graphGoal m) (varsX m) (varsX q) (graphGoal q) (graphPairs fixed hints)=true)
    (hm : properB (graphGoal m)=true) (hq : properB (graphGoal q)=true)
    (enough : L ≤ a + (List.map Prod.fst (graphPairs fixed hints)).toFinset.card) :
    Lower u (varsX m) (graphGoal m) L :=
  lowerHint (lift_ok mapped (proper_of _ hm) (proper_of _ hq) prior) enough
abbrev Face (u : Bool) (m L : Nat) := Lower u (varsX m) (graphGoal m) L
def tableWord (xs : Array Nat) (i : Nat) := xs.getD (i%8) 0
def tablePair (xs : Array (Nat × Nat)) (i : Nat) := xs.getD (i%8) (0,0)
def tableBits (xs : Array (Bits × Bits)) (i : Nat) := xs.getD (i%8) (0,0)
def readRules (pos neg width : Nat) (rules : Nat → Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,v => ruleData pos neg (rules (v % (1 <<< width))) :: readRules pos neg width rules n (v >>> width)
def readPanel (pos neg rw pw : Nat) (rules programs : Nat → Nat) (rec : Nat) :=
  let program := programs (rec % (1 <<< pw))
  (rec >>> pw,readRules pos neg rw rules (program % 16) (program >>> 4))
theorem consFace {u m L es} (h : Face u m L) (tail : Known u es) : Known u ((m,L)::es) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | h'
  · exact h
  · exact tail e h'
def smallSlot (h buckets slots iw pw : Nat) (disp slotsAt : Nat → Nat) : Option (Nat × Nat) :=
  let slot := (h/buckets+disp (h%buckets))%slots
  let val := slotsAt slot
  if val=0 || (val >>> (iw+pw)) != (h/(buckets*slots))%8 then none
  else some (val % (1 <<< iw)-1,(val >>> iw)%(1 <<< pw))
def variableSlot (blocks : Nat → Nat × Nat) (i : Nat) :=
  let b := blocks (i/16)
  let offsets := b.1 >>> (12*(i%16))
  let start := offsets % 4096
  (b.2 >>> start) % (1 <<< ((offsets >>> 12)%4096 - start))
def bookData (d fw mw : Nat) (fronts masks codes costs : Nat → Nat) (j : Nat) :=
  let i := j/2
  if j%2=1 then costs i else
    let code := codes i
    fronts (code % (1 <<< fw)) + ((code >>> (fw+mw)) <<< (12*(d-1))) +
      (masks ((code >>> fw)%(1 <<< mw)) <<< (12*d))
noncomputable def bandTest (g : Forest) (k a n ar : Nat) :=
  header g k a n ar && rowCut g k a n ar 0 ar
theorem bandTest_sound {g k a n ar} (ok : bandTest g k a n ar=true) :
    block g k a n=true :=
  cutsBlock (Bool.and_eq_true_iff.mp ok).1 (Bool.and_eq_true_iff.mp ok).2
noncomputable def bandCells (g : Forest) (k a n ar : Nat) (splitBand : Bool) :=
  if splitBand then bandTest g k a (n/2) ar && bandTest g k (a+n/2) (n-n/2) ar
  else bandTest g k a n ar
theorem bandCut {g k a n} (ar : Nat) (splitBand : Bool) (ok : bandCells g k a n ar splitBand=true) :
    CutRow g k a n := by
  apply checkedRow
  cases splitBand
  · exact bandTest_sound ok
  · have both := Bool.and_eq_true_iff.mp ok
    have all := block_merge (bandTest_sound both.1) (bandTest_sound both.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using all
def readGroup (n pad : Nat) : Nat → Nat → List Nat
  | 0,_ => []
  | s+1,x => (pad+x % (1 <<< n)) :: readGroup n pad s (x >>> n)
def readGroups (n pad : Nat) : Nat → Nat → List (List Nat)
  | 0,_ => []
  | s+1,x =>
    let len := x % 64
    readGroup n pad len (x >>> 6) :: readGroups n pad s (x >>> (6+n*len))
def orderPage (pos neg w : Nat) (bank : Nat → Nat) (n q names clauses groups : Nat) : OrderPage :=
  let pad := 1024-(1 <<< n)
  (names,readRules pos neg w bank (clauses % 128) (clauses >>> 7),pad,readGroups n pad (q-1) groups)

theorem h6_1 : Face true 6 1 := countFace 288 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h12_1 : Face true 12 1 := carry_of (swaps:=[33,49]) (by decide +kernel) h6_1
theorem h14_2 : Face true 14 2 := countFace 8480 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h17_1 : Face true 17 1 := carry_of (swaps:=[66,50,16]) (by decide +kernel) h6_1
theorem h24_1 : Face true 24 1 := carry_of (swaps:=[66,49]) (by decide +kernel) h6_1
theorem h28_2 : Face true 28 2 := carry_of (swaps:=[50,33,65]) (by decide +kernel) h14_2

namespace B29_4
def entries : List (Nat × Nat) := []
theorem prior : Known true entries := (known_down baseKnown)
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 20 0xe0ef0,padColumn 20 0xabad0),(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x7dc3,padColumn 20 0x75d81),(padColumn 20 0x1f3cf,padColumn 20 0x8a246),(padColumn 20 0xf8f3c,padColumn 20 0x54528),(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x0,padColumn 20 0x0)] i else tableBits #[(padColumn 20 0x0,padColumn 20 0x0),(padColumn 20 0x0,padColumn 20 0x0)] i))
def cols : List ColumnInfo := []
def data3 : Nat → Nat := (fun i => tableWord #[0xf,0x0] i)
def levels : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,data3)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def book : Forest := ⟨29,3,samples,cols,[[],[32,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row3_0 : CutRow book 3 0 1 := bandCut 4 false (by decide +kernel)
theorem band3 : CutRow book 3 0 1 := row3_0
theorem checked : mixedTables book 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band3
end B29_4
theorem h29_4 : Face true 29 4 :=
  mixedLower (g:=B29_4.book) (i:=0) (hints:=8964)
    (before_sound B29_4.entries B29_4.prior) B29_4.geometry B29_4.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h30_4 : Face true 30 4 := carry_of (swaps:=[66,16]) (by decide +kernel) h29_4
theorem h33_1 : Face true 33 1 := carry_of (swaps:=[82,66,50,16]) (by decide +kernel) h6_1
theorem h49_2 : Face true 49 2 := carry_of (swaps:=[83,65,16,32]) (by decide +kernel) h14_2
theorem h57_4 : Face true 57 4 := carry_of (swaps:=[82,48]) (by decide +kernel) h29_4

namespace B63_7
def entries : List (Nat × Nat) := [(29,4),(30,4),(57,4)]
theorem prior : Known true entries := (consFace h29_4 (consFace h30_4 (consFace h57_4 (known_down baseKnown))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 82 0x93fffe00003ff8460fc0,padColumn 82 0x1caaa0860ea50460d40),(padColumn 82 0x17fc000001fc31981fc03,padColumn 82 0x7fc186308b4319815801),(padColumn 82 0x3a4400007ffcc603ffc0f,padColumn 82 0x380061843348c602ca406),(padColumn 82 0x24fc001ffe03007fe103c,padColumn 82 0xfd8209cc13005521018),(padColumn 82 0x3f8807ff80000ffc860f0,padColumn 82 0x3f02055610600aa8860a0),(padColumn 82 0x3ff3f8000003f86318300,padColumn 82 0x3fe354186181586318200),(padColumn 82 0x0,padColumn 82 0x0),(padColumn 82 0x0,padColumn 82 0x0)] i else tableBits #[(padColumn 82 0x0,padColumn 82 0x0),(padColumn 82 0x0,padColumn 82 0x0)] i))
def cols : List ColumnInfo := [(1,32,30,0,4),(4,2,57,0,4),(34,0,29,0,4)]
def data6 : Nat → Nat := (fun i => tableWord #[0x3f,0x603] i)
def levels : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def book : Forest := ⟨63,6,samples,cols,[[],[32,81,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 6 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band6
end B63_7
theorem h63_7 : Face true 63 7 :=
  mixedLower (g:=B63_7.book) (i:=0) (hints:=8484)
    (before_sound B63_7.entries B63_7.prior) B63_7.geometry B63_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h66_1 : Face true 66 1 := carry_of (swaps:=[98,82,66,50]) (by decide +kernel) h6_1
theorem h70_2 : Face true 70 2 := carry_of (swaps:=[99,83,67,33]) (by decide +kernel) h14_2
theorem h78_4 : Face true 78 4 := carry_of (swaps:=[98,82,66,48,16]) (by decide +kernel) h29_4
theorem h95_7 : Face true 95 7 := carry_of (swaps:=[101,66,16]) (by decide +kernel) h63_7
theorem h132_1 : Face true 132 1 := carry_of (swaps:=[114,98,82,66,33,49]) (by decide +kernel) h6_1
theorem h164_2 : Face true 164 2 := carry_of (swaps:=[114,98,83,33,65]) (by decide +kernel) h14_2
theorem h165_4 : Face true 165 4 := carry_of (swaps:=[115,67,100,83]) (by decide +kernel) h29_4
theorem h166_4 : Face true 166 4 := carry_of (swaps:=[115,50,98,83,66,16]) (by decide +kernel) h29_4
theorem h156_4 : Face true 156 4 := carry_of (swaps:=[114,98,32,66,50,80,16]) (by decide +kernel) h29_4
theorem h172_4 : Face true 172 4 := carry_of (swaps:=[115,50,98,48,66,80,16]) (by decide +kernel) h29_4
theorem h177_4 : Face true 177 4 := carry_of (swaps:=[114,50,99,82,64]) (by decide +kernel) h29_4

namespace B189_8
def entries : List (Nat × Nat) := [(29,4),(57,4),(156,4),(165,4),(172,4),(177,4)]
theorem prior : Known true entries := (consFace h29_4 (consFace h57_4 (consFace h156_4 (consFace h165_4 (consFace h172_4 (consFace h177_4 (known_down baseKnown)))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 84 0xe4003ffc00007ff8430f0,padColumn 84 0xe010e55410c07a9043050),(padColumn 84 0x0,padColumn 84 0x0),(padColumn 84 0x3c0fc0000fc3e3183f303,padColumn 84 0x1c2a430c2343431816101),(padColumn 84 0xe8000003ffcc0c07ff00f,padColumn 84 0xe0c10c115c8c0c0569006),(padColumn 84 0x5c0000fff03180ffc403c,padColumn 84 0x1f0610aaa131806a84028),(padColumn 84 0x9ff03f00003e1f2198cc0,padColumn 84 0x1d681a20c62a052198480),(padColumn 84 0x0,padColumn 84 0x0),(padColumn 84 0xf3ffc000003ff0c620f00,padColumn 84 0xe295a0c30814b0c620a00)] i else tableBits #[(padColumn 84 0x0,padColumn 84 0x0),(padColumn 84 0x0,padColumn 84 0x0)] i))
def cols : List ColumnInfo := [(12,0,177,0,4),(17,0,172,0,4),(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]
def data7 : Nat → Nat := (fun i => tableWord #[0x3f,0x171506] i)
def data6 : Nat → Nat := (fun i => tableWord #[0x7f420,0x0,0x7f440,0x201] i)
def data5 : Nat → Nat := (fun i => tableWord #[0xb7cc3440,0x0] i)
def levels : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,data5)
  | 6 => (2,1,3,0,0,0,0,data6)
  | 7 => (1,0,3,0,0,0,0,data7)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun v => (if v=7502621870530246385 then some (0,0) else none)
  | 7 => fun h => smallSlot h 4 14 2 4 (fun i => ((fun i => tableWord #[0x2000] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0xa200000010346416663cd6000009cca] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨189,7,samples,cols,[[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66],[112,66,48,82]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 1 := bandCut 6 false (by decide +kernel)
theorem band7 : CutRow book 7 0 1 := row7_0
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 2 := bandCut 7 false (by decide +kernel)
theorem band6 : CutRow book 6 0 2 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 1 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 1 := row5_0
theorem checked : mixedTables book 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band5
  · exact band6
  · exact band7
end B189_8
theorem h189_8 : Face true 189 8 :=
  mixedLower (g:=B189_8.book) (i:=0) (hints:=536879876)
    (before_sound B189_8.entries B189_8.prior) B189_8.geometry B189_8.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h198_4 : Face true 198 4 := carry_of (swaps:=[114,96,82,50,64,16]) (by decide +kernel) h29_4
theorem h231_7 : Face true 231 7 := carry_of (swaps:=[83,82,114,99,66,16]) (by decide +kernel) h63_7
theorem h183_7 : Face true 183 7 := carry_of (swaps:=[115,84,99]) (by decide +kernel) h63_7

namespace B190_7
def entries : List (Nat × Nat) := [(30,4),(156,4),(166,4)]
theorem prior : Known true entries := (consFace h30_4 (consFace h156_4 (consFace h166_4 (known_down baseKnown))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0xfcfe000001f86030fc03,padColumn 80 0xfc7e0c20c3586030d401),(padColumn 80 0x279203e03ff81c0ffccf,padColumn 80 0x38012810ca018052846),(padColumn 80 0x5d2e001ffe0183ff043c,padColumn 80 0x1c0e604a720982aa0418),(padColumn 80 0xebf4001fc0060ff11830,padColumn 80 0xe3f1819584360d511820),(padColumn 80 0x93fffc000007f0c66300,padColumn 80 0x3feb60618c550c66100),(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0xfe49ffe00007ff0883c0,padColumn 80 0xfc0149782102a7088280)] i else tableBits #[(padColumn 80 0x0,padColumn 80 0x0),(padColumn 80 0x0,padColumn 80 0x0)] i))
def cols : List ColumnInfo := [(8,16,166,0,4),(24,0,166,0,4),(34,0,156,0,4),(128,32,30,0,4),(160,0,30,0,4)]
def data6 : Nat → Nat := (fun i => tableWord #[0x3f,0x4cc05] i)
def data5 : Nat → Nat := (fun i => tableWord #[0x7ec20,0x0] i)
def levels : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,data5)
  | 6 => (1,0,3,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun v => (if v=7689521405595769300 then some (0,0) else none)
  | _ => fun _ => none
def book : Forest := ⟨190,6,samples,cols,[[],[115,84]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 6 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 1 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 1 := row5_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band5
  · exact band6
end B190_7
theorem h190_7 : Face true 190 7 :=
  mixedLower (g:=B190_7.book) (i:=0) (hints:=544416032)
    (before_sound B190_7.entries B190_7.prior) B190_7.geometry B190_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h222_7 : Face true 222 7 := carry_of (swaps:=[101,113]) (by decide +kernel) h190_7
theorem h238_7 : Face true 238 7 := carry_of (swaps:=[84,100,49,113]) (by decide +kernel) h190_7

namespace B255_11
def entries : List (Nat × Nat) := [(29,4),(30,4),(57,4),(63,7),(78,4),(95,7),(166,4),(177,4),(183,7),(189,8),(190,7),(198,4),(222,7),(231,7),(238,7)]
theorem prior : Known true entries := (consFace h29_4 (consFace h30_4 (consFace h57_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h166_4 (consFace h177_4 (consFace h183_7 (consFace h189_8 (consFace h190_7 (consFace h198_4 (consFace h222_7 (consFace h231_7 (consFace h238_7 (known_down baseKnown))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 248 0xf8787c3f888447fe210f80000001ffffe0000000000c03ffffc02060303c0,padColumn 248 0x78783c3f800003fe0007802030074aaaa0080c06000c03d55280206030140),(padColumn 248 0x1088fffc7910888425fff80000ffe0000000003fe0603ff0180c0c01ff0c03,padColumn 248 0x7ffc7800000001fff80c0455201806030125a0602aa0180c0c01560401),(padColumn 248 0x211108448f813fcbfe210801ff00000000007fffe01fc000603001ffff300f,padColumn 248 0x7803fc3fe000010d10080601804165a40168000603000aca91006),(padColumn 248 0x47f813ff8227d13c484ff8000000000001ffffc0018000c18003fffe04003c,padColumn 248 0x7f803ff8007c03c000ff8600803018020a9e980818000c18002ab52040018),(padColumn 248 0xfa227c8917fa03d09ff2100000000007ffff80000603030007fffe081800f0,padColumn 248 0xf8007c0007f803c01ff00180300c0205555602030603030002d554081800a0),(padColumn 248 0x8444211227fffc211fffa7fe00001ff8000000001fe40c0ff840303060c300,padColumn 248 0x7fffc001fff82b440300b5040180c0c15440c02a8403030604200),(padColumn 248 0xffffc22047ffffffe084400000ffe0000000000018183ff60180c0c0800c00,padColumn 248 0xffff800007ffffffe000060180aacc0180603010181815560180c0c0800800),(padColumn 248 0xfffffffffc442202110807ffff000000000000001ffff0080603010100f000,padColumn 248 0xfffffffff80000000000054b2ec01006018040200aa970080603010100a000)] i else tableBits #[(padColumn 248 0x0,padColumn 248 0x0),(padColumn 248 0x0,padColumn 248 0x0)] i))
def cols : List ColumnInfo := [(2,64,189,0,8),(66,0,189,0,8),(17,0,238,0,7),(24,0,231,0,7),(33,0,222,0,7),(65,0,190,0,7),(72,0,183,0,7),(160,0,95,0,7),(192,0,63,0,7),(41,16,198,0,4),(56,1,198,0,4),(57,0,198,0,4),(73,16,166,0,4),(78,0,177,0,4),(89,0,166,0,4),(176,1,78,0,4),(177,0,78,0,4),(193,32,30,0,4),(198,0,57,0,4),(225,0,30,0,4),(226,0,29,0,4)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x220ce106] i)
def data9 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x1ff440,0x2a014f04,0x1ff460,0xe038f04,0x1ff462,0xf44c40d05,0x1ff482,0x115200cc05] i else tableWord #[0x1ff4a3,0x202d103,0x1ff4e3,0xa48c80f18707,0x1ff4a4,0x53202d105,0x1ff862,0x83d14930cd08] i) else tableWord #[0x1ff882,0x321224d06,0x1ffc40,0x31c529206] i))
def data8 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0x2efd04460,0x306102,0x2f7d03482,0x306102,0x2fed004a4,0x306102,0x2ef504c40,0x1201] i else tableWord #[0x3f7862460,0x18e02,0x3f74e3462,0x1401,0x2ff507462,0x0,0x2ffd07482,0x0] i) else tableWord #[0x2ffd024e3,0x6001] i))
def levels : Nat → Packing
  | 8 => (9,2,5,0,0,0,0,data8)
  | 9 => (10,1,5,0,0,0,0,data9)
  | 10 => (1,0,5,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun h => smallSlot h 5 17 4 1 (fun i => ((fun i => tableWord #[0x380c4] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0xe502d4612369a708e6e4760000000000,0x0] i) (i/16) >>> (8*(i%16))) % 256)
  | 10 => fun h => smallSlot h 8 25 4 1 (fun i => ((fun i => tableWord #[0x10400180c1] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0xd800000000e15265440043e92600a2,0x338a008708191594] i) (i/16) >>> (8*(i%16))) % 256)
  | _ => fun _ => none
def book : Forest := ⟨255,10,samples,cols,[[],[115,84]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 10 := bandCut 9 true (by decide +kernel)
theorem band9 : CutRow book 9 0 10 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 4 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_4 : CutRow book 8 4 5 := bandCut 9 false (by decide +kernel)
theorem combine8_0_9 : CutRow book 8 0 9 := @joinRow book 8 0 4 5 row8_0 row8_4
theorem band8 : CutRow book 8 0 9 := combine8_0_9
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
  · exact band10
end B255_11
theorem h255_11 : Face true 255 11 :=
  mixedLower (g:=B255_11.book) (i:=0) (hints:=553656612)
    (before_sound B255_11.entries B255_11.prior) B255_11.geometry B255_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h305_4 : Face true 305 4 := carry_of (swaps:=[130,114,50,99,82,64]) (by decide +kernel) h29_4
theorem h326_4 : Face true 326 4 := carry_of (swaps:=[130,50,115,98,83,32,64,16]) (by decide +kernel) h29_4
theorem h352_2 : Face true 352 2 := carry_of (swaps:=[130,33,113,99,82,65]) (by decide +kernel) h14_2
theorem h353_4 : Face true 353 4 := carry_of (swaps:=[131,50,66,116,99,82]) (by decide +kernel) h29_4
theorem h354_4 : Face true 354 4 := carry_of (swaps:=[131,67,116,99,82,16]) (by decide +kernel) h29_4
theorem h359_7 : Face true 359 7 := carry_of (swaps:=[131,67,116,99,82,16]) (by decide +kernel) h63_7
theorem h366_7 : Face true 366 7 := carry_of (swaps:=[128,64,116,49,96]) (by decide +kernel) h63_7
theorem h371_7 : Face true 371 7 := carry_of (swaps:=[131,84,115,98]) (by decide +kernel) h63_7
theorem h377_7 : Face true 377 7 := carry_of (swaps:=[128,80,84,66,16,114,97,48]) (by decide +kernel) h63_7
theorem h317_7 : Face true 317 7 := carry_of (swaps:=[133,117,80,48,50,33,97,64]) (by decide +kernel) h63_7
theorem h350_7 : Face true 350 7 := carry_of (swaps:=[133,117,50,65,96]) (by decide +kernel) h63_7

namespace B383_11
def entries : List (Nat × Nat) := [(57,4),(63,7),(78,4),(95,7),(317,7),(326,4),(350,7),(353,4),(354,4),(359,7),(366,7),(371,7),(377,7)]
theorem prior : Known true entries := (consFace h57_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h317_7 (consFace h326_4 (consFace h350_7 (consFace h353_4 (consFace h354_4 (consFace h359_7 (consFace h366_7 (consFace h371_7 (consFace h377_7 (known_down baseKnown))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 248 0x87c3ffe22111ffc421f00000003ffffc0000000000180fffff0080c0303c0,padColumn 248 0x3c3ffe00000ffc000f0040300e955540100c03000180f554a0080c030140),(padColumn 248 0x17ffc03e44222084bfff00000ffc0000000003ff03007fc060303003ff0c03,padColumn 248 0x7ffc01e000000003fff01804aa40300c060112d03006a8060303002560401),(padColumn 248 0xf88447e3e04ff17fc421000000000000000fffff0c06000180c007ffff000f,padColumn 248 0xf80003e1e00ff07fc000060180100c03008566d20c06000180c00559a90006),(padColumn 248 0x213ffc4089f44f8909ff0000000000003ffffc0030180306000ffffc04003c,padColumn 248 0x3ffc0001f00f8001ff180600603004153a980430180306000aaaa4040018),(padColumn 248 0xffc88885fe80f213fe420000000000fffff00000c0600c001ffff8101800f0,padColumn 248 0xffc00001fe00f003fe006018018040aaaac02018c0600c000b5550101800a0),(padColumn 248 0x42111109ffff0423fff4ffc00003ff0000000000ff80303fe100c06060c300,padColumn 248 0x1ffff0003fff0aaa006016a080300c060aa80300aa100c060604200),(padColumn 248 0x84222211fffffffc1088003ffffc00000000000000ffffd806030180803c00,padColumn 248 0x1fffffffc0000802a955980300c03008000d5155806030180801800),(padColumn 248 0x0,padColumn 248 0x0)] i else tableBits #[(padColumn 248 0xffffffff110888422100fffff000000000000000ffffc020180c060300f000,padColumn 248 0xfffffffe0000000000005555680200c0300c0300552ac020180c060300a000),(padColumn 248 0x0,padColumn 248 0x0)] i))
def cols : List ColumnInfo := [(6,0,377,0,7),(12,0,371,0,7),(17,0,366,0,7),(24,0,359,0,7),(33,0,350,0,7),(66,0,317,0,7),(288,0,95,0,7),(320,0,63,0,7),(22,8,353,0,4),(29,0,354,0,4),(56,1,326,0,4),(57,0,326,0,4),(304,1,78,0,4),(324,2,57,0,4)]
def data10 : Nat → Nat := (fun i => tableWord #[0xff,0x1256034708] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x1ff420,0x14d02,0x1ff440,0x12a02,0x1ff460,0x1b10b04] i)
def data8 : Nat → Nat := (fun i => tableWord #[0x2efd04460,0x0] i)
def levels : Nat → Packing
  | 8 => (1,2,4,0,0,0,0,data8)
  | 9 => (3,1,4,0,0,0,0,data9)
  | 10 => (1,0,4,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 9 => fun v => (if v=9836245588253958792 then some (0,0) else none)
  | 10 => fun h => smallSlot h 13 44 2 4 (fun i => ((fun i => tableWord #[0xc0000000001000] i) (i/16) >>> (6*(i%16))) % 64) (fun i => ((fun i => tableWord #[0x23003de000051c9400000000061,0x96c760d27c1eb801320000000019e,0x23c00662d0039600f38018511] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨383,10,samples,cols,[[],[98,131,84],[16,66,101],[16,82,131,100],[32,81,67,134],[32,81,128,99,65,67,64],[48,129,98,16,66,84],[48,129,82],[64,97,33,50,48,80,133],[64,97,130,83],[80,33,49,65,16,129,97],[80,33,99,132],[96,65,50,133],[96,65,32,83,129,49,50],[128,49,100],[128,49,66,16,82,98]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 8 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 3 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 3 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 1 := bandCut 8 false (by decide +kernel)
theorem band8 : CutRow book 8 0 1 := row8_0
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band8
  · exact band9
  · exact band10
end B383_11
theorem h383_11 : Face true 383 11 :=
  mixedLower (g:=B383_11.book) (i:=0) (hints:=21491622180)
    (before_sound B383_11.entries B383_11.prior) B383_11.geometry B383_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h486_8 : Face true 486 8 := carry_of (swaps:=[115,83,82,130,99,66,16]) (by decide +kernel) h189_8
theorem h503_11 : Face true 503 11 := carry_of (swaps:=[115,82,98,131,66,16]) (by decide +kernel) h255_11
theorem h480_4 : Face true 480 4 := carry_of (swaps:=[32,48,132,115,98,80,16]) (by decide +kernel) h29_4
theorem h497_7 : Face true 497 7 := carry_of (swaps:=[113,82,129,98,16,48]) (by decide +kernel) h190_7
theorem h509_11 : Face true 509 11 := carry_of (swaps:=[82,48,66,129,112]) (by decide +kernel) h255_11
theorem h510_11 : Face true 510 11 := carry_of (swaps:=[84,100,49,113,128]) (by decide +kernel) h255_11

namespace B511_13
def entries : List (Nat × Nat) := [(29,4),(30,4),(63,7),(78,4),(95,7),(177,4),(189,8),(222,7),(231,7),(255,11),(305,4),(353,4),(371,7),(377,7),(383,11),(480,4),(486,8),(497,7),(503,11),(509,11),(510,11)]
theorem prior : Known true entries := (consFace h29_4 (consFace h30_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h177_4 (consFace h189_8 (consFace h222_7 (consFace h231_7 (consFace h255_11 (consFace h305_4 (consFace h353_4 (consFace h371_7 (consFace h377_7 (consFace h383_11 (consFace h480_4 (consFace h486_8 (consFace h497_7 (consFace h503_11 (consFace h509_11 (consFace h510_11 (known_down baseKnown))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 320 0x3e1f0fe108210fff0820f800000000000003fffff8000000000000c0003007fffff00201803003c0,padColumn 320 0x3e0f0fe0000007ff0000780100300200c00f4aaaa8008030060000c0003007d554a0020180300140),(padColumn 320 0x43fff1e21042104117fff800000000003ffc00000000000ffe060000600ffe0180300c007ff00c03,padColumn 320 0x1fff1e00000000007fff80600400c012aa40180180300465a060000600d540180300c0055600401),(padColumn 320 0x8421123f009ff8bff8410800000001ffc000000000007ffffe1803001ff0000600c001fffff0300f,padColumn 320 0x1f001ff83ff8000018018010b44010060060042599a418030015a0000600c0012b2a901006),(padColumn 320 0xc04ffe0427e427c2209ff800000000000000000007fffff000600c0180001818000fffff8040003c,padColumn 320 0xc00ffe0007e007c0001ff860060060020060180082a9da6008600c0180001818000aaad480400018),(padColumn 320 0x9f2245ff900f904ffe21000000000000000007fffff80000180300600c060007ffffe02018000f0,padColumn 320 0x1f0001ff800f800ffe001801801800c01802055555600803180300600c060002b555402018000a0),(padColumn 320 0x1084489fffff0208ffffa7ff000ffe000003ff800000000001fe403fe10181ff8100300c060cc300,padColumn 320 0x1fffff0000ffff82aa2002b4100600b50100180300c15440154101802a8100300c06044200),(padColumn 320 0xff08811fffffffff01044000fff000003ffc0000000000000001ffd8060ffe600600c03008030c00,padColumn 320 0xfe00001fffffffff000002006a9600601558c00600600c0100016a980602aa600600c03008010800),(padColumn 320 0xffffffe84208401042080000000fffffc0000000000000000001803ffff60080180300401000f000,padColumn 320 0xffffffe00000000000000400c00d4b4b98010018018010020001802aaa560080180300401000a000)] i else tableBits #[(padColumn 320 0x2000001084108420841007fffff00000000000000000000001ffffe018080100600c0180600f0000,padColumn 320 0x55595680180200200600600600c00aa956018080100600c0180600a0000),(padColumn 320 0x0,padColumn 320 0x0)] i))
def cols : List ColumnInfo := [(1,0,510,0,11),(2,0,509,0,11),(8,0,503,0,11),(128,0,383,0,11),(256,0,255,0,11),(9,16,486,0,8),(25,0,486,0,8),(258,64,189,0,8),(322,0,189,0,8),(14,0,497,0,7),(134,0,377,0,7),(140,0,371,0,7),(280,0,231,0,7),(289,0,222,0,7),(416,0,95,0,7),(448,0,63,0,7),(31,0,480,0,4),(154,4,353,0,4),(202,4,305,0,4),(334,0,177,0,4),(401,32,78,0,4),(418,64,29,0,4),(449,32,30,0,4)]
def data12 : Nat → Nat := (fun i => tableWord #[0x1ff,0x1142438cc809] i)
def data11 : Nat → Nat := (fun i => tableWord #[0x3ff0a2,0x72051a7a0d24e09,0x3ff4a2,0x730f8248a18ce2a54560d,0x3ff8a2,0x528c3e090d9d058b0b] i)
def data10 : Nat → Nat := (fun i => tableWord #[0x57fd274a2,0x32601d9c89606,0x7dbca28a2,0xb2a4c80e05,0x77fd274a2,0x3c91403,0x5ff5258a2,0x3c91403] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x97fd475258a2,0x0] i)
def levels : Nat → Packing
  | 9 => (1,3,5,0,0,0,0,data9)
  | 10 => (4,2,5,0,0,0,0,data10)
  | 11 => (3,1,5,0,0,0,0,data11)
  | 12 => (1,0,5,0,0,0,0,data12)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun v => (if v=11369311757800862412 then some (0,0) else none)
  | 11 => fun v => (if v=11369311757800862412 then some (0,0) else (if v=11458423956265286981 then some (1,0) else (if v=12322638194242191766 then some (3,0) else (if v=12698024304231822181 then some (2,0) else none))))
  | 12 => fun v => (if v=11787858522310454322 then some (2,1) else (if v=12115950459901266192 then some (2,0) else (if v=12322638194242191766 then some (1,0) else (if v=13136768276869170638 then some (0,0) else none))))
  | _ => fun _ => none
def book : Forest := ⟨511,12,samples,cols,[[],[48,129,82],[16,82,131,100],[128,49,100]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 1 := bandCut 9 false (by decide +kernel)
theorem band12 : CutRow book 12 0 1 := row12_0
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 3 := bandCut 10 false (by decide +kernel)
theorem band11 : CutRow book 11 0 3 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 2 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_2 : CutRow book 10 2 2 := bandCut 10 false (by decide +kernel)
theorem combine10_0_4 : CutRow book 10 0 4 := @joinRow book 10 0 2 2 row10_0 row10_2
theorem band10 : CutRow book 10 0 4 := combine10_0_4
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 9 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
theorem checked : mixedTables book 12 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
  · exact band12
end B511_13
theorem h511_13 : Face true 511 13 :=
  mixedLower (g:=B511_13.book) (i:=0) (hints:=22028493092)
    (before_sound B511_13.entries B511_13.prior) B511_13.geometry B511_13.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h528_1 : Face true 528 1 := carry_of (swaps:=[146,130,114,98,33,81,66,49]) (by decide +kernel) h6_1
theorem h576_1 : Face true 576 1 := carry_of (swaps:=[146,130,33,113,98,81,66,49]) (by decide +kernel) h6_1
theorem h593_4 : Face true 593 4 := carry_of (swaps:=[147,131,50,114,99,82]) (by decide +kernel) h29_4
theorem h599_7 : Face true 599 7 := carry_of (swaps:=[147,131,67,116,66,99,82,16]) (by decide +kernel) h63_7
theorem h606_8 : Face true 606 8 := carry_of (swaps:=[151,135,101,66,16]) (by decide +kernel) h189_8
theorem h657_4 : Face true 657 4 := carry_of (swaps:=[147,131,114,99,82]) (by decide +kernel) h29_4
theorem h540_4 : Face true 540 4 := carry_of (swaps:=[146,130,114,98,67,32,80,16]) (by decide +kernel) h29_4
theorem h652_4 : Face true 652 4 := carry_of (swaps:=[146,130,115,98,48,66,80,16]) (by decide +kernel) h29_4
theorem h660_4 : Face true 660 4 := carry_of (swaps:=[147,131,116,66,99,32,80,16]) (by decide +kernel) h29_4
theorem h664_4 : Face true 664 4 := carry_of (swaps:=[147,50,130,115,48,98,80,16]) (by decide +kernel) h29_4

namespace B668_7
def entries : List (Nat × Nat) := [(156,4),(540,4),(652,4),(660,4),(664,4)]
theorem prior : Known true entries := (consFace h156_4 (consFace h540_4 (consFace h652_4 (consFace h660_4 (consFace h664_4 (known_down baseKnown))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x1e1e3e3c33,padColumn 45 0x2742a3c2411),(padColumn 45 0x1ff81fc0f,padColumn 45 0xc8355819806),(padColumn 45 0x1e1e077c4cc,padColumn 45 0x112ca2664448),(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x1e1e01cecb30,padColumn 45 0x150ac542c920)] i else tableBits #[(padColumn 45 0x0,padColumn 45 0x0),(padColumn 45 0x1fe001f933c0,padColumn 45 0xad118993280)] i))
def cols : List ColumnInfo := [(4,0,664,0,4),(8,0,660,0,4),(16,0,652,0,4),(128,0,540,0,4),(512,0,156,0,4)]
def data6 : Nat → Nat := (fun i => tableWord #[0x1f,0x29c05] i)
def data5 : Nat → Nat := (fun i => tableWord #[0x3f420,0x0,0x3f440,0x101] i)
def data4 : Nat → Nat := (fun i => tableWord #[0x5dca1440,0x0] i)
def levels : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,data4)
  | 5 => (2,1,3,0,0,0,0,data5)
  | 6 => (1,0,3,0,0,0,0,data6)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun v => (if v=5239425270783651293 then some (0,0) else none)
  | 6 => fun h => smallSlot h 5 16 2 4 (fun i => ((fun i => tableWord #[0x50050] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0x2085400000025800000051505ca6e9199d0d] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨668,6,samples,cols,[[],[115,148],[50,116],[50,66,146,114],[66,151],[66,147,114,50],[114,50,67,148],[114,147],[146,67],[146,115,66,67]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 1 := bandCut 5 false (by decide +kernel)
theorem band6 : CutRow book 6 0 1 := row6_0
set_option maxRecDepth 16000 in
theorem row5_0 : CutRow book 5 0 2 := bandCut 6 false (by decide +kernel)
theorem band5 : CutRow book 5 0 2 := row5_0
set_option maxRecDepth 16000 in
theorem row4_0 : CutRow book 4 0 1 := bandCut 5 false (by decide +kernel)
theorem band4 : CutRow book 4 0 1 := row4_0
theorem checked : mixedTables book 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band4
  · exact band5
  · exact band6
end B668_7
theorem h668_7 : Face true 668 7 :=
  mixedLower (g:=B668_7.book) (i:=0) (hints:=275414983424)
    (before_sound B668_7.entries B668_7.prior) B668_7.geometry B668_7.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h679_7 : Face true 679 7 := carry_of (swaps:=[145,129,49,99,48,114,81,64]) (by decide +kernel) h190_7
theorem h685_7 : Face true 685 7 := carry_of (swaps:=[145,129,97,83,114,16,64]) (by decide +kernel) h190_7
theorem h689_7 : Face true 689 7 := carry_of (swaps:=[116,83,16,32]) (by decide +kernel) h668_7
theorem h561_4 : Face true 561 4 := carry_of (swaps:=[146,130,114,32,48,99,82,64]) (by decide +kernel) h29_4
theorem h646_4 : Face true 646 4 := carry_of (swaps:=[146,130,115,98,83,66,16]) (by decide +kernel) h29_4
theorem h663_7 : Face true 663 7 := carry_of (swaps:=[147,131,116,66,99,32,80,16]) (by decide +kernel) h63_7
theorem h694_7 : Face true 694 7 := carry_of (swaps:=[151,114,130,81,98,50,65]) (by decide +kernel) h190_7

namespace B695_10
def entries : List (Nat × Nat) := [(165,4),(166,4),(183,7),(561,4),(646,4),(660,4),(663,7),(679,7),(689,7),(694,7)]
theorem prior : Known true entries := (consFace h165_4 (consFace h166_4 (consFace h183_7 (consFace h561_4 (consFace h646_4 (consFace h660_4 (consFace h663_7 (consFace h679_7 (consFace h689_7 (consFace h694_7 (known_down baseKnown)))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 146 0x47fc7c440000001fffe0030000ffff80c03c,padColumn 146 0x3fc3c001810106cb4a0330000ed6500c014),(padColumn 146 0xbc7ffcbc00000000001ffc18300181ffc003,padColumn 146 0x3c3ffc3c60606080606d5c18300181da8001),(padColumn 146 0x3cbc487c800000fe0001ff000cfc6067fc0c3,padColumn 146 0x3c3c003c080818d218192a000ce8606254042),(padColumn 146 0x0,padColumn 146 0x0),(padColumn 146 0x1108bcbfc000ff0001fe00067f3007f83030c,padColumn 146 0x3c3fd030aa3020b40c066a3001a830108),(padColumn 146 0x3fd1113fc07f0001fe00000fb043f880c0c30,padColumn 146 0x3fc0003fe05a60413420300d30412880c0420),(padColumn 146 0x0,padColumn 146 0x0),(padColumn 146 0x22223fd13fff00fe000000ffc0fc830103cc0,padColumn 146 0x3fc012a5802c40c040a2c014830101880)] i else tableBits #[(padColumn 146 0x0,padColumn 146 0x0),(padColumn 146 0x3fffe2223f80ff00000000f87f83040603300,padColumn 146 0x3fffc0002d405581810180581583040602200)] i))
def cols : List ColumnInfo := [(1,0,694,0,7),(16,0,679,0,7),(32,0,663,0,7),(512,0,183,0,7),(4,2,689,0,7),(6,0,689,0,7),(35,0,660,0,4),(48,1,646,0,4),(134,0,561,0,4),(513,16,166,0,4),(529,0,166,0,4),(530,0,165,0,4)]
def data9 : Nat → Nat := (fun i => tableWord #[0x7f,0x40123506] i)
def data8 : Nat → Nat := (fun i => (if i<8 then tableWord #[0xff460,0xa552a04,0xff480,0x50e603,0xff4a0,0x282582a706,0xff4c0,0x140d4ea05] i else tableWord #[0xff4a4,0x282424f506,0xff4c4,0x5043454e907,0xffca0,0x242ace807,0xffca4,0x810a93a84808] i))
def data7 : Nat → Nat := bookData 2 3 3 (fun i => ((fun i => tableWord #[0xca44c44a4ca04c04a0] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x1efdfdfeef6f] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => tableWord #[0x139954e64b3954ce64d39934c48e3159ce64138cace3273900] i) (i/16) >>> (18*(i%16))) % 262144) (fun i => (if i<8 then tableWord #[0xd3502,0xd3502,0x801,0x0,0x84a02,0xb01,0x0,0x0] i else tableWord #[0x3401,0x0,0x0] i))
def levels : Nat → Packing
  | 7 => (11,2,4,0,0,0,0,data7)
  | 8 => (8,1,4,0,0,0,0,data8)
  | 9 => (1,0,4,0,0,0,0,data9)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun h => smallSlot h 6 20 4 1 (fun i => ((fun i => tableWord #[0x18100] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0x2529a38400817588000007008a000016,0x2286008b] i) (i/16) >>> (8*(i%16))) % 256)
  | 9 => fun h => smallSlot h 7 22 4 1 (fun i => ((fun i => tableWord #[0x86020403] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0xc16288c35300000038d4a5b207a655d7,0x400000000] i) (i/16) >>> (8*(i%16))) % 256)
  | _ => fun _ => none
def book : Forest := ⟨695,9,samples,cols,[[],[64,149]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 7 false (by decide +kernel)
theorem band9 : CutRow book 9 0 1 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 8 := bandCut 8 true (by decide +kernel)
theorem band8 : CutRow book 8 0 8 := row8_0
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 3 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_3 : CutRow book 7 3 8 := bandCut 8 true (by decide +kernel)
theorem combine7_0_11 : CutRow book 7 0 11 := @joinRow book 7 0 3 8 row7_0 row7_3
theorem band7 : CutRow book 7 0 11 := combine7_0_11
theorem checked : mixedTables book 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band7
  · exact band8
  · exact band9
end B695_10
theorem h695_10 : Face true 695 10 :=
  mixedLower (g:=B695_10.book) (i:=0) (hints:=275414778148)
    (before_sound B695_10.entries B695_10.prior) B695_10.geometry B695_10.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h573_7 : Face true 573 7 := carry_of (swaps:=[145,129,66,16,112]) (by decide +kernel) h190_7
theorem h673_4 : Face true 673 4 := carry_of (swaps:=[146,50,131,66,116,99,82]) (by decide +kernel) h29_4
theorem h688_4 : Face true 688 4 := carry_of (swaps:=[148,132,66,64,115,98,80,16]) (by decide +kernel) h29_4

namespace B701_11
def entries : List (Nat × Nat) := [(29,4),(57,4),(156,4),(165,4),(172,4),(177,4),(189,8),(540,4),(561,4),(573,7),(652,4),(657,4),(660,4),(664,4),(668,7),(673,4),(685,7),(688,4),(689,7)]
theorem prior : Known true entries := (consFace h29_4 (consFace h57_4 (consFace h156_4 (consFace h165_4 (consFace h172_4 (consFace h177_4 (consFace h189_8 (consFace h540_4 (consFace h561_4 (consFace h573_7 (consFace h652_4 (consFace h657_4 (consFace h660_4 (consFace h664_4 (consFace h668_7 (consFace h673_4 (consFace h685_7 (consFace h688_4 (consFace h689_7 (known_down baseKnown))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 145 0x23ffe20000001fffc00018001fffc10300f0,padColumn 145 0x1ffe00c08106cb5408198001dac81030050),(padColumn 145 0x0,padColumn 145 0x0),(padColumn 145 0x5e3e3e00000fe000007f8007f830c0ff0303,padColumn 145 0x1e1e1e10106d2060c1268007d030c0960101),(padColumn 145 0x1e5e3e400000000003fffe0c000c03fff000f,padColumn 145 0x1e1e1e060608081812ad960c000c035690006),(padColumn 145 0x88445e0007f0001fff80033e600fff040c3c,padColumn 145 0x1e818523020a9502033460034a040428),(padColumn 145 0x1fe889e03f8001fe0000007d887f1061830c0,padColumn 145 0x1fe001f02b3041342060c0698825106181080),(padColumn 145 0x0,padColumn 145 0x0),(padColumn 145 0x11111e9fff80fe00000007fe1f9061820f300,padColumn 145 0x1e0a54c02c40c18105160290618206200)] i else tableBits #[(padColumn 145 0x0,padColumn 145 0x0),(padColumn 145 0x1ffff11fc07f0000000007c3f060820c0cc00,padColumn 145 0x1fffe015a02d8181020602c0b060820c08800)] i))
def cols : List ColumnInfo := [(512,0,189,0,8),(16,0,685,0,7),(128,0,573,0,7),(12,0,689,0,7),(33,0,668,0,7),(13,0,688,0,4),(20,8,673,0,4),(28,0,673,0,4),(37,0,664,0,4),(41,0,660,0,4),(44,0,657,0,4),(48,1,652,0,4),(49,0,652,0,4),(129,32,540,0,4),(136,4,561,0,4),(140,0,561,0,4),(161,0,540,0,4),(524,0,177,0,4),(529,0,172,0,4),(536,0,165,0,4),(545,0,156,0,4),(644,0,57,0,4),(672,0,29,0,4)]
def data10 : Nat → Nat := (fun i => tableWord #[0x7f,0x6403] i)
def data9 : Nat → Nat := (fun i => (if i<16 then (if i<8 then tableWord #[0xff0a3,0x49604310e18c4c20b,0xff420,0x20108b80e0c408,0xff440,0x108980b0c407,0xff460,0x422e348407] i else tableWord #[0xff4a0,0x10a040b8c407,0xff4c0,0x108b02348407,0xff4a3,0x200428e406,0xff4c3,0x10928c091307] i) else tableWord #[0xff8a3,0x31062c24e39010a,0xff8c3,0x218b8e400107,0xffc60,0x864e304407,0xffca0,0x138b56310208] i))
def data8 : Nat → Nat := bookData 2 4 4 (fun i => ((fun i => tableWord #[0xca0c608c34c34c04604404200a38a34a34a0] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x7ffefbff7f7ffd7febdf67f6f] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => tableWord #[0x4e6454e5454e3454a05546055ce644ce3444e6444e3444a0544e6434e043ca3324e122ce611ce400,0xca360ce240ce1404e6404a3604c050ce646ce546ce246ce1464e6464e5464c056ce645ce545ce345,0xce641ce0418c3914e6414c3910e681ce547ce347ce247ce1478c5874c3874c187ce640ce470ce340,0x4e24a4e14a4a05a8c5894e5494e1494e0494e6424e5424c3924e1424e042ce548ce148ce048ce681,0x4a1a6461a6ca3a58c5a54c5a54c3a54a3a54c3a44a3a44e64b4e34b4a36b4e24b4e14b4e64a4e54a,0x4c3a04a3a04c2a04a2a04c1a0461a0ca3a6ca2a6ca1a68c5a64c5a64a3a64c2a64a2a6462a64c1a6,0xca1aa8c5aa4c5aa4c1aa4c5a28e5a84e5a84e1a8ce6a1ce0a14e6a14c3a14e0a1ca3a74a3a74c5a0,0x4c3ab4c2ab] i) (i/16) >>> (20*(i%16))) % 1048576) (fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0xc18c59004,0x830b1e404,0x8b0c3071306,0x2654581043439608,0x59202,0x245499604,0xc70b03,0x65858e04] i else tableWord #[0x2058e03,0x58802,0x1870803,0x1a18b03,0x2c1218b04,0x18a8b03,0x4125a18b05,0x10e2012c8030b07] i) else (if i<24 then tableWord #[0x18048b03,0x3830904,0xa3830904,0x459203,0x30e251088b07,0x90b02,0x3071203,0x231a5890605] i else tableWord #[0x30b1c4461206,0x61c3079205,0xe084100b05,0xc4220b04,0x401030e284480b08,0x464c80e04,0x5831003,0x1059003] i)) else (if i<48 then (if i<40 then tableWord #[0x859003,0x1080b03,0x10061c4459006,0x39028551c406,0x84059204,0x42d04a1005,0x64871404,0x5831403] i else tableWord #[0x18c59203,0x81858e204839408,0x142a4cb2005,0x11a4c72005,0x401858d1c5890a08,0x843470616580a008,0x64838a8b05,0x20c2c79030e16345200a] i) else (if i<56 then tableWord #[0x20c7920c205,0xe263c59205,0xd2c4871305,0xd1c4841305,0x59202,0x38e02,0x1a4871304,0x41000c3458e07] i else tableWord #[0x68e2a5891306,0x59202,0xc38e03,0x110d1c185c006,0x20a202,0x41070b04,0xc38e03,0x11031303] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x3834404,0xe2b1099205,0x71502,0x30f02,0xc4870b04,0x20c5470b05,0x6122ca9605,0x402c40e04] i else tableWord #[0x2071303,0x20021848b05,0x48b02,0x2459603,0xc8058904,0x1848b03,0x8c70703,0x71502] i) else (if i<88 then tableWord #[0x71502,0x31302,0x8c78603,0x98602,0x459203,0x2c91603,0x2c91603,0x462c91604] i else tableWord #[0x462c91604,0x8c59203,0x23171038e05,0x885459004,0x471079004,0x882c81304,0x411059004,0x11080b03] i)) else (if i<112 then (if i<104 then tableWord #[0x2c81603,0xa0b02,0x4640a0b04,0x20164092405,0x4004b1304,0x8099603,0x120b02,0x4cb2003] i else tableWord #[0x5439303,0x99602,0x10491303,0x4ca9603,0x881c71504,0x11099603,0x41164091605,0x38b1c4091506] i) else tableWord #[0x11031303,0xb1202] i))))
def data7 : Nat → Nat := bookData 3 7 5 (fun i => ((fun i => tableWord #[0x4a04204e5c604e1c604a0c608c58c34e18c38c34a30e64a3ce14c08c54c04e64a04e5460ce54404e64404e54404e3420,0xca3460ce24608c54604a34604a24604c14604614604c0460ce64408c54404e34404a34404a0440460440ce64204a3420,0xca34c0ce24c04a34c04c14c0ce64a0ce44a0ce24a0ce14a04c34a04a34a04c24a04a24a04c14a04614a04c04a0ce6460,0xca1c608c5c604c5c604e08c34e58a34c58a34c38a34e18a3ce04c38e54c34e14c3ce64a3ce04a34e64a34c34a34e04a3,0x4c3ca04a3ca0] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => ((fun i => tableWord #[0xcff77feafe9febfdfaf6adf97c7e6f8fe779f67b,0xdf6f7bbfb7d7f9fb7f6ff5efdbefbe] i) (i/16) >>> (10*(i%16))) % 1024) (fun i => ((fun i => tableWord #[0xd0618ed0200dd0340c50338bd0200a8c5309907188502007ce5286d04205d06184d04204506183d03102d01081d02000,0x5035834e6796d05582d06581d06595d05595d06514ce3714ce64934a2693ce6492d05612503591d06580d06510ce648f,0xd026214c18215055a050289f50559ece679dd06584d0651cd0191bce679ad028998c58184c1818505597503597506583,0x5035a8ce4a27d06b26d06526ce6ba6ce4a264c39a6106b26ce67a5ce4a25d01924d05aa3ce4a234e67a3d028a24a39a2,0xd04cb00e67b09075085028af8c57ae5055ae503506501506d0652d8c5b2d4c3c2dd0352c5035ab4c5a2a5065a95065a8,0x5055b7503d36500636d028b5d007b45037b45007b4ce67b35065b30e67b3ce6c09d067b2ce6c31ce67b1d06530ce67b0,0x5075be4e5bbed0678ed0658e10678e5075bd4e5bbd4e648c4e248c8c57bcd065bb1067bb5075ba4e67ba4e57394c5db8,0x5075c14e3741d06b404e6bc04c39c0106b405075bf] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => (if i<64 then (if i<32 then (if i<16 then (if i<8 then tableWord #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101402] i else tableWord #[0xe01,0x0,0x131602,0x0,0x1601,0xb01,0xe01,0x0] i) else (if i<24 then tableWord #[0x0,0x0,0x0,0x0,0x0,0x0,0x43841603,0x901] i else tableWord #[0xa01602,0x0,0x0,0x0,0x0,0x901,0x410902,0x1601] i)) else (if i<48 then (if i<40 then tableWord #[0x0,0x0,0x0,0x1501,0x1601,0x0,0x1501,0x0] i else tableWord #[0x0,0x0,0xb01,0x1601,0x0,0xb01,0x841002,0x1401] i) else (if i<56 then tableWord #[0xe01,0xc401,0x1501,0x0,0xc401,0xc401,0x0,0x1301] i else tableWord #[0x1401,0xb01,0xa001,0xb01,0xc401,0x8101,0x0,0x1601] i))) else (if i<96 then (if i<80 then (if i<72 then tableWord #[0x0,0x0,0x0,0xb01,0x0,0xb1402,0x1401,0x1401] i else tableWord #[0x0,0x0,0x1601,0x0,0x0,0x1601,0x1601,0x0] i) else (if i<88 then tableWord #[0xa41402,0x2001,0x1301,0x8201,0x131602,0x421602,0x0,0x0] i else tableWord #[0x0,0x6401,0x4201,0x0,0x0,0x0,0x4101,0x1601] i)) else (if i<112 then (if i<104 then tableWord #[0x0,0x1601,0x1601,0x0,0x0,0x0,0x0,0x8401] i else tableWord #[0x8401,0x1601,0x0,0x0,0x0,0x1601,0x1601,0x4101] i) else tableWord #[0x1601,0x0,0x0,0x0,0x0,0x1601,0x0] i))))
def data6 : Nat → Nat := bookData 4 4 3 (fun i => ((fun i => tableWord #[0x507ca1c605074c5c605074c58a3500ce64a3d044e04a30e64e04a3503ce14a0ce44a34a0d014a24a0d024614a0505ce2460ce68c54604e68c5440] i) (i/16) >>> (36*(i%16))) % 68719476736) (fun i => ((fun i => tableWord #[0x297e2fcdb9ae1fd1f] i) (i/16) >>> (11*(i%16))) % 2048) (fun i => ((fun i => tableWord #[0x3498e6931bd2635a496739a4073489282fa4c5b41a2e7234ce447a4c494940e9280] i) (i/16) >>> (19*(i%16))) % 524288) (fun i => (if i<8 then tableWord #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0] i else tableWord #[0x0,0x0,0x0,0x0,0x0,0x0] i))
def levels : Nat → Packing
  | 6 => (14,4,5,0,0,0,0,data6)
  | 7 => (119,3,5,0,0,0,0,data7)
  | 8 => (114,2,5,0,0,0,0,data8)
  | 9 => (12,1,5,0,0,0,0,data9)
  | 10 => (1,0,5,0,0,0,0,data10)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 7 => fun h => smallSlot h 7 22 4 2 (fun i => ((fun i => tableWord #[0x100210000] i) (i/16) >>> (5*(i%16))) % 32) (fun i => ((fun i => tableWord #[0x29704000038709e40000000e08021985,0x1c4de10280ec6] i) (i/16) >>> (9*(i%16))) % 512)
  | 8 => fun h => smallSlot h 98 313 7 2 (fun i => ((fun i => tableWord #[0x180000000000e00008000001000180600,0x80404000000c0802000000000000000000,0x100000010080004000000c02000280c0600,0x81c0000018000000050000801000000009,0x1000040c09000000002028000401,0x18000402000080205008040000000000201,0x0] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x443e32c04d5e5cfa3bfd185bc62000000000f0281e000000,0x2db000e72000d3e9366c88d4294339ac9a47a21000452460,0x812c69006a4c875e496d921801b8298a6c56cd7,0xe6885c026c310d6000814a7664dd61cb2000e2a,0x26a00063f0006dc000a5a0000000000001ad000ab3000000,0xc1fc36c0d663c74e0146c63a348227416ec7e0c4ca,0xa655c8000bdae25000a1a00000000000002c000000000728,0xf670000000006be01dc35264845ed3a6fcb9a4644e000000] i else tableWord #[0x2d83c2a9359a8d00067140b957000000000e6e33da6ba13,0xa5e3d96bdf4fa670009d705400000025000afdce66e28,0xbf5d5ae051f200000020fdc70003cace7000441000951000,0x531be00062e4392e21187b9238b732402d10000006338cf,0x45d000000000a150001290000a40000000000003a9cb5e3e,0xa42c020000da0000590000004afe5f65700007722ba44000,0xa51e7304fa2f00080733aa340030001bd000000000d5c000,0xc48000000000f160000000000000005e78c5a19000000] i) else tableWord #[0xa10000c30655000e9a000cf50002f2f4600e000,0xc24ee397200044b00000000000000000047000000000086d,0xd12000e08a1c1cd00000000043d000a1763740937504a891,0xa20a22e11000c58a61000a23] i)) (i/16) >>> (12*(i%16))) % 4096)
  | 9 => fun h => smallSlot h 122 422 7 2 (fun i => ((fun i => tableWord #[0x40000000000000000000001000000000,0x18000602018040000008000000,0x40200000000200000040001,0x2000000201000000000000000001,0x80002000040000018000001000080000,0x8000400010000200000001400,0x8000600000040200010000600008000001,0x603000080201038000602] i) (i/16) >>> (9*(i%16))) % 512) (fun i => ((fun i => (if i<16 then (if i<8 then tableWord #[0x26245b4050000000003d7d36000000000559000000d15b2f,0xa1c000903000221a55000000000849000c3b0004cf016,0xe4e000000b0d0007e3000762000000e3113a636,0x266def8270e2000835ee481b41000000064d000560000,0x22439d73325d0023df0000000004dae08,0x954d14dc63a0007c50006ac87008784a000e71,0xc50000c4f62c2c942d226,0xe0dccc372000000000000b16e1d4c5000000000000] i else tableWord #[0xa2b000014000000000000a6e00000000000049d000c465a0,0xa53000c4100080f00000000000000043835e000000000,0x8ae000000f48ee7000e12cee7e2000023260011818,0xc174d54df1d600000000020921a00000000000030ce06000,0x2220af000c6dbe400000000043faceb05c47000613a19,0x1714a664800000000086460b00000060c000b53,0xd950007850006d7000000859000000042000000000204c6f,0xa152456a035f000c0300043dc61bee] i) else (if i<24 then tableWord #[0xe3c000000000000a67000aed000169a33fda59cc07000000,0x26a45eb54000000232000000000843258000000335000,0xc2f0000008ece2a43e3e1252000000000000c6cb32000,0xe3400000000000000000000006b00084be5c000000,0xd8000000000000000ba6456000839c1e000aca269,0x62ea6820e000000b1c000265,0x20a00000000000000000000005f000000000ee3000000425,0xb55000e1f000a72c300009250000007e7c5469cb3b000ccd] i else tableWord #[0xa28000663000437285651f4924c00000096448a767000fd5,0x4d64014e1945cefe5a9af044e88000000000840a29000000,0x657ce5e20] i))) (i/16) >>> (12*(i%16))) % 4096)
  | 10 => fun h => smallSlot h 20 69 4 2 (fun i => ((fun i => tableWord #[0xa0c001001828004000000200000,0x14001] i) (i/16) >>> (7*(i%16))) % 128) (fun i => ((fun i => tableWord #[0xe3a5a2a488dbb0344ca52ec0034,0x19800000021000002a0000000208027800,0x20c4a35a164f30b6000000000000000000,0xe5f714800000000a00000000000559640049,0x4600002c400] i) (i/16) >>> (9*(i%16))) % 512)
  | _ => fun _ => none
def book : Forest := ⟨701,10,samples,cols,[[],[32,83,116],[48,82],[80,50,116]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 7 false (by decide +kernel)
theorem band10 : CutRow book 10 0 1 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 12 := bandCut 8 true (by decide +kernel)
theorem band9 : CutRow book 9 0 12 := row9_0
set_option maxRecDepth 16000 in
theorem row8_0 : CutRow book 8 0 4 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_4 : CutRow book 8 4 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_16 : CutRow book 8 16 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_28 : CutRow book 8 28 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_40 : CutRow book 8 40 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_52 : CutRow book 8 52 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_64 : CutRow book 8 64 7 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_71 : CutRow book 8 71 12 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_83 : CutRow book 8 83 12 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_95 : CutRow book 8 95 12 := bandCut 9 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row8_107 : CutRow book 8 107 7 := bandCut 9 false (by decide +kernel)
theorem combine8_0_16 : CutRow book 8 0 16 := @joinRow book 8 0 4 12 row8_0 row8_4
theorem combine8_16_24 : CutRow book 8 16 24 := @joinRow book 8 16 12 12 row8_16 row8_28
theorem combine8_40_24 : CutRow book 8 40 24 := @joinRow book 8 40 12 12 row8_40 row8_52
theorem combine8_64_19 : CutRow book 8 64 19 := @joinRow book 8 64 7 12 row8_64 row8_71
theorem combine8_83_24 : CutRow book 8 83 24 := @joinRow book 8 83 12 12 row8_83 row8_95
theorem combine8_0_40 : CutRow book 8 0 40 := @joinRow book 8 0 16 24 combine8_0_16 combine8_16_24
theorem combine8_40_43 : CutRow book 8 40 43 := @joinRow book 8 40 24 19 combine8_40_24 combine8_64_19
theorem combine8_83_31 : CutRow book 8 83 31 := @joinRow book 8 83 24 7 combine8_83_24 row8_107
theorem combine8_0_83 : CutRow book 8 0 83 := @joinRow book 8 0 40 43 combine8_0_40 combine8_40_43
theorem combine8_0_114 : CutRow book 8 0 114 := @joinRow book 8 0 83 31 combine8_0_83 combine8_83_31
theorem band8 : CutRow book 8 0 114 := combine8_0_114
set_option maxRecDepth 16000 in
theorem row7_0 : CutRow book 7 0 12 := bandCut 7 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_12 : CutRow book 7 12 4 := bandCut 7 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_16 : CutRow book 7 16 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_28 : CutRow book 7 28 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_40 : CutRow book 7 40 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_52 : CutRow book 7 52 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_64 : CutRow book 7 64 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_76 : CutRow book 7 76 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_88 : CutRow book 7 88 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_100 : CutRow book 7 100 12 := bandCut 8 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row7_112 : CutRow book 7 112 7 := bandCut 8 false (by decide +kernel)
theorem combine7_0_16 : CutRow book 7 0 16 := @joinRow book 7 0 12 4 row7_0 row7_12
theorem combine7_16_24 : CutRow book 7 16 24 := @joinRow book 7 16 12 12 row7_16 row7_28
theorem combine7_40_24 : CutRow book 7 40 24 := @joinRow book 7 40 12 12 row7_40 row7_52
theorem combine7_64_24 : CutRow book 7 64 24 := @joinRow book 7 64 12 12 row7_64 row7_76
theorem combine7_88_24 : CutRow book 7 88 24 := @joinRow book 7 88 12 12 row7_88 row7_100
theorem combine7_0_40 : CutRow book 7 0 40 := @joinRow book 7 0 16 24 combine7_0_16 combine7_16_24
theorem combine7_40_48 : CutRow book 7 40 48 := @joinRow book 7 40 24 24 combine7_40_24 combine7_64_24
theorem combine7_88_31 : CutRow book 7 88 31 := @joinRow book 7 88 24 7 combine7_88_24 row7_112
theorem combine7_0_88 : CutRow book 7 0 88 := @joinRow book 7 0 40 48 combine7_0_40 combine7_40_48
theorem combine7_0_119 : CutRow book 7 0 119 := @joinRow book 7 0 88 31 combine7_0_88 combine7_88_31
theorem band7 : CutRow book 7 0 119 := combine7_0_119
set_option maxRecDepth 16000 in
theorem row6_0 : CutRow book 6 0 12 := bandCut 7 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row6_12 : CutRow book 6 12 2 := bandCut 7 false (by decide +kernel)
theorem combine6_0_14 : CutRow book 6 0 14 := @joinRow book 6 0 12 2 row6_0 row6_12
theorem band6 : CutRow book 6 0 14 := combine6_0_14
theorem checked : mixedTables book 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band6
  · exact band7
  · exact band8
  · exact band9
  · exact band10
end B701_11
theorem h701_11 : Face true 701 11 :=
  mixedLower (g:=B701_11.book) (i:=0) (hints:=275414786820)
    (before_sound B701_11.entries B701_11.prior) B701_11.geometry B701_11.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem h710_7 : Face true 710 7 := carry_of (swaps:=[116,100,84,49,33]) (by decide +kernel) h668_7
theorem h723_7 : Face true 723 7 := carry_of (swaps:=[146,33,114,129,50,99,32,81,64]) (by decide +kernel) h190_7
theorem h727_10 : Face true 727 10 := carry_of (swaps:=[151,101,66,16]) (by decide +kernel) h695_10
theorem h730_7 : Face true 730 7 := carry_of (swaps:=[146,50,131,113,83,98,65]) (by decide +kernel) h190_7
theorem h734_11 : Face true 734 11 := carry_of (swaps:=[151,101,66,16]) (by decide +kernel) h701_11
theorem h743_10 : Face true 743 10 := carry_of (swaps:=[100,82,16]) (by decide +kernel) h695_10
theorem h582_4 : Face true 582 4 := carry_of (swaps:=[146,130,50,115,98,83,32,64,16]) (by decide +kernel) h29_4
theorem h627_7 : Face true 627 7 := carry_of (swaps:=[147,131,115,98]) (by decide +kernel) h63_7
theorem h633_7 : Face true 633 7 := carry_of (swaps:=[151,135,84,66,98,16,48]) (by decide +kernel) h190_7
theorem h639_11 : Face true 639 11 := carry_of (swaps:=[151,135,101,66,16]) (by decide +kernel) h255_11
theorem h706_4 : Face true 706 4 := carry_of (swaps:=[147,50,67,130,116,99,82,16]) (by decide +kernel) h29_4
theorem h739_7 : Face true 739 7 := carry_of (swaps:=[148,32,132,115,98,80,16]) (by decide +kernel) h63_7
theorem h755_10 : Face true 755 10 := carry_of (swaps:=[151,84,98,50]) (by decide +kernel) h695_10
theorem h594_4 : Face true 594 4 := carry_of (swaps:=[147,131,67,116,66,99,82,16]) (by decide +kernel) h29_4

namespace B759_12
def entries : List (Nat × Nat) := [(165,4),(166,4),(177,4),(183,7),(198,4),(231,7),(582,4),(593,4),(594,4),(599,7),(627,7),(689,7),(695,10),(710,7),(727,10),(743,10),(755,10)]
theorem prior : Known true entries := (consFace h165_4 (consFace h166_4 (consFace h177_4 (consFace h183_7 (consFace h198_4 (consFace h231_7 (consFace h582_4 (consFace h593_4 (consFace h594_4 (consFace h599_7 (consFace h627_7 (consFace h689_7 (consFace h695_10 (consFace h710_7 (consFace h727_10 (consFace h743_10 (consFace h755_10 (known_down baseKnown))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 244 0x87ff0fc3f1111f8840000000000000fffff0003180000301fffff00c003c,padColumn 244 0x3ff07c1f0000f8000606010080c03696a500c3180000301dab4a00c0014),(padColumn 244 0x17c3f107ff2222097c00000000003ff00000ffc06030300ff80c03ffc00c3,padColumn 244 0x7c1f003ff0000007c08180603012a900c0365406030300d500c03aa80041),(padColumn 244 0xf8be120841f0ffff88000000007fc0000000ffcc0000cff000300cffc0303,padColumn 244 0xf83e000000f0ffff803020080c5a4040300c9a8c0000cda000300c5540102),(padColumn 244 0x0,padColumn 244 0x0),(padColumn 244 0x21042f93e2ff0f17fc000000ff80000003ff000000cff0c06003ff0300c0c,padColumn 244 0xf83e0ff0f07fc404030d5060180415a030000cea0c06000b50300408),(padColumn 244 0xffc8442084fff027fc0001ff0000000ffc00003007f3010187fc100c03030,padColumn 244 0xffc0000000fff007fd80815a3008060968100c3006a301018254100c01020),(padColumn 244 0x42108ffd08fffff813fe000000003ff00000003f8304060ff8c06010300c0,padColumn 244 0xffc00fffff802d300c0403015618060102a83040602a8c0601010080),(padColumn 244 0x84210fffff4444422001ffff007fc00000000000fff80ff6010180200f300,padColumn 244 0xfffff00000002014aa58025980201802000d15802560101802006200)] i else tableBits #[(padColumn 244 0x0,padColumn 244 0x0),(padColumn 244 0xfffff8421088888443fffe00ff8000000000003ffc0ff808060200c03cc00,padColumn 244 0xfffff00000000000012cb5002ac0200c0200c0152c015808060200c028800)] i))
def cols : List ColumnInfo := [(4,0,755,0,10),(16,0,743,0,10),(32,0,727,0,10),(64,0,695,0,10),(132,0,627,0,7),(160,0,599,0,7),(528,0,231,0,7),(576,0,183,0,7),(48,1,710,0,7),(49,0,710,0,7),(68,2,689,0,7),(70,0,689,0,7),(145,32,582,0,4),(162,4,593,0,4),(165,0,594,0,4),(177,0,582,0,4),(560,1,198,0,4),(577,16,166,0,4),(580,2,177,0,4),(594,0,165,0,4)]
def data11 : Nat → Nat := (fun i => tableWord #[0xff,0x89001a92b08] i)
def data10 : Nat → Nat := (fun i => tableWord #[0x1ff0e6,0x518a22a2d32443c70b,0x1ff4e6,0xaa38288a1147a6b0a,0x1ff8e6,0x263a84a0e1e1ac50a] i)
def data9 : Nat → Nat := (fun i => tableWord #[0x2fb5020e6,0x11241471305,0x33fce68e6,0x8920a1c71306,0x2ff5078e6,0x811243068706] i)
def levels : Nat → Packing
  | 9 => (3,2,5,0,0,0,0,data9)
  | 10 => (3,1,5,0,0,0,0,data10)
  | 11 => (1,0,5,0,0,0,0,data11)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun h => smallSlot h 3 11 2 2 (fun i => ((fun i => tableWord #[0x0] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0x546ae9e6f4000] i) (i/16) >>> (7*(i%16))) % 128)
  | 11 => fun v => (if v=8846553226619420952 then some (2,0) else (if v=9083563835880407257 then some (1,0) else (if v=9967659315218139993 then some (2,1) else (if v=10268309250932263832 then some (0,0) else none))))
  | _ => fun _ => none
def book : Forest := ⟨759,11,samples,cols,[[],[98,84,151],[16,66,101,151],[16,82,100]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 8 false (by decide +kernel)
theorem band11 : CutRow book 11 0 1 := row11_0
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 3 := bandCut 9 false (by decide +kernel)
theorem band10 : CutRow book 10 0 3 := row10_0
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 2 := bandCut 8 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_2 : CutRow book 9 2 1 := bandCut 9 false (by decide +kernel)
theorem combine9_0_3 : CutRow book 9 0 3 := @joinRow book 9 0 2 1 row9_0 row9_2
theorem band9 : CutRow book 9 0 3 := combine9_0_3
theorem checked : mixedTables book 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
end B759_12
theorem h759_12 : Face true 759 12 :=
  mixedLower (g:=B759_12.book) (i:=0) (hints:=275431555364)
    (before_sound B759_12.entries B759_12.prior) B759_12.geometry B759_12.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

namespace B767_14
def entries : List (Nat × Nat) := [(6,1),(14,2),(29,4),(30,4),(57,4),(63,7),(78,4),(95,7),(166,4),(177,4),(183,7),(189,8),(198,4),(231,7),(255,11),(561,4),(582,4),(593,4),(599,7),(606,8),(627,7),(633,7),(639,11),(668,7),(673,4),(689,7),(701,11),(706,4),(710,7),(734,11),(739,7),(743,10),(755,10),(759,12)]
theorem prior : Known true entries := (consFace h6_1 (consFace h14_2 (consFace h29_4 (consFace h30_4 (consFace h57_4 (consFace h63_7 (consFace h78_4 (consFace h95_7 (consFace h166_4 (consFace h177_4 (consFace h183_7 (consFace h189_8 (consFace h198_4 (consFace h231_7 (consFace h255_11 (consFace h561_4 (consFace h582_4 (consFace h593_4 (consFace h599_7 (consFace h606_8 (consFace h627_7 (consFace h633_7 (consFace h639_11 (consFace h668_7 (consFace h673_4 (consFace h689_7 (consFace h701_11 (consFace h706_4 (consFace h710_7 (consFace h734_11 (consFace h739_7 (consFace h743_10 (consFace h755_10 (consFace h759_12 (known_down baseKnown)))))))))))))))))))))))))))))))))))
def samples : Nat → Bits × Bits := (fun i => (if i<8 then tableBits #[(padColumn 320 0xf07fc210421ffe1043e0000000000000001fffffc00000000060c00000600fffffe0080600c003c0,padColumn 320 0xf07fc000000ffe0001e00c0300200806006d2b55400803006060c00000600ed56940080600c00140),(padColumn 320 0xff87c4208420822fffe0000000000001ffe00000000000ffe0030060601ffc0180603001ffc00c03,padColumn 320 0xff87c0000000000fffe0100c00c0300955200600c0300465a0030060601aa8018060300155800401),(padColumn 320 0x10887e013ff17ff084200000000007fe000000000007ffffe18000019fe00006018007ffffc0300f,padColumn 320 0x3e003ff07ff0000060100100c5a2008018030042599a418000019b400006018004acaa401006),(padColumn 320 0xfff8084fc84f84413fe0000000000000000000003fffff00060c018000003018001ffffe0100003c,padColumn 320 0xfff8000fc00f80003fe1806006010010030060042a9da600860c018000003018001aab5201000018),(padColumn 320 0x2110bff201f209ffc8400000001ff800000001fffff800000000061fe180c0007ffff8080600c0f0,padColumn 320 0x3ff001f001ffc0020080181a50600c0080aa956008030000061d4180c00016a55008060040a0),(padColumn 320 0x42213ffffe0411fffe800000ffe00000001ffe000000000018003fe6020303ff8200c03018030300,padColumn 320 0x3ffffe0001fffe0c0100ab4600803012d4080180300c180035460203012a8200c03018010200),(padColumn 320 0x84023ffffffffe02111ffc0000000001ffe00000000000001ff018080c1ffc600c0300c020300c00,padColumn 320 0x3ffffffffe000016a60060080300aac300300600c010155018080c0554600c0300c020100800),(padColumn 320 0xffffd08410802084200003ffffe007fe0000000000000000001ffff01fec0080300c0100400f3000,padColumn 320 0xffffc00000000000001002a554b0025cc00400c018010020001a8ab004ac0080300c010040062000)] i else tableBits #[(padColumn 320 0x0,padColumn 320 0x0),(padColumn 320 0x844210821084108001fffff001ff80000000000000000001fffe01ff010030040100601803cc000,padColumn 320 0x9595a8005ac0100180100200600c00aa56002b01003004010060180288000)] i))
def cols : List ColumnInfo := [(8,0,759,0,12),(128,0,639,0,11),(512,0,255,0,11),(33,0,734,0,11),(66,0,701,0,11),(12,0,755,0,10),(24,0,743,0,10),(129,32,606,0,8),(514,64,189,0,8),(578,0,189,0,8),(20,8,739,0,7),(28,0,739,0,7),(134,0,633,0,7),(140,0,627,0,7),(168,0,599,0,7),(536,0,231,0,7),(584,0,183,0,7),(672,0,95,0,7),(704,0,63,0,7),(57,0,710,0,7),(76,2,689,0,7),(78,0,689,0,7),(99,0,668,0,7),(52,9,706,0,4),(60,1,706,0,4),(92,2,673,0,4),(94,0,673,0,4),(170,4,593,0,4),(185,0,582,0,4),(202,4,561,0,4),(553,16,198,0,4),(585,16,166,0,4),(590,0,177,0,4),(646,64,57,0,4),(657,32,78,0,4),(689,0,78,0,4),(705,32,30,0,4),(708,2,57,0,4),(710,0,57,0,4),(738,0,29,0,4),(216,544,6,1,2),(240,513,14,0,2)]
def data13 : Nat → Nat := (fun i => tableWord #[0x1ff,0x421460c407] i)
def data12 : Nat → Nat := (fun i => tableWord #[0x3ff482,0x2e0c20b0e20607,0x3ff4e2,0x85180c40a3219408,0x3ff502,0xa0c60a2219407,0x3ff507,0x25022818c0a1c408] i)
def data11 : Nat → Nat := bookData 2 2 3 (fun i => ((fun i => tableWord #[0x5075024e2482] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x3ffefffef7fffddf7] i) (i/16) >>> (11*(i%16))) % 2048) (fun i => ((fun i => tableWord #[0x504aa93d141e9a44bd2756922941e5a509d244a9425408ba4e8d236293a14089a460,0x522be93db492ca4f6524b272594a2aa495] i) (i/16) >>> (17*(i%16))) % 131072) (fun i => (if i<16 then (if i<8 then tableWord #[0x506c1c20bc3c407,0xb15c442c3861e1d08,0x410d120bc485c31b1f09,0x15c1c2c3c40b06,0x1241c4c30b05,0xd2605c48142c31d08,0x4212810dc685c425c31d0a,0x4612c3c41f0d06] i else tableWord #[0x1342c4c30d05,0xc609122641c485c31d09,0x828512c4c3462607,0x1d82c685c441c32008,0x13c445c31b1206,0x410b121d0d42c3c48609,0x860a0d0b1b1f06,0x1d1f81420d0f1285c4c3460b] i) else tableWord #[0x21c30b260d1b06,0xd12261b04,0x23261d1f418246c4c3850a,0xf0b46c31d05,0x410d12261d05,0x12c3462604,0xc3121541261b06,0xd12c645c32606] i))
def data10 : Nat → Nat := bookData 3 5 5 (fun i => ((fun i => tableWord #[0x522507d27502d245025075025245024e4502d284e2d244e25284e25244e25024e2d27482d23482507482502482527482,0xd22507] i) (i/16) >>> (24*(i%16))) % 16777216) (fun i => ((fun i => tableWord #[0xbffff7dffe7fd7fb7fbf7f7bdf7bfb9ffff3dfbefbfeb9f7,0xeff] i) (i/16) >>> (12*(i%16))) % 4096) (fun i => ((fun i => tableWord #[0x54829151ce352738d41ce3d4828350ce0d42183508c054928b49c61d4408748c8152718541c414e408750c00,0x5442b951cadd2763350d2b9492a941d8a1492a9510a95482a351d67d4751f510a7d4349b508c6d4741749065,0x5246bd5120cd4879941dc3949689525a25442c351d4f] i) (i/16) >>> (22*(i%16))) % 4194304) (fun i => (if i<32 then (if i<16 then (if i<8 then tableWord #[0xa0f0f880a04,0x361f02,0x1d1487c421b05,0x483e1b03,0x4c3e1b03,0x4c1b02,0x161b02,0x5054361f04] i else tableWord #[0x2c3e1b03,0x34161e03,0x543a1e03,0x2839412064361f06,0xc8e1864361f05,0x38361f03,0x2c361f03,0x120603c1d04] i) else (if i<24 then tableWord #[0x3c2602,0x4c1b02,0x8c1a1b03,0x1a1b02,0x3c2602,0x1a1b02,0x90981a1b04,0x3c2602] i else tableWord #[0x7c181e03,0xe080b048382606,0x440743fc3a3614422208,0x3c2602,0x70c141d03,0x3a2602,0x1205c3c2604,0x5054361f04] i)) else tableWord #[0xe187c222604,0x461f02,0x201a02,0x3a1f02,0x8074341f04,0x4c1d02,0x3c4c2303,0x3a2602] i))
def data9 : Nat → Nat := (fun i => tableWord #[0x1e6b5074e4502482,0x280981f03,0x15f7d63549507482,0x0,0x157fd67549507482,0x2701] i)
def levels : Nat → Packing
  | 9 => (3,4,6,0,0,0,0,data9)
  | 10 => (40,3,6,0,0,0,0,data10)
  | 11 => (24,2,6,0,0,0,0,data11)
  | 12 => (4,1,6,0,0,0,0,data12)
  | 13 => (1,0,6,0,0,0,0,data13)
  | _ => (0,0,0,0,0,0,0,fun _ => 0)
def index : Nat → Nat → Option (Nat × Nat)
  | 10 => fun v => (if v=9173731893560143937 then some (1,0) else (if v=9817994258469878493 then some (0,0) else (if v=11282382653361050149 then some (2,0) else (if v=13146079884629819533 then some (2,1) else none))))
  | 11 => fun h => smallSlot h 24 76 6 1 (fun i => ((fun i => tableWord #[0x40400a000000006040010000000,0x22c0010604004] i) (i/16) >>> (7*(i%16))) % 128) (fun i => ((fun i => tableWord #[0xf0021e0a08400000b7094001026542068d88,0xc2dc564299002180740042903000229280004800,0x634000000019f96000a443887003819109c09ba7,0x30cd3e9a0000085d8900000000008141100000,0x84ea1219a5d3b1f00000003c30039b] i) (i/16) >>> (10*(i%16))) % 1024)
  | 12 => fun h => smallSlot h 25 92 5 1 (fun i => ((fun i => tableWord #[0x8000000000000000800400000,0x2000000000000] i) (i/16) >>> (7*(i%16))) % 128) (fun i => ((fun i => tableWord #[0xac0000003aa004528d0200,0xa403d4a00088028400005180000,0xda380050f981469000000026b600000,0x7122c00004981c0190000000000000025400,0x4125e00002140000000031d67000000009,0x157] i) (i/16) >>> (9*(i%16))) % 512)
  | 13 => fun h => smallSlot h 3 11 3 1 (fun i => ((fun i => tableWord #[0x0] i) (i/16) >>> (4*(i%16))) % 16) (fun i => ((fun i => tableWord #[0x480310002da30128064] i) (i/16) >>> (7*(i%16))) % 128)
  | _ => fun _ => none
def book : Forest := ⟨767,13,samples,cols,[[],[16,66,101,151]],levels,index⟩
theorem geometry : graphValid book (boundsBefore entries) = true := by decide +kernel
set_option maxRecDepth 16000 in
theorem row13_0 : CutRow book 13 0 1 := bandCut 9 false (by decide +kernel)
theorem band13 : CutRow book 13 0 1 := row13_0
set_option maxRecDepth 16000 in
theorem row12_0 : CutRow book 12 0 4 := bandCut 10 false (by decide +kernel)
theorem band12 : CutRow book 12 0 4 := row12_0
set_option maxRecDepth 16000 in
theorem row11_0 : CutRow book 11 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_1 : CutRow book 11 1 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row11_13 : CutRow book 11 13 11 := bandCut 11 true (by decide +kernel)
theorem combine11_0_13 : CutRow book 11 0 13 := @joinRow book 11 0 1 12 row11_0 row11_1
theorem combine11_0_24 : CutRow book 11 0 24 := @joinRow book 11 0 13 11 combine11_0_13 row11_13
theorem band11 : CutRow book 11 0 24 := combine11_0_24
set_option maxRecDepth 16000 in
theorem row10_0 : CutRow book 10 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_1 : CutRow book 10 1 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_13 : CutRow book 10 13 12 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_25 : CutRow book 10 25 9 := bandCut 10 true (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row10_34 : CutRow book 10 34 6 := bandCut 11 false (by decide +kernel)
theorem combine10_0_13 : CutRow book 10 0 13 := @joinRow book 10 0 1 12 row10_0 row10_1
theorem combine10_13_21 : CutRow book 10 13 21 := @joinRow book 10 13 12 9 row10_13 row10_25
theorem combine10_0_34 : CutRow book 10 0 34 := @joinRow book 10 0 13 21 combine10_0_13 combine10_13_21
theorem combine10_0_40 : CutRow book 10 0 40 := @joinRow book 10 0 34 6 combine10_0_34 row10_34
theorem band10 : CutRow book 10 0 40 := combine10_0_40
set_option maxRecDepth 16000 in
theorem row9_0 : CutRow book 9 0 1 := bandCut 9 false (by decide +kernel)
set_option maxRecDepth 16000 in
theorem row9_1 : CutRow book 9 1 2 := bandCut 10 false (by decide +kernel)
theorem combine9_0_3 : CutRow book 9 0 3 := @joinRow book 9 0 1 2 row9_0 row9_1
theorem band9 : CutRow book 9 0 3 := combine9_0_3
theorem checked : mixedTables book 13 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact mixedEmpty _ _ _
  · exact band9
  · exact band10
  · exact band11
  · exact band12
  · exact band13
end B767_14
theorem h767_14 : Face true 767 14 :=
  mixedLower (g:=B767_14.book) (i:=0) (hints:=275431563556)
    (before_sound B767_14.entries B767_14.prior) B767_14.geometry B767_14.checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end Engine
end PEqualNP.Outside.L_meta_9825
namespace PEqualNP.Outside.L_meta_9822.Bound
open PEqualNP.Outside.L_meta_9825.Engine
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 16000
set_option maxHeartbeats 0
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ffffffffffffffffffffffffffffffffffffffffffffffffffffeaeaffffc0c0fffffffffffffffffffffffffffafff0ffffffffffffffffffffffffffeaffc0fffffffffffefcfcfffffffffffaf0f0ffeeeeeeffeeccccffeaeaeaffeac0c0
def func (x : Fin 10 → Bool) : Bool := (x 1 && x 2) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)
theorem truth : ∀ r : Row, bit r target = func (sample r) := by decide +kernel
theorem properTarget : proper target := by unfold proper; decide +kernel
def moves := ([128,81,130,83,100,118]:List Nat).map swapRows ++ fixRows 1 0
def witnesses : List (Sig × Row × Row) := [(inputs.getD 0 zero,16,17)]
theorem lifted : Lower true inputs target 15 := by
  have chk : checkLift moves target inputs (varsX 767) (graphGoal 767) witnesses = true := by decide +kernel
  have b := lift_ok chk properTarget (proper_of _ (by decide +kernel)) h767_14
  change Lower true inputs target (14+(witnesses.map Prod.fst).toFinset.card) at b
  have cnt : (witnesses.map Prod.fst).toFinset.card = 1 := by decide +kernel
  rw [cnt] at b
  exact b
theorem physical (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = func) :
    15 ≤ C.gates.countP (fun g => !isNot g) := by
  classical
  have eq : (execute C.gates inputs).getD C.output zero = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (truth r).symm)
  have out := get_rep (u:=true) (execute C.gates inputs) C.output
  rw [eq] at out
  unfold PEqualNP.Outside.L_meta_9825.Engine.Repr at out
  have pg : bit 0 target = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal (by simp) properTarget
    (out.resolve_right (fun h => h properTarget))
  have ns : inputs.all plainWord=true := by decide +kernel
  rw [nrm_map ns] at sub
  have run' := list_run run S.toList (Finset.nodup_toList S) (by simp)
  have supp : supply true (inputs.map observe) (S.toList.map observe) := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub _ (Finset.mem_toList.mp ha)))
  obtain ⟨q,bank,reach,hit,paid⟩ := contraction (observe_proper properTarget) run' (inputs.map observe)
    (p:=0) Reach.start supp
  have bound := lifted q bank reach hit
  omega
end PEqualNP.Outside.L_meta_9822.Bound


namespace PEqualNP.Outside.L_meta_9785_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

theorem wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

theorem wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

theorem wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

theorem wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

theorem wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

theorem val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

theorem val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]

abbrev Ref := Bool ⊕ ℕ

def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

theorem na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

theorem na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

theorem na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

theorem na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

theorem na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]

theorem na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha

theorem na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

theorem na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

theorem na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

theorem na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

theorem na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

theorem na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩

theorem na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

theorem na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen

theorem na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)

theorem na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]

theorem exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl

theorem na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

theorem na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

theorem na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

theorem na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega

theorem na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'

theorem na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩

theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

theorem normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩

section SurplusFlow

variable {n : ℕ} {D : Dag}

theorem sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

theorem sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

theorem sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

theorem fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

theorem lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

theorem sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

theorem sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

theorem sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

theorem sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

theorem sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩

theorem sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

theorem sum_fanout (hS : Strict n D) :
    ∑ w ∈ Finset.range (n + D.length), fanout D w = 2 * D.length := by
  rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
  intro e he
  have := sb_src_lt hS e he
  exact Finset.mem_range.mpr (by omega)

theorem surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega

theorem totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem Bplus_le_total (n : ℕ) (D : Dag) : Bplus n D ≤ totalSurplus n D := by
  rw [totalSurplus_split]; omega

theorem Bplus_le_twelve (h13 : totalSurplus n D ≤ 13) (h0 : 1 ≤ Bzero n D) :
    Bplus n D ≤ 12 := by
  rw [totalSurplus_split] at h13; omega

theorem live_reaches_out (h : StrictLive n D) (w : ℕ) (hw : w < n + D.length) :
    Relation.ReflTransGen (fun a b => b < n + D.length ∧ n ≤ b ∧
      (opA D (b - n) = a ∨ opB D (b - n) = a)) w (outW n D) := by
  obtain ⟨hS, hL, -⟩ := h
  generalize hk : n + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hlast : w + 1 = n + D.length
    · have hw2 : w = outW n D := by unfold outW; omega
      rw [hw2]
    · obtain ⟨j, hj⟩ := Finset.card_pos.mp (hL w (by omega))
      simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
      have hs := hS j hj.1
      refine Relation.ReflTransGen.head (b := n + j) ⟨by omega, by omega, ?_⟩
        (ih (n + D.length - (n + j)) (by omega) (n + j) (by omega) rfl)
      simpa using hj.2

theorem mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

theorem val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

theorem val_zero (hS : Strict n D) (w : ℕ) : val D (fun _ : Fin n => false) w = false := by
  by_cases hw : w < n + D.length
  · exact val_unique hS _ (fun _ => false) (fun _ _ => rfl)
      (fun j _ => by cases tag D j <;> rfl) w hw
  · exact val_ge D _ w (by omega)

theorem supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

theorem supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

theorem supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

theorem carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n + j ∈ K → opA D j ∈ K ∨ opB D j ∈ K) :
    (exitArcs n D K).card + (merges n D K).card = (sources n K).card + surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := hpred j (Finset.mem_range.mp hj)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

theorem sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

theorem sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
    (sources n (carrierT n D T)).card = T.card := by
  have himg : sources n (carrierT n D T) = T.image (fun v : Fin n => v.val) := by
    ext w
    simp only [sources, carrierT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨-, v, hv⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_inter, Finset.mem_singleton] at hv
      exact ⟨v, hv.2, by rw [hv.1]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨by have := v.isLt; omega, v, ?_⟩, v.isLt⟩
      rw [supp_input]; simp [hv]
  rw [himg, Finset.card_image_of_injective _ Fin.val_injective]

theorem carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card =
      T.card + surplusOn D (carrierT n D T) := by
  rw [← sb_sources_carrierT D T]
  refine carrier_flow h _ (sb_carrierT_sub T hout) (fun j hj hK => ?_)
  obtain ⟨ha, hb, -⟩ := h.1 j hj
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hK ⊢
  obtain ⟨v, hv⟩ := hK.2
  rw [Finset.mem_inter, supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [Finset.mem_inter] at hv
    exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩
  · rw [Finset.mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩
    · exact Or.inr ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩

theorem carrier_flow_diff (h : StrictLive n D) (x y : Fin n) (hxy : x ≠ y)
    (hout : x ∉ supp n D (outW n D)) :
    (exitArcs n D (carrierDiff n D x y)).card + (merges n D (carrierDiff n D x y)).card =
      1 + surplusOn D (carrierDiff n D x y) := by
  have hsub : carrierDiff n D x y ⊆ inner n D := by
    intro w hw
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hw
    rw [sb_mem_inner]
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2] at hw
    exact hout hw.2.1
  have hsrc : sources n (carrierDiff n D x y) = {x.val} := by
    ext w
    simp only [sources, carrierDiff, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hx, -⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_singleton] at hx
      rw [hx]
    · rintro rfl
      refine ⟨⟨by have := x.isLt; omega, ?_, ?_⟩, x.isLt⟩
      · rw [supp_input]; exact Finset.mem_singleton_self x
      · rw [supp_input, Finset.mem_singleton]; exact fun hc => hxy hc.symm
  have hfl := carrier_flow h _ hsub (fun j hj hK => ?_)
  · rw [hsrc, Finset.card_singleton] at hfl; exact hfl
  · obtain ⟨ha, hb, -⟩ := h.1 j hj
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hK ⊢
    obtain ⟨-, hx, hy⟩ := hK
    rw [supp_gate h.1 j hj] at hx hy
    split_ifs at hx hy with ht
    · rw [Finset.mem_inter] at hx hy
      by_cases hya : y ∈ supp n D (opA D j)
      · exact Or.inr ⟨by omega, hx.2, fun hc => hy ⟨hya, hc⟩⟩
      · exact Or.inl ⟨by omega, hx.1, hya⟩
    · rw [Finset.mem_union] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl ⟨by omega, h1, fun hc => hy (Or.inl hc)⟩
      · exact Or.inr ⟨by omega, h1, fun hc => hy (Or.inr hc)⟩

theorem mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

theorem card_units (n : ℕ) (D : Dag) : (units n D).card = totalSurplus n D := by
  rw [units, Finset.card_sigma, totalSurplus, surplusOn]
  simp

theorem card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

theorem card_unitsOn (K : Finset ℕ) (hK : K ⊆ inner n D) :
    (unitsOn n D K).card = surplusOn D K := by
  rw [unitsOn, sb_card_units_filter n D (fun w => w ∈ K), Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hK]

theorem mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

theorem mem_ineligSet {v : Fin n} :
    v ∈ ineligSet n D ↔ ∀ w, v ∈ supp n D w → fanout D w ≤ 1 := by
  rw [ineligSet, Finset.mem_sdiff, mem_eligSet]
  constructor
  · rintro ⟨-, h⟩ w hw
    by_contra hc
    exact h ⟨w, by omega, hw⟩
  · intro h
    refine ⟨Finset.mem_univ v, ?_⟩
    rintro ⟨w, hw, hv⟩
    have := h w hv
    omega

theorem sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

theorem sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

theorem reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    reservedUnits n D b ⊆ unitsPlus n D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨h2, hs⟩ := hb v hv
  have h1 : 1 ≤ fanout D (b v) := by omega
  rw [unitsPlus, Finset.mem_filter, mem_units]
  refine ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS h1), ?_⟩, ?_⟩
  · show 0 + 1 < fanout D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs]; exact Finset.singleton_nonempty v

theorem card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

theorem elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

theorem card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

theorem surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) = (T ∩ eligSet n D).card +
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT n D T) =
      ((units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter n D (fun w => (supp n D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, Finset.mem_filter] at hw
      have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) ∪
        (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono Finset.inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(Finset.mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty))
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty] at hne
      exact ⟨hne, hv⟩
    · rintro ⟨hT, hv⟩
      refine ⟨hv, ?_⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty]
      exact hT
  rw [h1, h2, Finset.card_union_of_disjoint h3, h4,
    Finset.card_image_of_injOn ((sb_reserved_inj b hb).mono
      (Finset.coe_subset.mpr Finset.inter_subset_right))]

theorem surplus_carrierT_le (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) + (eligSet n D).card ≤
      (T ∩ eligSet n D).card + Bplus n D := by
  have h1 := surplus_carrierT_eq hS b hb T
  have h2 := card_residual hS b hb
  have h3 := Finset.card_filter_le (residualUnits n D b)
    (fun u => (supp n D u.1 ∩ T).Nonempty)
  omega

end SurplusFlow

def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

theorem tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

theorem tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

theorem tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

theorem liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

theorem tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

theorem tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

theorem relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

theorem tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

theorem tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

theorem tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

theorem relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

theorem relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (w : ℕ) :
    val (relabel σ D) x (liftP σ w) = val D (fun i => x (σ i)) w := by
  by_cases hw : w < n + D.length
  · refine (val_unique (relabel_strict σ hS) x
      (fun w' => val D (fun i => x (σ i)) (liftP σ⁻¹ w')) ?_ ?_ (liftP σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i => x (σ i)) (liftP σ⁻¹ i) = x ⟨i, hi⟩
      rw [tr_liftP_lt σ⁻¹ hi, val_input D _ _ (σ⁻¹ ⟨i, hi⟩).isLt]
      simp
    · intro j hj
      rw [relabel_length] at hj
      show val D (fun i => x (σ i)) (liftP σ⁻¹ (n + j)) =
        gop (tag (relabel σ D) j) (val D (fun i => x (σ i)) (liftP σ⁻¹ (opA (relabel σ D) j)))
          (val D (fun i => x (σ i)) (liftP σ⁻¹ (opB (relabel σ D) j)))
      rw [tr_liftP_ge σ⁻¹ (Nat.le_add_right n j), tr_tag σ D j hj, tr_opA σ D j hj,
        tr_opB σ D j hj, liftP_inv, liftP_inv, val_gate hS _ j hj]
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i => x (σ i)) (liftP σ⁻¹ (liftP σ w)) = _
      rw [liftP_inv]
  · have hw' := Nat.not_lt.mp hw
    rw [tr_liftP_ge σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [relabel_length]; exact hw'), val_ge _ _ _ hw']

theorem relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

theorem relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (relabel σ D) := by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [relabel_length] at hw'
    have hpos := List.length_pos_iff.mpr hne
    rw [← tr_liftP_inv' σ w', relabel_fanout]
    apply hL
    by_cases h : w' < n
    · have := (tr_liftP_lt_iff σ⁻¹ le_rfl w').mpr h
      omega
    · rw [tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]; exact hw'

theorem relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

theorem relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

theorem tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

theorem relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

theorem tr_sum_liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (P : ℕ → Prop)
    [DecidablePred P] (g : ℕ → ℕ) :
    ∑ w ∈ (Finset.range m).filter (fun w => P (liftP σ w)), g (liftP σ w) =
      ∑ w ∈ (Finset.range m).filter P, g w := by
  refine Finset.sum_nbij' (liftP σ) (liftP σ⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ hm a).mpr ha.1, ha.2⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ⁻¹ hm a).mpr ha.1, by rw [tr_liftP_inv']; exact ha.2⟩
  · intro a _; exact liftP_inv σ a
  · intro a _; exact tr_liftP_inv' σ a
  · intro a _; rfl

theorem tr_surplus_filter {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ w, Q (liftP σ w) ↔ P w) :
    surplusOn (relabel σ D) ((inner n (relabel σ D)).filter Q) =
      surplusOn D ((inner n D).filter P) := by
  rcases eq_or_ne D [] with rfl | hne
  · simp [surplusOn, relabel, fanout, readers]
  · have hpos := List.length_pos_iff.mpr hne
    have hm : n ≤ n + D.length - 1 := by omega
    unfold surplusOn inner
    rw [relabel_length]
    exact (tr_sum_liftP σ hm Q (fun w => fanout (relabel σ D) w - 1)).symm.trans
      (Finset.sum_congr (Finset.filter_congr fun w _ => hPQ w)
        fun w _ => by rw [relabel_fanout])

theorem relabel_totalSurplus {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    totalSurplus n (relabel σ D) = totalSurplus n D := by
  simpa [totalSurplus] using
    tr_surplus_filter σ D (fun _ => True) (fun _ => True) (fun _ => Iff.rfl)

theorem relabel_Bplus {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bplus n (relabel σ D) = Bplus n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)

theorem relabel_Bzero {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bzero n (relabel σ D) = Bzero n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)

theorem relabel_eligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    eligSet n (relabel σ D) = (eligSet n D).image σ := by
  ext v
  simp only [eligSet, Finset.mem_biUnion, Finset.mem_image, branchW, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨w', ⟨hw', hf⟩, hv⟩
    obtain ⟨w, rfl⟩ : ∃ w, w' = liftP σ w := ⟨liftP σ⁻¹ w', (tr_liftP_inv' σ w').symm⟩
    rw [relabel_supp σ hS, Finset.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    rw [relabel_fanout] at hf
    rw [relabel_length, tr_liftP_lt_iff σ (Nat.le_add_right _ _)] at hw'
    exact ⟨a, ⟨w, ⟨hw', hf⟩, ha⟩, rfl⟩
  · rintro ⟨a, ⟨w, ⟨hw, hf⟩, ha⟩, rfl⟩
    refine ⟨liftP σ w, ⟨?_, ?_⟩, ?_⟩
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · rw [relabel_fanout]; exact hf
    · rw [relabel_supp σ hS]; exact Finset.mem_image_of_mem _ ha

theorem relabel_ineligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    ineligSet n (relabel σ D) = (ineligSet n D).image σ := by
  ext v
  simp only [ineligSet, relabel_eligSet σ hS, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ v, fun hm => h ⟨σ⁻¹ v, hm, by simp⟩, by simp⟩
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact ha (σ.injective hab ▸ hb)

theorem relabel_pureBranch {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) :
    PureBranch n (relabel σ D) (fun v => liftP σ (b (σ⁻¹ v))) := by
  intro v hv
  rw [relabel_eligSet σ hS, Finset.mem_image] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨hf, hs⟩ := hb u hu
  have e : σ⁻¹ (σ u) = u := by simp
  show 2 ≤ fanout (relabel σ D) (liftP σ (b (σ⁻¹ (σ u)))) ∧
    supp n (relabel σ D) (liftP σ (b (σ⁻¹ (σ u)))) = {σ u}
  rw [e, relabel_fanout, relabel_supp σ hS, hs, Finset.image_singleton]
  exact ⟨hf, rfl⟩

def edgeList : List (ℕ × ℕ) :=
  [(1, 2), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (6, 9), (6, 8), (5, 8)]

def G10Edge (x : Fin 10 → Bool) : Prop :=
  ∃ u v : Fin 10, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true

abbrev Adj (u v : Fin 10) : Prop :=
  (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList

def adjBits (u : Fin 10) : ℕ :=
  match u.val with
  | 0 => 48 | 1 => 68 | 2 => 130 | 3 => 272 | 4 => 521 | 5 => 385 | 6 => 770 | 7 => 548 | 8 => 104 | _ => 208

def hc_adjB (u v : Fin 10) : Bool := (adjBits u).testBit v.val

theorem hc_adjB_iff : ∀ u v : Fin 10, hc_adjB u v = true ↔ Adj u v := by
  decide +kernel

theorem sem_adjB_false {u v : Fin 10} : hc_adjB u v = false ↔ ¬ Adj u v := by
  rw [← hc_adjB_iff]; cases hc_adjB u v <;> decide

theorem adj_symm {u v : Fin 10} (h : Adj u v) : Adj v u := h.symm

theorem adj_irrefl (u : Fin 10) : ¬ Adj u u := by
  revert u; decide +kernel

theorem g10Edge_iff_adj (x : Fin 10 → Bool) :
    G10Edge x ↔ ∃ u v : Fin 10, Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩; exact ⟨u, v, Or.inl huv, hx, hy⟩
  · rintro ⟨u, v, huv | hvu, hx, hy⟩
    · exact ⟨u, v, huv, hx, hy⟩
    · exact ⟨v, u, hvu, hy, hx⟩

def g10_nbB (v : Fin 10) : Finset (Fin 10) :=
  Finset.univ.filter (fun u => hc_adjB v u = true)

theorem nbr_diff_exists : ∀ u v : Fin 10, u ≠ v → ∃ z : Fin 10, Adj u z ∧ ¬ Adj v z := by
  have h : ∀ u v : Fin 10, u ≠ v → ∃ z : Fin 10, hc_adjB u z = true ∧ hc_adjB v z = false := by
    decide +kernel
  intro u v huv
  obtain ⟨z, h1, h2⟩ := h u v huv
  exact ⟨z, (hc_adjB_iff u z).1 h1, sem_adjB_false.1 h2⟩

def hc_mate (v : Fin 10) : Fin 10 :=
  match v.val with
  | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 0 | 6 => 1 | 7 => 2 | 8 => 3 | _ => 4

theorem hc_mate_adj : ∀ v : Fin 10, hc_adjB v (hc_mate v) = true := by
  decide +kernel

def IsAut (σ : Equiv.Perm (Fin 10)) : Prop :=
  ∀ u v : Fin 10, Adj (σ u) (σ v) ↔ Adj u v

theorem g10Edge_aut (σ : Equiv.Perm (Fin 10)) (hσ : IsAut σ) (x : Fin 10 → Bool) :
    G10Edge (x ∘ σ) ↔ G10Edge x := by
  rw [g10Edge_iff_adj, g10Edge_iff_adj]
  constructor
  · rintro ⟨u, v, huv, hx, hy⟩
    exact ⟨σ u, σ v, (hσ u v).mpr huv, hx, hy⟩
  · rintro ⟨u, v, huv, hx, hy⟩
    refine ⟨σ.symm u, σ.symm v, (hσ (σ.symm u) (σ.symm v)).mp ?_, ?_, ?_⟩
    · simpa using huv
    · simpa [Function.comp] using hx
    · simpa [Function.comp] using hy

def IsCover (S : Finset (Fin 10)) : Prop :=
  ∀ u v : Fin 10, Adj u v → u ∈ S ∨ v ∈ S

def IsIndep (I : Finset (Fin 10)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ Adj u v

def aut0Fun (v : Fin 10) : Fin 10 := match v.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | _ => 9
def aut0Inv (v : Fin 10) : Fin 10 := match v.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | _ => 9
def aut0 : Equiv.Perm (Fin 10) where
  toFun := aut0Fun
  invFun := aut0Inv
  left_inv := by decide
  right_inv := by decide
def aut1Fun (v : Fin 10) : Fin 10 := match v.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 7 | 7 => 6 | 8 => 5 | _ => 9
def aut1Inv (v : Fin 10) : Fin 10 := match v.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 7 | 7 => 6 | 8 => 5 | _ => 9
def aut1 : Equiv.Perm (Fin 10) where
  toFun := aut1Fun
  invFun := aut1Inv
  left_inv := by decide
  right_inv := by decide

def autOf (k : Fin 2) : Equiv.Perm (Fin 10) :=
  match k.val with
  | 0 => aut0
  | _ => aut1

theorem autOf_isAut : ∀ k : Fin 2, IsAut (autOf k) := by
  intro k u v
  rw [← hc_adjB_iff, ← hc_adjB_iff]
  revert k u v; decide +kernel

def hc_rep (idx : Fin 44) : Finset (Fin 10) :=
  match idx.val with
  | 0 => {0, 1}
  | 1 => {0, 2}
  | 2 => {0, 3}
  | 3 => {1, 4}
  | 4 => {1, 5}
  | 5 => {2, 5}
  | 6 => {3, 5}
  | 7 => {4, 5}
  | 8 => {0, 6}
  | 9 => {2, 6}
  | 10 => {3, 6}
  | 11 => {4, 6}
  | 12 => {5, 6}
  | 13 => {6, 7}
  | 14 => {0, 9}
  | 15 => {1, 9}
  | 16 => {5, 9}
  | 17 => {0, 1, 3}
  | 18 => {1, 3, 5}
  | 19 => {2, 3, 5}
  | 20 => {1, 4, 5}
  | 21 => {2, 4, 5}
  | 22 => {0, 2, 6}
  | 23 => {0, 3, 6}
  | 24 => {2, 3, 6}
  | 25 => {2, 4, 6}
  | 26 => {2, 5, 6}
  | 27 => {3, 5, 6}
  | 28 => {4, 5, 6}
  | 29 => {0, 6, 7}
  | 30 => {4, 6, 7}
  | 31 => {0, 1, 9}
  | 32 => {0, 2, 9}
  | 33 => {0, 3, 9}
  | 34 => {1, 5, 9}
  | 35 => {2, 5, 9}
  | 36 => {3, 5, 9}
  | 37 => {0, 2, 3, 6}
  | 38 => {2, 3, 5, 6}
  | 39 => {2, 4, 5, 6}
  | 40 => {0, 3, 6, 7}
  | 41 => {0, 1, 3, 9}
  | 42 => {1, 3, 5, 9}
  | _ => {2, 3, 5, 9}

def canonI : Finset (Finset (Fin 10)) := Finset.univ.image hc_rep

def repMask (idx : Fin 44) : ℕ :=
  match idx.val with
  | 0 => 3
  | 1 => 5
  | 2 => 9
  | 3 => 18
  | 4 => 34
  | 5 => 36
  | 6 => 40
  | 7 => 48
  | 8 => 65
  | 9 => 68
  | 10 => 72
  | 11 => 80
  | 12 => 96
  | 13 => 192
  | 14 => 513
  | 15 => 514
  | 16 => 544
  | 17 => 11
  | 18 => 42
  | 19 => 44
  | 20 => 50
  | 21 => 52
  | 22 => 69
  | 23 => 73
  | 24 => 76
  | 25 => 84
  | 26 => 100
  | 27 => 104
  | 28 => 112
  | 29 => 193
  | 30 => 208
  | 31 => 515
  | 32 => 517
  | 33 => 521
  | 34 => 546
  | 35 => 548
  | 36 => 552
  | 37 => 77
  | 38 => 108
  | 39 => 116
  | 40 => 201
  | 41 => 523
  | 42 => 554
  | _ => 556

def setMask (S : Finset (Fin 10)) : ℕ :=
  (if (0 : Fin 10) ∈ S then 2 ^ 0 else 0) |||
  (if (1 : Fin 10) ∈ S then 2 ^ 1 else 0) |||
  (if (2 : Fin 10) ∈ S then 2 ^ 2 else 0) |||
  (if (3 : Fin 10) ∈ S then 2 ^ 3 else 0) |||
  (if (4 : Fin 10) ∈ S then 2 ^ 4 else 0) |||
  (if (5 : Fin 10) ∈ S then 2 ^ 5 else 0) |||
  (if (6 : Fin 10) ∈ S then 2 ^ 6 else 0) |||
  (if (7 : Fin 10) ∈ S then 2 ^ 7 else 0) |||
  (if (8 : Fin 10) ∈ S then 2 ^ 8 else 0) |||
  (if (9 : Fin 10) ∈ S then 2 ^ 9 else 0)

theorem ite_two_pow_testBit (p : Prop) [Decidable p] (k b : ℕ) :
    (if p then 2 ^ k else 0).testBit b = (decide (k = b) && decide p) := by
  split_ifs with hp <;> simp [Nat.testBit_two_pow, hp]

theorem setMask_testBit (S : Finset (Fin 10)) (i : Fin 10) :
    (setMask S).testBit i.val = decide (i ∈ S) := by
  fin_cases i <;>
    (simp only [setMask, Nat.testBit_or, ite_two_pow_testBit]; simp)

theorem ite_two_pow_lt (p : Prop) [Decidable p] (k : ℕ) (hk : k < 10) :
    (if p then 2 ^ k else 0) < 2 ^ 10 := by
  split_ifs
  · exact Nat.pow_lt_pow_right (by omega) hk
  · omega

theorem setMask_lt (S : Finset (Fin 10)) : setMask S < 1024 := by
  change setMask S < 2 ^ 10
  unfold setMask
  repeat (apply Nat.or_lt_two_pow)
  all_goals exact ite_two_pow_lt _ _ (by omega)

theorem setMask_inj {S T : Finset (Fin 10)} (h : setMask S = setMask T) : S = T := by
  ext i
  have h1 := congrArg (fun m => m.testBit i.val) h
  rw [setMask_testBit, setMask_testBit] at h1
  simpa using h1

theorem repMask_eq : ∀ idx : Fin 44, setMask (hc_rep idx) = repMask idx := by
  decide +kernel

def isIndepMask (m : ℕ) : Bool :=
  edgeList.all (fun e => !(m.testBit e.1 && m.testBit e.2))

def popMask (m : ℕ) : ℕ :=
  (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 1 else 0) +
  (if m.testBit 2 then 1 else 0) + (if m.testBit 3 then 1 else 0) +
  (if m.testBit 4 then 1 else 0) + (if m.testBit 5 then 1 else 0) +
  (if m.testBit 6 then 1 else 0) + (if m.testBit 7 then 1 else 0) +
  (if m.testBit 8 then 1 else 0) + (if m.testBit 9 then 1 else 0)

def autMask (k : Fin 2) (m : ℕ) : ℕ :=
  (if m.testBit 0 then 2 ^ (autOf k 0).val else 0) |||
  (if m.testBit 1 then 2 ^ (autOf k 1).val else 0) |||
  (if m.testBit 2 then 2 ^ (autOf k 2).val else 0) |||
  (if m.testBit 3 then 2 ^ (autOf k 3).val else 0) |||
  (if m.testBit 4 then 2 ^ (autOf k 4).val else 0) |||
  (if m.testBit 5 then 2 ^ (autOf k 5).val else 0) |||
  (if m.testBit 6 then 2 ^ (autOf k 6).val else 0) |||
  (if m.testBit 7 then 2 ^ (autOf k 7).val else 0) |||
  (if m.testBit 8 then 2 ^ (autOf k 8).val else 0) |||
  (if m.testBit 9 then 2 ^ (autOf k 9).val else 0)

def findCanonIdx (m : ℕ) : Option (Fin 44) :=
  (List.finRange 44).find? (fun idx => repMask idx == m)

theorem isIndepMask_of_isIndep {I : Finset (Fin 10)} (hI : IsIndep I) :
    isIndepMask (setMask I) = true := by
  have hedge : ∀ u v : Fin 10, Adj u v →
      !((setMask I).testBit u.val && (setMask I).testBit v.val) = true := by
    intro u v huv
    rw [setMask_testBit, setMask_testBit]
    by_cases hu : u ∈ I <;> by_cases hv : v ∈ I
    · exact absurd huv (hI u hu v hv)
    · simp [hu, hv]
    · simp [hu, hv]
    · simp [hu, hv]
  unfold isIndepMask edgeList
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨hedge 1 2 (by decide), hedge 3 4 (by decide), hedge 0 4 (by decide), hedge 0 5 (by decide),
    hedge 1 6 (by decide), hedge 2 7 (by decide), hedge 3 8 (by decide), hedge 4 9 (by decide),
    hedge 5 7 (by decide), hedge 7 9 (by decide), hedge 6 9 (by decide), hedge 6 8 (by decide),
    hedge 5 8 (by decide)⟩

theorem popMask_eq_card (I : Finset (Fin 10)) : popMask (setMask I) = I.card := by
  have h1 : I.card = ∑ x ∈ (Finset.univ : Finset (Fin 10)), if x ∈ I then 1 else 0 := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  have huniv : (Finset.univ : Finset (Fin 10)) = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  rw [h1, huniv]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    Fin.reduceEq, or_self, not_false_eq_true]
  dsimp only [popMask]
  rw [show (setMask I).testBit 0 = decide ((0 : Fin 10) ∈ I) from setMask_testBit I 0,
      show (setMask I).testBit 1 = decide ((1 : Fin 10) ∈ I) from setMask_testBit I 1,
      show (setMask I).testBit 2 = decide ((2 : Fin 10) ∈ I) from setMask_testBit I 2,
      show (setMask I).testBit 3 = decide ((3 : Fin 10) ∈ I) from setMask_testBit I 3,
      show (setMask I).testBit 4 = decide ((4 : Fin 10) ∈ I) from setMask_testBit I 4,
      show (setMask I).testBit 5 = decide ((5 : Fin 10) ∈ I) from setMask_testBit I 5,
      show (setMask I).testBit 6 = decide ((6 : Fin 10) ∈ I) from setMask_testBit I 6,
      show (setMask I).testBit 7 = decide ((7 : Fin 10) ∈ I) from setMask_testBit I 7,
      show (setMask I).testBit 8 = decide ((8 : Fin 10) ∈ I) from setMask_testBit I 8,
      show (setMask I).testBit 9 = decide ((9 : Fin 10) ∈ I) from setMask_testBit I 9]
  simp only [decide_eq_true_eq]
  omega

theorem autMask_testBit (k : Fin 2) (m : ℕ) (i : Fin 10) :
    (autMask k m).testBit i.val = m.testBit ((autOf k)⁻¹ i).val := by
  have hc : ∀ (j : Fin 10), ((autOf k j).val = i.val) ↔ j = (autOf k)⁻¹ i := by
    intro j
    constructor
    · intro h; exact ((Equiv.eq_symm_apply (autOf k)).2 (Fin.ext h))
    · intro h; exact congrArg Fin.val ((Equiv.eq_symm_apply (autOf k)).1 h)
  have hterm : ∀ (j : Fin 10),
      (if m.testBit j.val = true then 2 ^ (autOf k j).val else 0).testBit i.val =
      (decide (j = (autOf k)⁻¹ i) && m.testBit j.val) := by
    intro j; rw [ite_two_pow_testBit, decide_eq_decide.2 (hc j)]; cases m.testBit j.val <;> rfl
  have hexp : (autMask k m).testBit i.val =
      ((decide ((0 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 0) ||
      (decide ((1 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 1) ||
      (decide ((2 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 2) ||
      (decide ((3 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 3) ||
      (decide ((4 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 4) ||
      (decide ((5 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 5) ||
      (decide ((6 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 6) ||
      (decide ((7 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 7) ||
      (decide ((8 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 8) ||
      (decide ((9 : Fin 10) = (autOf k)⁻¹ i) && m.testBit 9)) := by
    change ((if m.testBit (0 : Fin 10).val = true then 2 ^ (autOf k 0).val else 0) |||
      (if m.testBit (1 : Fin 10).val = true then 2 ^ (autOf k 1).val else 0) |||
      (if m.testBit (2 : Fin 10).val = true then 2 ^ (autOf k 2).val else 0) |||
      (if m.testBit (3 : Fin 10).val = true then 2 ^ (autOf k 3).val else 0) |||
      (if m.testBit (4 : Fin 10).val = true then 2 ^ (autOf k 4).val else 0) |||
      (if m.testBit (5 : Fin 10).val = true then 2 ^ (autOf k 5).val else 0) |||
      (if m.testBit (6 : Fin 10).val = true then 2 ^ (autOf k 6).val else 0) |||
      (if m.testBit (7 : Fin 10).val = true then 2 ^ (autOf k 7).val else 0) |||
      (if m.testBit (8 : Fin 10).val = true then 2 ^ (autOf k 8).val else 0) |||
      (if m.testBit (9 : Fin 10).val = true then 2 ^ (autOf k 9).val else 0)).testBit i.val = _
    simp only [Nat.testBit_or, hterm]
    rfl
  rw [hexp]
  generalize (autOf k)⁻¹ i = t
  fin_cases t <;> simp

theorem setMask_image_aut (k : Fin 2) (S : Finset (Fin 10)) :
    setMask (S.image (autOf k)) = autMask k (setMask S) := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 10
  · have hL : (setMask (S.image (autOf k))).testBit b =
        decide ((⟨b, hb⟩ : Fin 10) ∈ S.image (autOf k)) :=
      setMask_testBit (S.image (autOf k)) ⟨b, hb⟩
    rw [hL]
    have him : (⟨b, hb⟩ : Fin 10) ∈ S.image (autOf k) ↔ (autOf k)⁻¹ ⟨b, hb⟩ ∈ S := by
      constructor
      · intro hmem
        obtain ⟨x, hx, hxi⟩ := Finset.mem_image.1 hmem
        have : x = (autOf k)⁻¹ ⟨b, hb⟩ := by rw [← hxi]; simp
        exact this ▸ hx
      · intro hx; exact Finset.mem_image.2 ⟨(autOf k)⁻¹ ⟨b, hb⟩, hx, by simp⟩
    have hR : (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 10).val =
        decide ((autOf k)⁻¹ ⟨b, hb⟩ ∈ S) := by
      rw [autMask_testBit, setMask_testBit]
    change _ = (autMask k (setMask S)).testBit (⟨b, hb⟩ : Fin 10).val
    rw [hR, decide_eq_decide]
    exact him
  · have hL : (setMask (S.image (autOf k))).testBit b = false :=
      Nat.testBit_lt_two_pow ((setMask_lt _).trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 10 ≤ b)))
    have hltR : autMask k (setMask S) < 2 ^ 10 := by
      unfold autMask
      repeat (apply Nat.or_lt_two_pow)
      all_goals exact ite_two_pow_lt _ _ (Fin.isLt _)
    have hR : (autMask k (setMask S)).testBit b = false :=
      Nat.testBit_lt_two_pow (hltR.trans_le (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 10 ≤ b)))
    rw [hL, hR]

theorem findCanonIdx_some (m : ℕ) (idx : Fin 44) (h : findCanonIdx m = some idx) :
    repMask idx = m := by
  unfold findCanonIdx at h
  have := List.find?_some h
  simpa using this

theorem g10_indep_le_four : ∀ m : Fin 1024, isIndepMask m.val = true → popMask m.val ≤ 4 := by
  decide +kernel

theorem cover_card_ge_six {S : Finset (Fin 10)} (hcov : IsCover S) : 6 ≤ S.card := by
  have hind : IsIndep (Finset.univ \ S) := by
    intro u hu v hv huv
    have h1 := (Finset.mem_sdiff.mp hu).2
    have h2 := (Finset.mem_sdiff.mp hv).2
    exact (hcov u v huv).elim h1 h2
  have hle : (Finset.univ \ S).card ≤ 4 := by
    rw [← popMask_eq_card]
    exact g10_indep_le_four ⟨setMask (Finset.univ \ S), setMask_lt _⟩ (isIndepMask_of_isIndep hind)
  have hadd := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ, Fintype.card_fin] at hadd
  omega

theorem g10_canon_all : ∀ m : Fin 1024,
    isIndepMask m.val = true → 2 ≤ popMask m.val →
    ∃ k : Fin 2, (findCanonIdx (autMask k m.val)).isSome = true := by
  decide +kernel

theorem exists_aut_canon {I : Finset (Fin 10)} (h : IsIndep I) (hge : 2 ≤ I.card) :
    ∃ σ : Equiv.Perm (Fin 10), IsAut σ ∧ I.image σ ∈ canonI := by
  have hm_lt := setMask_lt I
  have hind := isIndepMask_of_isIndep h
  have hpop : 2 ≤ popMask (setMask I) := by rw [popMask_eq_card]; exact hge
  obtain ⟨k, hk⟩ := g10_canon_all ⟨setMask I, hm_lt⟩ hind hpop
  obtain ⟨idx, hidx⟩ := Option.isSome_iff_exists.1 hk
  refine ⟨autOf k, autOf_isAut k, Finset.mem_image.2 ⟨idx, Finset.mem_univ _, ?_⟩⟩
  apply setMask_inj
  rw [repMask_eq, setMask_image_aut]
  exact findCanonIdx_some _ _ hidx

theorem hc_rep_of_mem {I : Finset (Fin 10)} (h : I ∈ canonI) : ∃ idx : Fin 44, hc_rep idx = I := by
  obtain ⟨idx, -, hidx⟩ := Finset.mem_image.1 h
  exact ⟨idx, hidx⟩

theorem g10_not_empty : ¬ G10Edge (fun _ => false) := by
  rintro ⟨_, _, _, h, _⟩; exact Bool.noConfusion h

theorem g10_not_single (v : Fin 10) : ¬ G10Edge (fun i => decide (i = v)) := by
  rw [g10Edge_iff_adj]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  rw [ha, hb] at hab
  exact adj_irrefl v hab

theorem g10_pair {u v : Fin 10} (h : Adj u v) :
    G10Edge (fun i => decide (i = u) || decide (i = v)) := by
  rw [g10Edge_iff_adj]; exact ⟨u, v, h, by simp, by simp⟩

theorem g10_essential (i : Fin 10) : ∃ x y : Fin 10 → Bool,
    (∀ j, j ≠ i → x j = y j) ∧ G10Edge x ∧ ¬ G10Edge y :=
  ⟨fun j => decide (j = i) || decide (j = hc_mate i), fun j => decide (j = hc_mate i),
   fun j hj => by simp [hj], g10_pair ((hc_adjB_iff i (hc_mate i)).1 (hc_mate_adj i)),
   g10_not_single (hc_mate i)⟩

def Correct (D : Dag) : Prop :=
  ∀ x : Fin 10 → Bool, val D x (outW 10 D) = true ↔ G10Edge x

theorem g10_normalize (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = true ↔ G10Edge x) :
    ∃ D : Dag, StrictLive 10 D ∧ D.length ≤ C.size ∧ Correct D := by
  have h12 : Adj (1 : Fin 10) 2 := by decide
  obtain ⟨D, hD, hlen, hval⟩ := normalize_strictLive (n := 10) C hmono
    (by
      intro b
      cases b
      · exact ⟨_, by rw [Ne, Bool.not_eq_false]; exact (hC _).2 (g10_pair h12)⟩
      · exact ⟨fun _ => false, fun h => g10_not_empty ((hC _).1 h)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun h => g10_not_single i ((hC _).1 ?_)⟩
      rw [h]; simp)
    (by
      intro i
      obtain ⟨x, y, hxy, hx, hy⟩ := g10_essential i
      refine ⟨x, y, hxy, fun h => hy ((hC y).1 ?_)⟩
      rw [← h]; exact (hC x).2 hx)
  exact ⟨D, hD, hlen, fun x => by rw [hval x]; exact hC x⟩

theorem g10_relabel (σ : Equiv.Perm (Fin 10)) (hσ : IsAut σ) {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D) :
    StrictLive 10 (relabel σ D) ∧ Correct (relabel σ D) ∧
      (relabel σ D).length = D.length ∧
      totalSurplus 10 (relabel σ D) = totalSurplus 10 D ∧
      Bplus 10 (relabel σ D) = Bplus 10 D ∧ Bzero 10 (relabel σ D) = Bzero 10 D ∧
      eligSet 10 (relabel σ D) = (eligSet 10 D).image σ ∧
      ineligSet 10 (relabel σ D) = (ineligSet 10 D).image σ := by
  refine ⟨relabel_strictLive σ h, fun x => ?_, relabel_length σ D, relabel_totalSurplus σ D,
    relabel_Bplus σ h.1, relabel_Bzero σ h.1, relabel_eligSet σ h.1, relabel_ineligSet σ h.1⟩
  rw [relabel_out σ h.1 h.2.2 x, hD]
  exact g10Edge_aut σ hσ x

theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  simpa [ineligSet] using h

theorem g10_cover_iff_indep (D : Dag) :
    IsCover (eligSet 10 D) ↔ IsIndep (ineligSet 10 D) := by
  constructor
  · intro hcov u hu v hv huv
    have h1 := Finset.mem_sdiff.mp hu
    have h2 := Finset.mem_sdiff.mp hv
    exact (hcov u v huv).elim h1.2 h2.2
  · intro hind u v huv
    by_contra hc; push Not at hc
    exact hind u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc.1⟩)
      v (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hc.2⟩) huv

theorem g10_wlog {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hind : IsIndep (ineligSet 10 D)) (hge : 2 ≤ (ineligSet 10 D).card) :
    ∃ D' : Dag, StrictLive 10 D' ∧ Correct D' ∧ D'.length = D.length ∧
      totalSurplus 10 D' = totalSurplus 10 D ∧
      Bplus 10 D' = Bplus 10 D ∧ Bzero 10 D' = Bzero 10 D ∧
      (ineligSet 10 D').card = (ineligSet 10 D).card ∧
      ineligSet 10 D' ∈ canonI := by
  obtain ⟨σ, hσ, hmem⟩ := exists_aut_canon hind hge
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := g10_relabel σ hσ h hD
  refine ⟨relabel σ D, h1, h2, h3, h4, h5, h6, ?_, h8 ▸ hmem⟩
  rw [h8, Finset.card_image_of_injective _ σ.injective]

theorem g10_budget {D : Dag} (h : StrictLive 10 D) (hlen : D.length ≤ 17) :
    totalSurplus 10 D = D.length - 9 ∧ totalSurplus 10 D ≤ 8 := by
  have := surplus_identity h
  exact ⟨by omega, by omega⟩

theorem g10_p_bounds {D : Dag} (h : StrictLive 10 D) (hlen : D.length ≤ 17)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (hcov : IsCover (eligSet 10 D)) :
    6 ≤ (eligSet 10 D).card ∧ (eligSet 10 D).card ≤ Bplus 10 D ∧
      Bplus 10 D ≤ 8 ∧ totalSurplus 10 D ≤ 8 := by
  have h1 := cover_card_ge_six hcov
  have h2 := elig_le_Bplus h.1 b hb
  have h3 := Bplus_le_total 10 D
  have h4 := (g10_budget h hlen).2
  exact ⟨h1, h2, by omega, h4⟩

theorem g10_inelig_bounds {D : Dag} (h : StrictLive 10 D) (hlen : D.length ≤ 17)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (hcov : IsCover (eligSet 10 D)) :
    (ineligSet 10 D).Nonempty ∧ 2 ≤ (ineligSet 10 D).card ∧ (ineligSet 10 D).card ≤ 4 := by
  obtain ⟨h6, hp, hB, h8⟩ := g10_p_bounds h hlen b hb hcov
  have hc := inelig_card_add 10 D
  exact ⟨Finset.card_pos.1 (by omega), by omega, by omega⟩

def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

def sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)

theorem sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

theorem sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

theorem sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]

theorem sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

theorem sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

theorem sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

theorem sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

theorem sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

theorem sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm

theorem sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

theorem sem_step_iff {a b : ℕ} : sem_step n D a b ↔
    ∃ j s, j < D.length ∧ b = n + j ∧ src D (j, s) = a := by
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact ⟨b - n, false, by omega, by omega, by rw [sb_src_false]; exact h3⟩
    · exact ⟨b - n, true, by omega, by omega, by rw [sb_src_true]; exact h3⟩
  · rintro ⟨j, s, hj, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    cases s
    · exact Or.inl (sb_src_false j).symm
    · exact Or.inr (sb_src_true j).symm

theorem sem_step_lt (hS : Strict n D) {a b : ℕ} (h : sem_step n D a b) : a < b := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hS (b - n) (by omega)
  omega

theorem sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

theorem sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

theorem sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

theorem sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (w : ℕ) (hw : val D x w ≠ val D y w) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) v.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn] at hw
      have hwv : (⟨w, hn⟩ : Fin n) = v := by
        by_contra hc; exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hw
        rw [val_gate hS x j hj, val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j) ≠ val D y (opB D j) := by
            intro h2; apply hg; rw [h1, h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
      · exfalso; apply hw; rw [val_ge D x w (by omega), val_ge D y w (by omega)]

def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

theorem sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val D x b = val D y b) : val D x (outW n D) = val D y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

theorem sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
    sem_Dom n D b v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep _ ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest⟩
      · have h0 := fanout_eq_zero_of_ge hS a (by rw [heq]; unfold outW; omega)
        have h1 := hstep.2
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest

theorem sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
    (∀ u, u < w → v ∈ supp n D u → fanout D u ≤ 1) → sem_Chain n D v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, Finset.mem_singleton] at hv
      rw [hv]; exact Relation.ReflTransGen.refl
    · have hlt := sem_supp_lt hv
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, v ∈ supp n D (src D (j, s)) → sem_Chain n D v.val (n + j) := by
        intro s hva
        have hstep : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
        have hlt' := sem_src_lt hS hj s
        have h1 := sem_step_fanout hstep
        have h2 := hlow _ hlt' hva
        exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu => hlow u (by omega)))
          ⟨hstep, by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [sb_src_false]; exact (Finset.mem_inter.mp hv).1)
      · rcases Finset.mem_union.mp hv with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
        · exact key true (by rw [sb_src_true]; exact h1)

theorem sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

theorem sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

theorem sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

theorem sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨hsym, hirr, hsep, -⟩ := hG
  obtain ⟨z, hvz, huz⟩ := hsep v u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact h1 ((hC _).mp h3)

theorem sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hch : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ h2 (fun u hu huv => by
      have := Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega, huv⟩)
  exact ⟨Nat.find hex, h1, Finset.Subset.antisymm
    (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2), hch⟩

def sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

theorem sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_FirstBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · obtain ⟨b, hb⟩ := sem_first_branch hG hS hC v hv
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

theorem sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

theorem sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

theorem sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

theorem sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

theorem sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

theorem sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

theorem sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
      by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩

theorem sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {v : Fin n} (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1, !e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅ := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus hv, Finset.card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0, -⟩ := hG.2.2.2 v v
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := Finset.card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  rw [he, Finset.mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    sem_inelig_pure hG hS hC hv
      (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, Finset.mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, Finset.mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha

theorem sem_inelig_or (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {j : ℕ} (hj : j < D.length) (hc : v ∈ supp n D (n + j)) :
    tag D j = false := by
  obtain ⟨e, -, -, -, -, -, -, hmer⟩ := sem_inelig_consumer hG h hC hv
  by_contra ht
  rw [Bool.not_eq_false] at ht
  have hc2 := hc
  rw [sem_supp_and h.1 hj ht, Finset.mem_inter] at hc2
  have : j ∈ merges n D (carrierT n D {v}) := by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, sem_mem_carrier1.mpr hc, sem_mem_carrier1.mpr hc2.1, sem_mem_carrier1.mpr hc2.2⟩
  rw [hmer] at this
  exact Finset.notMem_empty _ this

theorem sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) : u ∈ eligSet n D ∨ v ∈ eligSet n D := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨eu, -, -, -, -, hnu, hxu, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.1)
  obtain ⟨ev, -, -, hsv, -, -, hxv, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.2)
  obtain ⟨j, hj, -, -, hju, hjv, s, h1, -, h3, -⟩ := sem_joint_meeting hG h.1 hC huv
  have m1 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, h1, hju⟩
  have m2 : (j, !s) ∈ exitArcs n D (carrierT n D {v}) := sem_mem_exit1.mpr ⟨hj, h3, hjv⟩
  rw [hxu, Finset.mem_singleton] at m1
  rw [hxv, Finset.mem_singleton] at m2
  subst m1
  subst m2
  obtain ⟨a, hua, hav⟩ := hG.2.2.2 u v
  have h5 : a ∈ supp n D (src D (j, !s)) := hnu a hua
  rw [hsv, Finset.mem_singleton] at h5
  exact hav h5

theorem sem_ind_no_edge {A : Finset (Fin n)} (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) :
    ¬ sem_Edge G (sem_ind A) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [sem_ind, decide_eq_true_eq] at ha hc
  exact hA a ha c hc hac

theorem sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (x : Fin n)
    (hnb : ∃ a ∈ A, G x a) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ x ∈ supp n D (src D (j, s)) ∧
      x ∉ supp n D (n + j) ∧ Disjoint (supp n D (src D (j, s))) A := by
  by_contra hcon
  have hmask : ∀ j s, j < D.length → tag D j = true → x ∈ supp n D (src D (j, s)) →
      x ∉ supp n D (n + j) → val D (sem_ind A) (src D (j, s)) = true ∧
        val D (sem_ins x (sem_ind A)) (src D (j, s)) = true := by
    intro j s hj ht h1 h2
    have hnd : ¬ Disjoint (supp n D (src D (j, s))) A :=
      fun hd => hcon ⟨j, s, hj, ht, h1, h2, hd⟩
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨a, ha1, ha2⟩ := hnd
    exact ⟨sem_val_of_supp hS ha1 (by simp [sem_ind, ha2]),
      sem_val_of_supp hS ha1 (by simp [sem_ins, sem_ind, ha2])⟩
  have key : ∀ w, x ∉ supp n D w → val D (sem_ind A) w = val D (sem_ins x (sem_ind A)) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hn : w < n
      · rw [val_input D _ w hn, val_input D _ w hn]
        have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
        rw [hs, Finset.mem_singleton] at hw
        exact sem_ins_agree x _ _ (fun hc => hw hc.symm)
      · by_cases hlt : w < n + D.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha, hb, -⟩ := hS j hj
          rw [val_gate hS _ j hj, val_gate hS _ j hj]
          cases ht : tag D j
          · rw [sem_supp_or hS hj ht, Finset.mem_union, not_or] at hw
            rw [ih _ ha hw.1, ih _ hb hw.2]
          · have hw2 := hw
            rw [sem_supp_and hS hj ht, Finset.mem_inter, not_and] at hw2
            by_cases hxa : x ∈ supp n D (opA D j)
            · have h1 := hmask j false hj ht (by rw [sb_src_false]; exact hxa) hw
              rw [sb_src_false] at h1
              rw [ih _ hb (hw2 hxa), h1.1, h1.2]
            · by_cases hxb : x ∈ supp n D (opB D j)
              · have h1 := hmask j true hj ht (by rw [sb_src_true]; exact hxb) hw
                rw [sb_src_true] at h1
                rw [ih _ ha hxa, h1.1, h1.2]
              · rw [ih _ ha hxa, ih _ hb hxb]
        · rw [val_ge D _ w (by omega), val_ge D _ w (by omega)]
  have hout := key (outW n D) (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  obtain ⟨a, ha, hxa⟩ := hnb
  have h2 : sem_Edge G (sem_ins x (sem_ind A)) :=
    ⟨x, a, hxa, sem_ins_self x _, by simp [sem_ins, sem_ind, ha]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact sem_ind_no_edge hA ((hC _).mp h3)

theorem sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
    (hw : supp n D w ∩ T = M) :
    ∃ j, j < D.length ∧ n + j ≤ w ∧ supp n D (n + j) ∩ T = M ∧
      j ∈ merges n D (carrierT n D T) ∧ (∀ u, u < n + j → supp n D u ∩ T ≠ M) ∧
      ((tag D j = true ∧ M ⊂ supp n D (opA D j) ∩ T ∧ M ⊂ supp n D (opB D j) ∩ T) ∨
        (tag D j = false ∧ supp n D (opA D j) ∩ T ⊂ M ∧ supp n D (opB D j) ∩ T ⊂ M ∧
          (supp n D (opA D j) ∩ T) ∪ (supp n D (opB D j) ∩ T) = M ∧
          (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty)) := by
  classical
  have hex : ∃ u, supp n D u ∩ T = M := ⟨w, hw⟩
  have hle : Nat.find hex ≤ w := Nat.find_min' hex hw
  have hmin : ∀ u, u < Nat.find hex → supp n D u ∩ T ≠ M := fun u hu => Nat.find_min hex hu
  have hspec := Nat.find_spec hex
  generalize Nat.find hex = f at hle hmin hspec
  have hMne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : ∀ {u : ℕ}, (supp n D u ∩ T).Nonempty → u ∈ carrierT n D T := by
    intro u hu
    obtain ⟨v, hv⟩ := hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (sem_supp_lt (Finset.mem_inter.mp hv).1), v, hv⟩
  have hflt : f < n + D.length := by
    obtain ⟨v, hv⟩ := hMne
    rw [← hspec] at hv
    exact sem_supp_lt (Finset.mem_inter.mp hv).1
  have hfn : n ≤ f := by
    by_contra hc
    have hc' : f < n := by omega
    have hs : supp n D f = {⟨f, hc'⟩} := supp_input D ⟨f, hc'⟩
    have h1 : M.card ≤ 1 := by
      rw [← hspec, hs]
      exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  refine ⟨j, hj, hle, hspec, ?_, hmin, ?_⟩
  · have hAB : (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty := by
      cases ht : tag D j
      · rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
        constructor
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.empty_union] at hspec
          exact hnb hspec
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.union_empty] at hspec
          exact hna hspec
      · rw [sem_supp_and hS hj ht] at hspec
        obtain ⟨v, hv⟩ := hMne
        rw [← hspec] at hv
        simp only [Finset.mem_inter] at hv
        exact ⟨⟨v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩, ⟨v, Finset.mem_inter.mpr ⟨hv.1.2, hv.2⟩⟩⟩
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hmem (by rw [hspec]; exact hMne), hmem hAB.1, hmem hAB.2⟩
  · cases ht : tag D j
    · right
      rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
      have hsa : supp n D (opA D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_left
      have hsb : supp n D (opB D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_right
      refine ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, hnb⟩, hspec, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.empty_union] at hspec
        exact hnb hspec
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.union_empty] at hspec
        exact hna hspec
    · left
      rw [sem_supp_and hS hj ht] at hspec
      have hsa : M ⊆ supp n D (opA D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.1, hv.2⟩
      have hsb : M ⊆ supp n D (opB D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.2, hv.2⟩
      exact ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, Ne.symm hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, Ne.symm hnb⟩⟩

end SemCore

theorem sem_g10_second : ∀ u v : Fin 10, ∃ a, hc_adjB u a = true ∧ a ≠ v := by decide +kernel

theorem sem_g10_gr : sem_Gr (fun u v : Fin 10 => Adj u v) :=
  ⟨fun _ _ => adj_symm, adj_irrefl, nbr_diff_exists, fun u v => by
    obtain ⟨a, h1, h2⟩ := sem_g10_second u v
    exact ⟨a, (hc_adjB_iff u a).mp h1, h2⟩⟩

theorem sem_g10_comp {D : Dag} (hD : Correct D) : sem_Comp 10 (fun u v : Fin 10 => Adj u v) D :=
  fun x => (hD x).trans (g10Edge_iff_adj x)

theorem exists_pureBranch {D : Dag} (h : StrictLive 10 D) (hD : Correct D) :
    ∃ b : Fin 10 → ℕ, PureBranch 10 D b :=
  sem_exists_pureBranch sem_g10_gr h.1 (sem_g10_comp hD)

theorem elig_isCover {D : Dag} (h : StrictLive 10 D) (hD : Correct D) :
    IsCover (eligSet 10 D) :=
  fun _ _ huv => sem_elig_cover sem_g10_gr h (sem_g10_comp hD) huv

theorem g10_wlog_canon (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = true ↔ G10Edge x)
    (hsize : C.size ≤ 17) :
    ∃ D : Dag, StrictLive 10 D ∧ Correct D ∧ D.length ≤ 17 ∧
      totalSurplus 10 D ≤ 8 ∧ 2 ≤ (ineligSet 10 D).card ∧ ineligSet 10 D ∈ canonI := by
  obtain ⟨D0, h0, hlen0, hD0⟩ := g10_normalize C hmono hC
  have hlen : D0.length ≤ 17 := by omega
  obtain ⟨b, hb⟩ := exists_pureBranch h0 hD0
  have hcov := elig_isCover h0 hD0
  obtain ⟨-, hge2, -⟩ := g10_inelig_bounds h0 hlen b hb hcov
  obtain ⟨D, h1, h2, h3, -, -, -, -, h8⟩ :=
    g10_wlog h0 hD0 ((g10_cover_iff_indep D0).mp hcov) hge2
  have hlen' : D.length ≤ 17 := by omega
  obtain ⟨b', hb'⟩ := exists_pureBranch h1 h2
  obtain ⟨-, hge2', -⟩ := g10_inelig_bounds h1 hlen' b' hb' (elig_isCover h1 h2)
  exact ⟨D, h1, h2, hlen', (g10_budget h1 hlen').2, hge2', h8⟩

def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

theorem sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

theorem sem_bar_ne (e : ℕ × Bool) : sem_bar e ≠ e := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [sem_bar] at h2

theorem sem_same_gate {e f : ℕ × Bool} (h : e.1 = f.1) : f = e ∨ f = sem_bar e := by
  obtain ⟨j, s⟩ := e
  obtain ⟨k, t⟩ := f
  simp only at h
  subst h
  cases s <;> cases t <;> simp [sem_bar]

theorem sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
    tag D e.1 = true := by
  obtain ⟨hj, h1, h2⟩ := sem_mem_W.mp he
  by_contra ht
  rw [Bool.not_eq_true] at ht
  apply h2
  rw [sem_supp_or hS hj ht, Finset.mem_union]
  obtain ⟨j, s⟩ := e
  cases s
  · left; simpa [src] using h1
  · right; simpa [src] using h1

theorem sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [Finset.card_singleton] at h1

theorem sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩

theorem sem_cover_free (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x a b y : Fin n} (hab : ¬ G a b) (hxy : G x y) (hya : ¬ G y a) (hyb : ¬ G y b) :
    ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) ∧ b ∉ supp n D (src D e) := by
  have hsym := hG.1
  have hirr := hG.2.1
  have hA : ∀ u ∈ ({a, b, y} : Finset (Fin n)), ∀ v ∈ ({a, b, y} : Finset (Fin n)),
      ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv]
    · exact hirr a
    · exact hab
    · exact fun h => hya (hsym _ _ h)
    · exact fun h => hab (hsym _ _ h)
    · exact hirr b
    · exact fun h => hyb (hsym _ _ h)
    · exact hya
    · exact hyb
    · exact hirr y
  obtain ⟨j, s, hj, -, h1, h2, hd⟩ := sem_exposure hG hS hC {a, b, y} hA x ⟨y, by simp, hxy⟩
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, h2⟩, fun h => Finset.disjoint_left.mp hd h (by simp),
    fun h => Finset.disjoint_left.mp hd h (by simp)⟩

theorem sem_antichain (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x a : Fin n}
    (hxa : x ≠ a) : ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) := by
  obtain ⟨z, hxz, haz⟩ := hG.2.2.1 x a hxa
  obtain ⟨e, he, h1, -⟩ := sem_cover_free hG hS hC (a := a) (b := a) (hG.2.1 a) hxz
    (fun h => haz (hG.1 _ _ h)) (fun h => haz (hG.1 _ _ h))
  exact ⟨e, he, h1⟩

theorem sem_free_empty (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) (hu : u ∈ eligSet n D) (hv : v ∈ eligSet n D) :
    ∃ j, j < D.length ∧ tag D j = true ∧ supp n D (n + j) = ∅ ∧
      (supp n D (opA D j)).Nonempty ∧ (supp n D (opB D j)).Nonempty ∧
      val D (sem_two u v) (n + j) = true ∧
      ∀ i ∈ ineligSet n D, i ∉ supp n D (opA D j) ∧ i ∉ supp n D (opB D j) := by
  classical
  have hS := h.1
  have hex : ∃ w, val D (sem_two u v) w = true ∧ supp n D w = ∅ :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), sem_supp_out hG hC⟩
  obtain ⟨hw1, hw2⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true → (supp n D a).Nonempty := by
    intro a ha hva
    rw [Finset.nonempty_iff_ne_empty]
    exact fun hc => Nat.find_min hex ha ⟨hva, hc⟩
  generalize Nat.find hex = w at hw1 hw2 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hs : supp n D w = {⟨w, by omega⟩} := supp_input D ⟨w, by omega⟩
    rw [hs] at hw2
    exact Finset.singleton_ne_empty _ hw2
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  have hdead : ∀ w', w' < n + j → ∀ i ∈ ineligSet n D, i ∈ supp n D w' →
      val D (sem_two u v) w' = false := by
    intro w'
    induction w' using Nat.strong_induction_on with
    | _ w' ih =>
      intro hlt' i hi hiw
      have hpure := sem_inelig_pure hG hS hC hi hiw
      by_cases hn' : w' < n
      · have hs : supp n D w' = {⟨w', hn'⟩} := supp_input D ⟨w', hn'⟩
        rw [hs, Finset.mem_singleton] at hiw
        rw [val_input D _ w' hn', ← hiw]
        have hiu : i ≠ u := fun hc => (sem_mem_inelig.mp hi) (hc ▸ hu)
        have hiv : i ≠ v := fun hc => (sem_mem_inelig.mp hi) (hc ▸ hv)
        simp [sem_two, hiu, hiv]
      · obtain ⟨j', rfl⟩ : ∃ j', w' = n + j' := ⟨w' - n, by omega⟩
        have hj' : j' < D.length := by omega
        obtain ⟨ha', hb', -⟩ := hS j' hj'
        have ht' := sem_inelig_or hG h hC hi hj' hiw
        have hop : ∀ a, a < n + j' → supp n D a ⊆ {i} → val D (sem_two u v) a = false := by
          intro a hlt2 hsub
          by_cases hia : i ∈ supp n D a
          · exact ih a hlt2 (by omega) i hi hia
          · by_contra hc
            rw [Bool.not_eq_false] at hc
            obtain ⟨q, hq⟩ := hmin a (by omega) hc
            have := hsub hq
            rw [Finset.mem_singleton] at this
            exact hia (this ▸ hq)
        rw [sem_supp_or hS hj' ht'] at hpure
        rw [val_gate hS _ j' hj', ht', gop_false,
          hop _ ha' (by rw [← hpure]; exact Finset.subset_union_left),
          hop _ hb' (by rw [← hpure]; exact Finset.subset_union_right)]
        rfl
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1
    simp only [gop_false, Bool.or_eq_true] at hw1
    rw [sem_supp_or hS hj ht, Finset.union_eq_empty] at hw2
    rcases hw1 with h1 | h1
    · have := hmin _ ha h1
      rw [hw2.1] at this
      exact Finset.not_nonempty_empty this
    · have := hmin _ hb h1
      rw [hw2.2] at this
      exact Finset.not_nonempty_empty this
  · rw [ht] at hw1
    simp only [gop_true, Bool.and_eq_true] at hw1
    refine ⟨j, hj, ht, hw2, hmin _ ha hw1.1, hmin _ hb hw1.2, hval, fun i hi => ⟨?_, ?_⟩⟩
    · intro hc
      have := hdead _ ha i hi hc
      rw [hw1.1] at this
      exact Bool.noConfusion this
    · intro hc
      have := hdead _ hb i hi hc
      rw [hw1.2] at this
      exact Bool.noConfusion this

end SemCodes

theorem sem_rtg_comparable {α : Type} {R : α → α → Prop}
    (hfun : ∀ a a' b, R a b → R a' b → a = a') {u v c : α}
    (hu : Relation.ReflTransGen R u c) (hv : Relation.ReflTransGen R v c) :
    Relation.ReflTransGen R u v ∨ Relation.ReflTransGen R v u := by
  induction hu with
  | refl => exact Or.inr hv
  | tail hab hbc ih =>
    rcases Relation.ReflTransGen.cases_tail hv with h | ⟨b', hvb', hb'c⟩
    · left
      rw [← h]
      exact Relation.ReflTransGen.tail hab hbc
    · have hbb : b' = _ := hfun _ _ _ hb'c hbc
      rw [hbb] at hvb'
      exact ih hvb'

def sem_MinBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v) ∧
    ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b v ≤ w

def sem_Arm (n : ℕ) (D : Dag) (X : Finset (Fin n)) (a b : ℕ) : Prop :=
  sem_step n D a b ∧ fanout D a = 1 ∧ ∀ x ∈ X, x ∈ supp n D a ∧ x ∈ supp n D b

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_rtg_le (hS : Strict n D) {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → sem_step n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (sem_step_lt hS (hR _ _ hbc)))

theorem sem_exists_minBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_MinBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b ∧
        ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b ≤ w := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
      obtain ⟨h1, h2⟩ := Nat.find_spec hex
      have hch : sem_Chain n D v.val (Nat.find hex) :=
        sem_carrier_chain hS v _ h2 (fun u hu huv => by
          have := Nat.find_min hex hu
          by_contra hc
          exact this ⟨by omega, huv⟩)
      exact ⟨Nat.find hex, fun _ => ⟨h1, Finset.Subset.antisymm
        (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2),
        hch, fun w hw1 hw2 => Nat.find_min' hex ⟨hw1, hw2⟩⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_minBranch_first {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : sem_FirstBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1, (hb v hv).2.2.1⟩

theorem sem_minBranch_pure {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_zm_gate (hS : Strict n D) {x : Fin n} (hM : merges n D (carrierT n D {x}) = ∅)
    {j : ℕ} (hj : j < D.length) (hx : x ∈ supp n D (n + j)) :
    tag D j = false ∧ ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
  have hnot : ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
    intro hc
    have hm : j ∈ merges n D (carrierT n D {x}) := by
      rw [merges, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, sem_mem_carrier1.mpr hx, sem_mem_carrier1.mpr hc.1, sem_mem_carrier1.mpr hc.2⟩
    rw [hM] at hm
    exact Finset.notMem_empty _ hm
  refine ⟨?_, hnot⟩
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rw [sem_supp_and hS hj ht, Finset.mem_inter] at hx
  exact hnot hx

theorem sem_code_count (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + (({x} : Finset (Fin n)) ∩ eligSet n D).card +
        ((residualUnits n D b).filter (fun u => x ∈ supp n D u.1)).card := by
  have h1 := sem_flow1 hG h hC x
  have h2 := surplus_carrierT_eq h.1 b hb {x}
  have h3 : (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ {x}).Nonempty) =
      (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) := by
    refine Finset.filter_congr (fun u _ => ?_)
    constructor
    · rintro ⟨y, hy⟩
      rw [Finset.mem_inter, Finset.mem_singleton] at hy
      exact hy.2 ▸ hy.1
    · intro hx
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_singleton_self x⟩⟩
  rw [h3] at h2
  omega

theorem sem_descent (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) :
    ∀ c, (∀ x ∈ X, x ∈ supp n D c) →
      (∀ x ∈ X, ∀ w, c ≤ w → x ∈ supp n D w → fanout D w ≤ 1) →
      ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
        Relation.ReflTransGen (sem_Arm n D X) c (src D e) := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  intro c
  generalize hk : n + D.length - c = k
  induction k using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    intro hc hlow
    have hclt := sem_supp_lt (hc x0 hx0)
    have hcne : c ≠ outW n D := by
      intro he
      have := hc x0 hx0
      rw [he, sem_supp_out hG hC] at this
      exact Finset.notMem_empty _ this
    have hf1 : 1 ≤ fanout D c := h.2.1 c (by unfold outW at hcne; omega)
    have hf : fanout D c = 1 := le_antisymm (hlow x0 hx0 c (le_refl c) (hc x0 hx0)) hf1
    obtain ⟨j, hjr⟩ := Finset.card_pos.mp hf1
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hjr
    obtain ⟨hj, hop⟩ := hjr
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = c := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    have hcj : c < n + j := hs ▸ sem_src_lt hS hj s
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hj hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hj ht, Finset.mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hc x hx
        · right; rw [h1]; exact hc x hx
      obtain ⟨e, he1, he2⟩ := ih (n + D.length - (n + j)) (by omega) (n + j) rfl hall
        (fun x hx w hw => hlow x hx w (by omega))
      refine ⟨e, he1, Relation.ReflTransGen.head ⟨?_, hf, fun x hx => ⟨hc x hx, hall x hx⟩⟩ he2⟩
      rw [← hs]
      exact sem_step_src hj s
    · refine ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hj, ?_, fun hc2 => hcar ⟨x, hx, hc2⟩⟩, ?_⟩
      · rw [hs]; exact hc x hx
      · rw [hs]

theorem sem_two_arms (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) (r : ℕ)
    (hr : ∀ x ∈ X, x ∈ supp n D r) (hf : 2 ≤ fanout D r)
    (hlow : ∀ x ∈ X, ∀ w, r < w → x ∈ supp n D w → fanout D w ≤ 1) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (show 1 < (readers D r).card from hf)
  have hread : ∀ j ∈ readers D r, j < D.length ∧ r < n + j ∧ (opA D j = r ∨ opB D j = r) := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
    have := hS j hj.1
    exact ⟨hj.1, by omega, hj.2⟩
  have hterm : ∀ j ∈ readers D r, ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
      ((e.1 = j ∧ src D e = r) ∨ Relation.ReflTransGen (sem_Arm n D X) (n + j) (src D e)) := by
    intro j hj
    obtain ⟨hjl, hrj, hop⟩ := hread j hj
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = r := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hjl hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hjl ht, Finset.mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hr x hx
        · right; rw [h1]; exact hr x hx
      obtain ⟨e, he1, he2⟩ := sem_descent hG h hC X ⟨x0, hx0⟩ hM (n + j) hall
        (fun x hx w hw => hlow x hx w (by omega))
      exact ⟨e, he1, Or.inr he2⟩
    · exact ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hjl, by rw [hs]; exact hr x hx,
        fun hc2 => hcar ⟨x, hx, hc2⟩⟩, Or.inl ⟨rfl, hs⟩⟩
  have hRstep : ∀ a b, sem_Arm n D X a b → sem_step n D a b := fun _ _ hab => hab.1
  have hfun : ∀ a a' b, sem_Arm n D X a b → sem_Arm n D X a' b → a = a' := by
    intro a a' b h1 h2
    by_contra hne2
    obtain ⟨hb1, hb2, hba⟩ := h1.1
    obtain ⟨-, -, hba'⟩ := h2.1
    have hjb : b - n < D.length := by omega
    have hcarb : x0 ∈ supp n D (n + (b - n)) := by
      rw [Nat.add_sub_cancel' hb2]; exact (h1.2.2 x0 hx0).2
    apply (sem_zm_gate hS (hM x0 hx0) hjb hcarb).2
    have ha := (h1.2.2 x0 hx0).1
    have ha' := (h2.2.2 x0 hx0).1
    rcases hba with e1 | e1 <;> rcases hba' with e2 | e2
    · exact absurd (e1.symm.trans e2) hne2
    · rw [e1, e2]; exact ⟨ha, ha'⟩
    · rw [e1, e2]; exact ⟨ha', ha⟩
    · exact absurd (e1.symm.trans e2) hne2
  have hcross : ∀ ja ∈ readers D r, ∀ jb ∈ readers D r, ja ≠ jb →
      ¬ Relation.ReflTransGen (sem_Arm n D X) (n + ja) (n + jb) := by
    intro ja hja jb hjb hab hp
    obtain ⟨hjla, hrja, -⟩ := hread ja hja
    obtain ⟨hjlb, hrjb, hopb⟩ := hread jb hjb
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu1, hu2⟩
    · exact hab (by omega)
    · have hle := sem_rtg_le hS hRstep hu1
      have hur : u = r := by
        by_contra hur
        obtain ⟨-, -, hbu⟩ := hu2.1
        rw [Nat.add_sub_cancel_left] at hbu
        apply (sem_zm_gate hS (hM x0 hx0) hjlb (hu2.2.2 x0 hx0).2).2
        have hu := (hu2.2.2 x0 hx0).1
        have hrr := hr x0 hx0
        rcases hbu with e1 | e1 <;> rcases hopb with e2 | e2
        · exact absurd (e1.symm.trans e2) hur
        · rw [e1, e2]; exact ⟨hu, hrr⟩
        · rw [e1, e2]; exact ⟨hrr, hu⟩
        · exact absurd (e1.symm.trans e2) hur
      omega
  obtain ⟨P, hP1, hP2⟩ := hterm j1 hj1
  obtain ⟨Q, hQ1, hQ2⟩ := hterm j2 hj2
  refine ⟨P, Q, fun hPQ => ?_, fun x hx => ⟨hP1 x hx, hQ1 x hx⟩⟩
  have hsame : Q = P := by
    rcases sem_same_gate hPQ with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨hjP, hxP, hnP⟩ := sem_mem_W.mp (hP1 x0 hx0)
      have hxQ := (sem_mem_W.mp (hQ1 x0 hx0)).2.1
      rw [h1] at hxQ
      apply hnP
      rw [sem_supp_and hS hjP (sem_W_and hS (hP1 x0 hx0)), Finset.mem_inter]
      obtain ⟨j, s⟩ := P
      cases s
      · exact ⟨by simpa [src] using hxP, by simpa [src, sem_bar] using hxQ⟩
      · exact ⟨by simpa [src, sem_bar] using hxQ, by simpa [src] using hxP⟩
  rw [hsame] at hQ2
  obtain ⟨-, hrj1, -⟩ := hread j1 hj1
  obtain ⟨-, hrj2, -⟩ := hread j2 hj2
  rcases hP2 with ⟨hPa, hPb⟩ | hPp <;> rcases hQ2 with ⟨hQa, hQb⟩ | hQp
  · exact hne (hPa.symm.trans hQa)
  · have := sem_rtg_le hS hRstep hQp
    omega
  · have := sem_rtg_le hS hRstep hPp
    omega
  · rcases sem_rtg_comparable hfun hPp hQp with h1 | h1
    · exact hcross j1 hj1 j2 hj2 hne h1
    · exact hcross j2 hj2 j1 hj1 (Ne.symm hne) h1

theorem sem_saturated (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {u0 : Σ _ : ℕ, ℕ}
    (hres : residualUnits n D b = {u0}) {x : Fin n} (hsat : 3 ≤ (sem_W n D x).card) :
    (sem_W n D x).card = 3 ∧ merges n D (carrierT n D {x}) = ∅ ∧ x ∈ eligSet n D ∧
      x ∈ supp n D u0.1 := by
  have h1 := sem_code_count hG h hC b hb x
  have h2 : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have h3 := Finset.card_filter_le (residualUnits n D b) (fun u => x ∈ supp n D u.1)
  rw [hres, Finset.card_singleton] at h3
  rw [hres] at h1
  refine ⟨by omega, Finset.card_eq_zero.mp (by omega), ?_, ?_⟩
  · by_contra hx
    have h4 : ({x} : Finset (Fin n)) ∩ eligSet n D = ∅ := by
      rw [Finset.singleton_inter_of_notMem hx]
    rw [h4, Finset.card_empty] at h1
    omega
  · have h4 : 0 < (({u0} : Finset (Σ _ : ℕ, ℕ)).filter (fun u => x ∈ supp n D u.1)).card := by
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp h4
    rw [Finset.mem_filter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2

theorem sem_common_terminals (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : sem_MinBranch n D b) (hone : Bplus n D = (eligSet n D).card + 1)
    (X : Finset (Fin n)) (hX : X.Nonempty) (hsat : ∀ x ∈ X, 3 ≤ (sem_W n D x).card) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  have hS := h.1
  have hbp := sem_minBranch_pure hb
  have hcard : (residualUnits n D b).card = 1 := by
    have := card_residual hS b hbp
    omega
  obtain ⟨u0, hres⟩ := Finset.card_eq_one.mp hcard
  have hu0 : u0 ∈ residualUnits n D b := by rw [hres]; exact Finset.mem_singleton_self _
  have hu0u : u0 ∈ units n D :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by
    have := (mem_units.mp hu0u).2
    omega
  refine sem_two_arms hG h hC X hX (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.1)
    u0.1 (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.2.2) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨-, -, hxe, hxr⟩ := sem_saturated hG h hC b hbp hres (hsat x hx)
  by_contra hc
  have hw2 : 2 ≤ fanout D w := by omega
  have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    rw [unitsPlus, Finset.mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), by show 0 + 1 < fanout D w; omega⟩,
      ⟨x, hxw⟩⟩
  by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits n D b
  · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
    have hbv : b v = w := congrArg Sigma.fst hveq
    have hsv := (hb v hv).2.1
    rw [hbv] at hsv
    rw [hsv, Finset.mem_singleton] at hxw
    have hmin := (hb x hxe).2.2.2 u0.1 hfr hxr
    rw [hxw, hbv] at hmin
    omega
  · have hwres : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits n D b :=
      Finset.mem_sdiff.mpr ⟨hwu, hwr⟩
    rw [hres, Finset.mem_singleton] at hwres
    have : w = u0.1 := congrArg Sigma.fst hwres
    omega

end SemArms

theorem sem_all_but_one {α : Type} (J : Finset α) (P : α → Prop)
    (h : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → P i ∨ P j) :
    ∃ J' ⊆ J, J.card ≤ J'.card + 1 ∧ ∀ i ∈ J', P i := by
  classical
  refine ⟨J.filter P, Finset.filter_subset _ _, ?_, fun i hi => (Finset.mem_filter.mp hi).2⟩
  have h1 : (J.filter (fun i => ¬ P i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    rcases h a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab with h1 | h1
    · exact (Finset.mem_filter.mp ha).2 h1
    · exact (Finset.mem_filter.mp hb).2 h1
  have h2 := Finset.card_filter_add_card_filter_not (s := J) P
  omega

section SemPaths

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ind_single (a : Fin n) : sem_ind ({a} : Finset (Fin n)) = single a := by
  funext k; simp [sem_ind, single]

theorem sem_val_gate_src (hS : Strict n D) (x : Fin n → Bool) {j : ℕ} (hj : j < D.length)
    (s : Bool) : val D x (n + j) =
      gop (tag D j) (val D x (src D (j, s))) (val D x (src D (j, !s))) := by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src, Bool.and_comm, Bool.or_comm]

theorem sem_ins_ind_edge (hG : sem_Gr G) {i : Fin n} {S : Finset (Fin n)}
    (h : sem_Edge G (sem_ins i (sem_ind S))) :
    (∃ a ∈ S, G i a) ∨ ∃ a ∈ S, ∃ b ∈ S, G a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu, hv] at huv; exact absurd huv (hG.2.1 i)
  · rw [hu] at huv; exact Or.inl ⟨v, hv, huv⟩
  · rw [hv] at huv; exact Or.inl ⟨u, hu, hG.1 _ _ huv⟩
  · exact Or.inr ⟨u, hu, v, hv, huv⟩

theorem sem_chain_dom_at (hS : Strict n D) {v b t : ℕ} (h : sem_Chain n D v b) (hbt : b ≤ t) :
    b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep hrest ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest'⟩
      · have h1 := sem_step_lt hS hstep.1
        have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest'

theorem sem_dom_eq_at (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b t : ℕ)
    (hdom : b = v.val ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v.val t)
    (hb : val D x b = val D y b) : val D x t = val D y t := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

theorem sem_chain_fork (hS : Strict n D) {a c q : ℕ} (hc : sem_Chain n D a c)
    (hq : Relation.ReflTransGen (sem_step n D) a q) :
    Relation.ReflTransGen (sem_step n D) c q ∨ (sem_Chain n D q c ∧ q ≠ c) := by
  revert hq
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hq => Or.inl hq
  | @head a a' hstep hrest ih =>
    intro hq
    rcases Relation.ReflTransGen.cases_head hq with heq | ⟨a'', hs, hrest'⟩
    · right
      have h1 := sem_step_lt hS hstep.1
      have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
      refine ⟨?_, by omega⟩
      rw [← heq]
      exact Relation.ReflTransGen.head hstep hrest
    · have hcc : a' = a'' := sem_step_unique hstep.1 hs hstep.2
      subst hcc
      exact ih hrest'

theorem sem_sibling_indep (hS : Strict n D) (v : Fin n) {j : ℕ} (hj : j < D.length) (s : Bool)
    (hch : sem_Chain n D v.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (x y : Fin n → Bool) (hxy : ∀ k, k ≠ v → x k = y k) :
    val D x (src D (j, s)) = val D y (src D (j, s)) := by
  by_contra hne
  have hp : Relation.ReflTransGen (sem_step n D) v.val (src D (j, s)) :=
    sem_rtg_mono (fun _ _ h => h.1) (sem_changed_path hS x y v hxy _ hne)
  have hstepc : sem_step n D (src D (j, !s)) (n + j) := sem_step_src hj (!s)
  have hstepq : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
  have hlt1 := sem_src_lt hS hj s
  have hlt2 := sem_src_lt hS hj (!s)
  rcases sem_chain_fork hS hch hp with h1 | ⟨h1, h2⟩
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨c', hs, hrest⟩
    · exact sem_src_ne hS hj s heq.symm
    · have hcc : n + j = c' := sem_step_unique hstepc hs hf
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h) hrest
      omega
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨q', hs, hrest⟩
    · exact h2 heq
    · have hcc : n + j = q' := sem_step_unique hstepq hs.1 hs.2
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h.1) hrest
      omega

theorem sem_dom_split (hS : Strict n D) (hC : sem_Comp n G D) (x : Fin n → Bool) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) (h0 : ¬ sem_Edge G x) (h1 : sem_Edge G (sem_ins v x)) :
    val D x b = false ∧ val D (sem_ins v x) b = true := by
  have hne : val D x b ≠ val D (sem_ins v x) b := by
    intro heq
    have h2 := sem_dom_eq hS x _ v (sem_ins_agree v x) b hdom heq
    exact h0 ((hC x).mp (by rw [h2]; exact (hC _).mpr h1))
  have hmono := val_mono hS x (sem_ins v x) (sem_ins_ge v x) b
  cases hx : val D x b
  · refine ⟨rfl, ?_⟩
    cases hy : val D (sem_ins v x) b
    · exact absurd (hx.trans hy.symm) hne
    · rfl
  · exact absurd (hx.trans (hmono hx).symm) hne

theorem sem_factor (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs N : Finset (Fin n)) (hN : N ⊆ Bs)
    (h0 : val D (sem_ins i (sem_ind (Bs \ N))) w = false)
    (h1 : ∀ a ∈ N, val D (sem_ins i (sem_ind {a})) w = true)
    (hz : ∀ a ∈ N, val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧ supp n D (src D (j, s)) ∩ Bs = N := by
  have hJ : ∀ c, sem_Chain n D i.val c → (val D (sem_ins i (sem_ind (Bs \ N))) c = true ∨
      ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ c ∧ sem_Chain n D i.val (src D (j, !s)) ∧
        fanout D (src D (j, !s)) = 1 ∧ val D (sem_ind (Bs \ N)) (src D (j, s)) = false) := by
    intro c hc
    induction hc with
    | refl => left; rw [val_input D _ _ i.isLt]; exact sem_ins_self i _
    | tail hab hbc ih =>
      obtain ⟨j, s, hj, rfl, rfl⟩ := sem_step_iff.mp hbc.1
      have hlt := sem_src_lt hS hj s
      rcases ih with hy | ⟨j', s', hj', ht', hle, hc', hf', hv'⟩
      · cases ht : tag D j
        · left
          rw [sem_val_gate_src hS _ hj s, ht, gop_false, hy]
          rfl
        · by_cases hq : val D (sem_ins i (sem_ind (Bs \ N))) (src D (j, !s)) = true
          · left
            rw [sem_val_gate_src hS _ hj s, ht, gop_true, hy, hq]
            rfl
          · right
            refine ⟨j, !s, hj, ht, le_refl _, by rw [Bool.not_not]; exact hab,
              by rw [Bool.not_not]; exact hbc.2, ?_⟩
            by_contra hc2
            rw [Bool.not_eq_false] at hc2
            exact hq (val_mono hS _ _ (sem_ins_ge i _) _ hc2)
      · right
        exact ⟨j', s', hj', ht', by omega, hc', hf', hv'⟩
  rcases hJ w hch with hy | ⟨j, s, hj, ht, hle, hc, hf, hv⟩
  · rw [h0] at hy
    exact absurd hy Bool.false_ne_true
  · refine ⟨j, s, hj, ht, hle, hc, ?_⟩
    have hchg : sem_Chain n D i.val (n + j) :=
      Relation.ReflTransGen.tail hc ⟨sem_step_src hj (!s), hf⟩
    ext a
    rw [Finset.mem_inter]
    constructor
    · rintro ⟨ha1, ha2⟩
      by_contra haN
      have := sem_val_of_supp hS ha1 (x := sem_ind (Bs \ N))
        (by simp [sem_ind, ha2, haN])
      rw [hv] at this
      exact Bool.false_ne_true this
    · intro haN
      refine ⟨?_, hN haN⟩
      have hgne : val D (sem_ind {a}) (n + j) ≠ val D (sem_ins i (sem_ind {a})) (n + j) := by
        intro heq
        have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (sem_ind {a})) (n + j) w
          (sem_chain_dom_at hS hchg hle) heq
        rw [hz a haN, h1 a haN] at h2
        exact Bool.false_ne_true h2
      have hgy : val D (sem_ins i (sem_ind {a})) (n + j) = true := by
        by_contra hc2
        rw [Bool.not_eq_true] at hc2
        apply hgne
        rw [hc2]
        by_contra hc3
        rw [Bool.not_eq_false] at hc3
        rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
        exact Bool.noConfusion hc2
      rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
      have hind := sem_sibling_indep hS i hj s hc hf _ _ (sem_ins_agree i (sem_ind {a}))
      rw [hgy.1, sem_ind_single] at hind
      exact mem_supp.mpr hind

theorem sem_exact_at (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs : Finset (Fin n))
    (h0 : ∀ S : Finset (Fin n), S ⊆ Bs → (∀ a ∈ S, ¬ G i a) →
      val D (sem_ins i (sem_ind S)) w = false)
    (h1 : ∀ a ∈ Bs, G i a →
      val D (sem_ins i (sem_ind {a})) w = true ∧ val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  classical
  obtain ⟨j, s, hj, ht, hle, hc, hsupp⟩ := sem_factor hS i w hch Bs (Bs.filter (fun a => G i a))
    (Finset.filter_subset _ _)
    (h0 _ Finset.sdiff_subset (fun a ha hia => by
      rw [Finset.mem_sdiff, Finset.mem_filter] at ha
      exact ha.2 ⟨ha.1, hia⟩))
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).1)
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).2)
  refine ⟨j, s, hj, ht, hle, hc, fun a ha => ?_⟩
  constructor
  · intro has
    have : a ∈ supp n D (src D (j, s)) ∩ Bs := Finset.mem_inter.mpr ⟨has, ha⟩
    rw [hsupp, Finset.mem_filter] at this
    exact this.2
  · intro hia
    have : a ∈ Bs.filter (fun a => G i a) := Finset.mem_filter.mpr ⟨ha, hia⟩
    rw [← hsupp] at this
    exact (Finset.mem_inter.mp this).1

theorem sem_branch_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {i : Fin n}
    (hi : i ∈ ineligSet n D) {b : ℕ} (hch : sem_Chain n D i.val b) (hf : 2 ≤ fanout D b) :
    supp n D b = ∅ := by
  have hsub := sem_dom_pure hG hS hC i b (sem_chain_dom hS hch)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have h1 := hsub hx
  rw [Finset.mem_singleton] at h1
  have h2 := mem_ineligSet.mp hi b (h1 ▸ hx)
  omega

theorem sem_path_chain {a t : ℕ} (hp : Relation.ReflTransGen (sem_step n D) a t) :
    sem_Chain n D a t ∨ ∃ b, sem_Chain n D a b ∧ 2 ≤ fanout D b := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @head a a' hstep _ ih =>
    by_cases hf : fanout D a = 1
    · rcases ih with h1 | ⟨b, h1, h2⟩
      · exact Or.inl (Relation.ReflTransGen.head ⟨hstep, hf⟩ h1)
      · exact Or.inr ⟨b, Relation.ReflTransGen.head ⟨hstep, hf⟩ h1, h2⟩
    · have := sem_step_fanout hstep
      exact Or.inr ⟨a, Relation.ReflTransGen.refl, by omega⟩

theorem sem_inelig_reach (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) ∨
      ∃ b, sem_Chain n D i.val b ∧ 2 ≤ fanout D b ∧ supp n D b = ∅ := by
  have hlt : i.val < n + D.length := by have := i.isLt; omega
  have hp : Relation.ReflTransGen (sem_step n D) i.val (outW n D) := live_reaches_out h i.val hlt
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨b, h1, h2, sem_branch_empty hG h.1 hC hi h1 h2⟩

theorem sem_bzero_mem (hS : Strict n D) {b : ℕ} (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) :
    b ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
  Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := b) (by omega)),
    by rw [he]; exact Finset.not_nonempty_empty⟩

theorem sem_bzero_branch (hS : Strict n D) (hB0 : Bzero n D = 0) {b : ℕ} (hf : 2 ≤ fanout D b) :
    (supp n D b).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h1 : fanout D b - 1 ≤ ∑ w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty),
      (fanout D w - 1) :=
    Finset.single_le_sum (f := fun w => fanout D w - 1) (fun _ _ => Nat.zero_le _)
      (sem_bzero_mem hS hf hne)
  unfold Bzero surplusOn at hB0
  omega

theorem sem_bzero_unique (hS : Strict n D) (hB0 : Bzero n D ≤ 1) {b b' : ℕ}
    (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) (hf' : 2 ≤ fanout D b')
    (he' : supp n D b' = ∅) : b = b' := by
  by_contra hne
  have hsub : ({b, b'} : Finset ℕ) ⊆ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) := by
    intro c hc
    rw [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact sem_bzero_mem hS hf he
    · exact sem_bzero_mem hS hf' he'
  have h1 := Finset.sum_le_sum_of_subset (f := fun w => fanout D w - 1) hsub
  rw [Finset.sum_pair hne] at h1
  unfold Bzero surplusOn at hB0
  omega

theorem sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hi h1 h2] at h3
    exact absurd h3 Finset.not_nonempty_empty

theorem sem_noempty_chain_out (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) :=
  sem_noempty_unique hG h hC hB0 hi
    (live_reaches_out h i.val (by have := i.isLt; omega))

theorem sem_exact_nbhd (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i : Fin n}
    (hch : sem_Chain n D i.val (outW n D)) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  obtain ⟨j, s, hj, ht, -, hc, hsupp⟩ := sem_exact_at (G := G) hS i (outW n D) hch Bs
    (fun S hS1 hS2 => by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rcases sem_ins_ind_edge hG ((hC _).mp hc) with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
      · exact hS2 a ha hia
      · exact hBs a (hS1 ha) b (hS1 hb) hab)
    (fun a _ hia => by
      constructor
      · exact (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
      · by_contra hc
        rw [Bool.not_eq_false, sem_ind_single] at hc
        exact sem_single_no_edge hG a ((hC _).mp hc))
  exact ⟨j, s, hj, ht, hc, hsupp⟩

theorem sem_shared_exact (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i j : Fin n} {w : ℕ}
    (hch : sem_Chain n D i.val w) (hdj : sem_Dom n D w j.val)
    (hnsub : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    ∃ k s, k < D.length ∧ tag D k = true ∧ n + k ≤ w ∧
      sem_Chain n D i.val (src D (k, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a) := by
  classical
  have hX0 : ¬ sem_Edge G (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) := by
    intro hc
    rcases sem_ins_ind_edge hG hc with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
    · exact (Finset.mem_filter.mp ha).2 hia
    · exact hBs a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  obtain ⟨a0, ha0, hja0, hia0⟩ := hnsub
  have hX1 : sem_Edge G (sem_ins j (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a))))) :=
    ⟨j, a0, hja0, sem_ins_self j _, by simp [sem_ins, sem_ind, ha0, hia0]⟩
  have hwX := (sem_dom_split hS hC _ j w hdj hX0 hX1).1
  refine sem_exact_at hS i w hch Bs (fun S hS1 hS2 => ?_) (fun a _ hia => ?_)
  · by_contra hc
    rw [Bool.not_eq_false] at hc
    have hmono := val_mono hS (sem_ins i (sem_ind S))
      (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) (fun k hk => by
        simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hk ⊢
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (Finset.mem_filter.mpr ⟨hS1 hk, hS2 k hk⟩)) w hc
    rw [hwX] at hmono
    exact Bool.false_ne_true hmono
  · have h2 := sem_dom_split hS hC (sem_ind {a}) i w (sem_chain_dom hS hch)
      (by rw [sem_ind_single]; exact sem_single_no_edge hG a)
      ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
    exact ⟨h2.2, h2.1⟩

theorem sem_shared_empty (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D ≤ 1) (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b)
    {i j : Fin n} (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    (hji : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain n D i.val (src D (k, !s)) ∧
        ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a)) ∨
      (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain n D j.val (src D (k, !s)) ∧
        ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G j a)) := by
  have hS := h.1
  rcases sem_inelig_reach hG h hC hi with h1 | ⟨b, hb1, hb2, hb3⟩
  · exact Or.inl (sem_exact_nbhd hG hS hC Bs hBs h1)
  · rcases sem_inelig_reach hG h hC hj with h1 | ⟨b', hb1', hb2', hb3'⟩
    · exact Or.inr (sem_exact_nbhd hG hS hC Bs hBs h1)
    · have hbb : b' = b := sem_bzero_unique hS hB0 hb2' hb3' hb2 hb3
      rw [hbb] at hb1'
      obtain ⟨k, s, hk, ht, -, hc, hsupp⟩ := sem_shared_exact hG hS hC Bs hBs hb1
        (sem_chain_dom hS hb1') hji
      exact Or.inl ⟨k, s, hk, ht, hc, hsupp⟩

theorem sem_full_support (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool} (he : sem_W n D i = {e})
    (hor : ∀ j, Relation.ReflTransGen (sem_step n D) (n + e.1) (n + j) → j ≠ e.1 →
      tag D j = false) :
    ∀ t, t ∈ supp n D (src D (sem_bar e)) ↔ G i t := by
  have hS := h.1
  obtain ⟨e0, hj0, ht0, hsrc0, hemp0, hnb0, hx0, -⟩ := sem_inelig_consumer hG h hC hi
  have hee : e = e0 := Finset.singleton_injective (he.symm.trans hx0)
  subst hee
  obtain ⟨g, s⟩ := e
  intro t
  refine ⟨fun ht => ?_, fun ht => hnb0 t ht⟩
  by_contra hnt
  have hgate : val D (sem_two i t) (n + g) = true := by
    rw [sem_val_gate_src hS _ hj0 s, ht0, gop_true, Bool.and_eq_true]
    exact ⟨sem_val_of_supp hS (by rw [hsrc0]; exact Finset.mem_singleton_self i)
      (by simp [sem_two]), sem_val_of_supp hS ht (by simp [sem_two])⟩
  have hall : ∀ c, Relation.ReflTransGen (sem_step n D) (n + g) c →
      val D (sem_two i t) c = true := by
    intro c hc
    induction hc with
    | refl => exact hgate
    | tail hab hbc ih =>
      obtain ⟨j, s', hj, rfl, rfl⟩ := sem_step_iff.mp hbc
      have hne : j ≠ g := by
        have := sem_rtg_le hS (fun _ _ h => h) hab
        have := sem_src_lt hS hj s'
        omega
      rw [sem_val_gate_src hS _ hj s', hor j (Relation.ReflTransGen.tail hab hbc) hne,
        gop_false, ih]
      rfl
  have hout := hall _ (live_reaches_out h (n + g) (by omega))
  obtain ⟨u, v, huv, hu, hv⟩ := (hC _).mp hout
  simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv] at huv
  · exact hG.2.1 _ huv
  · exact hnt huv
  · exact hnt (hG.1 _ _ huv)
  · exact hG.2.1 _ huv

end SemPaths

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_diff {x y : Fin n} {w : ℕ} :
    w ∈ carrierDiff n D x y ↔ x ∈ supp n D w ∧ y ∉ supp n D w := by
  simp only [carrierDiff, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨sem_supp_lt h.1, h⟩⟩

theorem sem_mem_exit_diff {x y : Fin n} {e : ℕ × Bool} :
    e ∈ exitArcs n D (carrierDiff n D x y) ↔ e.1 < D.length ∧
      (x ∈ supp n D (src D e) ∧ y ∉ supp n D (src D e)) ∧
      ¬ (x ∈ supp n D (n + e.1) ∧ y ∉ supp n D (n + e.1)) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_diff]

theorem sem_surplus_diff (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    {x y : Fin n} (hxy : x ≠ y) (hx : x ∈ eligSet n D) :
    surplusOn D (carrierDiff n D x y) = 1 + ((residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
  have h1 : surplusOn D (carrierDiff n D x y) =
      ((units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
    rw [sb_card_units_filter n D (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      exact sem_mem_diff.mpr hw.2
    · have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, sem_mem_diff.mp hw⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) =
      {(⟨b x, 0⟩ : Σ _ : ℕ, ℕ)} ∪ (residualUnits n D b).filter
        (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_singleton]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · left
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
        have hxv := hu.2.1
        rw [(hb v hv).2, Finset.mem_singleton] at hxv
        rw [hxv]
      · exact Or.inr ⟨⟨⟨hu.1, ⟨x, hu.2.1⟩⟩, hr⟩, hu.2⟩
    · rintro (rfl | hu)
      · have hbx := hb x hx
        refine ⟨(Finset.mem_filter.mp (hsub (Finset.mem_image.mpr ⟨x, hx, rfl⟩))).1, ?_, ?_⟩
        · rw [hbx.2]; exact Finset.mem_singleton_self x
        · rw [hbx.2, Finset.mem_singleton]; exact fun hc => hxy hc.symm
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : (⟨b x, 0⟩ : Σ _ : ℕ, ℕ) ∉ (residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    intro hc
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).2 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [h1, h2, Finset.singleton_union, Finset.card_insert_of_notMem h3]
  omega

theorem sem_first_joint (hS : Strict n D) {x y : Fin n} (hxy : x ≠ y) {w : ℕ}
    (hw : x ∈ supp n D w ∧ y ∈ supp n D w) :
    ∃ j s, j < D.length ∧ tag D j = false ∧ x ∈ supp n D (n + j) ∧ y ∈ supp n D (n + j) ∧
      x ∈ supp n D (src D (j, s)) ∧ y ∉ supp n D (src D (j, s)) ∧
      y ∈ supp n D (src D (j, !s)) ∧ x ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ u, x ∈ supp n D u ∧ y ∈ supp n D u := ⟨w, hw⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hmin : ∀ u, u < Nat.find hex → ¬ (x ∈ supp n D u ∧ y ∈ supp n D u) :=
    fun u hu => Nat.find_min hex hu
  generalize Nat.find hex = f at h1 h2 hmin
  have hlt := sem_supp_lt h1
  have hn : n ≤ f := by
    by_contra hc
    have hs : supp n D f = {⟨f, by omega⟩} := supp_input D ⟨f, by omega⟩
    rw [hs, Finset.mem_singleton] at h1 h2
    exact hxy (h1.trans h2.symm)
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  cases ht : tag D j
  · have h1' := h1
    have h2' := h2
    rw [sem_supp_or hS hj ht, Finset.mem_union] at h1' h2'
    refine ⟨j, ?_⟩
    rcases h1' with hxa | hxb
    · have hya : y ∉ supp n D (opA D j) := fun hc => hna ⟨hxa, hc⟩
      have hyb : y ∈ supp n D (opB D j) := h2'.resolve_left hya
      exact ⟨false, hj, ht, h1, h2, by simpa [src] using hxa, by simpa [src] using hya,
        by simpa [src] using hyb, by simpa [src] using fun hc => hnb ⟨hc, hyb⟩⟩
    · have hyb : y ∉ supp n D (opB D j) := fun hc => hnb ⟨hxb, hc⟩
      have hya : y ∈ supp n D (opA D j) := h2'.resolve_right hyb
      exact ⟨true, hj, ht, h1, h2, by simpa [src] using hxb, by simpa [src] using hyb,
        by simpa [src] using hya, by simpa [src] using fun hc => hna ⟨hc, hya⟩⟩
  · exfalso
    rw [sem_supp_and hS hj ht, Finset.mem_inter] at h1 h2
    exact hna ⟨h1.1, h2.1⟩

theorem sem_diff_two_exits (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {x c z : Fin n} (hxc : x ≠ c)
    (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1)
    {w : ℕ} (hw : x ∈ supp n D w ∧ c ∈ supp n D w) (hxz : G x z) (hcz : ¬ G c z) :
    surplusOn D (carrierDiff n D x c) = 1 ∧ merges n D (carrierDiff n D x c) = ∅ ∧
      (exitArcs n D (carrierDiff n D x c)).card = 2 ∧
      ∃ e ∈ exitArcs n D (carrierDiff n D x c), tag D e.1 = false ∧ c ∈ supp n D (n + e.1) := by
  have hS := h.1
  have hsur : surplusOn D (carrierDiff n D x c) = 1 := by
    rw [sem_surplus_diff hS b hb hxc hx, Finset.filter_eq_empty_iff.mpr
      (fun u hu hc => hc.2 (hres u hu hc.1)), Finset.card_empty]
  have hfl := carrier_flow_diff h x c hxc
    (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  rw [hsur] at hfl
  obtain ⟨j1, s1, hj1, ht1, hx1, hc1, hxs1, hcs1, -, -⟩ := sem_first_joint hS hxc hw
  have he1 : (j1, s1) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj1, ⟨hxs1, hcs1⟩, fun hc => hc.2 hc1⟩
  have hA : ∀ u ∈ ({c, z} : Finset (Fin n)), ∀ v ∈ ({c, z} : Finset (Fin n)), ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
    · exact hG.2.1 c
    · exact hcz
    · exact fun hc => hcz (hG.1 _ _ hc)
    · exact hG.2.1 z
  obtain ⟨j2, s2, hj2, -, hx2, hn2, hd2⟩ := sem_exposure hG hS hC {c, z} hA x ⟨z, by simp, hxz⟩
  have he2 : (j2, s2) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj2, ⟨hx2, fun hc => Finset.disjoint_left.mp hd2 hc (by simp)⟩,
      fun hc => hn2 hc.1⟩
  have hne : (j1, s1) ≠ (j2, s2) := by
    intro heq
    rw [Prod.mk.injEq] at heq
    exact hn2 (heq.1 ▸ hx1)
  have h2 : 2 ≤ (exitArcs n D (carrierDiff n D x c)).card :=
    Finset.one_lt_card.mpr ⟨_, he1, _, he2, hne⟩
  exact ⟨hsur, Finset.card_eq_zero.mp (by omega), by omega, (j1, s1), he1, ht1, hc1⟩

theorem sem_and_sibling_nbrs (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {j : ℕ} (hj : j < D.length) (s : Bool) (ht : tag D j = true)
    (hch : sem_Chain n D i.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (hout : n + j ≤ outW n D) {a : Fin n} (hia : G i a) : a ∈ supp n D (src D (j, s)) := by
  have hchg : sem_Chain n D i.val (n + j) :=
    Relation.ReflTransGen.tail hch ⟨sem_step_src hj (!s), hf⟩
  have hx0 : val D (single a) (outW n D) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact sem_single_no_edge hG a ((hC _).mp hc)
  have hy1 : val D (sem_ins i (single a)) (outW n D) = true :=
    (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, single]⟩
  have hgy : val D (sem_ins i (single a)) (n + j) = true := by
    by_contra hc2
    rw [Bool.not_eq_true] at hc2
    have hgx : val D (single a) (n + j) = false := by
      by_contra hc3
      rw [Bool.not_eq_false] at hc3
      rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
      exact Bool.noConfusion hc2
    have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (single a)) (n + j) (outW n D)
      (sem_chain_dom_at hS hchg hout) (hgx.trans hc2.symm)
    rw [hx0, hy1] at h2
    exact Bool.false_ne_true h2
  rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
  have hind := sem_sibling_indep hS i hj s hch hf _ _ (sem_ins_agree i (single a))
  rw [hgy.1] at hind
  exact mem_supp.mpr hind

end SemDiff

def k4_Pos (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) (pos : Fin n → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet n D, (pos i).1 < D.length ∧ supp n D (n + (pos i).1) = ∅ ∧
    (∀ a, G i a → a ∈ supp n D (src D (pos i))) ∧
    supp n D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ∀ i ∈ ineligSet n D, ∀ i' ∈ ineligSet n D, pos i = pos i' → i = i'

theorem k4_assigned {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag} (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) :
    ∃ pos : Fin n → ℕ × Bool, k4_Pos n G D pos := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ ineligSet n D → (e.1 < D.length ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G i a → a ∈ supp n D (src D e)) ∧
      supp n D (src D (e.1, !e.2)) = {i}) := by
    intro i
    by_cases hi : i ∈ ineligSet n D
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC hi
      exact ⟨(e.1, !e.2), fun _ => ⟨h1, h4, h5, by simpa using h3⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose pos hpos using hex
  refine ⟨pos, hpos, fun i hi i' hi' he => ?_⟩
  have h1 := (hpos i hi).2.2.2
  rw [he, (hpos i' hi').2.2.2] at h1
  exact (Finset.singleton_injective h1).symm

section L3bGen

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem ri_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) {x c : Fin n} (hxc : x ≠ c) (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1) {w : ℕ}
    (hw : x ∈ supp n D w ∧ c ∈ supp n D w) :
    ∃ e0, ∀ e ∈ sem_W n D x, e ≠ e0 → c ∈ supp n D (src D e) := by
  classical
  obtain ⟨z, hxz, hcz⟩ := hG.2.2.1 x c hxc
  obtain ⟨-, -, h2, e1, he1, ht1, -⟩ := sem_diff_two_exits hG h hC b hb hxc hx hres hw hxz hcz
  have hc1 : ((exitArcs n D (carrierDiff n D x c)).erase e1).card = 1 := by
    rw [Finset.card_erase_of_mem he1, h2]
  obtain ⟨e0, he0⟩ := Finset.card_eq_one.1 hc1
  refine ⟨e0, fun e he hne => ?_⟩
  by_contra hce
  obtain ⟨h1, h4, h5⟩ := sem_mem_W.1 he
  have hm : e ∈ (exitArcs n D (carrierDiff n D x c)).erase e1 :=
    Finset.mem_erase.2 ⟨fun heq => by
      have := sem_W_and h.1 he
      rw [heq, ht1] at this
      exact Bool.false_ne_true this, sem_mem_exit_diff.2 ⟨h1, ⟨h4, hce⟩, fun hc => h5 hc.1⟩⟩
  rw [he0, Finset.mem_singleton] at hm
  exact hne hm

theorem zm_mem (hS : Strict n D) {c : Fin n} (hM : merges n D (carrierT n D {c}) = ∅)
    {e : ℕ × Bool} (he : e.1 < D.length) (ht : tag D e.1 = true)
    (hc : c ∈ supp n D (src D e)) : e ∈ sem_W n D c :=
  sem_mem_W.2 ⟨he, hc, fun hc2 => by
    have := (sem_zm_gate hS hM he hc2).1
    rw [ht] at this
    exact Bool.noConfusion this⟩

theorem gct_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : sem_MinBranch n D b) {u0 : Σ _ : ℕ, ℕ} (hu0 : u0 ∈ residualUnits n D b)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hsat : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅ ∧ x ∈ supp n D u0.1 ∧
      ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → u = u0) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  have hS := h.1
  have hu0u : u0 ∈ units n D := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by
    have := (mem_units.mp hu0u).2
    omega
  refine sem_two_arms hG h hC X hX (fun x hx => (hsat x hx).1) u0.1
    (fun x hx => (hsat x hx).2.1) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨-, hxr, huniq⟩ := hsat x hx
  have hxe : x ∈ eligSet n D := mem_eligSet.2 ⟨u0.1, hfr, hxr⟩
  by_contra hc
  have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    rw [unitsPlus, Finset.mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
      by show 0 + 1 < fanout D w; omega⟩, ⟨x, hxw⟩⟩
  by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits n D b
  · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
    have hbv : b v = w := congrArg Sigma.fst hveq
    have hsv := (hb v hv).2.1
    rw [hbv] at hsv
    rw [hsv, Finset.mem_singleton] at hxw
    have hmin := (hb x hxe).2.2.2 u0.1 hfr hxr
    rw [hxw, hbv] at hmin
    omega
  · have h1 := huniq _ (Finset.mem_sdiff.mpr ⟨hwu, hwr⟩) hxw
    have : w = u0.1 := congrArg Sigma.fst h1
    omega

theorem full_gen (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i v : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool}
    (he : sem_W n D i = {e}) (hiv : G i v)
    (hv : ∀ p ∈ sem_W n D v, p.1 ≠ e.1 → ¬ supp n D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp n D (src D (sem_bar e)) ↔ G i t := by
  have hS := h.1
  refine sem_full_support hG h hC hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W n D i := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step n D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := sem_noempty_unique hG h hC hB0 hi hreach2
    have hf : fanout D w = 1 := by
      have h1 := sem_step_fanout hw2
      by_contra hne
      have h2 := sem_branch_empty hG hS hC hi hch (by omega)
      have h4 := sem_bzero_branch hS hB0 (b := w) (by omega)
      rw [h2] at h4
      exact Finset.not_nonempty_empty h4
    have hsub : supp n D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp n D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W n D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (Finset.mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)

end L3bGen

abbrev G10 : Fin 10 → Fin 10 → Prop := fun u v => Adj u v

def ru (D : Dag) (b : Fin 10 → ℕ) (x : Fin 10) : Finset (Σ _ : ℕ, ℕ) :=
  (residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)

theorem mem_ru {D : Dag} {b : Fin 10 → ℕ} {x : Fin 10} {u : Σ _ : ℕ, ℕ} :
    u ∈ ru D b x ↔ u ∈ residualUnits 10 D b ∧ x ∈ supp 10 D u.1 := by
  simp [ru]

theorem cc_le {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (b : Fin 10 → ℕ)
    (hb : PureBranch 10 D b) (x : Fin 10) :
    (sem_W 10 D x).card + (merges 10 D (carrierT 10 D {x})).card ≤ 2 + (ru D b x).card := by
  have h1 := sem_code_count sem_g10_gr h (sem_g10_comp hD) b hb x
  have h2 := Finset.card_le_card
    (Finset.inter_subset_left : ({x} : Finset (Fin 10)) ∩ eligSet 10 D ⊆ {x})
  rw [Finset.card_singleton] at h2
  unfold ru
  omega

theorem w_bar {n : ℕ} {D : Dag} (hS : Strict n D) {x : Fin n} {e : ℕ × Bool}
    (he : e ∈ sem_W n D x) : sem_bar e ∉ sem_W n D x := by
  intro hb
  obtain ⟨hj, hx, hn⟩ := sem_mem_W.mp he
  have hx' := (sem_mem_W.mp hb).2.1
  apply hn
  rw [sem_supp_and hS hj (sem_W_and hS he), Finset.mem_inter]
  obtain ⟨j, s⟩ := e
  cases s
  · exact ⟨by simpa [src] using hx, by simpa [src, sem_bar] using hx'⟩
  · exact ⟨by simpa [src, sem_bar] using hx', by simpa [src] using hx⟩

theorem as_mem {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {i a : Fin 10} (hi : i ∈ ineligSet 10 D) (hia : Adj i a) : pos i ∈ sem_W 10 D a := by
  obtain ⟨h1, h2, h4, -⟩ := hpos.1 i hi
  exact sem_mem_W.2 ⟨h1, h4 a hia, by rw [h2]; exact Finset.notMem_empty a⟩

theorem as_priv {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {i x : Fin 10} (hi : i ∈ ineligSet 10 D) (h : sem_bar (pos i) ∈ sem_W 10 D x) : x = i := by
  have h1 := (sem_mem_W.1 h).2.1
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl,
    (hpos.1 i hi).2.2.2] at h1
  exact Finset.mem_singleton.1 h1

theorem pos_bar_mem {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {i : Fin 10} (hi : i ∈ ineligSet 10 D) : i ∈ supp 10 D (src D (sem_bar (pos i))) := by
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl,
    (hpos.1 i hi).2.2.2]
  exact Finset.mem_singleton_self i

theorem as_W {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {i : Fin 10} (hi : i ∈ ineligSet 10 D) :
    sem_W 10 D i = {sem_bar (pos i)} := by
  obtain ⟨e, -, -, -, -, -, h6, -⟩ :=
    sem_inelig_consumer sem_g10_gr h (sem_g10_comp hD) hi
  obtain ⟨h1, h2, -, h5⟩ := hpos.1 i hi
  have hm : sem_bar (pos i) ∈ sem_W 10 D i :=
    sem_mem_W.2 ⟨h1, by
      rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, h5]
      exact Finset.mem_singleton_self i, by
      rw [show (sem_bar (pos i)).1 = (pos i).1 from rfl, h2]; exact Finset.notMem_empty i⟩
  have h7 : sem_W 10 D i = {e} := h6
  rw [h7] at hm ⊢
  rw [Finset.mem_singleton.1 hm]

theorem full_g10 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos) {i v : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hiv : Adj i v)
    (hv : ∀ p ∈ sem_W 10 D v, p.1 ≠ (pos i).1 → ¬ supp 10 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 10 D (src D (pos i)) ↔ Adj i t := by
  have := full_gen sem_g10_gr h (sem_g10_comp hD) hB0 hi (as_W h hD hpos hi) hiv hv
  rwa [sem_bar_bar] at this

theorem pa_card3 {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this

theorem pa_card4 {α : Type} [DecidableEq α] {s : Finset α} {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ s.card := by
  have hsub : ({a, b, c, d} : Finset α) ⊆ s := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd] at this

theorem pa_card5 {α : Type} [DecidableEq α] {s : Finset α} {a b c d e : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (he : e ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    5 ≤ s.card := by
  have hsub : ({a, b, c, d, e} : Finset α) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem (by simp [hab, hac, had, hae]),
    Finset.card_insert_of_notMem (by simp [hbc, hbd, hbe]),
    Finset.card_insert_of_notMem (by simp [hcd, hce]), Finset.card_pair hde] at this

theorem pa_two {α : Type} [DecidableEq α] {s : Finset α} {a b : α} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (hs : s.card ≤ 2) : ∀ e ∈ s, e = a ∨ e = b := by
  intro e he
  by_contra hne
  rw [not_or] at hne
  have := pa_card3 he ha hb hne.1 hne.2 hab
  omega

theorem pa_three {α : Type} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hs : s.card ≤ 3) :
    ∀ e ∈ s, e = a ∨ e = b ∨ e = c := by
  intro e he
  by_contra hne
  rw [not_or, not_or] at hne
  have := pa_card4 he ha hb hc hne.1 hne.2.1 hne.2.2 hab hac hbc
  omega

theorem pa_four {α : Type} [DecidableEq α] {s : Finset α} {a b c d : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hs : s.card ≤ 4) : ∀ e ∈ s, e = a ∨ e = b ∨ e = c ∨ e = d := by
  intro e he
  by_contra hne
  rw [not_or, not_or, not_or] at hne
  have := pa_card5 he ha hb hc hd hne.1 hne.2.1 hne.2.2.1 hne.2.2.2 hab hac had hbc hbd hcd
  omega

theorem pa_ed {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {x y : Fin 10} (hxy : Adj x y) :
    ∃ e ∈ sem_W 10 D x, sem_bar e ∈ sem_W 10 D y ∧
      (∀ i ∈ ineligSet 10 D, e = pos i → y = i) ∧
      ∀ i ∈ ineligSet 10 D, sem_bar e = pos i → x = i := by
  obtain ⟨e, he, hb, -⟩ := sem_edge_slots sem_g10_gr h.1 (sem_g10_comp hD) hxy
  exact ⟨e, he, hb, fun i hi hei => as_priv hpos hi (hei ▸ hb),
    fun i hi hei => as_priv hpos hi (by rw [← hei, sem_bar_bar]; exact he)⟩

theorem g10_deg3_third : ∀ x a b : Fin 10, (g10_nbB x).card = 3 →
    x ≠ a → x ≠ b → hc_adjB a b = false →
    ∃ y, hc_adjB x y = true ∧ hc_adjB y a = false ∧ hc_adjB y b = false := by decide +kernel

theorem g10_deg3_cover_free {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {x a b : Fin 10}
    (hd : (g10_nbB x).card = 3) (hxa : x ≠ a) (hxb : x ≠ b) (hab : ¬ Adj a b) :
    ∃ e, e ∈ sem_W 10 D x ∧ a ∉ supp 10 D (src D e) ∧ b ∉ supp 10 D (src D e) := by
  obtain ⟨y, h1, h2, h3⟩ := g10_deg3_third x a b hd hxa hxb (sem_adjB_false.mpr hab)
  exact sem_cover_free sem_g10_gr h.1 (sem_g10_comp hD) hab ((hc_adjB_iff x y).mp h1)
    (sem_adjB_false.mp h2) (sem_adjB_false.mp h3)

theorem ps_nonadj {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {i x r : Fin 10} (hi : i ∈ ineligSet 10 D)
    (hix : Adj i x) (hir : Adj i r) (hrx : r ≠ x) (hdx : (g10_nbB x).card = 3)
    (hc : (sem_W 10 D x).card ≤ 2) :
    ∃ Z, Z ≠ pos i ∧ sem_W 10 D x = {pos i, Z} ∧
      ∀ t, t ≠ x → ¬ Adj r t → Z ∉ sem_W 10 D t := by
  obtain ⟨Z, hZ, hZr⟩ := sem_antichain sem_g10_gr h.1 (sem_g10_comp hD) (x := x) (a := r) (Ne.symm hrx)
  have hY : pos i ∈ sem_W 10 D x := as_mem hpos hi hix
  have hZY : Z ≠ pos i := fun heq => hZr (heq ▸ (hpos.1 i hi).2.2.1 r hir)
  have hW : sem_W 10 D x = {pos i, Z} := by
    symm
    refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
    · rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact hY
      · exact hZ
    · rw [Finset.card_pair (Ne.symm hZY)]; exact hc
  refine ⟨Z, hZY, hW, fun t htx hrt hZt => ?_⟩
  obtain ⟨f, hf, h1, h2⟩ := g10_deg3_cover_free h hD hdx (Ne.symm hrx) (Ne.symm htx) hrt
  rw [hW, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with rfl | rfl
  · exact h1 ((hpos.1 i hi).2.2.1 r hir)
  · exact h2 (sem_mem_W.1 hZt).2.1

theorem two_in_deg3 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {i1 i2 u v : Fin 10}
    (hi1 : i1 ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true ∧
      v ≠ i1 ∧ v ≠ i2) : 3 ≤ (sem_W 10 D u).card := by
  obtain ⟨hne, h1, h2, h3, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3
  have p1 := as_mem hpos hi1 h1
  have p2 := as_mem hpos hi2 h2
  have p12 : pos i1 ≠ pos i2 := fun e => hne (hpos.2 i1 hi1 i2 hi2 e)
  by_cases hv : v ∈ ineligSet 10 D
  · exact pa_card3 p1 p2 (as_mem hpos hv (adj_symm h3)) p12
      (fun e => hv1.symm (hpos.2 i1 hi1 v hv e)) (fun e => hv2.symm (hpos.2 i2 hi2 v hv e))
  · obtain ⟨e, he, -, hf, -⟩ := pa_ed h hD hpos h3
    exact pa_card3 p1 p2 he p12 (fun hh => hv (hf i1 hi1 hh.symm ▸ hi1))
      (fun hh => hv (hf i2 hi2 hh.symm ▸ hi2))

theorem pa_m1_gen {D : Dag} (h : StrictLive 10 D) (hD : Correct D) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) (z k v iz ik r : Fin 10)
    (hiz : iz ∈ ineligSet 10 D) (hik : ik ∈ ineligSet 10 D)
    (hz : z ∉ ineligSet 10 D) (hk : k ∉ ineligSet 10 D) (hv : v ∉ ineligSet 10 D)
    (hg : hc_adjB iz z = true ∧ hc_adjB ik k = true ∧ hc_adjB z k = true ∧
      hc_adjB z v = true ∧ v ≠ k ∧ (g10_nbB k).card = 3 ∧
      hc_adjB ik r = true ∧ r ≠ k ∧ hc_adjB r v = false)
    (hcz : (sem_W 10 D z).card ≤ 2) (hck : (sem_W 10 D k).card ≤ 2) : False := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3 g4 g7
  obtain ⟨Dk, -, hWk, hpk⟩ := ps_nonadj h hD hpos hik g2 g7 g8 g6 hck
  obtain ⟨e, he, hbe, hf, hf'⟩ := pa_ed h hD hpos g3
  obtain ⟨e', he', hbe', hg', -⟩ := pa_ed h hD hpos g4
  rw [hWk, Finset.mem_insert, Finset.mem_singleton] at hbe
  have hb : sem_bar e = Dk := hbe.resolve_left (fun hh => hz (hf' ik hik hh ▸ hik))
  rcases pa_two (as_mem hpos hiz g1) he (fun hh => hk (hf iz hiz hh.symm ▸ hiz)) hcz e' he'
    with h1 | h1
  · exact hv (hg' iz hiz h1 ▸ hiz)
  · exact hpk v g5 (sem_adjB_false.1 g9) (by rw [← hb, ← h1]; exact hbe')

theorem ps_3star_gen {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    (u k1 k2 v ik1 ik2 r1 r2 : Fin 10)
    (hik1 : ik1 ∈ ineligSet 10 D) (hik2 : ik2 ∈ ineligSet 10 D)
    (hu : u ∉ ineligSet 10 D)
    (hg : hc_adjB u k1 = true ∧ hc_adjB u k2 = true ∧ hc_adjB u v = true ∧
      hc_adjB ik1 k1 = true ∧ hc_adjB ik2 k2 = true ∧
      k1 ≠ k2 ∧ v ≠ k1 ∧ v ≠ k2 ∧ (g10_nbB k1).card = 3 ∧ (g10_nbB k2).card = 3 ∧
      hc_adjB ik1 r1 = true ∧ r1 ≠ k1 ∧ hc_adjB r1 k2 = false ∧ hc_adjB r1 v = false ∧
      hc_adjB ik2 r2 = true ∧ r2 ≠ k2 ∧ hc_adjB r2 v = false)
    (hcu : (sem_W 10 D u).card ≤ 2) (hck1 : (sem_W 10 D k1).card ≤ 2)
    (hck2 : (sem_W 10 D k2).card ≤ 2) : False := by
  obtain ⟨g1, g2, g3, g4, g5, hk12, hvk1, hvk2, hd1, hd2, hr1a, hr1n, hr1k2, hr1v, hr2a, hr2n, hr2v⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3 g4 g5 hr1a hr2a
  obtain ⟨D1, -, hW1, hp1⟩ := ps_nonadj h hD hpos hik1 g4 hr1a hr1n hd1 hck1
  obtain ⟨D2, -, hW2, hp2⟩ := ps_nonadj h hD hpos hik2 g5 hr2a hr2n hd2 hck2
  obtain ⟨e1, he1, hbe1, -, hf1'⟩ := pa_ed h hD hpos g1
  obtain ⟨e2, he2, hbe2, -, hf2'⟩ := pa_ed h hD hpos g2
  obtain ⟨ev, hev, hbev, -, -⟩ := pa_ed h hD hpos g3
  rw [hW1, Finset.mem_insert, Finset.mem_singleton] at hbe1
  rw [hW2, Finset.mem_insert, Finset.mem_singleton] at hbe2
  have hb1 : sem_bar e1 = D1 := hbe1.resolve_left (fun hh => hu (hf1' ik1 hik1 hh ▸ hik1))
  have hb2 : sem_bar e2 = D2 := hbe2.resolve_left (fun hh => hu (hf2' ik2 hik2 hh ▸ hik2))
  have hne : e1 ≠ e2 := fun hh =>
    hp1 k2 hk12.symm (sem_adjB_false.1 hr1k2) (by rw [← hb1, hh, hb2, hW2]; simp)
  rcases pa_two he1 he2 hne hcu ev hev with rfl | rfl
  · exact hp1 v hvk1 (sem_adjB_false.1 hr1v) (hb1 ▸ hbev)
  · exact hp2 v hvk2 (sem_adjB_false.1 hr2v) (hb2 ▸ hbev)

theorem ps_3star_cyc {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    (u k1 k2 k3 ik1 ik2 ik3 r1 r2 r3 : Fin 10)
    (hik1 : ik1 ∈ ineligSet 10 D) (hik2 : ik2 ∈ ineligSet 10 D) (hik3 : ik3 ∈ ineligSet 10 D)
    (hu : u ∉ ineligSet 10 D)
    (hg : hc_adjB u k1 = true ∧ hc_adjB u k2 = true ∧ hc_adjB u k3 = true ∧
      hc_adjB ik1 k1 = true ∧ hc_adjB ik2 k2 = true ∧ hc_adjB ik3 k3 = true ∧
      k1 ≠ k2 ∧ k2 ≠ k3 ∧ k3 ≠ k1 ∧
      (g10_nbB k1).card = 3 ∧ (g10_nbB k2).card = 3 ∧ (g10_nbB k3).card = 3 ∧
      hc_adjB ik1 r1 = true ∧ r1 ≠ k1 ∧ hc_adjB r1 k3 = false ∧
      hc_adjB ik2 r2 = true ∧ r2 ≠ k2 ∧ hc_adjB r2 k1 = false ∧
      hc_adjB ik3 r3 = true ∧ r3 ≠ k3 ∧ hc_adjB r3 k2 = false)
    (hcu : (sem_W 10 D u).card ≤ 2)
    (hck1 : (sem_W 10 D k1).card ≤ 2) (hck2 : (sem_W 10 D k2).card ≤ 2)
    (hck3 : (sem_W 10 D k3).card ≤ 2) : False := by
  obtain ⟨g1, g2, g3, g4, g5, g6, h12, h23, h31, hd1, hd2, hd3,
    hr1a, hr1n, hr13, hr2a, hr2n, hr21, hr3a, hr3n, hr32⟩ := hg
  rw [hc_adjB_iff] at g1 g2 g3 g4 g5 g6 hr1a hr2a hr3a
  obtain ⟨D1, -, hW1, hp1⟩ := ps_nonadj h hD hpos hik1 g4 hr1a hr1n hd1 hck1
  obtain ⟨D2, -, hW2, hp2⟩ := ps_nonadj h hD hpos hik2 g5 hr2a hr2n hd2 hck2
  obtain ⟨D3, -, hW3, hp3⟩ := ps_nonadj h hD hpos hik3 g6 hr3a hr3n hd3 hck3
  obtain ⟨e1, he1, hbe1, -, hf1'⟩ := pa_ed h hD hpos g1
  obtain ⟨e2, he2, hbe2, -, hf2'⟩ := pa_ed h hD hpos g2
  obtain ⟨e3, he3, hbe3, -, hf3'⟩ := pa_ed h hD hpos g3
  rw [hW1, Finset.mem_insert, Finset.mem_singleton] at hbe1
  rw [hW2, Finset.mem_insert, Finset.mem_singleton] at hbe2
  rw [hW3, Finset.mem_insert, Finset.mem_singleton] at hbe3
  have hb1 : sem_bar e1 = D1 := hbe1.resolve_left (fun hh => hu (hf1' ik1 hik1 hh ▸ hik1))
  have hb2 : sem_bar e2 = D2 := hbe2.resolve_left (fun hh => hu (hf2' ik2 hik2 hh ▸ hik2))
  have hb3 : sem_bar e3 = D3 := hbe3.resolve_left (fun hh => hu (hf3' ik3 hik3 hh ▸ hik3))
  have h12' : e1 ≠ e2 := fun hh =>
    hp2 k1 h12 (sem_adjB_false.1 hr21) (by rw [← hb2, ← hh, hb1, hW1]; simp)
  have h23' : e2 ≠ e3 := fun hh =>
    hp3 k2 h23 (sem_adjB_false.1 hr32) (by rw [← hb3, ← hh, hb2, hW2]; simp)
  have h13' : e1 ≠ e3 := fun hh =>
    hp1 k3 h31 (sem_adjB_false.1 hr13) (by rw [← hb1, hh, hb3, hW3]; simp)
  have := pa_card3 he1 he2 he3 h12' h13' h23'
  omega

theorem ru_one_two_supp {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (b : Fin 10 → ℕ) (hb : sem_MinBranch 10 D b) {x : Fin 10} {u0 : Σ _ : ℕ, ℕ}
    (hM : merges 10 D (carrierT 10 D {x}) = ∅) (hru : ru D b x = {u0}) :
    ∃ e1 e2 : ℕ × Bool, e1 ∈ sem_W 10 D x ∧ e2 ∈ sem_W 10 D x ∧ e1 ≠ e2 ∧
      supp 10 D u0.1 ⊆ supp 10 D (src D e1) ∧ supp 10 D u0.1 ⊆ supp 10 D (src D e2) := by
  have hS := h.1
  have hu0m : u0 ∈ ru D b x := by rw [hru]; exact Finset.mem_singleton_self u0
  obtain ⟨hu0r, hxu0⟩ := mem_ru.1 hu0m
  have hu0u : u0 ∈ units 10 D := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0r).1).1
  have hfr : 2 ≤ fanout D u0.1 := by have := (mem_units.mp hu0u).2; omega
  have hxe : x ∈ eligSet 10 D := mem_eligSet.2 ⟨u0.1, hfr, hxu0⟩
  have hlow : ∀ w, 2 ≤ fanout D w → x ∈ supp 10 D w → w ≤ u0.1 := by
    intro w hrw hxw
    by_contra hlt
    have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
      rw [unitsPlus, Finset.mem_filter, mem_units]
      exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
        by show 0 + 1 < fanout D w; omega⟩, ⟨x, hxw⟩⟩
    by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D b
    · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
      have hbv : b v = w := congrArg Sigma.fst hveq
      have hsv := (hb v hv).2.1
      rw [hbv] at hsv
      rw [hsv, Finset.mem_singleton] at hxw
      have hmin := (hb x hxe).2.2.2 u0.1 hfr hxu0
      rw [hxw, hbv] at hmin; omega
    · have h1 : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ ru D b x := mem_ru.2 ⟨Finset.mem_sdiff.2 ⟨hwu, hwr⟩, hxw⟩
      rw [hru, Finset.mem_singleton] at h1
      have : w = u0.1 := congrArg Sigma.fst h1
      omega
  have harm_sub : ∀ {a c : ℕ}, Relation.ReflTransGen (sem_Arm 10 D {x}) a c →
      supp 10 D a ⊆ supp 10 D c := by
    intro a c hp
    induction hp with
    | refl => exact Finset.Subset.refl _
    | @tail u v _ huv ih =>
      obtain ⟨hj, hge, hop⟩ := huv.1
      have hv : 10 + (v - 10) = v := by omega
      have hxv : x ∈ supp 10 D (10 + (v - 10)) := by
        rw [hv]; exact (huv.2.2 x (Finset.mem_singleton_self x)).2
      have htag : tag D (v - 10) = false := (sem_zm_gate hS hM (by omega) hxv).1
      exact ih.trans (by
        rw [← hv, sem_supp_or hS (by omega) htag]
        rcases hop with he | he
        · rw [he]; exact Finset.subset_union_left
        · rw [he]; exact Finset.subset_union_right)
  have hread : ∀ j ∈ readers D u0.1,
      j < D.length ∧ u0.1 < 10 + j ∧ (opA D j = u0.1 ∨ opB D j = u0.1) := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
    have := hS j hj.1
    exact ⟨hj.1, by omega, hj.2⟩
  have hterm : ∀ j ∈ readers D u0.1, ∃ e : ℕ × Bool, e ∈ sem_W 10 D x ∧
      supp 10 D u0.1 ⊆ supp 10 D (src D e) ∧
      ((e.1 = j ∧ src D e = u0.1) ∨ Relation.ReflTransGen (sem_Arm 10 D {x}) (10 + j) (src D e)) := by
    intro j hj
    obtain ⟨hjl, hlt, hop⟩ := hread j hj
    by_cases hxj : x ∈ supp 10 D (10 + j)
    · have htag : tag D j = false := (sem_zm_gate hS hM hjl hxj).1
      have hsub1 : supp 10 D u0.1 ⊆ supp 10 D (10 + j) := by
        rw [sem_supp_or hS hjl htag]
        rcases hop with he | he
        · rw [he]; exact Finset.subset_union_left
        · rw [he]; exact Finset.subset_union_right
      obtain ⟨e, he1, he2⟩ := sem_descent sem_g10_gr h (sem_g10_comp hD) {x}
        ⟨x, Finset.mem_singleton_self x⟩
        (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hM)
        (10 + j) (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact hxj)
        (fun y hy w hrw hyw => by
          rw [Finset.mem_singleton.1 hy] at hyw
          by_contra hf; have := hlow w (by omega) hyw; omega)
      exact ⟨e, he1 x (Finset.mem_singleton_self x), hsub1.trans (harm_sub he2), Or.inr he2⟩
    · rcases hop with he | he
      · refine ⟨(j, false), sem_mem_W.2 ⟨hjl, by rw [sb_src_false, he]; exact hxu0, hxj⟩,
          by rw [sb_src_false, he], Or.inl ⟨rfl, by rw [sb_src_false, he]⟩⟩
      · refine ⟨(j, true), sem_mem_W.2 ⟨hjl, by rw [sb_src_true, he]; exact hxu0, hxj⟩,
          by rw [sb_src_true, he], Or.inl ⟨rfl, by rw [sb_src_true, he]⟩⟩
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.1 (by exact hfr : 1 < (readers D u0.1).card)
  have hRstep : ∀ a c, sem_Arm 10 D {x} a c → sem_step 10 D a c := fun _ _ hr => hr.1
  have hfun : ∀ a a' c, sem_Arm 10 D {x} a c → sem_Arm 10 D {x} a' c → a = a' := by
    intro a a' c h1 h2
    by_contra hne2
    obtain ⟨hjl, hge1, hop1⟩ := h1.1
    obtain ⟨-, -, hop2⟩ := h2.1
    have hcv : 10 + (c - 10) = c := by omega
    have ha := (h1.2.2 x (Finset.mem_singleton_self x)).1
    have ha' := (h2.2.2 x (Finset.mem_singleton_self x)).1
    have hc := (h1.2.2 x (Finset.mem_singleton_self x)).2
    have hxc : x ∈ supp 10 D (10 + (c - 10)) := by rw [hcv]; exact hc
    apply (sem_zm_gate hS hM (by omega) hxc).2
    rcases hop1 with e1 | e1 <;> rcases hop2 with e2 | e2
    · exact absurd (e1.symm.trans e2) hne2
    · rw [e1, e2]; exact ⟨ha, ha'⟩
    · rw [e1, e2]; exact ⟨ha', ha⟩
    · exact absurd (e1.symm.trans e2) hne2
  have hcross : ∀ ja ∈ readers D u0.1, ∀ jb ∈ readers D u0.1, ja ≠ jb →
      ¬ Relation.ReflTransGen (sem_Arm 10 D {x}) (10 + ja) (10 + jb) := by
    intro ja hja jb hjb hab hp
    obtain ⟨-, hlta, -⟩ := hread ja hja
    obtain ⟨hjlb, -, hopb⟩ := hread jb hjb
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu1, hu2⟩
    · exact hab (by omega)
    · have hu_ne : u ≠ u0.1 := by
        have := sem_rtg_le hS hRstep hu1; omega
      have hux := (hu2.2.2 x (Finset.mem_singleton_self x)).1
      apply (sem_zm_gate hS hM hjlb (hu2.2.2 x (Finset.mem_singleton_self x)).2).2
      have hstep : opA D jb = u ∨ opB D jb = u := by
        have := hu2.1.2.2; simpa using this
      rcases hopb with e1 | e1 <;> rcases hstep with e2 | e2
      · exact absurd (e2.symm.trans e1) hu_ne
      · rw [e1, e2]; exact ⟨hxu0, hux⟩
      · rw [e1, e2]; exact ⟨hux, hxu0⟩
      · exact absurd (e2.symm.trans e1) hu_ne
  obtain ⟨e1, he1W, he1s, he1p⟩ := hterm j1 hj1
  obtain ⟨e2, he2W, he2s, he2p⟩ := hterm j2 hj2
  refine ⟨e1, e2, he1W, he2W, fun heq => ?_, he1s, he2s⟩
  subst heq
  rcases he1p with ⟨hj1e, hs1⟩ | hp1 <;> rcases he2p with ⟨hj2e, hs2⟩ | hp2
  · exact hne (hj1e.symm.trans hj2e)
  · have hle := sem_rtg_le hS hRstep hp2
    have := (hread j2 hj2).2.1
    rw [hs1] at hle; omega
  · have hle := sem_rtg_le hS hRstep hp1
    have := (hread j1 hj1).2.1
    rw [hs2] at hle; omega
  · rcases sem_rtg_comparable hfun hp1 hp2 with h12 | h21
    · exact hcross j1 hj1 j2 hj2 hne h12
    · exact hcross j2 hj2 j1 hj1 hne.symm h21

theorem full_of_two_in_deg3 {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hB0 : Bzero 10 D = 0) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {i1 i2 u v : Fin 10} (hi1 : i1 ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D)
    (hg : i1 ≠ i2 ∧ hc_adjB i1 u = true ∧ hc_adjB i2 u = true ∧ hc_adjB u v = true ∧
      v ≠ i1 ∧ v ≠ i2) (hcu : (sem_W 10 D u).card ≤ 3) :
    (∀ t, t ∈ supp 10 D (src D (pos i1)) → Adj i1 t) ∧
    (∀ t, t ∈ supp 10 D (src D (pos i2)) → Adj i2 t) := by
  obtain ⟨hne, h1, h2, h3, hv1, hv2⟩ := hg
  rw [hc_adjB_iff] at h1 h2 h3
  have hfull : ∀ (ia ib : Fin 10), ia ∈ ineligSet 10 D → ib ∈ ineligSet 10 D → ia ≠ ib →
      Adj ia u → Adj ib u → v ≠ ia → v ≠ ib →
      ∀ t, t ∈ supp 10 D (src D (pos ia)) → Adj ia t := by
    intro ia ib hia hib hab hiau hibu hvia hvib t ht
    have pa := as_mem hpos hia hiau
    have pb := as_mem hpos hib hibu
    have pab : pos ia ≠ pos ib := fun e => hab (hpos.2 ia hia ib hib e)
    have hspec : ∀ t, t ∈ supp 10 D (src D (pos ia)) ↔ Adj ia t := by
      refine full_g10 h hD hB0 hpos hia hiau (fun p hp hne1 hsub => ?_)
      by_cases hv : v ∈ ineligSet 10 D
      · have pv := as_mem hpos hv (adj_symm h3)
        have pav : pos ia ≠ pos v := fun e => hvia.symm (hpos.2 ia hia v hv e)
        have pbv : pos ib ≠ pos v := fun e => hvib.symm (hpos.2 ib hib v hv e)
        rcases pa_three pa pb pv pab pav pbv hcu p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · exact hab.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hib)))
        · exact hvia (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hv)))
      · obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos h3
        have pae : pos ia ≠ e := fun hh => hv (hf ia hia hh.symm ▸ hia)
        have pbe : pos ib ≠ e := fun hh => hv (hf ib hib hh.symm ▸ hib)
        rcases pa_three pa pb he pab pae pbe hcu p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · exact hab.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hib)))
        · exact hv (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe).2.1) ▸ hia)
    exact (hspec t).1 ht
  exact ⟨hfull i1 i2 hi1 hi2 hne h1 h2 hv1 hv2, hfull i2 i1 hi2 hi1 hne.symm h2 h1 hv2 hv1⟩

theorem w3_ru_one_bound {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (b : Fin 10 → ℕ) (hb : sem_MinBranch 10 D b) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {x i1 i2 v : Fin 10}
    (hi1 : i1 ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D)
    (hg : (g10_nbB x).card = 3 ∧ i1 ≠ i2 ∧ hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧
      hc_adjB x v = true ∧ v ≠ i1 ∧ v ≠ i2)
    {u0 : Σ _ : ℕ, ℕ} (hru : ru D b x = {u0}) :
    ∀ t : Fin 10, t ∈ supp 10 D u0.1 → t ≠ x →
      (hc_adjB i1 t = true ∧ ∀ q : Fin 10, hc_adjB i2 q = true → q ≠ x → hc_adjB t q = true) ∨
      (hc_adjB i2 t = true ∧ ∀ q : Fin 10, hc_adjB i1 q = true → q ≠ x → hc_adjB t q = true) := by
  obtain ⟨hdx, h12, hx1, hx2, hxv, hv1, hv2⟩ := hg
  have hbp := sem_minBranch_pure hb
  have hx3 := two_in_deg3 h hD hpos hi1 hi2 ⟨h12, hx1, hx2, hxv, hv1, hv2⟩
  have hcc := cc_le h hD b hbp x
  rw [hru, Finset.card_singleton] at hcc
  have hM : merges 10 D (carrierT 10 D {x}) = ∅ := Finset.card_eq_zero.1 (by omega)
  have hW3 : (sem_W 10 D x).card ≤ 3 := by omega
  obtain ⟨e1, e2, he1W, he2W, he12, hs1, hs2⟩ := ru_one_two_supp h hD b hb hM hru
  obtain ⟨hfull1, hfull2⟩ := full_of_two_in_deg3 h hD hB0 hpos hi1 hi2 ⟨h12, hx1, hx2, hxv, hv1, hv2⟩ hW3
  have p1 := as_mem hpos hi1 ((hc_adjB_iff _ _).1 hx1)
  have p2 := as_mem hpos hi2 ((hc_adjB_iff _ _).1 hx2)
  have hp12 : pos i1 ≠ pos i2 := fun e => h12 (hpos.2 i1 hi1 i2 hi2 e)
  intro t ht htx
  have ht1 : t ∈ supp 10 D (src D e1) := hs1 ht
  have ht2 : t ∈ supp 10 D (src D e2) := hs2 ht
  by_cases h1 : e1 = pos i1 ∨ e2 = pos i1
  · have hti1 : Adj i1 t := by
      rcases h1 with rfl | rfl
      · exact hfull1 t ht1
      · exact hfull1 t ht2
    by_cases h2 : e1 = pos i2 ∨ e2 = pos i2
    · exfalso
      have hti2 : Adj i2 t := by
        rcases h2 with rfl | rfl
        · exact hfull2 t ht1
        · exact hfull2 t ht2
      have hc : (g10_nbB i1 ∩ g10_nbB i2).card ≤ 1 := by
        have : ∀ a b : Fin 10, a ≠ b → (g10_nbB a ∩ g10_nbB b).card ≤ 1 := by decide +kernel
        exact this i1 i2 h12
      have hxt : ({x, t} : Finset (Fin 10)) ⊆ g10_nbB i1 ∩ g10_nbB i2 := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        simp only [Finset.mem_inter, g10_nbB, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hw with rfl | rfl
        · exact ⟨hx1, hx2⟩
        · exact ⟨(hc_adjB_iff _ _).2 hti1, (hc_adjB_iff _ _).2 hti2⟩
      have hcard := Finset.card_le_card hxt
      rw [Finset.card_pair (Ne.symm htx)] at hcard; omega
    · rw [not_or] at h2
      obtain ⟨ev, hevW, hte⟩ : ∃ ev, ev ∈ sem_W 10 D x ∧ ev ≠ pos i1 ∧ ev ≠ pos i2 ∧ t ∈ supp 10 D (src D ev) := by
        rcases h1 with rfl | rfl
        · exact ⟨e2, he2W, he12.symm, h2.2, ht2⟩
        · exact ⟨e1, he1W, he12, h2.1, ht1⟩
      have hW := pa_three p1 p2 hevW hp12 hte.1.symm hte.2.1.symm hW3
      left
      refine ⟨(hc_adjB_iff _ _).2 hti1, fun q hq2 hqx => ?_⟩
      by_contra hntq
      have hntq' : hc_adjB t q = false := Bool.eq_false_iff.2 hntq
      obtain ⟨f, hfW, hfq, hft⟩ := g10_deg3_cover_free h hD hdx (Ne.symm hqx) (Ne.symm htx)
        (fun hqt => sem_adjB_false.1 hntq' (adj_symm hqt))
      rcases hW f hfW with rfl | rfl | rfl
      · exact hft (by rcases h1 with rfl | rfl; exact ht1; exact ht2)
      · exact hfq ((hpos.1 i2 hi2).2.2.1 q ((hc_adjB_iff _ _).1 hq2))
      · exact hft hte.2.2
  · rw [not_or] at h1
    by_cases h2 : e1 = pos i2 ∨ e2 = pos i2
    · have hti2 : Adj i2 t := by
        rcases h2 with rfl | rfl
        · exact hfull2 t ht1
        · exact hfull2 t ht2
      obtain ⟨ev, hevW, hte⟩ : ∃ ev, ev ∈ sem_W 10 D x ∧ ev ≠ pos i1 ∧ ev ≠ pos i2 ∧ t ∈ supp 10 D (src D ev) := by
        rcases h2 with rfl | rfl
        · exact ⟨e2, he2W, h1.2, he12.symm, ht2⟩
        · exact ⟨e1, he1W, h1.1, he12, ht1⟩
      have hW := pa_three p1 p2 hevW hp12 hte.1.symm hte.2.1.symm hW3
      right
      refine ⟨(hc_adjB_iff _ _).2 hti2, fun q hq1 hqx => ?_⟩
      by_contra hntq
      have hntq' : hc_adjB t q = false := Bool.eq_false_iff.2 hntq
      obtain ⟨f, hfW, hfq, hft⟩ := g10_deg3_cover_free h hD hdx (Ne.symm hqx) (Ne.symm htx)
        (fun hqt => sem_adjB_false.1 hntq' (adj_symm hqt))
      rcases hW f hfW with rfl | rfl | rfl
      · exact hfq ((hpos.1 i1 hi1).2.2.1 q ((hc_adjB_iff _ _).1 hq1))
      · exact hft (by rcases h2 with rfl | rfl; exact ht1; exact ht2)
      · exact hft hte.2.2
    · rw [not_or] at h2
      have h4 := pa_card4 p1 p2 he1W he2W hp12 (Ne.symm h1.1) (Ne.symm h1.2) (Ne.symm h2.1) (Ne.symm h2.2) he12
      omega

def w3_bad (x i1 i2 t : Fin 10) : Bool :=
  (t == x) ||
  (hc_adjB i1 t && (List.finRange 10).all (fun q => !(hc_adjB i2 q && !(q == x)) || hc_adjB t q)) ||
  (hc_adjB i2 t && (List.finRange 10).all (fun q => !(hc_adjB i1 q && !(q == x)) || hc_adjB t q))

theorem w3_ru_one_not_mem {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (b : Fin 10 → ℕ) (hb : sem_MinBranch 10 D b) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) {x i1 i2 v : Fin 10}
    (hi1 : i1 ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D)
    (hg : (g10_nbB x).card = 3 ∧ i1 ≠ i2 ∧ hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧
      hc_adjB x v = true ∧ v ≠ i1 ∧ v ≠ i2)
    {u0 : Σ _ : ℕ, ℕ} (hru : ru D b x = {u0})
    {t : Fin 10} (hnb : w3_bad x i1 i2 t = false) : t ∉ supp 10 D u0.1 := by
  intro ht
  have hnb1 : t ≠ x := by
    intro heq; subst heq; simp [w3_bad] at hnb
  have hbd := w3_ru_one_bound h hD hB0 b hb hpos hi1 hi2 hg hru t ht hnb1
  have htrue : w3_bad x i1 i2 t = true := by
    unfold w3_bad
    rcases hbd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_imp_iff]
      left; right
      refine ⟨h1, fun q => ?_⟩
      by_cases hq2 : hc_adjB i2 q = true
      · by_cases hqx : q = x
        · simp [hqx]
        · simp [hq2, hqx, h2 q hq2 hqx]
      · simp [Bool.eq_false_iff.2 hq2]
    · simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_imp_iff]
      right
      refine ⟨h1, fun q => ?_⟩
      by_cases hq1 : hc_adjB i1 q = true
      · by_cases hqx : q = x
        · simp [hqx]
        · simp [hq1, hqx, h2 q hq1 hqx]
      · simp [Bool.eq_false_iff.2 hq1]
  rw [hnb] at htrue; exact Bool.false_ne_true htrue

theorem pos_chain_or {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos) {i v : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hiv : Adj i v)
    (hv : ∀ p ∈ sem_W 10 D v, p.1 ≠ (pos i).1 → ¬ supp 10 D (src D (sem_bar p)) ⊆ {i}) :
    sem_Chain 10 D (10 + (pos i).1) (outW 10 D) ∧
    (∀ j, Relation.ReflTransGen (sem_step 10 D) (10 + (pos i).1) (10 + j) →
      j ≠ (pos i).1 → tag D j = false) ∧
    (∀ x : Fin 10 → Bool, val D x (10 + (pos i).1) = true → G10Edge x) := by
  have hS := h.1
  have hG := sem_g10_gr
  have hC := sem_g10_comp hD
  have heW := as_W h hD hpos hi
  have he1 : (pos i).1 < D.length := (hpos.1 i hi).1
  have hreach_e : Relation.ReflTransGen (sem_step 10 D) i.val (10 + (pos i).1) :=
    (sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi (pos_bar_mem hpos hi))).tail
      (sem_step_src he1 (sem_bar (pos i)).2)
  have hch_out : sem_Chain 10 D (10 + (pos i).1) (outW 10 D) := by
    have hch_all := sem_noempty_chain_out hG h hC hB0 hi
    have hch_e := sem_noempty_unique hG h hC hB0 hi hreach_e
    have hdet : ∀ a c1 c2, (sem_step 10 D a c1 ∧ fanout D a = 1) →
        (sem_step 10 D a c2 ∧ fanout D a = 1) → c1 = c2 :=
      fun _ _ _ h1 h2 => sem_step_unique h1.1 h2.1 h1.2
    have hsplit : ∀ {a}, sem_Chain 10 D a (10 + (pos i).1) → sem_Chain 10 D a (outW 10 D) →
        sem_Chain 10 D (10 + (pos i).1) (outW 10 D) := by
      intro a h1
      induction h1 using Relation.ReflTransGen.head_induction_on with
      | refl => intro h2; exact h2
      | head hac hc1 ih =>
        intro h2
        rcases Relation.ReflTransGen.cases_head h2 with heq | ⟨d, had, hdo⟩
        · exfalso
          have hlt := sem_step_lt hS hac.1
          have hle2 := sem_rtg_le hS (fun _ _ s => s.1) hc1
          rw [heq] at hlt; unfold outW at hlt; omega
        · exact ih (hdet _ _ d hac had ▸ hdo)
    exact hsplit hch_e hch_all
  have hor : ∀ j, Relation.ReflTransGen (sem_step 10 D) (10 + (pos i).1) (10 + j) →
      j ≠ (pos i).1 → tag D j = false := by
    intro j hreach hj
    by_contra ht
    rw [Bool.not_eq_false] at ht
    rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
    · exact hj (by omega)
    · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
      have hjj : j' = j := by omega
      subst hjj
      have hreach2 : Relation.ReflTransGen (sem_step 10 D) i.val w := hreach_e.trans hw1
      have hch := sem_noempty_unique hG h hC hB0 hi hreach2
      have hf : fanout D w = 1 := by
        have h1 := sem_step_fanout hw2
        by_contra hne
        have h2 := sem_branch_empty hG hS hC hi hch (by omega)
        have h4 := sem_bzero_branch hS hB0 (b := w) (by omega)
        rw [h2] at h4
        exact Finset.not_nonempty_empty h4
      have hsub : supp 10 D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
      have hvi : v ≠ i := fun hvi => adj_irrefl i (hvi ▸ hiv)
      have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
      have hmem : v ∈ supp 10 D (src D (j', !s)) :=
        sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
          (by unfold outW; omega) hiv
      have hp : ((j', !s) : ℕ × Bool) ∈ sem_W 10 D v :=
        sem_mem_W.2 ⟨hj', hmem, fun hc => by
          have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
          exact hvi (Finset.mem_singleton.1 this)⟩
      exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)
  refine ⟨hch_out, hor, fun x hx => ?_⟩
  have hval_out : val D x (outW 10 D) = true := by
    have hstep_val : ∀ {w}, Relation.ReflTransGen (sem_step 10 D) (10 + (pos i).1) w →
        val D x w = true := by
      intro w hp
      induction hp with
      | refl => exact hx
      | @tail u v' hp1 hstep ih =>
        have ⟨hlt, hge, hop⟩ := hstep
        have hv_eq : 10 + (v' - 10) = v' := by omega
        have hjlt : v' - 10 < D.length := by omega
        have hne : v' - 10 ≠ (pos i).1 := by
          have h1 := sem_rtg_le hS (fun _ _ s => s) hp1
          have h2 := sem_step_lt hS hstep
          omega
        have htag : tag D (v' - 10) = false := hor (v' - 10) (hv_eq.symm ▸ hp1.tail hstep) hne
        rw [← hv_eq, val_gate hS x (v' - 10) hjlt, htag, gop_false, Bool.or_eq_true]
        rcases hop with ha | hb'
        · left; rw [ha]; exact ih
        · right; rw [hb']; exact ih
    exact hstep_val (sem_rtg_mono (fun _ _ s => s.1) hch_out)
  exact (hD x).1 hval_out

theorem src_lt {n : ℕ} {D : Dag} (hS : Strict n D) {e : ℕ × Bool} (hj : e.1 < D.length) :
    src D e < n + e.1 := by
  rcases e with ⟨j, s⟩
  cases s
  · exact (hS j hj).1
  · exact (hS j hj).2.1

theorem sem_supp_path {n : ℕ} {D : Dag} (hS : Strict n D) {y : Fin n} {w : ℕ}
    (hy : y ∈ supp n D w) :
    Relation.ReflTransGen (fun a c => sem_step n D a c ∧ y ∈ supp n D a ∧ y ∈ supp n D c) y.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · have h1 := mem_supp.1 hy
      rw [val_input D _ w hw] at h1
      have : y.val = w := congrArg Fin.val (of_decide_eq_true h1).symm
      rw [this]
    · have hlt := sem_supp_lt hy
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha_lt, hb_lt, -⟩ := hS j hj
      by_cases ht : tag D j = true
      · rw [sem_supp_and hS hj ht, Finset.mem_inter] at hy
        exact (ih (opA D j) ha_lt hy.1).tail
          ⟨⟨by omega, by omega, Or.inl (by simp)⟩, hy.1, by rw [sem_supp_and hS hj ht, Finset.mem_inter]; exact hy⟩
      · rw [Bool.not_eq_true] at ht
        rw [sem_supp_or hS hj ht, Finset.mem_union] at hy
        rcases hy with ha | hb
        · exact (ih (opA D j) ha_lt ha).tail
            ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ha, by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl ha⟩
        · exact (ih (opB D j) hb_lt hb).tail
            ⟨⟨by omega, by omega, Or.inr (by simp)⟩, hb, by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr hb⟩

theorem pa_ed_avoid_min {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    {u v a b : Fin 10} (huv : Adj u v) (hnab : ¬ Adj a b)
    (hun : u ≠ a) (hun' : u ≠ b) (hvb : v = b ∨ v = a) :
    ∃ e : ℕ × Bool, e ∈ sem_W 10 D u ∧
      val D (sem_two u v) (10 + e.1) = true ∧
      val D (sem_two a b) (10 + e.1) = false ∧
      val D (sem_two a b) (src D (sem_bar e)) = true := by
  classical
  have hS := h.1
  have hC := sem_g10_comp hD
  have h1 : val D (sem_two u v) (outW 10 D) = true := (hC _).2 (sem_two_edge huv)
  have h0 : val D (sem_two a b) (outW 10 D) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    obtain ⟨p, q, hpq, hp, hq⟩ := (hC _).1 hc
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact adj_irrefl _ hpq
    · exact hnab hpq
    · exact hnab (adj_symm hpq)
    · exact adj_irrefl _ hpq
  have hu0 : val D (fun i => decide (i = u)) (outW 10 D) = false := by
    by_contra hc; rw [Bool.not_eq_false] at hc
    exact g10_not_single u ((hD _).1 hc)
  have hex : ∃ w, val D (sem_two u v) w = true ∧ val D (sem_two a b) w = false ∧
      val D (fun i => decide (i = u)) w = false := ⟨outW 10 D, h1, h0, hu0⟩
  obtain ⟨hw1, hw0, hwu⟩ := Nat.find_spec hex
  have hmin : ∀ w', w' < Nat.find hex → val D (sem_two u v) w' = true →
      val D (sem_two a b) w' = true ∨ val D (fun i => decide (i = u)) w' = true := by
    intro w' hlt hv'
    by_contra hc; push Not at hc
    exact Nat.find_min hex hlt ⟨hv', Bool.eq_false_iff.2 hc.1, Bool.eq_false_iff.2 hc.2⟩
  generalize Nat.find hex = w at hw1 hw0 hwu hmin
  have hlt : w < 10 + D.length := by
    by_contra hc; rw [val_ge D _ w (by omega)] at hw1; exact Bool.false_ne_true hw1
  have hge : 10 ≤ w := by
    by_contra hc
    rw [val_input D _ w (by omega)] at hw1 hw0 hwu
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with heq | heq
    · have : (⟨w, by omega⟩ : Fin 10) = u := heq
      rw [this] at hwu; simp at hwu
    · have hwe : (⟨w, by omega⟩ : Fin 10) = v := heq
      rw [hwe] at hw0
      rcases hvb with rfl | rfl <;> simp [sem_two] at hw0
  obtain ⟨j, rfl⟩ : ∃ j, w = 10 + j := ⟨w - 10, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha_lt, hb_lt, -⟩ := hS j hj
  rw [val_gate hS _ j hj] at hw1 hw0 hwu
  have htag : tag D j = true := by
    by_contra ht; rw [Bool.not_eq_true] at ht
    rw [ht, gop_false] at hw1 hw0 hwu
    rw [Bool.or_eq_false_iff] at hw0 hwu
    rw [Bool.or_eq_true] at hw1
    rcases hw1 with ha1 | hb1
    · rcases hmin _ ha_lt ha1 with h' | h'
      · rw [hw0.1] at h'; exact Bool.false_ne_true h'
      · rw [hwu.1] at h'; exact Bool.false_ne_true h'
    · rcases hmin _ hb_lt hb1 with h' | h'
      · rw [hw0.2] at h'; exact Bool.false_ne_true h'
      · rw [hwu.2] at h'; exact Bool.false_ne_true h'
  rw [htag, gop_true] at hw1 hw0 hwu
  rw [Bool.and_eq_true] at hw1
  rw [Bool.and_eq_false_iff] at hw0 hwu
  have hma := hmin _ ha_lt hw1.1
  have hmb := hmin _ hb_lt hw1.2
  have hu_not : u ∉ supp 10 D (10 + j) := by
    intro hm
    have := mem_supp.1 hm
    rw [val_gate hS _ j hj, htag, gop_true, Bool.and_eq_true] at this
    change val D (fun i => decide (i = u)) (opA D j) = true ∧ val D (fun i => decide (i = u)) (opB D j) = true at this
    rcases hwu with h' | h'
    · rw [h'] at this; exact Bool.false_ne_true this.1
    · rw [h'] at this; exact Bool.false_ne_true this.2
  have h1' : val D (sem_two u v) (10 + j) = true := by
    rw [val_gate hS _ j hj, htag, gop_true, hw1.1, hw1.2]; rfl
  have h0' : val D (sem_two a b) (10 + j) = false := by
    rw [val_gate hS _ j hj, htag, gop_true]
    rcases hw0 with h' | h'
    · rw [h']; rfl
    · rw [h']; simp
  rcases hma with ha0 | hau
  · have hb0 : val D (sem_two a b) (opB D j) = false := by
      rcases hw0 with h' | h'
      · rw [ha0] at h'; exact Bool.noConfusion h'
      · exact h'
    have hbu : val D (fun i => decide (i = u)) (opB D j) = true := by
      rcases hmb with h' | h'
      · rw [hb0] at h'; exact Bool.noConfusion h'
      · exact h'
    exact ⟨(j, true), sem_mem_W.2 ⟨hj, mem_supp.2 (by rw [sb_src_true]; exact hbu), hu_not⟩,
      h1', h0', by rw [show src D (sem_bar (j, true)) = opA D j from rfl]; exact ha0⟩
  · have hbu : val D (fun i => decide (i = u)) (opB D j) = false := by
      rcases hwu with h' | h'
      · rw [hau] at h'; exact Bool.noConfusion h'
      · exact h'
    have hb0 : val D (sem_two a b) (opB D j) = true := by
      rcases hmb with h' | h'
      · exact h'
      · rw [hbu] at h'; exact Bool.noConfusion h'
    exact ⟨(j, false), sem_mem_W.2 ⟨hj, mem_supp.2 (by rw [sb_src_false]; exact hau), hu_not⟩,
      h1', h0', by rw [show src D (sem_bar (j, false)) = opB D j from rfl]; exact hb0⟩

theorem elim_01_R0 {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (h8 : totalSurplus 10 D ≤ 8) (hI : ineligSet 10 D = {0, 1}) : False := by
  have hS := h.1
  have hC := sem_g10_comp hD
  obtain ⟨b, hb⟩ := sem_exists_minBranch sem_g10_gr hS hC
  have hbp := sem_minBranch_pure hb
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h hC
  have hel := inelig_card_add 10 D
  have hts := totalSurplus_split 10 D
  have hI2 : (ineligSet 10 D).card = 2 := by rw [hI]; decide
  have hE8 : (eligSet 10 D).card = 8 := by omega
  have hBp_ge := elig_le_Bplus hS b hbp
  have hB0 : Bzero 10 D = 0 := by omega
  have hR0 : residualUnits 10 D b = ∅ := by
    have := card_residual hS b hbp
    exact Finset.card_eq_zero.1 (by omega)
  have hcc0 : ∀ x : Fin 10, (sem_W 10 D x).card + (merges 10 D (carrierT 10 D {x})).card ≤ 2 := fun x => by
    have h1 := cc_le h hD b hbp x
    unfold ru at h1; rw [hR0, Finset.filter_empty, Finset.card_empty] at h1; omega
  have hW2 : ∀ x : Fin 10, (sem_W 10 D x).card ≤ 2 := fun x => by have := hcc0 x; omega
  have h0 : (0 : Fin 10) ∈ ineligSet 10 D := by rw [hI]; decide
  have h1 : (1 : Fin 10) ∈ ineligSet 10 D := by rw [hI]; decide
  have hni : ∀ v : Fin 10, v ≠ 0 → v ≠ 1 → v ∉ ineligSet 10 D := fun v h0' h1' hm => by
    rw [hI, Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm.elim h0' h1'
  have helig : ∀ v : Fin 10, v ≠ 0 → v ≠ 1 → v ∈ eligSet 10 D := fun v h0' h1' => by
    by_contra hc; exact hni v h0' h1' (sem_mem_inelig.2 hc)
  obtain ⟨Z4, hZ4n, hW4, hZ4p⟩ := ps_nonadj h hD hpos h0 (by decide) (by decide : Adj 0 5) (by decide) (by decide) (hW2 4)
  obtain ⟨Z5, hZ5n, hW5, hZ5p⟩ := ps_nonadj h hD hpos h0 (by decide) (by decide : Adj 0 4) (by decide) (by decide) (hW2 5)
  obtain ⟨Z6, hZ6n, hW6, hZ6p⟩ := ps_nonadj h hD hpos h1 (by decide) (by decide : Adj 1 2) (by decide) (by decide) (hW2 6)
  have hZ4_3 : sem_bar Z4 ∈ sem_W 10 D 3 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 4 3)
    rw [hW4, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z4 := he.resolve_left (fun hh => hni 3 (by decide) (by decide) (hf 0 h0 hh ▸ h0))
    rwa [← this]
  have hZ4_9 : sem_bar Z4 ∈ sem_W 10 D 9 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 4 9)
    rw [hW4, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z4 := he.resolve_left (fun hh => hni 9 (by decide) (by decide) (hf 0 h0 hh ▸ h0))
    rwa [← this]
  have hZ5_7 : sem_bar Z5 ∈ sem_W 10 D 7 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 5 7)
    rw [hW5, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z5 := he.resolve_left (fun hh => hni 7 (by decide) (by decide) (hf 0 h0 hh ▸ h0))
    rwa [← this]
  have hZ5_8 : sem_bar Z5 ∈ sem_W 10 D 8 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 5 8)
    rw [hW5, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z5 := he.resolve_left (fun hh => hni 8 (by decide) (by decide) (hf 0 h0 hh ▸ h0))
    rwa [← this]
  have hZ6_8 : sem_bar Z6 ∈ sem_W 10 D 8 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 6 8)
    rw [hW6, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z6 := he.resolve_left (fun hh => hni 8 (by decide) (by decide) (hf 1 h1 hh ▸ h1))
    rwa [← this]
  have hZ6_9 : sem_bar Z6 ∈ sem_W 10 D 9 := by
    obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 6 9)
    rw [hW6, Finset.mem_insert, Finset.mem_singleton] at he
    have : e = Z6 := he.resolve_left (fun hh => hni 9 (by decide) (by decide) (hf 1 h1 hh ▸ h1))
    rwa [← this]
  have hZ46 : Z4 ≠ Z6 := fun hh => hZ4p 6 (by decide) (by decide) (by rw [hh, hW6]; simp)
  have hZ56 : Z5 ≠ Z6 := fun hh => hZ5p 6 (by decide) (by decide) (by rw [hh, hW6]; simp)
  have hb46 : sem_bar Z4 ≠ sem_bar Z6 := fun hh => hZ46 (by simpa [sem_bar_bar] using congrArg sem_bar hh)
  have hb56 : sem_bar Z5 ≠ sem_bar Z6 := fun hh => hZ56 (by simpa [sem_bar_bar] using congrArg sem_bar hh)
  have hW8_eq : sem_W 10 D 8 = {sem_bar Z5, sem_bar Z6} := by
    symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hb56]; exact hW2 8)
    rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ5_8; exact hZ6_8
  have hW9_eq : sem_W 10 D 9 = {sem_bar Z4, sem_bar Z6} := by
    symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hb46]; exact hW2 9)
    rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ4_9; exact hZ6_9
  obtain ⟨Z2, hZ2_2, hZ2_7, hf2, -⟩ := pa_ed h hD hpos (by decide : Adj 2 7)
  have hZ2_ne1 : Z2 ≠ pos 1 := fun hh => hni 7 (by decide) (by decide) (hf2 1 h1 hh ▸ h1)
  have hW2_eq : sem_W 10 D 2 = {pos 1, Z2} := by
    symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hZ2_ne1.symm]; exact hW2 2)
    rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl
    · exact as_mem hpos h1 (by decide : Adj 1 2)
    · exact hZ2_2
  have hZ25 : Z2 ≠ Z5 := fun hh => hZ5p 2 (by decide) (by decide) (hh ▸ hZ2_2)
  have hb25 : sem_bar Z2 ≠ sem_bar Z5 := fun hh => hZ25 (by simpa [sem_bar_bar] using congrArg sem_bar hh)
  have hW7_eq : sem_W 10 D 7 = {sem_bar Z2, sem_bar Z5} := by
    symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hb25]; exact hW2 7)
    rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ2_7; exact hZ5_7
  have hZ4_or_Z6_7 : Z4 ∈ sem_W 10 D 7 ∨ Z6 ∈ sem_W 10 D 7 := by
    obtain ⟨e, he, hbe, -, -⟩ := pa_ed h hD hpos (by decide : Adj 9 7)
    rw [hW9_eq, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · left; simpa [sem_bar_bar] using hbe
    · right; simpa [sem_bar_bar] using hbe
  have hZ6_not7 : Z6 ∉ sem_W 10 D 7 := by
    intro h67
    rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at h67
    rcases h67 with h62 | h65
    · have h26 : sem_bar Z6 = Z2 := by rw [h62, sem_bar_bar]
      obtain ⟨f, hf, h3n, h2n⟩ := g10_deg3_cover_free h hD (x := 9) (a := 3) (b := 2) (by decide) (by decide) (by decide) (by decide)
      rw [hW9_eq, Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact h3n (sem_mem_W.1 hZ4_3).2.1
      · exact h2n (sem_mem_W.1 (h26 ▸ hZ2_2)).2.1
    · have h56' : sem_bar Z6 = Z5 := by rw [h65, sem_bar_bar]
      exact hZ5p 8 (by decide) (by decide) (h56' ▸ hZ6_8)
  have hZ4_7 : Z4 ∈ sem_W 10 D 7 := hZ4_or_Z6_7.resolve_right hZ6_not7
  have hZ4_eq_b5 : Z4 = sem_bar Z5 := by
    rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at hZ4_7
    rcases hZ4_7 with h42 | h45
    · exfalso
      obtain ⟨f, hf, h4n, h8n⟩ := g10_deg3_cover_free h hD (x := 7) (a := 4) (b := 8) (by decide) (by decide) (by decide) (by decide)
      rw [hW7_eq, ← h42, Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with hf' | hf'
      · exact h4n (sem_mem_W.1 (by rw [hf', hW4]; simp : f ∈ sem_W 10 D 4)).2.1
      · exact h8n (sem_mem_W.1 (hf' ▸ hZ5_8)).2.1
    · exact h45
  have hZ5_eq_b4 : Z5 = sem_bar Z4 := by rw [hZ4_eq_b5, sem_bar_bar]
  have hZ4_4 : Z4 ∈ sem_W 10 D 4 := by rw [hW4]; simp
  have hb4_5 : sem_bar Z4 ∈ sem_W 10 D 5 := by rw [← hZ5_eq_b4, hW5]; simp
  have hZ4_8 : Z4 ∈ sem_W 10 D 8 := by rw [hZ4_eq_b5]; exact hZ5_8
  have hZ26 : Z2 ≠ Z6 := by
    intro hh
    have h78 : sem_bar Z6 ∈ sem_W 10 D 7 := hh ▸ hZ2_7
    obtain ⟨f, hf, h4n, h7n⟩ := g10_deg3_cover_free h hD (x := 8) (a := 4) (b := 7) (by decide) (by decide) (by decide) (by decide)
    rw [hW8_eq, ← hZ4_eq_b5, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact h4n (sem_mem_W.1 hZ4_4).2.1
    · exact h7n (sem_mem_W.1 h78).2.1

  have hM0 : ∀ x : Fin 10, (sem_W 10 D x).card = 2 → merges 10 D (carrierT 10 D {x}) = ∅ := fun x hx => by
    have := hcc0 x; exact Finset.card_eq_zero.1 (by omega)
  have hM2 : merges 10 D (carrierT 10 D {2}) = ∅ := hM0 2 (by rw [hW2_eq, Finset.card_pair hZ2_ne1.symm])
  have hM4 : merges 10 D (carrierT 10 D {4}) = ∅ := hM0 4 (by rw [hW4, Finset.card_pair hZ4n.symm])
  have hM5 : merges 10 D (carrierT 10 D {5}) = ∅ := hM0 5 (by rw [hW5, Finset.card_pair hZ5n.symm])
  have hM6 : merges 10 D (carrierT 10 D {6}) = ∅ := hM0 6 (by rw [hW6, Finset.card_pair hZ6n.symm])
  have hval_Z4_45 : val D (sem_two (4 : Fin 10) (5 : Fin 10)) (10 + Z4.1) = true := by
    have hj4 := (sem_mem_W.1 hZ4_4).1
    have ht4 := sem_W_and hS hZ4_4
    have h4s := val_mono hS (fun i => decide (i = 4)) (sem_two (4 : Fin 10) (5 : Fin 10))
      (fun i hi => by simp only [decide_eq_true_eq] at hi; subst hi; simp [sem_two])
      (src D Z4) (mem_supp.1 (sem_mem_W.1 hZ4_4).2.1)
    have h5s := val_mono hS (fun i => decide (i = 5)) (sem_two (4 : Fin 10) (5 : Fin 10))
      (fun i hi => by simp only [decide_eq_true_eq] at hi; subst hi; simp [sem_two])
      (src D (sem_bar Z4)) (mem_supp.1 (sem_mem_W.1 hb4_5).2.1)
    rw [val_gate hS _ Z4.1 hj4, ht4, gop_true]
    rcases hZ4eq : Z4 with ⟨j, s⟩
    rw [hZ4eq] at h4s h5s
    cases s
    · rw [sb_src_false] at h4s; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at h5s; simp [h4s, h5s]
    · rw [sb_src_true] at h4s; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at h5s; simp [h4s, h5s]

  have ⟨hZ2_45_f, hZ2_src_45⟩ : val D (sem_two (4 : Fin 10) (5 : Fin 10)) (10 + Z2.1) = false ∧ val D (sem_two (4 : Fin 10) (5 : Fin 10)) (src D Z2) = true := by
    obtain ⟨e, he7, -, he45, hbe45⟩ := pa_ed_avoid_min h hD (u := 7) (v := 5) (a := 4) (b := 5)
      (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)
    rw [hW7_eq, ← hZ4_eq_b5, Finset.mem_insert, Finset.mem_singleton] at he7
    rcases he7 with rfl | rfl
    · exact ⟨he45, by simpa [sem_bar_bar] using hbe45⟩
    · rw [hval_Z4_45] at he45; exact Bool.noConfusion he45

  have ⟨hZ6_45_f, hZ6_src_45⟩ : val D (sem_two (4 : Fin 10) (5 : Fin 10)) (10 + Z6.1) = false ∧ val D (sem_two (4 : Fin 10) (5 : Fin 10)) (src D Z6) = true := by
    obtain ⟨e, he8, -, he45, hbe45⟩ := pa_ed_avoid_min h hD (u := 8) (v := 5) (a := 4) (b := 5)
      (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)
    rw [hW8_eq, ← hZ4_eq_b5, Finset.mem_insert, Finset.mem_singleton] at he8
    rcases he8 with rfl | rfl
    · rw [hval_Z4_45] at he45; exact Bool.noConfusion he45
    · exact ⟨he45, by simpa [sem_bar_bar] using hbe45⟩

  let inU : ℕ → Prop := fun w => w < 10 + D.length ∧ val D (sem_two (4 : Fin 10) (5 : Fin 10)) w = true ∧
    (4 : Fin 10) ∉ supp 10 D w ∧ (5 : Fin 10) ∉ supp 10 D w
  let stepU : ℕ → ℕ → Prop := fun a c => sem_step 10 D a c ∧ inU a ∧ inU c
  have hZ4_inU : inU (10 + Z4.1) := by
    have hj4 := (sem_mem_W.1 hZ4_4).1
    exact ⟨by omega, hval_Z4_45, (sem_mem_W.1 hZ4_4).2.2, (sem_mem_W.1 hb4_5).2.2⟩
  have hZ2_not4 : (4 : Fin 10) ∉ supp 10 D (src D Z2) := fun hm => by
    have hmW := zm_mem hS hM4 (sem_mem_W.1 hZ2_2).1 (sem_W_and hS hZ2_2) hm
    rw [hW4, Finset.mem_insert, Finset.mem_singleton] at hmW
    rcases hmW with heq | heq
    · have := as_priv hpos h0 (by rw [← heq]; exact hZ2_7); exact absurd this (by decide)
    · exact hZ4p 2 (by decide) (by decide) (heq ▸ hZ2_2)
  have hZ2_not5 : (5 : Fin 10) ∉ supp 10 D (src D Z2) := fun hm => by
    have hmW := zm_mem hS hM5 (sem_mem_W.1 hZ2_2).1 (sem_W_and hS hZ2_2) hm
    rw [hW5, Finset.mem_insert, Finset.mem_singleton] at hmW
    rcases hmW with heq | heq
    · have := as_priv hpos h0 (by rw [← heq]; exact hZ2_7); exact absurd this (by decide)
    · exact hZ25 heq
  have hZ6_not4 : (4 : Fin 10) ∉ supp 10 D (src D Z6) := fun hm => by
    have hmW := zm_mem hS hM4 (sem_mem_W.1 (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)).1
      (sem_W_and hS (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)) hm
    rw [hW4, Finset.mem_insert, Finset.mem_singleton] at hmW
    rcases hmW with heq | heq
    · have := as_priv hpos h0 (by rw [← heq]; exact hZ6_8); exact absurd this (by decide)
    · exact hZ46 heq.symm
  have hZ6_not5 : (5 : Fin 10) ∉ supp 10 D (src D Z6) := fun hm => by
    have hmW := zm_mem hS hM5 (sem_mem_W.1 (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)).1
      (sem_W_and hS (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)) hm
    rw [hW5, Finset.mem_insert, Finset.mem_singleton] at hmW
    rcases hmW with heq | heq
    · have := as_priv hpos h0 (by rw [← heq]; exact hZ6_8); exact absurd this (by decide)
    · exact hZ56 heq.symm
  have hZ2_inU : inU (src D Z2) := by
    have hj := (sem_mem_W.1 hZ2_2).1
    have hlt := src_lt hS hj
    exact ⟨by omega, hZ2_src_45, hZ2_not4, hZ2_not5⟩
  have hZ6_inU : inU (src D Z6) := by
    have hj := (sem_mem_W.1 (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)).1
    have hlt := src_lt hS hj
    exact ⟨by omega, hZ6_src_45, hZ6_not4, hZ6_not5⟩
  have hU_entry : ∀ w, inU w → w = 10 + Z4.1 ∨ ∃ a, stepU a w := by
    intro w hw
    obtain ⟨hwlt, hwv, h4n, h5n⟩ := hw
    have hwge : 10 ≤ w := by
      by_contra hc
      rw [val_input D _ w (by omega)] at hwv
      simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hwv
      rcases hwv with h' | h'
      · exact h4n (by rw [mem_supp, val_input D _ w (by omega)]; exact decide_eq_true h')
      · exact h5n (by rw [mem_supp, val_input D _ w (by omega)]; exact decide_eq_true h')
    obtain ⟨j, rfl⟩ : ∃ j, w = 10 + j := ⟨w - 10, by omega⟩
    have hj : j < D.length := by omega
    obtain ⟨ha_lt, hb_lt, -⟩ := hS j hj
    rw [val_gate hS _ j hj] at hwv
    by_cases ht : tag D j = true
    · rw [ht, gop_true, Bool.and_eq_true] at hwv
      by_cases haU : (4 : Fin 10) ∉ supp 10 D (opA D j) ∧ (5 : Fin 10) ∉ supp 10 D (opA D j)
      · right; exact ⟨opA D j, ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ⟨by omega, hwv.1, haU.1, haU.2⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_true, hwv.1, hwv.2]; rfl, h4n, h5n⟩⟩⟩
      · by_cases hbU : (4 : Fin 10) ∉ supp 10 D (opB D j) ∧ (5 : Fin 10) ∉ supp 10 D (opB D j)
        · right; exact ⟨opB D j, ⟨⟨by omega, by omega, Or.inr (by simp)⟩, ⟨by omega, hwv.2, hbU.1, hbU.2⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_true, hwv.1, hwv.2]; rfl, h4n, h5n⟩⟩⟩
        · left
          rw [not_and_or, Classical.not_not, Classical.not_not] at haU hbU
          have ha45 : ¬((4 : Fin 10) ∈ supp 10 D (opA D j) ∧ (4 : Fin 10) ∈ supp 10 D (opB D j)) :=
            fun h' => h4n (by rw [sem_supp_and hS hj ht, Finset.mem_inter]; exact h')
          have hb45 : ¬((5 : Fin 10) ∈ supp 10 D (opA D j) ∧ (5 : Fin 10) ∈ supp 10 D (opB D j)) :=
            fun h' => h5n (by rw [sem_supp_and hS hj ht, Finset.mem_inter]; exact h')
          have hpair : ∃ s : Bool, (j, s) ∈ sem_W 10 D 4 ∧ (j, !s) ∈ sem_W 10 D 5 := by
            rcases haU with ha4 | ha5 <;> rcases hbU with hb4 | hb5
            · exact absurd ⟨ha4, hb4⟩ ha45
            · exact ⟨false, sem_mem_W.2 ⟨hj, by simpa [src] using ha4, h4n⟩,
                sem_mem_W.2 ⟨hj, by simpa [src] using hb5, h5n⟩⟩
            · exact ⟨true, sem_mem_W.2 ⟨hj, by simpa [src] using hb4, h4n⟩,
                sem_mem_W.2 ⟨hj, by simpa [src] using ha5, h5n⟩⟩
            · exact absurd ⟨ha5, hb5⟩ hb45
          obtain ⟨s, hs4, hs5⟩ := hpair
          rw [hW4, Finset.mem_insert, Finset.mem_singleton] at hs4
          rcases hs4 with h0eq | h4eq
          · exfalso
            have hs5' : sem_bar (pos 0) ∈ sem_W 10 D 5 := by
              rw [← h0eq]; exact hs5
            exact absurd (as_priv hpos h0 hs5') (by decide)
          · have := congrArg Prod.fst h4eq; omega
    · rw [Bool.not_eq_true] at ht
      rw [ht, gop_false, Bool.or_eq_true] at hwv
      have h4a : (4 : Fin 10) ∉ supp 10 D (opA D j) := fun hm => h4n (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl hm)
      have h4b : (4 : Fin 10) ∉ supp 10 D (opB D j) := fun hm => h4n (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr hm)
      have h5a : (5 : Fin 10) ∉ supp 10 D (opA D j) := fun hm => h5n (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl hm)
      have h5b : (5 : Fin 10) ∉ supp 10 D (opB D j) := fun hm => h5n (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr hm)
      right
      rcases hwv with ha1 | hb1
      · exact ⟨opA D j, ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ⟨by omega, ha1, h4a, h5a⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_false, ha1]; rfl, h4n, h5n⟩⟩⟩
      · exact ⟨opB D j, ⟨⟨by omega, by omega, Or.inr (by simp)⟩, ⟨by omega, hb1, h4b, h5b⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_false, hb1]; simp, h4n, h5n⟩⟩⟩
  have hU_reach : ∀ w, inU w → Relation.ReflTransGen stepU (10 + Z4.1) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      rcases hU_entry w hw with rfl | ⟨a, ha⟩
      · exact Relation.ReflTransGen.refl
      · have hlt : a < w := sem_step_lt hS ha.1
        exact (ih a hlt ha.2.1).tail ha

  have hfan_eq_b : ∀ w, 2 ≤ fanout D w → ∃ x ∈ eligSet 10 D, b x = w := by
    intro w hfw
    have hne_s : (supp 10 D w).Nonempty := sem_bzero_branch hS hB0 (by omega)
    have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
      rw [unitsPlus, Finset.mem_filter, mem_units]
      exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)),
        by show 0 + 1 < fanout D w; omega⟩, hne_s⟩
    have hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D b := by
      by_contra hnr
      have : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits 10 D b := Finset.mem_sdiff.2 ⟨hwu, hnr⟩
      rw [hR0] at this; exact Finset.notMem_empty _ this
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 hwr
    exact ⟨x, hx, congrArg Sigma.fst hxe⟩
  have hfan1_det : ∀ {a c1 c2}, fanout D a = 1 → sem_step 10 D a c1 → sem_step 10 D a c2 → c1 = c2 :=
    fun hf h1 h2 => sem_step_unique h1 h2 hf

  have hsrc26 : src D Z2 ≠ src D Z6 := fun heq => by
    have h2in : (2 : Fin 10) ∈ supp 10 D (src D Z6) := heq ▸ (sem_mem_W.1 hZ2_2).2.1
    have hZ6_in2 := zm_mem hS hM2 (sem_mem_W.1 (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)).1
      (sem_W_and hS (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)) h2in
    rw [hW2_eq, Finset.mem_insert, Finset.mem_singleton] at hZ6_in2
    rcases hZ6_in2 with h61 | h62
    · exact absurd (as_priv hpos h1 (by rw [← h61]; exact hZ6_8)) (by decide)
    · exact hZ26 h62.symm

  have hstep_Z2 : sem_step 10 D (src D Z2) (10 + Z2.1) := by
    have hj := (sem_mem_W.1 hZ2_2).1
    exact ⟨by omega, by omega, by cases hs : Z2.2 <;> simp [src, hs]⟩
  have hstep_Z6 : sem_step 10 D (src D Z6) (10 + Z6.1) := by
    have hj := (sem_mem_W.1 (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)).1
    exact ⟨by omega, by omega, by cases hs : Z6.2 <;> simp [src, hs]⟩

  have hex_split : ∃ w, inU w ∧ 2 ≤ fanout D w := by
    by_contra hno
    push Not at hno
    have hdet : ∀ a c1 c2, stepU a c1 → stepU a c2 → c1 = c2 := fun a c1 c2 s1 s2 => by
      have hf0 : 1 ≤ fanout D a := by
        have hm : c1 - 10 ∈ readers D a := Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), s1.1.2.2⟩
        exact Finset.card_pos.2 ⟨_, hm⟩
      have hf2 := hno a s1.2.1
      exact hfan1_det (by omega) s1.1 s2.1
    have hp2 := hU_reach _ hZ2_inU
    have hp6 := hU_reach _ hZ6_inU
    have htot : ∀ {a x y}, Relation.ReflTransGen stepU a x → Relation.ReflTransGen stepU a y →
        Relation.ReflTransGen stepU x y ∨ Relation.ReflTransGen stepU y x := by
      intro a x y hx
      induction hx using Relation.ReflTransGen.head_induction_on with
      | refl => intro hy; exact Or.inl hy
      | head hab hbx ih =>
        intro hy
        rcases Relation.ReflTransGen.cases_head hy with rfl | ⟨c, hac, hcy⟩
        · exact Or.inr (Relation.ReflTransGen.head hab hbx)
        · exact ih (hdet _ _ c hab hac ▸ hcy)
    rcases htot hp2 hp6 with h26 | h62
    · rcases Relation.ReflTransGen.cases_head h26 with heq | ⟨c, hc, -⟩
      · exact hsrc26 heq
      · have hf2 := hno _ hZ2_inU
        have hf1 := sem_step_fanout hstep_Z2
        have hceq := hfan1_det (by omega) hc.1 hstep_Z2
        have hv := hc.2.2.2.1; rw [hceq, hZ2_45_f] at hv; exact Bool.false_ne_true hv
    · rcases Relation.ReflTransGen.cases_head h62 with heq | ⟨c, hc, -⟩
      · exact hsrc26 heq.symm
      · have hf6 := hno _ hZ6_inU
        have hf1 := sem_step_fanout hstep_Z6
        have hceq := hfan1_det (by omega) hc.1 hstep_Z6
        have hv := hc.2.2.2.1; rw [hceq, hZ6_45_f] at hv; exact Bool.false_ne_true hv

  let wb := Nat.find hex_split
  have hwb_spec : inU wb ∧ 2 ≤ fanout D wb := Nat.find_spec hex_split
  have hwb_min : ∀ w, w < wb → inU w → fanout D w ≤ 1 := fun w hlt hw => by
    by_contra hc; exact Nat.find_min hex_split hlt ⟨hw, by omega⟩
  obtain ⟨x, hxE, hbx⟩ := hfan_eq_b wb hwb_spec.2

  have hreach_from_wb : ∀ w, inU w → (∀ c, stepU w c → False) → Relation.ReflTransGen stepU wb w := by
    intro w hw hdead
    have hdet_lt : ∀ a c1 c2, a < wb → stepU a c1 → stepU a c2 → c1 = c2 := fun a c1 c2 hlt s1 s2 => by
      have hf1 := sem_step_fanout s1.1
      have hf2 := hwb_min a hlt s1.2.1
      exact hfan1_det (by omega) s1.1 s2.1
    have hp_wb := hU_reach wb hwb_spec.1
    have hp_w := hU_reach w hw
    have hsplit : ∀ {a}, Relation.ReflTransGen stepU a wb → Relation.ReflTransGen stepU a w →
        Relation.ReflTransGen stepU wb w ∨ Relation.ReflTransGen stepU w wb := by
      intro a h1
      induction h1 using Relation.ReflTransGen.head_induction_on with
      | refl => intro h2; exact Or.inl h2
      | head hac hcwb ih =>
        intro h2
        rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨d, had, hdw⟩
        · exact Or.inr (Relation.ReflTransGen.head hac hcwb)
        · have halt := (sem_step_lt hS hac.1).trans_le (sem_rtg_le hS (fun _ _ s => s.1) hcwb)
          exact ih (hdet_lt _ _ d halt hac had ▸ hdw)
    rcases hsplit hp_wb hp_w with h1 | h2
    · exact h1
    · rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨c, hc, -⟩
      · exact Relation.ReflTransGen.refl
      · exact absurd hc (hdead c)
  have hwb_gt_Z4 : 10 + Z4.1 < wb := by
    have hle := sem_rtg_le hS (fun _ _ s => s.1) (hU_reach wb hwb_spec.1)
    have hne : 10 + Z4.1 ≠ wb := fun heq => by
      have hx_in : x ∈ supp 10 D (10 + Z4.1) := by rw [heq, ← hbx, (hb x hxE).2.1]; exact Finset.mem_singleton_self x
      have hx_not_in : ∀ v : Fin 10, v ∈ eligSet 10 D → v ∉ supp 10 D (10 + Z4.1) := by
        intro v hvE hvm
        have hj4 := (sem_mem_W.1 hZ4_4).1
        have ht4 := sem_W_and hS hZ4_4
        fin_cases v
        · exact (Finset.mem_sdiff.1 h0).2 hvE
        · exact (Finset.mem_sdiff.1 h1).2 hvE
        · exact Bool.noConfusion (ht4.symm.trans (sem_zm_gate hS hM2 hj4 hvm).1)
        · exact (sem_mem_W.1 hZ4_3).2.2 hvm
        · exact (sem_mem_W.1 hZ4_4).2.2 hvm
        · exact (sem_mem_W.1 hb4_5).2.2 hvm
        · exact Bool.noConfusion (ht4.symm.trans (sem_zm_gate hS hM6 hj4 hvm).1)
        · exact (sem_mem_W.1 (by rw [hZ4_eq_b5]; exact hZ5_7)).2.2 hvm
        · exact (sem_mem_W.1 hZ4_8).2.2 hvm
        · exact (sem_mem_W.1 hZ4_9).2.2 hvm
      exact hx_not_in x hxE hx_in
    omega

  have hno_before_Z4 : ∀ y : Fin 10, y ∈ eligSet 10 D → b y = wb →
      ∀ e : ℕ × Bool, e ∈ sem_W 10 D y → e.1 = Z4.1 → False := by
    intro y hyE hby e heW he1
    have hysrc := (sem_mem_W.1 heW).2.1
    have hsrc_lt : src D e < 10 + Z4.1 := by rw [← he1]; exact src_lt hS (sem_mem_W.1 heW).1
    have hmin_y : ∀ w, y ∈ supp 10 D w → 2 ≤ fanout D w → wb ≤ w := fun w hw hfw => by
      rw [← hby]; exact (hb y hyE).2.2.2 w hfw hw
    have hpath_src : Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) y.val (src D e) :=
      sem_supp_path hS (w := src D e) hysrc
    have hpath_wb : Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) y.val wb :=
      sem_supp_path hS (w := wb) (by rw [← hby, (hb y hyE).2.1]; exact Finset.mem_singleton_self y)
    have htot_y : ∀ {a}, Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) a wb →
        Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) a (src D e) →
        Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) (src D e) wb := by
      intro a h1
      induction h1 using Relation.ReflTransGen.head_induction_on with
      | refl => intro h2; have := sem_rtg_le hS (fun _ _ s => s.1) h2; omega
      | @head a c hac hcwb ih =>
        intro h2
        rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨d, had, hds⟩
        · exact Relation.ReflTransGen.head hac hcwb
        · have halt := (sem_step_lt hS hac.1).trans_le (sem_rtg_le hS (fun _ _ s => s.1) hcwb)
          have hf2 : fanout D a ≤ 1 := by by_contra hf; have := hmin_y a hac.2.1 (by omega); omega
          have hf1 := sem_step_fanout hac.1
          exact ih (hfan1_det (by omega) hac.1 had.1 ▸ hds)
    have hsrc_wb := htot_y hpath_wb hpath_src
    rcases Relation.ReflTransGen.cases_head hsrc_wb with heq | ⟨c, hc, -⟩
    · omega
    · have hf2 : fanout D (src D e) ≤ 1 := by by_contra hf; have := hmin_y _ hysrc (by omega); omega
      have hstepe : sem_step 10 D (src D e) (10 + e.1) := sem_step_src (sem_mem_W.1 heW).1 e.2
      have hf1 := sem_step_fanout hstepe
      have hceq := hfan1_det (by omega) hc.1 hstepe
      exact (sem_mem_W.1 heW).2.2 (hceq ▸ hc.2.2)

  have hexit_inU : ∀ (y : Fin 10), y ∈ eligSet 10 D → b y = wb → ∀ t, Relation.ReflTransGen stepU wb t →
      y ∉ supp 10 D t → ∃ e ∈ sem_W 10 D y, inU (10 + e.1) ∧ 10 + e.1 ≤ t := by
    intro y hyE hby t hp hyt
    have hywb : y ∈ supp 10 D wb := by rw [← hby, (hb y hyE).2.1]; exact Finset.mem_singleton_self y
    induction hp with
    | refl => exact absurd hywb hyt
    | @tail u v huv hstep ih =>
      by_cases hyu : y ∈ supp 10 D u
      · obtain ⟨hjlt, hjge, hop⟩ := hstep.1
        have hveq : 10 + (v - 10) = v := by omega
        have heW : ∃ s : Bool, (v - 10, s) ∈ sem_W 10 D y := by
          rcases hop with ha | hb'
          · exact ⟨false, sem_mem_W.2 ⟨by omega, by simpa [src, ha] using hyu, by rwa [hveq]⟩⟩
          · exact ⟨true, sem_mem_W.2 ⟨by omega, by simpa [src, hb'] using hyu, by rwa [hveq]⟩⟩
        obtain ⟨s, hs⟩ := heW
        exact ⟨(v - 10, s), hs, by simpa [hveq] using hstep.2.2, by omega⟩
      · obtain ⟨e, heW, heU, hele⟩ := ih hyu
        exact ⟨e, heW, heU, hele.trans (sem_step_lt hS hstep.1).le⟩

  have hwb_to_ge : ∀ w, inU w → wb ≤ w → Relation.ReflTransGen stepU wb w := by
    intro w hw hle
    have hdet_lt : ∀ a c1 c2, a < wb → stepU a c1 → stepU a c2 → c1 = c2 := fun a c1 c2 hlt s1 s2 => by
      have hf1 := sem_step_fanout s1.1
      have hf2 := hwb_min a hlt s1.2.1
      exact hfan1_det (by omega) s1.1 s2.1
    have hsplit : ∀ {a}, Relation.ReflTransGen stepU a wb → Relation.ReflTransGen stepU a w →
        Relation.ReflTransGen stepU wb w ∨ Relation.ReflTransGen stepU w wb := by
      intro a h1
      induction h1 using Relation.ReflTransGen.head_induction_on with
      | refl => intro h2; exact Or.inl h2
      | head hac hcwb ih =>
        intro h2
        rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨d, had, hdw⟩
        · exact Or.inr (Relation.ReflTransGen.head hac hcwb)
        · have halt := (sem_step_lt hS hac.1).trans_le (sem_rtg_le hS (fun _ _ s => s.1) hcwb)
          exact ih (hdet_lt _ _ d halt hac had ▸ hdw)
    rcases hsplit (hU_reach wb hwb_spec.1) (hU_reach w hw) with h1 | h2
    · exact h1
    · rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨c, hc, hcw⟩
      · exact Relation.ReflTransGen.refl
      · have h1 := sem_step_lt hS hc.1
        have h2 := sem_rtg_le hS (fun _ _ s => s.1) hcw
        omega
  have hwb_le_Z2 : wb ≤ src D Z2 := by
    by_contra hlt; push Not at hlt
    have hdead : ∀ c, stepU (src D Z2) c → False := fun c hc => by
      have hf1 := sem_step_fanout hstep_Z2
      have hf2 := hwb_min _ hlt hZ2_inU
      have hceq := hfan1_det (by omega) hc.1 hstep_Z2
      have hv := hc.2.2.2.1; rw [hceq, hZ2_45_f] at hv; exact Bool.false_ne_true hv
    have hreach := hreach_from_wb _ hZ2_inU hdead
    have := sem_rtg_le hS (fun _ _ s => s.1) hreach; omega
  have hwb_le_Z6 : wb ≤ src D Z6 := by
    by_contra hlt; push Not at hlt
    have hdead : ∀ c, stepU (src D Z6) c → False := fun c hc => by
      have hf1 := sem_step_fanout hstep_Z6
      have hf2 := hwb_min _ hlt hZ6_inU
      have hceq := hfan1_det (by omega) hc.1 hstep_Z6
      have hv := hc.2.2.2.1; rw [hceq, hZ6_45_f] at hv; exact Bool.false_ne_true hv
    have hreach := hreach_from_wb _ hZ6_inU hdead
    have := sem_rtg_le hS (fun _ _ s => s.1) hreach; omega
  have hwb_reach_Z2 := hwb_to_ge _ hZ2_inU hwb_le_Z2
  have hwb_reach_Z6 := hwb_to_ge _ hZ6_inU hwb_le_Z6

  have hkill_pos1 : ∀ (y : Fin 10) (Zy : ℕ × Bool), y ∈ eligSet 10 D → b y = wb →
      sem_W 10 D y = {pos 1, Zy} → val D (sem_two (4 : Fin 10) (5 : Fin 10)) (10 + Zy.1) = false →
      inU (10 + (pos 1).1) → False := by
    intro y Zy hyE hby hWy hZyf hp1U
    have hj1 := (hpos.1 1 h1).1
    have ht1 : tag D (pos 1).1 = true := sem_W_and hS (as_mem hpos h1 (by decide : Adj 1 2))
    have hval1 := hp1U.2.1
    rw [val_gate hS _ (pos 1).1 hj1, ht1, gop_true, Bool.and_eq_true] at hval1
    have hbar1_val : val D (sem_two (4 : Fin 10) (5 : Fin 10)) (src D (sem_bar (pos 1))) = true := by
      cases hs : (pos 1).2 <;> simp [src, sem_bar, hs] at hval1 ⊢
      · exact hval1.2
      · exact hval1.1
    have hbar1_supp : supp 10 D (src D (sem_bar (pos 1))) = {1} := by
      rw [show src D (sem_bar (pos 1)) = src D ((pos 1).1, !(pos 1).2) from rfl]; exact (hpos.1 1 h1).2.2.2
    have hbar1_lt : src D (sem_bar (pos 1)) < 10 + (pos 1).1 := src_lt hS (e := sem_bar (pos 1)) hj1
    have hbar1_inU : inU (src D (sem_bar (pos 1))) :=
      ⟨by omega, hbar1_val, by rw [hbar1_supp]; decide, by rw [hbar1_supp]; decide⟩
    have hwb_le_bar1 : wb ≤ src D (sem_bar (pos 1)) := by
      by_contra hlt; push Not at hlt
      have hstep1 : sem_step 10 D (src D (sem_bar (pos 1))) (10 + (pos 1).1) := sem_step_src hj1 (sem_bar (pos 1)).2
      have hlt' : src D (sem_bar (pos 1)) < wb := hlt
      have hf2 := hwb_min _ hlt' hbar1_inU
      have hf1 := sem_step_fanout hstep1
      have hdet_lt : ∀ a c1 c2, a < wb → stepU a c1 → stepU a c2 → c1 = c2 := fun a c1 c2 hlt'' s1 s2 => by
        have hf1' := sem_step_fanout s1.1
        have hf2' := hwb_min a hlt'' s1.2.1
        exact hfan1_det (by omega) s1.1 s2.1
      have hsplit : ∀ {a}, Relation.ReflTransGen stepU a wb → Relation.ReflTransGen stepU a (src D (sem_bar (pos 1))) →
          Relation.ReflTransGen stepU wb (src D (sem_bar (pos 1))) ∨ Relation.ReflTransGen stepU (src D (sem_bar (pos 1))) wb := by
        intro a h1'
        induction h1' using Relation.ReflTransGen.head_induction_on with
        | refl => intro h2'; exact Or.inl h2'
        | head hac hcwb ih =>
          intro h2'
          rcases Relation.ReflTransGen.cases_head h2' with rfl | ⟨d, had, hdw⟩
          · exact Or.inr (Relation.ReflTransGen.head hac hcwb)
          · have halt := (sem_step_lt hS hac.1).trans_le (sem_rtg_le hS (fun _ _ s => s.1) hcwb)
            exact ih (hdet_lt _ _ d halt hac had ▸ hdw)
      rcases hsplit (hU_reach wb hwb_spec.1) (hU_reach _ hbar1_inU) with h1' | h2'
      · have := sem_rtg_le hS (fun _ _ s => s.1) h1'; omega
      · rcases Relation.ReflTransGen.cases_head h2' with heq | ⟨c, hc, hcwb⟩
        · omega
        · have hceq := hfan1_det (by omega) hc.1 hstep1
          rw [hceq] at hcwb
          have hle := sem_rtg_le hS (fun _ _ s => s.1) hcwb
          have hp1W : pos 1 ∈ sem_W 10 D y := by rw [hWy]; simp
          have hysrc := (sem_mem_W.1 hp1W).2.1
          have hsrc_lt : src D (pos 1) < wb := (src_lt hS (e := pos 1) hj1).trans_le hle
          have hmin_y : ∀ w, y ∈ supp 10 D w → 2 ≤ fanout D w → wb ≤ w := fun w hw hfw => by
            rw [← hby]; exact (hb y hyE).2.2.2 w hfw hw
          have htot_y : ∀ {a}, Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) a wb →
              Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) a (src D (pos 1)) →
              Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) (src D (pos 1)) wb := by
            intro a h1''
            induction h1'' using Relation.ReflTransGen.head_induction_on with
            | refl => intro h2''; have := sem_rtg_le hS (fun _ _ s => s.1) h2''; omega
            | @head a c hac hcwb' ih =>
              intro h2''
              rcases Relation.ReflTransGen.cases_head h2'' with rfl | ⟨d, had, hds⟩
              · exact Relation.ReflTransGen.head hac hcwb'
              · have halt := (sem_step_lt hS hac.1).trans_le (sem_rtg_le hS (fun _ _ s => s.1) hcwb')
                have hf2' : fanout D a ≤ 1 := by by_contra hf; have := hmin_y a hac.2.1 (by omega); omega
                have hf1' := sem_step_fanout hac.1
                exact ih (hfan1_det (by omega) hac.1 had.1 ▸ hds)
          have hsrc_wb := htot_y
            (sem_supp_path hS (w := wb) (by rw [← hby, (hb y hyE).2.1]; exact Finset.mem_singleton_self y))
            (sem_supp_path hS (w := src D (pos 1)) hysrc)
          rcases Relation.ReflTransGen.cases_head hsrc_wb with heq | ⟨c', hc', -⟩
          · omega
          · have hf2' : fanout D (src D (pos 1)) ≤ 1 := by by_contra hf; have := hmin_y _ hysrc (by omega); omega
            have hstepp : sem_step 10 D (src D (pos 1)) (10 + (pos 1).1) := sem_step_src hj1 (pos 1).2
            have hf1' := sem_step_fanout hstepp
            have hceq' := hfan1_det (by omega) hc'.1 hstepp
            exact (sem_mem_W.1 hp1W).2.2 (hceq' ▸ hc'.2.2)
    have hwb_to_bar1 := hwb_to_ge _ hbar1_inU hwb_le_bar1
    have hy_not1 : y ∉ supp 10 D (src D (sem_bar (pos 1))) := by
      rw [hbar1_supp, Finset.mem_singleton]
      intro hy1; subst hy1; exact (Finset.mem_sdiff.1 h1).2 hyE
    obtain ⟨e', he'W, he'U, he'le⟩ := hexit_inU y hyE hby _ hwb_to_bar1 hy_not1
    rw [hWy, Finset.mem_insert, Finset.mem_singleton] at he'W
    rcases he'W with rfl | rfl
    · omega
    · have hv := he'U.2.1; rw [hZyf] at hv; exact Bool.false_ne_true hv
  have hx_in_wb : x ∈ supp 10 D wb := by rw [← hbx, (hb x hxE).2.1]; exact Finset.mem_singleton_self x
  fin_cases x
  · exact (Finset.mem_sdiff.1 h0).2 hxE
  · exact (Finset.mem_sdiff.1 h1).2 hxE
  ·
    have h2n6 : (2 : Fin 10) ∉ supp 10 D (src D Z6) := fun hm => by
      have hmW := zm_mem hS hM2 (sem_mem_W.1 (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)).1
        (sem_W_and hS (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)) hm
      rw [hW2_eq, Finset.mem_insert, Finset.mem_singleton] at hmW
      rcases hmW with heq | heq
      · exact absurd (as_priv hpos h1 (by rw [← heq]; exact hZ6_8)) (by decide)
      · exact hZ26 heq.symm
    obtain ⟨e, heW, heU, -⟩ := hexit_inU 2 hxE hbx _ hwb_reach_Z6 h2n6
    rw [hW2_eq, Finset.mem_insert, Finset.mem_singleton] at heW
    rcases heW with rfl | rfl
    · exact hkill_pos1 2 Z2 hxE hbx hW2_eq hZ2_45_f heU
    · have hv := heU.2.1; rw [hZ2_45_f] at hv; exact Bool.false_ne_true hv
  · exact hno_before_Z4 3 hxE hbx (sem_bar Z4) hZ4_3 rfl
  · exact hwb_spec.1.2.2.1 hx_in_wb
  · exact hwb_spec.1.2.2.2 hx_in_wb
  ·
    have h6n2 : (6 : Fin 10) ∉ supp 10 D (src D Z2) := fun hm => by
      have hmW := zm_mem hS hM6 (sem_mem_W.1 hZ2_2).1 (sem_W_and hS hZ2_2) hm
      rw [hW6, Finset.mem_insert, Finset.mem_singleton] at hmW
      rcases hmW with heq | heq
      · exact absurd (as_priv hpos h1 (by rw [← heq]; exact hZ2_7)) (by decide)
      · exact hZ26 heq
    obtain ⟨e, heW, heU, -⟩ := hexit_inU 6 hxE hbx _ hwb_reach_Z2 h6n2
    rw [hW6, Finset.mem_insert, Finset.mem_singleton] at heW
    rcases heW with rfl | rfl
    · exact hkill_pos1 6 Z6 hxE hbx hW6 hZ6_45_f heU
    · have hv := heU.2.1; rw [hZ6_45_f] at hv; exact Bool.false_ne_true hv
  · exact hno_before_Z4 7 hxE hbx Z4 (by rw [hZ4_eq_b5]; exact hZ5_7) rfl
  · exact hno_before_Z4 8 hxE hbx Z4 hZ4_8 rfl
  · exact hno_before_Z4 9 hxE hbx (sem_bar Z4) hZ4_9 rfl

def r0_wit (idx : Fin 44) : ℕ × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 :=
  match idx.val with
  | 0 => (0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 1 => (1, 5, 7, 8, 0, 2, 1, 0, 0)
  | 2 => (0, 4, 0, 3, 9, 0, 0, 0, 0)
  | 3 => (1, 6, 9, 8, 1, 4, 0, 0, 0)
  | 4 => (1, 8, 6, 3, 5, 1, 2, 0, 0)
  | 5 => (0, 7, 2, 5, 9, 0, 0, 0, 0)
  | 6 => (0, 8, 3, 5, 6, 0, 0, 0, 0)
  | 7 => (1, 9, 7, 6, 4, 5, 0, 0, 0)
  | 8 => (1, 5, 8, 7, 0, 6, 1, 0, 0)
  | 9 => (1, 9, 7, 4, 6, 2, 1, 0, 0)
  | 10 => (0, 8, 3, 6, 5, 0, 0, 0, 0)
  | 11 => (0, 9, 4, 6, 7, 0, 0, 0, 0)
  | 12 => (0, 8, 5, 6, 3, 0, 0, 0, 0)
  | 13 => (0, 9, 6, 7, 4, 0, 0, 0, 0)
  | 14 => (0, 4, 0, 9, 3, 0, 0, 0, 0)
  | 15 => (0, 6, 1, 9, 8, 0, 0, 0, 0)
  | 16 => (0, 7, 5, 9, 2, 0, 0, 0, 0)
  | 17 => (0, 4, 0, 3, 9, 0, 0, 0, 0)
  | 18 => (0, 8, 3, 5, 6, 0, 0, 0, 0)
  | 19 => (0, 7, 2, 5, 9, 0, 0, 0, 0)
  | 20 => (1, 8, 6, 3, 5, 1, 2, 0, 0)
  | 21 => (0, 7, 2, 5, 9, 0, 0, 0, 0)
  | 22 => (1, 5, 7, 8, 0, 2, 1, 0, 0)
  | 23 => (0, 4, 0, 3, 9, 0, 0, 0, 0)
  | 24 => (0, 8, 3, 6, 5, 0, 0, 0, 0)
  | 25 => (0, 9, 4, 6, 7, 0, 0, 0, 0)
  | 26 => (0, 7, 2, 5, 9, 0, 0, 0, 0)
  | 27 => (0, 8, 3, 5, 6, 0, 0, 0, 0)
  | 28 => (0, 8, 5, 6, 3, 0, 0, 0, 0)
  | 29 => (0, 5, 0, 7, 8, 0, 0, 0, 0)
  | 30 => (0, 9, 4, 6, 7, 0, 0, 0, 0)
  | 31 => (0, 4, 0, 9, 3, 0, 0, 0, 0)
  | 32 => (0, 4, 0, 9, 3, 0, 0, 0, 0)
  | 33 => (0, 4, 0, 3, 9, 0, 0, 0, 0)
  | 34 => (0, 6, 1, 9, 8, 0, 0, 0, 0)
  | 35 => (0, 7, 2, 5, 9, 0, 0, 0, 0)
  | 36 => (0, 4, 3, 9, 0, 0, 0, 0, 0)
  | 37 => (0, 4, 0, 3, 9, 0, 0, 0, 0)
  | 38 => (0, 7, 2, 5, 9, 0, 0, 0, 0)
  | 39 => (0, 7, 2, 5, 9, 0, 0, 0, 0)
  | 40 => (0, 4, 0, 3, 9, 0, 0, 0, 0)
  | 41 => (0, 4, 0, 3, 9, 0, 0, 0, 0)
  | 42 => (0, 4, 3, 9, 0, 0, 0, 0, 0)
  | _ => (0, 4, 3, 9, 0, 0, 0, 0, 0)

theorem r0_wit_ok0 : ∀ idx : Fin 44, idx.val ≠ 0 → (r0_wit idx).1 = 0 →
    let I := hc_rep idx
    let (_, a, b, c, d, _, _, _, _) := r0_wit idx
    b ∈ I ∧ c ∈ I ∧ b ≠ c ∧ hc_adjB b a = true ∧ hc_adjB c a = true ∧ hc_adjB a d = true ∧ d ≠ b ∧ d ≠ c := by
  decide +kernel

theorem r0_wit_ok1 : ∀ idx : Fin 44, idx.val ≠ 0 → (r0_wit idx).1 = 1 →
    let I := hc_rep idx
    let (_, a, b, c, d, e, f, _, _) := r0_wit idx
    (d ∈ I ∧ e ∈ I ∧ a ∉ I ∧ b ∉ I ∧ c ∉ I) ∧
    (hc_adjB d a = true ∧ hc_adjB e b = true ∧ hc_adjB a b = true ∧ hc_adjB a c = true ∧
     c ≠ b ∧ (g10_nbB b).card = 3 ∧ hc_adjB e f = true ∧ f ≠ b ∧ hc_adjB f c = false) := by
  decide +kernel

theorem r0_wit_ok2 : ∀ idx : Fin 44, idx.val ≠ 0 → (r0_wit idx).1 ≠ 0 → (r0_wit idx).1 ≠ 1 →
    let I := hc_rep idx
    let (_, a, b, c, d, e, f, g, h') := r0_wit idx
    (e ∈ I ∧ f ∈ I ∧ a ∉ I) ∧
    (hc_adjB a b = true ∧ hc_adjB a c = true ∧ hc_adjB a d = true ∧
     hc_adjB e b = true ∧ hc_adjB f c = true ∧ b ≠ c ∧ d ≠ b ∧ d ≠ c ∧
     (g10_nbB b).card = 3 ∧ (g10_nbB c).card = 3) ∧
    (hc_adjB e g = true ∧ g ≠ b ∧ hc_adjB g c = false ∧ hc_adjB g d = false ∧
     hc_adjB f h' = true ∧ h' ≠ c ∧ hc_adjB h' d = false) := by
  decide +kernel

theorem elim_R0_all {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (h8 : totalSurplus 10 D ≤ 8) (hB : Bplus 10 D ≤ (eligSet 10 D).card)
    (idx : Fin 44) (hI : ineligSet 10 D = hc_rep idx) : False := by
  obtain ⟨b, hb⟩ := exists_pureBranch h hD
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h (sem_g10_comp hD)
  have hres : residualUnits 10 D b = ∅ := by
    have h1 := card_residual h.1 b hb
    have h2 := elig_le_Bplus h.1 b hb
    exact Finset.card_eq_zero.1 (by omega)
  have hW2 : ∀ x, (sem_W 10 D x).card ≤ 2 := fun x => by
    have h1 := cc_le h hD b hb x
    unfold ru at h1; rw [hres] at h1
    simp only [Finset.filter_empty, Finset.card_empty] at h1; omega
  by_cases h0 : idx.val = 0
  · have hIeq : ineligSet 10 D = {0, 1} := by
      rw [hI, show idx = ⟨0, by decide⟩ from Fin.ext h0]; decide
    exact elim_01_R0 h hD h8 hIeq
  · rcases hrw : r0_wit idx with ⟨k, a1, a2, a3, a4, a5, a6, a7, a8⟩
    by_cases hk0 : k = 0
    · have hw := r0_wit_ok0 idx h0 (by rw [hrw]; exact hk0)
      rw [hrw] at hw; dsimp only at hw
      obtain ⟨hi1, hi2, hg⟩ := hw
      have h3 := two_in_deg3 h hD hpos (hI ▸ hi1) (hI ▸ hi2) hg
      have := hW2 a1; omega
    · by_cases hk1 : k = 1
      · have hw := r0_wit_ok1 idx h0 (by rw [hrw]; exact hk1)
        rw [hrw] at hw; dsimp only at hw
        obtain ⟨⟨hd, he, ha, hb', hc'⟩, hg⟩ := hw
        exact pa_m1_gen h hD hpos a1 a2 a3 a4 a5 a6 (hI ▸ hd) (hI ▸ he) (hI ▸ ha) (hI ▸ hb') (hI ▸ hc') hg
          (hW2 a1) (hW2 a2)
      · have hw := r0_wit_ok2 idx h0 (by rw [hrw]; exact hk0) (by rw [hrw]; exact hk1)
        rw [hrw] at hw; dsimp only at hw
        obtain ⟨⟨he, hf, ha⟩, ⟨g1, g2, g3, g4, g5, hbc, hdb, hdc, hdb3, hdc3⟩,
          ⟨g6, hgb, hgc, hgd, g7, hhc, hhd⟩⟩ := hw
        exact ps_3star_gen h hD hpos a1 a2 a3 a4 a5 a6 a7 a8 (hI ▸ he) (hI ▸ hf) (hI ▸ ha)
          ⟨g1, g2, g3, g4, g5, hbc, hdb, hdc, hdb3, hdc3, g6, hgb, hgc, hgd, g7, hhc, hhd⟩
          (hW2 a1) (hW2 a2) (hW2 a3)

def pa_ctx (D : Dag) (pos : Fin 10 → ℕ × Bool) (P Q : ℕ × Bool) : Prop :=
  k4_Pos 10 G10 D pos ∧ (∀ x, (sem_W 10 D x).card ≤ 3) ∧ P ≠ Q ∧
    ∀ x, 3 ≤ (sem_W 10 D x).card → P ∈ sem_W 10 D x ∧ Q ∈ sem_W 10 D x

theorem pa_setup_one {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hB : Bplus 10 D = (eligSet 10 D).card + 1) : ∃ pos P Q, pa_ctx D pos P Q := by
  classical
  have hG := sem_g10_gr
  have hC := sem_g10_comp hD
  obtain ⟨b, hb⟩ := sem_exists_minBranch hG h.1 hC
  have hbp := sem_minBranch_pure hb
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hC
  have h1 := card_residual h.1 b hbp
  have hc3 : ∀ x, (sem_W 10 D x).card ≤ 3 := fun x => by
    have h3 := cc_le h hD b hbp x
    have h4 : (ru D b x).card ≤ (residualUnits 10 D b).card := Finset.card_filter_le _ _
    omega
  by_cases hX : (Finset.univ.filter (fun x : Fin 10 => 3 ≤ (sem_W 10 D x).card)).Nonempty
  · obtain ⟨P, Q, hPQ, hall⟩ := sem_common_terminals hG h hC b hb (by omega) _ hX
      (fun x hx => (Finset.mem_filter.1 hx).2)
    exact ⟨pos, P, Q, hpos, hc3, fun hpq => hPQ (hpq ▸ rfl),
      fun x hx => hall x (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)⟩
  · refine ⟨pos, (0, false), (0, true), hpos, hc3, by decide, fun x hx => ?_⟩
    exact absurd ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩⟩ hX

theorem two_w3_R1_kill {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    {pos : Fin 10 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : pa_ctx D pos P Q)
    {x y i1 i2 vx j1 j2 vy q : Fin 10}
    (hi1 : i1 ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D)
    (hj1 : j1 ∈ ineligSet 10 D) (hj2 : j2 ∈ ineligSet 10 D)
    (hg : x ≠ y ∧ q ≠ x ∧ hc_adjB y q = false ∧ (g10_nbB x).card = 3 ∧
      i1 ≠ i2 ∧ hc_adjB i1 x = true ∧ hc_adjB i2 x = true ∧ hc_adjB x vx = true ∧ vx ≠ i1 ∧ vx ≠ i2 ∧
      j1 ≠ j2 ∧ hc_adjB j1 y = true ∧ hc_adjB j2 y = true ∧ hc_adjB y vy = true ∧ vy ≠ j1 ∧ vy ≠ j2 ∧
      hc_adjB i1 y = false ∧ hc_adjB i1 q = true) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨hxy, hqx, hnyq, hdx, h12, hx1, hx2, hxv, hv1, hv2, hj12, hy1, hy2, hyv, hvy1, hvy2, hni1y, hq1⟩ := hg
  have hx3 := two_in_deg3 h hD hpos hi1 hi2 ⟨h12, hx1, hx2, hxv, hv1, hv2⟩
  have hy3 := two_in_deg3 h hD hpos hj1 hj2 ⟨hj12, hy1, hy2, hyv, hvy1, hvy2⟩
  obtain ⟨hPx, hQx⟩ := hsat x hx3
  obtain ⟨hPy, hQy⟩ := hsat y hy3
  have hi1_not_Wy : pos i1 ∉ sem_W 10 D y := by
    have hpj1 := as_mem hpos hj1 ((hc_adjB_iff _ _).1 hy1)
    have hpj2 := as_mem hpos hj2 ((hc_adjB_iff _ _).1 hy2)
    have hpj12 : pos j1 ≠ pos j2 := fun e => hj12 (hpos.2 _ hj1 _ hj2 e)
    have hni1j1 : i1 ≠ j1 := fun e => by subst e; rw [hy1] at hni1y; exact Bool.noConfusion hni1y
    have hni1j2 : i1 ≠ j2 := fun e => by subst e; rw [hy2] at hni1y; exact Bool.noConfusion hni1y
    intro hm
    by_cases hvy : vy ∈ ineligSet 10 D
    · have hpvy := as_mem hpos hvy (adj_symm ((hc_adjB_iff _ _).1 hyv))
      have hni1vy : i1 ≠ vy := fun e => by
        subst e; exact sem_adjB_false.1 hni1y (adj_symm ((hc_adjB_iff y i1).1 hyv))
      rcases pa_three hpj1 hpj2 hpvy hpj12 (fun e => hvy1.symm (hpos.2 _ hj1 _ hvy e))
          (fun e => hvy2.symm (hpos.2 _ hj2 _ hvy e)) (hc3 y) (pos i1) hm with e | e | e
      · exact hni1j1 (hpos.2 _ hi1 _ hj1 e)
      · exact hni1j2 (hpos.2 _ hi1 _ hj2 e)
      · exact hni1vy (hpos.2 _ hi1 _ hvy e)
    · obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 hyv)
      rcases pa_three hpj1 hpj2 hev hpj12 (fun e => hvy (hfv _ hj1 e.symm ▸ hj1))
          (fun e => hvy (hfv _ hj2 e.symm ▸ hj2)) (hc3 y) (pos i1) hm with e | e | e
      · exact hni1j1 (hpos.2 _ hi1 _ hj1 e)
      · exact hni1j2 (hpos.2 _ hi1 _ hj2 e)
      · exact hvy (hfv _ hi1 e.symm ▸ hi1)
  have hPne : P ≠ pos i1 := fun e => hi1_not_Wy (e ▸ hPy)
  have hQne : Q ≠ pos i1 := fun e => hi1_not_Wy (e ▸ hQy)
  have hpi1 := as_mem hpos hi1 ((hc_adjB_iff _ _).1 hx1)
  obtain ⟨e, he, hny, hnq⟩ := g10_deg3_cover_free h hD hdx hxy hqx.symm (sem_adjB_false.1 hnyq)
  rcases pa_three hPx hQx hpi1 hPQ hPne hQne (hc3 x) e he with rfl | rfl | rfl
  · exact hny (sem_mem_W.1 hPy).2.1
  · exact hny (sem_mem_W.1 hQy).2.1
  · exact hnq ((hpos.1 i1 hi1).2.2.1 q ((hc_adjB_iff _ _).1 hq1))

theorem hnot33_pair {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hB0 : Bzero 10 D = 0) {pos : Fin 10 → ℕ × Bool} {P Q : ℕ × Bool}
    (hctx : pa_ctx D pos P Q) (x y ix iy : Fin 10)
    (hix : ix ∈ ineligSet 10 D) (hiy : iy ∈ ineligSet 10 D)
    (hx : x ∉ ineligSet 10 D) (hy : y ∉ ineligSet 10 D)
    (hg : ix ≠ iy ∧ hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB x y = true ∧
      hc_adjB ix y = false)
    (hsx : 3 ≤ (sem_W 10 D x).card) (hsy : 3 ≤ (sem_W 10 D y).card) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨hixy, g1, g2, g3, g4⟩ := hg
  obtain ⟨hPx, hQx⟩ := hsat x hsx
  obtain ⟨hPy, hQy⟩ := hsat y hsy
  obtain ⟨e, he, hbe, hf, hf'⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 g3)
  have heP : e ≠ P := fun hh => w_bar h.1 (hh ▸ hPy) hbe
  have heQ : e ≠ Q := fun hh => w_bar h.1 (hh ▸ hQy) hbe
  have hWx := pa_three hPx hQx he hPQ heP.symm heQ.symm (hc3 x)
  have hpx := as_mem hpos hix ((hc_adjB_iff _ _).1 g1)
  have hpx_ne_e : pos ix ≠ e := fun hh => hy (hf ix hix hh.symm ▸ hix)
  have hpx_in_y : pos ix ∈ sem_W 10 D y := by
    rcases hWx (pos ix) hpx with h1 | h1 | h1
    · exact h1 ▸ hPy
    · exact h1 ▸ hQy
    · exact absurd h1 hpx_ne_e
  have hpy := as_mem hpos hiy ((hc_adjB_iff _ _).1 g2)
  have hpy_ne_be : pos iy ≠ sem_bar e := fun hh => hx (hf' iy hiy hh.symm ▸ hiy)
  have hbeP : sem_bar e ≠ P := fun hh => w_bar h.1 (hh ▸ hPx) (by rw [sem_bar_bar]; exact he)
  have hbeQ : sem_bar e ≠ Q := fun hh => w_bar h.1 (hh ▸ hQx) (by rw [sem_bar_bar]; exact he)
  have hWy := pa_three hPy hQy hbe hPQ hbeP.symm hbeQ.symm (hc3 y)
  have hpy_in_x : pos iy ∈ sem_W 10 D x := by
    rcases hWy (pos iy) hpy with h1 | h1 | h1
    · exact h1 ▸ hPx
    · exact h1 ▸ hQx
    · exact absurd h1 hpy_ne_be
  have hpxpy : pos ix ≠ pos iy := fun hh => hixy (hpos.2 _ hix _ hiy hh)
  have hpy_ne_e : pos iy ≠ e := fun hh => hy (hf iy hiy hh.symm ▸ hiy)
  have hWx2 := pa_three hpx hpy_in_x he hpxpy hpx_ne_e hpy_ne_e (hc3 x)
  have hfull := full_g10 h hD hB0 hpos hix ((hc_adjB_iff _ _).1 g1) (fun p hp hne1 hsub => by
    rcases hWx2 p hp with rfl | rfl | rfl
    · exact hne1 rfl
    · exact hixy.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hiy)))
    · exact hy (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe).2.1) ▸ hix))
  exact sem_adjB_false.1 g4 ((hfull y).1 (sem_mem_W.1 hpx_in_y).2.1)

theorem hnot33_diff_I {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    {pos : Fin 10 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : pa_ctx D pos P Q)
    (x y ix iy vx qx qy : Fin 10)
    (hix : ix ∈ ineligSet 10 D) (hiy : iy ∈ ineligSet 10 D) (hvx : vx ∉ ineligSet 10 D)
    (hg : x ≠ y ∧ ix ≠ iy ∧ (g10_nbB x).card = 3 ∧ (g10_nbB y).card = 3 ∧
          hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB ix y = false ∧
          hc_adjB x vx = true ∧ hc_adjB ix qx = true ∧ qx ≠ x ∧ hc_adjB y qx = false ∧
          hc_adjB iy qy = true ∧ qy ≠ y ∧ hc_adjB x qy = false)
    (hx3 : 3 ≤ (sem_W 10 D x).card) (hy3 : 3 ≤ (sem_W 10 D y).card) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨hxy, hixy, hdx, hdy, g1, g2, g3, g4, g5, hqxx, g6, g7, hqyy, g8⟩ := hg
  obtain ⟨hPx, hQx⟩ := hsat x hx3
  obtain ⟨hPy, hQy⟩ := hsat y hy3
  have hpx := as_mem hpos hix ((hc_adjB_iff _ _).1 g1)
  have hpy := as_mem hpos hiy ((hc_adjB_iff _ _).1 g2)
  by_cases hpxy : pos ix ∈ sem_W 10 D y
  · by_cases hpyx : pos iy ∈ sem_W 10 D x
    · obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 g4)
      have hpxpy : pos ix ≠ pos iy := fun e => hixy (hpos.2 _ hix _ hiy e)
      have hpxe : pos ix ≠ ev := fun e => hvx (hfv _ hix e.symm ▸ hix)
      have hpye : pos iy ≠ ev := fun e => hvx (hfv _ hiy e.symm ▸ hiy)
      have hWx := pa_three hpx hpyx hev hpxpy hpxe hpye (hc3 x)
      have hfull := full_g10 h hD hB0 hpos hix ((hc_adjB_iff _ _).1 g1) (fun p hp hne1 hsub => by
        rcases hWx p hp with rfl | rfl | rfl
        · exact hne1 rfl
        · exact hixy.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hiy)))
        · exact hvx (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbev).2.1) ▸ hix))
      exact sem_adjB_false.1 g3 ((hfull y).1 (sem_mem_W.1 hpxy).2.1)
    · have hPne : P ≠ pos iy := fun e => hpyx (e ▸ hPx)
      have hQne : Q ≠ pos iy := fun e => hpyx (e ▸ hQx)
      obtain ⟨e, he, hnx, hnq⟩ := g10_deg3_cover_free h hD hdy hxy.symm hqyy.symm (sem_adjB_false.1 g8)
      rcases pa_three hPy hQy hpy hPQ hPne hQne (hc3 y) e he with rfl | rfl | rfl
      · exact hnx (sem_mem_W.1 hPx).2.1
      · exact hnx (sem_mem_W.1 hQx).2.1
      · exact hnq ((hpos.1 iy hiy).2.2.1 qy ((hc_adjB_iff _ _).1 g7))
  · have hPne : P ≠ pos ix := fun e => hpxy (e ▸ hPy)
    have hQne : Q ≠ pos ix := fun e => hpxy (e ▸ hQy)
    obtain ⟨e, he, hny, hnq⟩ := g10_deg3_cover_free h hD hdx hxy hqxx.symm (sem_adjB_false.1 g6)
    rcases pa_three hPx hQx hpx hPQ hPne hQne (hc3 x) e he with rfl | rfl | rfl
    · exact hny (sem_mem_W.1 hPy).2.1
    · exact hny (sem_mem_W.1 hQy).2.1
    · exact hnq ((hpos.1 ix hix).2.2.1 qx ((hc_adjB_iff _ _).1 g5))

theorem hnot33_via_deg2 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    {pos : Fin 10 → ℕ × Bool} {P Q : ℕ × Bool} (hctx : pa_ctx D pos P Q)
    (x y ix iy i2 v0 qx : Fin 10)
    (hix : ix ∈ ineligSet 10 D) (hiy : iy ∈ ineligSet 10 D) (hi2 : i2 ∈ ineligSet 10 D)
    (hg : x ≠ y ∧ ix ≠ iy ∧ iy ≠ i2 ∧ ix ≠ i2 ∧ (g10_nbB x).card = 3 ∧ (g10_nbB y).card = 3 ∧
          hc_adjB ix x = true ∧ hc_adjB iy y = true ∧ hc_adjB iy x = false ∧
          hc_adjB iy v0 = true ∧ hc_adjB i2 v0 = true ∧ v0 ≠ x ∧ v0 ≠ y ∧
          hc_adjB x v0 = false ∧ hc_adjB ix qx = true ∧ qx ≠ x ∧ hc_adjB v0 qx = false)
    (hx3 : 3 ≤ (sem_W 10 D x).card) (hy3 : 3 ≤ (sem_W 10 D y).card) : False := by
  obtain ⟨hpos, hc3, hPQ, hsat⟩ := hctx
  obtain ⟨hxy, hixy, hiy2, hix2, hdx, hdy, g1, g2, g3, g4, g5, hv0x, hv0y, g6, g7, hqxx, g8⟩ := hg
  obtain ⟨hPx, hQx⟩ := hsat x hx3
  obtain ⟨hPy, hQy⟩ := hsat y hy3
  have hpx := as_mem hpos hix ((hc_adjB_iff _ _).1 g1)
  have hpy := as_mem hpos hiy ((hc_adjB_iff _ _).1 g2)
  have hpiy_v0 := as_mem hpos hiy ((hc_adjB_iff _ _).1 g4)
  have hpi2_v0 := as_mem hpos hi2 ((hc_adjB_iff _ _).1 g5)
  by_cases hpiy_PQ : P = pos iy ∨ Q = pos iy
  · have hpyx : pos iy ∈ sem_W 10 D x := by
      rcases hpiy_PQ with h1 | h1 <;> [exact h1 ▸ hPx; exact h1 ▸ hQx]
    by_cases hv0_3 : 3 ≤ (sem_W 10 D v0).card
    · obtain ⟨hPv0, hQv0⟩ := hsat v0 hv0_3
      by_cases hpix_PQ : P = pos ix ∨ Q = pos ix
      · have hpix_v0 : pos ix ∈ sem_W 10 D v0 := by
          rcases hpix_PQ with h1 | h1 <;> [exact h1 ▸ hPv0; exact h1 ▸ hQv0]
        have hW0 := pa_three hpix_v0 hpiy_v0 hpi2_v0
          (fun e => hixy (hpos.2 _ hix _ hiy e))
          (fun e => hix2 (hpos.2 _ hix _ hi2 e))
          (fun e => hiy2 (hpos.2 _ hiy _ hi2 e)) (hc3 v0)
        have hfull := full_g10 h hD hB0 hpos hiy ((hc_adjB_iff _ _).1 g4) (fun p hp hne1 hsub => by
          rcases hW0 p hp with rfl | rfl | rfl
          · exact hixy (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hix)))
          · exact hne1 rfl
          · exact hiy2.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hi2))))
        exact sem_adjB_false.1 g3 ((hfull x).1 (sem_mem_W.1 hpyx).2.1)
      · rw [not_or] at hpix_PQ
        obtain ⟨e, he, hnv0, hnq⟩ := g10_deg3_cover_free h hD hdx hv0x.symm hqxx.symm (sem_adjB_false.1 g8)
        rcases pa_three hPx hQx hpx hPQ hpix_PQ.1 hpix_PQ.2 (hc3 x) e he with rfl | rfl | rfl
        · exact hnv0 (sem_mem_W.1 hPv0).2.1
        · exact hnv0 (sem_mem_W.1 hQv0).2.1
        · exact hnq ((hpos.1 ix hix).2.2.1 qx ((hc_adjB_iff _ _).1 g7))
    · have hv0_2 : (sem_W 10 D v0).card ≤ 2 := by omega
      have hW0 := pa_two hpiy_v0 hpi2_v0 (fun e => hiy2 (hpos.2 _ hiy _ hi2 e)) hv0_2
      have hfull := full_g10 h hD hB0 hpos hiy ((hc_adjB_iff _ _).1 g4) (fun p hp hne1 hsub => by
        rcases hW0 p hp with rfl | rfl
        · exact hne1 rfl
        · exact hiy2.symm (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos hi2))))
      exact sem_adjB_false.1 g3 ((hfull x).1 (sem_mem_W.1 hpyx).2.1)
  · rw [not_or] at hpiy_PQ
    obtain ⟨e, he, hnx, hnv0⟩ := g10_deg3_cover_free h hD hdy hxy.symm hv0y.symm (sem_adjB_false.1 g6)
    rcases pa_three hPy hQy hpy hPQ hpiy_PQ.1 hpiy_PQ.2 (hc3 y) e he with rfl | rfl | rfl
    · exact hnx (sem_mem_W.1 hPx).2.1
    · exact hnx (sem_mem_W.1 hQx).2.1
    · exact hnv0 ((hpos.1 iy hiy).2.2.1 v0 ((hc_adjB_iff _ _).1 g4))

theorem sem_minBranch_not_and {D : Dag} (h : StrictLive 10 D) (br : Fin 10 → ℕ)
    (hbm : sem_MinBranch 10 D br) {y : Fin 10} (hyE : y ∈ eligSet 10 D)
    {j : ℕ} (hj : j < D.length) (ht : tag D j = true) : br y ≠ 10 + j := by
  intro heq
  have hS := h.1
  have hyin : y ∈ supp 10 D (10 + j) := by rw [← heq, (hbm y hyE).2.1]; exact Finset.mem_singleton_self y
  rw [sem_supp_and hS hj ht, Finset.mem_inter] at hyin
  obtain ⟨ha_lt, hb_lt, hab_ne⟩ := hS j hj
  have hmin : ∀ u, y ∈ supp 10 D u → 2 ≤ fanout D u → 10 + j ≤ u := fun u hu hfu => by
    rw [← heq]; exact (hbm y hyE).2.2.2 u hfu hu
  have hcomp : ∀ {x}, Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) x (opA D j) →
      Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) x (opB D j) →
      Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) (opA D j) (opB D j) ∨
      Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ y ∈ supp 10 D a ∧ y ∈ supp 10 D c) (opB D j) (opA D j) := by
    intro x h1
    induction h1 using Relation.ReflTransGen.head_induction_on with
    | refl => intro h2; exact Or.inl h2
    | @head a c hac hca ih =>
      intro h2
      rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨d, had, hdb⟩
      · exact Or.inr (Relation.ReflTransGen.head hac hca)
      · have halt : a < 10 + j := (sem_step_lt hS hac.1).trans_le ((sem_rtg_le hS (fun _ _ s => s.1) hca).trans_lt ha_lt).le
        have hf2 : fanout D a ≤ 1 := by by_contra hf; have := hmin a hac.2.1 (by omega); omega
        have hf1 := sem_step_fanout hac.1
        exact ih (sem_step_unique hac.1 had.1 (by omega) ▸ hdb)
  rcases hcomp (sem_supp_path hS hyin.1) (sem_supp_path hS hyin.2) with h1 | h2
  · rcases Relation.ReflTransGen.cases_head h1 with heq' | ⟨c, hc, hcb⟩
    · exact hab_ne heq'
    · have hf2 : fanout D (opA D j) ≤ 1 := by by_contra hf; have := hmin _ hyin.1 (by omega); omega
      have hst : sem_step 10 D (opA D j) (10 + j) := ⟨by omega, by omega, Or.inl (by simp)⟩
      have hceq := sem_step_unique hc.1 hst (by have := sem_step_fanout hst; omega)
      rw [hceq] at hcb
      have := sem_rtg_le hS (fun _ _ s => s.1) hcb; omega
  · rcases Relation.ReflTransGen.cases_head h2 with heq' | ⟨c, hc, hca⟩
    · exact hab_ne heq'.symm
    · have hf2 : fanout D (opB D j) ≤ 1 := by by_contra hf; have := hmin _ hyin.2 (by omega); omega
      have hst : sem_step 10 D (opB D j) (10 + j) := ⟨by omega, by omega, Or.inr (by simp)⟩
      have hceq := sem_step_unique hc.1 hst (by have := sem_step_fanout hst; omega)
      rw [hceq] at hca
      have := sem_rtg_le hS (fun _ _ s => s.1) hca; omega

theorem sem_minBranch_not_after {D : Dag} (h : StrictLive 10 D) (br : Fin 10 → ℕ)
    (hbm : sem_MinBranch 10 D br) {v : Fin 10} (hvE : v ∈ eligSet 10 D)
    {e : ℕ × Bool} (heW : e ∈ sem_W 10 D v) : ¬ (10 + e.1 < br v) := by
  intro hgt
  have hS := h.1
  have hvsrc := (sem_mem_W.1 heW).2.1
  have hsrc_lt : src D e < br v := (src_lt hS (sem_mem_W.1 heW).1).trans hgt
  have hmin : ∀ u, v ∈ supp 10 D u → 2 ≤ fanout D u → br v ≤ u := fun u hu hfu =>
    (hbm v hvE).2.2.2 u hfu hu
  have htot : ∀ {a}, Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ v ∈ supp 10 D a ∧ v ∈ supp 10 D c) a (br v) →
      Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ v ∈ supp 10 D a ∧ v ∈ supp 10 D c) a (src D e) →
      Relation.ReflTransGen (fun a c => sem_step 10 D a c ∧ v ∈ supp 10 D a ∧ v ∈ supp 10 D c) (src D e) (br v) := by
    intro a h1
    induction h1 using Relation.ReflTransGen.head_induction_on with
    | refl => intro h2; have := sem_rtg_le hS (fun _ _ s => s.1) h2; omega
    | @head a c hac hcw ih =>
      intro h2
      rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨d, had, hds⟩
      · exact Relation.ReflTransGen.head hac hcw
      · have halt : a < br v := (sem_step_lt hS hac.1).trans_le (sem_rtg_le hS (fun _ _ s => s.1) hcw)
        have hf2 : fanout D a ≤ 1 := by by_contra hf; have := hmin a hac.2.1 (by omega); omega
        have hf1 := sem_step_fanout hac.1
        exact ih (sem_step_unique hac.1 had.1 (by omega) ▸ hds)
  have hsw := htot (sem_supp_path hS (by rw [(hbm v hvE).2.1]; exact Finset.mem_singleton_self v)) (sem_supp_path hS hvsrc)
  rcases Relation.ReflTransGen.cases_head hsw with heq | ⟨c, hc, -⟩
  · omega
  · have hf2 : fanout D (src D e) ≤ 1 := by by_contra hf; have := hmin _ hvsrc (by omega); omega
    have hstepe : sem_step 10 D (src D e) (10 + e.1) := sem_step_src (sem_mem_W.1 heW).1 e.2
    have hf1 := sem_step_fanout hstepe
    have hceq := sem_step_unique hc.1 hstepe (by omega)
    exact (sem_mem_W.1 heW).2.2 (hceq ▸ hc.2.2)

theorem kill_4cycle_gate {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (br : Fin 10 → ℕ) (hbm : sem_MinBranch 10 D br) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {Z Z' : ℕ × Bool} {a1 b1 a2 b2 c d i0 : Fin 10}
    (hZ_lt : Z.1 < D.length) (hZ_and : tag D Z.1 = true)
    (_hZ'_lt : Z'.1 < D.length) (_hZ'_and : tag D Z'.1 = true)
    (hZa1 : a1 ∈ supp 10 D (src D Z)) (hZb1 : b1 ∈ supp 10 D (src D (sem_bar Z))) (hnab1 : ¬ Adj a1 b1)
    (hZa2 : a2 ∈ supp 10 D (src D Z)) (hZb2 : b2 ∈ supp 10 D (src D (sem_bar Z)))
    (ha2n : a2 ∉ supp 10 D (10 + Z.1)) (hb2n : b2 ∉ supp 10 D (10 + Z.1))
    (hZ_uniq2 : ∀ j s, (j, s) ∈ sem_W 10 D a2 → (j, !s) ∈ sem_W 10 D b2 → j = Z.1)
    (hi0 : i0 ∈ ineligSet 10 D) (ha1i0 : a1 ≠ i0)
    (hp0_val : ∀ x, val D x (10 + (pos i0).1) = true → G10Edge x)
    (hp0_a1 : a1 ∈ supp 10 D (src D (pos i0)))
    (hp0_2 : val D (sem_two a2 b2) (src D (sem_bar (pos i0))) = true)
    (hno_a2b2_gk : ∀ e : ℕ × Bool, (e ∈ sem_W 10 D a2 ∨ e ∈ sem_W 10 D b2) →
      val D (sem_two a2 b2) (10 + e.1) = true → val D (sem_two a1 b1) (10 + e.1) = false → e.1 = Z'.1)
    (hsplit_mid : ∀ w, 10 + Z.1 < w → val D (sem_two a2 b2) w = true →
      a2 ∉ supp 10 D w → b2 ∉ supp 10 D w → 2 ≤ fanout D w →
      ∃ y ∈ eligSet 10 D, br y = w ∧
        ∀ e ∈ sem_W 10 D y, val D (sem_two a2 b2) (10 + e.1) = true →
          a2 ∉ supp 10 D (10 + e.1) → b2 ∉ supp 10 D (10 + e.1) → e.1 = Z'.1)
    (hsplit_after : ∀ w, 10 + Z.1 < w → 10 + Z'.1 < w → val D (sem_two a2 b2) w = true →
      a2 ∉ supp 10 D w → b2 ∉ supp 10 D w → 2 ≤ fanout D w →
      ∃ y ∈ eligSet 10 D, br y = w ∧
        ∀ e ∈ sem_W 10 D y, val D (sem_two a2 b2) (10 + e.1) = true →
          a2 ∉ supp 10 D (10 + e.1) → b2 ∉ supp 10 D (10 + e.1) → False)
    (hcd : Adj c d)
    (hZ'_uniq_cd : ∀ j s, (j, s) ∈ sem_W 10 D c → (j, !s) ∈ sem_W 10 D d → j = Z'.1)
    (hcn_p0 : c ∉ supp 10 D (src D (pos i0))) (hdn_p0 : d ∉ supp 10 D (src D (pos i0)))
    (hZ_fan1 : fanout D (10 + Z.1) ≤ 1) (hZ'_fan1 : fanout D (10 + Z'.1) ≤ 1) : False := by
  have hS := h.1
  have hC := sem_g10_comp hD
  let inU : ℕ → Prop := fun w => w < 10 + D.length ∧ val D (sem_two a2 b2) w = true ∧
    a2 ∉ supp 10 D w ∧ b2 ∉ supp 10 D w
  let stepU : ℕ → ℕ → Prop := fun u v => sem_step 10 D u v ∧ inU u ∧ inU v
  have hval_Z_1 : val D (sem_two a1 b1) (10 + Z.1) = true := by
    have h1 := val_mono hS (fun i => decide (i = a1)) (sem_two a1 b1)
      (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D Z) (mem_supp.1 hZa1)
    have h2 := val_mono hS (fun i => decide (i = b1)) (sem_two a1 b1)
      (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D (sem_bar Z)) (mem_supp.1 hZb1)
    rw [val_gate hS _ Z.1 hZ_lt, hZ_and, gop_true]
    rcases hZeq : Z with ⟨j, s⟩; rw [hZeq] at h1 h2
    cases s
    · rw [sb_src_false] at h1; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at h2; simp [h1, h2]
    · rw [sb_src_true] at h1; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at h2; simp [h1, h2]
  have hval_Z_2 : val D (sem_two a2 b2) (10 + Z.1) = true := by
    have h1 := val_mono hS (fun i => decide (i = a2)) (sem_two a2 b2)
      (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D Z) (mem_supp.1 hZa2)
    have h2 := val_mono hS (fun i => decide (i = b2)) (sem_two a2 b2)
      (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D (sem_bar Z)) (mem_supp.1 hZb2)
    rw [val_gate hS _ Z.1 hZ_lt, hZ_and, gop_true]
    rcases hZeq : Z with ⟨j, s⟩; rw [hZeq] at h1 h2
    cases s
    · rw [sb_src_false] at h1; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at h2; simp [h1, h2]
    · rw [sb_src_true] at h1; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at h2; simp [h1, h2]
  have hU_entry : ∀ w, inU w → w = 10 + Z.1 ∨ ∃ u, stepU u w := by
    intro w hw
    obtain ⟨hwlt, hwv, han, hbn⟩ := hw
    have hwge : 10 ≤ w := by
      by_contra hc; rw [val_input D _ w (by omega)] at hwv
      simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hwv
      rcases hwv with h' | h'
      · exact han (by rw [mem_supp, val_input D _ w (by omega)]; exact decide_eq_true h')
      · exact hbn (by rw [mem_supp, val_input D _ w (by omega)]; exact decide_eq_true h')
    obtain ⟨j, rfl⟩ : ∃ j, w = 10 + j := ⟨w - 10, by omega⟩
    have hj : j < D.length := by omega
    obtain ⟨ha_lt, hb_lt, -⟩ := hS j hj
    rw [val_gate hS _ j hj] at hwv
    by_cases ht : tag D j = true
    · rw [ht, gop_true, Bool.and_eq_true] at hwv
      by_cases haU : a2 ∉ supp 10 D (opA D j) ∧ b2 ∉ supp 10 D (opA D j)
      · right; exact ⟨opA D j, ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ⟨by omega, hwv.1, haU.1, haU.2⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_true, hwv.1, hwv.2]; rfl, han, hbn⟩⟩⟩
      · by_cases hbU : a2 ∉ supp 10 D (opB D j) ∧ b2 ∉ supp 10 D (opB D j)
        · right; exact ⟨opB D j, ⟨⟨by omega, by omega, Or.inr (by simp)⟩, ⟨by omega, hwv.2, hbU.1, hbU.2⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_true, hwv.1, hwv.2]; rfl, han, hbn⟩⟩⟩
        · left
          rw [not_and_or, Classical.not_not, Classical.not_not] at haU hbU
          have haab : ¬(a2 ∈ supp 10 D (opA D j) ∧ a2 ∈ supp 10 D (opB D j)) :=
            fun h' => han (by rw [sem_supp_and hS hj ht, Finset.mem_inter]; exact h')
          have hbab : ¬(b2 ∈ supp 10 D (opA D j) ∧ b2 ∈ supp 10 D (opB D j)) :=
            fun h' => hbn (by rw [sem_supp_and hS hj ht, Finset.mem_inter]; exact h')
          rcases haU with ha | hb <;> rcases hbU with ha' | hb'
          · exact absurd ⟨ha, ha'⟩ haab
          · have := hZ_uniq2 j false (sem_mem_W.2 ⟨hj, by rw [sb_src_false]; exact ha, han⟩)
              (sem_mem_W.2 ⟨hj, by rw [show src D (j, !false) = opB D j from rfl]; exact hb', hbn⟩); omega
          · have := hZ_uniq2 j true (sem_mem_W.2 ⟨hj, by rw [sb_src_true]; exact ha', han⟩)
              (sem_mem_W.2 ⟨hj, by rw [show src D (j, !true) = opA D j from rfl]; exact hb, hbn⟩); omega
          · exact absurd ⟨hb, hb'⟩ hbab
    · rw [Bool.not_eq_true] at ht; rw [ht, gop_false, Bool.or_eq_true] at hwv
      have haa : a2 ∉ supp 10 D (opA D j) := fun hm => han (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl hm)
      have hab : a2 ∉ supp 10 D (opB D j) := fun hm => han (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr hm)
      have hba : b2 ∉ supp 10 D (opA D j) := fun hm => hbn (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl hm)
      have hbb : b2 ∉ supp 10 D (opB D j) := fun hm => hbn (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr hm)
      right
      rcases hwv with ha1 | hb1
      · exact ⟨opA D j, ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ⟨by omega, ha1, haa, hba⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_false, ha1]; rfl, han, hbn⟩⟩⟩
      · exact ⟨opB D j, ⟨⟨by omega, by omega, Or.inr (by simp)⟩, ⟨by omega, hb1, hab, hbb⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_false, hb1]; simp, han, hbn⟩⟩⟩
  have hU_reach : ∀ w, inU w → Relation.ReflTransGen stepU (10 + Z.1) w := by
    intro w; induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      rcases hU_entry w hw with rfl | ⟨u, hu⟩
      · exact Relation.ReflTransGen.refl
      · exact (ih u (sem_step_lt hS hu.1) hu.2.1).tail hu

  have hbar0_supp : supp 10 D (src D (sem_bar (pos i0))) = {i0} := by
    rw [show src D (sem_bar (pos i0)) = src D ((pos i0).1, !(pos i0).2) from rfl]; exact (hpos.1 i0 hi0).2.2.2
  have hp0_lt : (pos i0).1 < D.length := (hpos.1 i0 hi0).1
  have hbar0_lt : src D (sem_bar (pos i0)) < 10 + (pos i0).1 := src_lt hS (e := sem_bar (pos i0)) hp0_lt
  have ha2_ne_i0 : a2 ≠ i0 := fun heq => by
    have hZa2W : Z ∈ sem_W 10 D i0 := sem_mem_W.2 ⟨hZ_lt, heq ▸ hZa2, heq ▸ ha2n⟩
    rw [as_W h hD hpos hi0, Finset.mem_singleton] at hZa2W
    have := hZa1; rw [hZa2W, hbar0_supp, Finset.mem_singleton] at this
    exact ha1i0 this
  have hb2_ne_i0 : b2 ≠ i0 := fun heq => by
    have hZb2W : sem_bar Z ∈ sem_W 10 D i0 := sem_mem_W.2 ⟨hZ_lt, heq ▸ hZb2, heq ▸ hb2n⟩
    rw [as_W h hD hpos hi0, Finset.mem_singleton] at hZb2W
    have hZeq : Z = pos i0 := by simpa [sem_bar_bar] using congrArg sem_bar hZb2W
    have h1 := hp0_val (sem_two a1 b1) (by rw [← hZeq]; exact hval_Z_1)
    rw [g10Edge_iff_adj] at h1
    obtain ⟨p, q, hpq, hp, hq⟩ := h1
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact adj_irrefl _ hpq
    · exact hnab1 hpq
    · exact hnab1 (adj_symm hpq)
    · exact adj_irrefl _ hpq
  have hbar0_inU : inU (src D (sem_bar (pos i0))) :=
    ⟨by omega, hp0_2, by rw [hbar0_supp, Finset.mem_singleton]; exact ha2_ne_i0,
      by rw [hbar0_supp, Finset.mem_singleton]; exact hb2_ne_i0⟩
  have hbar0_val1_f : val D (sem_two a1 b1) (src D (sem_bar (pos i0))) = false := by
    by_contra hc; rw [Bool.not_eq_false] at hc
    have ha1v := val_mono hS (fun i => decide (i = a1)) (sem_two a1 b1)
      (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two])
      (src D (pos i0)) (mem_supp.1 hp0_a1)
    have ht0 : tag D (pos i0).1 = true := sem_W_and hS (e := sem_bar (pos i0)) (as_W h hD hpos hi0 ▸ Finset.mem_singleton_self _)
    have hval0 : val D (sem_two a1 b1) (10 + (pos i0).1) = true := by
      rw [val_gate hS _ (pos i0).1 hp0_lt, ht0, gop_true]
      rcases hpeq : pos i0 with ⟨j, s⟩; rw [hpeq] at ha1v hc
      cases s
      · rw [sb_src_false] at ha1v; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at hc; simp [ha1v, hc]
      · rw [sb_src_true] at ha1v; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at hc; simp [ha1v, hc]
    have h1 := hp0_val (sem_two a1 b1) hval0
    rw [g10Edge_iff_adj] at h1
    obtain ⟨p, q, hpq, hp, hq⟩ := h1
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact adj_irrefl _ hpq
    · exact hnab1 hpq
    · exact hnab1 (adj_symm hpq)
    · exact adj_irrefl _ hpq

  have hexit_U : ∀ (y : Fin 10), y ∈ eligSet 10 D → ∀ w, br y = w → ∀ t, Relation.ReflTransGen stepU w t →
      y ∉ supp 10 D t → ∃ e ∈ sem_W 10 D y, inU (10 + e.1) ∧ Relation.ReflTransGen stepU (10 + e.1) t := by
    intro y hyE w hby t hp hyt
    have hyw : y ∈ supp 10 D w := by rw [← hby, (hbm y hyE).2.1]; exact Finset.mem_singleton_self y
    induction hp with
    | refl => exact absurd hyw hyt
    | @tail u v _ hstep ih =>
      by_cases hyu : y ∈ supp 10 D u
      · obtain ⟨hjlt, hjge, hop⟩ := hstep.1
        have hveq : 10 + (v - 10) = v := by omega
        have heW : ∃ s : Bool, (v - 10, s) ∈ sem_W 10 D y := by
          rcases hop with ha | hb'
          · exact ⟨false, sem_mem_W.2 ⟨by omega, by simpa [src, ha] using hyu, by rwa [hveq]⟩⟩
          · exact ⟨true, sem_mem_W.2 ⟨by omega, by simpa [src, hb'] using hyu, by rwa [hveq]⟩⟩
        obtain ⟨s, hs⟩ := heW
        exact ⟨(v - 10, s), hs, by simpa [hveq] using hstep.2.2, by rw [hveq]⟩
      · obtain ⟨e, heW, heU, hrt⟩ := ih hyu
        exact ⟨e, heW, heU, hrt.tail hstep⟩
  have hfan1_det : ∀ {a c1 c2}, fanout D a = 1 → sem_step 10 D a c1 → sem_step 10 D a c2 → c1 = c2 :=
    fun hf h1 h2 => sem_step_unique h1 h2 hf

  have hZ'_reach_bar0 : Relation.ReflTransGen stepU (10 + Z'.1) (src D (sem_bar (pos i0))) := by
    have hp_all := hU_reach _ hbar0_inU
    by_cases hsp : ∃ w, Relation.ReflTransGen stepU (10 + Z.1) w ∧
        Relation.ReflTransGen stepU w (src D (sem_bar (pos i0))) ∧ 10 + Z.1 < w ∧ 2 ≤ fanout D w
    · obtain ⟨w, h1, h2, hlt, hfw⟩ := hsp
      have hw_inU : inU w := by
        rcases Relation.ReflTransGen.cases_tail h1 with heq | ⟨_, _, hs⟩
        · omega
        · exact hs.2.2
      obtain ⟨y, hyE, hby, hex⟩ := hsplit_mid w hlt hw_inU.2.1 hw_inU.2.2.1 hw_inU.2.2.2 hfw
      have hy_not_bar0 : y ∉ supp 10 D (src D (sem_bar (pos i0))) := by
        rw [hbar0_supp, Finset.mem_singleton]
        intro heq; subst heq; exact (Finset.mem_sdiff.1 hi0).2 hyE
      obtain ⟨e, heW, heU, hrt⟩ := hexit_U y hyE w hby _ h2 hy_not_bar0
      have heeq : e.1 = Z'.1 := hex e heW heU.2.1 heU.2.2.1 heU.2.2.2
      rwa [heeq] at hrt
    · push Not at hsp

      have hfirst_drop : ∀ {t}, Relation.ReflTransGen stepU (10 + Z.1) t →
          val D (sem_two a1 b1) t = false →
          ∃ u v, Relation.ReflTransGen stepU (10 + Z.1) u ∧ stepU u v ∧ Relation.ReflTransGen stepU v t ∧
            val D (sem_two a1 b1) u = true ∧ val D (sem_two a1 b1) v = false := by
        intro t hp
        induction hp with
        | refl => intro hv; rw [hval_Z_1] at hv; exact Bool.noConfusion hv
        | @tail u v hp1 hstep ih =>
          intro hv
          by_cases hu : val D (sem_two a1 b1) u = false
          · obtain ⟨u0, v0, h1, h2, h3, h4, h5⟩ := ih hu
            exact ⟨u0, v0, h1, h2, h3.tail hstep, h4, h5⟩
          · exact ⟨u, v, hp1, hstep, Relation.ReflTransGen.refl, Bool.eq_true_of_not_eq_false hu, hv⟩
      obtain ⟨u, v, hZu, huv, hv_bar0, hu1, hv1⟩ := hfirst_drop hp_all hbar0_val1_f
      obtain ⟨hvlt, hvge, hop⟩ := huv.1
      obtain ⟨j, rfl⟩ : ∃ j, v = 10 + j := ⟨v - 10, by omega⟩
      have hj : j < D.length := by omega
      have htag : tag D j = true := by
        by_contra ht; rw [Bool.not_eq_true] at ht
        rw [val_gate hS _ j hj, ht, gop_false, Bool.or_eq_false_iff] at hv1
        have hop' : opA D j = u ∨ opB D j = u := by simpa using hop
        rcases hop' with h' | h'
        · rw [h', hu1] at hv1; exact Bool.noConfusion hv1.1
        · rw [h', hu1] at hv1; exact Bool.noConfusion hv1.2
      have hv_val2 := huv.2.2.2.1
      rw [val_gate hS _ j hj, htag, gop_true, Bool.and_eq_true] at hv_val2
      rw [val_gate hS _ j hj, htag, gop_true, Bool.and_eq_false_iff] at hv1
      have hop' : opA D j = u ∨ opB D j = u := by simpa using hop
      obtain ⟨s, hs_other, hv'_val2, hv'_val1⟩ : ∃ s : Bool, src D (j, s) ≠ u ∧
          val D (sem_two a2 b2) (src D (j, s)) = true ∧ val D (sem_two a1 b1) (src D (j, s)) = false := by
        rcases hop' with ha | hb'
        · refine ⟨true, fun heq => ?_, by rw [sb_src_true]; exact hv_val2.2, ?_⟩
          · rw [sb_src_true] at heq
            rcases hv1 with h' | h'
            · rw [ha, hu1] at h'; exact Bool.noConfusion h'
            · rw [heq, hu1] at h'; exact Bool.noConfusion h'
          · rw [sb_src_true]
            rcases hv1 with h' | h'
            · rw [ha, hu1] at h'; exact Bool.noConfusion h'
            · exact h'
        · refine ⟨false, fun heq => ?_, by rw [sb_src_false]; exact hv_val2.1, ?_⟩
          · rw [sb_src_false] at heq
            rcases hv1 with h' | h'
            · rw [heq, hu1] at h'; exact Bool.noConfusion h'
            · rw [hb', hu1] at h'; exact Bool.noConfusion h'
          · rw [sb_src_false]
            rcases hv1 with h' | h'
            · exact h'
            · rw [hb', hu1] at h'; exact Bool.noConfusion h'
      by_cases hmem : a2 ∈ supp 10 D (src D (j, s)) ∨ b2 ∈ supp 10 D (src D (j, s))
      · have heW : (j, s) ∈ sem_W 10 D a2 ∨ (j, s) ∈ sem_W 10 D b2 := by
          rcases hmem with ha | hb'
          · exact Or.inl (sem_mem_W.2 ⟨hj, ha, huv.2.2.2.2.1⟩)
          · exact Or.inr (sem_mem_W.2 ⟨hj, hb', huv.2.2.2.2.2⟩)
        have hjeq := hno_a2b2_gk (j, s) heW huv.2.2.2.1 (by rw [val_gate hS _ j hj, htag, gop_true]; rcases hv1 with h' | h' <;> simp [h'])
        rwa [← hjeq]
      · exfalso
        rw [not_or] at hmem
        have hv'_lt : src D (j, s) < 10 + j := src_lt hS (e := (j, s)) hj
        have hv'_inU : inU (src D (j, s)) := ⟨by omega, hv'_val2, hmem.1, hmem.2⟩
        have hZv' := hU_reach _ hv'_inU

        have hchain_Zu : sem_Chain 10 D (10 + Z.1) u := by
          have hsub : ∀ {x}, Relation.ReflTransGen stepU (10 + Z.1) x →
              Relation.ReflTransGen stepU x (src D (sem_bar (pos i0))) → sem_Chain 10 D (10 + Z.1) x := by
            intro x h1
            induction h1 with
            | refl => intro _; exact Relation.ReflTransGen.refl
            | @tail a c hZa hac ih =>
              intro hcb
              have hf1 : 1 ≤ fanout D a := sem_step_fanout hac.1
              have hf2 : fanout D a ≤ 1 := by
                have hle := sem_rtg_le hS (fun _ _ s => s.1) hZa
                by_cases heq : a = 10 + Z.1
                · rw [heq]; exact hZ_fan1
                · have := hsp a hZa (Relation.ReflTransGen.head hac hcb) (by omega); omega
              exact (ih (Relation.ReflTransGen.head hac hcb)).tail ⟨hac.1, by omega⟩
          exact hsub hZu (Relation.ReflTransGen.head huv hv_bar0)

        have hcomp : ∀ {a}, sem_Chain 10 D a u → Relation.ReflTransGen stepU a (src D (j, s)) →
            Relation.ReflTransGen (sem_step 10 D) u (src D (j, s)) ∨ sem_Chain 10 D (src D (j, s)) u := by
          intro a h1
          induction h1 using Relation.ReflTransGen.head_induction_on with
          | refl => intro h2; exact Or.inl (sem_rtg_mono (fun _ _ s => s.1) h2)
          | head hac hcu ih =>
            intro h2
            rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨d, had, hdv⟩
            · exact Or.inr (Relation.ReflTransGen.head hac hcu)
            · exact ih (hfan1_det hac.2 hac.1 had.1 ▸ hdv)
        rcases hcomp hchain_Zu hZv' with huv' | hv'u
        · rcases Relation.ReflTransGen.cases_head huv' with heq | ⟨c, huc, hcv'⟩
          · exact hs_other heq.symm
          · have hf1 := sem_step_fanout huv.1
            have hf2 : fanout D u ≤ 1 := by
              have hle := sem_rtg_le hS (fun _ _ s => s.1) hZu
              by_cases heq : u = 10 + Z.1
              · rw [heq]; exact hZ_fan1
              · have := hsp u hZu (Relation.ReflTransGen.head huv hv_bar0) (by omega); omega
            have hceq := hfan1_det (by omega) huc huv.1
            rw [hceq] at hcv'
            have := sem_rtg_le hS (fun _ _ s => s) hcv'; omega
        · rcases Relation.ReflTransGen.cases_head hv'u with heq | ⟨c, hv'c, hcu⟩
          · exact hs_other heq
          · have hstep' : sem_step 10 D (src D (j, s)) (10 + j) := sem_step_src hj s
            have hceq := hfan1_det hv'c.2 hv'c.1 hstep'
            rw [hceq] at hcu
            have hle := sem_rtg_le hS (fun _ _ s => s.1) hcu
            have hlt := sem_step_lt hS huv.1
            omega

  have hchain_Z'_bar0 : sem_Chain 10 D (10 + Z'.1) (src D (sem_bar (pos i0))) := by
    have hsub : ∀ {x}, Relation.ReflTransGen stepU (10 + Z'.1) x →
        Relation.ReflTransGen stepU x (src D (sem_bar (pos i0))) → sem_Chain 10 D (10 + Z'.1) x := by
      intro x h1
      induction h1 with
      | refl => intro _; exact Relation.ReflTransGen.refl
      | @tail a c hZa hac ih =>
        intro hcb
        have hf1 : 1 ≤ fanout D a := sem_step_fanout hac.1
        have hf2 : fanout D a ≤ 1 := by
          have hle := sem_rtg_le hS (fun _ _ s => s.1) hZa
          by_cases heq : a = 10 + Z'.1
          · rw [heq]; exact hZ'_fan1
          · by_contra hge2
            have hleZ := sem_rtg_le hS (fun _ _ s => s.1) (hU_reach _ hac.2.1)
            have hneZ : a ≠ 10 + Z.1 := fun h' => by rw [h'] at hge2; omega
            obtain ⟨y, hyE, hby, hno⟩ := hsplit_after a (by omega) (by omega) hac.2.1.2.1 hac.2.1.2.2.1 hac.2.1.2.2.2 (by omega)
            have hy_not : y ∉ supp 10 D (src D (sem_bar (pos i0))) := by
              rw [hbar0_supp, Finset.mem_singleton]
              intro hyi; subst hyi; exact (Finset.mem_sdiff.1 hi0).2 hyE
            obtain ⟨e, heW, heU, -⟩ := hexit_U y hyE a hby _ (Relation.ReflTransGen.head hac hcb) hy_not
            exact hno e heW heU.2.1 heU.2.2.1 heU.2.2.2
        exact (ih (Relation.ReflTransGen.head hac hcb)).tail ⟨hac.1, by omega⟩
    exact hsub hZ'_reach_bar0 Relation.ReflTransGen.refl
  have hbar0_fan1 : fanout D (src D (sem_bar (pos i0))) = 1 := by
    have hch_all := sem_noempty_chain_out sem_g10_gr h hC hB0 hi0
    have hreach_bar0 : Relation.ReflTransGen (sem_step 10 D) i0.val (src D (sem_bar (pos i0))) :=
      sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi0 (pos_bar_mem hpos hi0))
    have hch_bar0 := sem_noempty_unique sem_g10_gr h hC hB0 hi0 hreach_bar0
    have hstep0 : sem_step 10 D (src D (sem_bar (pos i0))) (10 + (pos i0).1) := sem_step_src hp0_lt (sem_bar (pos i0)).2
    have h1 := sem_step_fanout hstep0
    by_contra hne
    have h2 := sem_branch_empty sem_g10_gr hS hC hi0 hch_bar0 (by omega)
    rw [hbar0_supp] at h2; exact Finset.singleton_ne_empty i0 h2
  have hchain_Z'_p0 : sem_Chain 10 D (10 + Z'.1) (10 + (pos i0).1) :=
    hchain_Z'_bar0.tail ⟨sem_step_src hp0_lt (sem_bar (pos i0)).2, hbar0_fan1⟩

  let inUcd : ℕ → Prop := fun w => w < 10 + D.length ∧ val D (sem_two c d) w = true ∧
    c ∉ supp 10 D w ∧ d ∉ supp 10 D w
  let stepUcd : ℕ → ℕ → Prop := fun u v => sem_step 10 D u v ∧ inUcd u ∧ inUcd v
  have hUcd_entry : ∀ w, inUcd w → w = 10 + Z'.1 ∨ ∃ u, stepUcd u w := by
    intro w hw
    obtain ⟨hwlt, hwv, hcn, hdn⟩ := hw
    have hwge : 10 ≤ w := by
      by_contra hc; rw [val_input D _ w (by omega)] at hwv
      simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hwv
      rcases hwv with h' | h'
      · exact hcn (by rw [mem_supp, val_input D _ w (by omega)]; exact decide_eq_true h')
      · exact hdn (by rw [mem_supp, val_input D _ w (by omega)]; exact decide_eq_true h')
    obtain ⟨j, rfl⟩ : ∃ j, w = 10 + j := ⟨w - 10, by omega⟩
    have hj : j < D.length := by omega
    obtain ⟨ha_lt, hb_lt, -⟩ := hS j hj
    rw [val_gate hS _ j hj] at hwv
    by_cases ht : tag D j = true
    · rw [ht, gop_true, Bool.and_eq_true] at hwv
      by_cases haU : c ∉ supp 10 D (opA D j) ∧ d ∉ supp 10 D (opA D j)
      · right; exact ⟨opA D j, ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ⟨by omega, hwv.1, haU.1, haU.2⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_true, hwv.1, hwv.2]; rfl, hcn, hdn⟩⟩⟩
      · by_cases hbU : c ∉ supp 10 D (opB D j) ∧ d ∉ supp 10 D (opB D j)
        · right; exact ⟨opB D j, ⟨⟨by omega, by omega, Or.inr (by simp)⟩, ⟨by omega, hwv.2, hbU.1, hbU.2⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_true, hwv.1, hwv.2]; rfl, hcn, hdn⟩⟩⟩
        · left
          rw [not_and_or, Classical.not_not, Classical.not_not] at haU hbU
          have haab : ¬(c ∈ supp 10 D (opA D j) ∧ c ∈ supp 10 D (opB D j)) :=
            fun h' => hcn (by rw [sem_supp_and hS hj ht, Finset.mem_inter]; exact h')
          have hbab : ¬(d ∈ supp 10 D (opA D j) ∧ d ∈ supp 10 D (opB D j)) :=
            fun h' => hdn (by rw [sem_supp_and hS hj ht, Finset.mem_inter]; exact h')
          rcases haU with ha | hb <;> rcases hbU with ha' | hb'
          · exact absurd ⟨ha, ha'⟩ haab
          · have := hZ'_uniq_cd j false (sem_mem_W.2 ⟨hj, by rw [sb_src_false]; exact ha, hcn⟩)
              (sem_mem_W.2 ⟨hj, by rw [show src D (j, !false) = opB D j from rfl]; exact hb', hdn⟩); omega
          · have := hZ'_uniq_cd j true (sem_mem_W.2 ⟨hj, by rw [sb_src_true]; exact ha', hcn⟩)
              (sem_mem_W.2 ⟨hj, by rw [show src D (j, !true) = opA D j from rfl]; exact hb, hdn⟩); omega
          · exact absurd ⟨hb, hb'⟩ hbab
    · rw [Bool.not_eq_true] at ht; rw [ht, gop_false, Bool.or_eq_true] at hwv
      have hca : c ∉ supp 10 D (opA D j) := fun hm => hcn (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl hm)
      have hcb : c ∉ supp 10 D (opB D j) := fun hm => hcn (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr hm)
      have hda : d ∉ supp 10 D (opA D j) := fun hm => hdn (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inl hm)
      have hdb : d ∉ supp 10 D (opB D j) := fun hm => hdn (by rw [sem_supp_or hS hj ht, Finset.mem_union]; exact Or.inr hm)
      right
      rcases hwv with ha1 | hb1
      · exact ⟨opA D j, ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ⟨by omega, ha1, hca, hda⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_false, ha1]; rfl, hcn, hdn⟩⟩⟩
      · exact ⟨opB D j, ⟨⟨by omega, by omega, Or.inr (by simp)⟩, ⟨by omega, hb1, hcb, hdb⟩, ⟨hwlt, by rw [val_gate hS _ j hj, ht, gop_false, hb1]; simp, hcn, hdn⟩⟩⟩
  have hUcd_reach : ∀ w, inUcd w → Relation.ReflTransGen stepUcd (10 + Z'.1) w := by
    intro w; induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      rcases hUcd_entry w hw with rfl | ⟨u, hu⟩
      · exact Relation.ReflTransGen.refl
      · exact (ih u (sem_step_lt hS hu.1) hu.2.1).tail hu
  have hout_inUcd : inUcd (outW 10 D) := by
    have hlen : 0 < D.length := by omega
    refine ⟨by unfold outW; omega, (hC _).2 (sem_two_edge hcd), ?_, ?_⟩
    · rw [sem_supp_out sem_g10_gr hC]; exact Finset.notMem_empty c
    · rw [sem_supp_out sem_g10_gr hC]; exact Finset.notMem_empty d
  have hZ'_to_out := hUcd_reach _ hout_inUcd

  have hp0_inUcd : inUcd (10 + (pos i0).1) := by
    have hcomp : ∀ {a}, sem_Chain 10 D a (10 + (pos i0).1) → Relation.ReflTransGen stepUcd a (outW 10 D) →
        inUcd (10 + (pos i0).1) := by
      intro a h1
      induction h1 using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro h2
        rcases Relation.ReflTransGen.cases_head h2 with heq | ⟨_, hs, -⟩
        · exact heq ▸ hout_inUcd
        · exact hs.2.1
      | head hac hcp ih =>
        intro h2
        rcases Relation.ReflTransGen.cases_head h2 with heq | ⟨e, hae, heo⟩
        · exfalso
          have h1' := sem_step_lt hS hac.1
          have h2' := sem_rtg_le hS (fun _ _ s => s.1) hcp
          rw [heq] at h1'; unfold outW at h1'; omega
        · exact ih (hfan1_det hac.2 hac.1 hae.1 ▸ heo)
    exact hcomp hchain_Z'_p0 hZ'_to_out
  have hsrcp0_inUcd : inUcd (src D (pos i0)) := by
    have ht0 : tag D (pos i0).1 = true := sem_W_and hS (e := sem_bar (pos i0)) (as_W h hD hpos hi0 ▸ Finset.mem_singleton_self _)
    have hv := hp0_inUcd.2.1
    rw [val_gate hS _ (pos i0).1 hp0_lt, ht0, gop_true, Bool.and_eq_true] at hv
    have hsrcv : val D (sem_two c d) (src D (pos i0)) = true := by
      cases hs : (pos i0).2 <;> simp [src, hs] at hv ⊢
      · exact hv.1
      · exact hv.2
    exact ⟨(src_lt hS (e := pos i0) hp0_lt).trans (by omega), hsrcv, hcn_p0, hdn_p0⟩
  have hZ'_to_srcp0 := hUcd_reach _ hsrcp0_inUcd
  have hsrc_ne_bar : src D (pos i0) ≠ src D (sem_bar (pos i0)) := fun heq => by
    have := hp0_a1; rw [heq, hbar0_supp, Finset.mem_singleton] at this; exact ha1i0 this

  have hcomp2 : ∀ {a}, sem_Chain 10 D a (src D (sem_bar (pos i0))) →
      Relation.ReflTransGen stepUcd a (src D (pos i0)) →
      Relation.ReflTransGen (sem_step 10 D) (src D (sem_bar (pos i0))) (src D (pos i0)) ∨
      sem_Chain 10 D (src D (pos i0)) (src D (sem_bar (pos i0))) := by
    intro a h1
    induction h1 using Relation.ReflTransGen.head_induction_on with
    | refl => intro h2; exact Or.inl (sem_rtg_mono (fun _ _ s => s.1) h2)
    | head hae heb ih =>
      intro h2
      rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨f, haf, hfs⟩
      · exact Or.inr (Relation.ReflTransGen.head hae heb)
      · exact ih (hfan1_det hae.2 hae.1 haf.1 ▸ hfs)
  rcases hcomp2 hchain_Z'_bar0 hZ'_to_srcp0 with h1 | h2
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨e, he1, he2⟩
    · exact hsrc_ne_bar heq.symm
    · have hceq := hfan1_det hbar0_fan1 he1 (sem_step_src hp0_lt (sem_bar (pos i0)).2)
      rw [hceq] at he2
      have hle := sem_rtg_le hS (fun _ _ s => s) he2
      have hlt := src_lt hS (e := pos i0) hp0_lt
      omega
  · rcases Relation.ReflTransGen.cases_head h2 with heq | ⟨e, he1, he2⟩
    · exact hsrc_ne_bar heq
    · have hceq := hfan1_det he1.2 he1.1 (sem_step_src hp0_lt (pos i0).2)
      rw [hceq] at he2
      have hle := sem_rtg_le hS (fun _ _ s => s.1) he2
      omega

theorem elim_17_R1 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (hB : Bplus 10 D = (eligSet 10 D).card + 1) (hI : ineligSet 10 D = {0, 1, 3}) : False := by
  have hS := h.1
  have hC := sem_g10_comp hD
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g10_gr hS hC
  have hbp := sem_minBranch_pure hbm
  obtain ⟨pos, P, Q, hctx⟩ := pa_setup_one h hD hB
  have hpos := hctx.1
  have hR1 : (residualUnits 10 D br).card = 1 := by have := card_residual hS br hbp; omega
  obtain ⟨u0, hRu0⟩ := Finset.card_eq_one.1 hR1
  have hm : ∀ v : Fin 10, v ∈ ({0, 1, 3} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({0, 1, 3} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hI ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({0, 1, 3} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hI ▸ sem_mem_inelig.2 hc)
  have h4_3 := two_in_deg3 h hD hpos (hm 0 (by decide)) (hm 3 (by decide)) (u := 4) (v := 9) (by decide)
  have hru4 : ru D br 4 = {u0} := by
    have hcc := cc_le h hD br hbp 4
    have hsub : ru D br 4 ⊆ {u0} := by rw [← hRu0]; exact Finset.filter_subset _ _
    exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)
  have hle2_of_nb : ∀ x : Fin 10, w3_bad 4 0 3 x = false → (sem_W 10 D x).card ≤ 2 := fun x hnb => by
    have hnot := w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide))
      (x := 4) (v := 9) (by decide) hru4 hnb
    have hrux : ru D br x = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
      exact hnot ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
    have := cc_le h hD br hbp x; rw [hrux, Finset.card_empty] at this; omega
  have hW2_2 : (sem_W 10 D 2).card ≤ 2 := hle2_of_nb 2 (by decide)
  have hW2_6 : (sem_W 10 D 6).card ≤ 2 := hle2_of_nb 6 (by decide)
  have hW2_7 : (sem_W 10 D 7).card ≤ 2 := hle2_of_nb 7 (by decide)
  have hW2_9 : (sem_W 10 D 9).card ≤ 2 := hle2_of_nb 9 (by decide)
  by_cases h5_3 : 3 ≤ (sem_W 10 D 5).card
  · have h8_2 : (sem_W 10 D 8).card ≤ 2 := by
      by_contra h8_3; push Not at h8_3
      exact hnot33_pair h hD hB0 hctx 5 8 0 3 (hm 0 (by decide)) (hm 3 (by decide))
        (hn 5 (by decide)) (hn 8 (by decide)) (by decide) h5_3 h8_3
    exact pa_m1_gen h hD hpos 8 6 5 3 1 2 (hm 3 (by decide)) (hm 1 (by decide))
      (hn 8 (by decide)) (hn 6 (by decide)) (hn 5 (by decide)) (by decide) h8_2 hW2_6
  · have hW2_5 : (sem_W 10 D 5).card ≤ 2 := by omega
    by_cases h8_3 : 3 ≤ (sem_W 10 D 8).card
    ·
      have hru8 : ru D br 8 = {u0} := by
        have hcc := cc_le h hD br hbp 8
        have hsub : ru D br 8 ⊆ {u0} := by rw [← hRu0]; exact Finset.filter_subset _ _
        exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)
      have hM4 : merges 10 D (carrierT 10 D {4}) = ∅ := by
        have := cc_le h hD br hbp 4; rw [hru4, Finset.card_singleton] at this; exact Finset.card_eq_zero.1 (by omega)
      have hM8 : merges 10 D (carrierT 10 D {8}) = ∅ := by
        have := cc_le h hD br hbp 8; rw [hru8, Finset.card_singleton] at this; exact Finset.card_eq_zero.1 (by omega)
      have hW4_le3 : (sem_W 10 D 4).card ≤ 3 := hctx.2.1 4
      have hW8_le3 : (sem_W 10 D 8).card ≤ 3 := hctx.2.1 8
      obtain ⟨Z5, hZ5n, hW5, hZ5p⟩ := ps_nonadj h hD hpos (hm 0 (by decide)) (by decide) (by decide : Adj 0 4) (by decide) (by decide) hW2_5
      obtain ⟨Z6, hZ6n, hW6, hZ6p⟩ := ps_nonadj h hD hpos (hm 1 (by decide)) (by decide) (by decide : Adj 1 2) (by decide) (by decide) hW2_6
      have hbZ5_8 : sem_bar Z5 ∈ sem_W 10 D 8 := by
        obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 5 8)
        rw [hW5, Finset.mem_insert, Finset.mem_singleton] at he
        have : e = Z5 := he.resolve_left (fun hh => hn 8 (by decide) (hf 0 (hm 0 (by decide)) hh ▸ hm 0 (by decide)))
        rwa [← this]
      have hbZ5_7 : sem_bar Z5 ∈ sem_W 10 D 7 := by
        obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 5 7)
        rw [hW5, Finset.mem_insert, Finset.mem_singleton] at he
        have : e = Z5 := he.resolve_left (fun hh => hn 7 (by decide) (hf 0 (hm 0 (by decide)) hh ▸ hm 0 (by decide)))
        rwa [← this]
      have hbZ6_8 : sem_bar Z6 ∈ sem_W 10 D 8 := by
        obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 6 8)
        rw [hW6, Finset.mem_insert, Finset.mem_singleton] at he
        have : e = Z6 := he.resolve_left (fun hh => hn 8 (by decide) (hf 1 (hm 1 (by decide)) hh ▸ hm 1 (by decide)))
        rwa [← this]
      have hbZ6_9 : sem_bar Z6 ∈ sem_W 10 D 9 := by
        obtain ⟨e, he, hbe, hf, -⟩ := pa_ed h hD hpos (by decide : Adj 6 9)
        rw [hW6, Finset.mem_insert, Finset.mem_singleton] at he
        have : e = Z6 := he.resolve_left (fun hh => hn 9 (by decide) (hf 1 (hm 1 (by decide)) hh ▸ hm 1 (by decide)))
        rwa [← this]
      have hZ56 : Z5 ≠ Z6 := fun hh => hZ5p 6 (by decide) (by decide) (by rw [hh, hW6]; simp)
      have hb56 : sem_bar Z5 ≠ sem_bar Z6 := fun hh => hZ56 (by simpa [sem_bar_bar] using congrArg sem_bar hh)
      have hp3_8 := as_mem hpos (hm 3 (by decide)) (by decide : Adj 3 8)
      have hp3_ne_b5 : pos 3 ≠ sem_bar Z5 := fun hh => by
        have := as_priv hpos (hm 3 (by decide)) (by rw [hh, sem_bar_bar, hW5]; simp); exact absurd this (by decide)
      have hp3_ne_b6 : pos 3 ≠ sem_bar Z6 := fun hh => by
        have := as_priv hpos (hm 3 (by decide)) (by rw [hh, sem_bar_bar, hW6]; simp); exact absurd this (by decide)
      have hW8_eq : sem_W 10 D 8 = {pos 3, sem_bar Z5, sem_bar Z6} := by
        symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with rfl | rfl | rfl; exact hp3_8; exact hbZ5_8; exact hbZ6_8
        · rw [Finset.card_insert_of_notMem (by simp [hp3_ne_b5, hp3_ne_b6]), Finset.card_pair hb56]; exact hW8_le3

      have hch0 := pos_chain_or h hD hB0 hpos (hm 0 (by decide)) (by decide : Adj 0 5) (fun p hp hne hsub => by
        rw [hW5, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hne rfl
        · exact hn 8 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbZ5_8).2.1) ▸ hm 0 (by decide)))
      have hch1 := pos_chain_or h hD hB0 hpos (hm 1 (by decide)) (by decide : Adj 1 6) (fun p hp hne hsub => by
        rw [hW6, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact hne rfl
        · exact hn 8 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbZ6_8).2.1) ▸ hm 1 (by decide)))
      obtain ⟨hfull0, hfull3⟩ := full_of_two_in_deg3 h hD hB0 hpos (hm 0 (by decide)) (hm 3 (by decide))
        (u := 4) (v := 9) (by decide) hW4_le3

      obtain ⟨ev, hev4, hbev9, hfev, -⟩ := pa_ed h hD hpos (by decide : Adj 4 9)
      have hp0_4 := as_mem hpos (hm 0 (by decide)) (by decide : Adj 0 4)
      have hp3_4 := as_mem hpos (hm 3 (by decide)) (by decide : Adj 3 4)
      have hW4_eq : sem_W 10 D 4 = {pos 0, pos 3, ev} := by
        have hp03 : pos 0 ≠ pos 3 := fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 3 (by decide)) e) (by decide)
        have hp0e : pos 0 ≠ ev := fun e => hn 9 (by decide) (hfev _ (hm 0 (by decide)) e.symm ▸ hm 0 (by decide))
        have hp3e : pos 3 ≠ ev := fun e => hn 9 (by decide) (hfev _ (hm 3 (by decide)) e.symm ▸ hm 3 (by decide))
        symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with rfl | rfl | rfl; exact hp0_4; exact hp3_4; exact hev4
        · rw [Finset.card_insert_of_notMem (by simp [hp03, hp0e]), Finset.card_pair hp3e]; exact hW4_le3
      have hch3 := pos_chain_or h hD hB0 hpos (hm 3 (by decide)) (by decide : Adj 3 4) (fun p hp hne hsub => by
        rw [hW4_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl | rfl
        · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 0 (by decide))))) (by decide)
        · exact hne rfl
        · exact hn 9 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbev9).2.1) ▸ hm 3 (by decide)))
      obtain ⟨hP4, hQ4⟩ := hctx.2.2.2 4 h4_3
      obtain ⟨hP8, hQ8⟩ := hctx.2.2.2 8 h8_3
      have hp0_not8 : pos 0 ∉ sem_W 10 D 8 := fun hm8 => absurd (hfull0 8 (sem_mem_W.1 hm8).2.1) (by decide)
      have hev_in8 : ev ∈ sem_W 10 D 8 := by
        have hPne0 : P ≠ pos 0 := fun e => hp0_not8 (e ▸ hP8)
        have hQne0 : Q ≠ pos 0 := fun e => hp0_not8 (e ▸ hQ8)
        rw [hW4_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hP4 hQ4
        rcases hP4 with rfl | rfl | rfl
        · exact absurd rfl hPne0
        · rcases hQ4 with rfl | rfl | rfl
          · exact absurd rfl hQne0
          · exact absurd rfl hctx.2.2.1
          · exact hQ8
        · exact hP8
      have hev_eq : ev = sem_bar Z5 := by
        rw [hW8_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hev_in8
        rcases hev_in8 with heq | heq | heq
        · exact absurd heq (fun e => hn 9 (by decide) (hfev _ (hm 3 (by decide)) e ▸ hm 3 (by decide)))
        · exact heq
        · exfalso; exact hZ6p 9 (by decide) (by decide) (by rw [heq, sem_bar_bar] at hbev9; exact hbev9)
      subst hev_eq
      have hZ5_9 : Z5 ∈ sem_W 10 D 9 := by simpa [sem_bar_bar] using hbev9
      have hZ5_ne_b6 : Z5 ≠ sem_bar Z6 := fun hh => hZ6p 4 (by decide) (by decide) (by rw [hh, sem_bar_bar] at hev4; exact hev4)
      have hW9_eq : sem_W 10 D 9 = {Z5, sem_bar Z6} := by
        symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hZ5_ne_b6]; exact hW2_9)
        rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ5_9; exact hbZ6_9

      obtain ⟨Z2, hZ2_2, hZ2_7, hf2, -⟩ := pa_ed h hD hpos (by decide : Adj 2 7)
      have hZ2_ne1 : Z2 ≠ pos 1 := fun hh => hn 7 (by decide) (hf2 1 (hm 1 (by decide)) hh ▸ hm 1 (by decide))
      have hW2_eq : sem_W 10 D 2 = {pos 1, Z2} := by
        symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hZ2_ne1.symm]; exact hW2_2)
        rw [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl; exact as_mem hpos (hm 1 (by decide)) (by decide : Adj 1 2); exact hZ2_2

      have hZ5_val_89 : val D (sem_two (9 : Fin 10) (8 : Fin 10)) (10 + Z5.1) = true := by
        have hj5 := (sem_mem_W.1 hZ5_9).1; have ht5 := sem_W_and hS hZ5_9
        have h9s := val_mono hS (fun i => decide (i = 9)) (sem_two (9 : Fin 10) (8 : Fin 10))
          (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D Z5) (mem_supp.1 (sem_mem_W.1 hZ5_9).2.1)
        have h8s := val_mono hS (fun i => decide (i = 8)) (sem_two (9 : Fin 10) (8 : Fin 10))
          (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D (sem_bar Z5)) (mem_supp.1 (sem_mem_W.1 hbZ5_8).2.1)
        rw [val_gate hS _ Z5.1 hj5, ht5, gop_true]
        rcases hZeq : Z5 with ⟨j, s⟩; rw [hZeq] at h9s h8s
        cases s
        · rw [sb_src_false] at h9s; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at h8s; simp [h9s, h8s]
        · rw [sb_src_true] at h9s; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at h8s; simp [h9s, h8s]
      have hp0_val_89 : val D (sem_two (9 : Fin 10) (8 : Fin 10)) (src D (sem_bar (pos 0))) = true := by
        obtain ⟨e, he5, -, he89, hbe89⟩ := pa_ed_avoid_min h hD (u := 5) (v := 8) (a := 9) (b := 8)
          (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)
        rw [hW5, Finset.mem_insert, Finset.mem_singleton] at he5
        rcases he5 with rfl | rfl
        · exact hbe89
        · rw [hZ5_val_89] at he89; exact Bool.noConfusion he89
      have hfan_gt_Z5 : ∀ w, 10 + Z5.1 < w → val D (sem_two (9 : Fin 10) (8 : Fin 10)) w = true →
          (9 : Fin 10) ∉ supp 10 D w → (8 : Fin 10) ∉ supp 10 D w → 2 ≤ fanout D w →
          (br 2 = w ∨ br 6 = w) := by
        intro w hgt _ h9n h8n hfw
        have hne_s := sem_bzero_branch hS hB0 hfw
        have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
          rw [unitsPlus, Finset.mem_filter, mem_units]
          exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), by show 0 + 1 < fanout D w; omega⟩, hne_s⟩
        have hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D br := by
          by_contra hnr
          have hmemR : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits 10 D br := Finset.mem_sdiff.2 ⟨hwu, hnr⟩
          rw [hRu0, Finset.mem_singleton] at hmemR
          have hweq : w = u0.1 := congrArg Sigma.fst hmemR
          exact h8n (hweq ▸ (mem_ru.1 (hru8 ▸ Finset.mem_singleton_self u0)).2)
        obtain ⟨y, hyE, hyeq⟩ := Finset.mem_image.1 hwr
        have hby : br y = w := congrArg Sigma.fst hyeq
        fin_cases y
        · exact absurd hyE (Finset.mem_sdiff.1 (hm 0 (by decide))).2
        · exact absurd hyE (Finset.mem_sdiff.1 (hm 1 (by decide))).2
        · exact Or.inl hby
        · exact absurd hyE (Finset.mem_sdiff.1 (hm 3 (by decide))).2
        · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE hev4)
        · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE (by rw [hW5]; simp : Z5 ∈ sem_W 10 D 5))
        · exact Or.inr hby
        · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE hbZ5_7)
        · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE hbZ5_8)
        · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE hZ5_9)

      have hZ2_not_U89 : ¬(val D (sem_two (9 : Fin 10) (8 : Fin 10)) (10 + Z2.1) = true ∧ (9 : Fin 10) ∉ supp 10 D (10 + Z2.1) ∧ (8 : Fin 10) ∉ supp 10 D (10 + Z2.1)) := by
        rintro ⟨hv2, h9n2, h8n2⟩
        have hj2 := (sem_mem_W.1 hZ2_2).1; have ht2 := sem_W_and hS hZ2_2
        rw [val_gate hS _ Z2.1 hj2, ht2, gop_true, Bool.and_eq_true] at hv2

        have hM7 : merges 10 D (carrierT 10 D {7}) = ∅ := by
          have h27 : (sem_W 10 D 7).card = 2 := by
            have hne7 : sem_bar Z2 ≠ sem_bar Z5 := fun hh => hZ5p 2 (by decide) (by decide) (by
              have : Z2 = Z5 := by simpa [sem_bar_bar] using congrArg sem_bar hh
              rw [← this]; exact hZ2_2)
            have hsub : ({sem_bar Z2, sem_bar Z5} : Finset (ℕ × Bool)) ⊆ sem_W 10 D 7 := by
              intro f hf; rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ2_7; exact hbZ5_7
            have := Finset.card_le_card hsub; rw [Finset.card_pair hne7] at this; omega
          have hru7 : ru D br 7 = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
            exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide))
              (x := 4) (v := 9) (by decide) hru4 (t := 7) (by decide) ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
          have := cc_le h hD br hbp 7; rw [hru7, Finset.card_empty] at this; exact Finset.card_eq_zero.1 (by omega)
        have hM9 : merges 10 D (carrierT 10 D {9}) = ∅ := by
          have hru9 : ru D br 9 = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
            exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide))
              (x := 4) (v := 9) (by decide) hru4 (t := 9) (by decide) ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
          have h29 : (sem_W 10 D 9).card = 2 := by rw [hW9_eq, Finset.card_pair hZ5_ne_b6]
          have := cc_le h hD br hbp 9; rw [hru9, Finset.card_empty] at this; exact Finset.card_eq_zero.1 (by omega)
        have hZ2_ne_Z5 : Z2 ≠ Z5 := fun hh => hZ5p 2 (by decide) (by decide) (hh ▸ hZ2_2)
        have hZ2_ne_b5 : Z2 ≠ sem_bar Z5 := fun hh => by
          have := hh ▸ hZ2_7; rw [sem_bar_bar] at this; exact hZ5p 7 (by decide) (by decide) this
        have hZ2_ne_b6 : Z2 ≠ sem_bar Z6 := fun hh => by
          obtain ⟨f, hf, h5n, h2n⟩ := g10_deg3_cover_free h hD (x := 9) (a := 5) (b := 2) (by decide) (by decide) (by decide) (by decide)
          rw [hW9_eq, Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with hf' | hf'
          · exact h5n (sem_mem_W.1 (by rw [hf', hW5]; simp : f ∈ sem_W 10 D 5)).2.1
          · exact h2n (sem_mem_W.1 (by rw [hf', ← hh]; exact hZ2_2)).2.1
        have hZ2_ne_p3 : Z2 ≠ pos 3 := fun hh => hn 7 (by decide) (hf2 3 (hm 3 (by decide)) hh ▸ hm 3 (by decide))
        have hbZ2_ne_p3 : sem_bar Z2 ≠ pos 3 := fun hh => by
          have := as_priv hpos (hm 3 (by decide)) (by rw [← hh, sem_bar_bar]; exact hZ2_2); exact absurd this (by decide)
        have hbZ2_ne_Z5 : sem_bar Z2 ≠ Z5 := fun hh => hZ5p 7 (by decide) (by decide) (hh ▸ hZ2_7)
        have hbZ2_ne_b5 : sem_bar Z2 ≠ sem_bar Z5 := fun hh => hZ2_ne_Z5 (by simpa [sem_bar_bar] using congrArg sem_bar hh)
        have hbZ2_ne_b6 : sem_bar Z2 ≠ sem_bar Z6 := fun hh => by
          have h26 : Z2 = Z6 := by simpa [sem_bar_bar] using congrArg sem_bar hh
          have h67 : sem_bar Z6 ∈ sem_W 10 D 7 := h26 ▸ hZ2_7
          obtain ⟨f, hf, h4n, h7n⟩ := g10_deg3_cover_free h hD (x := 8) (a := 4) (b := 7) (by decide) (by decide) (by decide) (by decide)
          rw [hW8_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with rfl | rfl | rfl
          · exact h4n (sem_mem_W.1 hp3_4).2.1
          · exact h4n (sem_mem_W.1 hev4).2.1
          · exact h7n (sem_mem_W.1 h67).2.1
        have h9n_s : (9 : Fin 10) ∉ supp 10 D (src D Z2) := fun hm9 => by
          have := zm_mem hS hM9 hj2 ht2 hm9; rw [hW9_eq, Finset.mem_insert, Finset.mem_singleton] at this
          exact this.elim hZ2_ne_Z5 hZ2_ne_b6
        have h8n_s : (8 : Fin 10) ∉ supp 10 D (src D Z2) := fun hm8 => by
          have := zm_mem hS hM8 hj2 ht2 hm8; rw [hW8_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h' | h' | h'; exact hZ2_ne_p3 h'; exact hZ2_ne_b5 h'; exact hZ2_ne_b6 h'
        have h9n_b : (9 : Fin 10) ∉ supp 10 D (src D (sem_bar Z2)) := fun hm9 => by
          have := zm_mem hS hM9 (e := sem_bar Z2) hj2 ht2 hm9; rw [hW9_eq, Finset.mem_insert, Finset.mem_singleton] at this
          exact this.elim hbZ2_ne_Z5 hbZ2_ne_b6
        have h8n_b : (8 : Fin 10) ∉ supp 10 D (src D (sem_bar Z2)) := fun hm8 => by
          have := zm_mem hS hM8 (e := sem_bar Z2) hj2 ht2 hm8; rw [hW8_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h' | h' | h'; exact hbZ2_ne_p3 h'; exact hbZ2_ne_b5 h'; exact hbZ2_ne_b6 h'

        have h2n_b : (2 : Fin 10) ∉ supp 10 D (src D (sem_bar Z2)) := fun hm2 => by
          have hM2 : merges 10 D (carrierT 10 D {2}) = ∅ := by
            have hru2 : ru D br 2 = ∅ := by
              rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
              exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide))
                (x := 4) (v := 9) (by decide) hru4 (t := 2) (by decide) ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
            have h22 : (sem_W 10 D 2).card = 2 := by rw [hW2_eq, Finset.card_pair hZ2_ne1.symm]
            have := cc_le h hD br hbp 2; rw [hru2, Finset.card_empty] at this; exact Finset.card_eq_zero.1 (by omega)
          exact w_bar hS hZ2_2 (zm_mem hS hM2 hj2 ht2 hm2)
        have hs_val : val D (sem_two (9 : Fin 10) (8 : Fin 10)) (src D Z2) = true ∧ val D (sem_two (9 : Fin 10) (8 : Fin 10)) (src D (sem_bar Z2)) = true := by
          cases hs : Z2.2 <;> simp [src, sem_bar, hs] at hv2 ⊢ <;> [exact hv2; exact ⟨hv2.2, hv2.1⟩]

        let inU2 : ℕ → Prop := fun w => w < 10 + D.length ∧ val D (sem_two (9 : Fin 10) (8 : Fin 10)) w = true ∧
          (9 : Fin 10) ∉ supp 10 D w ∧ (8 : Fin 10) ∉ supp 10 D w
        let stepU2 : ℕ → ℕ → Prop := fun u v => sem_step 10 D u v ∧ inU2 u ∧ inU2 v
        have hU2_reach : ∀ w, inU2 w → Relation.ReflTransGen stepU2 (10 + Z5.1) w := by
          intro w; induction w using Nat.strong_induction_on with
          | _ w ih =>
            intro hw
            obtain ⟨hwlt, hwv, h9n', h8n'⟩ := hw
            have hwge : 10 ≤ w := by
              by_contra hc; rw [val_input D _ w (by omega)] at hwv
              simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hwv
              rcases hwv with h' | h'
              · exact h9n' (by rw [mem_supp, val_input D _ w (by omega)]; exact decide_eq_true h')
              · exact h8n' (by rw [mem_supp, val_input D _ w (by omega)]; exact decide_eq_true h')
            obtain ⟨k, rfl⟩ : ∃ k, w = 10 + k := ⟨w - 10, by omega⟩
            have hk : k < D.length := by omega
            obtain ⟨ha_lt, hb_lt, -⟩ := hS k hk
            rw [val_gate hS _ k hk] at hwv
            by_cases ht : tag D k = true
            · rw [ht, gop_true, Bool.and_eq_true] at hwv
              by_cases haU : (9 : Fin 10) ∉ supp 10 D (opA D k) ∧ (8 : Fin 10) ∉ supp 10 D (opA D k)
              · exact (ih (opA D k) ha_lt ⟨by omega, hwv.1, haU.1, haU.2⟩).tail
                  ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ⟨by omega, hwv.1, haU.1, haU.2⟩,
                    ⟨hwlt, by rw [val_gate hS _ k hk, ht, gop_true, hwv.1, hwv.2]; rfl, h9n', h8n'⟩⟩
              · by_cases hbU : (9 : Fin 10) ∉ supp 10 D (opB D k) ∧ (8 : Fin 10) ∉ supp 10 D (opB D k)
                · exact (ih (opB D k) hb_lt ⟨by omega, hwv.2, hbU.1, hbU.2⟩).tail
                    ⟨⟨by omega, by omega, Or.inr (by simp)⟩, ⟨by omega, hwv.2, hbU.1, hbU.2⟩,
                      ⟨hwlt, by rw [val_gate hS _ k hk, ht, gop_true, hwv.1, hwv.2]; rfl, h9n', h8n'⟩⟩
                · rw [not_and_or, Classical.not_not, Classical.not_not] at haU hbU
                  have huniq : ∀ s', (k, s') ∈ sem_W 10 D 9 → (k, !s') ∈ sem_W 10 D 8 → k = Z5.1 := by
                    intro s' h9W h8W
                    rw [hW9_eq, Finset.mem_insert, Finset.mem_singleton] at h9W
                    rw [hW8_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h8W
                    rcases h9W with h9e | h9e
                    · exact congrArg Prod.fst h9e
                    · exfalso; have h8e' : (k, !s') = Z6 := by simpa [sem_bar, sem_bar_bar] using congrArg sem_bar h9e
                      rw [h8e'] at h8W
                      rcases h8W with h' | h' | h'
                      · exact absurd (hfull3 6 (sem_mem_W.1 (by rw [← h', hW6]; simp : pos 3 ∈ sem_W 10 D 6)).2.1) (by decide)
                      · have : Z5 = sem_bar Z6 := by simpa [sem_bar_bar] using congrArg sem_bar h'.symm
                        exact hZ5p 8 (by decide) (by decide) (this ▸ hbZ6_8)
                      · exact sem_bar_ne Z6 h'.symm
                  have haab : ¬((9 : Fin 10) ∈ supp 10 D (opA D k) ∧ (9 : Fin 10) ∈ supp 10 D (opB D k)) :=
                    fun h' => h9n' (by rw [sem_supp_and hS hk ht, Finset.mem_inter]; exact h')
                  have hbab : ¬((8 : Fin 10) ∈ supp 10 D (opA D k) ∧ (8 : Fin 10) ∈ supp 10 D (opB D k)) :=
                    fun h' => h8n' (by rw [sem_supp_and hS hk ht, Finset.mem_inter]; exact h')
                  have hkeq : k = Z5.1 := by
                    rcases haU with ha | hb <;> rcases hbU with ha' | hb'
                    · exact absurd ⟨ha, ha'⟩ haab
                    · exact huniq false (sem_mem_W.2 ⟨hk, by rw [sb_src_false]; exact ha, h9n'⟩)
                        (sem_mem_W.2 ⟨hk, by rw [show src D (k, !false) = opB D k from rfl]; exact hb', h8n'⟩)
                    · exact huniq true (sem_mem_W.2 ⟨hk, by rw [sb_src_true]; exact ha', h9n'⟩)
                        (sem_mem_W.2 ⟨hk, by rw [show src D (k, !true) = opA D k from rfl]; exact hb, h8n'⟩)
                    · exact absurd ⟨hb, hb'⟩ hbab
                  rw [hkeq]
            · rw [Bool.not_eq_true] at ht; rw [ht, gop_false, Bool.or_eq_true] at hwv
              have h9a : (9 : Fin 10) ∉ supp 10 D (opA D k) := fun hm' => h9n' (by rw [sem_supp_or hS hk ht, Finset.mem_union]; exact Or.inl hm')
              have h9b : (9 : Fin 10) ∉ supp 10 D (opB D k) := fun hm' => h9n' (by rw [sem_supp_or hS hk ht, Finset.mem_union]; exact Or.inr hm')
              have h8a : (8 : Fin 10) ∉ supp 10 D (opA D k) := fun hm' => h8n' (by rw [sem_supp_or hS hk ht, Finset.mem_union]; exact Or.inl hm')
              have h8b : (8 : Fin 10) ∉ supp 10 D (opB D k) := fun hm' => h8n' (by rw [sem_supp_or hS hk ht, Finset.mem_union]; exact Or.inr hm')
              rcases hwv with ha1 | hb1
              · exact (ih (opA D k) ha_lt ⟨by omega, ha1, h9a, h8a⟩).tail
                  ⟨⟨by omega, by omega, Or.inl (by simp)⟩, ⟨by omega, ha1, h9a, h8a⟩,
                    ⟨hwlt, by rw [val_gate hS _ k hk, ht, gop_false, ha1]; rfl, h9n', h8n'⟩⟩
              · exact (ih (opB D k) hb_lt ⟨by omega, hb1, h9b, h8b⟩).tail
                  ⟨⟨by omega, by omega, Or.inr (by simp)⟩, ⟨by omega, hb1, h9b, h8b⟩,
                    ⟨hwlt, by rw [val_gate hS _ k hk, ht, gop_false, hb1]; simp, h9n', h8n'⟩⟩
        have hs_inU : inU2 (src D Z2) := ⟨(src_lt hS hj2).trans (by omega), hs_val.1, h9n_s, h8n_s⟩
        have hb_inU : inU2 (src D (sem_bar Z2)) := ⟨(show src D (sem_bar Z2) < 10 + Z2.1 from src_lt hS (e := sem_bar Z2) hj2).trans (by omega), hs_val.2, h9n_b, h8n_b⟩
        have hps := hU2_reach _ hs_inU
        have hpb := hU2_reach _ hb_inU
        have hb2_no_bar : ∀ hp : Relation.ReflTransGen stepU2 (br 2) (src D (sem_bar Z2)), False := by
          intro hp
          have h2w : (2 : Fin 10) ∈ supp 10 D (br 2) := by rw [(hbm 2 (helig 2 (by decide))).2.1]; exact Finset.mem_singleton_self 2
          have hex : ∀ {t}, Relation.ReflTransGen stepU2 (br 2) t → (2 : Fin 10) ∉ supp 10 D t →
              ∃ e ∈ sem_W 10 D 2, inU2 (10 + e.1) ∧ 10 + e.1 ≤ t := by
            intro t hp' h2t
            induction hp' with
            | refl => exact absurd h2w h2t
            | @tail u v _ hstep ih =>
              by_cases h2u : (2 : Fin 10) ∈ supp 10 D u
              · obtain ⟨hjlt, hjge, hop⟩ := hstep.1
                have hveq : 10 + (v - 10) = v := by omega
                rcases hop with ha | hb'
                · exact ⟨(v - 10, false), sem_mem_W.2 ⟨by omega, by simpa [src, ha] using h2u, by rwa [hveq]⟩, by simpa [hveq] using hstep.2.2, by omega⟩
                · exact ⟨(v - 10, true), sem_mem_W.2 ⟨by omega, by simpa [src, hb'] using h2u, by rwa [hveq]⟩, by simpa [hveq] using hstep.2.2, by omega⟩
              · obtain ⟨e, heW, heU, hele⟩ := ih h2u
                exact ⟨e, heW, heU, hele.trans (sem_step_lt hS hstep.1).le⟩
          obtain ⟨e, heW, heU, hele⟩ := hex hp h2n_b
          rw [hW2_eq, Finset.mem_insert, Finset.mem_singleton] at heW
          rcases heW with he' | he'
          · rw [he'] at heU
            have hg := hch1.2.2 (sem_two (9 : Fin 10) (8 : Fin 10)) heU.2.1
            rw [g10Edge_iff_adj] at hg; obtain ⟨p, q, hpq, hp', hq'⟩ := hg
            simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp' hq'
            rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
            · exact adj_irrefl _ hpq
            · exact absurd hpq (by decide)
            · exact absurd hpq (by decide)
            · exact adj_irrefl _ hpq
          · rw [he'] at hele; have : src D (sem_bar Z2) < 10 + Z2.1 := src_lt hS (e := sem_bar Z2) hj2; omega
        have hstep_s : sem_step 10 D (src D Z2) (10 + Z2.1) := sem_step_src hj2 Z2.2
        have hstep_b : sem_step 10 D (src D (sem_bar Z2)) (10 + Z2.1) := sem_step_src hj2 (sem_bar Z2).2
        have hne_sb : src D Z2 ≠ src D (sem_bar Z2) := fun heq => h2n_b (heq ▸ (sem_mem_W.1 hZ2_2).2.1)
        have hno_div2 : ∀ k a, 10 + Z2.1 - a = k → 10 + Z5.1 ≤ a →
            Relation.ReflTransGen stepU2 a (src D Z2) → Relation.ReflTransGen stepU2 a (src D (sem_bar Z2)) → False := by
          intro k
          induction k using Nat.strong_induction_on with
          | _ k ih =>
            intro a hk hge h1 h2
            rcases Relation.ReflTransGen.cases_head h1 with rfl | ⟨c1, hc1, h1'⟩
            · rcases Relation.ReflTransGen.cases_head h2 with heq | ⟨c2, hc2, h2'⟩
              · exact hne_sb heq
              · by_cases hf2 : 2 ≤ fanout D (src D Z2)
                · have hgt : 10 + Z5.1 < src D Z2 := by
                    by_contra hle; have heq : src D Z2 = 10 + Z5.1 := by omega
                    have hZ5_emp : supp 10 D (10 + Z5.1) = ∅ := by
                      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
                      have hj5 := (sem_mem_W.1 hZ5_9).1; have ht5 := sem_W_and hS hZ5_9
                      fin_cases v
                      · exact (sem_mem_W.1 (as_W h hD hpos (hm 0 (by decide)) ▸ Finset.mem_singleton_self _)).2.2 (by
                          have := (hpos.1 0 (hm 0 (by decide))).2.1; exact absurd (sem_zm_gate hS (by
                            obtain ⟨-, -, -, -, -, -, -, hm0⟩ := sem_inelig_consumer sem_g10_gr h hC (hm 0 (by decide)); exact hm0) hj5 hv).1 (by rw [ht5]; decide))
                      · exact absurd (sem_zm_gate hS (by obtain ⟨-, -, -, -, -, -, -, hm1⟩ := sem_inelig_consumer sem_g10_gr h hC (hm 1 (by decide)); exact hm1) hj5 hv).1 (by rw [ht5]; decide)
                      · have hM2' : merges 10 D (carrierT 10 D {2}) = ∅ := by
                          have hru2 : ru D br 2 = ∅ := by
                            rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
                            exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 (t := 2) (by decide) ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
                          have := cc_le h hD br hbp 2; rw [hru2, Finset.card_empty, hW2_eq, Finset.card_pair hZ2_ne1.symm] at this; exact Finset.card_eq_zero.1 (by omega)
                        exact absurd (sem_zm_gate hS hM2' hj5 hv).1 (by rw [ht5]; decide)
                      · exact absurd (sem_zm_gate hS (by obtain ⟨-, -, -, -, -, -, -, hm3⟩ := sem_inelig_consumer sem_g10_gr h hC (hm 3 (by decide)); exact hm3) hj5 hv).1 (by rw [ht5]; decide)
                      · exact (sem_mem_W.1 hev4).2.2 hv
                      · exact (sem_mem_W.1 (by rw [hW5]; simp : Z5 ∈ sem_W 10 D 5)).2.2 hv
                      · have hM6' : merges 10 D (carrierT 10 D {6}) = ∅ := by
                          have hru6 : ru D br 6 = ∅ := by
                            rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
                            exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 (t := 6) (by decide) ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
                          have := cc_le h hD br hbp 6; rw [hru6, Finset.card_empty, hW6, Finset.card_pair hZ6n.symm] at this; exact Finset.card_eq_zero.1 (by omega)
                        exact absurd (sem_zm_gate hS hM6' hj5 hv).1 (by rw [ht5]; decide)
                      · exact (sem_mem_W.1 hbZ5_7).2.2 hv
                      · exact (sem_mem_W.1 hbZ5_8).2.2 hv
                      · exact (sem_mem_W.1 hZ5_9).2.2 hv
                    have := sem_bzero_branch hS hB0 (heq ▸ hf2); rw [hZ5_emp] at this; exact Finset.not_nonempty_empty this
                  rcases hfan_gt_Z5 _ hgt hs_inU.2.1 hs_inU.2.2.1 hs_inU.2.2.2 hf2 with h2eq | h6eq
                  · exact hb2_no_bar (h2eq.symm ▸ h2)
                  ·
                    have h6in : (6 : Fin 10) ∈ supp 10 D (src D Z2) := by rw [← h6eq, (hbm 6 (helig 6 (by decide))).2.1]; exact Finset.mem_singleton_self 6
                    have hM6' : merges 10 D (carrierT 10 D {6}) = ∅ := by
                      have hru6 : ru D br 6 = ∅ := by
                        rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
                        exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 (t := 6) (by decide) ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
                      have := cc_le h hD br hbp 6; rw [hru6, Finset.card_empty, hW6, Finset.card_pair hZ6n.symm] at this; exact Finset.card_eq_zero.1 (by omega)
                    have := zm_mem hS hM6' hj2 ht2 h6in; rw [hW6, Finset.mem_insert, Finset.mem_singleton] at this
                    rcases this with h' | h'
                    · exact hZ2_ne1 h'
                    · exact hbZ2_ne_b6 (by rw [h'])
                · have hf1 := sem_step_fanout hc2.1
                  have hceq := sem_step_unique hc2.1 hstep_s (by omega)
                  rw [hceq] at h2'
                  have := sem_rtg_le hS (fun _ _ s => s.1) h2'
                  have : src D (sem_bar Z2) < 10 + Z2.1 := src_lt hS (e := sem_bar Z2) hj2; omega
            · rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨c2, hc2, h2'⟩
              · by_cases hf2 : 2 ≤ fanout D (src D (sem_bar Z2))
                · have hgt : 10 + Z5.1 < src D (sem_bar Z2) := by
                    by_contra hle; have heq : src D (sem_bar Z2) = 10 + Z5.1 := by omega
                    exact (sem_mem_W.1 hbZ5_7).2.2 (heq ▸ (sem_mem_W.1 hZ2_7).2.1)
                  rcases hfan_gt_Z5 _ hgt hb_inU.2.1 hb_inU.2.2.1 hb_inU.2.2.2 hf2 with h2eq | h6eq
                  · exact h2n_b (by rw [← h2eq, (hbm 2 (helig 2 (by decide))).2.1]; exact Finset.mem_singleton_self 2)
                  · have h6in : (6 : Fin 10) ∈ supp 10 D (src D (sem_bar Z2)) := by rw [← h6eq, (hbm 6 (helig 6 (by decide))).2.1]; exact Finset.mem_singleton_self 6
                    have hM6' : merges 10 D (carrierT 10 D {6}) = ∅ := by
                      have hru6 : ru D br 6 = ∅ := by
                        rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
                        exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 (t := 6) (by decide) ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
                      have := cc_le h hD br hbp 6; rw [hru6, Finset.card_empty, hW6, Finset.card_pair hZ6n.symm] at this; exact Finset.card_eq_zero.1 (by omega)
                    have := zm_mem hS hM6' (e := sem_bar Z2) hj2 ht2 h6in; rw [hW6, Finset.mem_insert, Finset.mem_singleton] at this
                    rcases this with h' | h'
                    · exact absurd (as_priv hpos (hm 1 (by decide)) (by rw [← h', sem_bar_bar]; exact hZ2_2)) (by decide)
                    · exact hZ2_ne_b6 (by simpa [sem_bar_bar] using congrArg sem_bar h')
                · have hf1 := sem_step_fanout hc1.1
                  have hceq := sem_step_unique hc1.1 hstep_b (by omega)
                  rw [hceq] at h1'
                  have := sem_rtg_le hS (fun _ _ s => s.1) h1'
                  have := src_lt hS hj2; omega
              · by_cases hceq : c1 = c2
                · subst hceq
                  have hlt := sem_step_lt hS hc1.1
                  have hle1 := (sem_rtg_le hS (fun _ _ s => s.1) h1').trans (src_lt hS hj2).le
                  exact ih (10 + Z2.1 - c1) (by omega) c1 rfl (by omega) h1' h2'
                · have hf2 : 2 ≤ fanout D a := by
                    by_contra hf; have hf1 := sem_step_fanout hc1.1
                    exact hceq (sem_step_unique hc1.1 hc2.1 (by omega))
                  have hgt : 10 + Z5.1 < a := by
                    by_contra hle; have haeq : a = 10 + Z5.1 := by omega
                    have hZ5_emp : supp 10 D (10 + Z5.1) = ∅ := by
                      refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
                      have hj5 := (sem_mem_W.1 hZ5_9).1; have ht5 := sem_W_and hS hZ5_9
                      fin_cases v
                      · exact absurd (sem_zm_gate hS (by obtain ⟨-, -, -, -, -, -, -, hm0⟩ := sem_inelig_consumer sem_g10_gr h hC (hm 0 (by decide)); exact hm0) hj5 hv).1 (by rw [ht5]; decide)
                      · exact absurd (sem_zm_gate hS (by obtain ⟨-, -, -, -, -, -, -, hm1⟩ := sem_inelig_consumer sem_g10_gr h hC (hm 1 (by decide)); exact hm1) hj5 hv).1 (by rw [ht5]; decide)
                      · have hM2' : merges 10 D (carrierT 10 D {2}) = ∅ := by
                          have hru2 : ru D br 2 = ∅ := by
                            rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
                            exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 (t := 2) (by decide) ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
                          have := cc_le h hD br hbp 2; rw [hru2, Finset.card_empty, hW2_eq, Finset.card_pair hZ2_ne1.symm] at this; exact Finset.card_eq_zero.1 (by omega)
                        exact absurd (sem_zm_gate hS hM2' hj5 hv).1 (by rw [ht5]; decide)
                      · exact absurd (sem_zm_gate hS (by obtain ⟨-, -, -, -, -, -, -, hm3⟩ := sem_inelig_consumer sem_g10_gr h hC (hm 3 (by decide)); exact hm3) hj5 hv).1 (by rw [ht5]; decide)
                      · exact (sem_mem_W.1 hev4).2.2 hv
                      · exact (sem_mem_W.1 (by rw [hW5]; simp : Z5 ∈ sem_W 10 D 5)).2.2 hv
                      · have hM6' : merges 10 D (carrierT 10 D {6}) = ∅ := by
                          have hru6 : ru D br 6 = ∅ := by
                            rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
                            exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 (t := 6) (by decide) ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
                          have := cc_le h hD br hbp 6; rw [hru6, Finset.card_empty, hW6, Finset.card_pair hZ6n.symm] at this; exact Finset.card_eq_zero.1 (by omega)
                        exact absurd (sem_zm_gate hS hM6' hj5 hv).1 (by rw [ht5]; decide)
                      · exact (sem_mem_W.1 hbZ5_7).2.2 hv
                      · exact (sem_mem_W.1 hbZ5_8).2.2 hv
                      · exact (sem_mem_W.1 hZ5_9).2.2 hv
                    have := sem_bzero_branch hS hB0 (haeq ▸ hf2); rw [hZ5_emp] at this; exact Finset.not_nonempty_empty this
                  rcases hfan_gt_Z5 a hgt hc1.2.1.2.1 hc1.2.1.2.2.1 hc1.2.1.2.2.2 hf2 with h2eq | h6eq
                  · exact hb2_no_bar (h2eq.symm ▸ h2)
                  ·
                    have h6_exit : ∀ {t}, Relation.ReflTransGen stepU2 (br 6) t → (6 : Fin 10) ∉ supp 10 D t →
                        Relation.ReflTransGen stepU2 (10 + Z6.1) t := by
                      intro t hpt h6t
                      have h6w : (6 : Fin 10) ∈ supp 10 D (br 6) := by rw [(hbm 6 (helig 6 (by decide))).2.1]; exact Finset.mem_singleton_self 6
                      induction hpt with
                      | refl => exact absurd h6w h6t
                      | @tail u v _ hstep ih' =>
                        by_cases h6u : (6 : Fin 10) ∈ supp 10 D u
                        · obtain ⟨hjlt, hjge, hop⟩ := hstep.1
                          have hveq : 10 + (v - 10) = v := by omega
                          have heW : ∃ s', (v - 10, s') ∈ sem_W 10 D 6 := by
                            rcases hop with ha | hb'
                            · exact ⟨false, sem_mem_W.2 ⟨by omega, by simpa [src, ha] using h6u, by rwa [hveq]⟩⟩
                            · exact ⟨true, sem_mem_W.2 ⟨by omega, by simpa [src, hb'] using h6u, by rwa [hveq]⟩⟩
                          obtain ⟨s', hs'⟩ := heW
                          rw [hW6, Finset.mem_insert, Finset.mem_singleton] at hs'
                          rcases hs' with h1' | h6'
                          · exfalso
                            have hg := hch1.2.2 (sem_two (9 : Fin 10) (8 : Fin 10)) (by have := congrArg Prod.fst h1'; simpa [← this, hveq] using hstep.2.2.2.1)
                            rw [g10Edge_iff_adj] at hg; obtain ⟨p, q, hpq, hp', hq'⟩ := hg
                            simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp' hq'
                            rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
                            · exact adj_irrefl _ hpq
                            · exact absurd hpq (by decide)
                            · exact absurd hpq (by decide)
                            · exact adj_irrefl _ hpq
                          · have := congrArg Prod.fst h6'; rw [← this, hveq]
                        · exact (ih' h6u).tail hstep
                    have hM6' : merges 10 D (carrierT 10 D {6}) = ∅ := by
                      have hru6 : ru D br 6 = ∅ := by
                        rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
                        exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 (t := 6) (by decide) ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
                      have := cc_le h hD br hbp 6; rw [hru6, Finset.card_empty, hW6, Finset.card_pair hZ6n.symm] at this; exact Finset.card_eq_zero.1 (by omega)
                    have h6ns : (6 : Fin 10) ∉ supp 10 D (src D Z2) := fun hm6 => by
                      have := zm_mem hS hM6' hj2 ht2 hm6; rw [hW6, Finset.mem_insert, Finset.mem_singleton] at this
                      rcases this with h' | h'; exact hZ2_ne1 h'; exact hbZ2_ne_b6 (by rw [h'])
                    have h6nb : (6 : Fin 10) ∉ supp 10 D (src D (sem_bar Z2)) := fun hm6 => by
                      have := zm_mem hS hM6' (e := sem_bar Z2) hj2 ht2 hm6; rw [hW6, Finset.mem_insert, Finset.mem_singleton] at this
                      rcases this with h' | h'
                      · exact absurd (as_priv hpos (hm 1 (by decide)) (by rw [← h', sem_bar_bar]; exact hZ2_2)) (by decide)
                      · exact hZ2_ne_b6 (by simpa [sem_bar_bar] using congrArg sem_bar h')
                    have hZ6_to_s := h6_exit (h6eq.symm ▸ h1) h6ns
                    have hZ6_to_b := h6_exit (h6eq.symm ▸ h2) h6nb
                    have hlt_a6 : a < 10 + Z6.1 := by
                      have h6w : (6 : Fin 10) ∈ supp 10 D a := by rw [← h6eq, (hbm 6 (helig 6 (by decide))).2.1]; exact Finset.mem_singleton_self 6
                      have hnot_lt := sem_minBranch_not_after h br hbm (helig 6 (by decide)) (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)
                      have hne_a6 : a ≠ 10 + Z6.1 := fun heq => (sem_mem_W.1 (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)).2.2 (heq ▸ h6w)
                      omega
                    have hle62 := (sem_rtg_le hS (fun _ _ s => s.1) hZ6_to_s).trans (src_lt hS hj2).le
                    exact ih (10 + Z2.1 - (10 + Z6.1)) (by omega) (10 + Z6.1) rfl (by omega) hZ6_to_s hZ6_to_b
        exact hno_div2 (10 + Z2.1 - (10 + Z5.1)) (10 + Z5.1) rfl le_rfl hps hpb
      have hfan1_of_not8 : ∀ (g : ℕ), g < D.length → tag D g = true → (8 : Fin 10) ∉ supp 10 D (10 + g) →
          fanout D (10 + g) ≤ 1 := fun g hg ht h8n => by
        by_contra hf
        have hne_s := sem_bzero_branch hS hB0 (by omega : 2 ≤ fanout D (10 + g))
        have hwu : (⟨10 + g, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
          rw [unitsPlus, Finset.mem_filter, mem_units]
          exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := 10 + g) (by omega)), by show 0 + 1 < fanout D (10 + g); omega⟩, hne_s⟩
        have hwr : (⟨10 + g, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D br := by
          by_contra hnr
          have hmemR : (⟨10 + g, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits 10 D br := Finset.mem_sdiff.2 ⟨hwu, hnr⟩
          rw [hRu0, Finset.mem_singleton] at hmemR
          have hge : 10 + g = u0.1 := congrArg Sigma.fst hmemR
          rw [hge] at h8n; exact h8n (mem_ru.1 (hru8 ▸ Finset.mem_singleton_self u0)).2
        obtain ⟨y, hyE, hyeq⟩ := Finset.mem_image.1 hwr
        exact sem_minBranch_not_and h br hbm hyE hg ht (congrArg Sigma.fst hyeq)
      have hZ5_fan1 : fanout D (10 + Z5.1) ≤ 1 :=
        hfan1_of_not8 Z5.1 (sem_mem_W.1 hZ5_9).1 (sem_W_and hS hZ5_9) (sem_mem_W.1 hbZ5_8).2.2
      have hZ6_fan1 : fanout D (10 + Z6.1) ≤ 1 :=
        hfan1_of_not8 Z6.1 (sem_mem_W.1 (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)).1 (sem_W_and hS (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)) (sem_mem_W.1 hbZ6_8).2.2
      exact kill_4cycle_gate h hD hB0 br hbm hpos
        (Z := Z5) (Z' := Z6) (a1 := 5) (b1 := 4) (a2 := 9) (b2 := 8) (c := 6) (d := 8) (i0 := 0)
        (sem_mem_W.1 hZ5_9).1 (sem_W_and hS hZ5_9)
        (sem_mem_W.1 (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)).1 (sem_W_and hS (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6))
        (sem_mem_W.1 (by rw [hW5]; simp : Z5 ∈ sem_W 10 D 5)).2.1 (sem_mem_W.1 hev4).2.1 (by decide)
        (sem_mem_W.1 hZ5_9).2.1 (sem_mem_W.1 hbZ5_8).2.1 (sem_mem_W.1 hZ5_9).2.2 (sem_mem_W.1 hbZ5_8).2.2
        (fun j s h9W h8W => by
          rw [hW9_eq, Finset.mem_insert, Finset.mem_singleton] at h9W
          rw [hW8_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h8W
          rcases h9W with h9e | h9e
          · exact congrArg Prod.fst h9e
          · exfalso; have h8e' : (j, !s) = Z6 := by simpa [sem_bar, sem_bar_bar] using congrArg sem_bar h9e
            rw [h8e'] at h8W
            rcases h8W with h' | h' | h'
            · exact absurd (hfull3 6 (sem_mem_W.1 (by rw [← h', hW6]; simp : pos 3 ∈ sem_W 10 D 6)).2.1) (by decide)
            · have : Z5 = sem_bar Z6 := by simpa [sem_bar_bar] using congrArg sem_bar h'.symm
              exact hZ5p 8 (by decide) (by decide) (this ▸ hbZ6_8)
            · exact sem_bar_ne Z6 h'.symm)
        (hm 0 (by decide)) (by decide) hch0.2.2 ((hpos.1 0 (hm 0 (by decide))).2.2.1 5 (by decide)) hp0_val_89
        (fun e he hv2 hv1 => by
          have hno_p3 : val D (sem_two (9 : Fin 10) (8 : Fin 10)) (10 + (pos 3).1) = false := by
            by_contra hc; rw [Bool.not_eq_false] at hc
            have hg := hch3.2.2 _ hc; rw [g10Edge_iff_adj] at hg; obtain ⟨p, q, hpq, hp', hq'⟩ := hg
            simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp' hq'
            rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
            · exact adj_irrefl _ hpq
            · exact absurd hpq (by decide)
            · exact absurd hpq (by decide)
            · exact adj_irrefl _ hpq
          have hZ5_val_54 : val D (sem_two (5 : Fin 10) (4 : Fin 10)) (10 + Z5.1) = true := by
            have hj5 := (sem_mem_W.1 hZ5_9).1; have ht5 := sem_W_and hS hZ5_9
            have h5s := val_mono hS (fun i => decide (i = 5)) (sem_two (5 : Fin 10) (4 : Fin 10))
              (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D Z5) (mem_supp.1 (sem_mem_W.1 (by rw [hW5]; simp : Z5 ∈ sem_W 10 D 5)).2.1)
            have h4s := val_mono hS (fun i => decide (i = 4)) (sem_two (5 : Fin 10) (4 : Fin 10))
              (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D (sem_bar Z5)) (mem_supp.1 (sem_mem_W.1 hev4).2.1)
            rw [val_gate hS _ Z5.1 hj5, ht5, gop_true]
            rcases hZeq : Z5 with ⟨j, s⟩; rw [hZeq] at h5s h4s
            cases s
            · rw [sb_src_false] at h5s; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at h4s; simp [h5s, h4s]
            · rw [sb_src_true] at h5s; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at h4s; simp [h5s, h4s]
          rcases he with he9 | he8
          · rw [hW9_eq, Finset.mem_insert, Finset.mem_singleton] at he9
            rcases he9 with rfl | rfl
            · rw [hZ5_val_54] at hv1; exact Bool.noConfusion hv1
            · rfl
          · rw [hW8_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at he8
            rcases he8 with rfl | rfl | rfl
            · rw [hno_p3] at hv2; exact Bool.noConfusion hv2
            · rw [show (sem_bar Z5).1 = Z5.1 from rfl, hZ5_val_54] at hv1; exact Bool.noConfusion hv1
            · rfl)
        (fun w hgt hv2 h9n h8n hfw => by
          rcases hfan_gt_Z5 w hgt hv2 h9n h8n hfw with h2eq | h6eq
          · refine ⟨2, helig 2 (by decide), h2eq, fun e heW hev h9e h8e => ?_⟩
            rw [hW2_eq, Finset.mem_insert, Finset.mem_singleton] at heW
            rcases heW with rfl | rfl
            · exfalso; have hg := hch1.2.2 _ hev; rw [g10Edge_iff_adj] at hg; obtain ⟨p, q, hpq, hp', hq'⟩ := hg
              simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp' hq'
              rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
              · exact adj_irrefl _ hpq
              · exact absurd hpq (by decide)
              · exact absurd hpq (by decide)
              · exact adj_irrefl _ hpq
            · exact absurd ⟨hev, h9e, h8e⟩ hZ2_not_U89
          · refine ⟨6, helig 6 (by decide), h6eq, fun e heW hev _ _ => ?_⟩
            rw [hW6, Finset.mem_insert, Finset.mem_singleton] at heW
            rcases heW with rfl | rfl
            · exfalso; have hg := hch1.2.2 _ hev; rw [g10Edge_iff_adj] at hg; obtain ⟨p, q, hpq, hp', hq'⟩ := hg
              simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp' hq'
              rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
              · exact adj_irrefl _ hpq
              · exact absurd hpq (by decide)
              · exact absurd hpq (by decide)
              · exact adj_irrefl _ hpq
            · rfl)
        (fun w hgt5 hgt6 hv2 h9n h8n hfw => by
          rcases hfan_gt_Z5 w hgt5 hv2 h9n h8n hfw with h2eq | h6eq
          · refine ⟨2, helig 2 (by decide), h2eq, fun e heW hev h9e h8e => ?_⟩
            rw [hW2_eq, Finset.mem_insert, Finset.mem_singleton] at heW
            rcases heW with rfl | rfl
            · have hg := hch1.2.2 _ hev; rw [g10Edge_iff_adj] at hg; obtain ⟨p, q, hpq, hp', hq'⟩ := hg
              simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp' hq'
              rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
              · exact adj_irrefl _ hpq
              · exact absurd hpq (by decide)
              · exact absurd hpq (by decide)
              · exact adj_irrefl _ hpq
            · exact hZ2_not_U89 ⟨hev, h9e, h8e⟩
          · exact absurd (h6eq ▸ hgt6) (sem_minBranch_not_after h br hbm (helig 6 (by decide)) (by rw [hW6]; simp : Z6 ∈ sem_W 10 D 6)))
        (by decide : Adj 6 8)
        (fun j s h6W h8W => by
          rw [hW6, Finset.mem_insert, Finset.mem_singleton] at h6W
          rcases h6W with h6e | h6e
          · exfalso; exact absurd (as_priv hpos (hm 1 (by decide)) (by rw [← h6e]; exact h8W)) (by decide)
          · exact congrArg Prod.fst h6e)
        (fun h6in => absurd (hfull0 6 h6in) (by decide))
        (fun h8in => absurd (hfull0 8 h8in) (by decide))
        hZ5_fan1 hZ6_fan1
    · exact pa_m1_gen h hD hpos 8 5 6 3 0 4 (hm 3 (by decide)) (hm 0 (by decide))
        (hn 8 (by decide)) (hn 5 (by decide)) (hn 6 (by decide)) (by decide) (by omega) hW2_5

theorem elim_18_R1 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (hB : Bplus 10 D = (eligSet 10 D).card + 1) (hI : ineligSet 10 D = {1, 3, 5}) : False := by
  obtain ⟨b, hb⟩ := sem_exists_minBranch sem_g10_gr h.1 (sem_g10_comp hD)
  have hbp := sem_minBranch_pure hb
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h (sem_g10_comp hD)
  have hR1 : (residualUnits 10 D b).card = 1 := by have := card_residual h.1 b hbp; omega
  obtain ⟨u0, hRu0⟩ := Finset.card_eq_one.1 hR1
  have h1 : (1 : Fin 10) ∈ ineligSet 10 D := by rw [hI]; decide
  have h3 : (3 : Fin 10) ∈ ineligSet 10 D := by rw [hI]; decide
  have h5 : (5 : Fin 10) ∈ ineligSet 10 D := by rw [hI]; decide
  have h8_3 := two_in_deg3 h hD hpos h3 h5 (u := 8) (v := 6) (by decide)
  have hru8 : ru D b 8 = {u0} := by
    have hcc := cc_le h hD b hbp 8
    have hsub : ru D b 8 ⊆ {u0} := by rw [← hRu0]; exact Finset.filter_subset _ _
    exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)
  have hle2 : ∀ x : Fin 10, w3_bad 8 3 5 x = false → (sem_W 10 D x).card ≤ 2 := fun x hnb => by
    have hnot := w3_ru_one_not_mem h hD hB0 b hb hpos h3 h5 (x := 8) (v := 6) (by decide) hru8 hnb
    have hrux : ru D b x = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
      exact hnot ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
    have := cc_le h hD b hbp x; rw [hrux, Finset.card_empty] at this; omega
  exact ps_3star_cyc h hD hpos 9 4 6 7 3 1 5 8 2 0 h3 h1 h5 (by rw [hI]; decide) (by decide)
    (hle2 9 (by decide)) (hle2 4 (by decide)) (hle2 6 (by decide)) (hle2 7 (by decide))

theorem elim_20_R1 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (hB : Bplus 10 D = (eligSet 10 D).card + 1) (hI : ineligSet 10 D = {1, 4, 5}) : False := by
  obtain ⟨pos, P, Q, hctx⟩ := pa_setup_one h hD hB
  have hpos := hctx.1
  have hm : ∀ v : Fin 10, v ∈ ({1, 4, 5} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({1, 4, 5} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hI ▸ hv
  have h68 : 3 ≤ (sem_W 10 D 6).card ∨ 3 ≤ (sem_W 10 D 8).card := by
    by_contra hc; push Not at hc
    exact pa_m1_gen h hD hpos 6 8 9 1 5 0 (hm 1 (by decide)) (hm 5 (by decide))
      (hn 6 (by decide)) (hn 8 (by decide)) (hn 9 (by decide)) (by decide) (by omega) (by omega)
  have h69 : 3 ≤ (sem_W 10 D 6).card ∨ 3 ≤ (sem_W 10 D 9).card := by
    by_contra hc; push Not at hc
    exact pa_m1_gen h hD hpos 6 9 8 1 4 0 (hm 1 (by decide)) (hm 4 (by decide))
      (hn 6 (by decide)) (hn 9 (by decide)) (hn 8 (by decide)) (by decide) (by omega) (by omega)
  have h79 : 3 ≤ (sem_W 10 D 7).card ∨ 3 ≤ (sem_W 10 D 9).card := by
    by_contra hc; push Not at hc
    exact pa_m1_gen h hD hpos 7 9 2 5 4 0 (hm 5 (by decide)) (hm 4 (by decide))
      (hn 7 (by decide)) (hn 9 (by decide)) (hn 2 (by decide)) (by decide) (by omega) (by omega)
  by_cases h9 : 3 ≤ (sem_W 10 D 9).card
  · rcases h68 with h6 | h8
    · exact hnot33_pair h hD hB0 hctx 6 9 1 4 (hm 1 (by decide)) (hm 4 (by decide))
        (hn 6 (by decide)) (hn 9 (by decide)) (by decide) h6 h9
    · exact hnot33_diff_I h hD hB0 hctx 8 9 5 4 6 0 0 (hm 5 (by decide)) (hm 4 (by decide))
        (hn 6 (by decide)) (by decide) h8 h9
  · have h6 : 3 ≤ (sem_W 10 D 6).card := h69.resolve_right h9
    have h7 : 3 ≤ (sem_W 10 D 7).card := h79.resolve_right h9
    exact hnot33_via_deg2 h hD hB0 hctx 6 7 1 5 4 0 2 (hm 1 (by decide)) (hm 5 (by decide)) (hm 4 (by decide))
      (by decide) h6 h7

theorem elim_22_R1 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (hB : Bplus 10 D = (eligSet 10 D).card + 1) (hI : ineligSet 10 D = {0, 2, 6}) : False := by
  obtain ⟨pos, P, Q, hctx⟩ := pa_setup_one h hD hB
  have hpos := hctx.1
  have hm : ∀ v : Fin 10, v ∈ ({0, 2, 6} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({0, 2, 6} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hI ▸ hv
  have h58 : 3 ≤ (sem_W 10 D 5).card ∨ 3 ≤ (sem_W 10 D 8).card := by
    by_contra hc; push Not at hc
    exact pa_m1_gen h hD hpos 5 8 7 0 6 1 (hm 0 (by decide)) (hm 6 (by decide))
      (hn 5 (by decide)) (hn 8 (by decide)) (hn 7 (by decide)) (by decide) (by omega) (by omega)
  have h49 : 3 ≤ (sem_W 10 D 4).card ∨ 3 ≤ (sem_W 10 D 9).card := by
    by_contra hc; push Not at hc
    exact pa_m1_gen h hD hpos 4 9 3 0 6 1 (hm 0 (by decide)) (hm 6 (by decide))
      (hn 4 (by decide)) (hn 9 (by decide)) (hn 3 (by decide)) (by decide) (by omega) (by omega)
  have h57 : 3 ≤ (sem_W 10 D 5).card ∨ 3 ≤ (sem_W 10 D 7).card := by
    by_contra hc; push Not at hc
    exact pa_m1_gen h hD hpos 5 7 8 0 2 1 (hm 0 (by decide)) (hm 2 (by decide))
      (hn 5 (by decide)) (hn 7 (by decide)) (hn 8 (by decide)) (by decide) (by omega) (by omega)
  have h79 : 3 ≤ (sem_W 10 D 9).card ∨ 3 ≤ (sem_W 10 D 7).card := by
    by_contra hc; push Not at hc
    exact pa_m1_gen h hD hpos 9 7 4 6 2 1 (hm 6 (by decide)) (hm 2 (by decide))
      (hn 9 (by decide)) (hn 7 (by decide)) (hn 4 (by decide)) (by decide) (by omega) (by omega)
  rcases h58 with h5 | h8
  · rcases h49 with h4 | h9
    · rcases h79 with h9' | h7
      · exact hnot33_pair h hD hB0 hctx 4 9 0 6 (hm 0 (by decide)) (hm 6 (by decide))
          (hn 4 (by decide)) (hn 9 (by decide)) (by decide) h4 h9'
      · exact hnot33_pair h hD hB0 hctx 5 7 0 2 (hm 0 (by decide)) (hm 2 (by decide))
          (hn 5 (by decide)) (hn 7 (by decide)) (by decide) h5 h7
    · exact hnot33_via_deg2 h hD hB0 hctx 5 9 0 6 2 1 4 (hm 0 (by decide)) (hm 6 (by decide)) (hm 2 (by decide))
        (by decide) h5 h9
  · rcases h49 with h4 | h9
    · exact hnot33_via_deg2 h hD hB0 hctx 4 8 0 6 2 1 5 (hm 0 (by decide)) (hm 6 (by decide)) (hm 2 (by decide))
        (by decide) h4 h8
    · rcases h57 with h5 | h7
      · exact hnot33_pair h hD hB0 hctx 5 8 0 6 (hm 0 (by decide)) (hm 6 (by decide))
          (hn 5 (by decide)) (hn 8 (by decide)) (by decide) h5 h8
      · exact hnot33_pair h hD hB0 hctx 7 9 2 6 (hm 2 (by decide)) (hm 6 (by decide))
          (hn 7 (by decide)) (hn 9 (by decide)) (by decide) h7 h9

theorem elim_24_R1 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (hB : Bplus 10 D = (eligSet 10 D).card + 1) (hI : ineligSet 10 D = {2, 3, 6}) : False := by
  have hS := h.1
  have hC := sem_g10_comp hD
  obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g10_gr hS hC
  have hbp := sem_minBranch_pure hbm
  obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h hC
  have hR1 : (residualUnits 10 D br).card = 1 := by have := card_residual hS br hbp; omega
  obtain ⟨u0, hRu0⟩ := Finset.card_eq_one.1 hR1
  have hm : ∀ v : Fin 10, v ∈ ({2, 3, 6} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hI ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({2, 3, 6} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hI ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({2, 3, 6} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hI ▸ sem_mem_inelig.2 hc)
  have h8_3 := two_in_deg3 h hD hpos (hm 3 (by decide)) (hm 6 (by decide)) (u := 8) (v := 5) (by decide)
  have hru8 : ru D br 8 = {u0} := by
    have hcc := cc_le h hD br hbp 8
    have hsub : ru D br 8 ⊆ {u0} := by rw [← hRu0]; exact Finset.filter_subset _ _
    exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)
  have hW8_le3 : (sem_W 10 D 8).card ≤ 3 := by
    have := cc_le h hD br hbp 8; rw [hru8, Finset.card_singleton] at this; omega
  have hle2_of_nb : ∀ x : Fin 10, w3_bad 8 3 6 x = false → (sem_W 10 D x).card ≤ 2 := fun x hnb => by
    have hnot := w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 3 (by decide)) (hm 6 (by decide))
      (x := 8) (v := 5) (by decide) hru8 hnb
    have hrux : ru D br x = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
      exact hnot ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
    have := cc_le h hD br hbp x; rw [hrux, Finset.card_empty] at this; omega
  have hW2_4 : (sem_W 10 D 4).card ≤ 2 := hle2_of_nb 4 (by decide)
  have hW2_7 : (sem_W 10 D 7).card ≤ 2 := hle2_of_nb 7 (by decide)
  have hW2_5 : (sem_W 10 D 5).card ≤ 2 := hle2_of_nb 5 (by decide)
  have hW2_1 : (sem_W 10 D 1).card ≤ 2 := hle2_of_nb 1 (by decide)
  by_cases h9_3 : 3 ≤ (sem_W 10 D 9).card
  · have hru9 : ru D br 9 = {u0} := by
      have hcc := cc_le h hD br hbp 9
      have hsub : ru D br 9 ⊆ {u0} := by rw [← hRu0]; exact Finset.filter_subset _ _
      exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)
    have hW9_le3 : (sem_W 10 D 9).card ≤ 3 := by
      have := cc_le h hD br hbp 9; rw [hru9, Finset.card_singleton] at this; omega
    have hM9 : merges 10 D (carrierT 10 D {9}) = ∅ := by
      have := cc_le h hD br hbp 9; rw [hru9, Finset.card_singleton] at this; exact Finset.card_eq_zero.1 (by omega)
    obtain ⟨e5, he5_8, hbe5_5, hfe5, -⟩ := pa_ed h hD hpos (by decide : Adj 8 5)
    have hp3_8 := as_mem hpos (hm 3 (by decide)) (by decide : Adj 3 8)
    have hp6_8 := as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 8)
    have hW8_eq : sem_W 10 D 8 = {pos 3, pos 6, e5} := by
      have hp36 : pos 3 ≠ pos 6 := fun e => absurd (hpos.2 _ (hm 3 (by decide)) _ (hm 6 (by decide)) e) (by decide)
      have hp3e : pos 3 ≠ e5 := fun e => hn 5 (by decide) (hfe5 _ (hm 3 (by decide)) e.symm ▸ hm 3 (by decide))
      have hp6e : pos 6 ≠ e5 := fun e => hn 5 (by decide) (hfe5 _ (hm 6 (by decide)) e.symm ▸ hm 6 (by decide))
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl | rfl; exact hp3_8; exact hp6_8; exact he5_8
      · rw [Finset.card_insert_of_notMem (by simp [hp36, hp3e]), Finset.card_pair hp6e]; exact hW8_le3
    obtain ⟨hfull3, _⟩ := full_of_two_in_deg3 h hD hB0 hpos (hm 3 (by decide)) (hm 6 (by decide))
      (u := 8) (v := 5) (by decide) hW8_le3
    have hch3 := pos_chain_or h hD hB0 hpos (hm 3 (by decide)) (by decide : Adj 3 8) (fun p hp hne hsub => by
      rw [hW8_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hne rfl
      · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 6 (by decide))))) (by decide)
      · exact hn 5 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe5_5).2.1) ▸ hm 3 (by decide)))
    have hch6 := pos_chain_or h hD hB0 hpos (hm 6 (by decide)) (by decide : Adj 6 8) (fun p hp hne hsub => by
      rw [hW8_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 3 (by decide))))) (by decide)
      · exact hne rfl
      · exact hn 5 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe5_5).2.1) ▸ hm 6 (by decide)))

    obtain ⟨Z4, hZ4_4, hbZ4_0, hfZ4, -⟩ := pa_ed h hD hpos (by decide : Adj 4 0)
    have hZ4_ne3 : Z4 ≠ pos 3 := fun hh => hn 0 (by decide) (hfZ4 3 (hm 3 (by decide)) hh ▸ hm 3 (by decide))
    have hW4_eq : sem_W 10 D 4 = {pos 3, Z4} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hZ4_ne3.symm]; exact hW2_4)
      rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl; exact as_mem hpos (hm 3 (by decide)) (by decide : Adj 3 4); exact hZ4_4
    obtain ⟨Z7, hZ7_7, hbZ7_5, hfZ7, -⟩ := pa_ed h hD hpos (by decide : Adj 7 5)
    have hZ7_ne2 : Z7 ≠ pos 2 := fun hh => hn 5 (by decide) (hfZ7 2 (hm 2 (by decide)) hh ▸ hm 2 (by decide))
    have hW7_eq : sem_W 10 D 7 = {pos 2, Z7} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hZ7_ne2.symm]; exact hW2_7)
      rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl; exact as_mem hpos (hm 2 (by decide)) (by decide : Adj 2 7); exact hZ7_7
    have hch2 := pos_chain_or h hD hB0 hpos (hm 2 (by decide)) (by decide : Adj 2 7) (fun p hp hne hsub => by
      rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hne rfl
      · exact hn 5 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbZ7_5).2.1) ▸ hm 2 (by decide)))
    have hW1_eq : sem_W 10 D 1 = {pos 2, pos 6} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_)
        (by rw [Finset.card_pair (fun e => absurd (hpos.2 _ (hm 2 (by decide)) _ (hm 6 (by decide)) e) (by decide))]; exact hW2_1)
      rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl; exact as_mem hpos (hm 2 (by decide)) (by decide : Adj 2 1); exact as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 1)

    have hbZ4_9 : sem_bar Z4 ∈ sem_W 10 D 9 := by
      obtain ⟨e4, he4_9, hbe4_4, -, -⟩ := pa_ed h hD hpos (by decide : Adj 9 4)
      rw [hW4_eq, Finset.mem_insert, Finset.mem_singleton] at hbe4_4
      rcases hbe4_4 with h' | h'
      · exact absurd (as_priv hpos (hm 3 (by decide)) (by rw [← h', sem_bar_bar]; exact he4_9)) (by decide)
      · have : e4 = sem_bar Z4 := by simpa [sem_bar_bar] using congrArg sem_bar h'
        exact this ▸ he4_9
    have hbZ7_9 : sem_bar Z7 ∈ sem_W 10 D 9 := by
      obtain ⟨e7, he7_9, hbe7_7, -, -⟩ := pa_ed h hD hpos (by decide : Adj 9 7)
      rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at hbe7_7
      rcases hbe7_7 with h' | h'
      · exact absurd (as_priv hpos (hm 2 (by decide)) (by rw [← h', sem_bar_bar]; exact he7_9)) (by decide)
      · have : e7 = sem_bar Z7 := by simpa [sem_bar_bar] using congrArg sem_bar h'
        exact this ▸ he7_9
    have he5_9 : e5 ∈ sem_W 10 D 9 := by
      have hres89 : ∀ u ∈ residualUnits 10 D br, (8 : Fin 10) ∈ supp 10 D u.1 → (9 : Fin 10) ∈ supp 10 D u.1 := fun u hu _ => by
        have hu_eq : u = u0 := Finset.mem_singleton.1 (hRu0 ▸ hu)
        rw [hu_eq]
        exact (mem_ru.1 (hru9 ▸ Finset.mem_singleton_self u0)).2
      have hw89 : (8 : Fin 10) ∈ supp 10 D u0.1 ∧ (9 : Fin 10) ∈ supp 10 D u0.1 :=
        ⟨(mem_ru.1 (hru8 ▸ Finset.mem_singleton_self u0)).2, (mem_ru.1 (hru9 ▸ Finset.mem_singleton_self u0)).2⟩
      obtain ⟨e0, he0⟩ := ri_gen sem_g10_gr h hC br hbp (by decide : (8 : Fin 10) ≠ 9) (helig 8 (by decide)) hres89 hw89
      have h0eq : pos 3 = e0 := by
        by_contra hne; exact absurd (hfull3 9 (he0 _ hp3_8 hne)) (by decide)
      have h9in := he0 e5 he5_8 (fun hh => hn 5 (by decide) (hfe5 3 (hm 3 (by decide)) (hh.trans h0eq.symm) ▸ hm 3 (by decide)))
      exact zm_mem hS hM9 (sem_mem_W.1 he5_8).1 (sem_W_and hS he5_8) h9in
    have he5_ne_b7 : e5 ≠ sem_bar Z7 := fun hh => w_bar hS hbe5_5 (by rw [hh, sem_bar_bar]; exact hbZ7_5)
    have hbZ4_ne_p6 : sem_bar Z4 ≠ pos 6 := fun hh =>
      absurd (as_priv hpos (hm 6 (by decide)) (by rw [← hh, sem_bar_bar]; exact hZ4_4)) (by decide)
    have hbZ7_ne_p6 : sem_bar Z7 ≠ pos 6 := fun hh =>
      absurd (as_priv hpos (hm 6 (by decide)) (by rw [← hh, sem_bar_bar]; exact hZ7_7)) (by decide)
    have he5_eq : e5 = sem_bar Z4 := by
      by_contra hne
      have hp6_9 := as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 9)
      have hp6e5 : pos 6 ≠ e5 := fun e => hn 5 (by decide) (hfe5 _ (hm 6 (by decide)) e.symm ▸ hm 6 (by decide))
      have hW9' : sem_W 10 D 9 = {pos 6, e5, sem_bar Z4} := by
        symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with rfl | rfl | rfl; exact hp6_9; exact he5_9; exact hbZ4_9
        · rw [Finset.card_insert_of_notMem (by simp [hp6e5, hbZ4_ne_p6.symm]), Finset.card_pair hne]; exact hW9_le3
      obtain ⟨f, hf, h0n, h8n⟩ := g10_deg3_cover_free h hD (x := 9) (a := 0) (b := 8) (by decide) (by decide) (by decide) (by decide)
      rw [hW9', Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl | rfl
      · exact h8n (sem_mem_W.1 hp6_8).2.1
      · exact h8n (sem_mem_W.1 he5_8).2.1
      · exact h0n (sem_mem_W.1 hbZ4_0).2.1
    subst he5_eq
    have hZ4_5 : Z4 ∈ sem_W 10 D 5 := by simpa [sem_bar_bar] using hbe5_5
    have hZ4_ne_b7 : Z4 ≠ sem_bar Z7 := fun hh => w_bar hS hbZ4_9 (by simpa [sem_bar_bar] using hh ▸ hbZ7_9)
    have hW5_eq : sem_W 10 D 5 = {Z4, sem_bar Z7} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hZ4_ne_b7]; exact hW2_5)
      rw [Finset.mem_insert, Finset.mem_singleton] at hf; rcases hf with rfl | rfl; exact hZ4_5; exact hbZ7_5
    have hp6_9 := as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 9)
    have hW9_eq : sem_W 10 D 9 = {pos 6, sem_bar Z4, sem_bar Z7} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl | rfl; exact hp6_9; exact hbZ4_9; exact hbZ7_9
      · rw [Finset.card_insert_of_notMem (by simp [hbZ4_ne_p6.symm, hbZ7_ne_p6.symm]),
          Finset.card_pair he5_ne_b7]; exact hW9_le3
    have hZ4_val_59 : val D (sem_two (5 : Fin 10) (9 : Fin 10)) (10 + Z4.1) = true := by
      have hj4 := (sem_mem_W.1 hZ4_4).1; have ht4 := sem_W_and hS hZ4_4
      have h5s := val_mono hS (fun i => decide (i = 5)) (sem_two (5 : Fin 10) (9 : Fin 10))
        (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D Z4) (mem_supp.1 (sem_mem_W.1 hZ4_5).2.1)
      have h9s := val_mono hS (fun i => decide (i = 9)) (sem_two (5 : Fin 10) (9 : Fin 10))
        (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D (sem_bar Z4)) (mem_supp.1 (sem_mem_W.1 hbZ4_9).2.1)
      rw [val_gate hS _ Z4.1 hj4, ht4, gop_true]
      rcases hZeq : Z4 with ⟨j, s⟩; rw [hZeq] at h5s h9s
      cases s
      · rw [sb_src_false] at h5s; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at h9s; simp [h5s, h9s]
      · rw [sb_src_true] at h5s; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at h9s; simp [h5s, h9s]
    have hp3_val_59 : val D (sem_two (5 : Fin 10) (9 : Fin 10)) (src D (sem_bar (pos 3))) = true := by
      obtain ⟨e, he4, -, he59, hbe59⟩ := pa_ed_avoid_min h hD (u := 4) (v := 9) (a := 5) (b := 9)
        (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)
      rw [hW4_eq, Finset.mem_insert, Finset.mem_singleton] at he4
      rcases he4 with rfl | rfl
      · exact hbe59
      · rw [hZ4_val_59] at he59; exact Bool.noConfusion he59
    have hno_59_edge : ¬ G10Edge (sem_two (5 : Fin 10) (9 : Fin 10)) := by
      rw [g10Edge_iff_adj]; rintro ⟨p, q, hpq, hp', hq'⟩
      simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp' hq'
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
      · exact adj_irrefl _ hpq
      · exact absurd hpq (by decide)
      · exact absurd hpq (by decide)
      · exact adj_irrefl _ hpq
    have hfan_gt_Z4 : ∀ w, 10 + Z4.1 < w → (9 : Fin 10) ∉ supp 10 D w → 2 ≤ fanout D w → (br 1 = w ∨ br 7 = w) := by
      intro w hgt h9n hfw
      have hne_s := sem_bzero_branch hS hB0 hfw
      have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
        rw [unitsPlus, Finset.mem_filter, mem_units]
        exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), by show 0 + 1 < fanout D w; omega⟩, hne_s⟩
      have hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D br := by
        by_contra hnr
        have hmemR : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits 10 D br := Finset.mem_sdiff.2 ⟨hwu, hnr⟩
        rw [hRu0, Finset.mem_singleton] at hmemR
        have hwe : w = u0.1 := congrArg Sigma.fst hmemR
        rw [hwe] at h9n; exact h9n (mem_ru.1 (hru9 ▸ Finset.mem_singleton_self u0)).2
      obtain ⟨y, hyE, hyeq⟩ := Finset.mem_image.1 hwr
      have hby : br y = w := congrArg Sigma.fst hyeq
      fin_cases y
      · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE hbZ4_0)
      · exact Or.inl hby
      · exact absurd hyE (Finset.mem_sdiff.1 (hm 2 (by decide))).2
      · exact absurd hyE (Finset.mem_sdiff.1 (hm 3 (by decide))).2
      · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE hZ4_4)
      · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE hZ4_5)
      · exact absurd hyE (Finset.mem_sdiff.1 (hm 6 (by decide))).2
      · exact Or.inr hby
      · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE he5_8)
      · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE hbZ4_9)
    have hfan1_of_not9 : ∀ (g : ℕ), g < D.length → tag D g = true → (9 : Fin 10) ∉ supp 10 D (10 + g) →
        fanout D (10 + g) ≤ 1 := fun g hg ht h9n => by
      by_contra hf
      have hne_s := sem_bzero_branch hS hB0 (by omega : 2 ≤ fanout D (10 + g))
      have hwu : (⟨10 + g, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
        rw [unitsPlus, Finset.mem_filter, mem_units]
        exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := 10 + g) (by omega)), by show 0 + 1 < fanout D (10 + g); omega⟩, hne_s⟩
      have hwr : (⟨10 + g, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D br := by
        by_contra hnr
        have hmemR : (⟨10 + g, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits 10 D br := Finset.mem_sdiff.2 ⟨hwu, hnr⟩
        rw [hRu0, Finset.mem_singleton] at hmemR
        have hge : 10 + g = u0.1 := congrArg Sigma.fst hmemR
        rw [hge] at h9n; exact h9n (mem_ru.1 (hru9 ▸ Finset.mem_singleton_self u0)).2
      obtain ⟨y, hyE, hyeq⟩ := Finset.mem_image.1 hwr
      exact sem_minBranch_not_and h br hbm hyE hg ht (congrArg Sigma.fst hyeq)
    exact kill_4cycle_gate h hD hB0 br hbm hpos
      (Z := Z4) (Z' := Z7) (a1 := 4) (b1 := 8) (a2 := 5) (b2 := 9) (c := 7) (d := 5) (i0 := 3)
      (sem_mem_W.1 hZ4_4).1 (sem_W_and hS hZ4_4)
      (sem_mem_W.1 hZ7_7).1 (sem_W_and hS hZ7_7)
      (sem_mem_W.1 hZ4_4).2.1 (sem_mem_W.1 he5_8).2.1 (by decide)
      (sem_mem_W.1 hZ4_5).2.1 (sem_mem_W.1 hbZ4_9).2.1 (sem_mem_W.1 hZ4_5).2.2 (sem_mem_W.1 hbZ4_9).2.2
      (fun j s h5W h9W => by
        rw [hW5_eq, Finset.mem_insert, Finset.mem_singleton] at h5W
        rcases h5W with h5e | h5e
        · exact congrArg Prod.fst h5e
        · exfalso; have : (j, !s) = Z7 := by simpa [sem_bar, sem_bar_bar] using congrArg sem_bar h5e
          exact w_bar hS hbZ7_9 (by simpa [sem_bar_bar] using this ▸ h9W))
      (hm 3 (by decide)) (by decide) hch3.2.2 ((hpos.1 3 (hm 3 (by decide))).2.2.1 4 (by decide)) hp3_val_59
      (fun e he hv2 hv1 => by
        have hZ4_val_48 : val D (sem_two (4 : Fin 10) (8 : Fin 10)) (10 + Z4.1) = true := by
          have hj4 := (sem_mem_W.1 hZ4_4).1; have ht4 := sem_W_and hS hZ4_4
          have h4s := val_mono hS (fun i => decide (i = 4)) (sem_two (4 : Fin 10) (8 : Fin 10))
            (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D Z4) (mem_supp.1 (sem_mem_W.1 hZ4_4).2.1)
          have h8s := val_mono hS (fun i => decide (i = 8)) (sem_two (4 : Fin 10) (8 : Fin 10))
            (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D (sem_bar Z4)) (mem_supp.1 (sem_mem_W.1 he5_8).2.1)
          rw [val_gate hS _ Z4.1 hj4, ht4, gop_true]
          rcases hZeq : Z4 with ⟨j, s⟩; rw [hZeq] at h4s h8s
          cases s
          · rw [sb_src_false] at h4s; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at h8s; simp [h4s, h8s]
          · rw [sb_src_true] at h4s; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at h8s; simp [h4s, h8s]
        rcases he with he5 | he9
        · rw [hW5_eq, Finset.mem_insert, Finset.mem_singleton] at he5
          rcases he5 with rfl | rfl
          · rw [hZ4_val_48] at hv1; exact Bool.noConfusion hv1
          · rfl
        · rw [hW9_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at he9
          rcases he9 with rfl | rfl | rfl
          · exact absurd (hch6.2.2 _ hv2) hno_59_edge
          · rw [show (sem_bar Z4).1 = Z4.1 from rfl, hZ4_val_48] at hv1; exact Bool.noConfusion hv1
          · rfl)
      (fun w hgt _ _ h9n hfw => by
        rcases hfan_gt_Z4 w hgt h9n hfw with h1eq | h7eq
        · refine ⟨1, helig 1 (by decide), h1eq, fun e heW hev _ _ => ?_⟩
          rw [hW1_eq, Finset.mem_insert, Finset.mem_singleton] at heW
          rcases heW with rfl | rfl
          · exact absurd (hch2.2.2 _ hev) hno_59_edge
          · exact absurd (hch6.2.2 _ hev) hno_59_edge
        · refine ⟨7, helig 7 (by decide), h7eq, fun e heW hev _ _ => ?_⟩
          rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at heW
          rcases heW with rfl | rfl
          · exact absurd (hch2.2.2 _ hev) hno_59_edge
          · rfl)
      (fun w hgt4 hgt7 _ _ h9n hfw => by
        rcases hfan_gt_Z4 w hgt4 h9n hfw with h1eq | h7eq
        · refine ⟨1, helig 1 (by decide), h1eq, fun e heW hev _ _ => ?_⟩
          rw [hW1_eq, Finset.mem_insert, Finset.mem_singleton] at heW
          rcases heW with rfl | rfl
          · exact hno_59_edge (hch2.2.2 _ hev)
          · exact hno_59_edge (hch6.2.2 _ hev)
        · exact absurd (h7eq ▸ hgt7) (sem_minBranch_not_after h br hbm (helig 7 (by decide)) hZ7_7))
      (by decide : Adj 7 5)
      (fun j s h7W h5W => by
        rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at h7W
        rcases h7W with h7e | h7e
        · exfalso; exact absurd (as_priv hpos (hm 2 (by decide)) (by rw [← h7e]; exact h5W)) (by decide)
        · exact congrArg Prod.fst h7e)
      (fun h7in => absurd (hfull3 7 h7in) (by decide))
      (fun h5in => absurd (hfull3 5 h5in) (by decide))
      (hfan1_of_not9 Z4.1 (sem_mem_W.1 hZ4_4).1 (sem_W_and hS hZ4_4) (sem_mem_W.1 hbZ4_9).2.2)
      (hfan1_of_not9 Z7.1 (sem_mem_W.1 hZ7_7).1 (sem_W_and hS hZ7_7) (sem_mem_W.1 hbZ7_9).2.2)
  · exact pa_m1_gen h hD hpos 9 4 7 6 3 8 (hm 6 (by decide)) (hm 3 (by decide))
      (hn 9 (by decide)) (hn 4 (by decide)) (hn 7 (by decide)) (by decide) (by omega) hW2_4

def r1_wit (idx : Fin 44) :
    ℕ × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 × Fin 10 :=
  match idx.val with
  | 0 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 1 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 2 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 3 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 4 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 5 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 6 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 7 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 8 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 9 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 10 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 11 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 12 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 13 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 14 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 15 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 16 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 17 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 18 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 19 => (0, 7, 8, 2, 5, 9, 3, 5, 6, 1, 0, 0, 0)
  | 20 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 21 => (2, 7, 2, 5, 9, 6, 8, 9, 1, 5, 4, 0, 0)
  | 22 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 23 => (0, 8, 4, 6, 3, 5, 0, 3, 9, 1, 0, 0, 0)
  | 24 => (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
  | 25 => (2, 9, 4, 6, 7, 5, 7, 8, 0, 2, 6, 1, 1)
  | 26 => (0, 7, 8, 2, 5, 9, 5, 6, 3, 1, 0, 0, 0)
  | 27 => (1, 8, 3, 5, 6, 9, 4, 7, 6, 3, 8, 0, 0)
  | 28 => (0, 8, 9, 5, 6, 3, 4, 6, 7, 0, 0, 0, 0)
  | 29 => (0, 9, 5, 6, 7, 4, 0, 7, 8, 1, 0, 0, 0)
  | 30 => (1, 9, 4, 6, 7, 8, 5, 3, 6, 7, 2, 0, 0)
  | 31 => (0, 4, 6, 0, 9, 3, 1, 9, 8, 5, 0, 0, 0)
  | 32 => (0, 7, 4, 2, 9, 5, 0, 9, 3, 1, 0, 0, 0)
  | 33 => (1, 4, 0, 9, 3, 8, 5, 6, 3, 0, 4, 0, 0)
  | 34 => (0, 7, 6, 5, 9, 2, 1, 9, 8, 0, 0, 0, 0)
  | 35 => (1, 7, 2, 5, 9, 8, 6, 3, 5, 9, 7, 0, 0)
  | 36 => (0, 4, 7, 3, 9, 0, 5, 9, 2, 8, 0, 0, 0)
  | 37 => (0, 8, 4, 6, 3, 5, 0, 3, 9, 1, 0, 0, 0)
  | 38 => (0, 7, 8, 2, 5, 9, 3, 5, 6, 1, 0, 0, 0)
  | 39 => (0, 7, 8, 2, 5, 9, 5, 6, 3, 1, 0, 0, 0)
  | 40 => (0, 4, 9, 0, 3, 9, 6, 7, 4, 5, 0, 0, 0)
  | 41 => (0, 4, 6, 0, 3, 9, 1, 9, 8, 5, 0, 0, 0)
  | 42 => (0, 4, 7, 3, 9, 0, 5, 9, 2, 8, 0, 0, 0)
  | _ => (0, 4, 7, 3, 9, 0, 2, 5, 9, 8, 0, 0, 0)

theorem r1_wit_ok0a : ∀ idx : Fin 44, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 17 → idx.val ≠ 18 → idx.val ≠ 20 → idx.val ≠ 22 → idx.val ≠ 24 → (r1_wit idx).1 = 0 →
    let I := hc_rep idx
    let (_, a1, a2, a3, a4, _, a6, a7, _, a9, _, _, _) := r1_wit idx
    a3 ∈ I ∧ a4 ∈ I ∧ a6 ∈ I ∧ a7 ∈ I ∧ a1 ≠ a2 ∧ a9 ≠ a1 ∧ hc_adjB a2 a9 = false ∧ (g10_nbB a1).card = 3 := by
  decide +kernel

theorem r1_wit_ok0b : ∀ idx : Fin 44, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 17 → idx.val ≠ 18 → idx.val ≠ 20 → idx.val ≠ 22 → idx.val ≠ 24 → (r1_wit idx).1 = 0 →
    let (_, a1, _, a3, a4, a5, _, _, _, _, _, _, _) := r1_wit idx
    a3 ≠ a4 ∧ hc_adjB a3 a1 = true ∧ hc_adjB a4 a1 = true ∧ hc_adjB a1 a5 = true ∧ a5 ≠ a3 ∧ a5 ≠ a4 := by
  decide +kernel

theorem r1_wit_ok0c : ∀ idx : Fin 44, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 17 → idx.val ≠ 18 → idx.val ≠ 20 → idx.val ≠ 22 → idx.val ≠ 24 → (r1_wit idx).1 = 0 →
    let (_, _, a2, a3, _, _, a6, a7, a8, a9, _, _, _) := r1_wit idx
    a6 ≠ a7 ∧ hc_adjB a6 a2 = true ∧ hc_adjB a7 a2 = true ∧ hc_adjB a2 a8 = true ∧ a8 ≠ a6 ∧ a8 ≠ a7 ∧
    hc_adjB a3 a2 = false ∧ hc_adjB a3 a9 = true := by
  decide +kernel

theorem r1_wit_ok1a : ∀ idx : Fin 44, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 17 → idx.val ≠ 18 → idx.val ≠ 20 → idx.val ≠ 22 → idx.val ≠ 24 → (r1_wit idx).1 = 1 →
    let I := hc_rep idx
    let (_, a1, a2, a3, a4, _, _, _, _, _, _, _, _) := r1_wit idx
    I.card = 3 ∧ a2 ∈ I ∧ a3 ∈ I ∧ (g10_nbB a1).card = 3 ∧ a2 ≠ a3 ∧
    hc_adjB a2 a1 = true ∧ hc_adjB a3 a1 = true ∧ hc_adjB a1 a4 = true ∧ a4 ≠ a2 ∧ a4 ≠ a3 := by
  decide +kernel

theorem r1_wit_ok1b : ∀ idx : Fin 44, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 17 → idx.val ≠ 18 → idx.val ≠ 20 → idx.val ≠ 22 → idx.val ≠ 24 → (r1_wit idx).1 = 1 →
    let I := hc_rep idx
    let (_, a1, a2, a3, _, a5, a6, a7, a8, a9, a10, _, _) := r1_wit idx
    (a8 ∈ I ∧ a9 ∈ I ∧ a5 ∉ I ∧ a6 ∉ I ∧ a7 ∉ I ∧ w3_bad a1 a2 a3 a5 = false ∧ w3_bad a1 a2 a3 a6 = false) ∧
    (hc_adjB a8 a5 = true ∧ hc_adjB a9 a6 = true ∧ hc_adjB a5 a6 = true ∧
     hc_adjB a5 a7 = true ∧ a7 ≠ a6 ∧ (g10_nbB a6).card = 3 ∧
     hc_adjB a9 a10 = true ∧ a10 ≠ a6 ∧ hc_adjB a10 a7 = false) := by
  decide +kernel

theorem r1_wit_ok2a : ∀ idx : Fin 44, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 17 → idx.val ≠ 18 → idx.val ≠ 20 → idx.val ≠ 22 → idx.val ≠ 24 → (r1_wit idx).1 ≠ 0 → (r1_wit idx).1 ≠ 1 →
    let I := hc_rep idx
    let (_, a1, a2, a3, a4, _, _, _, _, _, _, _, _) := r1_wit idx
    I.card = 3 ∧ a2 ∈ I ∧ a3 ∈ I ∧ (g10_nbB a1).card = 3 ∧ a2 ≠ a3 ∧
    hc_adjB a2 a1 = true ∧ hc_adjB a3 a1 = true ∧ hc_adjB a1 a4 = true ∧ a4 ≠ a2 ∧ a4 ≠ a3 := by
  decide +kernel

theorem r1_wit_ok2b : ∀ idx : Fin 44, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 17 → idx.val ≠ 18 → idx.val ≠ 20 → idx.val ≠ 22 → idx.val ≠ 24 → (r1_wit idx).1 ≠ 0 → (r1_wit idx).1 ≠ 1 →
    let I := hc_rep idx
    let (_, a1, a2, a3, _, a5, a6, a7, _, a9, a10, _, _) := r1_wit idx
    a9 ∈ I ∧ a10 ∈ I ∧ a5 ∉ I ∧ w3_bad a1 a2 a3 a5 = false ∧ w3_bad a1 a2 a3 a6 = false ∧ w3_bad a1 a2 a3 a7 = false := by
  decide +kernel

theorem r1_wit_ok2c : ∀ idx : Fin 44, 3 ≤ (hc_rep idx).card →
    idx.val ≠ 17 → idx.val ≠ 18 → idx.val ≠ 20 → idx.val ≠ 22 → idx.val ≠ 24 → (r1_wit idx).1 ≠ 0 → (r1_wit idx).1 ≠ 1 →
    let (_, _, _, _, _, a5, a6, a7, a8, a9, a10, a11, a12) := r1_wit idx
    (hc_adjB a5 a6 = true ∧ hc_adjB a5 a7 = true ∧ hc_adjB a5 a8 = true ∧
     hc_adjB a9 a6 = true ∧ hc_adjB a10 a7 = true ∧ a6 ≠ a7 ∧ a8 ≠ a6 ∧ a8 ≠ a7 ∧
     (g10_nbB a6).card = 3 ∧ (g10_nbB a7).card = 3) ∧
    (hc_adjB a9 a11 = true ∧ a11 ≠ a6 ∧ hc_adjB a11 a7 = false ∧ hc_adjB a11 a8 = false ∧
     hc_adjB a10 a12 = true ∧ a12 ≠ a7 ∧ hc_adjB a12 a8 = false) := by
  decide +kernel

theorem elim_R1_all {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (h8 : totalSurplus 10 D ≤ 8) (hB : Bplus 10 D = (eligSet 10 D).card + 1)
    (idx : Fin 44) (hc : 3 ≤ (hc_rep idx).card) (hI : ineligSet 10 D = hc_rep idx) : False := by
  have hts := totalSurplus_split 10 D
  have hel := inelig_card_add 10 D
  by_cases h17 : idx.val = 17
  · have hIeq : ineligSet 10 D = {0, 1, 3} := by rw [hI, show idx = ⟨17, by decide⟩ from Fin.ext h17]; decide
    have hB0 : Bzero 10 D = 0 := by
      have : (ineligSet 10 D).card = 3 := by rw [hIeq]; decide
      omega
    exact elim_17_R1 h hD hB0 hB hIeq
  by_cases h18 : idx.val = 18
  · have hIeq : ineligSet 10 D = {1, 3, 5} := by rw [hI, show idx = ⟨18, by decide⟩ from Fin.ext h18]; decide
    have hB0 : Bzero 10 D = 0 := by
      have : (ineligSet 10 D).card = 3 := by rw [hIeq]; decide
      omega
    exact elim_18_R1 h hD hB0 hB hIeq
  by_cases h20 : idx.val = 20
  · have hIeq : ineligSet 10 D = {1, 4, 5} := by rw [hI, show idx = ⟨20, by decide⟩ from Fin.ext h20]; decide
    have hB0 : Bzero 10 D = 0 := by
      have : (ineligSet 10 D).card = 3 := by rw [hIeq]; decide
      omega
    exact elim_20_R1 h hD hB0 hB hIeq
  by_cases h22 : idx.val = 22
  · have hIeq : ineligSet 10 D = {0, 2, 6} := by rw [hI, show idx = ⟨22, by decide⟩ from Fin.ext h22]; decide
    have hB0 : Bzero 10 D = 0 := by
      have : (ineligSet 10 D).card = 3 := by rw [hIeq]; decide
      omega
    exact elim_22_R1 h hD hB0 hB hIeq
  by_cases h24 : idx.val = 24
  · have hIeq : ineligSet 10 D = {2, 3, 6} := by rw [hI, show idx = ⟨24, by decide⟩ from Fin.ext h24]; decide
    have hB0 : Bzero 10 D = 0 := by
      have : (ineligSet 10 D).card = 3 := by rw [hIeq]; decide
      omega
    exact elim_24_R1 h hD hB0 hB hIeq
  rcases hrw : r1_wit idx with ⟨k, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩
  by_cases hk0 : k = 0
  · have hwa := r1_wit_ok0a idx hc h17 h18 h20 h22 h24 (by rw [hrw]; exact hk0)
    have hwb := r1_wit_ok0b idx hc h17 h18 h20 h22 h24 (by rw [hrw]; exact hk0)
    have hwc := r1_wit_ok0c idx hc h17 h18 h20 h22 h24 (by rw [hrw]; exact hk0)
    rw [hrw] at hwa hwb hwc; dsimp only at hwa hwb hwc
    obtain ⟨hi1, hi2, hj1, hj2, hxy, hqx, hnyq, hdx⟩ := hwa
    obtain ⟨h12', hx1, hx2, hxv, hv1, hv2⟩ := hwb
    obtain ⟨hj12, hy1, hy2, hyv, hvy1, hvy2, hni1y, hq1⟩ := hwc
    obtain ⟨pos, P, Q, hctx⟩ := pa_setup_one h hD hB
    exact two_w3_R1_kill h hD hctx (hI ▸ hi1) (hI ▸ hi2) (hI ▸ hj1) (hI ▸ hj2)
      ⟨hxy, hqx, hnyq, hdx, h12', hx1, hx2, hxv, hv1, hv2, hj12, hy1, hy2, hyv, hvy1, hvy2, hni1y, hq1⟩
  · by_cases hk1 : k = 1
    · have hwa := r1_wit_ok1a idx hc h17 h18 h20 h22 h24 (by rw [hrw]; exact hk1)
      have hwb := r1_wit_ok1b idx hc h17 h18 h20 h22 h24 (by rw [hrw]; exact hk1)
      rw [hrw] at hwa hwb; dsimp only at hwa hwb
      obtain ⟨hc3, hi1, hi2, hda, h12', ha1, ha2, hav, hv1, hv2⟩ := hwa
      obtain ⟨⟨hiz, hik, hnz, hnk, hnv, hza, hka⟩, hg⟩ := hwb
      have hB0 : Bzero 10 D = 0 := by rw [hI, hc3] at hel; omega
      obtain ⟨b, hb⟩ := sem_exists_minBranch sem_g10_gr h.1 (sem_g10_comp hD)
      have hbp := sem_minBranch_pure hb
      obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h (sem_g10_comp hD)
      have hR1 : (residualUnits 10 D b).card = 1 := by have := card_residual h.1 b hbp; omega
      obtain ⟨u0, hRu0⟩ := Finset.card_eq_one.1 hR1
      have ha3 := two_in_deg3 h hD hpos (hI ▸ hi1) (hI ▸ hi2) ⟨h12', ha1, ha2, hav, hv1, hv2⟩
      have hrua : ru D b a1 = {u0} := by
        have hcc := cc_le h hD b hbp a1
        have hsub1 : ru D b a1 ⊆ {u0} := by rw [← hRu0]; exact Finset.filter_subset _ _
        exact Finset.eq_of_subset_of_card_le hsub1 (by rw [Finset.card_singleton]; omega)
      have hle2 : ∀ x : Fin 10, w3_bad a1 a2 a3 x = false → (sem_W 10 D x).card ≤ 2 := fun x hnb => by
        have hnot := w3_ru_one_not_mem h hD hB0 b hb hpos (hI ▸ hi1) (hI ▸ hi2)
          ⟨hda, h12', ha1, ha2, hav, hv1, hv2⟩ hrua hnb
        have hrux : ru D b x = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
          exact hnot ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
        have := cc_le h hD b hbp x; rw [hrux, Finset.card_empty] at this; omega
      exact pa_m1_gen h hD hpos a5 a6 a7 a8 a9 a10 (hI ▸ hiz) (hI ▸ hik) (hI ▸ hnz) (hI ▸ hnk) (hI ▸ hnv) hg
        (hle2 a5 hza) (hle2 a6 hka)
    · have hwa := r1_wit_ok2a idx hc h17 h18 h20 h22 h24 (by rw [hrw]; exact hk0) (by rw [hrw]; exact hk1)
      have hwb := r1_wit_ok2b idx hc h17 h18 h20 h22 h24 (by rw [hrw]; exact hk0) (by rw [hrw]; exact hk1)
      have hwc := r1_wit_ok2c idx hc h17 h18 h20 h22 h24 (by rw [hrw]; exact hk0) (by rw [hrw]; exact hk1)
      rw [hrw] at hwa hwb hwc; dsimp only at hwa hwb hwc
      obtain ⟨hc3, hi1, hi2, hda, h12', ha1, ha2, hav, hv1, hv2⟩ := hwa
      obtain ⟨hik1, hik2, hnu, hua, hk1a, hk2a⟩ := hwb
      obtain ⟨⟨g1, g2, g3, g4, g5, h67, h86, h87, hd6, hd7⟩,
        ⟨g6, h116, h117, h118, g7, h127, h128⟩⟩ := hwc
      have hB0 : Bzero 10 D = 0 := by rw [hI, hc3] at hel; omega
      obtain ⟨b, hb⟩ := sem_exists_minBranch sem_g10_gr h.1 (sem_g10_comp hD)
      have hbp := sem_minBranch_pure hb
      obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h (sem_g10_comp hD)
      have hR1 : (residualUnits 10 D b).card = 1 := by have := card_residual h.1 b hbp; omega
      obtain ⟨u0, hRu0⟩ := Finset.card_eq_one.1 hR1
      have ha3 := two_in_deg3 h hD hpos (hI ▸ hi1) (hI ▸ hi2) ⟨h12', ha1, ha2, hav, hv1, hv2⟩
      have hrua : ru D b a1 = {u0} := by
        have hcc := cc_le h hD b hbp a1
        have hsub1 : ru D b a1 ⊆ {u0} := by rw [← hRu0]; exact Finset.filter_subset _ _
        exact Finset.eq_of_subset_of_card_le hsub1 (by rw [Finset.card_singleton]; omega)
      have hle2 : ∀ x : Fin 10, w3_bad a1 a2 a3 x = false → (sem_W 10 D x).card ≤ 2 := fun x hnb => by
        have hnot := w3_ru_one_not_mem h hD hB0 b hb hpos (hI ▸ hi1) (hI ▸ hi2)
          ⟨hda, h12', ha1, ha2, hav, hv1, hv2⟩ hrua hnb
        have hrux : ru D b x = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
          exact hnot ((Finset.mem_singleton.1 (hRu0 ▸ (mem_ru.1 hu).1)) ▸ (mem_ru.1 hu).2)
        have := cc_le h hD b hbp x; rw [hrux, Finset.card_empty] at this; omega
      exact ps_3star_gen h hD hpos a5 a6 a7 a8 a9 a10 a11 a12 (hI ▸ hik1) (hI ▸ hik2) (hI ▸ hnu)
        ⟨g1, g2, g3, g4, g5, h67, h86, h87, hd6, hd7, g6, h116, h117, h118, g7, h127, h128⟩
        (hle2 a5 hua) (hle2 a6 hk1a) (hle2 a7 hk2a)

theorem mem_W_of_pos {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {j t : Fin 10} (hj : j ∈ ineligSet 10 D) (ht : t ∈ supp 10 D (src D (pos j))) :
    pos j ∈ sem_W 10 D t := by
  obtain ⟨h1, h2, -, -⟩ := hpos.1 j hj
  exact sem_mem_W.2 ⟨h1, ht, by rw [h2]; exact Finset.notMem_empty t⟩

theorem pe_co_g10 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (b : Fin 10 → ℕ)
    (hb : PureBranch 10 D b) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    {v t j q : Fin 10} (hj : j ∈ ineligSet 10 D) (hv : v ∈ eligSet 10 D)
    (hres : ∀ u ∈ residualUnits 10 D b, v ∈ supp 10 D u.1 → t ∈ supp 10 D u.1)
    {w : ℕ} (hw : v ∈ supp 10 D w ∧ t ∈ supp 10 D w)
    (hg : (g10_nbB v).card = 3 ∧ hc_adjB j v = true ∧ hc_adjB j q = true ∧
      v ≠ t ∧ v ≠ q ∧ hc_adjB t q = false) :
    t ∈ supp 10 D (src D (pos j)) := by
  obtain ⟨hdv, hjv, hjq, hvt, hvq, htq⟩ := hg
  rw [hc_adjB_iff] at hjv hjq
  obtain ⟨e0, he0⟩ := ri_gen sem_g10_gr h (sem_g10_comp hD) b hb hvt hv hres hw
  by_contra hn
  have h0 : pos j = e0 := by
    by_contra hne
    exact hn (he0 _ (as_mem hpos hj hjv) hne)
  obtain ⟨e, he, h1, h2⟩ := g10_deg3_cover_free h hD hdv hvt hvq (sem_adjB_false.1 htq)
  exact h1 (he0 e he (fun hee => h2 (by rw [hee, ← h0]; exact (hpos.1 j hj).2.2.1 q hjq)))

theorem pe_co_blow5 {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (br : Fin 10 → ℕ) (hbr : PureBranch 10 D br) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos)
    (a b a1 a2 qa1 qa2 b1 b2 vb : Fin 10)
    (ha : a ∈ eligSet 10 D) (ha1 : a1 ∈ ineligSet 10 D) (ha2 : a2 ∈ ineligSet 10 D)
    (hb1 : b1 ∈ ineligSet 10 D) (hb2 : b2 ∈ ineligSet 10 D)
    (hvb : vb ∉ ineligSet 10 D)
    (hg : a ≠ b ∧ a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 ∧
      (g10_nbB a).card = 3 ∧ hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧
      hc_adjB a1 qa1 = true ∧ a ≠ qa1 ∧ hc_adjB b qa1 = false ∧
      hc_adjB a2 qa2 = true ∧ a ≠ qa2 ∧ hc_adjB b qa2 = false ∧
      hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b vb = true)
    (hAn : 1 ≤ (ru D br a).card) (hsub : ru D br a ⊆ ru D br b) (hBle : (ru D br b).card ≤ 2) :
    False := by
  obtain ⟨hab, ha12, ha1b1, ha1b2, ha2b1, ha2b2, hb12, hda, ga1, ga2,
    gqa1, haqa1, gbqa1, gqa2, haqa2, gbqa2, gb1, gb2, gvb⟩ := hg
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (ru D br a).card)
  have hres : ∀ u' ∈ residualUnits 10 D br, a ∈ supp 10 D u'.1 → b ∈ supp 10 D u'.1 :=
    fun u' hu' ha' => (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hu', ha'⟩))).2
  have hw : a ∈ supp 10 D u.1 ∧ b ∈ supp 10 D u.1 :=
    ⟨(Finset.mem_filter.1 hu).2, (Finset.mem_filter.1 (hsub hu)).2⟩
  have hm1 := mem_W_of_pos hpos ha1 (pe_co_g10 h hD br hbr hpos ha1 ha hres hw ⟨hda, ga1, gqa1, hab, haqa1, gbqa1⟩)
  have hm2 := mem_W_of_pos hpos ha2 (pe_co_g10 h hD br hbr hpos ha2 ha hres hw ⟨hda, ga2, gqa2, hab, haqa2, gbqa2⟩)
  have hb1m := as_mem hpos hb1 ((hc_adjB_iff _ _).1 gb1)
  have hb2m := as_mem hpos hb2 ((hc_adjB_iff _ _).1 gb2)
  obtain ⟨ev, hev, -, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvb)
  have h5 := pa_card5 hm1 hm2 hb1m hb2m hev
    (fun e => ha12 (hpos.2 _ ha1 _ ha2 e))
    (fun e => ha1b1 (hpos.2 _ ha1 _ hb1 e))
    (fun e => ha1b2 (hpos.2 _ ha1 _ hb2 e))
    (fun e => hvb (hfv _ ha1 e.symm ▸ ha1))
    (fun e => ha2b1 (hpos.2 _ ha2 _ hb1 e))
    (fun e => ha2b2 (hpos.2 _ ha2 _ hb2 e))
    (fun e => hvb (hfv _ ha2 e.symm ▸ ha2))
    (fun e => hb12 (hpos.2 _ hb1 _ hb2 e))
    (fun e => hvb (hfv _ hb1 e.symm ▸ hb1))
    (fun e => hvb (hfv _ hb2 e.symm ▸ hb2))
  have hc4 := cc_le h hD br hbr b
  omega

theorem w3_res2_dichotomy {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (br : Fin 10 → ℕ) (hbm : sem_MinBranch 10 D br) {pos : Fin 10 → ℕ × Bool}
    (hpos : k4_Pos 10 G10 D pos) (hR2 : (residualUnits 10 D br).card = 2)
    (a b a1 a2 va b1 b2 vb : Fin 10)
    (ha1 : a1 ∈ ineligSet 10 D) (ha2 : a2 ∈ ineligSet 10 D)
    (hb1 : b1 ∈ ineligSet 10 D) (hb2 : b2 ∈ ineligSet 10 D)
    (hga : (g10_nbB a).card = 3 ∧ a1 ≠ a2 ∧ hc_adjB a1 a = true ∧ hc_adjB a2 a = true ∧ hc_adjB a va = true ∧ va ≠ a1 ∧ va ≠ a2)
    (hgb : (g10_nbB b).card = 3 ∧ b1 ≠ b2 ∧ hc_adjB b1 b = true ∧ hc_adjB b2 b = true ∧ hc_adjB b vb = true ∧ vb ≠ b1 ∧ vb ≠ b2)
    (hab_ok : w3_bad a a1 a2 b = false) (hba_ok : w3_bad b b1 b2 a = false) :
    (ru D br a = residualUnits 10 D br ∧ ru D br b = residualUnits 10 D br) ∨
    (∀ x : Fin 10, w3_bad a a1 a2 x = false → w3_bad b b1 b2 x = false → (sem_W 10 D x).card ≤ 2) := by
  have hbr := sem_minBranch_pure hbm
  obtain ⟨u1, u2, hu12, hReq⟩ := Finset.card_eq_two.1 hR2
  have ha3 := two_in_deg3 h hD hpos ha1 ha2 hga.2
  have hb3 := two_in_deg3 h hD hpos hb1 hb2 hgb.2
  have hnea : (ru D br a).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr a; omega)
  have hneb : (ru D br b).Nonempty := Finset.card_pos.1 (by have := cc_le h hD br hbr b; omega)
  have hlea : (ru D br a).card ≤ 2 := by
    have := Finset.card_le_card (Finset.filter_subset (fun u => a ∈ supp 10 D u.1) (residualUnits 10 D br)); unfold ru; omega
  have hleb : (ru D br b).card ≤ 2 := by
    have := Finset.card_le_card (Finset.filter_subset (fun u => b ∈ supp 10 D u.1) (residualUnits 10 D br)); unfold ru; omega
  by_cases ha1c : (ru D br a).card = 1
  · right
    obtain ⟨ua, hua⟩ := Finset.card_eq_one.1 ha1c
    have hua_not_b : ua ∉ ru D br b := fun hm =>
      w3_ru_one_not_mem h hD hB0 br hbm hpos ha1 ha2 hga hua hab_ok (mem_ru.1 hm).2
    have hsub_b : ru D br b ⊆ (residualUnits 10 D br).erase ua := fun u hu =>
      Finset.mem_erase.2 ⟨fun heq => hua_not_b (heq ▸ hu), (mem_ru.1 hu).1⟩
    have hua_in_R : ua ∈ residualUnits 10 D br := (mem_ru.1 (hua ▸ Finset.mem_singleton_self ua)).1
    have herb : ((residualUnits 10 D br).erase ua).card = 1 := by
      rw [Finset.card_erase_of_mem hua_in_R, hR2]
    have hb1c : (ru D br b).card = 1 := by
      have := Finset.card_le_card hsub_b; have := Finset.card_pos.2 hneb; omega
    obtain ⟨ub, hub⟩ := Finset.card_eq_one.1 hb1c
    have hub_in_R : ub ∈ residualUnits 10 D br := (mem_ru.1 (hub ▸ Finset.mem_singleton_self ub)).1
    have huab : ua ≠ ub := fun heq => hua_not_b (heq ▸ hub ▸ Finset.mem_singleton_self ub)
    have hReq2 : residualUnits 10 D br = {ua, ub} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) (by rw [Finset.card_pair huab, hR2])
      rw [Finset.mem_insert, Finset.mem_singleton] at hu; rcases hu with rfl | rfl; exact hua_in_R; exact hub_in_R
    intro x hxa hxb
    have hrux : ru D br x = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
      have huR := (mem_ru.1 hu).1
      rw [hReq2, Finset.mem_insert, Finset.mem_singleton] at huR
      rcases huR with rfl | rfl
      · exact w3_ru_one_not_mem h hD hB0 br hbm hpos ha1 ha2 hga hua hxa (mem_ru.1 hu).2
      · exact w3_ru_one_not_mem h hD hB0 br hbm hpos hb1 hb2 hgb hub hxb (mem_ru.1 hu).2
    have := cc_le h hD br hbr x; rw [hrux, Finset.card_empty] at this; omega
  · by_cases hb1c : (ru D br b).card = 1
    · right
      obtain ⟨ub, hub⟩ := Finset.card_eq_one.1 hb1c
      have hub_not_a : ub ∉ ru D br a := fun hm =>
        w3_ru_one_not_mem h hD hB0 br hbm hpos hb1 hb2 hgb hub hba_ok (mem_ru.1 hm).2
      have hub_in_R : ub ∈ residualUnits 10 D br := (mem_ru.1 (hub ▸ Finset.mem_singleton_self ub)).1
      have hsub_a : ru D br a ⊆ (residualUnits 10 D br).erase ub := fun u hu =>
        Finset.mem_erase.2 ⟨fun heq => hub_not_a (heq ▸ hu), (mem_ru.1 hu).1⟩
      have hera : ((residualUnits 10 D br).erase ub).card = 1 := by
        rw [Finset.card_erase_of_mem hub_in_R, hR2]
      have := Finset.card_le_card hsub_a; have := Finset.card_pos.2 hnea; omega
    · left
      have ha2c : (ru D br a).card = 2 := by have := Finset.card_pos.2 hnea; omega
      have hb2c : (ru D br b).card = 2 := by have := Finset.card_pos.2 hneb; omega
      exact ⟨Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hR2, ha2c]),
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hR2, hb2c])⟩

theorem shared_w3_bothR {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (hB0 : Bzero 10 D = 0)
    (br : Fin 10 → ℕ) (hbr : PureBranch 10 D br) {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 G10 D pos)
    (hR2 : (residualUnits 10 D br).card = 2)
    (a b i0 ia ib vb qa qb : Fin 10)
    (ha : a ∈ eligSet 10 D) (hb : b ∈ eligSet 10 D)
    (hi0 : i0 ∈ ineligSet 10 D) (hia : ia ∈ ineligSet 10 D) (hib : ib ∈ ineligSet 10 D)
    (hvb : vb ∉ ineligSet 10 D)
    (hg : a ≠ b ∧ i0 ≠ ia ∧ i0 ≠ ib ∧ ia ≠ ib ∧
          (g10_nbB a).card = 3 ∧ (g10_nbB b).card = 3 ∧
          hc_adjB i0 a = true ∧ hc_adjB ia a = true ∧
          hc_adjB i0 b = true ∧ hc_adjB ib b = true ∧ hc_adjB b vb = true ∧
          hc_adjB ia qa = true ∧ a ≠ qa ∧ hc_adjB b qa = false ∧
          hc_adjB ib qb = true ∧ b ≠ qb ∧ hc_adjB a qb = false ∧ hc_adjB ib a = false)
    (hruA : ru D br a = residualUnits 10 D br) (hruB : ru D br b = residualUnits 10 D br) : False := by
  obtain ⟨hab, h0a, h0b, habi, hda, hdb, g0a, gaa, g0b, gbb, gvb, gqa, haqa, gbqa, gqb, hbqb, gaqb, gnba⟩ := hg
  obtain ⟨u, hu⟩ := Finset.card_pos.1 (by omega : 0 < (residualUnits 10 D br).card)
  have hres1 : ∀ u' ∈ residualUnits 10 D br, a ∈ supp 10 D u'.1 → b ∈ supp 10 D u'.1 :=
    fun u' hu' _ => (mem_ru.1 (hruB ▸ hu')).2
  have hres2 : ∀ u' ∈ residualUnits 10 D br, b ∈ supp 10 D u'.1 → a ∈ supp 10 D u'.1 :=
    fun u' hu' _ => (mem_ru.1 (hruA ▸ hu')).2
  have hw : a ∈ supp 10 D u.1 ∧ b ∈ supp 10 D u.1 :=
    ⟨(mem_ru.1 (hruA ▸ hu)).2, (mem_ru.1 (hruB ▸ hu)).2⟩
  have hpa_in_b := mem_W_of_pos hpos hia (pe_co_g10 h hD br hbr hpos hia ha hres1 hw ⟨hda, gaa, gqa, hab, haqa, gbqa⟩)
  have ha_in_pb := pe_co_g10 h hD br hbr hpos hib hb hres2 ⟨hw.2, hw.1⟩ ⟨hdb, gbb, gqb, hab.symm, hbqb, gaqb⟩
  have hp0_in_b := as_mem hpos hi0 ((hc_adjB_iff _ _).1 g0b)
  have hpb_in_b := as_mem hpos hib ((hc_adjB_iff _ _).1 gbb)
  obtain ⟨ev, hev, hbev, hfv, -⟩ := pa_ed h hD hpos ((hc_adjB_iff _ _).1 gvb)
  have hWb_le4 : (sem_W 10 D b).card ≤ 4 := by have := cc_le h hD br hbr b; rw [hruB, hR2] at this; omega
  have hWb := pa_four hpb_in_b hp0_in_b hpa_in_b hev
    (fun e => h0b.symm (hpos.2 _ hib _ hi0 e))
    (fun e => habi.symm (hpos.2 _ hib _ hia e))
    (fun e => hvb (hfv _ hib e.symm ▸ hib))
    (fun e => h0a (hpos.2 _ hi0 _ hia e))
    (fun e => hvb (hfv _ hi0 e.symm ▸ hi0))
    (fun e => hvb (hfv _ hia e.symm ▸ hia))
    hWb_le4
  have hfull := full_g10 h hD hB0 hpos hib ((hc_adjB_iff _ _).1 gbb) (fun p hp hne1 hsub' => by
    rcases hWb p hp with rfl | rfl | rfl | rfl
    · exact hne1 rfl
    · exact h0b (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hi0)))
    · exact habi (Finset.mem_singleton.1 (hsub' (pos_bar_mem hpos hia)))
    · exact hvb (Finset.mem_singleton.1 (hsub' (sem_mem_W.1 hbev).2.1) ▸ hib))
  exact sem_adjB_false.1 gnba ((hfull a).1 ha_in_pb)

theorem res2_setup {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h8 : totalSurplus 10 D ≤ 8)
    (idx : Fin 44) (hc4 : (hc_rep idx).card = 4) (hI : ineligSet 10 D = hc_rep idx) :
    Bzero 10 D = 0 ∧ ∃ br, sem_MinBranch 10 D br ∧ (residualUnits 10 D br).card = 2 ∧
      ∃ pos, k4_Pos 10 G10 D pos := by
  have hts := totalSurplus_split 10 D
  have hel := inelig_card_add 10 D
  have hE6 : (eligSet 10 D).card = 6 := by rw [hI, hc4] at hel; omega
  by_cases hB6 : Bplus 10 D ≤ 6
  · exact absurd (elim_R0_all h hD h8 (by omega) idx hI) id
  · by_cases hB7 : Bplus 10 D = 7
    · exact absurd (elim_R1_all h hD h8 (by omega) idx (by omega) hI) id
    · have hB8 : Bplus 10 D = 8 := by omega
      have hB0 : Bzero 10 D = 0 := by omega
      obtain ⟨br, hbm⟩ := sem_exists_minBranch sem_g10_gr h.1 (sem_g10_comp hD)
      have hR2 : (residualUnits 10 D br).card = 2 := by have := card_residual h.1 br (sem_minBranch_pure hbm); omega
      obtain ⟨pos, hpos⟩ := k4_assigned sem_g10_gr h (sem_g10_comp hD)
      exact ⟨hB0, br, hbm, hR2, pos, hpos⟩

theorem elim_37 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h8 : totalSurplus 10 D ≤ 8)
    (hI : ineligSet 10 D = hc_rep ⟨37, by decide⟩) : False := by
  have hS := h.1
  have hC := sem_g10_comp hD
  have hIeq : ineligSet 10 D = {0, 2, 3, 6} := by rw [hI]; decide
  have hm : ∀ v : Fin 10, v ∈ ({0, 2, 3, 6} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({0, 2, 3, 6} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({0, 2, 3, 6} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, br, hbm, hR2, pos, hpos⟩ := res2_setup h hD h8 ⟨37, by decide⟩ (by decide) hI
  have hbr := sem_minBranch_pure hbm
  have h4_3 := two_in_deg3 h hD hpos (hm 0 (by decide)) (hm 3 (by decide)) (u := 4) (v := 9) (by decide)
  have h8_3 := two_in_deg3 h hD hpos (hm 3 (by decide)) (hm 6 (by decide)) (u := 8) (v := 5) (by decide)
  have hne4 : 1 ≤ (ru D br 4).card := by have := cc_le h hD br hbr 4; omega
  have hne8 : 1 ≤ (ru D br 8).card := by have := cc_le h hD br hbr 8; omega
  have hle4 : (ru D br 4).card ≤ 2 := by
    have := Finset.card_le_card (Finset.filter_subset (fun u => (4 : Fin 10) ∈ supp 10 D u.1) (residualUnits 10 D br)); unfold ru; omega
  have hle8 : (ru D br 8).card ≤ 2 := by
    have := Finset.card_le_card (Finset.filter_subset (fun u => (8 : Fin 10) ∈ supp 10 D u.1) (residualUnits 10 D br)); unfold ru; omega
  by_cases hru8_2 : (ru D br 8).card = 2
  · have hru8 : ru D br 8 = residualUnits 10 D br :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hR2, hru8_2])
    by_cases hru4_2 : (ru D br 4).card = 2
    · have hru4 : ru D br 4 = residualUnits 10 D br :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hR2, hru4_2])
      obtain ⟨u0, hu0⟩ := Finset.card_pos.1 (by omega : 0 < (residualUnits 10 D br).card)
      have hres84 : ∀ u' ∈ residualUnits 10 D br, (8 : Fin 10) ∈ supp 10 D u'.1 → (4 : Fin 10) ∈ supp 10 D u'.1 :=
        fun u' hu' _ => (mem_ru.1 (hru4 ▸ hu')).2
      have hw84 : (8 : Fin 10) ∈ supp 10 D u0.1 ∧ (4 : Fin 10) ∈ supp 10 D u0.1 :=
        ⟨(mem_ru.1 (hru8 ▸ hu0)).2, (mem_ru.1 (hru4 ▸ hu0)).2⟩
      have hp6_4 := mem_W_of_pos hpos (hm 6 (by decide))
        (pe_co_g10 h hD br hbr hpos (hm 6 (by decide)) (helig 8 (by decide)) hres84 hw84 (q := 1) (by decide))
      have hp0_4 := as_mem hpos (hm 0 (by decide)) (by decide : Adj 0 4)
      have hp3_4 := as_mem hpos (hm 3 (by decide)) (by decide : Adj 3 4)
      obtain ⟨e9, he9, hbe9, hf9, -⟩ := pa_ed h hD hpos (by decide : Adj 4 9)
      have hW4_le4 : (sem_W 10 D 4).card ≤ 4 := by have := cc_le h hD br hbr 4; rw [hru4, hR2] at this; omega
      have hW4 := pa_four hp0_4 hp3_4 hp6_4 he9
        (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 3 (by decide)) e) (by decide))
        (fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 6 (by decide)) e) (by decide))
        (fun e => hn 9 (by decide) (hf9 _ (hm 0 (by decide)) e.symm ▸ hm 0 (by decide)))
        (fun e => absurd (hpos.2 _ (hm 3 (by decide)) _ (hm 6 (by decide)) e) (by decide))
        (fun e => hn 9 (by decide) (hf9 _ (hm 3 (by decide)) e.symm ▸ hm 3 (by decide)))
        (fun e => hn 9 (by decide) (hf9 _ (hm 6 (by decide)) e.symm ▸ hm 6 (by decide)))
        hW4_le4
      have hfull0 := full_g10 h hD hB0 hpos (hm 0 (by decide)) (by decide : Adj 0 4) (fun p hp hne1 hsub => by
        rcases hW4 p hp with rfl | rfl | rfl | rfl
        · exact hne1 rfl
        · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 3 (by decide))))) (by decide)
        · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 6 (by decide))))) (by decide)
        · exact hn 9 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe9).2.1) ▸ hm 0 (by decide)))
      have h57 : 3 ≤ (sem_W 10 D 5).card ∨ 3 ≤ (sem_W 10 D 7).card := by
        by_contra hc; push Not at hc
        exact pa_m1_gen h hD hpos 5 7 8 0 2 1 (hm 0 (by decide)) (hm 2 (by decide))
          (hn 5 (by decide)) (hn 7 (by decide)) (hn 8 (by decide)) (by decide) (by omega) (by omega)
      rcases h57 with h5 | h7
      · obtain ⟨u, hu⟩ := Finset.card_pos.1 (by have := cc_le h hD br hbr 5; omega : 0 < (ru D br 5).card)
        have hres58 : ∀ u' ∈ residualUnits 10 D br, (5 : Fin 10) ∈ supp 10 D u'.1 → (8 : Fin 10) ∈ supp 10 D u'.1 :=
          fun u' hu' _ => (mem_ru.1 (hru8 ▸ hu')).2
        have h8_in0 := pe_co_g10 h hD br hbr hpos (hm 0 (by decide)) (helig 5 (by decide)) hres58
          ⟨(mem_ru.1 hu).2, (mem_ru.1 (hru8 ▸ (mem_ru.1 hu).1)).2⟩ (q := 4) (by decide)
        exact absurd ((hfull0 8).1 h8_in0) (by decide)
      · obtain ⟨u, hu⟩ := Finset.card_pos.1 (by have := cc_le h hD br hbr 7; omega : 0 < (ru D br 7).card)
        have hres74 : ∀ u' ∈ residualUnits 10 D br, (7 : Fin 10) ∈ supp 10 D u'.1 → (4 : Fin 10) ∈ supp 10 D u'.1 :=
          fun u' hu' _ => (mem_ru.1 (hru4 ▸ hu')).2
        have hp2_4 := mem_W_of_pos hpos (hm 2 (by decide))
          (pe_co_g10 h hD br hbr hpos (hm 2 (by decide)) (helig 7 (by decide)) hres74
            ⟨(mem_ru.1 hu).2, (mem_ru.1 (hru4 ▸ (mem_ru.1 hu).1)).2⟩ (q := 1) (by decide))
        rcases hW4 (pos 2) hp2_4 with e | e | e | e
        · exact absurd (hpos.2 _ (hm 2 (by decide)) _ (hm 0 (by decide)) e) (by decide)
        · exact absurd (hpos.2 _ (hm 2 (by decide)) _ (hm 3 (by decide)) e) (by decide)
        · exact absurd (hpos.2 _ (hm 2 (by decide)) _ (hm 6 (by decide)) e) (by decide)
        · exact hn 9 (by decide) (hf9 _ (hm 2 (by decide)) e.symm ▸ hm 2 (by decide))
    ·
      obtain ⟨u1, hru4⟩ := Finset.card_eq_one.1 (by omega : (ru D br 4).card = 1)
      have hu1R : u1 ∈ residualUnits 10 D br := (mem_ru.1 (hru4 ▸ Finset.mem_singleton_self u1)).1
      obtain ⟨u2, hu2eq⟩ := Finset.card_eq_one.1 (by rw [Finset.card_erase_of_mem hu1R, hR2] : ((residualUnits 10 D br).erase u1).card = 1)
      have hu2mem : u2 ∈ (residualUnits 10 D br).erase u1 := hu2eq ▸ Finset.mem_singleton_self u2
      have hu2ne1 : u2 ≠ u1 := (Finset.mem_erase.1 hu2mem).1
      have hu2R : u2 ∈ residualUnits 10 D br := (Finset.mem_erase.1 hu2mem).2
      have hReq : residualUnits 10 D br = {u1, u2} := by
        symm; refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) (by rw [Finset.card_pair hu2ne1.symm, hR2])
        rw [Finset.mem_insert, Finset.mem_singleton] at hu; rcases hu with rfl | rfl; exact hu1R; exact hu2R
      have hW4_le3 : (sem_W 10 D 4).card ≤ 3 := by
        have := cc_le h hD br hbr 4; rw [hru4, Finset.card_singleton] at this; omega
      obtain ⟨hfull0, hfull3⟩ := full_of_two_in_deg3 h hD hB0 hpos (hm 0 (by decide)) (hm 3 (by decide))
        (u := 4) (v := 9) (by decide) hW4_le3
      have h57 : 3 ≤ (sem_W 10 D 5).card ∨ 3 ≤ (sem_W 10 D 7).card := by
        by_contra hc; push Not at hc
        exact pa_m1_gen h hD hpos 5 7 8 0 2 1 (hm 0 (by decide)) (hm 2 (by decide))
          (hn 5 (by decide)) (hn 7 (by decide)) (hn 8 (by decide)) (by decide) (by omega) (by omega)
      rcases h57 with h5 | h7
      · obtain ⟨u, hu⟩ := Finset.card_pos.1 (by have := cc_le h hD br hbr 5; omega : 0 < (ru D br 5).card)
        have hres58 : ∀ u' ∈ residualUnits 10 D br, (5 : Fin 10) ∈ supp 10 D u'.1 → (8 : Fin 10) ∈ supp 10 D u'.1 :=
          fun u' hu' _ => (mem_ru.1 (hru8 ▸ hu')).2
        have h8_in0 := pe_co_g10 h hD br hbr hpos (hm 0 (by decide)) (helig 5 (by decide)) hres58
          ⟨(mem_ru.1 hu).2, (mem_ru.1 (hru8 ▸ (mem_ru.1 hu).1)).2⟩ (q := 4) (by decide)
        exact absurd (hfull0 8 h8_in0) (by decide)
      · have h7n1 : (7 : Fin 10) ∉ supp 10 D u1.1 :=
          w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 (by decide)
        have hru7 : ru D br 7 = {u2} := by
          have hsub : ru D br 7 ⊆ {u2} := fun u hu => by
            have huR := (mem_ru.1 hu).1; rw [hReq, Finset.mem_insert, Finset.mem_singleton] at huR
            rcases huR with rfl | rfl
            · exact absurd (mem_ru.1 hu).2 h7n1
            · exact Finset.mem_singleton_self _
          have := cc_le h hD br hbr 7
          exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)
        have hres78 : ∀ u' ∈ residualUnits 10 D br, (7 : Fin 10) ∈ supp 10 D u'.1 → (8 : Fin 10) ∈ supp 10 D u'.1 :=
          fun u' hu' _ => (mem_ru.1 (hru8 ▸ hu')).2
        have h8_in2 := pe_co_g10 h hD br hbr hpos (hm 2 (by decide)) (helig 7 (by decide)) hres78
          ⟨(mem_ru.1 (hru7 ▸ Finset.mem_singleton_self u2)).2, (mem_ru.1 (hru8 ▸ hu2R)).2⟩ (q := 1) (by decide)
        have hp2_8 := mem_W_of_pos hpos (hm 2 (by decide)) h8_in2
        have hp3_8 := as_mem hpos (hm 3 (by decide)) (by decide : Adj 3 8)
        have hp6_8 := as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 8)
        obtain ⟨e5, he5_8, hbe5_5, hfe5, -⟩ := pa_ed h hD hpos (by decide : Adj 8 5)
        have hW8_le4 : (sem_W 10 D 8).card ≤ 4 := by have := cc_le h hD br hbr 8; rw [hru8, hR2] at this; omega
        have hp36 : pos 3 ≠ pos 6 := fun e => absurd (hpos.2 _ (hm 3 (by decide)) _ (hm 6 (by decide)) e) (by decide)
        have hp32 : pos 3 ≠ pos 2 := fun e => absurd (hpos.2 _ (hm 3 (by decide)) _ (hm 2 (by decide)) e) (by decide)
        have hp3e : pos 3 ≠ e5 := fun e => hn 5 (by decide) (hfe5 _ (hm 3 (by decide)) e.symm ▸ hm 3 (by decide))
        have hp62 : pos 6 ≠ pos 2 := fun e => absurd (hpos.2 _ (hm 6 (by decide)) _ (hm 2 (by decide)) e) (by decide)
        have hp6e : pos 6 ≠ e5 := fun e => hn 5 (by decide) (hfe5 _ (hm 6 (by decide)) e.symm ▸ hm 6 (by decide))
        have hp2e : pos 2 ≠ e5 := fun e => hn 5 (by decide) (hfe5 _ (hm 2 (by decide)) e.symm ▸ hm 2 (by decide))
        have hW8 := pa_four hp3_8 hp6_8 hp2_8 he5_8 hp36 hp32 hp3e hp62 hp6e hp2e hW8_le4
        have hM8 : merges 10 D (carrierT 10 D {8}) = ∅ := by
          have hsub4 : ({pos 3, pos 6, pos 2, e5} : Finset (ℕ × Bool)) ⊆ sem_W 10 D 8 := fun f hf => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hf
            rcases hf with rfl | rfl | rfl | rfl; exact hp3_8; exact hp6_8; exact hp2_8; exact he5_8
          have hc4 : (({pos 3, pos 6, pos 2, e5} : Finset (ℕ × Bool))).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [hp36, hp32, hp3e]),
                Finset.card_insert_of_notMem (by simp [hp62, hp6e]),
                Finset.card_pair hp2e]
          have hge4 := hc4 ▸ Finset.card_le_card hsub4
          have := cc_le h hD br hbr 8; rw [hru8, hR2] at this; exact Finset.card_eq_zero.1 (by omega)
        have hfull6 := full_g10 h hD hB0 hpos (hm 6 (by decide)) (by decide : Adj 6 8) (fun p hp hne1 hsub => by
          rcases hW8 p hp with rfl | rfl | rfl | rfl
          · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 3 (by decide))))) (by decide)
          · exact hne1 rfl
          · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 2 (by decide))))) (by decide)
          · exact hn 5 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe5_5).2.1) ▸ hm 6 (by decide)))
        by_cases h1_3 : 3 ≤ (sem_W 10 D 1).card
        · have h1n1 : (1 : Fin 10) ∉ supp 10 D u1.1 :=
            w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 (by decide)
          have hru1 : ru D br 1 = {u2} := by
            have hsub : ru D br 1 ⊆ {u2} := fun u hu => by
              have huR := (mem_ru.1 hu).1; rw [hReq, Finset.mem_insert, Finset.mem_singleton] at huR
              rcases huR with rfl | rfl
              · exact absurd (mem_ru.1 hu).2 h1n1
              · exact Finset.mem_singleton_self _
            have := cc_le h hD br hbr 1
            exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)
          have hW1_le3 : (sem_W 10 D 1).card ≤ 3 := by
            have := cc_le h hD br hbr 1; rw [hru1, Finset.card_singleton] at this; omega
          have hM1 : merges 10 D (carrierT 10 D {1}) = ∅ := by
            have := cc_le h hD br hbr 1; rw [hru1, Finset.card_singleton] at this; exact Finset.card_eq_zero.1 (by omega)
          obtain ⟨e1, e2, he1W, he2W, he12, hs1, hs2⟩ := ru_one_two_supp h hD br hbm hM1 hru1
          have h7u2 : (7 : Fin 10) ∈ supp 10 D u2.1 := (mem_ru.1 (hru7 ▸ Finset.mem_singleton_self u2)).2
          have h8u2 : (8 : Fin 10) ∈ supp 10 D u2.1 := (mem_ru.1 (hru8 ▸ hu2R)).2
          have he1_ne6 : e1 ≠ pos 6 := fun hh => absurd ((hfull6 7).1 (hh ▸ hs1 h7u2)) (by decide)
          have he2_ne6 : e2 ≠ pos 6 := fun hh => absurd ((hfull6 7).1 (hh ▸ hs2 h7u2)) (by decide)
          obtain ⟨e', he'W, he'ne2, he'ne6, h8e'⟩ : ∃ e' ∈ sem_W 10 D 1, e' ≠ pos 2 ∧ e' ≠ pos 6 ∧ (8 : Fin 10) ∈ supp 10 D (src D e') := by
            by_cases h' : e1 = pos 2
            · exact ⟨e2, he2W, fun hh => he12 (h'.trans hh.symm), he2_ne6, hs2 h8u2⟩
            · exact ⟨e1, he1W, h', he1_ne6, hs1 h8u2⟩
          have he'_in8 : e' ∈ sem_W 10 D 8 := zm_mem hS hM8 (sem_mem_W.1 he'W).1 (sem_W_and hS he'W) h8e'
          have he'_eq5 : e' = e5 := by
            rcases hW8 e' he'_in8 with rfl | rfl | rfl | rfl
            · exact absurd (hfull3 1 (sem_mem_W.1 he'W).2.1) (by decide)
            · exact absurd rfl he'ne6
            · exact absurd rfl he'ne2
            · rfl
          rw [he'_eq5] at he'W
          have hW1_eq : sem_W 10 D 1 = {pos 2, pos 6, e5} := by
            symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
              rcases hf with rfl | rfl | rfl
              · exact as_mem hpos (hm 2 (by decide)) (by decide : Adj 2 1)
              · exact as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 1)
              · exact he'W
            · rw [Finset.card_insert_of_notMem (by simp [hp62.symm, hp2e]), Finset.card_pair hp6e]; exact hW1_le3
          have hfull2 := full_g10 h hD hB0 hpos (hm 2 (by decide)) (by decide : Adj 2 1) (fun p hp hne1 hsub => by
            rw [hW1_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with rfl | rfl | rfl
            · exact hne1 rfl
            · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 6 (by decide))))) (by decide)
            · exact hn 5 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe5_5).2.1) ▸ hm 2 (by decide)))
          exact absurd ((hfull2 8).1 h8_in2) (by decide)
        · have hW1_eq : sem_W 10 D 1 = {pos 2, pos 6} := by
            symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_)
              (by rw [Finset.card_pair (fun e => absurd (hpos.2 _ (hm 2 (by decide)) _ (hm 6 (by decide)) e) (by decide))]; omega)
            rw [Finset.mem_insert, Finset.mem_singleton] at hf
            rcases hf with rfl | rfl
            · exact as_mem hpos (hm 2 (by decide)) (by decide : Adj 2 1)
            · exact as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 1)
          have hfull2 := full_g10 h hD hB0 hpos (hm 2 (by decide)) (by decide : Adj 2 1) (fun p hp hne1 hsub => by
            rw [hW1_eq, Finset.mem_insert, Finset.mem_singleton] at hp
            rcases hp with rfl | rfl
            · exact hne1 rfl
            · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 6 (by decide))))) (by decide))
          exact absurd ((hfull2 8).1 h8_in2) (by decide)
  ·
    obtain ⟨u2, hru8⟩ := Finset.card_eq_one.1 (by omega : (ru D br 8).card = 1)
    have hu2R : u2 ∈ residualUnits 10 D br := (mem_ru.1 (hru8 ▸ Finset.mem_singleton_self u2)).1
    obtain ⟨u1, hu1eq⟩ := Finset.card_eq_one.1 (by rw [Finset.card_erase_of_mem hu2R, hR2] : ((residualUnits 10 D br).erase u2).card = 1)
    have hu1mem : u1 ∈ (residualUnits 10 D br).erase u2 := hu1eq ▸ Finset.mem_singleton_self u1
    have hu1ne2 : u1 ≠ u2 := (Finset.mem_erase.1 hu1mem).1
    have hu1R : u1 ∈ residualUnits 10 D br := (Finset.mem_erase.1 hu1mem).2
    have hReq : residualUnits 10 D br = {u1, u2} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun u hu => ?_) (by rw [Finset.card_pair hu1ne2, hR2])
      rw [Finset.mem_insert, Finset.mem_singleton] at hu; rcases hu with rfl | rfl; exact hu1R; exact hu2R
    have h4n2 : (4 : Fin 10) ∉ supp 10 D u2.1 :=
      w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 3 (by decide)) (hm 6 (by decide)) (x := 8) (v := 5) (by decide) hru8 (by decide)
    have hru4 : ru D br 4 = {u1} := by
      have hsub : ru D br 4 ⊆ {u1} := fun u hu => by
        have huR := (mem_ru.1 hu).1; rw [hReq, Finset.mem_insert, Finset.mem_singleton] at huR
        rcases huR with rfl | rfl
        · exact Finset.mem_singleton_self _
        · exact absurd (mem_ru.1 hu).2 h4n2
      exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)
    have hle2_of_nb : ∀ x : Fin 10, w3_bad 4 0 3 x = false → w3_bad 8 3 6 x = false → (sem_W 10 D x).card ≤ 2 := fun x h4b h8b => by
      have hrux : ru D br x = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro u hu
        have huR := (mem_ru.1 hu).1; rw [hReq, Finset.mem_insert, Finset.mem_singleton] at huR
        rcases huR with rfl | rfl
        · exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 h4b (mem_ru.1 hu).2
        · exact w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 3 (by decide)) (hm 6 (by decide)) (x := 8) (v := 5) (by decide) hru8 h8b (mem_ru.1 hu).2
      have := cc_le h hD br hbr x; rw [hrux, Finset.card_empty] at this; omega
    have hW2_7 : (sem_W 10 D 7).card ≤ 2 := hle2_of_nb 7 (by decide) (by decide)
    have hW2_1 : (sem_W 10 D 1).card ≤ 2 := hle2_of_nb 1 (by decide) (by decide)
    have h5_3 : 3 ≤ (sem_W 10 D 5).card := by
      by_contra hc; exact pa_m1_gen h hD hpos 5 7 8 0 2 1 (hm 0 (by decide)) (hm 2 (by decide))
        (hn 5 (by decide)) (hn 7 (by decide)) (hn 8 (by decide)) (by decide) (by omega) hW2_7
    have h9_3 : 3 ≤ (sem_W 10 D 9).card := by
      by_contra hc; exact pa_m1_gen h hD hpos 9 7 4 6 2 1 (hm 6 (by decide)) (hm 2 (by decide))
        (hn 9 (by decide)) (hn 7 (by decide)) (hn 4 (by decide)) (by decide) (by omega) hW2_7
    have h5n2 : (5 : Fin 10) ∉ supp 10 D u2.1 :=
      w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 3 (by decide)) (hm 6 (by decide)) (x := 8) (v := 5) (by decide) hru8 (by decide)
    have h9n1 : (9 : Fin 10) ∉ supp 10 D u1.1 :=
      w3_ru_one_not_mem h hD hB0 br hbm hpos (hm 0 (by decide)) (hm 3 (by decide)) (x := 4) (v := 9) (by decide) hru4 (by decide)
    have hru5 : ru D br 5 = {u1} := by
      have hsub : ru D br 5 ⊆ {u1} := fun u hu => by
        have huR := (mem_ru.1 hu).1; rw [hReq, Finset.mem_insert, Finset.mem_singleton] at huR
        rcases huR with rfl | rfl
        · exact Finset.mem_singleton_self _
        · exact absurd (mem_ru.1 hu).2 h5n2
      have := cc_le h hD br hbr 5; exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)
    have hru9 : ru D br 9 = {u2} := by
      have hsub : ru D br 9 ⊆ {u2} := fun u hu => by
        have huR := (mem_ru.1 hu).1; rw [hReq, Finset.mem_insert, Finset.mem_singleton] at huR
        rcases huR with rfl | rfl
        · exact absurd (mem_ru.1 hu).2 h9n1
        · exact Finset.mem_singleton_self _
      have := cc_le h hD br hbr 9; exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_singleton]; omega)
    have hW4_le3 : (sem_W 10 D 4).card ≤ 3 := by have := cc_le h hD br hbr 4; rw [hru4, Finset.card_singleton] at this; omega
    have hW8_le3 : (sem_W 10 D 8).card ≤ 3 := by have := cc_le h hD br hbr 8; rw [hru8, Finset.card_singleton] at this; omega
    have hW5_le3 : (sem_W 10 D 5).card ≤ 3 := by have := cc_le h hD br hbr 5; rw [hru5, Finset.card_singleton] at this; omega
    have hW9_le3 : (sem_W 10 D 9).card ≤ 3 := by have := cc_le h hD br hbr 9; rw [hru9, Finset.card_singleton] at this; omega
    have hM5 : merges 10 D (carrierT 10 D {5}) = ∅ := by
      have := cc_le h hD br hbr 5; rw [hru5, Finset.card_singleton] at this; exact Finset.card_eq_zero.1 (by omega)
    have hM9 : merges 10 D (carrierT 10 D {9}) = ∅ := by
      have := cc_le h hD br hbr 9; rw [hru9, Finset.card_singleton] at this; exact Finset.card_eq_zero.1 (by omega)
    obtain ⟨e9, he9_4, hbe9_9, hfe9, -⟩ := pa_ed h hD hpos (by decide : Adj 4 9)
    obtain ⟨e5, he5_8, hbe5_5, hfe5, -⟩ := pa_ed h hD hpos (by decide : Adj 8 5)
    have hp0_4 := as_mem hpos (hm 0 (by decide)) (by decide : Adj 0 4)
    have hp3_4 := as_mem hpos (hm 3 (by decide)) (by decide : Adj 3 4)
    have hp3_8 := as_mem hpos (hm 3 (by decide)) (by decide : Adj 3 8)
    have hp6_8 := as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 8)
    have hW4_eq : sem_W 10 D 4 = {pos 0, pos 3, e9} := by
      have hp03 : pos 0 ≠ pos 3 := fun e => absurd (hpos.2 _ (hm 0 (by decide)) _ (hm 3 (by decide)) e) (by decide)
      have hp0e : pos 0 ≠ e9 := fun e => hn 9 (by decide) (hfe9 _ (hm 0 (by decide)) e.symm ▸ hm 0 (by decide))
      have hp3e : pos 3 ≠ e9 := fun e => hn 9 (by decide) (hfe9 _ (hm 3 (by decide)) e.symm ▸ hm 3 (by decide))
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl | rfl; exact hp0_4; exact hp3_4; exact he9_4
      · rw [Finset.card_insert_of_notMem (by simp [hp03, hp0e]), Finset.card_pair hp3e]; exact hW4_le3
    have hW8_eq : sem_W 10 D 8 = {pos 3, pos 6, e5} := by
      have hp36 : pos 3 ≠ pos 6 := fun e => absurd (hpos.2 _ (hm 3 (by decide)) _ (hm 6 (by decide)) e) (by decide)
      have hp3e : pos 3 ≠ e5 := fun e => hn 5 (by decide) (hfe5 _ (hm 3 (by decide)) e.symm ▸ hm 3 (by decide))
      have hp6e : pos 6 ≠ e5 := fun e => hn 5 (by decide) (hfe5 _ (hm 6 (by decide)) e.symm ▸ hm 6 (by decide))
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl | rfl; exact hp3_8; exact hp6_8; exact he5_8
      · rw [Finset.card_insert_of_notMem (by simp [hp36, hp3e]), Finset.card_pair hp6e]; exact hW8_le3
    obtain ⟨_, hfull3⟩ := full_of_two_in_deg3 h hD hB0 hpos (hm 0 (by decide)) (hm 3 (by decide))
      (u := 4) (v := 9) (by decide) hW4_le3
    have hch0 := pos_chain_or h hD hB0 hpos (hm 0 (by decide)) (by decide : Adj 0 4) (fun p hp hne hsub => by
      rw [hW4_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hne rfl
      · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 3 (by decide))))) (by decide)
      · exact hn 9 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe9_9).2.1) ▸ hm 0 (by decide)))
    have hch3 := pos_chain_or h hD hB0 hpos (hm 3 (by decide)) (by decide : Adj 3 4) (fun p hp hne hsub => by
      rw [hW4_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 0 (by decide))))) (by decide)
      · exact hne rfl
      · exact hn 9 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe9_9).2.1) ▸ hm 3 (by decide)))
    have hch6 := pos_chain_or h hD hB0 hpos (hm 6 (by decide)) (by decide : Adj 6 8) (fun p hp hne hsub => by
      rw [hW8_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact absurd (Finset.mem_singleton.1 (hsub (pos_bar_mem hpos (hm 3 (by decide))))) (by decide)
      · exact hne rfl
      · exact hn 5 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbe5_5).2.1) ▸ hm 6 (by decide)))
    obtain ⟨Z7, hZ7_7, hbZ7_5, hfZ7, -⟩ := pa_ed h hD hpos (by decide : Adj 7 5)
    have hZ7_ne2 : Z7 ≠ pos 2 := fun hh => hn 5 (by decide) (hfZ7 2 (hm 2 (by decide)) hh ▸ hm 2 (by decide))
    have hW7_eq : sem_W 10 D 7 = {pos 2, Z7} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) (by rw [Finset.card_pair hZ7_ne2.symm]; exact hW2_7)
      rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl; exact as_mem hpos (hm 2 (by decide)) (by decide : Adj 2 7); exact hZ7_7
    have hch2 := pos_chain_or h hD hB0 hpos (hm 2 (by decide)) (by decide : Adj 2 7) (fun p hp hne hsub => by
      rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hne rfl
      · exact hn 5 (by decide) (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hbZ7_5).2.1) ▸ hm 2 (by decide)))
    have hW1_eq : sem_W 10 D 1 = {pos 2, pos 6} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_)
        (by rw [Finset.card_pair (fun e => absurd (hpos.2 _ (hm 2 (by decide)) _ (hm 6 (by decide)) e) (by decide))]; exact hW2_1)
      rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl; exact as_mem hpos (hm 2 (by decide)) (by decide : Adj 2 1); exact as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 1)
    have hbZ7_9 : sem_bar Z7 ∈ sem_W 10 D 9 := by
      obtain ⟨e7, he7_9, hbe7_7, -, -⟩ := pa_ed h hD hpos (by decide : Adj 9 7)
      rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at hbe7_7
      rcases hbe7_7 with h' | h'
      · exact absurd (as_priv hpos (hm 2 (by decide)) (by rw [← h', sem_bar_bar]; exact he7_9)) (by decide)
      · have : e7 = sem_bar Z7 := by simpa [sem_bar_bar] using congrArg sem_bar h'
        exact this ▸ he7_9
    have he9_5 : e9 ∈ sem_W 10 D 5 := by
      have hres45 : ∀ u ∈ residualUnits 10 D br, (4 : Fin 10) ∈ supp 10 D u.1 → (5 : Fin 10) ∈ supp 10 D u.1 := fun u hu h4u => by
        have hmem : u ∈ ru D br 4 := mem_ru.2 ⟨hu, h4u⟩
        rw [hru4, Finset.mem_singleton] at hmem
        exact hmem ▸ (mem_ru.1 (hru5 ▸ Finset.mem_singleton_self u1)).2
      have hw45 : (4 : Fin 10) ∈ supp 10 D u1.1 ∧ (5 : Fin 10) ∈ supp 10 D u1.1 :=
        ⟨(mem_ru.1 (hru4 ▸ Finset.mem_singleton_self u1)).2, (mem_ru.1 (hru5 ▸ Finset.mem_singleton_self u1)).2⟩
      obtain ⟨e0, he0⟩ := ri_gen sem_g10_gr h hC br hbr (by decide : (4 : Fin 10) ≠ 5) (helig 4 (by decide)) hres45 hw45
      have h0eq : pos 3 = e0 := by by_contra hne; exact absurd (hfull3 5 (he0 _ hp3_4 hne)) (by decide)
      have h5in := he0 e9 he9_4 (fun hh => hn 9 (by decide) (hfe9 3 (hm 3 (by decide)) (hh.trans h0eq.symm) ▸ hm 3 (by decide)))
      exact zm_mem hS hM5 (sem_mem_W.1 he9_4).1 (sem_W_and hS he9_4) h5in
    have he5_9 : e5 ∈ sem_W 10 D 9 := by
      have hres89 : ∀ u ∈ residualUnits 10 D br, (8 : Fin 10) ∈ supp 10 D u.1 → (9 : Fin 10) ∈ supp 10 D u.1 := fun u hu h8u => by
        have hmem : u ∈ ru D br 8 := mem_ru.2 ⟨hu, h8u⟩
        rw [hru8, Finset.mem_singleton] at hmem
        exact hmem ▸ (mem_ru.1 (hru9 ▸ Finset.mem_singleton_self u2)).2
      have hw89 : (8 : Fin 10) ∈ supp 10 D u2.1 ∧ (9 : Fin 10) ∈ supp 10 D u2.1 :=
        ⟨(mem_ru.1 (hru8 ▸ Finset.mem_singleton_self u2)).2, (mem_ru.1 (hru9 ▸ Finset.mem_singleton_self u2)).2⟩
      obtain ⟨e0, he0⟩ := ri_gen sem_g10_gr h hC br hbr (by decide : (8 : Fin 10) ≠ 9) (helig 8 (by decide)) hres89 hw89
      have h0eq : pos 3 = e0 := by by_contra hne; exact absurd (hfull3 9 (he0 _ hp3_8 hne)) (by decide)
      have h9in := he0 e5 he5_8 (fun hh => hn 5 (by decide) (hfe5 3 (hm 3 (by decide)) (hh.trans h0eq.symm) ▸ hm 3 (by decide)))
      exact zm_mem hS hM9 (sem_mem_W.1 he5_8).1 (sem_W_and hS he5_8) h9in
    have he5_ne_b7 : e5 ≠ sem_bar Z7 := fun hh => w_bar hS hbe5_5 (by rw [hh, sem_bar_bar]; exact hbZ7_5)
    have hbe9_ne_b7 : sem_bar e9 ≠ sem_bar Z7 := fun hh => by
      have : e9 = Z7 := by simpa [sem_bar_bar] using congrArg sem_bar hh
      exact w_bar hS hbZ7_5 (by simpa [sem_bar_bar] using this ▸ he9_5)
    have hbe9_ne_p6 : sem_bar e9 ≠ pos 6 := fun hh =>
      absurd (as_priv hpos (hm 6 (by decide)) (by rw [← hh, sem_bar_bar]; exact he9_4)) (by decide)
    have hbZ7_ne_p6 : sem_bar Z7 ≠ pos 6 := fun hh =>
      absurd (as_priv hpos (hm 6 (by decide)) (by rw [← hh, sem_bar_bar]; exact hZ7_7)) (by decide)
    have he5_ne_p6 : e5 ≠ pos 6 := fun hh => hn 5 (by decide) (hfe5 6 (hm 6 (by decide)) hh ▸ hm 6 (by decide))
    have he5_eq : e5 = sem_bar e9 := by
      by_contra hne
      have hp6_9 := as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 9)
      have hsub4 : ({pos 6, e5, sem_bar e9, sem_bar Z7} : Finset (ℕ × Bool)) ⊆ sem_W 10 D 9 := fun f hf => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl | rfl | rfl; exact hp6_9; exact he5_9; exact hbe9_9; exact hbZ7_9
      have hc4 : (({pos 6, e5, sem_bar e9, sem_bar Z7} : Finset (ℕ × Bool))).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [he5_ne_p6.symm, hbe9_ne_p6.symm, hbZ7_ne_p6.symm]),
            Finset.card_insert_of_notMem (by simp [hne, he5_ne_b7]),
            Finset.card_pair hbe9_ne_b7]
      have := hc4 ▸ Finset.card_le_card hsub4; omega
    subst he5_eq
    have hp6_9 := as_mem hpos (hm 6 (by decide)) (by decide : Adj 6 9)
    have hp0_5 := as_mem hpos (hm 0 (by decide)) (by decide : Adj 0 5)
    have hW9_eq : sem_W 10 D 9 = {pos 6, sem_bar e9, sem_bar Z7} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl | rfl; exact hp6_9; exact hbe9_9; exact hbZ7_9
      · rw [Finset.card_insert_of_notMem (by simp [hbe9_ne_p6.symm, hbZ7_ne_p6.symm]),
          Finset.card_pair hbe9_ne_b7]; exact hW9_le3
    have he9_ne_p0 : e9 ≠ pos 0 := fun hh => hn 9 (by decide) (hfe9 0 (hm 0 (by decide)) hh ▸ hm 0 (by decide))
    have hbZ7_ne_p0 : sem_bar Z7 ≠ pos 0 := fun hh =>
      absurd (as_priv hpos (hm 0 (by decide)) (by rw [← hh, sem_bar_bar]; exact hZ7_7)) (by decide)
    have he9_ne_b7 : e9 ≠ sem_bar Z7 := fun hh => w_bar hS hbe9_9 (by simpa [sem_bar_bar] using hh ▸ hbZ7_9)
    have hW5_eq : sem_W 10 D 5 = {pos 0, e9, sem_bar Z7} := by
      symm; refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hf
        rcases hf with rfl | rfl | rfl; exact hp0_5; exact he9_5; exact hbZ7_5
      · rw [Finset.card_insert_of_notMem (by simp [he9_ne_p0.symm, hbZ7_ne_p0.symm]),
          Finset.card_pair he9_ne_b7]; exact hW5_le3
    have he9_val_59 : val D (sem_two (5 : Fin 10) (9 : Fin 10)) (10 + e9.1) = true := by
      have hj := (sem_mem_W.1 he9_4).1; have ht := sem_W_and hS he9_4
      have h5s := val_mono hS (fun i => decide (i = 5)) (sem_two (5 : Fin 10) (9 : Fin 10))
        (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D e9) (mem_supp.1 (sem_mem_W.1 he9_5).2.1)
      have h9s := val_mono hS (fun i => decide (i = 9)) (sem_two (5 : Fin 10) (9 : Fin 10))
        (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D (sem_bar e9)) (mem_supp.1 (sem_mem_W.1 hbe9_9).2.1)
      rw [val_gate hS _ e9.1 hj, ht, gop_true]
      rcases hZeq : e9 with ⟨j, s⟩; rw [hZeq] at h5s h9s
      cases s
      · rw [sb_src_false] at h5s; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at h9s; simp [h5s, h9s]
      · rw [sb_src_true] at h5s; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at h9s; simp [h5s, h9s]
    have hp3_val_59 : val D (sem_two (5 : Fin 10) (9 : Fin 10)) (src D (sem_bar (pos 3))) = true := by
      obtain ⟨e, he4, -, he59, hbe59⟩ := pa_ed_avoid_min h hD (u := 4) (v := 9) (a := 5) (b := 9)
        (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)
      rw [hW4_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at he4
      rcases he4 with rfl | rfl | rfl
      · exfalso
        have hp0_lt := (hpos.1 0 (hm 0 (by decide))).1
        have ht0 : tag D (pos 0).1 = true := sem_W_and hS (e := sem_bar (pos 0)) (as_W h hD hpos (hm 0 (by decide)) ▸ Finset.mem_singleton_self _)
        have h5s := val_mono hS (fun i => decide (i = 5)) (sem_two (5 : Fin 10) (9 : Fin 10))
          (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two])
          (src D (pos 0)) (mem_supp.1 ((hpos.1 0 (hm 0 (by decide))).2.2.1 5 (by decide)))
        have hv0 : val D (sem_two (5 : Fin 10) (9 : Fin 10)) (10 + (pos 0).1) = true := by
          rw [val_gate hS _ (pos 0).1 hp0_lt, ht0, gop_true]
          rcases hpeq : pos 0 with ⟨j, s⟩; rw [hpeq] at h5s hbe59
          cases s
          · rw [sb_src_false] at h5s; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at hbe59; simp [h5s, hbe59]
          · rw [sb_src_true] at h5s; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at hbe59; simp [h5s, hbe59]
        rw [hv0] at he59; exact Bool.noConfusion he59
      · exact hbe59
      · rw [he9_val_59] at he59; exact Bool.noConfusion he59
    have hno_59_edge : ¬ G10Edge (sem_two (5 : Fin 10) (9 : Fin 10)) := by
      rw [g10Edge_iff_adj]; rintro ⟨p, q, hpq, hp', hq'⟩
      simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hp' hq'
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
      · exact adj_irrefl _ hpq
      · exact absurd hpq (by decide)
      · exact absurd hpq (by decide)
      · exact adj_irrefl _ hpq
    have hfan_gt_e9 : ∀ w, 10 + e9.1 < w → (5 : Fin 10) ∉ supp 10 D w → (9 : Fin 10) ∉ supp 10 D w →
        2 ≤ fanout D w → (br 1 = w ∨ br 7 = w) := by
      intro w hgt h5n h9n hfw
      have hne_s := sem_bzero_branch hS hB0 hfw
      have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
        rw [unitsPlus, Finset.mem_filter, mem_units]
        exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), by show 0 + 1 < fanout D w; omega⟩, hne_s⟩
      have hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D br := by
        by_contra hnr
        have hmemR : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits 10 D br := Finset.mem_sdiff.2 ⟨hwu, hnr⟩
        rw [hReq, Finset.mem_insert, Finset.mem_singleton] at hmemR
        rcases hmemR with h1' | h2'
        · have hwe : w = u1.1 := congrArg Sigma.fst h1'
          rw [hwe] at h5n; exact h5n (mem_ru.1 (hru5 ▸ Finset.mem_singleton_self u1)).2
        · have hwe : w = u2.1 := congrArg Sigma.fst h2'
          rw [hwe] at h9n; exact h9n (mem_ru.1 (hru9 ▸ Finset.mem_singleton_self u2)).2
      obtain ⟨y, hyE, hyeq⟩ := Finset.mem_image.1 hwr
      have hby : br y = w := congrArg Sigma.fst hyeq
      fin_cases y
      · exact absurd hyE (Finset.mem_sdiff.1 (hm 0 (by decide))).2
      · exact Or.inl hby
      · exact absurd hyE (Finset.mem_sdiff.1 (hm 2 (by decide))).2
      · exact absurd hyE (Finset.mem_sdiff.1 (hm 3 (by decide))).2
      · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE he9_4)
      · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE he9_5)
      · exact absurd hyE (Finset.mem_sdiff.1 (hm 6 (by decide))).2
      · exact Or.inr hby
      · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE he5_8)
      · exact absurd (hby ▸ hgt) (sem_minBranch_not_after h br hbm hyE hbe9_9)
    have hfan1_of_not59 : ∀ (g : ℕ), g < D.length → tag D g = true →
        (5 : Fin 10) ∉ supp 10 D (10 + g) → (9 : Fin 10) ∉ supp 10 D (10 + g) →
        fanout D (10 + g) ≤ 1 := fun g hg ht h5n h9n => by
      by_contra hf
      have hne_s := sem_bzero_branch hS hB0 (by omega : 2 ≤ fanout D (10 + g))
      have hwu : (⟨10 + g, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus 10 D := by
        rw [unitsPlus, Finset.mem_filter, mem_units]
        exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := 10 + g) (by omega)), by show 0 + 1 < fanout D (10 + g); omega⟩, hne_s⟩
      have hwr : (⟨10 + g, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits 10 D br := by
        by_contra hnr
        have hmemR : (⟨10 + g, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits 10 D br := Finset.mem_sdiff.2 ⟨hwu, hnr⟩
        rw [hReq, Finset.mem_insert, Finset.mem_singleton] at hmemR
        rcases hmemR with h1' | h2'
        · have hge : 10 + g = u1.1 := congrArg Sigma.fst h1'
          rw [hge] at h5n; exact h5n (mem_ru.1 (hru5 ▸ Finset.mem_singleton_self u1)).2
        · have hge : 10 + g = u2.1 := congrArg Sigma.fst h2'
          rw [hge] at h9n; exact h9n (mem_ru.1 (hru9 ▸ Finset.mem_singleton_self u2)).2
      obtain ⟨y, hyE, hyeq⟩ := Finset.mem_image.1 hwr
      exact sem_minBranch_not_and h br hbm hyE hg ht (congrArg Sigma.fst hyeq)
    exact kill_4cycle_gate h hD hB0 br hbm hpos
      (Z := e9) (Z' := Z7) (a1 := 4) (b1 := 8) (a2 := 5) (b2 := 9) (c := 7) (d := 5) (i0 := 3)
      (sem_mem_W.1 he9_4).1 (sem_W_and hS he9_4)
      (sem_mem_W.1 hZ7_7).1 (sem_W_and hS hZ7_7)
      (sem_mem_W.1 he9_4).2.1 (sem_mem_W.1 he5_8).2.1 (by decide)
      (sem_mem_W.1 he9_5).2.1 (sem_mem_W.1 hbe9_9).2.1 (sem_mem_W.1 he9_5).2.2 (sem_mem_W.1 hbe9_9).2.2
      (fun j s h5W h9W => by
        rw [hW5_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h5W
        rcases h5W with h5e | h5e | h5e
        · exfalso; exact absurd (as_priv hpos (hm 0 (by decide)) (by rw [← h5e]; exact h9W)) (by decide)
        · exact congrArg Prod.fst h5e
        · exfalso; have : (j, !s) = Z7 := by simpa [sem_bar, sem_bar_bar] using congrArg sem_bar h5e
          exact w_bar hS hbZ7_9 (by simpa [sem_bar_bar] using this ▸ h9W))
      (hm 3 (by decide)) (by decide) hch3.2.2 ((hpos.1 3 (hm 3 (by decide))).2.2.1 4 (by decide)) hp3_val_59
      (fun e he hv2 hv1 => by
        have he9_val_48 : val D (sem_two (4 : Fin 10) (8 : Fin 10)) (10 + e9.1) = true := by
          have hj := (sem_mem_W.1 he9_4).1; have ht := sem_W_and hS he9_4
          have h4s := val_mono hS (fun i => decide (i = 4)) (sem_two (4 : Fin 10) (8 : Fin 10))
            (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D e9) (mem_supp.1 (sem_mem_W.1 he9_4).2.1)
          have h8s := val_mono hS (fun i => decide (i = 8)) (sem_two (4 : Fin 10) (8 : Fin 10))
            (fun i hi => by rw [decide_eq_true_eq] at hi; subst hi; simp [sem_two]) (src D (sem_bar e9)) (mem_supp.1 (sem_mem_W.1 he5_8).2.1)
          rw [val_gate hS _ e9.1 hj, ht, gop_true]
          rcases hZeq : e9 with ⟨j, s⟩; rw [hZeq] at h4s h8s
          cases s
          · rw [sb_src_false] at h4s; rw [show src D (sem_bar (j, false)) = opB D j from rfl] at h8s; simp [h4s, h8s]
          · rw [sb_src_true] at h4s; rw [show src D (sem_bar (j, true)) = opA D j from rfl] at h8s; simp [h4s, h8s]
        rcases he with he5 | he9'
        · rw [hW5_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at he5
          rcases he5 with rfl | rfl | rfl
          · exact absurd (hch0.2.2 _ hv2) hno_59_edge
          · rw [he9_val_48] at hv1; exact Bool.noConfusion hv1
          · rfl
        · rw [hW9_eq, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at he9'
          rcases he9' with rfl | rfl | rfl
          · exact absurd (hch6.2.2 _ hv2) hno_59_edge
          · rw [show (sem_bar e9).1 = e9.1 from rfl, he9_val_48] at hv1; exact Bool.noConfusion hv1
          · rfl)
      (fun w hgt _ h5n h9n hfw => by
        rcases hfan_gt_e9 w hgt h5n h9n hfw with h1eq | h7eq
        · refine ⟨1, helig 1 (by decide), h1eq, fun e heW hev _ _ => ?_⟩
          rw [hW1_eq, Finset.mem_insert, Finset.mem_singleton] at heW
          rcases heW with rfl | rfl
          · exact absurd (hch2.2.2 _ hev) hno_59_edge
          · exact absurd (hch6.2.2 _ hev) hno_59_edge
        · refine ⟨7, helig 7 (by decide), h7eq, fun e heW hev _ _ => ?_⟩
          rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at heW
          rcases heW with rfl | rfl
          · exact absurd (hch2.2.2 _ hev) hno_59_edge
          · rfl)
      (fun w hgt4 hgt7 _ h5n h9n hfw => by
        rcases hfan_gt_e9 w hgt4 h5n h9n hfw with h1eq | h7eq
        · refine ⟨1, helig 1 (by decide), h1eq, fun e heW hev _ _ => ?_⟩
          rw [hW1_eq, Finset.mem_insert, Finset.mem_singleton] at heW
          rcases heW with rfl | rfl
          · exact hno_59_edge (hch2.2.2 _ hev)
          · exact hno_59_edge (hch6.2.2 _ hev)
        · exact absurd (h7eq ▸ hgt7) (sem_minBranch_not_after h br hbm (helig 7 (by decide)) hZ7_7))
      (by decide : Adj 7 5)
      (fun j s h7W h5W => by
        rw [hW7_eq, Finset.mem_insert, Finset.mem_singleton] at h7W
        rcases h7W with h7e | h7e
        · exfalso; exact absurd (as_priv hpos (hm 2 (by decide)) (by rw [← h7e]; exact h5W)) (by decide)
        · exact congrArg Prod.fst h7e)
      (fun h7in => absurd (hfull3 7 h7in) (by decide))
      (fun h5in => absurd (hfull3 5 h5in) (by decide))
      (hfan1_of_not59 e9.1 (sem_mem_W.1 he9_4).1 (sem_W_and hS he9_4) (sem_mem_W.1 he9_5).2.2 (sem_mem_W.1 hbe9_9).2.2)
      (hfan1_of_not59 Z7.1 (sem_mem_W.1 hZ7_7).1 (sem_W_and hS hZ7_7) (sem_mem_W.1 hbZ7_5).2.2 (sem_mem_W.1 hbZ7_9).2.2)

theorem elim_38 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h8 : totalSurplus 10 D ≤ 8)
    (hI : ineligSet 10 D = hc_rep ⟨38, by decide⟩) : False := by
  have hIeq : ineligSet 10 D = {2, 3, 5, 6} := by rw [hI]; decide
  have hm : ∀ v : Fin 10, v ∈ ({2, 3, 5, 6} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({2, 3, 5, 6} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({2, 3, 5, 6} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, br, hbm, hR2, pos, hpos⟩ := res2_setup h hD h8 ⟨38, by decide⟩ (by decide) hI
  have hbr := sem_minBranch_pure hbm
  rcases w3_res2_dichotomy h hD hB0 br hbm hpos hR2 7 8 2 5 9 5 6 3
      (hm 2 (by decide)) (hm 5 (by decide)) (hm 5 (by decide)) (hm 6 (by decide))
      (by decide) (by decide) (by decide) (by decide) with ⟨hru7, hru8⟩ | hle2
  · exact pe_co_blow5 h hD br hbr hpos 8 7 3 6 4 1 2 5 9
      (helig 8 (by decide)) (hm 3 (by decide)) (hm 6 (by decide)) (hm 2 (by decide)) (hm 5 (by decide))
      (hn 9 (by decide)) (by decide) (by rw [hru8, hR2]; omega) (by rw [hru8, hru7]) (by rw [hru7, hR2])
  · exact pa_m1_gen h hD hpos 9 4 7 6 3 8 (hm 6 (by decide)) (hm 3 (by decide))
      (hn 9 (by decide)) (hn 4 (by decide)) (hn 7 (by decide)) (by decide)
      (hle2 9 (by decide) (by decide)) (hle2 4 (by decide) (by decide))

theorem elim_39 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h8 : totalSurplus 10 D ≤ 8)
    (hI : ineligSet 10 D = hc_rep ⟨39, by decide⟩) : False := by
  have hIeq : ineligSet 10 D = {2, 4, 5, 6} := by rw [hI]; decide
  have hm : ∀ v : Fin 10, v ∈ ({2, 4, 5, 6} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({2, 4, 5, 6} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({2, 4, 5, 6} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, br, hbm, hR2, pos, hpos⟩ := res2_setup h hD h8 ⟨39, by decide⟩ (by decide) hI
  have hbr := sem_minBranch_pure hbm
  rcases w3_res2_dichotomy h hD hB0 br hbm hpos hR2 7 9 2 5 9 4 6 7
      (hm 2 (by decide)) (hm 5 (by decide)) (hm 4 (by decide)) (hm 6 (by decide))
      (by decide) (by decide) (by decide) (by decide) with ⟨hru7, hru9⟩ | hle2
  · exact pe_co_blow5 h hD br hbr hpos 7 9 2 5 1 0 4 6 7
      (helig 7 (by decide)) (hm 2 (by decide)) (hm 5 (by decide)) (hm 4 (by decide)) (hm 6 (by decide))
      (hn 7 (by decide)) (by decide) (by rw [hru7, hR2]; omega) (by rw [hru7, hru9]) (by rw [hru9, hR2])
  · have h8_3 := two_in_deg3 h hD hpos (hm 5 (by decide)) (hm 6 (by decide)) (u := 8) (v := 3) (by decide)
    have := hle2 8 (by decide) (by decide); omega

theorem elim_40 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h8 : totalSurplus 10 D ≤ 8)
    (hI : ineligSet 10 D = hc_rep ⟨40, by decide⟩) : False := by
  have hIeq : ineligSet 10 D = {0, 3, 6, 7} := by rw [hI]; decide
  have hm : ∀ v : Fin 10, v ∈ ({0, 3, 6, 7} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({0, 3, 6, 7} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({0, 3, 6, 7} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, br, hbm, hR2, pos, hpos⟩ := res2_setup h hD h8 ⟨40, by decide⟩ (by decide) hI
  have hbr := sem_minBranch_pure hbm
  rcases w3_res2_dichotomy h hD hB0 br hbm hpos hR2 5 8 0 7 8 3 6 5
      (hm 0 (by decide)) (hm 7 (by decide)) (hm 3 (by decide)) (hm 6 (by decide))
      (by decide) (by decide) (by decide) (by decide) with ⟨hru5, hru8⟩ | hle2
  · exact pe_co_blow5 h hD br hbr hpos 5 8 0 7 4 2 3 6 5
      (helig 5 (by decide)) (hm 0 (by decide)) (hm 7 (by decide)) (hm 3 (by decide)) (hm 6 (by decide))
      (hn 5 (by decide)) (by decide) (by rw [hru5, hR2]; omega) (by rw [hru5, hru8]) (by rw [hru8, hR2])
  · have h4_3 := two_in_deg3 h hD hpos (hm 0 (by decide)) (hm 3 (by decide)) (u := 4) (v := 9) (by decide)
    have := hle2 4 (by decide) (by decide); omega

theorem elim_41 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h8 : totalSurplus 10 D ≤ 8)
    (hI : ineligSet 10 D = hc_rep ⟨41, by decide⟩) : False := by
  have hIeq : ineligSet 10 D = {0, 1, 3, 9} := by rw [hI]; decide
  have hm : ∀ v : Fin 10, v ∈ ({0, 1, 3, 9} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({0, 1, 3, 9} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({0, 1, 3, 9} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, br, hbm, hR2, pos, hpos⟩ := res2_setup h hD h8 ⟨41, by decide⟩ (by decide) hI
  have hbr := sem_minBranch_pure hbm
  rcases w3_res2_dichotomy h hD hB0 br hbm hpos hR2 4 6 0 9 3 1 9 8
      (hm 0 (by decide)) (hm 9 (by decide)) (hm 1 (by decide)) (hm 9 (by decide))
      (by decide) (by decide) (by decide) (by decide) with ⟨hru4, hru6⟩ | hle2
  · exact shared_w3_bothR h hD hB0 br hbr hpos hR2 4 6 9 0 1 8 5 2
      (helig 4 (by decide)) (helig 6 (by decide)) (hm 9 (by decide)) (hm 0 (by decide)) (hm 1 (by decide))
      (hn 8 (by decide)) (by decide) hru4 hru6
  · exact pa_m1_gen h hD hpos 8 5 6 3 0 4 (hm 3 (by decide)) (hm 0 (by decide))
      (hn 8 (by decide)) (hn 5 (by decide)) (hn 6 (by decide)) (by decide)
      (hle2 8 (by decide) (by decide)) (hle2 5 (by decide) (by decide))

theorem elim_42 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h8 : totalSurplus 10 D ≤ 8)
    (hI : ineligSet 10 D = hc_rep ⟨42, by decide⟩) : False := by
  have hIeq : ineligSet 10 D = {1, 3, 5, 9} := by rw [hI]; decide
  have hm : ∀ v : Fin 10, v ∈ ({1, 3, 5, 9} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({1, 3, 5, 9} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({1, 3, 5, 9} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, br, hbm, hR2, pos, hpos⟩ := res2_setup h hD h8 ⟨42, by decide⟩ (by decide) hI
  have hbr := sem_minBranch_pure hbm
  rcases w3_res2_dichotomy h hD hB0 br hbm hpos hR2 6 8 1 9 8 3 5 6
      (hm 1 (by decide)) (hm 9 (by decide)) (hm 3 (by decide)) (hm 5 (by decide))
      (by decide) (by decide) (by decide) (by decide) with ⟨hru6, hru8⟩ | hle2
  · exact pe_co_blow5 h hD br hbr hpos 6 8 1 9 2 4 3 5 6
      (helig 6 (by decide)) (hm 1 (by decide)) (hm 9 (by decide)) (hm 3 (by decide)) (hm 5 (by decide))
      (hn 6 (by decide)) (by decide) (by rw [hru6, hR2]; omega) (by rw [hru6, hru8]) (by rw [hru8, hR2])
  · have h4_3 := two_in_deg3 h hD hpos (hm 3 (by decide)) (hm 9 (by decide)) (u := 4) (v := 0) (by decide)
    have := hle2 4 (by decide) (by decide); omega

theorem elim_43 {D : Dag} (h : StrictLive 10 D) (hD : Correct D) (h8 : totalSurplus 10 D ≤ 8)
    (hI : ineligSet 10 D = hc_rep ⟨43, by decide⟩) : False := by
  have hIeq : ineligSet 10 D = {2, 3, 5, 9} := by rw [hI]; decide
  have hm : ∀ v : Fin 10, v ∈ ({2, 3, 5, 9} : Finset (Fin 10)) → v ∈ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have hn : ∀ v : Fin 10, v ∉ ({2, 3, 5, 9} : Finset (Fin 10)) → v ∉ ineligSet 10 D := fun v hv => hIeq ▸ hv
  have helig : ∀ v : Fin 10, v ∉ ({2, 3, 5, 9} : Finset (Fin 10)) → v ∈ eligSet 10 D := fun v hv => by
    by_contra hc; exact hv (hIeq ▸ sem_mem_inelig.2 hc)
  obtain ⟨hB0, br, hbm, hR2, pos, hpos⟩ := res2_setup h hD h8 ⟨43, by decide⟩ (by decide) hI
  have hbr := sem_minBranch_pure hbm
  rcases w3_res2_dichotomy h hD hB0 br hbm hpos hR2 4 8 3 9 0 3 5 6
      (hm 3 (by decide)) (hm 9 (by decide)) (hm 3 (by decide)) (hm 5 (by decide))
      (by decide) (by decide) (by decide) (by decide) with ⟨hru4, hru8⟩ | hle2
  · exact shared_w3_bothR h hD hB0 br hbr hpos hR2 4 8 3 9 5 6 7 7
      (helig 4 (by decide)) (helig 8 (by decide)) (hm 3 (by decide)) (hm 9 (by decide)) (hm 5 (by decide))
      (hn 6 (by decide)) (by decide) hru4 hru8
  · have h7_3 := two_in_deg3 h hD hpos (hm 2 (by decide)) (hm 5 (by decide)) (u := 7) (v := 9) (by decide)
    have := hle2 7 (by decide) (by decide); omega

theorem g10_orbit_partition : ∀ idx : Fin 44,
    (hc_rep idx).card ≤ 3 ∨
    idx.val = 37 ∨ idx.val = 38 ∨ idx.val = 39 ∨ idx.val = 40 ∨
    idx.val = 41 ∨ idx.val = 42 ∨ idx.val = 43 := by
  decide +kernel

theorem g10_lb_18 (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = true ↔ G10Edge x) (hsize : C.size ≤ 17) :
    False := by
  obtain ⟨D, h, hD, -, h8, -, hmem⟩ := g10_wlog_canon C hmono hC hsize
  obtain ⟨idx, hI⟩ := hc_rep_of_mem hmem
  have hI' : ineligSet 10 D = hc_rep idx := hI.symm
  have hts := totalSurplus_split 10 D
  have hel := inelig_card_add 10 D
  rcases g10_orbit_partition idx with hc3 | h37 | h38 | h39 | h40 | h41 | h42 | h43
  · by_cases hB : Bplus 10 D ≤ (eligSet 10 D).card
    · exact elim_R0_all h hD h8 hB idx hI'
    · have hcard3 : 3 ≤ (hc_rep idx).card := by rw [hI'] at hel; omega
      exact elim_R1_all h hD h8 (by rw [hI'] at hel; omega) idx hcard3 hI'
  · exact elim_37 h hD h8 ((show idx = ⟨37, by decide⟩ from Fin.ext h37) ▸ hI')
  · exact elim_38 h hD h8 ((show idx = ⟨38, by decide⟩ from Fin.ext h38) ▸ hI')
  · exact elim_39 h hD h8 ((show idx = ⟨39, by decide⟩ from Fin.ext h39) ▸ hI')
  · exact elim_40 h hD h8 ((show idx = ⟨40, by decide⟩ from Fin.ext h40) ▸ hI')
  · exact elim_41 h hD h8 ((show idx = ⟨41, by decide⟩ from Fin.ext h41) ▸ hI')
  · exact elim_42 h hD h8 ((show idx = ⟨42, by decide⟩ from Fin.ext h42) ▸ hI')
  · exact elim_43 h hD h8 ((show idx = ⟨43, by decide⟩ from Fin.ext h43) ▸ hI')

end PEqualNP.Outside.L_meta_9785_aux

theorem PEqualNP.Outside.L_meta_9785 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 17 ∧ (∀ x : Fin 10 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 10, (u.val, v.val) ∈ ([(1, 2), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (6, 9), (6, 8), (5, 8)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)))) := by
  rintro ⟨C, hmono, hsize, hC⟩
  exact PEqualNP.Outside.L_meta_9785_aux.g10_lb_18 C hmono hC hsize

namespace PEqualNP.Outside.L_meta_9822.Switch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
def readGate (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def stage (w : List Bool) (g : Gate) := w ++ [readGate g w]
def run (gs : List Gate) (w : List Bool) := gs.foldl stage w
def below (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true
theorem extend {a b : List Bool} {v w : Bool} (h : below a b) (hv : v=true → w=true) :
    below (a++[v]) (b++[w]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases lt : i<a.length
  · have lt' : i<b.length := h.1 ▸ lt
    simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left lt'] using h.2 i
  · by_cases eq : i=a.length
    · subst i
      have last (l : List Bool) (x : Bool) : (l++[x]).getD l.length false=x := by
        simp [List.getD_eq_getElem?_getD]
      rw [last,h.1,last]
      exact hv
    · have lo : (a++[v]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none lo]
theorem gate_mono {a b : List Bool} {g : Gate} (h : below a b) (hg : good g) :
    readGate g a=true → readGate g b=true := by
  have op : g.op=GateOp.and ∨ g.op=GateOp.or := by simpa using hg.1
  rcases op with ha | ho
  · simp only [readGate,ha,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro ht i hi
    exact h.2 i (ht i hi)
  · simp only [readGate,ho,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hh⟩
    exact ⟨i,hi,h.2 i hh⟩
theorem run_mono {a b : List Bool} (gs : List Gate) (ok : ∀ g ∈ gs, good g)
    (h : below a b) : below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun t ht => ok _ (by simp [ht])) (extend h (gate_mono h (ok _ (by simp))))
def edges : List (Nat × Nat) :=
  [(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
def target (x : Fin 10 → Bool) : Prop := ∃ u v : Fin 10,
  (u.val,v.val) ∈ edges ∧ x u=true ∧ x v=true
def replaced (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat) : Circuit :=
  ⟨pre ++ (g::post),out⟩
theorem replaced_eval (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat)
    (x : List Bool) : (replaced pre g post out).eval x =
    (run post (stage (run pre x) g)).getD out false := by
  simp only [replaced,Circuit.eval,Circuit.wires,run,stage,readGate,List.foldl_append,List.foldl_cons]
theorem obstruction (pre post : List Gate) (pivot repl : Gate) (out : Nat)
    (hp : ∀ g ∈ pre, good g) (hs : ∀ g ∈ post, good g) (hr : good repl)
    (lim : (replaced pre pivot post out).size ≤ 17)
    (hfun : ∀ x, (replaced pre pivot post out).eval (List.ofFn x)=true ↔ target x) :
    ∃ x : Fin 10 → Bool,
      let w := run pre (List.ofFn x)
      (target x ∧ readGate pivot w=true ∧ readGate repl w=false) ∨
      (¬ target x ∧ readGate repl w=true ∧ readGate pivot w=false) := by
  classical
  by_contra h
  have deny (x : Fin 10 → Bool) := not_exists.mp h x
  apply PEqualNP.Outside.L_meta_9785
  refine ⟨replaced pre repl post out, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ pre ++ (repl::post) at hg
    rcases List.mem_append.mp hg with ha | hb
    · exact hp _ ha
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hr
      · exact hs _ hb
  · simpa [Circuit.size,replaced] using lim
  · intro x
    change (replaced pre repl post out).eval (List.ofFn x)=true ↔ target x
    let w := run pre (List.ofFn x)
    have ww : below w w := ⟨rfl,fun _ h => h⟩
    have old := hfun x
    rw [replaced_eval] at old ⊢
    change (run post (stage w pivot)).getD out false=true ↔ target x at old
    change (run post (stage w repl)).getD out false=true ↔ target x
    constructor
    · intro hn
      by_contra ht
      have low : readGate repl w=true → readGate pivot w=true := by
        intro huv
        cases hh : readGate pivot w with
        | true => rfl
        | false => exact False.elim (deny x (Or.inr ⟨ht,huv,hh⟩))
      exact ht (old.mp ((run_mono post hs (extend ww low)).2 out hn))
    · intro ht
      have low : readGate pivot w=true → readGate repl w=true := by
        intro huv
        cases hh : readGate repl w with
        | true => rfl
        | false => exact False.elim (deny x (Or.inl ⟨ht,huv,hh⟩))
      exact (run_mono post hs (extend ww low)).2 out (old.mpr ht)
theorem twoSides (pre post : List Gate) (pivot : Gate) (out : Nat)
    (hp : ∀ g ∈ pre, good g) (hs : ∀ g ∈ post, good g)
    (lim : (replaced pre pivot post out).size ≤ 17)
    (hfun : ∀ x, (replaced pre pivot post out).eval (List.ofFn x)=true ↔ target x) :
    (∃ x, target x ∧ readGate pivot (run pre (List.ofFn x))=true) ∧
    (∃ x, ¬ target x ∧ readGate pivot (run pre (List.ofFn x))=false) := by
  constructor
  · obtain ⟨x,h⟩ := obstruction pre post pivot ⟨.or,[]⟩ out hp hs (by simp [good]) lim hfun
    refine ⟨x,?_⟩
    simpa [readGate,GateOp.eval] using h
  · obtain ⟨x,h⟩ := obstruction pre post pivot ⟨.and,[]⟩ out hp hs (by simp [good]) lim hfun
    refine ⟨x,?_⟩
    simpa [readGate,GateOp.eval] using h
end PEqualNP.Outside.L_meta_9822.Switch
