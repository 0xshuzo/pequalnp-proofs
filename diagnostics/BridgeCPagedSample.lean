import PEqualNP.Defs

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_4813_aux.Certificate
open PEqualNP.CircuitLowerBounds

def mask72 : Nat := 0xffffffffffffffffff

def limbs (xs : List Nat) : Nat := xs.foldl (fun a n => (a <<< 80) + n) 0
def word {n : Nat} (xs : List Nat) : BitVec n := BitVec.ofNat n (limbs xs)

def stripe4813 {n : Nat} (s : Nat) : BitVec n :=
  BitVec.ofNat n (((((1 : Nat) <<< n)-1)/(((1 : Nat) <<< s)+1)) <<< s)

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

def inputs : List Sig := [(stripe4813 1),(stripe4813 2),(stripe4813 4),(stripe4813 8),(stripe4813 16),(stripe4813 32),(stripe4813 64),(stripe4813 128),(stripe4813 256)]
def graph : Sig := (word [0xffffffff,0xfffffffffffffffffffa,0xfff8ffffffffffffffff,0xffffffffffeaffc8ffff,0xfffffffefcfcffffffff,0xfffaf8f8ffeefeeeffee,0xfcccffeafaeaffeaf8c8])
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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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
  | 0 => (limbs [0x1000000000000,0x10000000000000001,65536,4294967296,0x1000000000000,0x10000000000000001])
  | 1 => (limbs [0x10000000000000000,65536,0,0x1000000000000,1])
  | 2 => (limbs [1,65536,0,0,0x10000000000000001])
  | 3 => (limbs [65536,0,0,1])
  | 4 => (limbs [4294967296,0x1000000000000,0x10000000000000001])
  | 5 => (limbs [0x1000000000000,1])
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
def hardSeed : Sig := inputs.getD 0 zero &&& inputs.getD 2 zero
def chartGoal (m : Nat) : Sig := if m=1023 then graphGoal m &&& ~~~hardSeed else graphGoal m
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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  pools.any (fun p => scalarPoolCut u p k rest op) || (links (keySet ws)).any (sameWords ws)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · rw [sameWords_sound ok]
    exact lValid _ _ hx

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
def page (xs : Array Nat) (i : Nat) : Nat := xs.getD (i%103) 0
def gather (w : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => w i ||| (gather w (i+1) n <<< 80)
def pick4813 (w : Nat → Nat) (b p n : Nat) :=
  let i := 103*b+p/80
  let s := p%80
  let a := if s+n ≤ 80 then w i else if s+n ≤ 160 then
    w i ||| (w (i+1) <<< 80) else gather w i ((s+n+79)/80)
  (a >>> s) &&& ((1 <<< n)-1)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let b := pos/8192
  let s := pos % 8192
  let left := 8192-s
  if len ≤ left then pick4813 word b s len else
    pick4813 word b s left ||| (pick4813 word (b+1) 0 (len-left) <<< left)

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
  let prod := dbin 0 (ws.getD 0 defaultDecor) (ws.getD 2 defaultDecor)
  if g.mask=1023 then ws.map (fun w => dbin 2 w prod) else ws

theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin 2 (base w hw) (faithful_bin 0 (faithful_get base 0) (faithful_get base 2))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 2) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (2 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 2 zero).getLsbD (asRow v i).val = (v 2).getLsbD i.val at w
    have seedEq : hardSeed = inputs.getD 0 zero &&& inputs.getD 2 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
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
    getPairs data cw d (packedAt data pos 5) (pos+5+marker)
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


def ecY : Array (Bits × Bits) := #[((word [0x108380004061f0c00,0xdc0661804078f001f]),(word [0x908380004021f0400,0xd40260804078b004f])),((word [0xc10040c83828e03c27,0xde85c999e1ffc070cf1f]),(word [0xd00046c82aa0a0a825,0xde80888161318020e310])),((word [0x6078001c009003018,0x120600060878700fe0]),(word [0x2078001c009001008,0x100200060878500c80])),((word [0xf888000e0031ffc1e0,0x18e437e007f1bf80f1fc]),(word [0x5888100a0100c701a1,0x180515f000e083021178])),((word [0x3000f0003e000240,0x60f83801f801c000fe00]),(word [0x3400f0003c000240,0x60f02801f0014000ee00])),((word [0xc000ffffc0000380,0x7f003ffe0001ffff0000]),(word [0xc1005cf180800080,0xb003fd84481f0644400])),((word [0xffff0000000003ff,0x80003ffffffe00000000]),(word [0xd9980080000203da,0x377c9ecc22080001])),((word [0xff00000000000003ff,0xffffc000000000000000]),(word [0xfd0000000000140377,0xf4efc000000000000000])),((word [0xfffffffffffffffc00,0]),(word [0xa72664a1063f18a804,0x20400001010004008882]))]
def ecC : List ColumnInfo := [(1,0,510,0,12),(4,0,507,0,12),(17,0,494,0,11),(132,0,379,0,11),(1,16,486,8,9),(3,0,508,0,9),(4,128,347,32,9),(12,0,499,0,9),(33,0,478,0,9),(65,0,446,0,9),(257,0,254,0,8),(9,16,486,0,8),(36,128,347,0,8),(67,0,444,0,8),(1,2,440,68,7),(1,32,94,384,7),(1,64,188,258,7),(4,8,227,272,7),(14,0,497,0,7),(35,0,476,0,7),(268,0,243,0,7),(289,0,222,0,7),(321,0,190,0,7),(3,64,188,256,6),(12,64,177,258,6),(65,2,440,4,6),(65,32,30,384,6),(68,8,163,272,6),(257,32,94,128,6),(257,64,188,2,6),(260,8,227,16,6),(259,0,188,0,5),(14,64,177,256,5),(35,64,156,256,5),(41,16,454,0,5),(73,16,422,0,5),(78,0,433,0,5),(259,64,188,0,5),(268,64,177,2,5),(289,64,156,2,5),(321,32,30,128,5),(323,0,188,0,5),(324,8,163,16,5),(332,0,179,0,5),(270,0,177,0,4),(291,0,156,0,4),(102,128,281,0,4),(270,64,177,0,4),(291,64,156,0,4),(297,16,198,0,4),(355,0,156,0,4)]
def ecA : List (List Nat) := [[],[32,83,116]]
def ecD9 (j : Nat) : Nat := (if j<103 then page #[0x4ca98c31bfed9a1a6053,0xf2dd9860d6318717ecc3,0xa558c61e5bb66cc2c630,0x736fd3326c18c38bf663,0xa9b2030e2fd98e998318,0x3db660d6364061adf36c,0x59590186b7ddaac6c80c,0x1adf766b2b2030f67985,0x30ac80c35beed9836406,0xd6f9b3e1990186b7ddb,0x1a3e1861adf36bc33203,0xc737bd4f4cc09038bf66,0xcb1b0298c3ffb86a5654,0x631bfed9a960531f5ab0,0x9e99814c797bcb70cc0a,0x318dff6cd4b0a98e6f4a,0xb3434c2631bf6dba1655,0x98c6ffb66a7854c637fd,0xe396e1931cdef2cd0f0c,0x54f1fbcc342432a74bf6,0x74c8922a9e3df9868c86,0x2a71bfee996259538fef,0xb86a56354e1ffdd3304c,0x953b79b644c306a9c3ff,0xdb3434c2a74bf6db98a1,0xab1e3fb986808558e37f,0xe61a621563c7bf30d190,0x558f0ffcc34e42ac78bf,0xf74cc130b1c77fba6549,0x1ac79bded9a12616387f,0x5b12618658ede6d9130c,0x4d81b1fb6e4c30cb1daf,0xfdb35229b039bd259a11,0x6c0e6fb966808360637,0xfe59a420d81cddf2cd11,0x8360733fcb34a41b039a,0xfb4fcb106c0e67f96a94,0x49b031bfeeb9620d81c9,0xffa8259536063efdd326,0x54d8197f360542a6c0e2,0x7edb752a9b032bf6d8a8,0x326c0c6feba259936063,0x3f69c9694d818dfd75cb,0xa5360637fdb35329b039,0xdef2cd0cc6c0e4fda7e5,0x3cab075bd6c4a3e5981c,0x6ffb66869894e37fdb34,0x858e6195f970d32a730c,0x73eda950b1cc33bd6c4a,0x1b0330cef5b1aa163986,0x3bd6c7a660e619de974b,0x8595a0e37edb752a9d03,0x8dfb73d330398c6fdb6e,0x52a9ec31bfee996d4731,0xe3ff986869854e1ffdc3,0xa1e0d539dff6cd0d30a9,0xe77fdb343c1aa78ffe61,0xcc2a6b0d3ffb865b9154,0x36fdee15360561adff6c,0x2a15360757fd412ca9b0,0x1b5fb6c542a6c0dbf9b0,0x306a9b032ffae8a854d8,0xfb5e85a0d53607b6fcb,0xb8654d81edbf2d41aa6c,0x737ed472ca9b032ffae,0x1cb2a6c0e6ffa8e59536,0x39bfe59a5a0d81d5ff5,0x3a168360797e4b50b41b,0x81cdff2cd2d26c0dbddb,0x4330a9cc35bf6d6a3e59,0x30dafcb8699539871ffd,0xc78654e61e5fb31c32a7,0x986f6ed9f0ca9cc37bd6,0xca9b0330cefdbae1953,0xe636fdee15360661f5ef,0xc14006400337fd332ac0,0x62c55044c3c035c2f821,0x789ec9608d48207946b8,0xcd48cbcc58bccb68b04a,0x2cfa0f3ced8e74e10da,0x112852211bd1590f5091,0xd59152d4c946540139d3,0x8ed88982579970d68161,0xf9b95b31acda419b5951,0xdf19eb5dd9d25cc1c5db,0x1d617210e0aa045fe1f7,0x824f646a3b632a29e23a,0x687a81678a6fe69a60e5,0x9ce99297e91a9068ca8b,0x72b5eb22ae6aaaa46a0a,0xec8ac4ec3abd6bc2baeb,0xd3ed2ad16d02cc6cb2c9,0x2f83e00added7ad66d52,0x102c0d941b44c164481a,0xa285f081b058a1430be,0xd1122a0fc1f004890502,0xb141b84fc305a12068c0,0xf0e120a061460ba10360,0x84c2a18558282de18345,0xf0c1a1835e1e0a6a13c3,0xf0c5506860de0a6a0c55,0xf802f050510360b0a83,0x7c105c7e] j else page #[0x80205bc10347e0f80206,0x7c01783e00bc1f005e0f,0x82080fc10385e07822f0,0x7c01783268bc193440cf,0x83e00bc1f005e08382f0,0x408782a48dc3f08141f,0x822f03c11783240bc1f0,0x40df800c0fc19205e07,0x4140586c4f83e00fc1f0,0x1220521710320a420307,0xfc21c15e18bc1f005e0b,0xbc3828523f81e18ec391,0x5e1a142f07c01783e00,0xc16050152783448bc1f0,0x7c0102a0a02fe182c507,0x83448bc10645e00302f0,0xbc1f005e0f802f07c017,0x87e0f802f03c11783e00,0xc4a201de0b0a3e17c112,0x81d181de0b0a364f85f0,0x7c3074607782c28e0d84,0xa305fc1c147e07822a1,0x92104921f07c0102fe0e,0x38141438484008492204,0x40140648083410681c10,0xa020a25051001448,0x486122000000001008] j)
def ecD10 (j : Nat) : Nat := (if j<412 then (if j<206 then (if j<103 then page #[0xbe58d901872fd9858c61,0xee19901876f96564061d,0xea5812072fd98e1861db,0x598320f75d9560c839fd,0xd8621a7dfa960c83db76,0x9321a6ffa961886d3f65,0x854e6ffa666131db7619,0x54e7f5a1261539fe6809,0x4e3fca8659539bf69898,0x66fda6e45538ffea1965,0x7f9a0261639bfe999858,0xeda2261639fd6849858e,0x786606619df6949858e7,0xa1e1a61cbf66386987af,0x5614319bfe9991e0eef5,0x618539ff6a5850c777d9,0x58539ff6a58614f6fd96,0x8539ffea19614e7ffa16,0x539ff6a68614f6fd96a1,0x1df764d531867fda1a60,0xbbf699531873fd9854c6,0xffa61531867fda954c61,0x760d631867ffa954c61c,0xe95631876fd9858c61fb,0x4d831876ffa958c61bbf,0xd8318777d9560c61df76,0x831873fd9860c61d7f65,0x318777e9560c619ff6a5,0x1877f95364061bbfe998,0x877f98564061dfe60d90,0x77dda864c61df7695931,0xefda3e1861cff68d9818,0xfda961463ddf6558518e,0xd95a14639ffea19518e7,0x9354c819ff6a68518f77,0x954c819ff6a5532077dd,0x60481fbde99812067ffa,0x4483dfd6959120f7f7a9,0x483ddf6859520f7f5a66,0x83dbf6859620f77da665,0x1df76959321b6fda5658,0xbfd684854c6ff9a02153,0xf768c854c6feda221531,0xf69c854c6efda621531b,0x6a5514c67fda921531b7,0x19634c6ff7a154d319ff,0x1634c77dd9858d31fb76,0x634c6ff7a158d31df7e6,0x54c67fda959531ff5e85,0x4c67ffa959531dbfe596,0xc7ef4a660531ff528d81,0x7fd56360531dfd2a5814,0x7f59560531efd619814c,0xfda960531dfd659814c7,0x78660531ff598d814c67,0x9660531dfde55814c7bf,0x360531bf7e8d814c77f7,0x60531bbfe99814c7fd7a,0x19319ff6a5854c7ef7a6,0x5319ffe85954c67fda96,0x319ffe99954c77f7a165,0x1dfde85964c67ffa8655,0x9ffea1964c67ffa56593,0xffe8d984c76fca666131,0xfe95984c77dfa3661319,0xe99984c67ffa6661319f,0x62634c76ffa666131bbf,0x6654c6ff5a199531df76,0x814c77f595a05319ff6a,0x54c67fda9a1531bfd6a2,0x4c6efda6a5531bfb68a9,0xc6fdda3d45319ff68698,0x6ff5a1d4d31bbf69b514,0xff5a1e0d31bf768f814c,0xfda9e1531bfd687854c6,0xda9e1931bfd687864c67,0xa6e5531dbfe5b864c67f,0x5e59319ff6a3954c67fd,0xe61319ff6a3964c67fda,0x19539ff69b984c67fda5,0x953bfd6848654eff9a02,0x539ff6a48654efdda321,0x39ffaa48654eff6a1219,0xdfd6449154f3ff982195,0xffaa49654f6fd9625953,0xe6809854f3fd98261539,0x6849854e7fda126153bf,0x849854eefda626153bfd,0x49854eefea626153bfda,0x6354e7fda958d539ffaa,0x354ef7fa558d53dbfe59,0x54ff5d8560d53ef72618,0x4e7fda960d53df765983,0xf7df9660d53fd7a15835,0xbdf9860d53cffe618354,0xfda961953dbf6598654f,0xca8659539ffaa58654e7,0x9665953cff2a19654ebf,0x3659539ffe859654f6ff,0x65953df7e8d9654e7ffa,0x5953affea19654e7ffa8,0x153cffe619854f3ffa86,0xe7ffa166] j else page #[0x7dd96a0d539ffe999854,0x5e85a0d53bf76a28354f,0xd96a1953df7e5a8354ff,0xa9a19539ff6a68654f6f,0x8a4553cffe628654e7fe,0xa4553affaa29154ebfda,0x6153dbfe5a9654f7f791,0xd53cffe629854e7fda1a,0x53dbfe5b6354ef7da5d8,0x3cffe638354ef7da5e0d,0x9ff6a78654efdda3e195,0xff69b9154e7fea9e1953,0xf69b9154eefda6e45539,0xa9b9154e7fda8e4553db,0x879654f6fea6e4553bbf,0x79854e7fda8e59539ff6,0x535867fda6e61539ff68,0x3586ff9a020d619ff6a4,0x586feda220d61bfd6848,0x86f7da520d61bef69083,0x6dfda720d61bbf698835,0xf7ea520d619ff6a48358,0xf7a6605619ffea553586,0xfa6661619ffe8d98587e,0xa994d61b7f69e535876f,0x1e0d619ff6a6835867fd,0x215639ff6a783586ff5a,0x1563bfd6848558eff9a0,0x563bf768c8558efeda22,0x63b7f69c8558eefda621,0x39ffaa48558e7fda9215,0xddf6549558f3ff982156,0xfe6809858f3fd9826163,0xd6849858e7fda126163b,0x6949858efeda226163bf,0x949858edfda726163bdf,0xd6558e7fea926163bdfa,0x8358fbdc9860d63bf7e8,0x358e7fda960d63fb7619,0x58f7df9560d63fb7a198,0x8fbdf9860d63cffe6183,0xe7fea961563bf7e85835,0x3ff9861963ebf2618658,0xfca865563ebfe618658f,0xf9866163affea19558eb,0xa5661639ffe859858f3f,0x599563bf768e6558e7ff,0xa0d63fb761a8358f77f9,0xd63bf76a28358efdda1,0x563df7e568358fede86a,0x639ffaa68558e7fda9a1,0x3bbf6a28658f3ff98a15,0x9ff6869858f77f95a556,0xbf69b8358f3ff98a6163,0x768f8558f3ff98e0d63b,0x6a78558eefda6e1563bf,0x8f8658e7fea9e15639ff,0x79158f3ff98e1963bf76,0x9558e7fda8e45639ff69,0x558e7fda1e5563dbf61b,0x58f6fe86e55639ff6a39,0x67fda5e61639ff68798,0x6ff5a114d81dbf258536,0x7fea914d819ff6a45360,0xf9a020d81dbfe5853606,0xda420d81bfb68883606f,0xa620d81bdf69483606fb,0x520d81b7f69c83606efd,0x20d819ffaa483606f7ea,0x4d81dbf258936076ff96,0x981dbfe58936077dd932,0x81dbf25953606efea925,0x19ff2a553606bfca854d,0xdbfe59536067fea954d8,0xffea553606bffa854d81,0xf619636067fca958d819,0xe59636067fea958d81eb,0x59836067ffa958d81dbf,0x9836077df9360d81dbf2,0x86607aff8661981dbfe5,0x3607aff9661981dbfe59,0x6076ff9664d81dbf2599,0x76fc9694d81bbfe9993,0x6dfda794d81bfd686536,0x7fea994d819ff6a65360,0xf5a198d81dbfe5a53606,0xea998d819ff6a663606f,0x96a0d81dbfe5a636067f,0x3a0d81bfd686836076fc,0xa4d81dbfe5a836077df9,0x4d81bbf69a936076fc96,0x581dbfe5a936077df93a,0x81fbde5b816076ff96e0,0x1ebfe5b866076ff96e0d,0x9ff697936076fc96e4d8,0xbfe5b936067fda6e4d81,0xf687966076fca3e5981d,0x68f966067fda3e5981db,0x87966076fea3e5981dbf,0xf96607ef7a1e5981dbfe,0x9160eefca664583dbfe8,0x660efdda3a1583bbfe99,0x3bf768e8] j) else (if j<309 then page #[0x9ff69b9160e7fda5e458,0xff69b9560e7fda1e5583,0xf6979660e7fda1e59839,0x6879361a7fda3e45869f,0x55538c67fda5e4d869ff,0x5818c6ff7a154e31ddf6,0x838c7ef7a660631dfd65,0x48c67fda961631cff661,0x8c77bf8565231def6159,0xc73fd98e0e319ffe9598,0x6ff5a1e1631bfd687838,0x6fd96596539ff6a7858c,0xdd9660e53bf7e8d6594f,0xd9661a53cff6618594f7,0xa961a53d7f65d8694f6f,0x865a539ffe859694e7fd,0xa1a53dbf65a8694e7ffa,0x62539ff6a68694f5fd97,0x653dbf65b6594e7fda1a,0x61bbf69953986fdda3d9,0x19ffea5539867fda954e,0xfb760d63986efca858e6,0xbfaa1639876fd9858e61,0xfe9563987ef7a158e61b,0x64d81987ef56360661bb,0x9981987ef78660661dfd,0x9839867fda960e61fbde,0x989867ffa366261bbfe9,0x3986ff5a1e0e61dbfe99,0x9876fd98e1a619ff6a78,0x86efda3e1a61fbd68786,0xf7dd9560e63dbf6a7869,0x7fda961663ddf6558598,0xffa165663cff6618698e,0xda3996639ffea19598e7,0xa9a1663ddf6568598efd,0x954e819ff6869898e7fd,0x60e819ffea553a067fda,0x5683dbf65986a0f7dd93,0xa839ffe9995a0e7ffa16,0x839ffe9596a0e7ffa165,0x3dbf65a86a0efdda3a16,0x9ffe9593a1afdda3a1a8,0xf766163cc7edd8658f31,0xf6a565cc76fd9659731d,0x65981cc67ffa9597319f,0x6181cc73fd9860731dbf,0x981cc6fdfa360731cffa,0x85cc777d9561731bbfe9,0x5cc67fda961731dbf659,0xcc76fd9661b31dbfa598,0xc67ffa6657319ff6a586,0x76fca565b319ffea195c,0x6fda565b31dbf68596cc,0xfea565b31dbf6a196cc7,0xfa565b31dbfe8596cc76,0xa865b31dbfe9596cc67f,0x699731dbfea196cc67ff,0xa17319ff6a665cc76fd9,0x1731dbf65a85cc777d95,0x731dbfa5a85cc67fda9a,0x61bf768f51cc76fd96d4,0x19ff6a453d86ff5a114f,0x9ffea553d867fda954f6,0xff6a583d877dd9360f61,0xfea193d867ffa564f619,0x6a653d86dfda794f619f,0xa683d877dd93a0f619ff,0x585d8f3fd9860f639ff6,0x95d8e7fda961763ddf65,0x5d8e7ffa865763dbf619,0xe067fda9a1763ddf6568,0x67fda954f81df764d53,0x67ffa954f81affea153e,0x7dd9358f81ebf61963e0,0xfda958f81dbf65963e07,0xca6647839ffea563e067,0xa6647839ffe9591e0f6f,0x664783bbfe9991e0e7ff,0x60c619ffe8d91e1b6ffa,0x531ffd615814c77fd95,0x531dff661854c7ff6856,0x31ffd616814c77ff9861,0x1bff6a2854c77fd98a15,0xbff696984c77ff98a153,0xff697814c6ffda8d4531,0xf697864c6ffda5e0d31b,0xe856354effda126153bf,0x869854efffa165953bff,0x78654effda1e0d53bff6,0x9154f7fd63e4553bff68,0x154f7fd96e4553dff61b,0x587fdd8354d61bff69b9,0x86ffda854d61dff66153,0x6fffa854d61ff7a0d535,0xffda594d61ffd54d8158,0xfc9654d81bff69683586,0xd8354d81eff2a153607e,0xa854d81eff61953607fd,0x654d81ff7a0d53606ffd,0x54d81dffe5953607bff8,0x4d81bffea153607eff96,0x7bffa85] j else page #[0x6ffda5a0d81bff696536,0xffda5a4d81effa168360,0xfda5a4583bff6868560e,0xd9560e31bff6869560ef,0x8354e61dff6159194f7f,0x654e61dff66153987fdd,0x54e61bff6a153987efda,0x661bffea153987eff86,0xe81dff65583987ff5536,0x81bff6a153a07fdd8354,0x3dff65583a06fffa854e,0xeffa1a85a0f7fe856468,0x6d006400037fd9560731,0xc58159024e038c04f80,0x9f0125021803de06f4,0xe707460d5819202f2058,0x27504b8090c115021103,0x418f82fd05ad0ad21470,0xa00ea61ccc37786bd0d0,0x45f088c10b420583ed87,0x627044be8954124423c0,0xdb156429dc5198a1313e,0x5ea8ba316f42d205820a,0xc331864e8c59184e2ff8,0x41b92365c6ae0d2a19c,0x7760eb11d2239a071b0e,0xa404c7e78fa61ec43c78,0x63226243b485d9077208,0x9451258244c47888cf11,0x4d1499292fc25a64acc,0x5628364fec9f213b2270,0xa9a94f1297e5234a3b14,0x5778adf159e2aea5554,0xef2d9e5a2cb2396302c2,0xbfd97c02f2e5d04b8c16,0x66440c6198a330ac60fc,0xfd339666accc5996b329,0xd651aaa3514693cd1319,0xe6e38db71b45364a6c14,0xd5396a71a0e169be0376,0xef99d9d3afa7508e7f1c,0x7bd8f621e923cc078b8,0xec3faa7eb0fc61f5a3e5,0x53a07e40bc808d0019f,0xc86cd0c5214f42168365,0xfa459089ed124a21743d,0x1eca39546c68ce918d22,0x292e124c246f487a9075,0xdb4b7696012a2a50a49c,0x354267f4cbe98b5306a5,0x29e1d3aaa7354e069b45,0xbc5114a119405a7eb4f7,0x4d2298452a4a43947728,0x6aa7953aaa435446a77d,0xdc571ead2d595ab0b55d,0x654ac8058c0b10160bab,0xeb6b16b8ad3f5a2cb349,0x995d04b9417182e105bc,0x7c0af585e3abbf57612e,0xcc1a5820300e5fcabef1,0x8c62d8c50d891b0fa616,0x935b24b6432c7c18e3b1,0xcd7199532f8659eca51,0x7f68bed0fda0233d2674,0xaca35506a3cd3b1a6634,0x6dac9b44b63c6c02d761,0xba6f10dd7db96b7046db,0xc5eb89470b2e0c1bfab7,0xae76dcd4b9777254e3e1,0x347604eb41d4f3a5a741,0xe1bbc057770ee61dbc3b,0xaf5c1e963cfa7990f1c9,0xf67d76f9ddf1e3e017b7,0xebfd97f3cfd8df98be,0xf03f2060c0a180f10186,0x70847d07ea0d6c160826,0x1ddc36e86670b9a15a42,0xb12b2241c451881b0f6e,0xbd8b29158a29cc52289a,0x37fc6df8d37193a300c5,0xb200a3f147a78eeb1d0e,0x40920b239645e4881907,0x50fc9f693ad264a4b949,0xf2c1e56f4aac9507298e,0x697a92ed25c14b3e964,0x67bccaa98f1311a6134c,0xd392e715cdde9b2334ee,0x899eaf3d027874ec19d0,0x84f506ca0753fda7ddcf,0x5473a8c55158a23b438a,0xfaa5a34a7e936d244a42,0xa0353dda7574d9e9a3d2,0xb546ea7954c9a90b50e2,0x23ac07576aacfd56daa9,0xb8156c7ad6159d6b2ad6,0xd6016bee5798aef15cd2,0xdb1b762eec40584eb05,0xcf659c3b323655ac96d9,0xd6b52d4cda5eb46b6832,0xdcb7796e2adac5b2fb60,0xe66dca4b8d37102dfe5b,0x57766ed3dd6cba757422,0xede2bbc0] j)) else (if j<618 then (if j<515 then page #[0xdeef9bdef3bd717a62f2,0xc14581e701adffabf917,0x961c0c32f854f090e0ef,0xb231546264c489884b0f,0xc7df8e8b1af632cc6078,0x764b3c92791cf229e421,0x8332e4658dca93945f27,0xcdd79ae733ae643cc479,0x2e7dccf679de33a7e71d,0x46b478e8add0f7a0bb40,0xd483a81b4e1697ed287a,0x66b83d67fac5b56dea8e,0xc7611ec0cd7d9af335d,0xd95bb25b63fec68d8a3b,0xded3bda37b3ef66decc4,0x8376fb6dd6db7fb6136a,0xdd25b9ef72dee4ddc6db,0xe6f05ddddbb5f7576e97,0xef37ce6f7cdea7bcf378,0xe0b9c0f380e6ffcdfcbb,0xe7105e1cbc317857708e,0x6878c5717ce2b9c4cf88,0xe45fc83f8f371d8e383c,0x7f2cfe54dca1b9337246,0x305b8630e1048bcc3f97,0xfc309942c09a170c6012,0x4e254282f0c2c70b5085,0x1424d2485e170c2c7144,0x87c20a142bc3e1034285,0xa142c15e1f082850b057,0xc20a0351840b05787c20,0x81a1428541bc3e1050b,0x88662821e1f08e15e1f,0x8414285b86c20a850a27,0x5785c30b050a160af0f,0x70883e9b88c3f0b86164,0xf8460883f118712f0f84,0x109b860d289e8a191370,0x6162a3786c20a850a27e,0x3784c30a054a150a70b8,0xfe1f09014e105786162e,0x85c3069c2c5506950321,0x9510bc3e1203a192a953,0x50cc5387c238582e0e2a,0x91c243a37860f38422b4,0xb942687e1237860f3028,0xc20a70c207e122386140,0x23868838382e30701511,0xa124c09070142107e14,0x87e170c9a60451785c3,0x401308e1f08240e38401,0x2090a0a89e1f08261e28,0xa1689c4b8625282787c,0x1f0826142a2787c20907,0x4160d9c34090d888889e,0xf84121814501405e178,0x74286c463e1c485030b7,0x83660d52113c30970822,0x10482c8c204c1fc30970,0x212e1044e05e106c5e4e,0xd13c209054a0f0470d1,0x2e18485050d70ca98527,0xc3430250a121b1790134,0x89e13c3e104c3c504f0,0x41b179034c8e1c2425c2,0xa37860f3e14a81b18278,0x20a237860f282891c243,0x9050403e0fc2e1c34dc,0x421f85c3469b848de185,0x80f2f0f848d09850a0f0,0x8f85c30a2349c3e12342,0xfe1f082a14069a2b140f,0x8240e385787c209064a1,0x1854240f3935901ce1f0,0x7e170c2a20206193c2e,0xc2e50e32385c30b0482,0xe1f08290d08960fc20af,0x3250e85113c36104c3c7,0xb0f84130f1c91c3e1050,0x6e1f0828130d943a14c4,0x8261e38582fc3e104c28,0x10502611387429892370,0x87e1437861c284013c3e,0x83c17203e0fc207078a,0x3e107a1a4e107a1a3e1f,0x832110b8e0fc20f0349c,0xe1874a110570a1bc30e1,0x408e1f0a1a1e2844100d,0xb0481c60b0385830a064,0x22017083c19185787c20,0xf041c50984815c10c943,0x8e1f0a1a12071c380a06,0x38140c8f84120c8c1e0,0x21f04321d18b02a12141,0x868782f0b82192c341c1,0xe170c387070b04170744,0xa08e170c3a7088401c09,0x7041c446f0c6230883e1,0xc2e1a51bc1080648110e,0x42e4080200e110783b1b,0x881f850de1870c0e06f0,0x820883c43c286f0c3a70,0x41140385] j else page #[0x642230803c1208e1a1f8,0x48441c08e170c388090,0x2430782385c346840c10,0x4848323048385830883a,0x1c3e14343c5038384030,0x341c12243786120e109,0xe18401213e170c386e1,0xd1a0e30441d12184424,0xe890e1a0e090c1e08e17,0x41c121844260e09102e0,0xe105032408f081c12243,0xf040278614e104500f,0x8391c20e01c1bc107182,0x4108c241107823850de1,0xf84123a37821d0d13871,0x107386193040120807f0,0x5c30e2782190e8c2207e,0x34206088401c09038178,0xe1b089a14283c11c2e1a,0x9a11293787c20a068a88,0xf0f844d0a03cbc3e1050,0xc226850a49e1f0826142,0x7061186073874d2e2387,0xb0e88934508870845088,0x501c6e1870443088c441,0xc270c382218582bc3e10,0x11c3e11342850d70c441,0x1f08287c470f844d0a17,0xc226f0c386080380a1ae,0x1c38607c1c3a1b202a0f,0x58478414204387c2894,0x841b0e943bc3e1070285,0x240a14e170c1e80e02b,0x1d187787c20e050a1007,0x8381b270822141f0836,0x30e1c1417e1860385e1f,0x31c30b9c22100701785c,0xe143411188c38080d708,0xc500060384e1f082e180,0x103dc00d8609c10705c6,0x70e70b8625305c00180e,0xc1008d3785c30e18238,0x446230570f84170c07,0x21a0b8c200e04f0c6250,0xf082838902b86180e178,0xc3838749c2e1c1c5040d,0xc38505517861b0e1439,0x30d14121b0e8c23c226f,0x9bc3e1048385a687037c,0x1888383e1f089a140794,0x60e386823c262f0c386e,0xb861c28441e05e105b8,0x81f0f844d0c070a11a4f,0x1408e170e0e1a3878341,0x1050749e170c38112844,0x870701787c20a068c1be,0x40323080380b49e1f082,0x31890200e26f0c625e08,0x3c1c0701785c340389bc,0x6f0c6230d06c44308024,0xbc3e106c347e08382e32,0x381207e170c388080380,0x881f841ce185cc11080,0x4616468607c246f0c3a4,0xc6902cc30c6349c10723,0xe47e105b878d385b8618,0x1331a50b70c208d20541,0xf047091bc307188fc20b,0xc3a42411f8416e1e34c0,0x886060ee08347c246f0,0x1a26103431c2e1884bc0,0x1237860e37091bc30e93,0xbc307181dc1468c1e08e,0x1b86c20a08480f047091,0x20a084848e1864a7c20a,0x828172f0f8414109187c,0x8208dc20a084848e1f0,0x1e38441c48e194f8414,0x778748203b861429f089,0x8e184028424074303088,0x385c307234c1d0f08c6c,0xf08c819e08744640782,0x46310877861e11943ac3,0x1050dc3e10504240e878,0xf0ec343040783b8621e,0x82825285817c208874a,0x40511bc2e1840e1ce1f,0x822728718a14e106ca0f,0x5238707e1044d07e10a3,0x48e10511a30e84446308,0x5061c0701c0a1ee170c3,0x12846910de1840bc30b8,0x841708858e180a427862,0x70f841d0d85ce0fa470f,0x8d07182348e184080fa4,0x11c2e187100f0470b86,0x20221bc30e901c050884,0x81ce18584040d434301d,0x4823c20a143dc209064,0x1283870bc346c1c4e40e,0x81c53e1f08301c306387,0xe1d2080ee114c91c30e1,0x8183c1d] j) else (if j<721 then page #[0x21b0e86081ce170c1a14,0x874a0f0470b868d07184,0x20e0460e10404691c2e1,0x91c30c7082250491787c,0x185c2850a03c3a110b16,0x802f0c29c208a01fc2e,0xc1c05a470f8414383c1c,0xe1840a070e704210d283,0xe11e1437861c2d20370d,0x8461e0783811c2e1c34,0xc2e1871008070907c30e,0xc39c30d141c050f07411,0x483c11c2e1a341c66286,0x1108038120702f0b861c,0x824192d2387c28a234a,0x492387c209038e08e1f,0x4050802491c3e111d010,0x181d050c52387c28a1c1,0x509058c1f6170c2a120b,0x85c30a8482c70ff09861,0x7f85c30a8482c60f811,0x4c0b143fc2e185424163,0xf87c2240482c60ff0824,0x8a9c3fc20af0c2416307,0x514469c200ea3f081bc3,0x8b48120c883416a470f8,0xc3141b820e0f8e8fc2e1,0x786150a094c160da3785,0xe187100ae18944440b01,0xfc3e1202210050240bc2,0x17861c384215050cd228,0x70278631285f121ee00,0xa0f0502013c31288ce10,0xf0a1a184078420de1894,0x20e8604260883c1408e1,0x1007e170e1a0e401f87c,0x3f08365e14503630b83c,0x480cc1787c28a1c380e2,0x583040af0c1a140b143b,0x20da20bc30c85c81ce18,0x1c2c106a240ea423787c,0x170e281a2837820e1290,0x9c2091c1fc20906488de,0xf841207205820c48989,0xe70f841240401e0804f,0xa18e1f0a2870a0401208,0x8481c70711c4a3075220,0x3e111c6050782387c286,0x628682f0f8514109413c,0x370824191d2051c2e1a3,0x7c28a1c3847e1883801e,0x23868da5981d48828638,0x20c8c1bc10709481a8a5,0xb140752387c20c184a1,0x3c541b141c5787c282c5,0x60d18401d1506f0f8514,0x70c3870770b862d20678,0x4e006c303070440fc20d,0x787c24a084a0ee170c5a,0x8c3430342f041c17221,0x90850c70f84943860322,0x6a50695e1f081a942839,0x3141f0f841d0c084a950,0xa1f841b2f0823141f082,0xf40710fc226844a08e1,0x207080240a0ee1f0828,0x470c1c90782387c22685,0x14082024110803c13c20,0x7860e4038100507f0f84,0x868423090441e08e113,0xa0e303c1016e170e1a6e,0x82dc307a01e08e170d1,0xe12360e1c28380e0508f,0x5a0de084c385110785c3,0x12342260761f85c31694,0x13e1237860f3d238707e,0x50a9486c2f861328440e,0xe1437860f384e09c386a,0x548e1a37841130440e13,0x850a1f0e708288d08982,0x7a470b868d387c1fc246,0x8bc2080710e1a383c220,0x10508928470c301c2c22,0xe503f0a11c30794241ce,0x5119c21013841ce18502,0x70200a1ce1f08281040,0xb07e170c347838382e3,0x6928bc3e105034508038,0x4de1f08281a2f08288ca,0xc200f0402787c2090390,0x10928a85e1f0838870d1,0x38589f0e241d270c3887,0xa951bc3188c23c246f0c,0xc286f044e60491b87122,0x48aa3e1f08242720508f,0x2138f87c20e848425e1c,0x441f0c85b8612139b871,0x285b8455e1834a860906,0x7c246844f050b704321d,0x844fc32a084612078238,0x10e86480f0404b87c286,0x4321d182782190e920bc,0xc1a542f0] j else page #[0xb15785c342950dc22af0,0xbc2e1a14a85e1e14a830,0x70b86140d1037c20a0ca,0xc308141c05e1f08281a3,0x847c246f0c4e403f0a1b,0x70e10901b0d0609c30e0,0x1c05e1a1f841b370c908,0x9070a0f0470b868d0718,0x2446f0c2431223787c20,0x7385c30a05ca8d097082,0x30e86861007027863128,0x83907e1868f070705c7c,0xa190e18e185480e8970,0xbc34389c9c20d0878649,0x5ca1103f0a1bc30e189,0x3e1f08290d285b87c20a,0xc385047090e0de1874c2,0x270f850d13110fc286f0,0x7c286a1c1c50b7041c25,0x89460a03f0a1bc3071b8,0x7c445387c282860c0e43,0x82870702891c243f0c34,0xa70c1e8a44143a19e1f0,0xc346850a10070240bc20,0xc1449e121f8621352385,0xd101e08e170e1a14081,0x20807f0f85074237821d,0x943307e170c4e5080381,0x20ef0c2e706f083bc310,0xcbc2e18504240cb220fc,0x2f041c171c1f841de1a4,0xfc10c884607e1437861c,0x86460f0470f850d83874,0x4a470f840d43874dc10e,0x7864843870a072406034,0x44143a19e170c2948387,0x507838200943f0b8648,0x1785c3139785c3468529,0x303e2440386f0c62343c,0x415c246f0c386e085c46,0xe10451a51086c3420204,0xc0f0470f848d089c8e1c,0x858e1103f0a1bc30e182,0x3c488041107c378421e1,0xf861c4691c2c5e08684a,0x89422070782385c3469,0xc8d07f0c2c5e1c1f848d,0x8602c446f0b86160c143,0x40f61f850de1870dc306,0x387c24686088d2470c38,0xe1f08280f403b841b0a1,0x3890bf0c385080381205,0x10200e0481787c20a1c2,0x6e1070290d207386170b,0xa1a11387387c20684028,0x470b870d383c1014e1f0,0x15e170c1c4d30400e0f0,0x4200902f082bc307a035,0x883c1408e170c9a10404,0xc1f20662b45e1f0a2860,0x2029c3e143422704f041,0x20741c6130903c364078,0x204890789c6120741c61,0x120709121c108c2a1078,0x708240e11201c20e0204,0x1c38483c423090384120,0x10389a30384c92311070,0x44942838c0a249141e41,0x44200d185c1c20983c1,0x4d10c4200d24902c101,0x381a21103c1c324042,0x81a20b0381b09203b1a2,0xa4287060e0f881c0d103,0x14619428582e40d89441,0xa44c14822050a061a070,0xa06890707c6190808320,0x50d038a1a0507060e028,0xe0a851068260e1888140,0x808882411070c3448070,0x3c6130781c2242284444,0x24110c321d1074212070,0x40338d212821908085c,0x248184c1e2848643a30a,0x380a1c18380a3118c42,0xc3090381030983c0e112,0x868541c31409c4] j)))
def ecH10 := page #[0xaa04010178e0e0000100,0x9540a2e003020214b820,0xda0b3cdc00e261c36137,0xc33f1f529aed00073a28,0x157101262a331c147601,0x7d5cb8b352d6b80a0447,0xb3838f321f2896dd5b28,0x3d790a6035d33e424125,0x23906703f36c5059467,0xf56932258bddc4b5da05,0x3b508e45f59b0c34fc66,0xe6e114e3142f642c631,0x72300d31a309000a2d00,0x941a070000006628a8,0x8c1ec36000000000c350,0xea7d64a4c53c251b0ee6,0xd55465b0f83789e957,0xc4dddf00000011ba4e0,0x5ea48000930a1700,0x6174342a31185ae00f70,0xa1886f63400014a0,0x620303e54b4900000000,0x86ad12000853,0x2a1d0009408e655f0000,0x36900000000091300052,0x2d7192782b000dbb606,0x6c8aa2e00000051982c0,918657]
def ecD11 (j : Nat) : Nat := (if j<206 then (if j<103 then page #[0x94186fbb2630dfe64061,0xdf7a4c619fecc0c37bd,0xcc81077bd942067fd303,0x20efdb2441dfd64483bf,0xbf65883bbeca9077bd94,0xa9077f69120ebfb2e41d,0xaff320435bfa5883bbf4,0x65086beec990d7f59121,0x37de9321afed22435ef,0x7b2918dbfe5981b7e4b3,0xb31b7ecb6635fd9794ef,0x7fd980c6ffb2a18dbfa5,0x2c29dff64453bff4c063,0x1bff4c0a77fd9814effb,0xd98186ffb2630fbf58c6,0x31fbfe1861bff4c0c37f,0xff4c0c77fd9818effb2a,0x8206ffb2640ffd60481b,0xdff64483feec19077fe9,0x4c1077fd9620effb2a41,0x1affb26437bf61886bff,0x758d31bfe4c2637fe982,0x2637fd954c7feb0298ff,0xfbcc698dff66131bfecb,0x5531bff4c263ff6814c7,0x77ff984c6fff2c98dffe,0xb2ca9ff760d53bfe4c2a,0x53fef41aa77fd9854eff,0xff9654efff22a9dffa61,0xb0ffd60561bffcc2a77,0xbfe4c2c77fe98586ffb3,0x9858fdfb0cb1ff760d63,0x1fbfa1963fef41ac77fd,0xfcaac77ff9158effd30b,0x607df92cc0dffe6163bf,0xffe1981ffbc0b03bfd86,0xb3037ff96606fff26c0e,0xefff22c1ff7e0d83f7fc,0xe1986bffcb3077ff9560,0x637ff9361afff22c37bf,0xfb2b18dff64e31ffac0c,0xe53bff4c4637fd988c6f,0x7fd9594effb2329ff760,0x3129dff66253bfecb4a7,0x1ffac0cc3efd63986ffd,0xe98986ffb3130dff64e6,0x31ff760e63f7fc34c37f,0xfecb4c77fd9598effb23,0x3a06ffd3131dff66263b,0xffde0681bfecc5037fd9,0xcb5077fd95a0effb2341,0x1bfbf0741dff66283bfe,0xfe1a86bfecc50d7fd93a,0x6637fd95cc7fbac798fb,0xffd3198dff66331bfecb,0x6361bfecc6c37fd93d86,0x77fd95d8fdfb0db1dffa,0xb0dc0dffa6363bfecc6c,0x81bfecb7037fd93e077f,0xfd95e0effb23c1effe1b,0x7c35ff64786bfecb7077,0xffec30a7ffd850c6ffb2,0x83187ffaa630fffa1853,0xfffa1463ffec28c7ffd,0xea8a63ffc854c7ffaa64,0x4c7ffac698fff54d31ff,0xff60d31ffec0a63ffd65,0xaa63ffd864c7ffb0a98f,0x7ffb3098fff65931ffec,0xa5531fff42a63ffe654c,0x63fff514c7ffd3098fff,0xff0698fffe0531fffa9a,0x953fffc3263fff854c7f,0xffc9654fff922a9fff21,0x6a9fff58d53ffe4c2a7,0x3ffec8aa7ffd8654fffb,0xe8654fffb30a9fff6595,0xa9fffa5953fff48aa7ff,0xffc1aa7fff6354fffd30,0x654ffff22a9fffe1953f,0xfff14d61fffcc2a7fff9,0xc1ac3ffd53587ff906b0,0x87ffd06b0fff94d61ffe,0xf25563ffe42ac7fff835,0xac7ffd6558fff930b1ff,0xffb0cb1fff61563ffec1,0x6163ffecaac7ffd9158f,0x7ffe8558fffccab1fff6,0xf06b1fffa6163fff4aac,0x63fffc32c7fff8558fff,0xff9858ffff2ab1fffe45,0x6c0fff20d81ffe29b03f,0xffeb1b03ffd53607ff92,0x93607ffb0cc0fff60d81,0xfff94d81ffecb303ffd,0xf49b03ffe83607ffcc6c,0x607fff06c0fffe0581ff,0xffe5981fffc9b03fff86,0x8b07ffd8660fffb0ac1f,0xfffb2cc1fff65583ffec,0xa4583fff43307ffe8560,0xdffe9660fffd2ac1fff,0x86ffec8b] j else page #[0xfd538c7ffd26c37ff64d,0x718fff61631ffec1c63f,0xffeb2ca7fff858c7fff0,0x8694fffb0d29fff61653,0xfff54e61fffb2ca7ffe,0xec2cc7fff83987ffb073,0x98fffccb31fff61a63ff,0xff60e81ffea9d03ffe85,0x2d07ffd86a0ffff0740f,0x7ffacb98fffa1a83fff4,0x61b31ffec2e63ffd81cc,0x63ffe85cc7ffccb98fff,0xfaa7b0fff14f61fffa8e,0xf61fff29ec3ffd83d87f,0xffd85d8fffb07b1fffa0,0xc7c0fff54f81fff42ec7,0x6fff48f07ffd91e0fffa,0xaf00f400f40007ff6478,0xd8018302bc04a407600,0xc0ae4142024f04340794,0xcf07440dd41a4031305c,0x254048308ac10841fe03,0xc15c42a2051709d41314,0xbf0cf418f430005d30b4,0x3ec07a30ebc1ca437a06,0xc2344452087710942054,0xf13a426544ac092b11f,0x5880acb153c29c45220a,0xc31e46160be717342d34,0xc71b1435346840cdb194,0x7a00f031d6c39a47120d,0xc42e483a101f1f843dd4,0x6f243447148c4112b21f,0x9d81353261c4b6495212,0xc53a4a56147728644ff4,0x472c045714acc156b2a5,0xbbc17432dfc5ac4b3e16,0xc6224c2a18272fd45eb4,0x733a46674cac1913318,0xd941af3358c6a24d261a,0xc70e4e021bc737246d54,0x8f3a947434e701ca338d,0xf601e833c8c7864eee1d,0xc7f44fca1f573e347bb4,0x3f41f4831504c204b400,0x12c221b43cc86a50be21,0xc8e051a222ff458489f5,0xd74924915521423f3476,0x30025db4afc950528a24,0xc9be536a26a74cd498d5,0x4f50449fd53e8279b4ec,0x4c4294b521ca38545228,0xcabc555a2a5f53f4a715,0x4757f4af355c02b3b561,0x6ac2d1b59ccb3056462c,0xcb9a57162df75b74b615,0xa75ea4bc9577c2ebb5d2,0x858307b608cc0457ee2f,0xcc7a58d6316f6254c375,0x476604cb159443253643,0xa2c342367cccea59c233,0xcd685ab234f76964d215,0xf6dc4dab5b38363b6b9,0xc3038236fccdee5ba237,0xce5e5ca6390f71b4e255,0xd77504e955d183a03739,0xde83b9b76eced05d823a,0xcf365e4e3c5f7844eff5,0x177bd4f6d5ebc3d3b7a1,0xf9c3f0b7dacfa65f263e,0xd01060063fc77f34fd95,0xb782f504f608040ab80d,0x18842e3853d09a610e41,0xd10461ea439f86e50d16,0x878a951456268448b887,0xb09892102e1849e2da45,0x61661613120905c3c238,0x48170b0c24e2c26120b8,0xa098482e183e11c584c,0x1b8616415090514c3c23,0x3e1e1184858570c2ca2a,0x1216154307c23090b0a8,0x1f0f08c242c2a0e09866,0x890b0a83e1e118485854,0xf85861a5121607c20c2,0x1869448581c230f08c2a,0xa5151442c30d28a83e16,0x54530b0c34a2a2985861,0x40905c3c230a86e18590,0xb0c3482a0f85861a5151,0x130dc30b206e1e10c5b0,0x141f0f08a28240f84185,0x2c31330a03e161869452,0x4a1187841a2850a0d07c,0x68461e1091c1f08370c5,0xa1207c208c3253900a2,0x58c564c1225878410288,0x619861091814201f0b0c,0x2c8161309c3c2123058b,0xf0850c501226240b8586,0x9c96142e18b1c2414570,0xa2850a1cc3c2070d3144,0xa1187841] j) else (if j<309 then page #[0xe10a868a141f08370c54,0x841a28508c3c20d142e1,0x1091f0f08585450a2b87,0x7c2c315390028b0ae1e,0x22a240f85862c7271612,0xe18b1414581f0b0c54c4,0x28515c3c20d1428a8a06,0x5b0b0c544902b85861a,0x38889611861869c1c181,0x71e050a1912c3c22f48,0x221c151a26258586509,0x17a44428204b089f0c35,0xd1228a090884048ce1e1,0x262985861a24630c3c20,0xe61e10920505b0b0c54a,0x27c2c30d123850310468,0x61028411b87842470a08,0x201c18101458570f0851,0x8388840a14616198a024,0x9880a87111c4d25c3c24,0xe2a28120a2251858662,0x1e10a188848570f081ca,0x719c24dc3314828a8b6,0xb0f103585864ab090a08,0x5308a30c894100e36140,0x93616186a01c24147820,0x72726c2c30d412870513,0xc5962b87841a28516080,0xc24201c18101454530b0,0xc32150388848a6161981,0x642a2725071e0d1416c2,0xc0c4e4a22100a2c29858,0x6113e18698485b0f081c,0x1a8051415c2c31630d8a,0xb0cc160e141057846186,0x824ac903c241c2a361f0,0xd304838f04468a61619,0x24185861a8162d2cc2c3,0x170854530c58c4a322c4,0x3304128c8a8a6161869c,0x85861a70508118d14c2c,0x434b70f08b0a100e4e4d,0x4dc3c2143e18b0ae10a1,0xa4c9035878428808260e,0x8b1820170c870850c120,0xdc2c3164c2e10a8a61,0x8e6585862c8282108072,0x8785308c30c34c100a22,0xdc31338a09e186e1091,0xe263d85861a71c0a87c2,0xe10a1b08570c3450a610,0x44d88c3c212393441461,0x141210240e5187849201,0x28684a230c97081d044,0x153130489441461e10a2,0xf864f842460516c3c207,0x9464589c9b0b0c350120,0x30d38f0509e1e106891c,0x87841a28527071326c2c,0x10a14255709530e14c2b,0x80dc330c212384e1986,0xc34e151b87840e6060a,0xe198610a1828201f089f,0x2460515c3c2071630446,0x4530b0c34e2827861b84,0x1238ae1e1068a1494385,0x451864480820144dc3c2,0x941f0b0c8521210240f8,0xa8961e10a1c9c242048,0x861a715c3c207162930b,0x308370c58e221029844f,0xd2e10ae1868a14a0545,0xa0f845186447c20730c3,0x1c201c509f0b0c34e151,0x2c315318841346e1e10a,0x103d8461861a8168d07c,0x4201c8308370c5928e14,0xc31630ae161868a14a08,0x491844d861a81e87c20d,0x207a1f08370c58e0e1e1,0x20dc31638ae161868a14,0x4c2b1b8784286281514c,0x68a10a0545308370c58e,0x9151914c2c325461618,0x5900a2d0e6185862a705,0x61869c20146e1c870b0c,0x58dc3c21430b870a8a61,0xc1e2b851b8628267181,0x461a68a1458530b0e208,0xe8090c0bc2c312283e14,0x3450e171036291387845,0x61c6a40a143d20570b0e,0x3cb0c0b8dc2c3121c3e1,0x403a282512161b878426,0xde1e1090f18344c48388,0x45e71207c20d1e243040,0x344838bca1e10241b878,0x2fc2c36e1090a089028,0x615120e89490f48871e3,0xf084878c2d8625845440,0xe2f28906871210644f0,0x4d4258784905e50d1412,0x84530b0c] j else page #[0xe1e1090f1c492624bc78,0x1c748c3c2121928c8586,0xf084878e281187841a24,0x461e10689071c2c206f0,0x43cc4814c3c2121b3052,0x3a1e1d1292902429878,0x3920704a230f08345144,0x118605a6e1e10a0d1e48,0x8a1186509a364454dc33,0x3e10f24291508302f0c8,0x14113128807848904618,0xa8a3d0e2d85865090807,0x883848684f0b0c711110,0x4113120d08a6e1618e18,0x870e2c37849b86506151,0x126e18e14302d370f084,0xa3c70a451ac31131308e,0xc206cc4c0e103587849,0x8403a2851461989d142b,0x3412364440f0e4dc3312,0x693146828201f0c7088e,0xaa47c2c38d272e1e1244,0xc4428222c1e908f85871,0x61c6931851230f0a3498,0x64807c2c38d2632403e1,0xf085084c144f87851a4c,0x2348413e1909194342f0,0xa3a8240a420b270dc31e,0x5044ace221e100f85861,0x438ae161981c48241f08,0x4260907c2c316213448f,0xf08746c84c25843a1b86,0x38b0a0ee1e10d909c230,0xf864281107c248c30d1d,0x5f086c74f123d0e2b844,0x4253e1e10a10902d230c,0x8784284a7070927c3c21,0x4241f0f085084c120e4f,0x8c12123292838690119,0xa423a1586120e3c46827,0x14b0962480530f092049,0x6a38ae161929c983924,0x298784d05c3c2473028b,0xa4512924a3c1c910a38,0xa61179c781c370b0cc0c,0xc3c230162f3442402e18,0x3b0c94c281a241c5e50d,0xe240961e10a385834a4,0x7302930724829612c490,0x900e0b87845e70dc3c24,0x71835201f0f0838bcf10,0xc215141640a8a6161868,0xf87842a1a2861f0e12c3,0x9294381478530b0cc0e3,0x726c2c3141550560868c,0x8428542c5e6894985452,0xa089890504b0844bcb87,0x49028a1614c2112b28a8,0x6c98a4f12928a4c43878,0xa426e1e10a089f085124,0x224c40b45c3c2141b305,0x9460370b0c5884c2984,0xc7c2c3162120a61618b1,0x85044e1f0411871a163,0x4382e161981c2e230e37,0x2650b05c3c2143030a8f,0x41f08307080f1b878428,0x30603c2e1618a8d1e0c2,0xb862834507c216c32028,0x89260e1f09343070d849,0xd263910a078b09e1e146,0x8784244e6148848c3c28,0xb1094570b0e1cc0a1413,0x48c3c20d871d303e1618,0x370f0849011858628425,0x2461e1468a188870504e,0x862c4078dc3c212152c4,0x8870b0d20515100e5185,0x3e161a6931c9e2525149,0xf0807c3c20d263c4140,0x85191187841a0e1c5e7,0x24543c3925201498c30f,0x140b4403e1618c0695a6,0x86262880748c3c20d263,0x1c370cc4b12924c4385,0xc328295e1e1244690182,0xa0d842912365e51b8dc2,0xe1618b101c241f0b0c80,0x349c214118d262a41403,0x5904e3c2b0e2d851b86,0x10a1420847a1e370b0d2,0xc20d14273070403c2e1e,0xa3e8b87842a282c707c3,0xae18a0b9b0d37084854,1761] j))
def ecH11 (j : Nat) : Nat := (if j<103 then page #[0x4086ac0048100020c301,0x90c0c200668c1801,0x400285005548a1c,0x2810204f2a0400086020,0x8018009030408088040d,0x312381072238182146c0,0x2207ab02043010004e0,0x408d8100240800a08b03,0x80141600e8426207020,0x870c001c58d000c1092e,0x320c78d080024091020,0x2702c4009c0c0800030,0xc08108180830200b40c7,0xa2cf9a0a2cb8902529c,0x23468c1a0000e0038006,0xa20068f3a30eec10b0,0x4fe0ec06e800404a030a,0x86c2902e3b2b5ba0c1b9,0x72e800064000001,0x84000127c24579887000,0xc2740000c,0x825e2a98000d23a0000,0x5cc164000348c0000000,0x112752ea0001c5860,0x3009307200018174,0x5300000953c9408cc000,0x624cb19d63b6c2858,0xa65586bcd0f200018664,0x5f00000001cec096fe3f,0x4a28000000001048d0d8,0x400030e280004c3d433d,0x82019246c52dc1256745,0x45ce85a40740498028e1,0xa0003ceea0fbf3e8e13d,0x2fd8a540c400010d4b81,0x529b93d3aca44972e02a,0xc1120a1a03584aaa468,0xd1c562f907c2a04000,0xc53e1c3f093c66cc4280,0xc6370000198d803c46a9,0x8b5a3723e4000623101b,0x3df0acb1,0xb80f2c1df80b23a4c2fc,0xa3fdc97f12de46,0x804f9800000003800000,0xb2470a7bd880b29358e5,0x402c4348374ebc836f21,0x11940000426cce3f9,0x400010dd1a46000082a4,0x4e0000d0ec449d8f0248,547049,0x4c52fc3e80000000c630,0x340000a944000000029f,0x71aa5700018964c38cc,0x38eb0000000081ec,0x160406a28ec922c4eb09,0x4e0d0dd5969697f0c851,0x5e84381a094800018392,0x1606690d7d76117,0xc25dc5082fed55329280,0x3813f9ea0001e87e,0x1fe962a4462372152000,0x105506e311ed6738d6f1,0x830d8ce229390000a960,0x47602c000000041333b1,0xc59b00f1ac123baac97a,0x3ecfb89600014920,0x308b09269341b8c8f000,0x8733a2ec3cc622303f14,0xe81510dd620186223b1,0x680000000261948a0000,0x4149a010d21e9,0xb48a000000000000d1e4,0x41930231b706df50c534,0x112e616421de234c3699,0xc8488e62ea4a5339885a,0x41a7455c87790b6147,0x4947f8e096c400000,0x31cc00000000,0x62c0de00000001222518,0x23800091120001855e0,0x1a267518785900000000,0xf000000006155000,0x4d74984f030e0e561c00,0x6977878c249634e0003,0x37822a0001a47087c915,0x520e161000102b186d39,0x1080a652000172b0,0xc4e3920001d04120b000,0x10371930000a88400038,0xe057a4b9820f00000001,0xf8000153da01f0000a18,0x980000b3f052804,0xa4162852f8920001646c,0x1fb345735391b0000915,0x88000080c0000000050,0x5e76c000000000000001,0xb28c00018f4f36,0x510508af0ee00,0x29a8ec80d180,0x8c291a767480d8000000,0x632c0f339ac000181520,0xa22f82ab] j else (if j<206 then page #[0x7a0e22e4f6e910c0000,0x18dcd7fe230000926000,0xc13c85ebc50c0634b34d,0xd19000008df84ab,0x5604f4f907020607b000,0x53ab059b4e690d26aaa8,0x40000b46600010fde151,0x6a451028697b91096b64,0x30ebc833c4180000001e,0x8000a49dc22909e00c6,0x2084755ea2da000103,0x43c320b6cf2b93a00000,0x79740000987764188d7,0x7e1c3838730000245349,0xe0ee000000014af0c486,0xc2142342a0001b268886,0x20400055d4000150010d,0x323c0002f14c8fe59646,0x8a033a37d57e98b8a4d2,0x6f40bf3a131252000289,0x4870000715de2a82,0x57854b020f2f4295ed59,0x92eac780007402a61f6d,0x112211a60001a,0x57c33000088980000000,0x2466906ce458f22600,0x1376663e4ca8000707e0,0xd00004966029b0bdb808,0x8018000000142f524,0x531200020a340e7fbc20,0x5717dc046219d4b2b94d,0xe201120568200317847,0x1a32de2980000001c,0x504ab0860001c87d9b9,0x520b284400,0xbaae515bd0bb9f518840,0x13a2450cd68e1851243c,0x20b56e15b0d600008e,0xcaba67034a6798600000,0x800061aa9642cf3f005,0x2e9611790001278af0,0xa8072033d26800000000,0xb000000000003cb1f8c2,0xa311a6c38d,0x98d00000000589500000,0x80e130001886400054d3,0x9804b480005029622d44,0xc87a04fc688000b0d1c,0xa61ed890306394dba16e,0x57d50f000073a896d444,0xb3bd098790900008,0x7782cc46868778ff2801,0x2df0f7e227f32e000182,0xc27e88508e571124cb36,0xd3cbc726aa7cac5a6207,0x48609b0000400dc42e03,0x148dc89f60e833c64,0xd20eb38cda5ac000792b,0xf48e9f021fadae7f30e,0xa96ee28c23af1ec2,0xe189f72ce0000000387f,0x87069f9f11de3d607,0x1330c7cc000423be4240,0x21960c473c244000425e,0x7ec08cc82e4194000126,0x38ce0a3012e4fb62197,0x31223a1a00003d22b23d,0x180e515ad804a6ae42,0x798f43f4691581161f40,0x3509d0a5502fabebdb0,0x7fc0bb125c0001021000,0x20482054c83254922d9c,0x12295c504359ca201c8,0x1d0519197c136915a50d,0x41be28f2462c14a00010,0x6e0f6ae800028b2589c,0x5700003842f00463670f,0x89a2d7eb3962,0xf4c2c0000000000069ce,0x22bcc28000000185df82,0x33dc7a04bc000050ca9,0x549d113258628000684d,0x7e80001826e2e000036b,0x1630c000000050aea,0x2387998a8f0940000000,0x5c4432485b517195e908,0x42c400028d1d2520000d,0x779bcb3ec00bc00059b5,0x1300000000a01b2647c5,0x295ae4b0c14de1f63356,0x2041a54df1b0000,0x7412000000,0x232d76d085e04f900000,0x713260340000000399f,0x409a2247c6b000,0x1e0acaa3f49000000,0x98000b405c4e00006cd5,0x8c8000000000000000c8,0xc177e54000040c1747f7,0x22400000277c0005055,0x3832000021a800,0x1b8ad3128000833a0,0x7cf58000] j else page #[0x14d4b424049d00001a39,0x180b913bf2,0x80e8000c16a000072d0,0x8aa01d516e44f649e000,0x12e000000028f8800080,0x1870d8300b0200010e79,0xb600028956d463af8610,0x1e453ee00018f701b352,0xd3bdb97b474e] j))
def ecD12 := page #[0xffc63ffc61ffc53ffc31,0xffd31ffc86ffc83ffc81,0xffd81ffd63ffd61ffd53,0xffe53ffe31ffd86ffd83,0xffe83ffe81ffe63ffe61,0xfff63fff61fff31ffe86,0x1b000fff86fff83fff81,0x1c532c5808e0e616e1cc,0xd600b455126c488870fa,0x451ce224157b0e89b9b3,0x4c3c28634f54a874d19,0x291214a12110e1074141,0x431a6101cb1324161431,0x20395290a18d388281e1,0x34e244052458ac3841d2,0x724361c23080e54a4286,0x28634a242880f0e11840,0xd8708a2038d8708a203c,0x330910143948708e2038,0x987850c6984072c3614,0xc69c4852848443841d02,0x28361c20e6101c992850,0x841d020393250a18d388,0x396850c6984880a50943,0x1431a610506c3841cc20,0x1204160f0a18d3080e5a,0xe561c2496101ca941b0e,0x95283614341412202960,180739]
def ecH12 := page #[0x124053c000100030602,0x6000c0600010402,0xd4b060f07010f000b00,0x131b2e000001180e2c,0x4a2d0018256305152301,0x113f0b01049e110e0006,0x100000a3402000f0a,0x2360f106000f804,0x171302083e0335070545,0x80208610127032d04,0x477a8fc3030206092200,0x8f1098a90001830c8b6,0x622650ea2bd4ac149f9d,0xfbcba9e344d8ec000126,0x2ac89d33fb1a508a074,0x6bcad8a76eaa0003c630,0x926bc69c05070e23,0xeb71010d20003075000,0xc0d210251930251e941c,0x4e033635208c4a8015b6,0x60fd30800034f10002ea,0x3d3c36438212fa2a8000,0x54c8f000000000000005,0x284c329dc5adc7407d72,0xaa800002b20000000a11,0xc55000328eebd1,0xfa2d0e4782f7493a4c40,0x1c6f321b046040e8e,0xbc3ca334100f57324e02,0x364620003f0200033153,0x1ca210d7c07b0ac070f2,0xc8e412c8bddc39000,0x30000151c00000000000,0x36278000e45000000015,0x98f0d1253b8cb1000080,0x3aefdc8e48362fbb31,0xc09c0009417c3b4,0x73132a1a90b90c400000,0x732244fd35d03dd39,0x721c0003acd6917c80,0xb00020d69079eab00000,0xd2208b814ba410e25ba3,0x1cd8052b2aae2ac30000,0x98811a336c5bb03c0004,0x1891832d043e40089de3,0x4b9415c533112b00440a,0x9c22af4c764082740001,0x91357e55c911cdf00034,0x33286e69b5b83841ee70,0x1cf2aae94e3dab8000,0x9e6cb41f8000e084a040,0x20f7e1c88f3000304194,0x8ed427cfb31e98f8231,0xa62bec8f6a1989268b44,0xbc4b4a00000c6a00014,0x62e9f240000000000000,0x9c8000784f0686897461,0x12a000045910828582,0xa49690c2297c6e00,0x8b0000000fcbeea3000,0xec5c0002819490c1b4,0x300014fc626c00000000,0x40349167a8b09293e785,0x25d524c42a43eac4204b,0x4c000c4466ece06971c0,0x21224e800018db90,0xf16f3f5c710002caf000,0x120c7a852abe645d34ac,0xcc134000e8fa0e7f8468,0xe18046b1095864000202,0x150cd8413800041d8a00,0x9380e00b80063008c0b2,0xd216231ac1714d2d19c3,0xc1b01fc41510f38c3b48,0xdcac96424017f2e7794a,0xf219dcb5e2b24a1c976a,0x134c00043534e28c6189,0x4199186950ead8379d1b,0x422d5d4a1321a1b34809,0x5449b058000a1e70b624,0x30ab251c8c00014e1031,0xcc7cb0000d43cd1a7ae3,0x6c407c5e130747c0000c,0x80999214c4400093fbeb,0xd000002c10d180656bb,0x9000000000dd6adc000a,0xe82f23646ed20b6447d8,0xd1500026febcaca9602e,0x17d2c8322299c00052ce,0xad0a88320cab8d023c31,0x434000d115cbc33ffc8,0x34650000037,0x9b6d7a0734e9b3080000,0x48160a693208073266a,0x922807c70f4b77c1d41e,0x7b86808a060c3343eb,0xe6373c82533a0bfd2140,0xfcbb85cf482d1d285050,0x3b49290002c519007898,0x6d3d0272d4e,0xa4b790e80009bd951f00,0x385004b54a482b]
def ecD13 (j : Nat) : Nat := (if j%103=0 then 3180031 else 0)
def ecH13 := page #[0x1560000000010,476053504,0x53000e4400f200016000,0x5022310c00,0xd96b3000000000000000,992,0,0xa4800610cf75c00,0x15adc0000000,0,693,0x5a800b9c00002ef0018e,0x141001d900000,0x5b00000309ee400f4000,0xb8d000000000002c00,0xc4e6e05000bc400,0,810549514,0x287c680000000]
def ecLevels : Nat → Packing
  | 9 => (114,4,6,0,0,12,0,ecD9)
  | 10 => (609,3,6,0,0,15,0,ecD10)
  | 11 => (309,2,6,0,0,15,0,ecD11)
  | 12 => (27,1,6,0,0,11,0,ecD12)
  | 13 => (1,0,6,0,0,0,0,ecD13)
  | _ => emptyPacking
def ecIndex : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 32 163 7 12 7 1 ecH10
  | 11 => lookupWord 191 1049 7 15 10 1 ecH11
  | 12 => lookupWord 105 521 8 14 9 1 ecH12
  | 13 => lookupWord 10 149 1 10 5 1 ecH13
  | _ => fun _ => none
def ec : Forest := ⟨1023,13,fun i => ecY[i]?.getD (0,0),ecC,ecA,ecLevels,ecIndex⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem sample121 : block ec 10 0 121 = true := by decide +kernel
end PEqualNP.Outside.L_meta_4813_aux.Certificate
