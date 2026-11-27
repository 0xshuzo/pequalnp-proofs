import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_393_aux

def changes {m : Nat} (x : Fin (m+1)→Bool) (i : Fin m) : Bool := Bool.xor (x i.castSucc) (x i.succ)
def walk : (m : Nat) → Bool → (Fin m→Bool) → Fin (m+1)→Bool
  | 0, a, _ => fun _ => a
  | m+1, a, f => Fin.cases a (walk m (Bool.xor a (f 0)) (fun i => f i.succ))

lemma walk_zero (m : Nat) (a : Bool) (f : Fin m→Bool) : walk m a f 0 = a := by cases m <;> rfl

lemma change_walk (m : Nat) (a : Bool) (f : Fin m→Bool) : changes (walk m a f)=f := by
  induction m generalizing a with
  | zero => funext i; exact Fin.elim0 i
  | succ m ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Bool.xor a (walk m (Bool.xor a (f 0)) (fun i => f i.succ) 0) = f 0
      rw [walk_zero]; cases a <;> cases f 0 <;> rfl
    · exact congrFun (ih (Bool.xor a (f 0)) (fun i => f i.succ)) j

lemma walk_change (m : Nat) (x : Fin (m+1)→Bool) : walk m (x 0) (changes x)=x := by
  induction m with
  | zero => funext i; have e : i=0 := Subsingleton.elim _ _; subst i; rfl
  | succ m ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    change walk m (Bool.xor (x 0) (Bool.xor (x 0) (x (0:Fin(m+1)).succ))) _ j = _
    have a : ∀ b c : Bool, Bool.xor b (Bool.xor b c) = c := by decide
    rw [a]
    exact congrFun (ih (fun i => x i.succ)) j

def ones {m : Nat} (f : Fin m→Bool) : Nat := ∑ i,(f i).toNat
def parity (n : Nat) := decide (n%2=1)

lemma parity_step (n : Nat) (a d : Bool) :
    Bool.xor (Bool.xor a d) (parity n) = Bool.xor a (parity (d.toNat+n)) := by
  have hn : n%2=0 ∨ n%2=1 := by omega
  rcases hn with h|h <;> cases a <;> cases d <;> simp [parity,Nat.add_mod,h]

lemma walk_last (m : Nat) (a : Bool) (f : Fin m→Bool) :
    walk m a f (Fin.last m) = Bool.xor a (parity (ones f)) := by
  induction m generalizing a with
  | zero => cases a <;> simp [walk,ones,parity]
  | succ m ih =>
    change walk m (Bool.xor a (f 0)) (fun i => f i.succ) (Fin.last m) = _
    rw [ih,parity_step]
    have cnt : ones f = (f 0).toNat+ones (fun i : Fin m => f i.succ) := Fin.sum_univ_succ _
    rw [cnt]

def supportB {m : Nat} (f : Fin m→Bool) := Finset.univ.filter (fun i => f i=true)

lemma ones_eq_card {m : Nat} (f : Fin m→Bool) : ones f=(supportB f).card := by
  unfold ones supportB
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases h : f i <;> simp

abbrev PathSet (m : Nat) (a b : Bool) (red : Finset (Fin m)) (r s : Nat) :=
  {x : Fin (m+1)→Bool // x 0=a ∧ x (Fin.last m)=b ∧
    (supportB (changes x) ∩ red).card=r ∧ (supportB (changes x) \ red).card=s}

abbrev PairSet {m : Nat} (red : Finset (Fin m)) (r s : Nat) :=
  {A // A ∈ red.powersetCard r} × {B // B ∈ redᶜ.powersetCard s}

def pairFlags {m : Nat} {red : Finset (Fin m)} {r s : Nat} (p : PairSet red r s) (i : Fin m) :=
  decide (i ∈ p.1.val ∪ p.2.val)

lemma support_pair {m : Nat} {red : Finset (Fin m)} {r s : Nat} (p : PairSet red r s) :
    supportB (pairFlags p)=p.1.val ∪ p.2.val := by ext i; simp [supportB,pairFlags]

lemma pair_parts {m : Nat} {red : Finset (Fin m)} {r s : Nat} (p : PairSet red r s) :
    supportB (pairFlags p) ∩ red=p.1.val ∧ supportB (pairFlags p) \ red=p.2.val := by
  have left := (Finset.mem_powersetCard.mp p.1.property).1
  have right := (Finset.mem_powersetCard.mp p.2.property).1
  rw [support_pair]
  constructor <;> ext i <;> simp only [Finset.mem_inter,Finset.mem_sdiff,Finset.mem_union]
  all_goals have lx := @left i; have rx := @right i
  all_goals simp only [Finset.mem_compl] at rx
  all_goals tauto

lemma pair_count {m : Nat} {red : Finset (Fin m)} {r s : Nat} (p : PairSet red r s) :
    ones (pairFlags p)=r+s := by
  rw [ones_eq_card]
  have h := Finset.card_sdiff_add_card_inter (supportB (pairFlags p)) red
  rw [(pair_parts p).1,(pair_parts p).2,
    (Finset.mem_powersetCard.mp p.1.property).2,(Finset.mem_powersetCard.mp p.2.property).2] at h
  omega

def pathPair {m : Nat} {a b : Bool} {red : Finset (Fin m)} {r s : Nat} (x : PathSet m a b red r s) :
    PairSet red r s :=
  (⟨_,Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right,x.property.2.2.1⟩⟩,
   ⟨_,Finset.mem_powersetCard.mpr ⟨fun _ h => Finset.mem_compl.mpr (Finset.mem_sdiff.mp h).2,x.property.2.2.2⟩⟩)

lemma flags_path {m : Nat} {a b : Bool} {red : Finset (Fin m)} {r s : Nat} (x : PathSet m a b red r s) :
    pairFlags (pathPair x) = changes x.val := by
  funext i
  by_cases h : i∈red <;> cases hi : changes x.val i <;> simp [pathPair,pairFlags,supportB,hi,h]

def arcEquiv (m : Nat) (a b : Bool) (red : Finset (Fin m)) (r s : Nat)
    (endpoint : Bool.xor a (parity (r+s))=b) : PairSet red r s ≃ PathSet m a b red r s where
  toFun p := ⟨walk m a (pairFlags p),walk_zero ..,by rw [walk_last,pair_count,endpoint],by
    rw [change_walk,(pair_parts p).1]; exact (Finset.mem_powersetCard.mp p.1.property).2,by
    rw [change_walk,(pair_parts p).2]; exact (Finset.mem_powersetCard.mp p.2.property).2⟩
  invFun := pathPair
  left_inv p := by
    apply Prod.ext <;> apply Subtype.ext
    · change supportB (changes (walk m a (pairFlags p))) ∩ red = _
      rw [change_walk,(pair_parts p).1]
    · change supportB (changes (walk m a (pairFlags p))) \ red = _
      rw [change_walk,(pair_parts p).2]
  right_inv x := by
    apply Subtype.ext
    change walk m a (pairFlags (pathPair x)) = x.val
    rw [flags_path,← x.property.1,walk_change]

theorem arc_histogram (m : Nat) (a b : Bool) (red : Finset (Fin m)) (r s : Nat) :
    Fintype.card (PathSet m a b red r s) =
      if Bool.xor a (parity (r+s))=b then red.card.choose r * redᶜ.card.choose s else 0 := by
  classical
  split_ifs with h
  · rw [←Fintype.card_congr (arcEquiv m a b red r s h)]
    simp [PairSet,Finset.card_powersetCard]
  · apply Fintype.card_eq_zero_iff.mpr
    constructor
    intro x
    apply h
    have cnt := pair_count (pathPair x)
    rw [flags_path] at cnt
    have hl := walk_last m (x.val 0) (changes x.val)
    rw [walk_change,x.property.2.1,x.property.1,cnt] at hl
    exact hl.symm

end PEqualNP.Outside.L_pcx_393_aux
