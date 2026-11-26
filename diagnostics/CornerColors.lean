import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9755.SignedColor
open PEqualNP.CircuitLowerBounds
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

abbrev Row := Fin 512
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
theorem gate_share_eq {a b z U f v w} (hv : v∈gateList a b U)
    (eq : gateColor a b z U f v = gateColor a b z U f w) : v=w := by
  have bound := List.idxOf_lt_length_of_mem hv
  by_cases hw : w∈gateList a b U
  · simp only [gateColor,if_pos hv,if_pos hw] at eq
    exact (List.idxOf_inj hv).mp eq
  · simp only [gateColor,if_pos hv,if_neg hw] at eq
    omega

def Isolated (T : Sig) (S : Finset Sig) (v : Sig) (r s : Row) : Prop :=
  bit r T ≠ bit s T ∧ ∀ w∈S, bit r w≠bit s w → w=v
theorem isoValue {u k S T v r s} (run : Live u T k S) (h : Isolated T S v r s) :
    v∈S ∧ bit r v≠bit s v := by
  obtain ⟨w,mem,neq⟩ := live_row_difference run h.1
  exact h.2 w mem neq ▸ ⟨mem,neq⟩
theorem isoPull {a b d U T v r s} (unused : v∉gateList a b U)
    (h : Isolated T (insert a (insert b U)) v r s) :
    Isolated T (insert (bin d a b) U) (gateMap a b (bin d a b) v) r s := by
  refine ⟨h.1,?_⟩
  intro w mem neq
  rcases Finset.mem_insert.mp mem with rfl|mem
  · have diff : bit r a≠bit s a ∨ bit r b≠bit s b := by
      by_contra! same
      exact neq (by rw [bit_bin,bit_bin,same.1,same.2])
    have hn : v=a ∨ v=b := diff.imp (fun ha => (h.2 a (by simp) ha).symm)
      (fun hb => (h.2 b (by simp) hb).symm)
    simp [gateMap,hn]
  · obtain rfl := h.2 w (by simp [mem]) neq
    have hn : ¬(w=a ∨ w=b) := fun eq => unused (gate_kept.mpr ⟨eq,mem⟩)
    simp [gateMap,hn]
def oriented (phase b : Bool) : Bool := if phase then b else !b
def markAt (a b z : Sig) (d : Nat) (f : Sig → Bool) (v : Sig) :=
  if v=a then (if d=3 then !(f z) else f z) else
  if v=b then (if d=2 then !(f z) else f z) else f v
theorem orientedA {u d r s a b} (hd : allowed u d) (f : Bool)
    (same : bit r b=bit s b) (changeZ : bit r (bin d a b)≠bit s (bin d a b)) :
    oriented (if d=3 then !f else f) (bit r a)=oriented f (bit r (bin d a b)) := by
  rcases allowed_four hd with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩ <;>
    cases f <;> cases ar : bit r a <;> cases as' : bit s a <;> cases br : bit r b <;>
    simp_all [oriented,bit_bin]
theorem orientedB {u d r s a b} (hd : allowed u d) (f : Bool)
    (same : bit r a=bit s a) (changeZ : bit r (bin d a b)≠bit s (bin d a b)) :
    oriented (if d=2 then !f else f) (bit r b)=oriented f (bit r (bin d a b)) := by
  rcases allowed_four hd with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩ <;>
    cases f <;> cases br : bit r b <;> cases bs : bit s b <;> cases ar : bit r a <;>
    simp_all [oriented,bit_bin]
theorem inheritMark {u k a b d U T v r s} (hd : allowed u d) (ab : a≠b)
    (tail : Live u T k (insert (bin d a b) U)) (unused : v∉gateList a b U)
    (h : Isolated T (insert a (insert b U)) v r s) (f : Sig → Bool) :
    oriented (markAt a b (bin d a b) d f v) (bit r v) =
      oriented (f (gateMap a b (bin d a b) v)) (bit r (gateMap a b (bin d a b) v)) := by
  have z := (isoValue tail (isoPull unused h)).2
  by_cases ea : v=a
  · subst v
    have same : bit r b = bit s b := by
      by_contra ne
      exact ab (h.2 b (by simp) ne).symm
    simp only [gateMap,true_or,if_true] at z ⊢
    simpa [markAt] using orientedA hd (f (bin d a b)) same z
  · by_cases eb : v=b
    · subst v
      have same : bit r a=bit s a := by
        by_contra ne
        exact ab (h.2 a (by simp) ne)
      simp only [gateMap,or_true,if_true] at z ⊢
      simpa [markAt,ea] using orientedB hd (f (bin d a b)) same z
    · simp [markAt,gateMap,ea,eb]
def law (T : Sig) (S : Finset Sig) (count : Nat) (color : Sig → Nat) (mark : Sig → Bool) :=
  (∀ {v w r s t}, Isolated T S v r s → Isolated T S w r t → color v=color w →
    oriented (mark v) (bit r v)=oriented (mark w) (bit r w)) ∧
  (∀ {v r s}, Isolated T S v r s → color v+1=count → oriented (mark v) (bit r v)=bit r T)

def cornerLaw (T : Sig) (S : Finset Sig) (f : Sig → Nat) :=
  ∀ {v w r s t r' s' t'}, v ≠ w →
    Isolated T S v r s → Isolated T S w r t →
    Isolated T S v r' s' → Isolated T S w r' t' →
    f v=f w → bit r v=bit r' v
theorem sharedCornerA {u d r s a b} (hd : allowed u d)
    (same : bit r a=bit s a) (diff : bit r (bin d a b) ≠ bit s (bin d a b)) :
    bit r a = decide (d=0 ∨ d=2) := by
  rcases allowed_four hd with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩ <;>
    cases x : bit r a <;> cases y : bit r b <;> cases z : bit s b <;> simp_all [bit_bin]
theorem sharedCornerB {u d r s a b} (hd : allowed u d)
    (same : bit r b=bit s b) (diff : bit r (bin d a b) ≠ bit s (bin d a b)) :
    bit r b = decide (d=0 ∨ d=3) := by
  rcases allowed_four hd with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩ <;>
    cases x : bit r b <;> cases y : bit r a <;> cases z : bit s a <;> simp_all [bit_bin]
theorem activeA {u k a b d U T r s} (hd : allowed u d) (ab : a≠b)
    (tail : Live u T k (insert (bin d a b) U)) (unused : b∉gateList a b U)
    (iso : Isolated T (insert a (insert b U)) b r s) :
    bit r a=decide (d=0 ∨ d=2) := by
  have diff := (isoValue tail (isoPull unused iso)).2
  simp only [gateMap,or_true,if_true] at diff
  apply sharedCornerA hd _ diff
  by_contra ne
  exact ab (iso.2 a (by simp) ne)
theorem activeB {u k a b d U T r s} (hd : allowed u d) (ab : a≠b)
    (tail : Live u T k (insert (bin d a b) U)) (unused : a∉gateList a b U)
    (iso : Isolated T (insert a (insert b U)) a r s) :
    bit r b=decide (d=0 ∨ d=3) := by
  have diff := (isoValue tail (isoPull unused iso)).2
  simp only [gateMap,true_or,if_true] at diff
  apply sharedCornerB hd _ diff
  by_contra ne
  exact ab (iso.2 b (by simp) ne).symm
theorem orientedInj (p x y : Bool) (h : oriented p x=oriented p y) : x=y := by
  cases p <;> cases x <;> cases y <;> simp_all [oriented]
set_option maxHeartbeats 0 in
theorem signed_corner_colors {u k S T} (h : Live u T k S) :
    ∃ count color mark, 0<count ∧ count+S.card≤k+2 ∧ (∀v∈S,color v<count) ∧ law T S count color mark ∧ cornerLaw T S color := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,pr⟩ := h
    refine ⟨1,fun _ => 0,fun _ => true,by decide,by simp,by simp,⟨?_,?_⟩,?_⟩
    · intro v w r s t A B _
      have e : v=T := by simpa using (isoValue (Live.stop (u:=u) pr) A).1
      subst v
      have e : w=T := by simpa using (isoValue (Live.stop (u:=u) pr) B).1
      subst w
      rfl
    · intro v r s A _
      have e : v=T := by simpa using (isoValue (Live.stop (u:=u) pr) A).1
      subst v
      rfl
    · intro v w r s t rp sp tp ne A B _ _ _
      have a : v=T := by simpa using (isoValue (Live.stop (u:=u) pr) A).1
      have b : w=T := by simpa using (isoValue (Live.stop (u:=u) pr) B).1
      exact False.elim (ne (a.trans b.symm))
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,pa,pb,ab,fresh,tail⟩ := h
    let z := bin d a b
    let kept := gateList a b U
    obtain ⟨count,f,g,positive,mass,bound,rule,corner⟩ := ih tail
    have zeroU : z∉U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem zeroU] at mass
    have size : kept.length+(insert a (insert b U)).card=U.card+2 := by
      by_cases x : a∈U <;> by_cases y : b∈U <;> simp [kept,gateList,x,y,ab,Finset.card_insert_of_notMem] <;> omega
    refine ⟨kept.length+count,gateColor a b z U f,markAt a b z d g,by omega,by omega,?_,⟨?_,?_⟩,?_⟩
    · intro v hv
      by_cases vu : v∈kept
      · have small := List.idxOf_lt_length_of_mem vu
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_pos vu]
        omega
      · have small := bound _ (gate_mem (z:=z) hv)
        change (if v∈kept then kept.idxOf v else _) < _
        rw [if_neg vu]
        exact Nat.add_lt_add_left small _
    · intro v w r s t A B eq
      by_cases same : v=w
      · rw [same]
      have uv : v∉kept := fun m => same (gate_share_eq m eq)
      have uw : w∉kept := fun m => same (gate_share_eq m eq.symm).symm
      have eqc : f (gateMap a b z v)=f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_)=(if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      exact (inheritMark hd ab tail uv A g).trans ((rule.1 (isoPull uv A) (isoPull uw B) eqc).trans
        (inheritMark hd ab tail uw B g).symm)
    · intro v r s A hv
      have uv : v∉kept := by
        intro m
        have small := List.idxOf_lt_length_of_mem m
        change (if v∈kept then kept.idxOf v else _)+1=_ at hv
        rw [if_pos m] at hv
        omega
      have eqc : f (gateMap a b z v)+1=count := by
        change (if v∈kept then _ else kept.length+_)+1=_ at hv
        rw [if_neg uv] at hv
        omega
      exact (inheritMark hd ab tail uv A g).trans (rule.2 (isoPull uv A) eqc)
    · intro v w r s t rp sp tp ne A B C D eq
      have uv : v∉kept := fun m => ne (gate_share_eq m eq)
      have uw : w∉kept := fun m => ne (gate_share_eq m eq.symm).symm
      have same : f (gateMap a b z v)=f (gateMap a b z w) := by
        change (if v∈kept then _ else kept.length+_)=(if w∈kept then _ else kept.length+_) at eq
        rw [if_neg uv,if_neg uw] at eq
        omega
      by_cases nm : gateMap a b z v≠gateMap a b z w
      · have hx := corner nm (isoPull uv A) (isoPull uw B) (isoPull uv C) (isoPull uw D) same
        have first := inheritMark hd ab tail uv A g
        have second := inheritMark hd ab tail uv C g
        apply orientedInj (markAt a b z d g v)
        exact first.trans ((congrArg (oriented (g (gateMap a b z v))) hx).trans second.symm)
      · have vv := (isoValue (Live.binary hd pa pb ab fresh tail) A).1
        have ww := (isoValue (Live.binary hd pa pb ab fresh tail) B).1
        have vz : v≠z := fun h => fresh (h ▸ vv)
        have wz : w≠z := fun h => fresh (h ▸ ww)
        have cases' : (v=a ∧ w=b) ∨ (v=b ∧ w=a) := by
          by_cases va : v=a ∨ v=b <;> by_cases wa : w=a ∨ w=b <;> simp_all [gateMap] <;> grind
        rcases cases' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact (activeA hd ab tail uw B).trans (activeA hd ab tail uw D).symm
        · exact (activeB hd ab tail uw B).trans (activeB hd ab tail uw D).symm
end PEqualNP.Outside.L_meta_9755.SignedColor
