import Mathlib
import PEqualNP.Outside.L_meta_1674
open PEqualNP.Outside.L_meta_1674
namespace Share670
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
        exact ⟨factorExpand hd01 (by simp [neA,ain]) (by simp [neB,bin']) zU F⟩
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

def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
abbrev HornGroups := BitVec 128
abbrev HornSlot := Fin 7
def hornActive (s : BitVec 7) (w : HornGroups) := w.getLsbD s.toNat=true
def hornMask (i : HornSlot) : HornGroups :=
  BitVec.ofNat 128 (((2^128-1)/(2^(2^i.val)+1)) <<< (2^i.val))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hornMask_at : ∀ (s : BitVec 7) (i : HornSlot), hornActive s (hornMask i) ↔ s.getLsbD i.val=true := by
  decide +kernel

def hornAssignment (A : Finset Sig) (wire : HornSlot→Sig) : BitVec 7 :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : HornSlot => decide (wire i∈A)))).cast List.length_ofFn

theorem hornAssignment_at (A : Finset Sig) (wire : HornSlot→Sig) (i : HornSlot) :
    hornActive (hornAssignment A wire) (hornMask i) ↔ wire i∈A := by
  rw [hornMask_at]
  simp only [hornAssignment,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

theorem hornNever (s : BitVec 7) : ¬hornActive s 0 := by simp [hornActive]
theorem hornAlways (s : BitVec 7) : hornActive s (BitVec.allOnes 128) := by
  have bound : s.toNat<128 := s.isLt
  simp [hornActive,bound]
theorem hornAnd (s : BitVec 7) (a b : HornGroups) : hornActive s (a &&& b) ↔ hornActive s a ∧ hornActive s b := by
  simp only [hornActive,BitVec.getLsbD_and,Bool.and_eq_true]
theorem hornOr (s : BitVec 7) (a b : HornGroups) : hornActive s (a ||| b) ↔ hornActive s a ∨ hornActive s b := by
  simp only [hornActive,BitVec.getLsbD_or,Bool.or_eq_true]
theorem hornNot (s : BitVec 7) (a : HornGroups) : hornActive s (~~~a) ↔ ¬hornActive s a := by
  have bound : s.toNat<128 := s.isLt
  simp [hornActive,BitVec.getLsbD_not,bound]

def hornCase (ws : List Sig) (T : Sig) (wire : HornSlot→Sig) (a b c : HornSlot)
    (p n na nb pa pb : Row) (parity : Bool) : HornGroups :=
  let A := wire a
  let B := wire b
  if parity then
    if decide (A∈ws) && decide (B∈ws) && decide (A≠B) &&
       kwWireB ws T A p na && kwWireB ws T B p nb &&
       kwWireB ws T A pa n && kwWireB ws T B pb n then
      (hornMask a &&& hornMask b) ||| (~~~(hornMask a) &&& ~~~(hornMask b)) else 0
  else if kwWireB ws T A p na && kwWireB ws T B pa n && kwWireB ws T (wire c) p n then
    (hornMask a &&& hornMask b) &&& ~~~(hornMask c) else 0

theorem hornCase_sound {ws T wire a b c p n na nb pa pb parity}
    (F : SingleFactor (List.toFinset ws) T) :
    ¬hornActive (hornAssignment F.inner wire) (hornCase ws T wire a b c p n na nb pa pb parity) := by
  intro active
  cases parity
  · simp only [hornCase,Bool.false_eq_true,ite_false] at active
    split at active
    next h =>
      simp only [Bool.and_eq_true] at h
      simp only [hornAnd,hornNot,hornAssignment_at] at active
      exact active.2 (hornRule F (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2) active.1.1 active.1.2)
    next => exact hornNever _ active
  · simp only [hornCase,ite_true] at active
    split at active
    next h =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h
      simp only [hornOr,hornAnd,hornNot,hornAssignment_at] at active
      exact parityRule F (List.mem_toFinset.mpr h.1.1.1.1.1.1)
        (List.mem_toFinset.mpr h.1.1.1.1.1.2) h.1.1.1.1.2
        (kwWireB_sound h.1.1.1.2) (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2) active
    next => exact hornNever _ active

def hornWire (ws : List Sig) (core : Nat) (i : HornSlot) := ws.getD ((core >>> (4*i.val)) &&& 15) zero
def hornWord (pos neg : Nat) (ws : List Sig) (T : Sig) (core r : Nat) :=
  let fld := fun i => (r >>> (1+4*i)) &&& 15
  let slot := fun i => Fin.ofNat 7 (fld i)
  hornCase ws T (hornWire ws core) (slot 0) (slot 1) (slot 2)
    (kwProbe pos (fld 3)) (kwProbe neg (fld 4)) (kwProbe neg (fld 5)) (kwProbe neg (fld 6))
    (kwProbe pos (fld 7)) (kwProbe pos (fld 8)) (r.testBit 0)
def hornCollect (pos neg : Nat) (ws : List Sig) (T : Sig) (core : Nat) : Nat → Nat → HornGroups
  | 0,_ => 0
  | n+1,data => hornWord pos neg ws T core (data &&& 137438953471) |||
      hornCollect pos neg ws T core n (data >>> 37)
theorem hornCollect_sound {pos neg ws T core} (F : SingleFactor (List.toFinset ws) T) (n data : Nat) :
    ¬hornActive (hornAssignment F.inner (hornWire ws core)) (hornCollect pos neg ws T core n data) := by
  induction n generalizing data with
  | zero => exact hornNever _
  | succ n ih =>
    intro h
    rcases (hornOr _ _ _).mp h with cur | rest
    · exact hornCase_sound F cur
    · exact ih _ rest

theorem hornReplay {pos neg ws T core cap count data} (budget : cap≤(List.toFinset ws).card)
    (rejected : hornCollect pos neg ws T core count data=BitVec.allOnes 128) :
    Impossible false T cap ws.toFinset := by
  intro k hk live
  obtain ⟨F⟩ := oneShare live (hk.trans budget)
  have contra := hornCollect_sound (pos:=pos) (neg:=neg) (core:=core) F count data
  rw [rejected] at contra
  exact contra (hornAlways _)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
example : Impossible false (0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8 : Sig) 9 ([0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa,0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,0xffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc] : List Sig).toFinset := by
  apply hornReplay (pos:=0x9050141084210842110c0300c03) (neg:=0xc9606290568325147434114642a) (core:=554272) (count:=7) (data:=0x43cdd5821ed2ae6010a16152e2860809a404202023298101c191484d70c96a065)
  · decide +kernel
  · decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
example : Impossible false (0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8 : Sig) 10 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88,0xffffffffff88ff88ffffffffff88ff88ffffffffff88ff88ffffffffff88ff88ffffffffff88ff88ffffffffff88ff88ffffffffff88ff88ffffffffff88ff88] : List Sig).toFinset := by
  apply hornReplay (pos:=0x9050141084210842110c0300c03) (neg:=0xc9606290568325147434114642a) (core:=9851936) (count:=10) (data:=0x142c9c950e8c96a0815a942b05385812281a8282c904c00e048a04a070b24120020212a8802c1a5014568492a0a1)
  · decide +kernel
  · decide +kernel

end Share670
