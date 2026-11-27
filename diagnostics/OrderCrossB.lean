import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9737.Order
abbrev Sig := BitVec 64
def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
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

def bit (i : Fin 64) (a : Sig) : Bool := a.getLsbD i.val
abbrev Row := Fin 64
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop := ∀ k, k ≤ cap → ¬Live u T k S
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

theorem polarDirFalse (a b : Bool) : kwDir false a b ↔ a=true ∧ b=false := by
  cases a <;> cases b <;> simp [kwDir]
def polarOfMono {S T} (H : KWRooms S T) : PolarRooms false S T where
  owns := H.owns
  total := H.total
  valid := fun h => ⟨(H.valid h).1,(polarDirFalse _ _).mpr (H.valid h).2⟩
  unique := H.unique
  rect := H.rect
def monoOfPolar {S T} (H : PolarRooms false S T) : KWRooms S T where
  owns := H.owns
  total := H.total
  valid := fun h => ⟨(H.valid h).1,(polarDirFalse _ _).mp (H.valid h).2⟩
  unique := H.unique
  rect := H.rect
def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (hd : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T :=
  monoOfPolar (polarFork (u:=false) (Or.inl (by omega)) ha hb hz (polarOfMono H))
theorem kwTight {T k S} (r : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  obtain ⟨h⟩ := polarTight r tight
  exact ⟨monoOfPolar h⟩
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

structure FreePolar (u : Bool) (S : Finset Sig) (T H : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false →
    kwDir u (bit p H) (bit n H) ∨ ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ kwDir u (bit p v) (bit n v)
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

structure PolarFactor (u : Bool) (S : Finset Sig) (T : Sig) where
  inner : Finset Sig
  outer : Finset Sig
  pivot : Sig
  cover : inner ∪ outer = S
  apart : Disjoint inner outer
  inside : PolarRooms u inner pivot
  outside : FreePolar u outer T pivot

def polarFreeFrom {u : Bool} {S T} (D : PolarRooms u S T) (h : Sig) : FreePolar u S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect

def polarHide {u : Bool} {S T h} (D : FreePolar u S T h) : FreePolar u (S.erase h) T h where
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

def polarFactorOfTree {u : Bool} {S T} (D : PolarRooms u S T) : PolarFactor u S T where
  inner := S
  outer := ∅
  pivot := T
  cover := by simp
  apart := by simp
  inside := D
  outside := {
    owns := fun _ _ _ => False
    total := fun p n hp hn => Or.inl (by simp [kwDir,hp,hn])
    valid := fun h => h.elim
    unique := fun h _ => h.elim
    rect := fun h _ => h.elim }

def freePolarFork {u : Bool} {pivot : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : FreePolar u (insert (bin d a b) U) T pivot) : FreePolar u (insert a (insert b U)) T pivot := by
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


def polarExpand {u : Bool} {U T a b d} (hd : allowed u d)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : PolarFactor u (insert (bin d a b) U) T) :
    PolarFactor u (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := supportSide F.cover F.apart inn freshA freshB freshZ
    have old : PolarRooms u (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,polarFork hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := supportSide ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : FreePolar u (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      freePolarFork hd ha hb (by simp [z]) old⟩

def polarKeep {u : Bool} {U T a b d} (hd : allowed u d) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : PolarRooms u (insert (bin d a b) U) T) :
    PolarFactor u (insert a (insert b U)) T := by
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
  have H0 : FreePolar u (insert z (U.erase a)) T a := set0 ▸ polarHide (polarFreeFrom H a)
  have H1 := freePolarFork hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : FreePolar u (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,polarLeaf u a,polarHide H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp

theorem polarOneShare {u : Bool} {T k S} (r : Live u T k S) (budget : k≤S.card) :
    Nonempty (PolarFactor u S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨polarFactorOfTree (polarLeaf u T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := kwWidth tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := polarTight tail (by change (insert z U).card=k+1; omega)
        exact ⟨polarKeep hd ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := polarTight tail (by change (insert z U).card=k+1; omega)
        have comm : bin (flipOp d) b a=z := (bin_flip hd a b).symm
        have H' : PolarRooms u (insert (bin (flipOp d) b a) U) T := by simpa only [comm] using H
        have fr : bin (flipOp d) b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := polarKeep (flip_flip hd).1 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨polarExpand hd fa fb zU F⟩
theorem orderedOwner {S T} (F : PolarFactor false S T) {w p n}
    (one : polarOnly false S T w p n) :
    (w∈F.inner ∧ F.inside.owns w p n) ∨ (w∈F.outer ∧ F.outside.owns w p n) := by
  rcases F.outside.total p n one.1 one.2.1 with dir | ⟨a,ha⟩
  · obtain ⟨hp,hn⟩ := (polarDirFalse _ _).mp dir
    obtain ⟨a,ha⟩ := F.inside.total p n hp hn
    have ai := (F.inside.valid ha).1
    have eq := one.2.2 a (F.cover ▸ Finset.mem_union_left _ ai) (F.inside.valid ha).2
    exact Or.inl (eq ▸ ⟨ai,ha⟩)
  · have ao := (F.outside.valid ha).1
    have eq := one.2.2 a (F.cover ▸ Finset.mem_union_right _ ao) (F.outside.valid ha).2
    exact Or.inr (eq ▸ ⟨ao,ha⟩)

theorem innerOwn {S T} (F : PolarFactor false S T) {w p n} (wi : w∈F.inner)
    (one : polarOnly false S T w p n) : F.inside.owns w p n := by
  rcases orderedOwner F one with h | h
  · exact h.2
  · exact (Finset.disjoint_left.mp F.apart wi h.1).elim

theorem outerOwn {S T} (F : PolarFactor false S T) {w p n} (wo : w∉F.inner)
    (one : polarOnly false S T w p n) : F.outside.owns w p n := by
  rcases orderedOwner F one with h | h
  · exact (wo h.1).elim
  · exact h.2

theorem opposite {S T} (F : PolarFactor false S T) {a b p n pa pb na nb}
    (diff : a≠b) (c1 : polarOnly false S T a p na) (c2 : polarOnly false S T b p nb)
    (c3 : polarOnly false S T a pa n) (c4 : polarOnly false S T b pb n) :
    a∈F.inner ↔ b∉F.inner := by
  constructor
  · intro ai bi
    exact diff (F.inside.unique (F.inside.rect (innerOwn F ai c1) (innerOwn F ai c3))
      (F.inside.rect (innerOwn F bi c2) (innerOwn F bi c4)))
  · intro bo
    by_contra ao
    exact diff (F.outside.unique (F.outside.rect (outerOwn F ao c1) (outerOwn F ao c3))
      (F.outside.rect (outerOwn F bo c2) (outerOwn F bo c4)))

def cell (ws : List Sig) (T v : Sig) (p n : Row) :=
  bit p T && !bit n T && ws.all (fun w => !(bit p w && !bit n w) || w==v)

theorem cell_sound {ws T v p n} (h : cell ws T v p n=true) :
    polarOnly false ws.toFinset T v p n := by
  simp only [cell,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw sep
  obtain ⟨hp,hn⟩ := (polarDirFalse _ _).mp sep
  simpa only [hp,hn,Bool.not_false,Bool.and_true,Bool.not_true,Bool.false_or,beq_iff_eq]
    using h.2 w (List.mem_toFinset.mp hw)

def link (ws : List Sig) (T a b : Sig) (p n pa pb na nb : Row) :=
  decide (a≠b) && cell ws T a p na && cell ws T b p nb && cell ws T a pa n && cell ws T b pb n

theorem link_sound {ws T a b p n pa pb na nb} (F : PolarFactor false ws.toFinset T)
    (h : link ws T a b p n pa pb na nb=true) : a∈F.inner ↔ b∉F.inner := by
  simp only [link,Bool.and_eq_true,decide_eq_true_eq] at h
  exact opposite F h.1.1.1.1 (cell_sound h.1.1.1.2) (cell_sound h.1.1.2)
    (cell_sound h.1.2) (cell_sound h.2)
theorem polarOddThree (A B C : Prop) (ab : A ↔ ¬B) (bc : B ↔ ¬C) (ca : C ↔ ¬A) : False := by
  by_cases a : A
  · have c : ¬C := fun c => ca.mp c a
    exact ab.mp a (bc.mpr c)
  · have c := ca.mpr a
    have b : ¬B := fun b => bc.mp b c
    exact a (ab.mpr b)
theorem polarOddFive (A B C D E : Prop) (ab : A ↔ ¬B) (bc : B ↔ ¬C) (cd : C ↔ ¬D)
    (de : D ↔ ¬E) (ea : E ↔ ¬A) : False := by
  by_cases a : A
  · have e : ¬E := fun e => ea.mp e a
    have d := de.mpr e
    have c : ¬C := fun c => cd.mp c d
    exact ab.mp a (bc.mpr c)
  · have e := ea.mpr a
    have d : ¬D := fun d => de.mp d e
    have c := cd.mpr d
    have b : ¬B := fun b => bc.mp b c
    exact a (ab.mpr b)

def target : Sig := 0x1ffff
def deck : List Sig := [0x12a55540043,0x14c99980414,0x170e1e00828,0x180fe001380,0x5500aa0081,0x3300660110,0xf001e0220,0xaaaa2040,0x66664400,0x1e1e8800,0x1ff1000,0x33aaee2150,0xfaabe2260,0x8103ff100e,0x10811100000,0x1ffe1e1e828,0x1ff0203e00e]
theorem sample : Impossible false target 17 deck.toFinset := by
  intro k hk run
  have bound : 17≤deck.toFinset.card := by decide +kernel
  obtain ⟨F⟩ := polarOneShare run (hk.trans bound)
  have e0 := link_sound (a:=0x12a55540043) (b:=0xaaaa2040) F (show link deck target 0x12a55540043 0xaaaa2040 6 32 0 13 17 18=true by decide +kernel)
  have e1 := link_sound (a:=0xaaaa2040) (b:=0x1ff0203e00e) F (show link deck target 0xaaaa2040 0x1ff0203e00e 13 18 6 1 32 21=true by decide +kernel)
  have e2 := link_sound (a:=0x1ff0203e00e) (b:=0x12a55540043) F (show link deck target 0x1ff0203e00e 0x12a55540043 1 19 2 0 18 17=true by decide +kernel)
  exact polarOddThree _ _ _ e0 e1 e2
end PEqualNP.Outside.L_meta_9737.Order
