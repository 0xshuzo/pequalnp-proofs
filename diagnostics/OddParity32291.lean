import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_32291
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
abbrev Row := Fin 512
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
theorem polarDepends {S T} (H : PolarRooms true S T) {p n : Row}
    (agree : ∀ w∈S,bit p w=bit n w) : bit p T=bit n T := by
  cases hp : bit p T <;> cases hn : bit n T
  · rfl
  · obtain ⟨w,hw⟩ := H.total n p hn hp
    exact False.elim ((H.valid hw).2.1 (agree w (H.valid hw).1).symm)
  · obtain ⟨w,hw⟩ := H.total p n hp hn
    exact False.elim ((H.valid hw).2.1 (agree w (H.valid hw).1))
  · rfl

theorem polarForces {S T} (F : PolarFactor true S T) {p n : Row}
    (hp : bit p T=true) (hn : bit n T=false)
    (agree : ∀ w∈F.outer,bit p w=bit n w) : bit p F.pivot≠bit n F.pivot := by
  rcases F.outside.total p n hp hn with e | ⟨w,hw⟩
  · exact e.1
  · exact False.elim ((F.outside.valid hw).2.1 (agree w (F.outside.valid hw).1))
theorem polarPair {S T} (F : PolarFactor true S T) {w p n} (only : polarOnly true S T w p n) :
    bit p F.pivot≠bit n F.pivot ↔ w∈F.inner := by
  constructor
  · intro different
    by_contra missing
    apply different
    apply polarDepends F.inside
    intro v vin
    by_contra sep
    have eq := only.2.2 v (F.cover ▸ Finset.mem_union_left _ vin) ⟨sep,by simp⟩
    exact missing (eq ▸ vin)
  · intro wi
    apply polarForces F only.1 only.2.1
    intro v vo
    by_contra sep
    have eq := only.2.2 v (F.cover ▸ Finset.mem_union_right _ vo) ⟨sep,by simp⟩
    exact Finset.disjoint_left.mp F.apart wi (eq ▸ vo)

theorem roomPhase {S T} (H : PolarRooms true S T) (v : Sig) :
    ∃ phase : Bool, ∀ {p n}, H.owns v p n → bit p v=phase ∧ bit n v=!phase := by
  by_cases used : ∃ p n, H.owns v p n
  · obtain ⟨p0,n0,start⟩ := used
    refine ⟨bit p0 v,?_⟩
    intro p n here
    have d1 := (H.valid here).2.1
    have d2 := (H.valid (H.rect start here)).2.1
    cases z : bit p0 v <;> cases q : bit p v <;> cases r : bit n v <;> simp_all
  · exact ⟨false,fun h => False.elim (used ⟨_,_,h⟩)⟩

theorem freePolarPhase {S T pivot} (H : FreePolar true S T pivot) (v : Sig) :
    ∃ phase : Bool, ∀ {p n}, H.owns v p n → bit p v=phase ∧ bit n v=!phase := by
  by_cases used : ∃ p n, H.owns v p n
  · obtain ⟨p0,n0,start⟩ := used
    refine ⟨bit p0 v,?_⟩
    intro p n here
    have d1 := (H.valid here).2.1
    have d2 := (H.valid (H.rect start here)).2.1
    cases z : bit p0 v <;> cases q : bit p v <;> cases r : bit n v <;> simp_all
  · exact ⟨false,fun h => False.elim (used ⟨_,_,h⟩)⟩

theorem polarOuterOwn {S T} (F : PolarFactor true S T) {w p n} (wo : w∈F.outer)
    (one : polarOnly true S T w p n) : F.outside.owns w p n := by
  rcases F.outside.total p n one.1 one.2.1 with d | ⟨v,hv⟩
  · exact False.elim (Finset.disjoint_left.mp F.apart ((polarPair F one).mp d.1) wo)
  · have vs : v∈S := F.cover ▸ Finset.mem_union_right _ (F.outside.valid hv).1
    exact (one.2.2 v vs (F.outside.valid hv).2) ▸ hv

theorem polarInnerPhase {S T} (F : PolarFactor true S T) {w : Sig} (wi : w∈F.inner) :
    ∃ phase : Bool, ∀ {p n}, polarOnly true S T w p n → (bit p F.pivot == phase)=bit p w := by
  obtain ⟨phase,dir⟩ := roomPhase F.inside w
  refine ⟨phase,?_⟩
  intro p n one
  have d := (polarPair F one).mpr wi
  have found {r s} (hp : bit r F.pivot=true) (hn : bit s F.pivot=false)
      (only : ∀ u∈F.inner, bit r u≠bit s u → u=w) : F.inside.owns w r s := by
    apply polarOwn F.inside
    exact ⟨hp,hn,fun u hu diff => only u hu diff.1⟩
  have whole {v} (h : v∈F.inner) : v∈S := F.cover ▸ Finset.mem_union_left _ h
  cases hp : bit p F.pivot
  · have hn : bit n F.pivot=true := by cases q : bit n F.pivot <;> simp_all
    have owns := found hn hp (fun v vin diff => one.2.2 v (whole vin) ⟨Ne.symm diff,by simp⟩)
    have eq := (dir owns).2
    cases phase <;> simpa using eq.symm
  · have hn : bit n F.pivot=false := by cases q : bit n F.pivot <;> simp_all
    have owns := found hp hn (fun v vin diff => one.2.2 v (whole vin) ⟨diff,by simp⟩)
    have eq := (dir owns).1
    cases phase <;> simpa using eq.symm

theorem polarInnerOwn {S T} (F : PolarFactor true S T) {w p n}
    (wi : w∈F.inner) (one : polarOnly true S T w p n) :
    if bit p F.pivot then F.inside.owns w p n else F.inside.owns w n p := by
  have d := (polarPair F one).mpr wi
  have whole {v} (h : v∈F.inner) : v∈S := F.cover ▸ Finset.mem_union_left _ h
  cases hp : bit p F.pivot
  · have hn : bit n F.pivot=true := by cases h : bit n F.pivot <;> simp_all
    apply polarOwn F.inside
    exact ⟨hn,hp,fun v hv dir => one.2.2 v (whole hv) ⟨Ne.symm dir.1,by simp⟩⟩
  · have hn : bit n F.pivot=false := by cases h : bit n F.pivot <;> simp_all
    apply polarOwn F.inside
    exact ⟨hp,hn,fun v hv dir => one.2.2 v (whole hv) dir⟩
theorem beqPhaseInject {p q r : Bool} (h : (p==r)=(q==r)) : p=q := by
  cases p <;> cases q <;> cases r <;> simp_all

theorem polarOutsideCross {S T} (F : PolarFactor true S T) {a b p n pa pb na nb}
    (different : a≠b) (ao : a∈F.outer) (bo : b∈F.outer)
    (c1 : polarOnly true S T a p na) (c2 : polarOnly true S T b p nb)
    (c3 : polarOnly true S T a pa n) (c4 : polarOnly true S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (polarOuterOwn F ao c1) (polarOuterOwn F ao c3))
    (F.outside.rect (polarOuterOwn F bo c2) (polarOuterOwn F bo c4)))

theorem polarInsideCross {S T} (F : PolarFactor true S T) {a b p n pa pb na nb}
    (different : a≠b) (ai : a∈F.inner) (bi : b∈F.inner)
    (c1 : polarOnly true S T a p na) (c2 : polarOnly true S T b p nb)
    (c3 : polarOnly true S T a pa n) (c4 : polarOnly true S T b pb n)
    (matchA : bit p a=bit pa a) (matchB : bit p b=bit pb b) : False := by
  obtain ⟨sa,qa⟩ := polarInnerPhase F ai
  obtain ⟨sb,qb⟩ := polarInnerPhase F bi
  have sameA := beqPhaseInject ((qa c1).trans (matchA.trans (qa c3).symm))
  have sameB := beqPhaseInject ((qb c2).trans (matchB.trans (qb c4).symm))
  have h1 := polarInnerOwn F ai c1
  have h2 := polarInnerOwn F bi c2
  have h3 := polarInnerOwn F ai c3
  have h4 := polarInnerOwn F bi c4
  rw [←sameA] at h3
  rw [←sameB] at h4
  cases h : bit p F.pivot
  · simp only [h,Bool.false_eq_true,ite_false] at h1 h2 h3 h4
    exact different (F.inside.unique (F.inside.rect h3 h1) (F.inside.rect h4 h2))
  · simp only [h,ite_true] at h1 h2 h3 h4
    exact different (F.inside.unique (F.inside.rect h1 h3) (F.inside.rect h2 h4))

theorem polarBinate {S T} (F : PolarFactor true S T) {w p p' n n'} (ws : w∈S)
    (h : polarOnly true S T w p n) (j : polarOnly true S T w p' n')
    (different : bit p w≠bit p' w) : w∈F.inner := by
  by_contra no
  rw [←F.cover,Finset.mem_union] at ws
  have out := ws.resolve_left no
  obtain ⟨phase,dir⟩ := freePolarPhase F.outside w
  exact different ((dir (polarOuterOwn F out h)).1.trans (dir (polarOuterOwn F out j)).1.symm)

theorem polarOpposite {S T} (F : PolarFactor true S T) {a b p n pa pb na nb}
    (different : a≠b) (hs : a∈S) (ht : b∈S)
    (c1 : polarOnly true S T a p na) (c2 : polarOnly true S T b p nb)
    (c3 : polarOnly true S T a pa n) (c4 : polarOnly true S T b pb n)
    (matchA : bit p a=bit pa a) (matchB : bit p b=bit pb b) :
    (a∈F.inner) ↔ (b∉F.inner) := by
  constructor
  · intro aIn bIn
    exact polarInsideCross F different aIn bIn c1 c2 c3 c4 matchA matchB
  · intro bOut
    by_contra aOut
    rw [←F.cover,Finset.mem_union] at hs ht
    exact polarOutsideCross F different (hs.resolve_left aOut) (ht.resolve_left bOut) c1 c2 c3 c4


def polarCell (ws : List Sig) (T v : Sig) (p n : Row) :=
  bit p T && !bit n T && ws.all (fun w => (bit p w==bit n w) || w==v)
theorem polarCell_sound {ws T v p n} (h : polarCell ws T v p n=true) :
    polarOnly true ws.toFinset T v p n := by
  simp only [polarCell,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw sep
  have e : (bit p w==bit n w)=false := beq_eq_false_iff_ne.mpr sep.1
  simpa only [e,Bool.false_or,beq_iff_eq] using h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
theorem panelAnd {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h
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

def oddLink (ws : List Sig) (T a b : Sig) (rows : Nat) :=
  let r := kwProbe rows
  (decide (a∈ws ∧ b∈ws ∧ a≠b) && ((bit (r 0) a==bit (r 1) a) && (bit (r 0) b==bit (r 2) b))) &&
    ((polarCell ws T a (r 0) (r 4) && polarCell ws T b (r 0) (r 5)) &&
     (polarCell ws T a (r 1) (r 3) && polarCell ws T b (r 2) (r 3)))
theorem oddLink_sound {ws T a b rows} (F : PolarFactor true (List.toFinset ws) T)
    (h : oddLink ws T a b rows=true) : a∈F.inner ↔ b∉F.inner := by
  obtain ⟨mem,one⟩ := panelAnd h
  obtain ⟨ma,ph⟩ := panelAnd mem
  obtain ⟨am,bm,diff⟩ := of_decide_eq_true ma
  obtain ⟨left,right⟩ := panelAnd one
  exact polarOpposite F diff (List.mem_toFinset.mpr am) (List.mem_toFinset.mpr bm)
    (polarCell_sound (panelAnd left).1) (polarCell_sound (panelAnd left).2)
    (polarCell_sound (panelAnd right).1) (polarCell_sound (panelAnd right).2)
    (beq_iff_eq.mp (panelAnd ph).1) (beq_iff_eq.mp (panelAnd ph).2)
def oddCheck (ws : List Sig) (T : Sig) (k n : Nat) (labels rows : Nat→Nat) :=
  decide (k≤ws.toFinset.card) && (n==3 || n==5) &&
    (List.range n).all (fun i => oddLink ws T (ws.getD (labels i) zero)
      (ws.getD (labels ((i+1)%n)) zero) (rows i))
theorem oddCheck_sound {ws T k n labels rows} (ok : oddCheck ws T k n labels rows=true) :
    Impossible true T k ws.toFinset := by
  obtain ⟨budget,links⟩ := panelAnd ok
  intro j hj live
  obtain ⟨F⟩ := polarOneShare live (hj.trans (of_decide_eq_true (panelAnd budget).1))
  have edge (i : Nat) (bound : i<n) := oddLink_sound F
    (List.all_eq_true.mp links i (List.mem_range.mpr bound))
  have ar : n=3 ∨ n=5 := by
    simpa only [Bool.or_eq_true,beq_iff_eq] using (panelAnd budget).2
  rcases ar with rfl | rfl
  · exact polarOddThree _ _ _ (edge 0 (by decide)) (edge 1 (by decide)) (edge 2 (by decide))
  · exact polarOddFive _ _ _ _ _ (edge 0 (by decide)) (edge 1 (by decide))
      (edge 2 (by decide)) (edge 3 (by decide)) (edge 4 (by decide))

def raw (i : Nat) : Sig := BitVec.ofNat 512 ((((2:Nat)^512-1)/(2^(2^i)+1)) <<< (2^i))
def edgeTable : Sig := (raw 0 &&& raw 3) ||| (raw 1 &&& raw 4) ||| (raw 0 &&& raw 5) ||| (raw 1 &&& raw 5) ||| (raw 2 &&& raw 5) ||| (raw 0 &&& raw 6) ||| (raw 1 &&& raw 6) ||| (raw 3 &&& raw 6) ||| (raw 5 &&& raw 6) ||| (raw 1 &&& raw 7) ||| (raw 2 &&& raw 7) ||| (raw 3 &&& raw 7) ||| (raw 4 &&& raw 7) ||| (raw 6 &&& raw 7)
def gateCode (ws : List Sig) (c : Nat) : Sig :=
  bin (c/1024) (ws.getD (c%32) 0) (ws.getD ((c/32)%32) 0)
def wires (program : List Nat) (mask : Nat) : List Sig :=
  let ws := program.foldl (fun w c => w++[gateCode w c]) ((List.range 8).map raw)
  ((List.range ws.length).filter (fun i => mask.testBit i)).map (fun i => ws.getD i 0)

set_option maxHeartbeats 0 in
theorem odd_10_112 : Impossible true edgeTable 10 (wires [1056, 1219, 1319] 1535).toFinset := by
  apply oddCheck_sound (n:=3) (labels:=fun i => (1651 >>> (4*i)) &&& 15)
    (rows:=fun i => ([1418381329741992, 4508005221626048, 2957432919801948] : List Nat).getD i 0)
  decide +kernel

set_option maxHeartbeats 0 in
theorem odd_10_282 : Impossible true edgeTable 10 (wires [1120, 1217, 1285] 1791).toFinset := by
  apply oddCheck_sound (n:=5) (labels:=fun i => (471122 >>> (4*i)) &&& 15)
    (rows:=fun i => ([989028065544764, 5638368112441505, 740817478173213, 1418372857477800, 4539135128858757] : List Nat).getD i 0)
  decide +kernel

set_option maxHeartbeats 0 in
theorem odd_9_12 : Impossible true edgeTable 9 (wires [1056, 1184, 1318, 3399] 2558).toFinset := by
  apply oddCheck_sound (n:=3) (labels:=fun i => (1396 >>> (4*i)) &&& 15)
    (rows:=fun i => ([5638375643343009, 744665783550549, 2818065658380912] : List Nat).getD i 0)
  decide +kernel

set_option maxHeartbeats 0 in
theorem odd_9_16 : Impossible true edgeTable 9 (wires [1056, 1216, 1121, 3367] 3580).toFinset := by
  apply oddCheck_sound (n:=5) (labels:=fun i => (405586 >>> (4*i)) &&& 15)
    (rows:=fun i => ([1699846893092016, 4503882037293188, 989028065544764, 5638375643343009, 494526875648542] : List Nat).getD i 0)
  decide +kernel

set_option maxHeartbeats 0 in
theorem odd_8_15 : Impossible true edgeTable 8 (wires [1056, 1216, 1219, 1283, 3367] 7350).toFinset := by
  apply oddCheck_sound (n:=3) (labels:=fun i => (576 >>> (4*i)) &&& 15)
    (rows:=fun i => ([79241138173059, 5632799956115120, 986141839663646] : List Nat).getD i 0)
  decide +kernel

set_option maxHeartbeats 0 in
theorem odd_8_9 : Impossible true edgeTable 8 (wires [1056, 1216, 1121, 1219, 3367] 7604).toFinset := by
  apply oddCheck_sound (n:=5) (labels:=fun i => (270385 >>> (4*i)) &&& 15)
    (rows:=fun i => ([1699846909869232, 4503882037325956, 989028065544764, 5638375643343009, 494526875648542] : List Nat).getD i 0)
  decide +kernel

set_option maxHeartbeats 0 in
theorem odd_7_456 : Impossible true edgeTable 7 (wires [1089, 1185, 1221, 1347, 3424, 1286] 13976).toFinset := by
  apply oddCheck_sound (n:=3) (labels:=fun i => (84 >>> (4*i)) &&& 15)
    (rows:=fun i => ([2956934130219093, 740817478173213, 990937695402588] : List Nat).getD i 0)
  decide +kernel

set_option maxHeartbeats 0 in
theorem odd_7_10 : Impossible true edgeTable 7 (wires [1056, 1217, 1314, 1220, 3335, 2442] 10921).toFinset := by
  apply oddCheck_sound (n:=5) (labels:=fun i => (156432 >>> (4*i)) &&& 15)
    (rows:=fun i => ([740542600266269, 1418381330266280, 4503882037293188, 989028065544764, 5638366229716129] : List Nat).getD i 0)
  decide +kernel

end PEqualNP.Outside.L_meta_32291
