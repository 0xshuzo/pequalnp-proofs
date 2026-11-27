import Mathlib.Tactic.Tauto
import Mathlib.Tactic.NormNum
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_25467

namespace WordEngine
def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)
def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start
theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)
theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩
abbrev Word := Nat
abbrev RowState := Nat × List Word × List (Word × Word × Word)
def insertWord (w : Word) (ws : List Word) : List Word :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws
def childState (mask token : Nat) (state : RowState) : Option RowState :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 3
  let a := token / (4 * 3 * 64)
  let b := (token / (4 * 3)) % 64
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if op == 2 || keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)
def gateToken (a b op keep : Nat) : Nat := ((a * 64 + b) * 3 + op) * 4 + keep
def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask
def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words
def availableB (mask : Nat) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w
def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank
def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))
theorem restrictWord (mask : Nat) (word : Word) : word &&& mask &&& mask = word &&& mask := by
  simp
theorem projectGate {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots : List Word} {out : Word} (gate : GateWord mask roots out) :
    GateWord cut (roots.map (· &&& cut)) (out &&& cut) := by
  have av {word : Word} (ha : AvailableWord mask roots word) :
      AvailableWord cut (roots.map (· &&& cut)) (word &&& cut) := by
    rcases ha with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl submask)
    · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · refine Or.inl ⟨a &&& cut, av ha, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt := congrArg (fun n : Nat => n.testBit i) submask
    simp only [Nat.testBit_and, Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases cut.testBit i <;> simp
theorem availableWeaken {mask : Nat} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h
def properWord (mask word : Word) : Prop := word ≠ 0 ∧ word ≠ mask
def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a ||| b else a &&& b
theorem binWord_comm (d : Bool) (a b : Word) : binWord d a b = binWord d b a := by
  cases d <;> simp [binWord, Nat.land_comm, Nat.lor_comm]
variable {mask : Nat} {target : Word}
def LiveWord (mask : Nat) (target : Word) : Nat → Nat → Finset (Word) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ properWord mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Word)) (a : Word), t=u+1 ∧ S=insert a U ∧ properWord mask a ∧
      (mask ^^^ a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask ^^^ a)) U)) ∨
    (∃ (U : Finset (Word)) (a b : Word) (d : Bool), S=insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Word} (hp : properWord mask target) : LiveWord mask target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Word} {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
    (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Word} {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
    (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Word} {motive : ∀ (k t : Nat) (S : Finset (Word)), LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Word)} {a : Word} (ha : properWord mask a)
      (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)),
      motive k t (insert ((mask ^^^ a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Word)} {a b : Word} {d : Bool}
      (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)),
      motive k t (insert (binWord d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (LiveWord.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Word)} (h : LiveWord mask target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)
theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S, properWord mask a := by
  induction h using LiveWord.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
theorem liveWordSize {k t S} (h : LiveWord mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using LiveWord.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : (mask ^^^ a) ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : binWord d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩
def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  w ∈ ws ∨ ¬properWord mask w
def Masked (mask word : Nat) : Prop := word &&& mask = word
theorem maskedAvailable {bank : List Word} {word : Word}
    (all : ∀ w ∈ bank, Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word := by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw
theorem maskedGate {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateWord mask bank out) :
    Masked mask out := by
  rcases g with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, ea | ea⟩
  · have h := projectGate (mask := mask) (cut := mask) (by simp)
      (roots := bank) (out := mask ^^^ a) (Or.inl ⟨a, ha, rfl⟩)
    have ma := maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc, mb]
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA := congrArg (fun n : Nat => n.testBit i) ma
    have bitB := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all
def binaryWitness (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ d a b, a ∈ bank ∧ b ∈ bank ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ out = binWord d a b
theorem classifyBinary {bank : List Word}
    (all : ∀ w ∈ bank, Masked mask w) (d : Bool) {a b : Word}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b) := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Word} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  have ma : a &&& mask = a := maskedAvailable all ha
  have mb : b &&& mask = b := maskedAvailable all hb
  have absorbA : a ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha', pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma, binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, mb, wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord, absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb', pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord, ma, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord, absorbA] using cm)
  by_cases eq : a = b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord, wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d, a, b, ha', hb', pa, pb, eq, rfl⟩
theorem insertWordMem {x w : Word} {ws : List Word} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]
theorem insertWordNodup {w : Word} {ws : List Word} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩
theorem insertWordSet (w : Word) (ws : List Word) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]
theorem eraseWordSet {ws : List Word} (nd : ws.Nodup) (w : Word) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]
theorem gateTokenFields {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
    gateToken a b op keep % 4 = keep ∧
    gateToken a b op keep / 4 % 3 = op ∧
    gateToken a b op keep / (4 * 3 * 64) = a ∧
    gateToken a b op keep / (4 * 3) % 64 = b := by
  unfold gateToken
  omega
def keepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
  if save then ws else ws.erase w
theorem keepNodup {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd
theorem keepSubset (save : Bool) (w : Word) (ws : List Word) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h
theorem keepSet {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]
theorem keepPairSet {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h
theorem getWord {ws : List Word} {x : Word} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb
theorem binaryChild {mask fuel a b : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x y : Word} {keep : Nat}
    (d : Bool) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (binWord d x y)) (fresh : binWord d x y ∉ ws) :
    childState mask (gateToken a b (if d then 1 else 0) keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (binWord d x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (binWord d x y, x, y) :: history) := by
  have oh : (if d then 1 else 0) < 3 := by cases d <;> decide
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) hb64 oh hk
  simp only [childState, ke, op, aa, bb, hx, hy]
  cases d <;>
    simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, binWord, properWord]
variable {rows : Nat}
def fullMask (rows : Nat) : Nat := 2 ^ rows - 1
theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))
abbrev maskedFlat (m a : Word) : Prop := a &&& m = 0 ∨ a &&& m = m
def flatSet (m : Word) (s : Finset (Word)) := s.filter (maskedFlat m)
def visibleWords (m : Word) (s : Finset (Word)) := s.image fun w => w &&& m
theorem flIns {m a : Word} {s : Finset (Word)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]
theorem flLe (m a : Word) (s : Finset (Word)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]
theorem prIns (m a : Word) (s : Finset (Word)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..
theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp
theorem flBoth {m a b : Word} {d : Bool} (ha : maskedFlat m a) (hb : maskedFlat m b) :
    maskedFlat m (binWord d a b) := by
  unfold maskedFlat at *
  rw [cofBinary]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> cases d <;>
    simp [binWord, ha, hb]
theorem simpleBin {m a b : Word} {d : Bool} (h : maskedFlat m a ∨ maskedFlat m b) :
    binWord d a b &&& m = 0 ∨ binWord d a b &&& m = m ∨
      binWord d a b &&& m = a &&& m ∨ binWord d a b &&& m = b &&& m := by
  rw [cofBinary]
  have top1 (x : Word) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]
    simp
  have top2 (x : Word) : m ||| (x &&& m) = m := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and]
    cases x.testBit i <;> cases m.testBit i <;> rfl
  have right1 (x : Word) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Word) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  rcases h with (ha|ha)|(hb|hb) <;> cases d <;>
    simp [binWord, *, top1, top2, right1, right2]
def projectedStock (m : Word) (s : Finset (Word)) := insert 0 (insert m (visibleWords m s))
theorem availableB_spec {mask : Nat} {bank : List Word} {v : Word} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]
theorem flatCountCard (mask : Nat) {words : List Word} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]
abbrev PointWire (rows : Nat) := Fin rows → Bool
def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]
theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
def pointWord (f : PointWire rows) : Word := (encodePoint f).toNat
def relabel (sourceIndex : Fin rows → Fin rows) (word : Word) : Word :=
  pointWord fun i => word.testBit (sourceIndex i).val
theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]
theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))
theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]
theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]
theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq
theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i
theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)
theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Word} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]
theorem kw_step (goal : Word) (D D' : Finset Word) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, goal.testBit e = true → goal.testBit i = false →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, goal.testBit e = true → goal.testBit i = false → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_eq_left (h3), ite_eq_left (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_eq_right h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_eq_right h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_eq_right (h3n)]
        exact h3
theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all
def KWPartition (goal : Word) (ws : Finset Word) : Prop :=
  ∃ f : Nat → Nat → Word,
    (∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ ws ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
    (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true →
      goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
theorem kwFromLive {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) (tight : S.card = k + 1) : KWPartition goal S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    subst S
    exact ⟨fun _ _ => goal, fun _ _ hp hn => ⟨by simp, hp, hn⟩, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, eq, _⟩ | ⟨U, a, b, op, rfl, pa, pb, ab, fresh, tail⟩
    · omega
    let w := binWord op a b
    have wU : w ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have wA : w ≠ a := fun eq => fresh (Finset.mem_insert.mpr (Or.inl eq))
    have wB : w ≠ b := fun eq => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
    have tailSize := (liveWordSize tail).2
    change (insert w U).card + 0 ≤ k + 1 at tailSize
    rw [Finset.card_insert_of_notMem wU] at tailSize
    have paCard := Finset.card_insert_le a (insert b U)
    have pbCard := Finset.card_insert_le b U
    have aU : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      omega
    have bU : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have := Finset.card_insert_le a U
      omega
    obtain ⟨f, hf, hr⟩ := ih tail (by
      change (insert w U).card = k + 1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U := by simp [wA.symm, aU]
    have keepB : b ∉ insert w U := by simp [wB.symm, bU]
    have other : ∀ x ∈ insert w U, x ≠ w → x ∈ insert a (insert b U) := by
      intro x hx hn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
    have ha : a ∈ insert a (insert b U) := Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    cases op
    · exact kw_step goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => and_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv a b e i h1 h2 h3)
        (fun _ _ _ _ h => h.symm)
    · exact kw_step goal _ _ a b w (fun e _ => a.testBit e) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => or_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv a b e i h1 h2 h3)
        (fun _ _ _ _ _ => rfl)
theorem liveDirected {mask goal : Word} {k : Nat} {S : Finset Word}
    (live : LiveWord mask goal k 0 S) {p n : Nat}
    (hp : goal.testBit p = true) (hn : goal.testBit n = false) :
    ∃ w ∈ S, w.testBit p = true ∧ w.testBit n = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := live
    exact ⟨goal, by simp, hp, hn⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, ueq, _⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w, hw, wp, wn⟩ := ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n = false
        · exact ⟨a, Finset.mem_insert_self .., and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p = true
        · exact ⟨a, Finset.mem_insert_self .., or_cu a b p n wp wn ha⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩
namespace PackedRect
end PackedRect
def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal
abbrev WordMoveStep := List (Word × Nat) × List (Word × Nat)
abbrev WordMove := List WordMoveStep
def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right
def BitLinear (f : Word → Word) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true
theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]
theorem bitLinearOr {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩
theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩
theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩
theorem mixStepLinear (move : WordMoveStep) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih
def mixMove (move : WordMove) (w : Word) : Word :=
  (List.rec (motive := fun _ => Word → Word) id
    (fun step _ next w => next (mixStep step w)) move) w
theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]
theorem bitLinearComp {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩
theorem mixMoveLinear (move : WordMove) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)
theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Word} {move : WordMove}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Word} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩
theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]
theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Word} {move : WordMove}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Word} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩
theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]
theorem liveMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k t : Nat} {S : Finset Word} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)) := by
  let f := relabel select
  have hmask : f mask = mask := auto.2.1
  have inj {a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
      f a = f b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Word} (ma : Masked mask a) (ha : properWord mask a) :
      properWord mask (f a) := by
    exact ⟨fun eq => ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Word} {v : Word} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S, Masked mask w) : f v ∉ S.image f := by
    intro hw
    obtain ⟨w,hs,eq⟩ := Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton, auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v := mask ^^^ a
    have ma := masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v := by
      apply maskedGate (bank := [a]) (by simpa using ma)
      exact Or.inl ⟨a, Or.inr (Or.inr (by simp)), rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v = mask ^^^ f a := by
      change relabel select (mask ^^^ a) = _
      rw [relabelXor, auto.2.1]
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) (t+1) ((insert a U).image f)
    rw [Finset.image_insert] at ht hf
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (proper ma ha) hf ht
  | @binary k t U a b op pa pb ab fresh tail ih =>
    let v := binWord op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply maskedGate (bank := [a,b]) (by simpa using And.intro ma mb)
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v, binWord]⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have fve : f v = binWord op (f a) (f b) := by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) t ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h => ab (inj ma mb h)) hf ht
def dagMoveWords (m : WordMove) (ws : List Word) : List Word :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws
theorem dagMoveSet {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWords m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [dagMoveWords]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (dagMoveWords m ws)).toFinset = _
    rw [insertWordSet, ih (fun w hw => agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]
abbrev DagLink := Nat × Nat
abbrev DagLinks := Nat → Nat → Option DagLink
def dagRef (count : Nat) (states : Nat → Option RowState)
    (moves : Array WordMove) (links : DagLinks) (parent token : Nat) (state : RowState) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto-1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWords m state.2.1
def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)
theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩
theorem childStateData {mask token : Nat} {state child : RowState}
    (eval : childState mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let a := token / (4 * 3 * 64)
  let b := token / (4 * 3) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let rest := keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega,?_⟩
  have read (i : Nat) : AvailableWord mask ws (ws.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : ws[i]? with
    | none => exact Or.inl rfl
    | some a => exact Or.inr (Or.inr (List.mem_of_getElem? h))
  have hm : Masked mask z := by
    apply maskedGate masked
    unfold z
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
    · exact Or.inl ⟨x,read _,rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (op == 2 || keep.testBit 1) y _ w other
def DagMovesOK (mask goal : Word) (width : Nat) (moves : Array WordMove) : Prop :=
  ∀ (i : Nat) (m : WordMove), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w
abbrev DagMoveRecord (width : Nat) := WordMove × (Fin width → Fin width) × (Fin width → Fin width)
def dagMoves (cert : List (DagMoveRecord width)) : Array WordMove := (cert.map Prod.fst).toArray
def dagMoveRecordProps {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal
def dagMoveRecordOK {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)
theorem dagMoveRecordSpec {width : Nat} {mask goal : Word} {entry : DagMoveRecord width}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok
theorem dagMovesOfCheck {width : Nat} {mask goal : Word} {cert : List (DagMoveRecord width)}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩
theorem dagLinked {mask goal : Word} {width count : Nat} {states : Nat → Option RowState}
    {moves : Array WordMove} {links : DagLinks} {parent token : Nat} {state : RowState}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRef count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold dagRef at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination,saved,hd,eq,finish.1,?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select,auto,agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWords m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSet (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))
def dagLookupLinks (index data indexWidth sizeBits tokenBits destinationBits autoBits trials : Nat) :
    DagLinks := fun parent token =>
  let entry := unpack index indexWidth parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  let width := tokenBits + destinationBits + autoBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option DagLink) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := unpack data width mid
        let key := code &&& ((1 <<< tokenBits) - 1)
        if Nat.beq token key then
          some ((code >>> tokenBits) &&& ((1 <<< destinationBits) - 1),
            code >>> (tokenBits + destinationBits))
        else if Nat.blt token key then next lo mid else next (mid+1) hi
      else none) trials) offset (offset+size)
theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)
def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0
def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]
theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp
theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]
theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]
theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]
theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]
theorem suppliesOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)
end WordEngine

open WordEngine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Rep9102
abbrev AO (m : Nat) (stock : List Word) (out : Word) :=
  ∃ a b, AvailableWord m stock a ∧ AvailableWord m stock b ∧ (out = a &&& b ∨ out = a ||| b)
def AOBuild (m : Nat) (stock : List Word) : List Word → Prop
  | [] => True
  | w::ws => AO m stock w ∧ AOBuild m (w::stock) ws
def AOLower (m : Nat) (stock : List Word) (target : Word) (bound : Nat) : Prop :=
  ∀ vs, AOBuild m stock vs → AvailableWord m (vs++stock) target → bound ≤ vs.length
theorem aoOfAvailable {m stock w} (av : AvailableWord m stock w) : AO m stock w :=
  ⟨w,0,av,Or.inl rfl,Or.inr (by simp)⟩
theorem aoWeaken {m small big vs} (sub : ∀ w ∈ small, AvailableWord m big w)
    (h : AOBuild m small vs) : AOBuild m big vs := by
  induction vs generalizing small big with
  | nil => trivial
  | cons w ws ih =>
    obtain ⟨⟨a,b,ha,hb,ev⟩,tail⟩ := h
    refine ⟨⟨a,b,availableWeaken sub ha,availableWeaken sub hb,ev⟩,ih ?_ tail⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun v hv => Or.inr (Or.inr (List.mem_cons_of_mem _ hv))) (sub _ ha)
variable {mask target : Word}
theorem pullAO {w : List (Word)} {z : Word} {k S} (h : LiveWord mask target k 0 S)
    (hz : wordRep mask w z ∨ binaryWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+1 ∧ LiveWord mask target k' 0 S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k 0 (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : binWord d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
theorem extractAO {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : AOBuild mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k S, k ≤ values.length ∧ LiveWord mask target k 0 S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all (Or.inr builds.1)
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    have gate : wordRep mask roots w ∨ binaryWitness mask roots w := by
      obtain ⟨a,b,ha,hb,eq|eq⟩ := builds.1
      · subst w; exact classifyBinary all false ha hb
      · subst w; exact classifyBinary all true ha hb
    obtain ⟨k', S', hk', hl, hsub⟩ := pullAO live gate available
    exact ⟨k', S', by simp only [List.length_cons]; omega, hl, hsub⟩
theorem aoGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    AO (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact aoOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact aoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact aoOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact aoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
theorem aoBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ AOBuild (fullMask rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl hcsStep bank, v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[], rfl, trivial, fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := hcsGateVal bank g
    have hg := hfan g List.mem_cons_self
    obtain ⟨xs, len, build, sub⟩ := ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have eq : (hcsStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [hcsStep, v]
    rw [eq] at build
    refine ⟨v.toNat :: xs, by simp [len], ⟨aoGateWord bank g hg.1 hg.2, aoWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m
theorem monoFan {C : Circuit} (legal : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨op,sz⟩ := legal g hg
  refine ⟨?_,sz⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at op ⊢
  tauto
end Rep9102

open WordEngine PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace Rep9102
set_option maxHeartbeats 0 in
def posted (u v : Fin 5) : Bool := (25032655 : Nat).testBit (5*u.val+v.val)
set_option maxHeartbeats 0 in
def raw : List (BitVec 25) := [0x1f, 0x3e0, 0x7c00, 0xf8000, 0x1f00000, 0x210842, 0x421084, 0x842108, 0x1084210, 0x108421]
set_option maxHeartbeats 0 in
def stock : List Word := raw.map BitVec.toNat
set_option maxHeartbeats 0 in
def target25 : BitVec 25 := 0xfbefbe
set_option maxHeartbeats 0 in
abbrev T : Word := target25.toNat
set_option maxHeartbeats 0 in
def point (r : Fin 25) := oneEach (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 ((r.val % 5 + 4) % 5))
set_option maxHeartbeats 0 in
theorem representation_live (C : Circuit) (legal : Monotone2 C) (right : Represents posted C) :
    ∃ k ≤ C.size, LiveWord (fullMask 25) T k 0 stock.toFinset := by
  have rawBits : ∀ r : Fin 25, (raw.map fun w => w.getLsbD r.val) = point r := by decide +kernel
  have goalBits : ∀ r : Fin 25, target25.getLsbD r.val =
      posted (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 ((r.val % 5 + 4) % 5)) := by decide +kernel
  let eb := C.gates.foldl hcsStep raw
  have eq : eb.getD C.output 0 = target25 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Fin 25 := ⟨j,hj⟩
    have bits := hcsFoldBits raw r C.gates (monoFan legal)
    have ack := right (Fin.ofNat 5 (r.val / 5)) (Fin.ofNat 5 ((r.val % 5 + 4) % 5))
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (point r)).getD C.output false = _ at ack
    rw [← rawBits r,← bits] at ack
    exact (hcsGetDBit eb j C.output).trans (ack.trans (goalBits r).symm)
  obtain ⟨ws,len,built,sub⟩ := aoBuilds raw C.gates legal
  have hit : AvailableWord (fullMask 25) (ws++stock) T := by
    change AvailableWord _ _ target25.toNat
    rw [←eq,List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some w => exact Or.inr (Or.inr (sub w (List.mem_of_getElem? h)))
  obtain ⟨k,S,budget,run,subset⟩ := extractAO (stockMaskedOfCheck (by decide +kernel : stock.all (fun w => w &&& fullMask 25 == w) = true)) built hit
      (by unfold properWord; decide +kernel)
  have witnesses : ∀ w ∈ stock, ∃ p n : Fin 25, T.testBit p.val = true ∧ T.testBit n.val = false ∧
      ∀ u ∈ stock, u.testBit p.val = true → u.testBit n.val = false → u = w := by decide +kernel
  have same : S = stock.toFinset := by
    ext w; constructor
    · exact fun h => List.mem_toFinset.mpr (subset w h)
    · intro h
      obtain ⟨p,n,yes,no,unique⟩ := witnesses w (List.mem_toFinset.mp h)
      obtain ⟨u,mem,a,b⟩ := liveDirected run yes no
      exact (unique u (subset u mem) a b) ▸ mem
  exact ⟨k,budget.trans (Nat.le_of_eq len),same ▸ run⟩
end Rep9102

open WordEngine PEqualNP.Represents
namespace Rep9102.Orbit
set_option maxHeartbeats 0 in
def MonoViable (mask goal : Word) (s : RowState) : Prop :=
  s.2.1.Nodup ∧ ∃ k ≤ s.1, LiveWord mask goal k 0 s.2.1.toFinset
set_option maxHeartbeats 0 in
def AOChild (mask : Word) (s c : RowState) : Prop :=
  ∃ a b op keep, a < s.2.1.length ∧ a < b ∧ b < s.2.1.length ∧ op < 2 ∧ keep < 4 ∧
    childState mask (gateToken a b op keep) s = some c
set_option maxHeartbeats 0 in
theorem binaryMonoProgress {mask fuel k : Nat} {x y target : Word} {d : Bool} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k 0 (insert (binWord d x y) U)) :
    ∃ child, AOChild mask (fuel, ws, history) child ∧ MonoViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := binWord d x y
  have p := liveWordProper tail v (Finset.mem_insert_self _ _)
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep
    cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : RowState := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, hab, hb, ?_, keepLt, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k 0 (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail
set_option maxHeartbeats 0 in
theorem monoProgress {mask : Nat} {target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : MonoViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, AOChild mask state child ∧ MonoViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,impossible,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · omega
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryMonoProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k 0 (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryMonoProgress nd width cap eq' xy.symm (by omega) fresh' tail'
set_option maxHeartbeats 0 in
def coverAt (n : Nat) (ws : List Word) : Word :=
  List.rec 0 (fun w _ acc => if w.testBit n then acc else w ||| acc) ws
set_option maxHeartbeats 0 in
theorem coverAt_bit {w : Word} {ws : List Word} {p n : Nat}
    (member : w ∈ ws) (pos : w.testBit p = true) (neg : w.testBit n = false) :
    (coverAt n ws).testBit p = true := by
  induction ws with
  | nil => simp at member
  | cons x xs ih =>
    change (if x.testBit n then coverAt n xs else x ||| coverAt n xs).testBit p = true
    rcases List.mem_cons.mp member with rfl | tail
    · simp [neg, Nat.testBit_or, pos]
    · cases x.testBit n <;> simp [Nat.testBit_or, ih tail]
set_option maxHeartbeats 0 in
theorem coverAt_live {mask goal : Word} {ws : List Word} {k n : Nat}
    (live : LiveWord mask goal k 0 ws.toFinset) (neg : goal.testBit n = false) :
    goal &&& coverAt n ws = goal := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_and]
  cases h : goal.testBit p with
  | false => rfl
  | true =>
    obtain ⟨w,mem,one,zero⟩ := liveDirected live h neg
    simp [coverAt_bit (List.mem_toFinset.mp mem) one zero]
set_option maxHeartbeats 0 in
def basicCut (goal : Word) (neg : List Nat) (s : RowState) : Bool :=
  decide (s.1+1 < s.2.1.length) ||
    neg.any (fun n => (goal &&& coverAt n s.2.1) != goal)
set_option maxHeartbeats 0 in
theorem basicOpen {mask goal : Word} {neg : List Nat} {s : RowState}
    (negative : ∀ n ∈ neg, goal.testBit n = false) (v : MonoViable mask goal s) :
    basicCut goal neg s = false := by
  obtain ⟨nd,k,cap,live⟩ := v
  have size := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at size
  simp only [basicCut, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    List.any_eq_false, bne_iff_ne, ne_eq]
  constructor
  · omega
  · intro n mem
    simp [coverAt_live live (negative n mem)]
set_option maxHeartbeats 0 in
abbrev Table := Nat → Option RowState
set_option maxHeartbeats 0 in
abbrev EdgeCut := Nat → Nat → RowState → Bool
set_option maxHeartbeats 0 in
def pass (m g : Word) (neg : List Nat) (states : Table) (count : Nat)
    (moves : Array WordMove) (links : DagLinks) (cut : EdgeCut) (i : Nat)
    (s : RowState) (a b op keep : Nat) : Bool :=
  let tok := gateToken a b op keep
  match childState m tok s with
  | none => true
  | some c => basicCut g neg c || cut i tok c || dagRef count states moves links i tok c
set_option maxHeartbeats 0 in
def scan (m g : Word) (neg : List Nat) (states : Table) (count : Nat)
    (moves : Array WordMove) (links : DagLinks) (cut : EdgeCut) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some s =>
    let n := s.2.1.length
    dagStateOK m s.2.1 && decide (n ≤ 64) && !(s.2.1.contains g) &&
    treeBlock 0 n (fun a => treeBlock (a+1) (n-(a+1)) (fun b =>
      treeBlock 0 2 (fun op => treeBlock 0 4 (pass m g neg states count moves links cut i s a b op))))
set_option maxHeartbeats 0 in
theorem tableSound {m g : Word} {width count : Nat} {neg : List Nat} {states : Table}
    {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (mb : Masked (fullMask width) m) (autos : DagMovesOK m g width moves)
    (negative : ∀ n ∈ neg, g.testBit n = false)
    (cutOpen : ∀ i tok s, MonoViable m g s → cut i tok s = false)
    (checked : ∀ i < count, scan m g neg states count moves links cut i = true) :
    ∀ fuel i s, i < count → states i = some s → s.1 = fuel →
      ∀ k ≤ fuel, ¬ LiveWord m g k 0 s.2.1.toFinset := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    intro i s hi row cap k fit live
    have h := checked i hi
    simp only [scan, row, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨nd,masked⟩ := dagStateOKSpec h.1.1.1
    rcases monoProgress h.1.1.2 ⟨nd,k,cap ▸ fit,live⟩ with hit | ⟨c,edge,v⟩
    · simpa [hit] using h.1.2
    obtain ⟨a,b,op,keep,ha,hab,hb,hop,hkeep,ev⟩ := edge
    have aa := treeBlock_at h.2 (i := a) (Nat.zero_le _) (by simpa using ha)
    have bb := treeBlock_at aa (i := b) (by omega) (by omega)
    have oo := treeBlock_at bb (i := op) (Nat.zero_le _) (by simpa using hop)
    have kk := treeBlock_at oo (i := keep) (Nat.zero_le _) (by simpa using hkeep)
    simp only [pass, ev, basicOpen negative v, cutOpen _ _ _ v, Bool.false_or] at kk
    obtain ⟨less,cm⟩ := childStateData ev masked
    obtain ⟨_,j,fit',plan⟩ := v
    obtain ⟨dest,saved,inRange,lookup,eq,tail⟩ := dagLinked mb autos cm kk plan
    exact ih c.1 (cap ▸ less) dest saved inRange lookup eq j fit' tail
set_option maxHeartbeats 0 in
def diagonal : List Nat := [0,6,12,18,24]
set_option maxHeartbeats 0 in
theorem lowerFromTable {fuel count root : Nat} {states : Table} {s : RowState}
    {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (autos : DagMovesOK (fullMask 25) T 25 moves)
    (cuts : ∀ i tok c, MonoViable (fullMask 25) T c → cut i tok c = false)
    (checked : ∀ i < count, scan (fullMask 25) T diagonal states count moves links cut i = true)
    (bound : root < count) (lookup : states root = some s) (budget : s.1 = fuel)
    (bank : s.2.1.toFinset = stock.toFinset) : ¬ RepSizeAtMost posted fuel := by
  rintro ⟨C,legal,size,right⟩
  obtain ⟨k,fit,run⟩ := representation_live C legal right
  rw [←bank] at run
  exact tableSound (m := fullMask 25) (by unfold Masked; decide +kernel) autos
    (by decide +kernel : ∀ n ∈ diagonal, T.testBit n = false) cuts checked fuel root s bound
    lookup budget k (fit.trans size) run
end Rep9102.Orbit

open WordEngine
namespace Rep9102.Geometry
open Rep9102.Orbit
set_option maxHeartbeats 0 in
def forcesAt (goal : Word) (ws : List Word) (w : Word) (p n : Nat) : Bool :=
  goal.testBit p && !goal.testBit n &&
    ws.all (fun v => v == w || !v.testBit p || v.testBit n)
set_option maxHeartbeats 0 in
theorem forcedAnswer {g : Word} {ws : List Word} {w : Word} {p n : Nat}
    {f : Nat → Nat → Word}
    (legal : ∀ p n, g.testBit p = true → g.testBit n = false →
      f p n ∈ ws.toFinset ∧ (f p n).testBit p = true ∧ (f p n).testBit n = false)
    (h : forcesAt g ws w p n = true) :
    g.testBit p = true ∧ g.testBit n = false ∧ f p n = w := by
  simp only [forcesAt, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨mem,on,off⟩ := legal _ _ h.1.1 h.1.2
  have v := List.all_eq_true.mp h.2 _ (List.mem_toFinset.mp mem)
  exact ⟨h.1.1,h.1.2,by simpa [on,off] using v⟩
set_option maxHeartbeats 0 in
def overlap (g : Word) (ws : List Word) (x y : Word) (p n px nx py ny : Nat) : Bool :=
  x != y && forcesAt g ws x p nx && forcesAt g ws x px n &&
  forcesAt g ws y p ny && forcesAt g ws y py n
set_option maxHeartbeats 0 in
theorem overlapImpossible {g : Word} {ws : List Word} {x y p n px nx py ny : Nat}
    (kw : KWPartition g ws.toFinset) : overlap g ws x y p n px nx py ny = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨f,legal,box⟩ := kw
  simp only [overlap, Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨ne,a⟩,b⟩,c⟩,d⟩ := h
  obtain ⟨pos,nnx,xa⟩ := forcedAnswer legal a
  obtain ⟨ppx,neg,xb⟩ := forcedAnswer legal b
  obtain ⟨_,nny,ya⟩ := forcedAnswer legal c
  obtain ⟨ppy,_,yb⟩ := forcedAnswer legal d
  have X := box p nx px n pos ppx nnx neg (xa.trans xb.symm)
  have Y := box p ny py n pos ppy nny neg (ya.trans yb.symm)
  exact ne ((X.trans xa).symm.trans (Y.trans ya))
set_option maxHeartbeats 0 in
theorem tightPartition {m g : Word} {s : RowState} (live : MonoViable m g s)
    (tight : s.2.1.length = s.1+1) : KWPartition g s.2.1.toFinset := by
  obtain ⟨nd,k,fit,run⟩ := live
  have sz := (liveWordSize run).2
  have card := List.toFinset_card_of_nodup nd
  apply kwFromLive run
  omega
set_option maxHeartbeats 0 in
def rectangleReject (g : Word) (s : RowState) (code : Nat) : Bool :=
  let field := unpack code 5
  (s.2.1.length == s.1+1) &&
  overlap g s.2.1 (s.2.1.getD (field 0) 0) (s.2.1.getD (field 1) 0)
    (field 2) (field 3) (field 4) (field 5) (field 6) (field 7)
set_option maxHeartbeats 0 in
theorem rectangleOpen {m g : Word} {s : RowState} (code : Nat)
    (live : MonoViable m g s) : rectangleReject g s code = false := by
  unfold rectangleReject
  by_cases t : s.2.1.length = s.1+1
  · simp [t,overlapImpossible (tightPartition live t)]
  · simp [t]
end Rep9102.Geometry

open WordEngine
namespace Rep9102.Project
def Pool (g : Word) : Nat → Finset Word → Prop
  | 0, s => g ∈ s
  | n+1, s => Pool g n s ∨ ∃ a ∈ s, ∃ b ∈ s, ∃ d, Pool g n (insert (binWord d a b) s)
theorem weakenPool {g : Word} {n s q} (sub : s ⊆ q) (h : Pool g n s) : Pool g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,b,hb,d,run⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) run⟩
theorem maskedAO {mask goal : Word} {k s} (run : LiveWord mask goal k 0 s) (m : Word) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ Pool (goal &&& m) n (projectedStock m s) := by
  induction k generalizing s with
  | zero =>
    have es := run.2.1
    subst s
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | succ k ih =>
    rcases run with ⟨v,u,a,impossible,_⟩ | ⟨u,a,b,d,eq,pa,pb,ab,fresh,tail⟩
    · omega
    subst s
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih tail
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n+(flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k+1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa,fb,ite_true,ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBoth fa fb; simp only [vf,ite_true] at cap; omega | omega | tauto
      refine ⟨n,budget,weakenPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with e|e|e|e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · subst w
        have cases := simpleBin (d := d) simple
        tauto
      · tauto
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa,fb,ite_false] at ca cb
      refine ⟨n+1,by omega,Or.inr ⟨a &&& m,?_,b &&& m,?_,d,weakenPool ?_ built⟩⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto
theorem toBuild {m g : Word} {n s} {stock : List Word}
    (sources : ∀ x ∈ s, AvailableWord m stock x) (h : Pool g n s) :
    ∃ vs, vs.length ≤ n ∧ AOBuild m stock vs ∧ AvailableWord m (vs ++ stock) g := by
  induction n generalizing s stock with
  | zero => exact ⟨[],by simp,True.intro,sources g h⟩
  | succ n ih =>
    rcases h with h | ⟨a,ha,b,hb,d,h⟩
    · obtain ⟨vs,len,built,hit⟩ := ih sources h; exact ⟨vs,by omega,built,hit⟩
    · let z := binWord d a b
      have sub : ∀ x ∈ insert z s, AvailableWord m (z::stock) x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun v hv => Or.inr (Or.inr (List.mem_cons_of_mem _ hv))) (sources _ hx)
      obtain ⟨vs,len,built,hit⟩ := ih sub h
      refine ⟨z::vs,by simp; omega,⟨⟨a,b,sources _ ha,sources _ hb,?_⟩,built⟩,?_⟩
      · cases d <;> simp [z,binWord]
      · rcases hit with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_left_comm,or_assoc] using h))
theorem appendAO {mask : Word} {stock xs ys : List Word} (left : AOBuild mask stock xs)
    (right : AOBuild mask (xs ++ stock) ys) : AOBuild mask stock (xs ++ ys) := by
  induction xs generalizing stock with
  | nil => exact right
  | cons x xs ih =>
    refine ⟨left.1, ih left.2 (aoWeaken ?_ right)⟩
    intro w hw
    exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hw))
theorem cut {mask goal m k S stock prep floor} (run : LiveWord mask goal k 0 S)
    (proper : ¬ maskedFlat m goal) (built : AOBuild m stock prep)
    (supply : ∀ x ∈ projectedStock m S, AvailableWord m (prep ++ stock) x)
    (lower : AOLower m stock (goal &&& m) floor) :
    floor + (flatSet m S).card ≤ prep.length + k := by
  obtain ⟨n,len,red⟩ := maskedAO run m proper
  obtain ⟨vs,cap,prog,hit⟩ := toBuild supply red
  have total := appendAO built prog
  have hit' : AvailableWord m ((prep++vs)++stock) (goal &&& m) := by
    rcases hit with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by simpa [List.mem_append,or_left_comm,or_comm,or_assoc] using h))
  have bound := lower _ total hit'
  simp only [List.length_append] at bound
  omega
end Rep9102.Project

open WordEngine
namespace Rep9102.Project
def oneAO (stock : List Word) (w : Word) : Bool :=
  stock.any fun a => stock.any fun b => (a &&& b == w) || (a ||| b == w)
theorem oneAO_spec {m : Word} {stock w} (h : oneAO stock w) : AO m stock w := by
  obtain ⟨a,ha,ok⟩ := List.any_eq_true.mp h
  obtain ⟨b,hb,ok⟩ := List.any_eq_true.mp ok
  have eq := Bool.or_eq_true_iff.mp ok
  exact ⟨a,b,Or.inr (Or.inr ha),Or.inr (Or.inr hb),eq.elim (fun e => Or.inl (eq_of_beq e).symm)
    (fun e => Or.inr (eq_of_beq e).symm)⟩
def cheapPrep (m : Word) (stock : List Word) : List Word → Option (List Word)
  | [] => some []
  | w::ws =>
    if availableB m stock w then cheapPrep m stock ws
    else if oneAO stock w then (cheapPrep m (w::stock) ws).map (w::·)
    else none
theorem inLarger {m w : Word} {xs raw : List Word} (h : AvailableWord m raw w) :
    AvailableWord m (xs ++ raw) w :=
  availableWeaken (fun _ hw => Or.inr (Or.inr (List.mem_append_right _ hw))) h
theorem cheapPrep_spec {m : Word} {stock needed vs}
    (h : cheapPrep m stock needed = some vs) :
    AOBuild m stock vs ∧ ∀ w ∈ needed, AvailableWord m (vs++stock) w := by
  induction needed generalizing stock vs with
  | nil =>
    obtain rfl := Option.some.inj h
    exact ⟨True.intro,by simp⟩
  | cons w ws ih =>
    simp only [cheapPrep] at h
    split at h
    · rename_i present
      obtain ⟨built,covered⟩ := ih h
      refine ⟨built,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact inLarger (availableB_spec.mp present)
      · exact covered _ hv
    · split at h
      · rename_i step
        cases he : cheapPrep m (w::stock) ws with
        | none => simp [he] at h
        | some more =>
          simp [he] at h
          subst vs
          obtain ⟨built,covered⟩ := ih he
          refine ⟨⟨oneAO_spec step,built⟩,?_⟩
          intro v hv
          rcases List.mem_cons.mp hv with rfl | hv
          · exact Or.inr (Or.inr (by simp))
          · apply availableWeaken (small := more++w::stock) (big := (w::more)++stock) _ (covered v hv)
            intro x hx
            exact Or.inr (Or.inr (by simpa [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hx))
      · contradiction
def cheapCut (m : Word) (low fuel : Nat) (stock ws : List Word) : Bool :=
  let needed := ws.map (· &&& m)
  match cheapPrep m stock needed with
  | none => false
  | some vs => decide (vs.length + fuel < low + flatCount m ws)
theorem cheapCut_sound {m mask goal low fuel stock ws k}
    (lower : AOLower m stock (goal &&& m) low) (proper : ¬ maskedFlat m goal)
    (nd : ws.Nodup) (hk : k ≤ fuel) (close : cheapCut m low fuel stock ws = true) :
    ¬ LiveWord mask goal k 0 ws.toFinset := by
  intro run
  unfold cheapCut at close
  cases he : cheapPrep m stock (ws.map (· &&& m)) with
  | none => simp [he] at close
  | some vs =>
    simp [he] at close
    obtain ⟨built,covered⟩ := cheapPrep_spec he
    have source : ∀ w ∈ projectedStock m ws.toFinset, AvailableWord m (vs++stock) w := by
      intro w hw
      simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image,List.mem_toFinset] at hw
      rcases hw with rfl | rfl | ⟨v,hv,rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact covered _ (List.mem_map_of_mem hv)
    have bound := cut run proper built source lower
    rw [flatCountCard m nd] at close
    omega
end Rep9102.Project

open WordEngine
namespace Rep9102.Project
theorem lowerFromPrep {m goal low : Word} {raw derived prep : List Word}
    (h : cheapPrep m raw derived = some prep) (floor : AOLower m raw goal low) :
    AOLower m derived goal (low-prep.length) := by
  obtain ⟨built,supply⟩ := cheapPrep_spec h
  intro vs prog hit
  have combined := appendAO built (aoWeaken supply prog)
  have hv : AvailableWord m ((prep++vs)++raw) goal := by
    rcases hit with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases List.mem_append.mp h with hy | hy
      · exact Or.inr (Or.inr (by simp [List.mem_append,hy]))
      · exact availableWeaken (small := prep++raw) (big := (prep++vs)++raw)
          (fun a ha => Or.inr (Or.inr (by simpa only [List.mem_append] using
            (show (a ∈ prep ∨ a ∈ vs) ∨ a ∈ raw from (List.mem_append.mp ha).elim
              (fun h => Or.inl (Or.inl h)) Or.inr)))) (supply goal hy)
  have bound := floor _ combined hv
  simp only [List.length_append] at bound
  omega
abbrev Minor := Word × Nat × List Word
def Minor.mask (x : Minor) : Word := x.1
def Minor.low (x : Minor) : Nat := x.2.1
def Minor.raw (x : Minor) : List Word := x.2.2
def Minor.Valid (goal : Word) (q : Minor) : Prop :=
  ¬ maskedFlat q.mask goal ∧ AOLower q.mask q.raw (goal &&& q.mask) q.low
def bankCut (minors : Array Minor) (hint : Nat → Nat → Nat) : Orbit.EdgeCut :=
  fun i tok s =>
    match minors[hint i tok]? with
    | none => false
    | some q => cheapCut q.mask q.low s.1 q.raw s.2.1
theorem bankCut_open {goal mask : Word} {minors : Array Minor} {hint : Nat → Nat → Nat}
    (valid : ∀ q ∈ minors, Minor.Valid goal q) (i tok s) (v : Orbit.MonoViable mask goal s) :
    bankCut minors hint i tok s = false := by
  obtain ⟨nd,k,fit,run⟩ := v
  unfold bankCut
  cases h : minors[hint i tok]? with
  | none => rfl
  | some q =>
    have proof := valid q (Array.mem_of_getElem? h)
    exact Bool.eq_false_iff.mpr (fun pos => cheapCut_sound proof.2 proof.1 nd fit pos run)
end Rep9102.Project

open WordEngine
namespace Rep9102.Project
def geometryOrMinor (minors : Array Minor) (hint : Nat → Nat → Nat) : Orbit.EdgeCut :=
  fun i tok s =>
    let code := hint i tok
    if code < 16 then bankCut minors hint i tok s else Geometry.rectangleReject T s (code - 16)
theorem geometryOrMinor_open {mask} {minors : Array Minor} {hint : Nat → Nat → Nat}
    (valid : ∀ q ∈ minors, Minor.Valid T q) (i tok s) (v : Orbit.MonoViable mask T s) :
    geometryOrMinor minors hint i tok s = false := by
  simp only [geometryOrMinor]
  split
  · exact bankCut_open valid i tok s v
  · exact Geometry.rectangleOpen _ v
end Rep9102.Project

open WordEngine
namespace Rep9102.Orbit
abbrev requiredTests (width : Nat) (goal : Word) (ws : List Word) : Prop :=
  ∀ w ∈ ws, ∃ p n : Fin width, goal.testBit p.val = true ∧ goal.testBit n.val = false ∧
    ∀ v ∈ ws, v.testBit p.val = true → v.testBit n.val = false → v = w

theorem lowerStock {m goal width fuel root count raw} {states : Table} {row : RowState}
    {neg : List Nat} {moves : Array WordMove} {links : DagLinks} {cut : EdgeCut}
    (all : ∀ w ∈ raw, Masked m w) (proper : properWord m goal) (needs : requiredTests width goal raw)
    (mb : Masked (fullMask width) m) (autos : DagMovesOK m goal width moves)
    (negative : ∀ n ∈ neg, goal.testBit n = false)
    (cutOpen : ∀ i tok s, MonoViable m goal s → cut i tok s = false)
    (checked : ∀ i < count, scan m goal neg states count moves links cut i = true)
    (index : root < count) (look : states root = some row) (rFuel : row.1 = fuel)
    (exactStock : row.2.1.toFinset = raw.toFinset) : AOLower m raw goal (fuel+1) := by
  intro vs builds hit
  by_contra! h
  obtain ⟨k,S,budget,live,sub⟩ := extractAO all builds hit proper
  have eq : S = raw.toFinset := by
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub _ hw)
    · intro hw
      obtain ⟨p,n,yes,no,only⟩ := needs _ (List.mem_toFinset.mp hw)
      obtain ⟨v,hv,a,b⟩ := liveDirected live yes no
      exact (only v (sub v hv) a b) ▸ hv
  rw [eq,←exactStock] at live
  exact tableSound mb autos negative cutOpen checked fuel root row index look rFuel k (by omega) live
def joined : List Word := [1082431,2165730,4357252,9412872,33047056]
theorem joinedTests : requiredTests 25 T joined := by decide +kernel
end Rep9102.Orbit

open WordEngine
namespace Rep9102.CompactMoves
abbrev RawMove := WordMove × Nat × Nat
def rawMove (code : Nat) : RawMove := Id.run do
  let mut left := Array.replicate 25 0
  let mut right := Array.replicate 25 0
  let mut select := 0
  let mut inverse := 0
  for s in [:25] do
    let r := unpack code 3 (s/5)
    let c := unpack code 3 (s % 5)
    let d := if code.testBit 15 then 5*c+r else 5*r+c
    if s ≤ d then left := left.modify (d-s) (· ||| (1 <<< s))
    else right := right.modify (s-d) (· ||| (1 <<< s))
    select := select ||| (s <<< (5*d))
    inverse := inverse ||| (d <<< (5*s))
  let parts := fun (a : Array Nat) => (List.range 25).filterMap (fun n =>
    if a[n]! == 0 then none else some (a[n]!,n))
  return ([(parts left,parts right)],select,inverse)
def rawList (count packed : Nat) : List RawMove :=
  (List.range count).map (fun i => rawMove (unpack packed 16 i))
def record (r : RawMove) : DagMoveRecord 25 :=
  (r.1,fun i => Fin.ofNat 25 (unpack r.2.1 5 i.val),fun i => Fin.ofNat 25 (unpack r.2.2 5 i.val))
end Rep9102.CompactMoves

open WordEngine

namespace Rep9102.SmallCrown

open Orbit

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def records : List (DagMoveRecord 25) := [
([([(0x1041041,0),(0x82082,4),(0x4104,8),(0x208,12),(0x10,16)], [(0x820820,4),(0x410400,8),(0x208000,12),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack (0x189b924bc9a81da2 * 0x10000000000000000 + 0xc38ab0598347a8a0) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x189b924bc9a81da2 * 0x10000000000000000 + 0xc38ab0598347a8a0) 5 i.val))),
([([(0x1300273,0),(0x400084,1),(0x2000,4),(0x4c00,5),(0x1000,6)], [(0x800108,1),(0x20000,4),(0x98000,5),(0x40000,6)])], (fun i => Fin.ofNat 25 (unpack (0x18b5eb4731ab54e3 * 0x10000000000000000 + 0x283d27418a410c20) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18b5eb4731ab54e3 * 0x10000000000000000 + 0x283d27418a410c20) 5 i.val))),
([([(0x1022041,0),(0x80100,3),(0x2,4),(0x1000,6),(0x8,7),(0x4080,9),(0x200,12),(0x4,13),(0x10,16)], [(0x400800,3),(0x20,4),(0x40000,6),(0x400,7),(0x810000,9),(0x200000,12),(0x8000,13),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack (0x1874d24b322715db * 0x10000000000000000 + 0x240eab8183453ca0) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x1874d24b322715db * 0x10000000000000000 + 0x240eab8183453ca0) 5 i.val))),
([([(0x19c8019,0),(0x210002,1),(0x80,4),(0x320,5),(0x40,6)], [(0x420004,1),(0x800,4),(0x6400,5),(0x1000,6)])], (fun i => Fin.ofNat 25 (unpack (0x18bd6d49ca117a50 * 0x10000000000000000 + 0x6395cd5b14418440) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18bd6d49ca117a50 * 0x10000000000000000 + 0x6395cd5b14418440) 5 i.val))),
([([(0x1040881,0),(0x2004,3),(0x80000,4),(0x40,6),(0x4000,7),(0x102,9),(0x8,12),(0x200,13),(0x10,16)], [(0x10020,3),(0x800000,4),(0x1000,6),(0x200000,7),(0x20400,9),(0x8000,12),(0x400000,13),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack (0x189a5c4bc90d1d60 * 0x10000000000000000 + 0x6586d13b05479540) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x189a5c4bc90d1d60 * 0x10000000000000000 + 0x6586d13b05479540) 5 i.val))),
([([(0x1100011,0),(0x600006,1),(0x2100,3),(0x4620,5),(0x18c0,6)], [(0x800008,2),(0x30000,9),(0x88000,10),(0x40000,12)])], (fun i => Fin.ofNat 25 (unpack (0x18b56f47316d524e * 0x10000000000000000 + 0x641671849e410460) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18aded4499072ce1 * 0x10000000000000000 + 0x28bdcb6b14408c40) 5 i.val))),
([([(0x1000001,0),(0x80808,2),(0x1040,6),(0x4002,9),(0x80,10),(0x204,13),(0x10,16)], [(0x20100,1),(0x400020,3),(0x12000,5),(0x200400,7),(0x40000,12),(0x808000,14),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack (0x1872664b30f11556 * 0x10000000000000000 + 0x6806ed44874515e0) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x184cdc4a9a0b0dd1 * 0x10000000000000000 + 0x268ec78b0542bd40) 5 i.val))),
([([(0x1100011,0),(0x200002,2),(0x180,9),(0x220,10),(0x40,12)], [(0xc0000c,1),(0x10800,3),(0x8c400,5),(0x63000,6)])], (fun i => Fin.ofNat 25 (unpack (0x18aded4499072ce1 * 0x10000000000000000 + 0x28bdcb6b14408c40) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18b56f47316d524e * 0x10000000000000000 + 0x641671849e410460) 5 i.val))),
([([(0x1000001,0),(0x10080,1),(0x80004,3),(0x900,5),(0x4008,7),(0x40,12),(0x202,14),(0x10,16)], [(0x202020,2),(0x41000,6),(0x800400,9),(0x20000,10),(0x408000,13),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack (0x184cdc4a9a0b0dd1 * 0x10000000000000000 + 0x268ec78b0542bd40) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x1872664b30f11556 * 0x10000000000000000 + 0x6806ed44874515e0) 5 i.val))),
([([(0x1011101,0),(0x80008,2),(0x880,6),(0x4004,8),(0x40,12),(0x202,14),(0x10,16)], [(0x200020,2),(0x22000,6),(0x400400,8),(0x40000,12),(0x808000,14),(0x100000,16)])], (fun i => Fin.ofNat 25 (unpack (0x184ba64a99700d8e * 0x10000000000000000 + 0xc88ae86c8742a9e0) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x184ba64a99700d8e * 0x10000000000000000 + 0xc88ae86c8742a9e0) 5 i.val))),
([([(0x1ce7000,0),(0x108400,1),(0x2,4),(0x1c,5),(0x1,6)], [(0x210800,1),(0x20,4),(0x380,5),(0x40,6)])], (fun i => Fin.ofNat 25 (unpack (0x18bda959ca2f839a * 0x10000000000000000 + 0xc52c831002941ca6) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18bda959ca2f839a * 0x10000000000000000 + 0xc52c831002941ca6) 5 i.val))),
([([(0x1041022,0),(0x80,3),(0x82000,4),(0x1,6),(0x100,7),(0x4000,8),(0x4,9),(0x200,11),(0x8,13),(0x10,17)], [(0x400,3),(0x820000,4),(0x40,6),(0x8000,7),(0x400000,8),(0x800,9),(0x100000,11),(0x10000,13),(0x200000,17)])], (fun i => Fin.ofNat 25 (unpack (0x189b889bc9a345a2 * 0x10000000000000000 + 0xc11e8f500b582c26) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x189b889bc9a345a2 * 0x10000000000000000 + 0xc11e8f500b582c26) 5 i.val))),
([([(0x1000000,0),(0x500000,1),(0x280a,4),(0x4010,5),(0x1405,6)], [(0xa00000,1),(0x280a0,4),(0x80200,5),(0x50140,6)])], (fun i => Fin.ofNat 25 (unpack (0x18b5e95731aa5ce3 * 0x10000000000000000 + 0x27c082180293a0a6) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18b5e95731aa5ce3 * 0x10000000000000000 + 0x27c082180293a0a6) 5 i.val))),
([([(0x1022022,0),(0x100,2),(0x80000,3),(0x1001,6),(0x88,8),(0x4000,9),(0x200,11),(0x4,14),(0x10,17)], [(0x400,2),(0x400000,3),(0x40040,6),(0x8800,8),(0x800000,9),(0x100000,11),(0x10000,14),(0x200000,17)])], (fun i => Fin.ofNat 25 (unpack (0x1874c89b32223ddb * 0x10000000000000000 + 0x21a28a780b55c026) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x1874c89b32223ddb * 0x10000000000000000 + 0x21a28a780b55c026) 5 i.val))),
([([(0x18c0000,0),(0x318000,1),(0x84,3),(0x318,5),(0x63,6)], [(0x420000,2),(0xc00,9),(0x6000,10),(0x1000,12)])], (fun i => Fin.ofNat 25 (unpack (0x18bd6969ca0f8a50 * 0x10000000000000000 + 0x629c830804e6ad4c) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18bd2d59c9f18106 * 0x10000000000000000 + 0x105cd53169414e6) 5 i.val))),
([([(0x1040000,0),(0x2020,2),(0x80000,4),(0x4041,6),(0x100,9),(0x2,10),(0x208,13),(0x10,17)], [(0x804,1),(0x10000,3),(0x800000,4),(0x480,5),(0x208000,7),(0x100000,11),(0x1000,12),(0x20000,14),(0x400000,18)])], (fun i => Fin.ofNat 25 (unpack (0x189a48ebc9036d60 * 0x10000000000000000 + 0x60ae8f2815689c4c) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18991c9bc86d451e * 0x10000000000000000 + 0x516d1130f580566) 5 i.val))),
([([(0x1000000,0),(0x700000,1),(0x2108,2),(0x4210,5),(0x1ce7,6)], [(0x800000,3),(0x38000,14),(0x80000,15),(0x40000,18)])], (fun i => Fin.ofNat 25 (unpack (0x18b56977316a6a4e * 0x10000000000000000 + 0x62a082080738c1f2) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18a5ed5200620cdf * 0x10000000000000000 + 0x28c1ca6b1692a0e6) 5 i.val))),
([([(0x1000000,0),(0x80000,1),(0x820,2),(0x1041,6),(0x4000,9),(0x82,10),(0x200,13),(0x4,14),(0x10,17)], [(0x20408,2),(0x400000,3),(0x10100,6),(0x200000,7),(0xa000,10),(0x100000,11),(0x40000,18),(0x800000,19)])], (fun i => Fin.ofNat 25 (unpack (0x1872493b30e28d56 * 0x10000000000000000 + 0x60c28a281f76a072) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x1824dc9a01ea2dc7 * 0x10000000000000000 + 0x26a2c28b0f50c166) 5 i.val))),
([([(0x18c0000,0),(0x108000,2),(0x6,9),(0x18,10),(0x1,12)], [(0x630000,1),(0x420,3),(0x6300,5),(0x18c0,6)])], (fun i => Fin.ofNat 25 (unpack (0x18bd2d59c9f18106 * 0x10000000000000000 + 0x105cd53169414e6) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18bd6969ca0f8a50 * 0x10000000000000000 + 0x629c830804e6ad4c) 5 i.val))),
([([(0x1040000,0),(0x402,1),(0x2000,3),(0x80000,4),(0x24,5),(0x4100,7),(0x200,11),(0x1,12),(0x8,14),(0x10,18)], [(0x8080,2),(0x800000,4),(0x101040,6),(0x20000,9),(0x800,10),(0x410000,13),(0x200000,17)])], (fun i => Fin.ofNat 25 (unpack (0x18991c9bc86d451e * 0x10000000000000000 + 0x516d1130f580566) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x189a48ebc9036d60 * 0x10000000000000000 + 0x60ae8f2815689c4c) 5 i.val))),
([([(0x1000000,0),(0x400000,1),(0x100000,2),(0x2000,3),(0x800,4),(0x4000,5),(0x1000,6),(0x400,7),(0x8,8),(0x2,9),(0x10,10),(0x4,11),(0x1,12)], [(0x200000,1),(0x800000,2),(0x20,3),(0x80,4),(0x200,5),(0x40,6),(0x100,7),(0x8000,8),(0x20000,9),(0x80000,10),(0x10000,11),(0x40000,12)])], (fun i => Fin.ofNat 25 (unpack (0x18b52f57314d5904 * 0x10000000000000000 + 0x186717ca0939506) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18ade96499053ce1 * 0x10000000000000000 + 0x27c4811804e5b54c) 5 i.val))),
([([(0x1000000,0),(0x2,1),(0x80000,2),(0x400,3),(0x8,4),(0x20,5),(0x1000,6),(0x80,8),(0x4000,9),(0x200,11),(0x1,12),(0x4,15),(0x10,18)], [(0x20000,1),(0x400100,3),(0x8000,4),(0x2000,5),(0x100040,6),(0x800,8),(0x40000,12),(0x800000,14),(0x10000,15),(0x200000,17)])], (fun i => Fin.ofNat 25 (unpack (0x1871269b30513d14 * 0x10000000000000000 + 0x796ed1c91558606) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x184cc8ea9a015dd1 * 0x10000000000000000 + 0x21b685781563c44c) 5 i.val))),
([([(0x1ad0340,0),(0x108020,2),(0x4,8),(0x1a,10),(0x1,12)], [(0x420080,2),(0x400,8),(0x6800,10),(0x1000,12)])], (fun i => Fin.ofNat 25 (unpack (0x18bd2b69c9f08906 * 0x10000000000000000 + 0x8928298ee6a96c) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18bd2b69c9f08906 * 0x10000000000000000 + 0x8928298ee6a96c) 5 i.val))),
([([(0x1000040,0),(0x80000,1),(0x400,3),(0x1022,6),(0x4080,9),(0x201,12),(0x4,15),(0x10,18)], [(0x8,1),(0x20000,2),(0x400800,3),(0x8000,5),(0x100000,6),(0x100,7),(0x2000,10),(0x10000,11),(0x200000,12),(0x40000,18),(0x800000,19)])], (fun i => Fin.ofNat 25 (unpack (0x1871133b30478d14 * 0x10000000000000000 + 0x2beab09a1768d12) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x1824d2ea01e555c7 * 0x10000000000000000 + 0x2436a181976144ec) 5 i.val))),
([([(0x1000000,0),(0x300000,2),(0x18c,8),(0x210,10),(0x63,12)], [(0xc00000,2),(0x18c00,8),(0x84000,10),(0x63000,12)])], (fun i => Fin.ofNat 25 (unpack (0x18ad2f6498a83902 * 0x10000000000000000 + 0x18a707ca2e5a9ac) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18ad2f6498a83902 * 0x10000000000000000 + 0x18a707ca2e5a9ac) 5 i.val))),
([([(0x1010504,0),(0x80000,2),(0x808,4),(0x4000,6),(0x20,8),(0x41,12),(0x200,14),(0x2,16),(0x10,18)], [(0x200000,2),(0x8080,4),(0x100000,6),(0x2000,8),(0x41000,12),(0x800000,14),(0x20000,16),(0x400000,18)])], (fun i => Fin.ofNat 25 (unpack (0x184926ea98305d0a * 0x10000000000000000 + 0x7aae81c9b638a2c) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x184926ea98305d0a * 0x10000000000000000 + 0x7aae81c9b638a2c) 5 i.val))),
([([(0x1000000,0),(0x300000,2),(0x108,7),(0x84,9),(0x210,10),(0x63,12)], [(0x400000,1),(0x800c00,3),(0x4000,5),(0x1000,6),(0x2000,8),(0x18000,13),(0x80000,15),(0x20000,16),(0x40000,18)])], (fun i => Fin.ofNat 25 (unpack (0x18ad2d7498a74102 * 0x10000000000000000 + 0x10dcb531b383e32) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18a56f620023124a * 0x10000000000000000 + 0x641e6f84a2e52dac) 5 i.val))),
([([(0x1000000,0),(0x8102,2),(0x80000,3),(0x404,6),(0x4000,7),(0x28,10),(0x200,11),(0x1,18),(0x10,19)], [(0x100000,1),(0x2080,2),(0x41040,6),(0x800000,9),(0x20800,10),(0x400000,13),(0x10000,14),(0x200000,17)])], (fun i => Fin.ofNat 25 (unpack (0x1824dc9a01ea2dc7 * 0x10000000000000000 + 0x26a2c28b0f50c166) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x1872493b30e28d56 * 0x10000000000000000 + 0x60c28a281f76a072) 5 i.val))),
([([(0x1200240,0),(0x100020,3),(0x4,13),(0x8,14),(0x12,15),(0x1,18)], [(0x800100,1),(0x408080,2),(0x90000,5),(0x40000,6),(0x20400,7),(0x4800,10),(0x2000,11),(0x1000,12)])], (fun i => Fin.ofNat 25 (unpack (0x18a5eb62006114df * 0x10000000000000000 + 0x284525418ee5356c) 5 i.val)), (fun i => Fin.ofNat 25 (unpack (0x18b52b77314b6904 * 0x10000000000000000 + 0x8d27299138be12) 5 i.val)))]

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def mask : Word := 0x7bdef

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def goal : Word := 0x3adae

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def raw : List Word := [15,480,15360,33825,67650,135300,270600,491520]

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def neg : List Nat := [0,6,12,18]

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem autos : DagMovesOK mask goal 25 (dagMoves records) := dagMovesOfCheck (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def hullCode (i : Nat) := unpack ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0x640c * 0x10000000000000000 + 0xd92c8263e42044c4) * 0x10000000000000000 + 0x63e42044c363e420) * 0x10000000000000000 + 0x44a363e42044a263) * 0x10000000000000000 + 0xc0d9286263c0d928) * 0x10000000000000000 + 0x41620cd92c61620c) * 0x10000000000000000 + 0xd92c406140b32883) * 0x10000000000000000 + 0x6140b328626140b3) * 0x10000000000000000 + 0x28416140b3282061) * 0x10000000000000000 + 0x4013284160e4a034) * 0x10000000000000000 + 0xe160e4a034c160e4) * 0x10000000000000000 + 0xa034c060e4a034a4) * 0x10000000000000000 + 0x60e4a034a060e4a0) * 0x10000000000000000 + 0x348060e42034a460) * 0x10000000000000000 + 0xe42034a360e42034) * 0x10000000000000000 + 0x8360e420346260cc) * 0x10000000000000000 + 0xd9286160ccd92841) * 0x10000000000000000 + 0x60ccd9284060ccd9) * 0x10000000000000000 + 0x282060ccd9042060) * 0x10000000000000000 + 0xc0d9286260c0d928) * 0x10000000000000000 + 0x4160c0d9282060c0) * 0x10000000000000000 + 0x89146260c0891441) * 0x10000000000000000 + 0x604cd92820604ca0) * 0x10000000000000000 + 0x2ca2604ca02c8160) * 0x10000000000000000 + 0x4ca02c61604ca02c) * 0x10000000000000000 + 0x60604ca02c40604c) * 0x10000000000000000 + 0x502c606040b32862) * 0x10000000000000000 + 0x6040b328616040b3) * 0x10000000000000000 + 0x28416040b3284060) * 0x10000000000000000 + 0x40b3282060407328) * 0x10000000000000000 + 0x413458891cc23458) * 0x10000000000000000 + 0x891cc13458891ca1) * 0x10000000000000000 + 0x3458891ca0345889) * 0x10000000000000000 + 0x1c8034583908c234) * 0x10000000000000000 + 0x583908a134583908) * 0x10000000000000000 + 0x62345839084133e4) * 0x10000000000000000 + 0x1040e433e41040c3) * 0x10000000000000000 + 0x33e41040c233e410) * 0x10000000000000000 + 0x40a133c089148233) * 0x10000000000000000 + 0xc089148133647620) * 0x10000000000000000 + 0xc133647620c03364) * 0x10000000000000000 + 0x7620a03364160c60) * 0x10000000000000000 + 0x3358891ca2335889) * 0x10000000000000000 + 0x1c823358891c8133) * 0x10000000000000000 + 0x58891c803358891c) * 0x10000000000000000 + 0x623358891c613358) * 0x10000000000000000 + 0x891c603358891c41) * 0x10000000000000000 + 0x3358392861335839) * 0x10000000000000000 + 0x8a2335839086233) * 0x10000000000000000 + 0x5839086133583908) * 0x10000000000000000 + 0x4133583904403358) * 0x10000000000000000 + 0x3904203358190820) * 0x10000000000000000 + 0x3298501c20329810) * 0x10000000000000000 + 0x2ca33298102c8232) * 0x10000000000000000 + 0x8076148232807614) * 0x10000000000000000 + 0x8132807614613280) * 0x10000000000000000 + 0x7614603280761441) * 0x10000000000000000 + 0x3280761440328076) * 0x10000000000000000 + 0x142030e45020e130) * 0x10000000000000000 + 0xe45020e030e45020) * 0x10000000000000000 + 0xc030e41040a230e4) * 0x10000000000000000 + 0x10408130e41020a2) * 0x10000000000000000 + 0x30d889044130d889) * 0x10000000000000000 + 0x42030c089146130) * 0x10000000000000000 + 0xc089144130c08914) * 0x10000000000000000 + 0x4030c08914203098) * 0x10000000000000000 + 0x501cc13098501cc0) * 0x10000000000000000 + 0x3098501ca1309850) * 0x10000000000000000 + 0x1ca03098501c8130) * 0x10000000000000000 + 0x98501c803098102c) * 0x10000000000000000 + 0xa43098102c833098) * 0x10000000000000000 + 0x102c623098102c41) * 0x10000000000000000 + 0x3098101c83309810) * 0x10000000000000000 + 0x1c623098101c4130) * 0x10000000000000000 + 0x8076146130807614) * 0x10000000000000000 + 0x6030807614413080) * 0x10000000000000000 + 0x7614403080761420) * 0x10000000000000000 + 0x4583908c1045839) * 0x10000000000000000 + 0x8c004583908a004) * 0x10000000000000000 + 0x5839088204583908) * 0x10000000000000000 + 0x610424533d040424) * 0x10000000000000000 + 0x533ce30424533ce2) * 0x10000000000000000 + 0x424133ca0040c39) * 0x10000000000000000 + 0x4a1040c3904a004) * 0x10000000000000000 + 0xc390480040c3904) * 0x10000000000000000 + 0x62040c3904600364) * 0x10000000000000000 + 0x260ce10364260ce0) * 0x10000000000000000 + 0x364260cc0036426) * 0x10000000000000000 + 0xc800358f9286103) * 0x10000000000000000 + 0x5839288103583928) * 0x10000000000000000 + 0x6003583908610358) * 0x10000000000000000 + 0x39084002d85328c3) * 0x10000000000000000 + 0x2d85328a202d813) * 0x10000000000000000 + 0x28a102cca6048302) * 0x10000000000000000 + 0xcca6046202cca604) * 0x10000000000000000 + 0x4102cca6042002cc) * 0x10000000000000000 + 0x2604a102cc2604a0) * 0x10000000000000000 + 0x2cc26048302cc26) * 0x10000000000000000 + 0x48102cc26048002) * 0x10000000000000000 + 0xcc26046202cc2604) * 0x10000000000000000 + 0x6002cc26044102cc) * 0x10000000000000000 + 0x2604200224533cc2) * 0x10000000000000000 + 0x224130cc0022413) * 0x10000000000000000 + 0xca10224130ca002) * 0x10000000000000000 + 0x18390420020c3904) * 0x10000000000000000 + 0x62020c390441020c) * 0x10000000000000000 + 0x39042001d85328a3) * 0x10000000000000000 + 0x1d85328a201d853) * 0x10000000000000000 + 0x288201d85308a301) * 0x10000000000000000 + 0xd813288101d81328) * 0x10000000000000000 + 0x6101d813286001d8) * 0x10000000000000000 + 0x13284001d81308c1) * 0x10000000000000000 + 0x1d81308c001d813) * 0x10000000000000000 + 0x8a201d81308a001) * 0x10000000000000000 + 0xd813088101d81308) * 0x10000000000000000 + 0x8001d813086101d8) * 0x10000000000000000 + 0x13086001d8130840) * 0x10000000000000000 + 0x1cca6148201cca6) * 0x10000000000000000 + 0x146201cca6146101) * 0x10000000000000000 + 0xcca6046201cca604) * 0x10000000000000000 + 0x6101cca6044101cc) * 0x10000000000000000 + 0xa6044001cc261482) * 0x10000000000000000 + 0x1cc26048101cc26) * 0x10000000000000000 + 0x48001cc26046201) * 0x10000000000000000 + 0xcc26046101cc2604) * 0x10000000000000000 + 0x6001cc26044101cc) * 0x10000000000000000 + 0x26044001cc260420) 40 i

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state0 (i : Nat) : Option RowState :=
  let h := unpack (0x3b99329929992099 * 0x10000000000000000 + 0x17990f890879008a) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack (((((((((((((((((((((0x7800 * 0x10000000000000000 + 0x421082108410842) * 0x10000000000000000 + 0x842103c00001e00) * 0x10000000000000000 + 0xf000017800042) * 0x10000000000000000 + 0x1082108410842084) * 0x10000000000000000 + 0x2103c00001e00000) * 0x10000000000000000 + 0xf000027800042108) * 0x10000000000000000 + 0x2108410842084210) * 0x10000000000000000 + 0x3c00001ef001e000) * 0x10000000000000000 + 0xf7800042108210) * 0x10000000000000000 + 0x84108420842f0842) * 0x10000000000000000 + 0x103c00001e00000f) * 0x10000000000000000 + 0x7800042108210841) * 0x10000000000000000 + 0x84f108420842103) * 0x10000000000000000 + 0xc00001e00000f780) * 0x10000000000000000 + 0x42108210841084) * 0x10000000000000000 + 0x20842f03c00001e0) * 0x10000000000000000 + 0xf78000421082) * 0x10000000000000000 + 0x1084108420842f03) * 0x10000000000000000 + 0xc00001e078000421) * 0x10000000000000000 + 0x821084108420842) * 0x10000000000000000 + 0x103c00001e00000f) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge0 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x9a1288a378a063aa * 0x10000000000000000 + 0x522332bf1c2d0038) ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0x3101566310 * 0x10000000000000000 + 0x156506335642e009) * 0x10000000000000000 + 0x4e310094d043294c) * 0x10000000000000000 + 0x1800642310064100) * 0x10000000000000000 + 0x3264061003367400) * 0x10000000000000000 + 0x33500303342d0006) * 0x10000000000000000 + 0x62d0005a2d0004e1) * 0x10000000000000000 + 0x700042300002a300) * 0x10000000000000000 + 0x1e4f015664f015) * 0x10000000000000000 + 0x6511215644f00c41) * 0x10000000000000000 + 0x410094e4f0094d0f) * 0x10000000000000000 + 0x2094c4f006424f00) * 0x10000000000000000 + 0x6410b22640720034) * 0x10000000000000000 + 0x27400341002e3406) * 0x10000000000000000 + 0x1003367400335012) * 0x10000000000000000 + 0x2334950031e4d000) * 0x10000000000000000 + 0x664f000650228064) * 0x10000000000000000 + 0x4d0005a4f000590e) * 0x10000000000000000 + 0x28058400004e4f00) * 0x10000000000000000 + 0x4d0c2804c4e0003) * 0x10000000000000000 + 0x64f000350c260344) * 0x10000000000000000 + 0xe0002a4f00029002) * 0x10000000000000000 + 0x8028170001e4f000) * 0x10000000000000000 + 0x1d002601cc001566) * 0x10000000000000000 + 0xc001565022d56438) * 0x10000000000000000 + 0x94e4a0094d002c) * 0x10000000000000000 + 0x94c4400666440065) * 0x10000000000000000 + 0xa30006562d0064e4) * 0x10000000000000000 + 0x50064abf00642170) * 0x10000000000000000 + 0x63ea60063630006) * 0x10000000000000000 + 0x32300062abf00366) * 0x10000000000000000 + 0xbf0035abf0034ebf) * 0x10000000000000000 + 0x342c0003410b1e) * 0x10000000000000000 + 0x3409a003324a0032) * 0x10000000000000000 + 0xabf00066bf0005ab) * 0x10000000000000000 + 0xf0004e950003ea60) * 0x10000000000000000 + 0x36c000035001e0) * 0x10000000000000000 + 0x344a0002a6101566) * 0x10000000000000000 + 0x610156511195645f) * 0x10000000000000000 + 0xc663000c625f00) * 0x10000000000000000 + 0xc5a3100c566d00c4) * 0x10000000000000000 + 0xe4600c4a6100c424) * 0x10000000000000000 + 0xf00c3e5f00966730) * 0x10000000000000000 + 0x9625f0095a6d009) * 0x10000000000000000 + 0x4e61009426d0064e) * 0x10000000000000000 + 0x610064d0f1864c61) * 0x10000000000000000 + 0x63530006316100) * 0x10000000000000000 + 0x6298c00625bb0034) * 0x10000000000000000 + 0x2a6003410b18340a) * 0x10000000000000000 + 0x6003353000331a60) * 0x10000000000000000 + 0x3299a003255e000) * 0x10000000000000000 + 0x665e0005a6100056) * 0x10000000000000000 + 0x6c0004e990004a60) * 0x10000000000000000 + 0x42610003e6100) * 0x10000000000000000 + 0x267400025003002) * 0x10000000000000000 + 0x4600001ea6000127) * 0x10000000000000000 + 0x2015667201565111) * 0x10000000000000000 + 0x75644400f663000f) * 0x10000000000000000 + 0x624400f5a3100f56) * 0x10000000000000000 + 0x2d00f4e4600f4a72) * 0x10000000000000000 + 0xc667200c5a7200) * 0x10000000000000000 + 0xc4e6100941310093) * 0x10000000000000000 + 0xd700064e720064d0) * 0x10000000000000000 + 0xf1664c2d00641450) * 0x10000000000000000 + 0x63d7200635bf003) * 0x10000000000000000 + 0x41300033dbe00336) * 0x10000000000000000 + 0xbf003350c1a3346f) * 0x10000000000000000 + 0x666f0005a6f00) * 0x10000000000000000 + 0x4e7200032740003) * 0x10000000000000000 + 0x1002e030600002a7) * 0x10000000000000000 + 0x200029001a028710) * 0x10000000000000000 + 0x1e720125b062b2) * 0x10000000000000000 + 0x5a06252591115258) * 0x10000000000000000 + 0x72012577200f5b72) * 0x10000000000000000 + 0xf577200f4f7200) * 0x10000000000000000 + 0xc5b7200c577200c4) * 0x10000000000000000 + 0xf7200c435f0095b7) * 0x10000000000000000 + 0x3009575f0094f740) * 0x10000000000000000 + 0x94b6d0094374009) * 0x10000000000000000 + 0x3f61009377400933) * 0x10000000000000000 + 0x720065b720064f73) * 0x10000000000000000 + 0x64b72006430424) * 0x10000000000000000 + 0x642042a6410f1464) * 0x10000000000000000 + 0x730063f72006377) * 0x10000000000000000 + 0x300633610062b8c0) * 0x10000000000000000 + 0x627bf0035bbf003) * 0x10000000000000000 + 0x4f740034bbf00343) * 0x10000000000000000 + 0x8d0033fbf0033700) * 0x10000000000000000 + 0x24336002a3350b14) * 0x10000000000000000 + 0x3347400333a60032) * 0x10000000000000000 + 0xb9a003274a0031f7) * 0x10000000000000000 + 0x20005b061e05a720) * 0x10000000000000000 + 0x4f061a04e74000) * 0x10000000000000000 + 0x4b072204a7200043) * 0x10000000000000000 + 0x41a042740003f05) * 0x10000000000000000 + 0x2203e7200037001a) * 0x10000000000000000 + 0x367400033012203) * 0x10000000000000000 + 0x2730001f041e01ec) * 0x10000000000000000 + 0x13001e012061) * 0x10000000000000000 + 0x8f4f0614f4e0714f) * 0x10000000000000000 + 0x4d0612f4c1132f4b) * 0x10000000000000000 + 0x916c4f0920c4b1a) * 0x10000000000000000 + 0x2cc43031694f0320) * 0x10000000000000000 + 0x94b162c943142c93) * 0x10000000000000000 + 0x7061c64f062264b0) * 0x10000000000000000 + 0x71c643072263f051) * 0x10000000000000000 + 0xc6370522633011c6) * 0x10000000000000000 + 0x2b0122627192c34f) * 0x10000000000000000 + 0x816343082033f04) * 0x10000000000000000 + 0x1833705143360414) * 0x10000000000000000 + 0x33504123340f3233) * 0x10000000000000000 + 0x3011632b01203270) * 0x10000000000000000 + 0x41c31f042231b152) * 0x10000000000000000 + 0xc04f021604302200) * 0x10000000000000000 + 0x3f00160370020033) * 0x10000000000000000 + 0x1802b011402a00) * 0x10000000000000000 + 0x1402900120280b32) * 0x10000000000000000 + 0x27001c01f002201) * 0x10000000000000000 + 0xb132c013110b25b1) * 0x10000000000000000 + 0x10725a1207259110) * 0x10000000000000000 + 0x525811112571a08f) * 0x10000000000000000 + 0x5b1a0ef571a0cf4f) * 0x10000000000000000 + 0x1608c5b160ec5716) * 0x10000000000000000 + 0xcc4f140cc430708) * 0x10000000000000000 + 0x95b070e957070c94) * 0x10000000000000000 + 0xf050c943010c9371) * 0x10000000000000000 + 0x90c65b190864f190) * 0x10000000000000000 + 0xe64b0f0a64310066) * 0x10000000000000000 + 0x420f066410f04640) * 0x10000000000000000 + 0xf1063f140863714) * 0x10000000000000000 + 0xe633050862b050e) * 0x10000000000000000 + 0x627150c35b150834) * 0x10000000000000000 + 0xf150e34b13083431) * 0x10000000000000000 + 0x30e33f0b0a3370c0) * 0x10000000000000000 + 0x63360b063350b043) * 0x10000000000000000 + 0x340b10333010832b) * 0x10000000000000000 + 0x10e327130c31f06) * 0x10000000000000000 + 0xc05b060804f060e) * 0x10000000000000000 + 0x4b0408043040e03) * 0x10000000000000000 + 0xf0008037000e0330) * 0x10000000000000000 + 0xa02b010602a000) * 0x10000000000000000 + 0x6029000402800100) * 0x10000000000000000 + 0x27040c01f000c013) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state1 (i : Nat) : Option RowState :=
  let h := unpack (0x35882d8825881d88 * 0x10000000000000000 + 0x15880d8806780068) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack (((((((((((((((((((0x7 * 0x10000000000000000 + 0x8000421082108410) * 0x10000000000000000 + 0x8420842f03c00001) * 0x10000000000000000 + 0xe000080780004210) * 0x10000000000000000 + 0x821084108420842f) * 0x10000000000000000 + 0x3c00001ef001e07) * 0x10000000000000000 + 0x8000421082108410) * 0x10000000000000000 + 0x842085ef0842f03c) * 0x10000000000000000 + 0x1e0780004210) * 0x10000000000000000 + 0x8210841084f10842) * 0x10000000000000000 + 0x842f03c00001e07) * 0x10000000000000000 + 0x8000421082108410) * 0x10000000000000000 + 0x9e2108420842f03c) * 0x10000000000000000 + 0x1e0780004210) * 0x10000000000000000 + 0x8211e42108410842) * 0x10000000000000000 + 0x842f03c00001e07) * 0x10000000000000000 + 0x8000421082108410) * 0x10000000000000000 + 0x9e20842f03c00001) * 0x10000000000000000 + 0xe078000421082108) * 0x10000000000000000 + 0x4109e20842f03c00) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge1 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x709d6498569c499a * 0x10000000000000000 + 0x38232a1c11320022) (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0x65 * 0x10000000000000000 + 0x125a65012590645) * 0x10000000000000000 + 0x2586500c41640064) * 0x10000000000000000 + 0x2650064117646409) * 0x10000000000000000 + 0xe00342a000341005) * 0x10000000000000000 + 0xe3409e00336a0003) * 0x10000000000000000 + 0x351464334a90031e) * 0x10000000000000000 + 0x630005a650005905) * 0x10000000000000000 + 0x5a058630004e6500) * 0x10000000000000000 + 0x4d005a04c630003) * 0x10000000000000000 + 0x66500035054c0346) * 0x10000000000000000 + 0xb0002a6500029005) * 0x10000000000000000 + 0x2028530001e65000) * 0x10000000000000000 + 0x1d004c01ca00125a) * 0x10000000000000000 + 0xa001259025d25834) * 0x10000000000000000 + 0x6423500641005c) * 0x10000000000000000 + 0x640630035a630034) * 0x10000000000000000 + 0xe540034a51003426) * 0x10000000000000000 + 0x50033e9e00336540) * 0x10000000000000000 + 0x332a50032a5f003) * 0x10000000000000000 + 0x26530031e9e0005a) * 0x10000000000000000 + 0x9e0004e9e000429e) * 0x10000000000000000 + 0x36a0000350046) * 0x10000000000000000 + 0x349800026350001) * 0x10000000000000000 + 0xea50125aa5012590) * 0x10000000000000000 + 0x24b258630095a530) * 0x10000000000000000 + 0x956630094e54009) * 0x10000000000000000 + 0x4a5100942650093e) * 0x10000000000000000 + 0xba009365400932a4) * 0x10000000000000000 + 0x65aa40064ea400) * 0x10000000000000000 + 0x6427600342910034) * 0x10000000000000000 + 0x1004a34051003295) * 0x10000000000000000 + 0x300325910031da30) * 0x10000000000000000 + 0x5aa30004ea3000) * 0x10000000000000000 + 0x42b900036a500035) * 0x10000000000000000 + 0x42034a50001a91) * 0x10000000000000000 + 0x126f0125a6f01) * 0x10000000000000000 + 0x259113d2586f00c5) * 0x10000000000000000 + 0xa5100c566f00c4e5) * 0x10000000000000000 + 0x400c4a5100c42720) * 0x10000000000000000 + 0xc3e6f0095a6f009) * 0x10000000000000000 + 0x4e6f009425e00635) * 0x10000000000000000 + 0x720063172006256e) * 0x10000000000000000 + 0x3426f003410f3c) * 0x10000000000000000 + 0x3405100335530033) * 0x10000000000000000 + 0x16f003299e000355) * 0x10000000000000000 + 0x4000319c0002a9e0) * 0x10000000000000000 + 0x2900400289e012) * 0x10000000000000000 + 0x5a9e01259063b258) * 0x10000000000000000 + 0x9e00c5a5100c569e) * 0x10000000000000000 + 0xc4e5400c4a9e00) * 0x10000000000000000 + 0xc426500c3e9e0095) * 0x10000000000000000 + 0xa9e009569e0094e9) * 0x10000000000000000 + 0xe00942ba00635980) * 0x10000000000000000 + 0x631ba00629bf006) * 0x10000000000000000 + 0x2536003421600341) * 0x10000000000000000 + 0x43a340160033553) * 0x10000000000000000 + 0x3311600329ac00) * 0x10000000000000000 + 0x3259c0005a9c0004) * 0x10000000000000000 + 0xe9e0004a9c000429) * 0x10000000000000000 + 0xe0003e9e00026a00) * 0x10000000000000000 + 0x250b6a024b9000) * 0x10000000000000000 + 0x1e9e0001a1600012) * 0x10000000000000000 + 0x9e0125a9e0125906) * 0x10000000000000000 + 0x392589600f5a5100) * 0x10000000000000000 + 0xf569600f4e5400f4) * 0x10000000000000000 + 0xa9e00c5a9e00c4e9) * 0x10000000000000000 + 0xe00941540093d510) * 0x10000000000000000 + 0x641980063da4006) * 0x10000000000000000 + 0x352c00341530033d) * 0x10000000000000000 + 0x2a003362c0033505) * 0x10000000000000000 + 0x3c3349c0005a9c00) * 0x10000000000000000 + 0x4e9e00032a00003) * 0x10000000000000000 + 0x1005e0309c0002a9) * 0x10000000000000000 + 0xe00029003c028a30) * 0x10000000000000000 + 0x1e9e00f4f0254f) * 0x10000000000000000 + 0x4e0248f4d0636f4c) * 0x10000000000000000 + 0x9e00f4b9e00c4f9e) * 0x10000000000000000 + 0xc4b9e00c439e00) * 0x10000000000000000 + 0x94f9e0094b9e0094) * 0x10000000000000000 + 0x3a00093f9e00937a) * 0x10000000000000000 + 0x933a40064f9f0) * 0x10000000000000000 + 0x64ba400643a0006) * 0x10000000000000000 + 0x3fa400637a000633) * 0x10000000000000000 + 0xba0062bac006272c) * 0x10000000000000000 + 0x34f2c00343a000) * 0x10000000000000000 + 0x33f2c00337004833) * 0x10000000000000000 + 0x600543350436334a) * 0x10000000000000000 + 0x333160032bac0) * 0x10000000000000000 + 0x327910031fc9003) * 0x10000000000000000 + 0x1b9e0004f155c04e) * 0x10000000000000000 + 0x9e00043023c042a0) * 0x10000000000000000 + 0x3f166403e9e00) * 0x10000000000000000 + 0x37003c036a00003) * 0x10000000000000000 + 0x31464032a50001f0) * 0x10000000000000000 + 0x4201ea00001b006) * 0x10000000000000000 + 0x201a2f00013135c0) * 0x10000000000000000 + 0x12023ac430236c42) * 0x10000000000000000 + 0x336c410234c4011) * 0x10000000000000000 + 0x6cc3f01389430144) * 0x10000000000000000 + 0x93f1a68937154a64) * 0x10000000000000000 + 0x3156463f164a6371) * 0x10000000000000000 + 0x664633144a62b146) * 0x10000000000000000 + 0x4627064a34306643) * 0x10000000000000000 + 0x3f074a3370764333) * 0x10000000000000000 + 0x54a32b056432700) * 0x10000000000000000 + 0x3e31f006031b1968) * 0x10000000000000000 + 0x430038037004403) * 0x10000000000000000 + 0x3003a02b013602a0) * 0x10000000000000000 + 0x3602900340280f6) * 0x10000000000000000 + 0xc027134a01f13640) * 0x10000000000000000 + 0x1b044a013046400f) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state2 (i : Nat) : Option RowState :=
  let h := unpack (0x3888308828882088 * 0x10000000000000000 + 0x1888108808880088) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack (((((((((((((((((((0x7800042108210841 * 0x10000000000000000 + 0x8420842f03c0000) * 0x10000000000000000 + 0x1e00000178000421) * 0x10000000000000000 + 0x8210841084f0842) * 0x10000000000000000 + 0x103c00001e000002) * 0x10000000000000000 + 0x780004210823c841) * 0x10000000000000000 + 0x84208421001ef00) * 0x10000000000000000 + 0x1e00000f78000421) * 0x10000000000000000 + 0x821084109e20842) * 0x10000000000000000 + 0xf03c00001e00000f) * 0x10000000000000000 + 0x7800042108210841) * 0x10000000000000000 + 0x8420842103c0200) * 0x10000000000000000 + 0x1e00000f78000421) * 0x10000000000000000 + 0x821084108420842) * 0x10000000000000000 + 0x103c00001e20000f) * 0x10000000000000000 + 0x7800042108210841) * 0x10000000000000000 + 0x9e2108420842f03) * 0x10000000000000000 + 0xc000000f78000421) * 0x10000000000000000 + 0x821084108420842) * 0x10000000000000000 + 0xf03c00001e000020) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge2 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x4e8f4396369a2a19 * 0x10000000000000000 + 0x21911a8e0c9c0019) (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0x5401 * 0x10000000000000000 + 0x25a5401259066b25) * 0x10000000000000000 + 0x8520064254006410) * 0x10000000000000000 + 0x46a6409e00336a00) * 0x10000000000000000 + 0x335006a33451000) * 0x10000000000000000 + 0x5a510004e5100042) * 0x10000000000000000 + 0x5100036530001ea0) * 0x10000000000000000 + 0x12720125a7201) * 0x10000000000000000 + 0x259115f2585f0093) * 0x10000000000000000 + 0x5700064272006410) * 0x10000000000000000 + 0xf5e640bf003356f0) * 0x10000000000000000 + 0x5a720005902500) * 0x10000000000000000 + 0x586f0004e720004d) * 0x10000000000000000 + 0xe5004c6f0004272) * 0x10000000000000000 + 0x410c500407200) * 0x10000000000000000 + 0x29710001e720001) * 0x10000000000000000 + 0xd005001c72000112) * 0x10000000000000000 + 0x125a2001259006) * 0x10000000000000000 + 0x9258420065a42006) * 0x10000000000000000 + 0x4e2d0064a2b00642) * 0x10000000000000000 + 0x440063e1f0063615) * 0x10000000000000000 + 0x6325b0062a2d00) * 0x10000000000000000 + 0x6261e0035a1e0034) * 0x10000000000000000 + 0xe48003421f003362) * 0x10000000000000000 + 0x3350b5c334870) * 0x10000000000000000 + 0x3261e0005a1e000) * 0x10000000000000000 + 0x4e48000427e00032) * 0x10000000000000000 + 0x5b0002a200002900) * 0x10000000000000000 + 0x5c028bf0125abf01) * 0x10000000000000000 + 0x2591155258370064) * 0x10000000000000000 + 0x249006410f54640b) * 0x10000000000000000 + 0xe0035abe0034ebf0) * 0x10000000000000000 + 0x34abe00342bf003) * 0x10000000000000000 + 0x3ea50032ac400326) * 0x10000000000000000 + 0x490031ebe0005abe) * 0x10000000000000000 + 0x4ea00004abe00) * 0x10000000000000000 + 0x42a00003e9e0003) * 0x10000000000000000 + 0x6bf000321d0001ea) * 0x10000000000000000 + 0x12bf00011004) * 0x10000000000000000 + 0x60104d0125a4d012) * 0x10000000000000000 + 0x59185b2584d00935) * 0x10000000000000000 + 0x3f006424d006410f) * 0x10000000000000000 + 0x526404d003364d00) * 0x10000000000000000 + 0x3350b4e3346f0003) * 0x10000000000000000 + 0x6720003500500345) * 0x10000000000000000 + 0xe0002a7200029015) * 0x10000000000000000 + 0x8028940001215012) * 0x10000000000000000 + 0x5a1501259114d258) * 0x10000000000000000 + 0x935270064215) * 0x10000000000000000 + 0x6410f4c6401500) * 0x10000000000000000 + 0x3361500335006633) * 0x10000000000000000 + 0x472000355e0002a7) * 0x10000000000000000 + 0x2000290156028be0) * 0x10000000000000000 + 0x125abe0125911492) * 0x10000000000000000 + 0x58be0095abe00956) * 0x10000000000000000 + 0xbe0094ebe00942ba) * 0x10000000000000000 + 0x629bf006250d00) * 0x10000000000000000 + 0x3420f003410f4834) * 0x10000000000000000 + 0xe00329c400325b) * 0x10000000000000000 + 0xd0005abd0004e9e0) * 0x10000000000000000 + 0x4abd000429e000) * 0x10000000000000000 + 0x3e9c00036be00032) * 0x10000000000000000 + 0x9c0002abe0002900) * 0x10000000000000000 + 0x40028be00026bf00) * 0x10000000000000000 + 0x250162024080001) * 0x10000000000000000 + 0x2980125a98012590) * 0x10000000000000000 + 0x2652588b00642980) * 0x10000000000000000 + 0x64100646409e003) * 0x10000000000000000 + 0x36a0003350062334) * 0x10000000000000000 + 0xa50032a960005a98) * 0x10000000000000000 + 0x59024e0589600) * 0x10000000000000000 + 0x4e980004d025804) * 0x10000000000000000 + 0xc8a0004298000410) * 0x10000000000000000 + 0x580409700036980) * 0x10000000000000000 + 0x35005603497000) * 0x10000000000000000 + 0x1e980001d004e01c) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state3 (i : Nat) : Option RowState :=
  let h := unpack (0x2f77287721771a77 * 0x10000000000000000 + 0x13770d6708570088) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack ((((((((((((((((0x78000421082108 * 0x10000000000000000 + 0x4109e21084f0842f) * 0x10000000000000000 + 0x3c0078000421082) * 0x10000000000000000 + 0x108418def109e208) * 0x10000000000000000 + 0x42f03c0078000421) * 0x10000000000000000 + 0x8211e421084109e) * 0x10000000000000000 + 0x20842f03c0078000) * 0x10000000000000000 + 0x4210823c84210841) * 0x10000000000000000 + 0x9e20842f03c0078) * 0x10000000000000000 + 0x43d0842108210) * 0x10000000000000000 + 0x84109e20842f03c0) * 0x10000000000000000 + 0x780004210823c84) * 0x10000000000000000 + 0x109e20842f03c007) * 0x10000000000000000 + 0x80004210823c8410) * 0x10000000000000000 + 0x9e20842f78000421) * 0x10000000000000000 + 0x821084109e20842) * 0x10000000000000000 + 0x103c000000f00001) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge3 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x541247993d942f9c * 0x10000000000000000 + 0x251512a50717000e) (((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0x9c00f4 * 0x10000000000000000 + 0xe9c00f4d1176f4c9) * 0x10000000000000000 + 0xc0064e9c0064a9c0) * 0x10000000000000000 + 0x6429e0063e9c006) * 0x10000000000000000 + 0x369e006329c0062a) * 0x10000000000000000 + 0x9c00626b70031dbe) * 0x10000000000000000 + 0x31909000360b00) * 0x10000000000000000 + 0x350f760349c0001) * 0x10000000000000000 + 0xdab00019b900f4ec) * 0x10000000000000000 + 0x800f4d0278f4cb60) * 0x10000000000000000 + 0x94e9c0094a22009) * 0x10000000000000000 + 0x429e0093e9c00936) * 0x10000000000000000 + 0x9e00932b60064ec7) * 0x10000000000000000 + 0x642b700636b600) * 0x10000000000000000 + 0x34ec700342b70033) * 0x10000000000000000 + 0x6b10031ac2003190) * 0x10000000000000000 + 0xa0318b800036c80) * 0x10000000000000000 + 0x3500780349c000) * 0x10000000000000000 + 0x290500025c80001d) * 0x10000000000000000 + 0xc8000119c00f4e9c) * 0x10000000000000000 + 0xf4d0674f4c9c00) * 0x10000000000000000 + 0xc4e9c00c4a9c00c4) * 0x10000000000000000 + 0x29e00c3e9c0094e9) * 0x10000000000000000 + 0xc009429c006359e0) * 0x10000000000000000 + 0x6319e006259c003) * 0x10000000000000000 + 0x359e00331a200329) * 0x10000000000000000 + 0x2000359e0003100) * 0x10000000000000000 + 0x2a02000290076) * 0x10000000000000000 + 0x280200f4e0200f4) * 0x10000000000000000 + 0xd0272f4c0200c4e9) * 0x10000000000000000 + 0xc00c4a0200c429e0) * 0x10000000000000000 + 0xc3e020094e02009) * 0x10000000000000000 + 0x4a02009422600635) * 0x10000000000000000 + 0xab0063126006292c) * 0x10000000000000000 + 0x6256800335c200) * 0x10000000000000000 + 0x33168003290c0032) * 0x10000000000000000 + 0x5000004e00000420) * 0x10000000000000000 + 0x20003e0200026050) * 0x10000000000000000 + 0x250fa602425000) * 0x10000000000000000 + 0x1e020001a6800012) * 0x10000000000000000 + 0x20000e0200f4e9c) * 0x10000000000000000 + 0xf4a0200c4e0200) * 0x10000000000000000 + 0xc4d0374c4c020094) * 0x10000000000000000 + 0x19e0093dc100641a) * 0x10000000000000000 + 0xb0063d1200635aa0) * 0x10000000000000000 + 0x341c20033d56003) * 0x10000000000000000 + 0x3502000320500031) * 0x10000000000000000 + 0x8e030000002a02) * 0x10000000000000000 + 0x2900740281100) * 0x10000000000000000 + 0x1e56000120200c4) * 0x10000000000000000 + 0x30084c420086c410) * 0x10000000000000000 + 0x370c400200c3f020) * 0x10000000000000000 + 0x943020093f02009) * 0x10000000000000000 + 0x3705009331200643) * 0x10000000000000000 + 0x40063f120063705) * 0x10000000000000000 + 0x633260062b2300) * 0x10000000000000000 + 0x6275600343050033) * 0x10000000000000000 + 0xf560033705003336) * 0x10000000000000000 + 0x80032b2300327c80) * 0x10000000000000000 + 0x31f4c0031b02000) * 0x10000000000000000 + 0x43199c0420200037) * 0x10000000000000000 + 0x7403605000331a) * 0x10000000000000000 + 0xa4032140001f137a) * 0x10000000000000000 + 0x1e050001b13a201) * 0x10000000000000000 + 0xa5700013047a0120) * 0x10000000000000000 + 0x50000f04a200e007) * 0x10000000000000000 + 0x2937017093600709) * 0x10000000000000000 + 0x35006e93411a8933) * 0x10000000000000000 + 0x199663719a46331a) * 0x10000000000000000 + 0x9662b1aa46271596) * 0x10000000000000000 + 0x33715a4333169632) * 0x10000000000000000 + 0xb16a4327137831f1) * 0x10000000000000000 + 0x39e31b069603706a) * 0x10000000000000000 + 0x4033079602b07a40) * 0x10000000000000000 + 0x27047801f049e01b) * 0x10000000000000000 + 0x78013009e00f07) * 0x10000000000000000 + 0x125a0701259026d) * 0x10000000000000000 + 0x2580400642070064) * 0x10000000000000000 + 0x1006c640a50032ab) * 0x10000000000000000 + 0xf00329006a328030) * 0x10000000000000000 + 0x5a030004e03000) * 0x10000000000000000 + 0x421500036060001e) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state4 (i : Nat) : Option RowState :=
  let h := unpack (0x31772a7723771c77 * 0x10000000000000000 + 0x15770e7707770077) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack (((((((((((((((((0x78000421 * 0x10000000000000000 + 0x8210841084f0842) * 0x10000000000000000 + 0x103c02001e078000) * 0x10000000000000000 + 0x4210821084108420) * 0x10000000000000000 + 0x842f03c20001e078) * 0x10000000000000000 + 0x4210821084108) * 0x10000000000000000 + 0x420842f03c80001e) * 0x10000000000000000 + 0x780004210823c84) * 0x10000000000000000 + 0x10842085ef0842f0) * 0x10000000000000000 + 0x1e0780004210823) * 0x10000000000000000 + 0xc8421084109e2084) * 0x10000000000000000 + 0x2f001e0780004210) * 0x10000000000000000 + 0x821084109e20842f) * 0x10000000000000000 + 0x3c00001ef780004) * 0x10000000000000000 + 0x210821084109e208) * 0x10000000000000000 + 0x42f03c0002000780) * 0x10000000000000000 + 0x4210821084109e) * 0x10000000000000000 + 0x2085ef0842f03c00) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge4 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x3e88398a340b2995 * 0x10000000000000000 + 0x1e1716100a970015) ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0x6f0 * 0x10000000000000000 + 0xf4e6f00f4d188cf) * 0x10000000000000000 + 0x4c5c006296e00336) * 0x10000000000000000 + 0x6f003350f82334bc) * 0x10000000000000000 + 0x299600f4e9600) * 0x10000000000000000 + 0xf4d0098f4c890033) * 0x10000000000000000 + 0x6960033500943349) * 0x10000000000000000 + 0xc0002a9e00029007) * 0x10000000000000000 + 0xe028a10001e5100f) * 0x10000000000000000 + 0x4e5100f4d0a88f4c) * 0x10000000000000000 + 0x7700935500033651) * 0x10000000000000000 + 0x335048a3349b00) * 0x10000000000000000 + 0x359c0002a9e0002) * 0x10000000000000000 + 0x914920285a00f4e5) * 0x10000000000000000 + 0xa00f4d0096f4c620) * 0x10000000000000000 + 0x64e510064a62006) * 0x10000000000000000 + 0x42520063e5000636) * 0x10000000000000000 + 0x6300632b50062a52) * 0x10000000000000000 + 0x626590034e5900) * 0x10000000000000000 + 0x3428f00336590004) * 0x10000000000000000 + 0xe59000428f00036b) * 0x10000000000000000 + 0x50002a5a00029007) * 0x10000000000000000 + 0xa028860000e2a00f) * 0x10000000000000000 + 0x4e2a00f4d0686f4c) * 0x10000000000000000 + 0x2a0094e2a0094a2a) * 0x10000000000000000 + 0x9421b006292c00) * 0x10000000000000000 + 0x6255900329340032) * 0x10000000000000000 + 0x5290004e29000420) * 0x10000000000000000 + 0x20003e00000362a0) * 0x10000000000000000 + 0x32000002a2a000) * 0x10000000000000000 + 0x2900760282a00026) * 0x10000000000000000 + 0x2c0002514a202475) * 0x10000000000000000 + 0x12020000e9e00) * 0x10000000000000000 + 0xf4e9e00f4d0290f4) * 0x10000000000000000 + 0xc330033634003350) * 0x10000000000000000 + 0x903349c0004e9c0) * 0x10000000000000000 + 0x429e0003e9c000) * 0x10000000000000000 + 0x369e000329c0002a) * 0x10000000000000000 + 0x9e00026a30001ec3) * 0x10000000000000000 + 0x1a9d000129e00) * 0x10000000000000000 + 0xf4e9e00f4d1ba4f4) * 0x10000000000000000 + 0xc9e00c41020034e0) * 0x10000000000000000 + 0x2003420500341008) * 0x10000000000000000 + 0xe340020033605003) * 0x10000000000000000 + 0x351aa43349c0004e) * 0x10000000000000000 + 0x9e0004d038804c9c) * 0x10000000000000000 + 0x369e000350088) * 0x10000000000000000 + 0x349c0002a9e0002) * 0x10000000000000000 + 0x90b80028a30001e9) * 0x10000000000000000 + 0xe0001d008001ca30) * 0x10000000000000000 + 0xf4ea300f4d027af) * 0x10000000000000000 + 0x4ca20064e9d0064a) * 0x10000000000000000 + 0xa2006429e0063e9c) * 0x10000000000000000 + 0x6369e00632b700) * 0x10000000000000000 + 0x62a9e00626a20034) * 0x10000000000000000 + 0xea200342a200336b) * 0x10000000000000000 + 0x3267500036900) * 0x10000000000000000 + 0x35007a0349c000) * 0x10000000000000000 + 0x1dc2000199000011) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state5 (i : Nat) : Option RowState :=
  let h := unpack (0x31772a7723771c77 * 0x10000000000000000 + 0x15770e7707770077) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack (((((((((((((((((0x78000421 * 0x10000000000000000 + 0x821084109e20842) * 0x10000000000000000 + 0xf03c000002278000) * 0x10000000000000000 + 0x42108211e4108420) * 0x10000000000000000 + 0x842f03c000008078) * 0x10000000000000000 + 0x4210823c84108) * 0x10000000000000000 + 0x420842f001ef001e) * 0x10000000000000000 + 0x780004218821084) * 0x10000000000000000 + 0x108420842f03c000) * 0x10000000000000000 + 0x1e0780004210821) * 0x10000000000000000 + 0xa4108420842f03c) * 0x10000000000000000 + 0x1e0780004210) * 0x10000000000000000 + 0x821084108620842f) * 0x10000000000000000 + 0x3c00001e0780004) * 0x10000000000000000 + 0x210823c84109e208) * 0x10000000000000000 + 0x42f03c00001e0780) * 0x10000000000000000 + 0x42108210841084) * 0x10000000000000000 + 0x2084af03c00001e0) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge5 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x33952b9022131b0e * 0x10000000000000000 + 0x160a110a0714000e) ((((((((((((((((((((((((((((((((((((((((((((((((((((((0xab00 * 0x10000000000000000 + 0xf4eab00f4d029ef4) * 0x10000000000000000 + 0xcb10062ac2006290) * 0x10000000000000000 + 0xa06283c003364c0) * 0x10000000000000000 + 0x335009e334aa000) * 0x10000000000000000 + 0x4eab0004d027c04c) * 0x10000000000000000 + 0xaa00042ab0004103) * 0x10000000000000000 + 0x7c040aa00036ab00) * 0x10000000000000000 + 0x35017c0344c0001) * 0x10000000000000000 + 0x2ab00011007c0109) * 0x10000000000000000 + 0xe00f4e9e00f4d068) * 0x10000000000000000 + 0xef4c9e009352c003) * 0x10000000000000000 + 0x359c0004e9e0004d) * 0x10000000000000000 + 0x58c04c9c000429e) * 0x10000000000000000 + 0x41008c0409e00) * 0x10000000000000000 + 0x29a30001e9e0001) * 0x10000000000000000 + 0xd008201c9e000113) * 0x10000000000000000 + 0x400f4e3400f4d009) * 0x10000000000000000 + 0xcf4c620034e62003) * 0x10000000000000000 + 0x42520033e5000336) * 0x10000000000000000 + 0x64003321c0032a52) * 0x10000000000000000 + 0x3265a0031e5d00) * 0x10000000000000000 + 0x31a330004e330004) * 0x10000000000000000 + 0x233000361c0002a3) * 0x10000000000000000 + 0x4000290090028850) * 0x10000000000000000 + 0x1a6300f4e6300f) * 0x10000000000000000 + 0x4d1180f4c6300935) * 0x10000000000000000 + 0x620033663003351d) * 0x10000000000000000 + 0x9a3349c000369e00) * 0x10000000000000000 + 0x35008c0349c0002) * 0x10000000000000000 + 0xa9e000291c98028a) * 0x10000000000000000 + 0x8000129600f4e960) * 0x10000000000000000 + 0xf4d009af4c89003) * 0x10000000000000000 + 0x3696003350094334) * 0x10000000000000000 + 0x9c0002a9e000290c) * 0x10000000000000000 + 0x7e028a30001e9600) * 0x10000000000000000 + 0xf4e9600f4d0292f4) * 0x10000000000000000 + 0xc890033696003350) * 0x10000000000000000 + 0x923349c0002a9e0) * 0x10000000000000000 + 0x29008a028a3000) * 0x10000000000000000 + 0x1e2c00f4e2c00f4d) * 0x10000000000000000 + 0x684f4c2a0034e2a) * 0x10000000000000000 + 0x3422c0033e1400) * 0x10000000000000000 + 0x32a4300326900031) * 0x10000000000000000 + 0xe2c0031a2a0004e2) * 0x10000000000000000 + 0xa00042050003e020) * 0x10000000000000000 + 0x362c0003290000) * 0x10000000000000000 + 0x1e050001a0500012) * 0x10000000000000000 + 0x2c00011139001063) * 0x10000000000000000 + 0xf4e6300f4d0680) * 0x10000000000000000 + 0xf4c6300935620033) * 0x10000000000000000 + 0x6630033517943349) * 0x10000000000000000 + 0xc000369e00035008) * 0x10000000000000000 + 0x20349c0002a9e000) * 0x10000000000000000 + 0x291494028a800012) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state6 (i : Nat) : Option RowState :=
  let h := unpack (0x2e562a4623771c77 * 0x10000000000000000 + 0x15770e7707770077) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack (((((((((((((((0x7a1084210823c84 * 0x10000000000000000 + 0x109e20842f7a1082) * 0x10000000000000000 + 0x3c84109e20842f78) * 0x10000000000000000 + 0x4210823c84109) * 0x10000000000000000 + 0xe2084210000f0000) * 0x10000000000000000 + 0x1780004210821084) * 0x10000000000000000 + 0x109e20842f03c000) * 0x10000000000000000 + 0x17a10823c8410) * 0x10000000000000000 + 0x84208421001ef001) * 0x10000000000000000 + 0xe00000f780004210) * 0x10000000000000000 + 0x821084109e208421) * 0x10000000000000000 + 0x3c000000f780004) * 0x10000000000000000 + 0x210823c841084208) * 0x10000000000000000 + 0x42f001e000020780) * 0x10000000000000000 + 0x4210821084109e) * 0x10000000000000000 + 0x20842f03c0000020) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge6 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x31982b8c268a210b * 0x10000000000000000 + 0x1714128909130012) (((((((((((((((((((((((((((((((((((((((((((((((((((((0x637000063 * 0x10000000000000000 + 0x3000062b1aba6290) * 0x10000000000000000 + 0x2006271aca625100) * 0x10000000000000000 + 0x337010033310003) * 0x10000000000000000 + 0x2b16ba3290200327) * 0x10000000000000000 + 0x16ca325470031f22) * 0x10000000000000000 + 0x31b55000370200) * 0x10000000000000000 + 0x33550002b07ba02) * 0x10000000000000000 + 0x9020002707ca0258) * 0x10000000000000000 + 0xe0001f220001bc60) * 0x10000000000000000 + 0x133a0000f19b86) * 0x10000000000000000 + 0x2b19c862715b832b) * 0x10000000000000000 + 0x15c832713b831f13) * 0x10000000000000000 + 0xc831b06b802b06c8) * 0x10000000000000000 + 0x2704b801f04c801) * 0x10000000000000000 + 0xb00b801300c800f0) * 0x10000000000000000 + 0x400f4e0400f4d00a) * 0x10000000000000000 + 0x8f4c050031e0e003) * 0x10000000000000000 + 0x1d00a631c010004e) * 0x10000000000000000 + 0x100042010003613) * 0x10000000000000000 + 0x2a9e00f4e9e00) * 0x10000000000000000 + 0xf4d02a6f4c020033) * 0x10000000000000000 + 0x6050033500a63349) * 0x10000000000000000 + 0xc0004e9c000429c0) * 0x10000000000000000 + 0x369c0002a05000) * 0x10000000000000000 + 0x12420064e2d0064a) * 0x10000000000000000 + 0x2b00642440063e1f) * 0x10000000000000000 + 0x63615006325b00) * 0x10000000000000000 + 0x62a2d006261e0034) * 0x10000000000000000 + 0xe28003421f003362) * 0x10000000000000000 + 0x3350b9c334870) * 0x10000000000000000 + 0x3261e0004e28000) * 0x10000000000000000 + 0x427e000325b0002a) * 0x10000000000000000 + 0x2000029009c02803) * 0x10000000000000000 + 0xf4e0300f4d158a) * 0x10000000000000000 + 0xf4c0100336030033) * 0x10000000000000000 + 0x5138a334a30001eb) * 0x10000000000000000 + 0xe0001d008a01c850) * 0x10000000000000000 + 0xf4e8500f4d00a4f) * 0x10000000000000000 + 0x4c140032a2c00329) * 0x10000000000000000 + 0xa2328860031e81) * 0x10000000000000000 + 0x4e850004d0298) * 0x10000000000000000 + 0x4c8100042850004) * 0x10000000000000000 + 0x1029a04089000368) * 0x10000000000000000 + 0x5000350094034840) * 0x10000000000000000 + 0x2a850002900920) * 0x10000000000000000 + 0x289e00f4e9e00f4d) * 0x10000000000000000 + 0x2a2f4c020033605) * 0x10000000000000000 + 0x33500a23349c00) * 0x10000000000000000 + 0x4e9e0004d027e04) * 0x10000000000000000 + 0xc9c000429e000410) * 0x10000000000000000 + 0xe7e0409c000369e0) * 0x10000000000000000 + 0x350c7e03405000) * 0x10000000000000000 + 0x129e00011007e010) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state7 (i : Nat) : Option RowState :=
  let h := unpack (0x2a6624661e661866 * 0x10000000000000000 + 0x12660c6606660066) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack ((((((((((((((0x7800042108210841 * 0x10000000000000000 + 0x9e20a42f03c0078) * 0x10000000000000000 + 0x4210821084109) * 0x10000000000000000 + 0xe20842f03c207800) * 0x10000000000000000 + 0x4210821084109e2) * 0x10000000000000000 + 0x842f03c22780004) * 0x10000000000000000 + 0x210823c84109e208) * 0x10000000000000000 + 0x5ef0842f78000421) * 0x10000000000000000 + 0x823c8418def109e) * 0x10000000000000000 + 0x20842f7800042108) * 0x10000000000000000 + 0x23c84211e4109e20) * 0x10000000000000000 + 0x842f7800043d0842) * 0x10000000000000000 + 0x10823c84109e2084) * 0x10000000000000000 + 0x2f7a108780004210) * 0x10000000000000000 + 0x823c84109e20842f) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge7 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x300b2d062889210f * 0x10000000000000000 + 0x1812118d0a8e0015) ((((((((((((((((((((((((((((((((((((((((((((((0x9c00c429c00c4 * 0x10000000000000000 + 0x11bc4c409c009350) * 0x10000000000000000 + 0x420000036020) * 0x10000000000000000 + 0x3500ac03400000) * 0x10000000000000000 + 0x2a02000291ac4028) * 0x10000000000000000 + 0x9c00c429c00c4100) * 0x10000000000000000 + 0xbec40000002a0200) * 0x10000000000000000 + 0x2900b0028aa00c4) * 0x10000000000000000 + 0x2aa00c4103b4c40a) * 0x10000000000000000 + 0xf0031ec10031d00b) * 0x10000000000000000 + 0xc31c3b0002a4b000) * 0x10000000000000000 + 0x2900ae0285900c42) * 0x10000000000000000 + 0x5900c4100bac4021) * 0x10000000000000000 + 0x342020033e2100) * 0x10000000000000000 + 0x3360200332000032) * 0x10000000000000000 + 0xa2200326b30031e1) * 0x10000000000000000 + 0x20031a5800042580) * 0x10000000000000000 + 0x368e0002a7c000) * 0x10000000000000000 + 0x1ab400c42c600c41) * 0x10000000000000000 + 0xb8c40210064200) * 0x10000000000000000 + 0x63e21006360200) * 0x10000000000000000 + 0x632000062a220062) * 0x10000000000000000 + 0x6b200342c5003360) * 0x10000000000000000 + 0xbaa32ab200042c50) * 0x10000000000000000 + 0x3600aa02a7d000) * 0x10000000000000000 + 0xe830000d00c600c) * 0x10000000000000000 + 0xc420000c4106) * 0x10000000000000000 + 0xb2c4000006420000) * 0x10000000000000000 + 0x63e0000636020063) * 0x10000000000000000 + 0x2000062a00006261) * 0x10000000000000000 + 0x90031d2a00319000) * 0x10000000000000000 + 0x1d0a000190000c) * 0x10000000000000000 + 0x420000c3e0000942) * 0x10000000000000000 + 0x94100b294000) * 0x10000000000000000 + 0x63502006310200) * 0x10000000000000000 + 0x6251000335020033) * 0x10000000000000000 + 0x1100032939000350) * 0x10000000000000000 + 0x2000315500029000) * 0x10000000000000000 + 0x932000093111cc9) * 0x10000000000000000 + 0x300000641000063d) * 0x10000000000000000 + 0x635000063100) * 0x10000000000000000 + 0x62902006251000) * 0x10000000000000000 + 0x341010033d100033) * 0x10000000000000000 + 0x5010033110003290) * 0x10000000000000000 + 0x2003255500041020) * 0x10000000000000000 + 0x3d550003502000) * 0x10000000000000000 + 0x3155000290200025) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state8 (i : Nat) : Option RowState :=
  let h := unpack (0x2a6624661e661866 * 0x10000000000000000 + 0x12660c6606660066) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack ((((((((((((((0x780004210823c841 * 0x10000000000000000 + 0x9e20842f001ef78) * 0x10000000000000000 + 0x43d0821084109) * 0x10000000000000000 + 0xe20842f020007800) * 0x10000000000000000 + 0x42188211e410842) * 0x10000000000000000 + 0x842f03c00780004) * 0x10000000000000000 + 0x210821084109e208) * 0x10000000000000000 + 0x42f03c0078000421) * 0x10000000000000000 + 0x823084109e20842) * 0x10000000000000000 + 0xf03c007a10842108) * 0x10000000000000000 + 0x23c84109e20842f0) * 0x10000000000000000 + 0x3c007a1087800023) * 0x10000000000000000 + 0xc84109e20842f03c) * 0x10000000000000000 + 0x7800042108211e) * 0x10000000000000000 + 0x410842084af03c00) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge8 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x218c1c8a1a051706 * 0x10000000000000000 + 0x13080a12028f0005) ((((((((((((((((((((((((((((((((((0x3300c4233 * 0x10000000000000000 + 0xc4100c0c403200) * 0x10000000000000000 + 0x423200036020003) * 0x10000000000000000 + 0x2000002a33000261) * 0x10000000000000000 + 0xa0001e120001a590) * 0x10000000000000000 + 0x123d0000e0200c) * 0x10000000000000000 + 0x4202009350200041) * 0x10000000000000000 + 0x200029110001e02) * 0x10000000000000000 + 0x1d0bac01c5600) * 0x10000000000000000 + 0x12020001100ac01) * 0x10000000000000000 + 0x9c00c429c00c411) * 0x10000000000000000 + 0x1acc409c006292a0) * 0x10000000000000000 + 0x299c00c429c00c) * 0x10000000000000000 + 0x4102b6c40000002a) * 0x10000000000000000 + 0x20002900b60289c) * 0x10000000000000000 + 0xc429c00c411bc2) * 0x10000000000000000 + 0xc400000042000003) * 0x10000000000000000 + 0x6000002a02000290) * 0x10000000000000000 + 0xb60280200935050) * 0x10000000000000000 + 0x931120063505006) * 0x10000000000000000 + 0x3156003350500331) * 0x10000000000000000 + 0x42020003e00) * 0x10000000000000000 + 0x36020003500b2) * 0x10000000000000000 + 0x340200032050003) * 0x10000000000000000 + 0x11aca030110001e0) * 0x10000000000000000 + 0x20001a5600012020) * 0x10000000000000000 + 0xe020093502009) * 0x10000000000000000 + 0x3112006350400631) * 0x10000000000000000 + 0x5600335050033100) * 0x10000000000000000 + 0x42020003e0000) * 0x10000000000000000 + 0x36020003519c003) * 0x10000000000000000 + 0x4110001e020001a5) * 0x10000000000000000 + 0x600012020000e9c0) * 0x10000000000000000 + 0xc429c00c4106acc) * 0x10000000000000000 + 0x409c006292a00029) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state9 (i : Nat) : Option RowState :=
  let h := unpack (0x2a6624661e661866 * 0x10000000000000000 + 0x12660c6606660066) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack ((((((((((((((0x7800042108210841 * 0x10000000000000000 + 0x8def03c000002278) * 0x10000000000000000 + 0x4210823c84109) * 0x10000000000000000 + 0xe20842f000227a10) * 0x10000000000000000 + 0x823c84108420842f) * 0x10000000000000000 + 0x1ef001e07a1082) * 0x10000000000000000 + 0x10a4108420842f03) * 0x10000000000000000 + 0xc00001e07a108210) * 0x10000000000000000 + 0x84108420842f03c2) * 0x10000000000000000 + 0x1e07a10823c84) * 0x10000000000000000 + 0x10842085ef0842f0) * 0x10000000000000000 + 0x1e0780004210823) * 0x10000000000000000 + 0xca4108420842f001) * 0x10000000000000000 + 0xe0780004210823c8) * 0x10000000000000000 + 0x4108620842f001e0) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge9 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x23921c0f150e1187 * 0x10000000000000000 + 0xe07070e03870007) ((((((((((((((((((((((((((((((((((((((0xb000c42b000c410 * 0x10000000000000000 + 0x2c6c407f0032a930) * 0x10000000000000000 + 0x32900c6328a7000) * 0x10000000000000000 + 0x42b00004102bc040) * 0x10000000000000000 + 0xa700036b00003503) * 0x10000000000000000 + 0xbc034ae0002ab000) * 0x10000000000000000 + 0x2901bc028930001) * 0x10000000000000000 + 0x2b00001100bc0103) * 0x10000000000000000 + 0xa00c423a00c4100c) * 0x10000000000000000 + 0x8c407d0031e83003) * 0x10000000000000000 + 0x1d00c631c3900042) * 0x10000000000000000 + 0x3a0004101b404039) * 0x10000000000000000 + 0x363a0003500b4) * 0x10000000000000000 + 0x343e0002a3a0002) * 0x10000000000000000 + 0x900ae02862003425) * 0x10000000000000000 + 0x20033e5000336640) * 0x10000000000000000 + 0x3321c0032a52003) * 0x10000000000000000 + 0x265a0031e5d0031a) * 0x10000000000000000 + 0x330004233000361c) * 0x10000000000000000 + 0x2a340002900c0) * 0x10000000000000000 + 0x28850001a890033) * 0x10000000000000000 + 0x6960033500c43349) * 0x10000000000000000 + 0xc0002a9e000290cb) * 0x10000000000000000 + 0xe028a30001e89003) * 0x10000000000000000 + 0x36960033500c4334) * 0x10000000000000000 + 0x9c0002a9e0002900) * 0x10000000000000000 + 0xbe028a10001e6200) * 0x10000000000000000 + 0x642510063e500063) * 0x10000000000000000 + 0x66300632b50062a5) * 0x10000000000000000 + 0x20062659003426a0) * 0x10000000000000000 + 0x33659000426a000) * 0x10000000000000000 + 0x36b50002a5a00029) * 0x10000000000000000 + 0xba028860000e81) * 0x10000000000000000 + 0xc428100c4100c4) * 0x10000000000000000 + 0xc40110001e2a0001) * 0x10000000000000000 + 0xd00b001c82000128) * 0x10000000000000000 + 0x100c428100c4100c) * 0x10000000000000000 + 0x2c40110001e2a000) * 0x10000000000000000 + 0x1d00b601c8200012) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state10 (i : Nat) : Option RowState :=
  let h := unpack (0x285523551e551865 * 0x10000000000000000 + 0x12660c6606660066) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack ((((((((((((((0x7 * 0x10000000000000000 + 0x80004210823ca410) * 0x10000000000000000 + 0x9e20842f78000421) * 0x10000000000000000 + 0x823ca6109e20842) * 0x10000000000000000 + 0xf7800043d0821084) * 0x10000000000000000 + 0x109e20a42f780004) * 0x10000000000000000 + 0x21082bcaf23c8418) * 0x10000000000000000 + 0xdef109e27a10823c) * 0x10000000000000000 + 0x84109e2084210000) * 0x10000000000000000 + 0xf000017800042108) * 0x10000000000000000 + 0x23c84109e20842f0) * 0x10000000000000000 + 0x17a10823c8410) * 0x10000000000000000 + 0x8420842f001e0000) * 0x10000000000000000 + 0x20780004210823c8) * 0x10000000000000000 + 0x4109e20842f00020) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge10 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x1983168615821305 * 0x10000000000000000 + 0x10060c87060d000c) (((((((((((((((((((((((0x936000 * 0x10000000000000000 + 0x93500d893439009) * 0x10000000000000000 + 0x36390093500d6934) * 0x10000000000000000 + 0x7b00012800001100) * 0x10000000000000000 + 0xd001000009360000) * 0x10000000000000000 + 0x62900d4c40210032) * 0x10000000000000000 + 0x467003187b000240) * 0x10000000000000000 + 0xce01c050031e0e0) * 0x10000000000000000 + 0x31d00cc31c01000) * 0x10000000000000000 + 0x420100036130002a) * 0x10000000000000000 + 0x200c420200c4100) * 0x10000000000000000 + 0xccc4000000420000) * 0x10000000000000000 + 0x36000002a110001) * 0x10000000000000000 + 0xe140032a2c003290) * 0x10000000000000000 + 0xca328860031e810) * 0x10000000000000000 + 0x42850004102c40) * 0x10000000000000000 + 0x4089000368500035) * 0x10000000000000000 + 0xc4034840002a85) * 0x10000000000000000 + 0x2900c20280200) * 0x10000000000000000 + 0xc420200c4100cac4) * 0x10000000000000000 + 0x4202000410) * 0x10000000000000000 + 0x2be0400000036020) * 0x10000000000000000 + 0x350ebe03400000) * 0x10000000000000000 + 0x2a020002900b0028) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state11 (i : Nat) : Option RowState :=
  let h := unpack (0x23551e5519551455 * 0x10000000000000000 + 0xf550a5505550055) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack ((((((((((((0x7a10823c * 0x10000000000000000 + 0x84109e20842f001e) * 0x10000000000000000 + 0xf7a10821084109e2) * 0x10000000000000000 + 0x842f03c20780004) * 0x10000000000000000 + 0x21082108418def03) * 0x10000000000000000 + 0xc227a10823c84109) * 0x10000000000000000 + 0xe2085ef0842f7a10) * 0x10000000000000000 + 0x823c8418def109e2) * 0x10000000000000000 + 0x842f78000421082) * 0x10000000000000000 + 0x3c84109e20842f78) * 0x10000000000000000 + 0x4212a23c84109) * 0x10000000000000000 + 0xe20842f7a10843d0) * 0x10000000000000000 + 0x823c84109e20842f) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge11 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x1708158312860e09 * 0x10000000000000000 + 0x88b070304060008) (((((((((((((((((((((((0x3200036020 * 0x10000000000000000 + 0x32000002a33000) * 0x10000000000000000 + 0x261a0001e120001a) * 0x10000000000000000 + 0x59000123d0000e00) * 0x10000000000000000 + 0x2a020002900d8) * 0x10000000000000000 + 0x28ad00936ad0093) * 0x10000000000000000 + 0x503d29347a0001e9) * 0x10000000000000000 + 0x20001d00d001c210) * 0x10000000000000000 + 0x336020033200003) * 0x10000000000000000 + 0x2a2200326b30031e) * 0x10000000000000000 + 0x120031a580003669) * 0x10000000000000000 + 0x2a7c0001a2100) * 0x10000000000000000 + 0x6360000632000062) * 0x10000000000000000 + 0xa22006260dd43360) * 0x10000000000000000 + 0xbd432a02d403600d) * 0x10000000000000000 + 0x402a7d0000e83000) * 0x10000000000000000 + 0xd00dc00c0000936) * 0x10000000000000000 + 0x93500da93439) * 0x10000000000000000 + 0x936390093502d6) * 0x10000000000000000 + 0x9347b00012800001) * 0x10000000000000000 + 0x100d201000009360) * 0x10000000000000000 + 0x9320000629020) * 0x10000000000000000 + 0x625100032902003) * 0x10000000000000000 + 0x2539000290200025) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state12 (i : Nat) : Option RowState :=
  let h := unpack (0x23441e5419551455 * 0x10000000000000000 + 0xf550a5505550055) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack ((((((((((((0x780 * 0x10000000000000000 + 0x4210823ca618de) * 0x10000000000000000 + 0xf780004210833de6) * 0x10000000000000000 + 0x2bcaf18def7a1082) * 0x10000000000000000 + 0x3c84109e20842f00) * 0x10000000000000000 + 0x17a10823c84109) * 0x10000000000000000 + 0xe20842f000207a10) * 0x10000000000000000 + 0x823c84109e20842f) * 0x10000000000000000 + 0x2278000421082) * 0x10000000000000000 + 0x3c8418def000227a) * 0x10000000000000000 + 0x10823ca410842084) * 0x10000000000000000 + 0x2f001e07a10823c8) * 0x10000000000000000 + 0x4108620842f001e0) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge12 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x1503130411830e86 * 0x10000000000000000 + 0xa09040c02040004) (((((((((((((((((((0x790062a7900 * 0x10000000000000000 + 0x62900e062800de93) * 0x10000000000000000 + 0x4790031866000182) * 0x10000000000000000 + 0x40000c0000036000) * 0x10000000000000000 + 0x2a110001e00000) * 0x10000000000000000 + 0x36020003502d8034) * 0x10000000000000000 + 0x2a020002900) * 0x10000000000000000 + 0xd80287d0031e8300) * 0x10000000000000000 + 0x31d00dc31c390003) * 0x10000000000000000 + 0x63a0003502d60343) * 0x10000000000000000 + 0xe0002a3a0002900d) * 0x10000000000000000 + 0x60287b009367b009) * 0x10000000000000000 + 0x3500dc9347800036) * 0x10000000000000000 + 0x7b0003501d203478) * 0x10000000000000000 + 0x2a7b0002900d2) * 0x10000000000000000 + 0x28880001e7b0001) * 0x10000000000000000 + 0xd00d001c110001e2) * 0x10000000000000000 + 0xa0001d00d801c820) * 0x10000000000000000 + 0x12110001e2a000) * 0x10000000000000000 + 0x1d00da01c8200012) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def state13 (i : Nat) : Option RowState :=
  let h := unpack (0x1d33194315441144 * 0x10000000000000000 + 0xd44094404540044) 16 (i % 8)
  some (h % 16, (List.range ((h/16) % 16)).map (fun j => unpack (((((((((0x7a10823ca618def7 * 0x10000000000000000 + 0xa10833de62bcaf18) * 0x10000000000000000 + 0xdef7a10823c8418d) * 0x10000000000000000 + 0xef000227a10823c8) * 0x10000000000000000 + 0x4109e20842f7a108) * 0x10000000000000000 + 0x23ca4109e20842f7) * 0x10000000000000000 + 0xa10823ca6109e208) * 0x10000000000000000 + 0x42f7a1082bcaf23c) * 0x10000000000000000 + 0x8418def109e27800) * 0x10000000000000000 + 0x4212a23c8418def) 20 (h/256+j)), [])

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge13 (i tok : Nat) : Option DagLink :=
  dagLookupLinks (0x980080305060500 * 0x10000000000000000 + 0x500038301840003) ((((((((0x79003 * 0x10000000000000000 + 0x186600018240000c) * 0x10000000000000000 + 0x780002a7b0002902) * 0x10000000000000000 + 0xe0028880001e7b00) * 0x10000000000000000 + 0x1d00e001c7b0001) * 0x10000000000000000 + 0x2800001100e00102) * 0x10000000000000000 + 0x10032467003187b0) * 0x10000000000000000 + 0x2400de01c78006) * 0x10000000000000000 + 0x2a780062902e0628) 16 7 13 7 8 8 (i % 8) tok

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def states (i : Nat) : Option RowState := (if i < 56 then (if i < 24 then (if i < 8 then state0 i else (if i < 16 then state1 i else state2 i)) else (if i < 40 then (if i < 32 then state3 i else state4 i) else (if i < 48 then state5 i else state6 i))) else (if i < 80 then (if i < 64 then state7 i else (if i < 72 then state8 i else state9 i)) else (if i < 96 then (if i < 88 then state10 i else state11 i) else (if i < 104 then state12 i else state13 i))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def edge (i tok : Nat) : Option DagLink := (if i < 56 then (if i < 24 then (if i < 8 then edge0 i tok else (if i < 16 then edge1 i tok else edge2 i tok)) else (if i < 40 then (if i < 32 then edge3 i tok else edge4 i tok) else (if i < 48 then edge5 i tok else edge6 i tok))) else (if i < 80 then (if i < 64 then edge7 i tok else (if i < 72 then edge8 i tok else edge9 i tok)) else (if i < 96 then (if i < 88 then edge10 i tok else edge11 i tok) else (if i < 104 then edge12 i tok else edge13 i tok))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def links (i tok : Nat) : Option DagLink := do
  let (d,a) ← edge i tok
  if d == 0 then none else some (d-1,a)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def cut (i tok : Nat) (s : RowState) : Bool :=
  match edge i tok with
  | some (0,code) => Geometry.rectangleReject goal s (hullCode code)
  | _ => false
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem cutOpen (i tok s) (h : MonoViable mask goal s) : cut i tok s = false := by
  unfold cut
  split
  · exact Geometry.rectangleOpen _ h
  · rfl

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
def check := scan mask goal neg states 112 (dagMoves records) links cut

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b0to28 : treeBlock 0 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b28to56 : treeBlock 28 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b0to56 : treeBlock 0 56 check = true := treeBlock_merge (left := 28) (right := 28) b0to28 b28to56

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b56to84 : treeBlock 56 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b84to112 : treeBlock 84 28 check = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b56to112 : treeBlock 56 56 check = true := treeBlock_merge (left := 28) (right := 28) b56to84 b84to112

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem b0to112 : treeBlock 0 112 check = true := treeBlock_merge (left := 56) (right := 56) b0to56 b56to112

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem lower : AOLower mask raw goal 11 := by
  apply lowerStock (width := 25) (root := 0) (fuel := 10) (row := (10,raw,[]))
    (stockMaskedOfCheck (by decide +kernel)) (by unfold properWord; decide +kernel)
    (by decide +kernel) (by unfold Masked; decide +kernel) autos
    (by decide +kernel : ∀ n ∈ neg, goal.testBit n = false) cutOpen
    (fun i hi => treeBlock_at b0to112 (Nat.zero_le i) (by simpa using hi))
  · decide +kernel
  · decide +kernel
  · rfl
  · rfl
end Rep9102.SmallCrown

open WordEngine
namespace Rep9102.Subfloor
open SmallCrown

def rawOn (m : Word) := Rep9102.stock.map (· &&& m)
def dropMask (v : Fin 5) : Word :=
  (![0x1ef7bc0,0x1def41d,0x1bd837b,0x1705ef7,0x7bdef] : Fin 5 → Nat) v
def omitRowMask (v : Fin 5) : Word :=
  (![0x1ffffe0,0x1fffc1f,0x1ff83ff,0x1f07fff,0xfffff] : Fin 5 → Nat) v
def omitColMask (v : Fin 5) : Word :=
  (![0x1ef7bde,0x1def7bd,0x1bdef7b,0x17bdef7,0xf7bdef] : Fin 5 → Nat) v

private theorem mapLower {m n target low roots bank} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (andG : ∀ a b, f (a &&& b) = f a &&& f b) (orG : ∀ a b, f (a ||| b) = f a ||| f b)
    (supply : ∀ a ∈ roots, AvailableWord n bank (f a)) (lower : AOLower n bank (f target) low) :
    AOLower m roots target low := by
  have av {roots bank} (src : ∀ a ∈ roots, AvailableWord n bank (f a)) {a}
      (h : AvailableWord m roots a) : AvailableWord n bank (f a) := by
    rcases h with rfl | rfl | h
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ h
  intro vs built hit
  have mapBuilt {ws roots bank} (src : ∀ a ∈ roots, AvailableWord n bank (f a))
      (b : AOBuild m roots ws) : AOBuild n bank (ws.map f) := by
    induction ws generalizing roots bank with
    | nil => trivial
    | cons w ws ih =>
      obtain ⟨⟨a,b,ha,hb,op⟩,tail⟩ := b
      refine ⟨⟨f a,f b,av src ha,av src hb,?_⟩,ih ?_ tail⟩
      · rcases op with rfl | rfl
        · exact Or.inl (andG _ _)
        · exact Or.inr (orG _ _)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ h => Or.inr (Or.inr (List.mem_cons_of_mem _ h))) (src _ hx)
  rw [← List.length_map (f := f) (as := vs)]
  apply lower (vs.map f) (mapBuilt supply built)
  apply av _ hit
  intro w hw
  rcases List.mem_append.mp hw with hv | hr
  · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hv)))
  · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_append_right _ hx))) (supply _ hr)

private def gather : List Nat → Word → Word
  | [], _ => 0
  | j::js, w => Nat.bit (w.testBit j) (gather js w)

private theorem gatherGates (js : List Nat) (x y : Word) :
    gather js (x &&& y) = gather js x &&& gather js y ∧
    gather js (x ||| y) = gather js x ||| gather js y := by
  induction js with
  | nil => simp [gather]
  | cons j js ih => exact ⟨by simp [gather,Nat.land_bit,ih.1], by simp [gather,Nat.lor_bit,ih.2]⟩

private def slots (v : Fin 5) : List Nat :=
  (List.range 19).map fun j =>
    let skip := fun a => if a < v.val then a else a+1
    if j % 5 = 4 then 25 else 5*skip (j/5) + skip (j % 5)

theorem allFour (v : Fin 5) : AOLower (dropMask v) (rawOn (dropMask v)) (T &&& dropMask v) 11 := by
  have ok := (by decide +kernel : ∀ i : Fin 5,
    let f := gather (slots i)
    f 0 = 0 ∧ f (dropMask i) = SmallCrown.mask ∧ f (T &&& dropMask i) = SmallCrown.goal ∧
    (rawOn (dropMask i)).all (fun w => availableB SmallCrown.mask SmallCrown.raw (f w)) = true) v
  obtain ⟨zero,ones,goalEq,cover⟩ := ok
  exact mapLower _ zero ones (fun a b => (gatherGates _ a b).1) (fun a b => (gatherGates _ a b).2)
    (suppliesOfCheck cover) (goalEq ▸ SmallCrown.lower)

private abbrev removesPort (m s : Word) : Prop :=
  ∃ p n : Fin 25, (T &&& m).testBit p.val = true ∧ (T &&& m).testBit n.val = false ∧
    ∀ w ∈ rawOn m, w.testBit p.val = true → w.testBit n.val = false → maskedFlat s w

private def lineMask (row : Bool) (i : Fin 5) := if row then omitRowMask i else omitColMask i

theorem line12 (row : Bool) (i : Fin 5) :
    AOLower (lineMask row i) (rawOn (lineMask row i)) (T &&& lineMask row i) 12 := by
  let m := lineMask row i
  let s := dropMask i
  have properties := (by decide +kernel : ∀ r : Bool, ∀ v : Fin 5,
    let m := lineMask r v
    let s := dropMask v
    (rawOn m).all (fun w => w &&& m == w) = true ∧
    (T &&& m ≠ 0 ∧ T &&& m ≠ m) ∧
    ¬ maskedFlat s (T &&& m) ∧ (T &&& m) &&& s = T &&& s ∧
    (rawOn m).all (fun w => availableB s (rawOn s) (w &&& s)) = true ∧ removesPort m s) row i
  obtain ⟨masked,proper,nonflat,restrict,sources,p,n,pos,neg,sep⟩ := properties
  intro vs built hit
  obtain ⟨k,S,budget,live,sub⟩ := extractAO (stockMaskedOfCheck masked) built hit proper
  obtain ⟨w,hw,yes,no⟩ := liveDirected live pos neg
  have flat : w ∈ flatSet s S := Finset.mem_filter.mpr ⟨hw,sep w (sub w hw) yes no⟩
  have posCard := Finset.card_pos.mpr ⟨w,flat⟩
  have supply : ∀ x ∈ projectedStock s S, AvailableWord s ([] ++ rawOn s) x := by
    intro x hx
    simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image] at hx
    rcases hx with rfl | rfl | ⟨a,ha,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact suppliesOfCheck sources a (sub a ha)
  have cut := Project.cut live nonflat (show AOBuild s (rawOn s) [] from trivial) supply (restrict ▸ allFour i)
  simp only [List.length_nil,Nat.zero_add] at cut
  change 11 + (flatSet s S).card ≤ k at cut
  omega

theorem row12 (v : Fin 5) : AOLower (omitRowMask v) (rawOn (omitRowMask v)) (T &&& omitRowMask v) 12 :=
  line12 true v
theorem col12 (v : Fin 5) : AOLower (omitColMask v) (rawOn (omitColMask v)) (T &&& omitColMask v) 12 :=
  line12 false v
def minorFacts : List (Word × Nat) :=
  (List.finRange 5).map (fun v => (dropMask v, 11)) ++
  (List.finRange 5).map (fun v => (omitRowMask v, 12)) ++
  (List.finRange 5).map (fun v => (omitColMask v, 12))

theorem minorMasks_distinct : minorFacts.length = 15 ∧ (minorFacts.map Prod.fst).Nodup := by
  decide +kernel

theorem minorLower {m n} (h : (m,n) ∈ minorFacts) : AOLower m (rawOn m) (T &&& m) n := by
  simp only [minorFacts, List.mem_append, List.mem_map, or_assoc] at h
  rcases h with ⟨v, _, e⟩ | ⟨v, _, e⟩ | ⟨v, _, e⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact allFour v
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact row12 v
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    exact col12 v

end Rep9102.Subfloor

open Rep9102 Rep9102.Orbit Rep9102.Project
namespace Punctured
set_option maxHeartbeats 0 in
def postedHere (u v : Fin 5) : Bool := (32435687 : Nat).testBit (5*u.val+v.val)
set_option maxHeartbeats 0 in
def rawHere : List (BitVec 25) := [0x1f, 0x3e0, 0x7c00, 0xf8000, 0x1f00000, 0x1084210, 0x842108, 0x421084, 0x108421, 0x210842]
set_option maxHeartbeats 0 in
def stockHere : List Word := rawHere.map BitVec.toNat
set_option maxHeartbeats 0 in
def target25Here : BitVec 25 := 0xfbefbc
set_option maxHeartbeats 0 in
abbrev THere : Word := target25Here.toNat
set_option maxHeartbeats 0 in
def pointHere (r : Fin 25) := oneEach (Fin.ofNat 5 (r.val / 5)) ((![3,4,2,1,0] : Fin 5 → Fin 5) (Fin.ofNat 5 (r.val % 5)))
set_option maxHeartbeats 0 in
theorem representation_liveHere (C : Circuit) (legal : Monotone2 C) (right : Represents postedHere C) :
    ∃ k ≤ C.size, LiveWord (fullMask 25) THere k 0 stockHere.toFinset := by
  have rawBits : ∀ r : Fin 25, (rawHere.map fun w => w.getLsbD r.val) = pointHere r := by decide +kernel
  have goalBits : ∀ r : Fin 25, target25Here.getLsbD r.val =
      postedHere (Fin.ofNat 5 (r.val / 5)) ((![3,4,2,1,0] : Fin 5 → Fin 5) (Fin.ofNat 5 (r.val % 5))) := by decide +kernel
  let eb := C.gates.foldl hcsStep rawHere
  have eq : eb.getD C.output 0 = target25Here := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Fin 25 := ⟨j,hj⟩
    have bits := hcsFoldBits rawHere r C.gates (monoFan legal)
    have ack := right (Fin.ofNat 5 (r.val / 5)) ((![3,4,2,1,0] : Fin 5 → Fin 5) (Fin.ofNat 5 (r.val % 5)))
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (pointHere r)).getD C.output false = _ at ack
    rw [← rawBits r,← bits] at ack
    exact (hcsGetDBit eb j C.output).trans (ack.trans (goalBits r).symm)
  obtain ⟨ws,len,built,sub⟩ := aoBuilds rawHere C.gates legal
  have hit : AvailableWord (fullMask 25) (ws++stockHere) THere := by
    change AvailableWord _ _ target25Here.toNat
    rw [←eq,List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some w => exact Or.inr (Or.inr (sub w (List.mem_of_getElem? h)))
  obtain ⟨k,S,budget,run,subset⟩ := extractAO (stockMaskedOfCheck (by decide +kernel : stockHere.all (fun w => w &&& fullMask 25 == w) = true)) built hit
      (by unfold properWord; decide +kernel)
  have witnesses : ∀ w ∈ stockHere, ∃ p n : Fin 25, THere.testBit p.val = true ∧ THere.testBit n.val = false ∧
      ∀ u ∈ stockHere, u.testBit p.val = true → u.testBit n.val = false → u = w := by decide +kernel
  have same : S = stockHere.toFinset := by
    ext w; constructor
    · exact fun h => List.mem_toFinset.mpr (subset w h)
    · intro h
      obtain ⟨p,n,yes,no,unique⟩ := witnesses w (List.mem_toFinset.mp h)
      obtain ⟨u,mem,a,b⟩ := liveDirected run yes no
      exact (unique u (subset u mem) a b) ▸ mem
  exact ⟨k,budget.trans (Nat.le_of_eq len),same ▸ run⟩

def rm : Word := Subfloor.omitRowMask 0

theorem restricted : AOLower rm (Subfloor.rawOn rm) (THere &&& rm) 12 := by
  have eq : THere &&& rm = Rep9102.T &&& rm := by decide +kernel
  rw [eq]
  exact Subfloor.row12 0

theorem lower13 (C : Circuit) (hc : Monotone2 C) (hr : Represents postedHere C) : 13 ≤ C.size := by
  obtain ⟨k,ks,run⟩ := representation_liveHere C hc hr
  have correct : stockHere.all (fun a => availableB rm (Subfloor.rawOn rm) (a &&& rm)) = true := by decide +kernel
  have supplied : ∀ x ∈ projectedStock rm stockHere.toFinset, AvailableWord rm ([] ++ Subfloor.rawOn rm) x := by
    intro x hx
    simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image] at hx
    rcases hx with rfl | rfl | ⟨a,ha,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact suppliesOfCheck correct a (List.mem_toFinset.mp ha)
  have cut := Project.cut run (by decide +kernel : ¬maskedFlat rm THere)
    (show AOBuild rm (Subfloor.rawOn rm) [] from trivial) supplied restricted
  have flat : (flatSet rm stockHere.toFinset).card = 1 := by decide +kernel
  simp only [List.length_nil,Nat.zero_add,flat] at cut
  omega

end Punctured
end PEqualNP.Outside.L_meta_25467


/- Adapted from the checked live-circuit normalization and search in L-meta-6349. -/

namespace PEqualNP.Outside.L_meta_25467.Donor4

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

theorem build_mono {ops : α → α → Finset α} {goal : α} {k : ℕ} {s t : Finset α}
    (hsub : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hsub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, hab, z, hz, ih (Finset.insert_subset_insert z hsub) tail⟩

def liveChain (ops : α → α → Finset α) (goal : α) : List (α × α × α) → Finset α → Prop
  | [], s => s = {goal}
  | (a, b, z) :: gs, s =>
    a ∈ s ∧ b ∈ s ∧ a ≠ b ∧ z ∈ ops a b ∧ z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ liveChain ops goal gs (insert z rest)

theorem compress_chain {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) :
    ∃ gs : List (α × α × α), gs.length ≤ k ∧ ∃ s ⊆ available, liveChain ops goal gs s := by
  induction k generalizing available with
  | zero =>
    exact ⟨[], Nat.le_refl 0, {goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨gs, hlen, s, hs, hrun⟩ := ih skip
      exact ⟨gs, Nat.le_succ_of_le hlen, s, hs, hrun⟩
    · obtain ⟨gs, hlen, t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨gs, Nat.le_succ_of_le hlen, t, sub, hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨(a, b, z) :: gs, Nat.succ_le_succ hlen, s, hs,
          by simp [s], by simp [s], hab, hz, fun h => hzout (hs h), rest, rfl, ?_⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem chain_to_build {ops : α → α → Finset α} {goal : α} {gs : List (α × α × α)} {s : Finset α}
    (h : liveChain ops goal gs s) : build ops goal gs.length s := by
  induction gs generalizing s with
  | nil => change s = {goal} at h; simp [build, h]
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨ha, hb, hab, hz, _, rest, hs, tail⟩
    refine Or.inr ⟨a, ha, b, hb, hab, z, hz, build_mono ?_ (ih tail)⟩
    intro u hu
    rw [hs]
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_insert_self u _
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))

theorem chain_card {ops : α → α → Finset α} {goal : α} {gs : List (α × α × α)} {s : Finset α}
    (h : liveChain ops goal gs s) : s.card ≤ gs.length + 1 := by
  induction gs generalizing s with
  | nil => change s = {goal} at h; simp [h]
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨_, _, _, _, hout, rest, rfl, tail⟩
    have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
    have htail := ih tail
    rw [Finset.card_insert_of_notMem hzrest] at htail
    have h₁ := Finset.card_insert_le a (insert b rest)
    have h₂ := Finset.card_insert_le b rest
    simp only [List.length_cons]
    omega

theorem chain_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {gs : List (α × α × α)} {s : Finset α} (h : liveChain ops goal gs s) : ∃ w ∈ s, D w := by
  induction gs generalizing s with
  | nil => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨ha, hb, _, hz, _, rest, rfl, tail⟩
    obtain ⟨w, hw, hD⟩ := ih tail
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rcases hops a b w hz hD with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    · exact ⟨w, by simp [hw], hD⟩

theorem swap_two {ops : α → α → Finset α} {goal : α}
    {g₁ g₂ : α × α × α} {gs : List (α × α × α)} {s₀ : Finset α}
    (h : liveChain ops goal (g₁ :: g₂ :: gs) s₀)
    (h1 : g₂.1 ≠ g₁.2.2) (h2 : g₂.2.1 ≠ g₁.2.2) :
    liveChain ops goal (g₂ :: g₁ :: gs) s₀ ∨ build ops goal (gs.length + 1) s₀ := by
  rcases g₁ with ⟨a₁, b₁, z₁⟩
  rcases g₂ with ⟨a₂, b₂, z₂⟩
  rcases h with ⟨ha₁, hb₁, hab₁, hz₁, hout₁, rest₁, hs₀,
                 ha₂, hb₂, hab₂, hz₂, hout₂, rest₂, hs₁, tail⟩
  dsimp only at h1 h2
  have hz₁_r₂ : z₁ ∈ rest₂ := by
    have hm : z₁ ∈ insert a₂ (insert b₂ rest₂) := hs₁ ▸ Finset.mem_insert_self z₁ rest₁
    rcases Finset.mem_insert.mp hm with h | hm
    · exact absurd h.symm h1
    · rcases Finset.mem_insert.mp hm with h | hm
      · exact absurd h.symm h2
      · exact hm
  let core := rest₂.erase z₁
  have hcore_eq : insert z₁ core = rest₂ := Finset.insert_erase hz₁_r₂
  have hz₁_core : z₁ ∉ core := Finset.notMem_erase z₁ rest₂
  have hz₁_r₁ : z₁ ∉ rest₁ := fun hm => hout₁ (hs₀ ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hr₁ : rest₁ = insert a₂ (insert b₂ core) := by
    ext u
    by_cases hu : u = z₁
    · subst hu
      simp [hz₁_r₁, h1.symm, h2.symm, hz₁_core]
    · have hmem : u ∈ insert z₁ rest₁ ↔ u ∈ insert a₂ (insert b₂ (insert z₁ core)) := by
        rw [hcore_eq, hs₁]
      simp [hu] at hmem
      simpa using hmem
  by_cases hz₂_s₀ : z₂ ∈ s₀
  · right
    refine Or.inr ⟨a₁, ha₁, b₁, hb₁, hab₁, z₁, hz₁, build_mono ?_ (chain_to_build tail)⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.mem_insert_of_mem hz₂_s₀
    · rw [← hcore_eq] at hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_insert_self u s₀
      · rw [hs₀, hr₁]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))))
  · left
    have hs₀' : s₀ = insert a₂ (insert b₂ (insert a₁ (insert b₁ core))) := by
      rw [hs₀, hr₁]
      ext u; simp [or_left_comm]
    have ha₂_s₀ : a₂ ∈ s₀ := by rw [hs₀']; simp
    have hb₂_s₀ : b₂ ∈ s₀ := by rw [hs₀']; simp
    have hz₁_ne_z₂ : z₁ ≠ z₂ := fun heq => hout₂ (heq ▸ Finset.mem_insert_self z₁ rest₁)
    have hs₁' : insert z₂ (insert a₁ (insert b₁ core)) = insert a₁ (insert b₁ (insert z₂ core)) := by
      ext u; simp [or_left_comm]
    have hz₁_out' : z₁ ∉ insert z₂ (insert a₁ (insert b₁ core)) := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | hm
      · exact hz₁_ne_z₂ h
      · exact hout₁ (hs₀' ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    refine ⟨ha₂_s₀, hb₂_s₀, hab₂, hz₂, hz₂_s₀, insert a₁ (insert b₁ core), hs₀',
            by rw [hs₁']; simp, by rw [hs₁']; simp, hab₁, hz₁, hz₁_out', insert z₂ core, hs₁', ?_⟩
    have hs₂' : insert z₁ (insert z₂ core) = insert z₂ rest₂ := by
      rw [← hcore_eq, Finset.insert_comm]
    simpa only [hs₂'] using tail

def chainOrd (key : α → ℕ) : ℕ → List (α × α × α) → Prop
  | _, [] => True
  | last, (a, b, z) :: gs =>
    (key a = last ∨ key b = last ∨ last ≤ key z) ∧ chainOrd key (key z) gs

def invCount (key : α → ℕ) : List (α × α × α) → ℕ
  | [] => 0
  | g :: gs => (gs.filter (fun h => decide (key h.2.2 < key g.2.2))).length + invCount key gs

theorem invCount_swap_lt (key : α → ℕ) (pre suf : List (α × α × α)) (g₁ g₂ : α × α × α)
    (hlt : key g₂.2.2 < key g₁.2.2) :
    invCount key (pre ++ g₂ :: g₁ :: suf) < invCount key (pre ++ g₁ :: g₂ :: suf) := by
  induction pre with
  | nil =>
    simp only [List.nil_append, invCount, List.filter_cons]
    have h1 : decide (key g₂.2.2 < key g₁.2.2) = true := decide_eq_true hlt
    have h2 : decide (key g₁.2.2 < key g₂.2.2) = false := decide_eq_false (by omega)
    simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, List.length_cons]
    omega
  | cons x xs ih =>
    simp only [List.cons_append, invCount]
    have hperm : (xs ++ g₂ :: g₁ :: suf).Perm (xs ++ g₁ :: g₂ :: suf) :=
      List.Perm.append_left xs (List.Perm.swap g₁ g₂ suf)
    have hlen : ((xs ++ g₂ :: g₁ :: suf).filter (fun h => decide (key h.2.2 < key x.2.2))).length =
                ((xs ++ g₁ :: g₂ :: suf).filter (fun h => decide (key h.2.2 < key x.2.2))).length :=
      (hperm.filter _).length_eq
    omega

theorem swap_in_chain {ops : α → α → Finset α} {goal : α}
    (pre : List (α × α × α)) (g₁ g₂ : α × α × α) (suf : List (α × α × α)) {s : Finset α}
    (h : liveChain ops goal (pre ++ g₁ :: g₂ :: suf) s)
    (h1 : g₂.1 ≠ g₁.2.2) (h2 : g₂.2.1 ≠ g₁.2.2) :
    liveChain ops goal (pre ++ g₂ :: g₁ :: suf) s ∨ build ops goal (pre.length + suf.length + 1) s := by
  induction pre generalizing s with
  | nil =>
    simpa using swap_two h h1 h2
  | cons g pre ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨ha, hb, hab, hz, hout, rest, hs, tail⟩
    rcases ih tail with hswap | hshort
    · exact Or.inl ⟨ha, hb, hab, hz, hout, rest, hs, hswap⟩
    · right
      have hlen : ((a, b, z) :: pre).length + suf.length + 1 = (pre.length + suf.length + 1) + 1 := by
        simp; omega
      rw [hlen]
      refine Or.inr ⟨a, ha, b, hb, hab, z, hz, build_mono ?_ hshort⟩
      intro u hu
      rw [hs]
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Finset.mem_insert_self u _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))

omit [DecidableEq α] in
theorem find_violation (key : α → ℕ) (last : ℕ) (gs : List (α × α × α))
    (hstart : ∀ g gs', gs = g :: gs' → key g.1 = last ∨ key g.2.1 = last ∨ last ≤ key g.2.2) :
    chainOrd key last gs ∨
    ∃ pre g₁ g₂ suf, gs = pre ++ g₁ :: g₂ :: suf ∧
      key g₂.1 ≠ key g₁.2.2 ∧ key g₂.2.1 ≠ key g₁.2.2 ∧ key g₂.2.2 < key g₁.2.2 := by
  induction gs generalizing last with
  | nil => exact Or.inl trivial
  | cons g₁ rest ih =>
    have hg₁ := hstart g₁ rest rfl
    cases rest with
    | nil => exact Or.inl ⟨hg₁, trivial⟩
    | cons g₂ suf =>
      by_cases hok : key g₂.1 = key g₁.2.2 ∨ key g₂.2.1 = key g₁.2.2 ∨ key g₁.2.2 ≤ key g₂.2.2
      · rcases ih (key g₁.2.2) (fun g gs' heq => by cases heq; exact hok) with hord | ⟨pre, a, b, s', heq, h1, h2, hlt⟩
        · exact Or.inl ⟨hg₁, hord⟩
        · exact Or.inr ⟨g₁ :: pre, a, b, s', by simp [heq], h1, h2, hlt⟩
      · push_neg at hok
        exact Or.inr ⟨[], g₁, g₂, suf, rfl, hok.1, hok.2.1, hok.2.2⟩

theorem normalize_aux {ops : α → α → Finset α} {goal : α} (key : α → ℕ) (av : Finset α) :
    ∀ (m inv : ℕ) (gs : List (α × α × α)) (s : Finset α),
      gs.length ≤ m → invCount key gs ≤ inv → s ⊆ av → liveChain ops goal gs s →
      ∃ gs' : List (α × α × α), gs'.length ≤ m ∧ chainOrd key 0 gs' ∧
        ∃ s' ⊆ av, liveChain ops goal gs' s' := by
  intro m
  induction m with
  | zero =>
    intro inv gs s hlen _ hsub hrun
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil
    exact ⟨[], Nat.le_refl 0, trivial, s, hsub, hrun⟩
  | succ m ihm =>
    intro inv
    induction inv with
    | zero =>
      intro gs s hlen hinv hsub hrun
      rcases find_violation key 0 gs (fun _ _ _ => Or.inr (Or.inr (Nat.zero_le _))) with
        hord | ⟨pre, g₁, g₂, suf, rfl, h1, h2, hlt⟩
      · exact ⟨gs, hlen, hord, s, hsub, hrun⟩
      · exfalso
        have hpos : 0 < invCount key (pre ++ g₁ :: g₂ :: suf) :=
          Nat.lt_of_le_of_lt (Nat.zero_le _) (invCount_swap_lt key pre suf g₁ g₂ hlt)
        omega
    | succ inv ihi =>
      intro gs s hlen hinv hsub hrun
      rcases find_violation key 0 gs (fun _ _ _ => Or.inr (Or.inr (Nat.zero_le _))) with
        hord | ⟨pre, g₁, g₂, suf, rfl, h1, h2, hlt⟩
      · exact ⟨gs, hlen, hord, s, hsub, hrun⟩
      · have hne1 : g₂.1 ≠ g₁.2.2 := fun heq => h1 (congrArg key heq)
        have hne2 : g₂.2.1 ≠ g₁.2.2 := fun heq => h2 (congrArg key heq)
        rcases swap_in_chain pre g₁ g₂ suf hrun hne1 hne2 with hswap | hshort
        · have hlt' := invCount_swap_lt key pre suf g₁ g₂ hlt
          have hlen' : (pre ++ g₂ :: g₁ :: suf).length ≤ m + 1 := by
            simp only [List.length_append, List.length_cons] at hlen ⊢; omega
          exact ihi (pre ++ g₂ :: g₁ :: suf) s hlen' (by omega) hsub hswap
        · have hbm : build ops goal m av := by
            have hle : pre.length + suf.length + 1 ≤ m := by
              simp only [List.length_append, List.length_cons] at hlen; omega
            have hb1 : build ops goal (pre.length + suf.length + 1) av := build_mono hsub hshort
            clear hshort hsub hrun hlen ihm ihi hinv h1 h2 hlt hne1 hne2
            induction hle with
            | refl => exact hb1
            | step _ ih => exact Or.inl ih
          obtain ⟨gs', hlen', s', hsub', hrun'⟩ := compress_chain hbm
          obtain ⟨gs'', hlen'', hord'', s'', hsub'', hrun''⟩ :=
            ihm (invCount key gs') gs' s' hlen' (Nat.le_refl _) hsub' hrun'
          exact ⟨gs'', Nat.le_succ_of_le hlen'', hord'', s'', hsub'', hrun''⟩

theorem normalize_build {ops : α → α → Finset α} {goal : α} (key : α → ℕ)
    {k : ℕ} {av : Finset α} (h : build ops goal k av) :
    ∃ gs : List (α × α × α), gs.length ≤ k ∧ chainOrd key 0 gs ∧
      ∃ s ⊆ av, liveChain ops goal gs s := by
  obtain ⟨gs, hlen, s, hsub, hrun⟩ := compress_chain h
  exact normalize_aux key av k (invCount key gs) gs s hlen (Nat.le_refl _) hsub hrun

theorem chain_score {ops : α → α → Finset α} {goal : α} (val : α → Nat)
    (sub : ∀ a b, ∀ z ∈ ops a b, val z ≤ val a + val b)
    {gs : List (α × α × α)} {s : Finset α}
    (h : liveChain ops goal gs s) (hc : s.card = gs.length + 1) :
    val goal ≤ s.sum val := by
  induction gs generalizing s with
  | nil =>
    change s = {goal} at h
    simp [h]
  | cons g gs ih =>
    rcases g with ⟨a, b, z⟩
    rcases h with ⟨_, _, _, hgate, hout, rest, rfl, tail⟩
    have hz : z ∉ rest := fun hm => hout (by simp [hm])
    have hnext := chain_card tail
    rw [Finset.card_insert_of_notMem hz] at hnext
    simp only [List.length_cons] at hc
    have ha₀ := Finset.card_insert_le a (insert b rest)
    have hb₀ := Finset.card_insert_le b rest
    have ha : a ∉ insert b rest := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at hc
      omega
    have hb : b ∉ rest := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at ha₀
      rw [Finset.insert_eq_of_mem hm] at hc
      omega
    have ih' := ih tail (by rw [Finset.card_insert_of_notMem hz]; omega)
    rw [Finset.sum_insert hz] at ih'
    rw [Finset.sum_insert ha, Finset.sum_insert hb]
    have hz' := sub a b z hgate
    omega

theorem sum_list_score (val : α → Nat) {ws : List α} (hn : ws.Nodup) :
    ws.toFinset.sum val = (ws.map val).sum := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    obtain ⟨hw, hws⟩ := List.nodup_cons.mp hn
    simp [Finset.sum_insert, hw, ih hws]

end Live

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y].filter (fun z => z != 0 && z != BitVec.allOnes 128)

def sep (x : W) : BitVec 64 := ((x >>> 64) &&& ~~~x).setWidth 64

def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [(0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz.1 with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (64 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (64 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 64, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 128 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {gs : List (W × W × W)} {ws : List W} (h : liveChain basicOps goal gs ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := chain_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 128 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 128, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 128 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · by_cases h0 : x &&& y = 0
      · exact .inl h0
      · by_cases h1 : x &&& y = BitVec.allOnes 128
        · exact .inr (.inl h1)
        · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by
            simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons,
              List.not_mem_nil, or_false, Bool.and_eq_true, bne_iff_ne]
            exact ⟨by simp, h0, h1⟩⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · by_cases h0 : x ||| y = 0
      · exact .inl h0
      · by_cases h1 : x ||| y = BitVec.allOnes 128
        · exact .inr (.inl h1)
        · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by
            simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons,
              List.not_mem_nil, or_false, Bool.and_eq_true, bne_iff_ne]
            exact ⟨by simp, h0, h1⟩⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 128) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra last : ℕ) (next : ℕ → ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    if w == a || w == b || r.elem w || (a.toNat != last && b.toNat != last && w.toNat < last) then false
    else
      let v := sep w ||| base
      let wn := w.toNat
      ((v == -1) && next extra wn (w :: r)) ||
      ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) wn (w :: a :: r)) ||
                         ((v ||| sep b == -1) && next (extra - 1) wn (w :: b :: r)))) ||
      ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) wn (w :: a :: b :: r))

def value6 (a b c d e f : Bool) : Nat :=
  let x := b.toNat+c.toNat
  let y := (!e).toNat+(!f).toNat
  if a then (if d then y else max x (max y (x+y-1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

structure ScorePoints where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat

def wireScore (q : ScorePoints) (w : W) : Nat :=
  let x := w.toNat
  value6 (x.testBit q.a) (x.testBit q.b) (x.testBit q.c)
    (x.testBit q.d) (x.testBit q.e) (x.testBit q.f)

theorem score_ops (q : ScorePoints) (a b : W) (z : W) (hz : z ∈ basicOps a b) :
    wireScore q z ≤ wireScore q a + wireScore q b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hz.1 with rfl | rfl
  · simpa only [wireScore, BitVec.toNat_and, Nat.testBit_and] using value6_and
      (a.toNat.testBit q.a) (a.toNat.testBit q.b) (a.toNat.testBit q.c)
      (a.toNat.testBit q.d) (a.toNat.testBit q.e) (a.toNat.testBit q.f)
      (b.toNat.testBit q.a) (b.toNat.testBit q.b) (b.toNat.testBit q.c)
      (b.toNat.testBit q.d) (b.toNat.testBit q.e) (b.toNat.testBit q.f)
  · simpa only [wireScore, BitVec.toNat_or, Nat.testBit_or] using value6_or
      (a.toNat.testBit q.a) (a.toNat.testBit q.b) (a.toNat.testBit q.c)
      (a.toNat.testBit q.d) (a.toNat.testBit q.e) (a.toNat.testBit q.f)
      (b.toNat.testBit q.a) (b.toNat.testBit q.b) (b.toNat.testBit q.c)
      (b.toNat.testBit q.d) (b.toNat.testBit q.e) (b.toNat.testBit q.f)

def enoughScore (q : ScorePoints) : List W → Nat → Bool
  | [], need => need == 0
  | w :: ws, need =>
    let v := wireScore q w
    if need ≤ v then true else enoughScore q ws (need - v)

theorem enoughScore_of_sum (q : ScorePoints) (ws : List W) (need : Nat)
    (h : need ≤ (ws.map (wireScore q)).sum) : enoughScore q ws need = true := by
  induction ws generalizing need with
  | nil => simp at h; simp [enoughScore, h]
  | cons w ws ih =>
    simp only [List.map_cons, List.sum_cons] at h
    dsimp only [enoughScore]
    split
    · rfl
    · apply ih; omega

def scorePool : List ScorePoints :=
  [⟨64, 69, 114, 3, 0, 1⟩,
   ⟨79, 89, 94, 2, 0, 1⟩,
   ⟨104, 84, 99, 1, 2, 3⟩,
   ⟨74, 64, 89, 1, 0, 2⟩,
   ⟨114, 64, 109, 0, 1, 3⟩,
   ⟨89, 74, 79, 0, 1, 2⟩]

theorem pool_score : ∀ q ∈ scorePool, wireScore q goal = 3 := by
  intro q hq
  simp only [scorePool, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def scoreGuard (extra : Nat) (ws : List W) : Bool :=
  extra != 0 || scorePool.all (fun q => enoughScore q ws 3)

theorem scoreGuard_ok {n extra : Nat} {ws : List W} {gs : List (W × W × W)}
    (hn : ws.Nodup) (hlen : gs.length ≤ n) (room : extra + ws.length = n + 1)
    (h : liveChain basicOps goal gs ws.toFinset) : scoreGuard extra ws = true := by
  by_cases he : extra = 0
  · subst extra
    simp only [scoreGuard, ne_eq, bne_self_eq_false, Bool.false_or, List.all_eq_true]
    intro q hq
    apply enoughScore_of_sum
    have hcard := chain_card h
    rw [List.toFinset_card_of_nodup hn] at hcard
    have exactCard : ws.toFinset.card = gs.length + 1 := by
      rw [List.toFinset_card_of_nodup hn]
      omega
    have hsum := chain_score (wireScore q) (score_ops q) h exactCard
    rw [sum_list_score _ hn, pool_score q hq] at hsum
    exact hsum
  · simp [scoreGuard, he]

def optimized : ℕ → ℕ → ℕ → List W → Bool
  | 0, _, _, ws => ws == [goal]
  | 1, _, _, [a] => a == goal
  | 1, _, _, [a, b] => (a &&& b == goal) || (a ||| b == goal)
  | 1, _, _, _ => false
  | 2, _, _, [a] => a == goal
  | 2, _, _, [a, b] => a == goal || b == goal || (a &&& b == goal) || (a ||| b == goal)
  | 2, _, _, [a, b, c] =>
    (a &&& b &&& c == goal) || (a ||| b ||| c == goal) ||
    ((a &&& b) ||| c == goal) || ((a ||| b) &&& c == goal) ||
    ((a &&& c) ||| b == goal) || ((a ||| c) &&& b == goal) ||
    ((b &&& c) ||| a == goal) || ((b ||| c) &&& a == goal)
  | 2, _, _, _ => false
  | k + 3, extra, last, ws => scoreGuard extra ws && (ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra last (optimized (k + 2)) a b r))

theorem dispatch_complete {k extra last : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hna : z ≠ a) (hnb : z ≠ b) (hnr : z ∉ r)
    (hord : a.toNat = last ∨ b.toNat = last ∨ last ≤ z.toNat)
    (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) z.toNat (z :: kept) = true) :
    dispatch extra last next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  have hordb : (a.toNat != last && b.toNat != last && decide (z.toNat < last)) = false := by
    rcases hord with h | h | h
    · simp [h]
    · simp [h]
    · have : ¬ (z.toNat < last) := by omega
      simp [this]
  have hcond : (z == a || z == b || r.elem z || (a.toNat != last && b.toNat != last && decide (z.toNat < last))) = false := by
    simp [hna, hnb, hnr, hordb]
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem chain_one_pair {a b : W} {gs : List (W × W × W)}
    (h : liveChain basicOps goal gs {a, b}) (hab : a ≠ b) (hlen : gs.length ≤ 1) :
    goal ∈ basicOps a b := by
  cases gs with
  | nil =>
    change ({a, b} : Finset W) = {goal} at h
    have hc := congrArg Finset.card h
    rw [Finset.card_pair hab, Finset.card_singleton] at hc
    omega
  | cons g gs' =>
    cases gs' with
    | cons => simp at hlen
    | nil =>
      rcases g with ⟨x, y, z⟩
      rcases h with ⟨hx, hy, hxy, hz, hout, rest, hs, tail⟩
      change insert z rest = {goal} at tail
      have hzg : z = goal := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_self z rest)
      have hxy_ab : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨rfl, rfl⟩
        · exact absurd rfl hxy
      rcases hxy_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hzg ▸ hz
      · rw [ops_swap]; exact hzg ▸ hz

theorem optimized_one {ws : List W} {extra last : ℕ} {gs : List (W × W × W)}
    (hn : ws.Nodup) (hlen : gs.length ≤ 1) (h : liveChain basicOps goal gs ws.toFinset) :
    optimized 1 extra last ws = true := by
  have hc := chain_card h
  rw [List.toFinset_card_of_nodup hn] at hc
  match ws, hn, hc, h with
  | [], _, _, h =>
    cases gs with
    | nil => change ∅ = {goal} at h; simp at h
    | cons g _ => rcases g with ⟨a, _, _⟩; exact absurd h.1 (by simp)
  | [a], hn, _, h =>
    cases gs with
    | nil =>
      have : a = goal := by
        have hm : a ∈ ({goal} : Finset W) := h ▸ Finset.mem_singleton_self a
        exact Finset.mem_singleton.mp hm
      simp [optimized, this]
    | cons g _ =>
      rcases g with ⟨x, y, _⟩
      rcases h with ⟨hx, hy, hxy, _⟩
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  | [a, b], hn, _, h =>
    have hab : a ≠ b := (List.nodup_cons.mp hn).1 ∘ List.mem_singleton.mpr
    have hset : ([a, b] : List W).toFinset = {a, b} := by simp
    rw [hset] at h
    have hzg := chain_one_pair h hab hlen
    simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hzg
    simp only [optimized, Bool.or_eq_true, beq_iff_eq]
    exact hzg.1.imp Eq.symm Eq.symm
  | _ :: _ :: _ :: _, _, hc, _ => simp at hc; omega

theorem abs_ops {a b z : W} (hz : z ∈ basicOps a b) (w : W) (hw : w ∈ basicOps z a ∨ w ∈ basicOps z b) :
    w = a ∨ w = b ∨ w = (a &&& b) ∨ w = (a ||| b) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz hw
  rcases hz.1 with rfl | rfl <;> rcases hw with (⟨rfl | rfl, _⟩) | (⟨rfl | rfl, _⟩)
  · right; right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; right; right; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; left; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)
  · right; right; right; ext i hi; simp; try (cases a[i] <;> cases b[i] <;> simp)

theorem optimized_two {ws : List W} {extra last : ℕ} {gs : List (W × W × W)}
    (hn : ws.Nodup) (hlen : gs.length ≤ 2) (h : liveChain basicOps goal gs ws.toFinset) :
    optimized 2 extra last ws = true := by
  have hc := chain_card h
  rw [List.toFinset_card_of_nodup hn] at hc
  match ws, hn, hc, h with
  | [], _, _, h =>
    cases gs with
    | nil => change ∅ = {goal} at h; simp at h
    | cons g _ => rcases g with ⟨a, _, _⟩; exact absurd h.1 (by simp)
  | [a], hn, _, h =>
    cases gs with
    | nil =>
      have : a = goal := Finset.mem_singleton.mp (h ▸ Finset.mem_singleton_self a)
      simp [optimized, this]
    | cons g _ =>
      rcases g with ⟨x, y, _⟩
      rcases h with ⟨hx, hy, hxy, _⟩
      simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
  | [a, b], hn, _, h =>
    have hab : a ≠ b := (List.nodup_cons.mp hn).1 ∘ List.mem_singleton.mpr
    have hset : ([a, b] : List W).toFinset = {a, b} := by simp
    rw [hset] at h
    cases gs with
    | nil =>
      change ({a, b} : Finset W) = {goal} at h
      have hcard := congrArg Finset.card h
      rw [Finset.card_pair hab, Finset.card_singleton] at hcard
      omega
    | cons g gs' =>
      rcases g with ⟨x, y, z⟩
      rcases h with ⟨hx, hy, hxy, hz, hout, rest, hs, tail⟩
      have hxy_ab : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact .inl ⟨rfl, rfl⟩
        · exact .inr ⟨rfl, rfl⟩
        · exact absurd rfl hxy
      have hz_ab : z ∈ basicOps a b := by
        rcases hxy_ab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hz
        · rw [ops_swap]; exact hz
      cases gs' with
      | nil =>
        change insert z rest = {goal} at tail
        have hzg : z = goal := Finset.mem_singleton.mp (tail ▸ Finset.mem_insert_self z rest)
        have hmem : goal ∈ basicOps a b := hzg ▸ hz_ab
        simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [optimized, Bool.or_eq_true, beq_iff_eq]
        rcases hmem.1 with h1 | h2
        · left; right; exact h1.symm
        · right; exact h2.symm
      | cons g2 gs'' =>
        cases gs'' with
        | cons => simp at hlen
        | nil =>
          have hsub : rest ⊆ {a, b} := by
            intro u hu; rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
          have hcard2 := chain_card tail
          have hzrest : z ∉ rest := fun hm => hout (hsub hm)
          rw [Finset.card_insert_of_notMem hzrest] at hcard2
          simp only [List.length_singleton] at hcard2
          have hrest1 : rest.card = 1 := by
            by_cases he : rest = ∅
            · subst he
              rcases g2 with ⟨u, v, _⟩
              rcases tail with ⟨hu, hv, huv, _⟩
              simp at hu hv
              exact absurd (hu.trans hv.symm) huv
            · have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he); omega
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hrest1
          rw [hw] at tail hsub
          have hw_ab : w = a ∨ w = b := by
            have := hsub (Finset.mem_singleton_self w); simpa using this
          have hzw : z ≠ w := fun heq => hout (heq ▸ hsub (Finset.mem_singleton_self w))
          have hzg := chain_one_pair (by simpa [insert_empty_eq] using tail) hzw (by simp)
          have hres := abs_ops hz_ab goal (hw_ab.elim (fun h => .inl (h ▸ hzg)) (fun h => .inr (h ▸ hzg)))
          simp only [optimized, Bool.or_eq_true, beq_iff_eq]
          rcases hres with h1 | h2 | h3 | h4
          · left; left; left; exact h1.symm
          · left; left; right; exact h2.symm
          · left; right; exact h3.symm
          · right; exact h4.symm
  | [a, b, c], hn, _, h =>
    have hnd1 := List.nodup_cons.mp hn
    have hnd2 := List.nodup_cons.mp hnd1.2
    have hab : a ≠ b := fun heq => hnd1.1 (by simp [heq])
    have hac : a ≠ c := fun heq => hnd1.1 (by simp [heq])
    have hbc : b ≠ c := fun heq => hnd2.1 (by simp [heq])
    have hlen2 : gs.length = 2 := by
      have hc' := chain_card h
      rw [List.toFinset_card_of_nodup hn] at hc'
      simp at hc'; omega
    match gs, hlen2, h with
    | [(x, y, z), g2], _, h =>
      rcases h with ⟨hx, hy, hxy, hz, hout, rest, hs, tail⟩
      have hcard2 := chain_card tail
      have hzrest : z ∉ rest := fun hm => hout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
      rw [Finset.card_insert_of_notMem hzrest] at hcard2
      simp only [List.length_singleton] at hcard2
      have hset3 : ([a, b, c] : List W).toFinset = {a, b, c} := by simp
      rw [hset3] at hs hx hy hout
      have hcard3 : ({a, b, c} : Finset W).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
      have hrest1 : rest.card = 1 := by
        have h1 := Finset.card_insert_le x (insert y rest)
        have h2 := Finset.card_insert_le y rest
        rw [← hs, hcard3] at h1
        omega
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hrest1
      rw [hw] at hs tail
      have hzw : z ≠ w := fun heq => hout (hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (heq ▸ Finset.mem_singleton_self w)))
      have hzg := chain_one_pair (by simpa [insert_empty_eq] using tail) hzw (by simp)
      have htri : (z ∈ basicOps a b ∧ w = c) ∨ (z ∈ basicOps a c ∧ w = b) ∨ (z ∈ basicOps b c ∧ w = a) := by
        have hwx : w ≠ x := by
          intro heq; subst heq
          have : (insert w (insert y ({w} : Finset W))).card ≤ 2 := by
            rw [Finset.insert_comm, show insert w ({w} : Finset W) = {w} by simp]
            exact Finset.card_insert_le y {w}
          rw [← hs, hcard3] at this; omega
        have hwy : w ≠ y := by
          intro heq; subst heq
          have : (insert x (insert w ({w} : Finset W))).card ≤ 2 := by
            rw [show insert w ({w} : Finset W) = {w} by simp]
            exact Finset.card_insert_le x {w}
          rw [← hs, hcard3] at this; omega
        have hwm : w ∈ ({a, b, c} : Finset W) := hs ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hwm
        rcases hwm with rfl | rfl | rfl
        · rcases hx with rfl | rfl | rfl
          · exact absurd rfl hwx
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hwy
            · exact absurd rfl hxy
            · exact .inr (.inr ⟨hz, rfl⟩)
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hwy
            · exact .inr (.inr ⟨ops_swap _ _ ▸ hz, rfl⟩)
            · exact absurd rfl hxy
        · rcases hx with rfl | rfl | rfl
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hxy
            · exact absurd rfl hwy
            · exact .inr (.inl ⟨hz, rfl⟩)
          · exact absurd rfl hwx
          · rcases hy with rfl | rfl | rfl
            · exact .inr (.inl ⟨ops_swap _ _ ▸ hz, rfl⟩)
            · exact absurd rfl hwy
            · exact absurd rfl hxy
        · rcases hx with rfl | rfl | rfl
          · rcases hy with rfl | rfl | rfl
            · exact absurd rfl hxy
            · exact .inl ⟨hz, rfl⟩
            · exact absurd rfl hwy
          · rcases hy with rfl | rfl | rfl
            · exact .inl ⟨ops_swap _ _ ▸ hz, rfl⟩
            · exact absurd rfl hxy
            · exact absurd rfl hwy
          · exact absurd rfl hwx
      simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at htri hzg
      simp only [optimized, Bool.or_eq_true, beq_iff_eq]
      rcases htri with ⟨⟨hz1 | hz1, _⟩, rfl⟩ | ⟨⟨hz1 | hz1, _⟩, rfl⟩ | ⟨⟨hz1 | hz1, _⟩, rfl⟩ <;>
        (subst hz1; rcases hzg.1 with hzg | hzg)
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl hzg.symm))))))
      · exact .inl (.inl (.inl (.inl (.inl (.inr hzg.symm)))))
      · exact .inl (.inl (.inl (.inl (.inr hzg.symm))))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr hzg.symm))))))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (by rw [hzg]; ac_rfl)))))))
      · exact .inl (.inl (.inl (.inr hzg.symm)))
      · exact .inl (.inl (.inr hzg.symm))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr (by rw [hzg]; ac_rfl)))))))
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (by rw [hzg]; ac_rfl)))))))
      · exact .inl (.inr hzg.symm)
      · exact .inr hzg.symm
      · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr (by rw [hzg]; ac_rfl)))))))
  | _ :: _ :: _ :: _ :: _, _, hc, _ => simp at hc; omega

theorem optimized_complete (n : ℕ) (ws : List W) (extra last : ℕ) (gs : List (W × W × W))
    (hn : ws.Nodup) (hlen : gs.length ≤ n)
    (room : extra + ws.length = n + 1)
    (hord : chainOrd BitVec.toNat last gs)
    (h : liveChain basicOps goal gs ws.toFinset) :
    optimized n extra last ws = true := by
  induction n generalizing ws extra last gs with
  | zero =>
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hnil
    simp [optimized, singleton_list hn h]
  | succ k ih =>
    cases k with
    | zero => exact optimized_one hn hlen h
    | succ m =>
      cases m with
      | zero => exact optimized_two hn hlen h
      | succ p =>
        have pass := scoreGuard_ok hn hlen room h
        cases gs with
        | nil =>
          simp only [optimized, pass, Bool.true_and]
          simp [singleton_list hn h]
        | cons g gs' =>
          rcases g with ⟨a, b, z⟩
          rcases h with ⟨ha, hb, hab, hz, hout, needed, hs, tail⟩
          rcases hord with ⟨hg_ord, hgs_ord⟩
          obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
          have go {a b : W} (perm : ws.Perm (a :: b :: r))
              (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b)
              (hord' : a.toNat = last ∨ b.toNat = last ∨ last ≤ z.toNat) :
              dispatch extra last (optimized (p + 2)) a b r = true := by
            obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
            have hzws : z ∉ a :: b :: r := fun hu => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hu))
            have hna : z ≠ a := fun h => hzws (h ▸ List.mem_cons_self)
            have hnb : z ≠ b := fun h => hzws (List.mem_cons_of_mem _ (h ▸ List.mem_cons_self))
            have hnr : z ∉ r := fun h => hzws (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
            have hznew : z ∉ kept := by
              intro hu
              apply hout
              rw [hset]
              exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
            have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
            have hl : liveChain basicOps goal gs' (z :: kept).toFinset := by
              simpa [hfin] using tail
            have hlen' : gs'.length ≤ p + 2 := by simp at hlen; omega
            have hc := chain_card hl
            rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
            have len := perm.length_eq
            simp only [List.length_cons] at len
            apply dispatch_complete (k := p + 2) (extra := extra) (last := last) (optimized (p + 2))
              hop hna hnb hnr hord' hk (by omega) (by omega) (cuts_full hl)
            apply ih _ _ _ gs' hnd hlen' _ hgs_ord hl
            simp; omega
          simp only [optimized, pass, Bool.true_and, Bool.or_eq_true, List.any_eq_true]
          right
          rcases hm with direct | swap
          · exact ⟨(a, b, r), direct, go hp hs hz hg_ord⟩
          · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
              (ops_swap a b ▸ hz) (by rcases hg_ord with h | h | h; exact .inr (.inl h); exact .inl h; exact .inr (.inr h))⟩

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (14302 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) := [(0, 1), (0, 2), (0, 3), (1, 0), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (3, 0), (3, 1)]

def negL : List (Fin 4 × Fin 4) := [(0, 0), (1, 1), (2, 3), (3, 2), (3, 3)]

def samp (k : Fin 128) : Fin 4 × Fin 4 :=
  if k.val < 64 then negL.getD (k.val % 5) (0, 0) else posL.getD (((k.val - 64) / 5) % 11) (0, 0)

theorem input_rows : ∀ k : Fin 128,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 128, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 128) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem inputs_nodup : inputs.Nodup := by decide +kernel

def tab0 : List (ℕ × ℕ × List W) :=
  [(1, (0xff8000003fffffff * 0x10000000000000000 + 0x318c6318c6318c63), [(0xff8000003fffffff * 0x10000000000000000 + 0x318c6318c6318c63), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab1 : List (ℕ × ℕ × List W) :=
  [(1, (0xff801fffc0007fff * 0x10000000000000000 + 0x5294a5294a5294a5), [(0xff801fffc0007fff * 0x10000000000000000 + 0x5294a5294a5294a5), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab2 : List (ℕ × ℕ × List W) :=
  [(1, (0xffffe00000007fff * 0x10000000000000000 + 0x9ce739ce739ce739), [(0xffffe00000007fff * 0x10000000000000000 + 0x9ce739ce739ce739), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab3 : List (ℕ × ℕ × List W) :=
  [(1, 0x1084210842108421, [0x1084210842108421, (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab4 : List (ℕ × ℕ × List W) :=
  [(3, (0xff83e007c00fffff * 0x10000000000000000 + 0x1084210842108421), [(0xff83e007c00fffff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab5 : List (ℕ × ℕ × List W) :=
  [(2, (0xff83e007c00fffff * 0x10000000000000000 + 0x1084210842108421), [(0xff83e007c00fffff * 0x10000000000000000 + 0x1084210842108421), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab6 : List (ℕ × ℕ × List W) :=
  [(2, (0xff83e007c00fffff * 0x10000000000000000 + 0x1084210842108421), [(0xff83e007c00fffff * 0x10000000000000000 + 0x1084210842108421), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab7 : List (ℕ × ℕ × List W) :=
  [(1, (0xff83e007c00fffff * 0x10000000000000000 + 0x1084210842108421), [(0xff83e007c00fffff * 0x10000000000000000 + 0x1084210842108421), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab8 : List (ℕ × ℕ × List W) :=
  [(1, (0xf8000000000001f * 0x10000000000000000 + 0x0), [(0xf8000000000001f * 0x10000000000000000 + 0x0), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab9 : List (ℕ × ℕ × List W) :=
  [(1, (0xfffc00f800007fff * 0x10000000000000000 + 0x318c6318c6318c63), [(0xfffc00f800007fff * 0x10000000000000000 + 0x318c6318c6318c63), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab10 : List (ℕ × ℕ × List W) :=
  [(1, (0xf0000000000003e0 * 0x10000000000000000 + 0x0), [(0xf0000000000003e0 * 0x10000000000000000 + 0x0), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab11 : List (ℕ × ℕ × List W) :=
  [(1, (0xff801f0001f07fff * 0x10000000000000000 + 0x94a5294a5294a529), [(0xff801f0001f07fff * 0x10000000000000000 + 0x94a5294a5294a529), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab12 : List (ℕ × ℕ × List W) :=
  [(1, 0x7c000000000000000000, [0x7c000000000000000000, (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab13 : List (ℕ × ℕ × List W) :=
  [(1, (0xff8000003e007fff * 0x10000000000000000 + 0x5ad6b5ad6b5ad6b5), [(0xff8000003e007fff * 0x10000000000000000 + 0x5ad6b5ad6b5ad6b5), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab14 : List (ℕ × ℕ × List W) :=
  [(1, (0x1fffffff8000 * 0x10000000000000000 + 0x6318c6318c6318c6), [(0x1fffffff8000 * 0x10000000000000000 + 0x6318c6318c6318c6), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab15 : List (ℕ × ℕ × List W) :=
  [(1, (0x7fe0003fff8000 * 0x10000000000000000 + 0xad6b5ad6b5ad6b5a), [(0x7fe0003fff8000 * 0x10000000000000000 + 0xad6b5ad6b5ad6b5a), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab16 : List (ℕ × ℕ × List W) :=
  [(1, (0xf8000 * 0x10000000000000000 + 0x0), [(0xf8000 * 0x10000000000000000 + 0x0), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab17 : List (ℕ × ℕ × List W) :=
  [(1, (0x3e007ffff8000 * 0x10000000000000000 + 0x318c6318c6318c63), [(0x3e007ffff8000 * 0x10000000000000000 + 0x318c6318c6318c63), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab18 : List (ℕ × ℕ × List W) :=
  [(1, 0x2108421084210842, [0x2108421084210842, (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab19 : List (ℕ × ℕ × List W) :=
  [(3, (0xffc00f83fff801f * 0x10000000000000000 + 0x2108421084210842), [(0xffc00f83fff801f * 0x10000000000000000 + 0x2108421084210842), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab20 : List (ℕ × ℕ × List W) :=
  [(2, (0xffc00f83fff801f * 0x10000000000000000 + 0x2108421084210842), [(0xffc00f83fff801f * 0x10000000000000000 + 0x2108421084210842), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab21 : List (ℕ × ℕ × List W) :=
  [(2, (0xffc00f83fff801f * 0x10000000000000000 + 0x2108421084210842), [(0xffc00f83fff801f * 0x10000000000000000 + 0x2108421084210842), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab22 : List (ℕ × ℕ × List W) :=
  [(1, (0xffc00f83fff801f * 0x10000000000000000 + 0x2108421084210842), [(0xffc00f83fff801f * 0x10000000000000000 + 0x2108421084210842), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab23 : List (ℕ × ℕ × List W) :=
  [(1, (0x1f00000 * 0x10000000000000000 + 0x0), [(0x1f00000 * 0x10000000000000000 + 0x0), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab24 : List (ℕ × ℕ × List W) :=
  [(1, (0xf0001f003fff83e0 * 0x10000000000000000 + 0xa5294a5294a5294a), [(0xf0001f003fff83e0 * 0x10000000000000000 + 0xa5294a5294a5294a), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab25 : List (ℕ × ℕ × List W) :=
  [(1, (0x3e000000 * 0x10000000000000000 + 0x0), [(0x3e000000 * 0x10000000000000000 + 0x0), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab26 : List (ℕ × ℕ × List W) :=
  [(1, (0x3ffffc00 * 0x10000000000000000 + 0x6b5ad6b5ad6b5ad6), [(0x3ffffc00 * 0x10000000000000000 + 0x6b5ad6b5ad6b5ad6), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab27 : List (ℕ × ℕ × List W) :=
  [(2, (0x7fffffc0000000 * 0x10000000000000000 + 0xce739ce739ce739c), [(0x7fffffc0000000 * 0x10000000000000000 + 0xce739ce739ce739c), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab28 : List (ℕ × ℕ × List W) :=
  [(1, (0x7fffffc0000000 * 0x10000000000000000 + 0xce739ce739ce739c), [(0x7fffffc0000000 * 0x10000000000000000 + 0xce739ce739ce739c), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab29 : List (ℕ × ℕ × List W) :=
  [(1, (0x7c0000000 * 0x10000000000000000 + 0x0), [(0x7c0000000 * 0x10000000000000000 + 0x0), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab30 : List (ℕ × ℕ × List W) :=
  [(1, (0x3ffffc00f8000 * 0x10000000000000000 + 0x5294a5294a5294a5), [(0x3ffffc00f8000 * 0x10000000000000000 + 0x5294a5294a5294a5), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab31 : List (ℕ × ℕ × List W) :=
  [(1, (0xf800000000 * 0x10000000000000000 + 0x0), [(0xf800000000 * 0x10000000000000000 + 0x0), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab32 : List (ℕ × ℕ × List W) :=
  [(1, (0xffc1fffc000001f * 0x10000000000000000 + 0x6318c6318c6318c6), [(0xffc1fffc000001f * 0x10000000000000000 + 0x6318c6318c6318c6), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab33 : List (ℕ × ℕ × List W) :=
  [(1, (0x1f0000000000 * 0x10000000000000000 + 0x0), [(0x1f0000000000 * 0x10000000000000000 + 0x0), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab34 : List (ℕ × ℕ × List W) :=
  [(1, (0xf0001fffc1f003e0 * 0x10000000000000000 + 0xc6318c6318c6318c), [(0xf0001fffc1f003e0 * 0x10000000000000000 + 0xc6318c6318c6318c), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab35 : List (ℕ × ℕ × List W) :=
  [(1, 0x4210842108421084, [0x4210842108421084, (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab36 : List (ℕ × ℕ × List W) :=
  [(3, (0x1ffffe007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), [(0x1ffffe007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab37 : List (ℕ × ℕ × List W) :=
  [(2, (0x1ffffe007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), [(0x1ffffe007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab38 : List (ℕ × ℕ × List W) :=
  [(2, (0x1ffffe007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), [(0x1ffffe007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab39 : List (ℕ × ℕ × List W) :=
  [(1, (0x1ffffe007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), [(0x1ffffe007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab40 : List (ℕ × ℕ × List W) :=
  [(1, (0x3e00000000000 * 0x10000000000000000 + 0x0), [(0x3e00000000000 * 0x10000000000000000 + 0x0), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab41 : List (ℕ × ℕ × List W) :=
  [(1, (0x7fe007c00f8000 * 0x10000000000000000 + 0x9ce739ce739ce739), [(0x7fe007c00f8000 * 0x10000000000000000 + 0x9ce739ce739ce739), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab42 : List (ℕ × ℕ × List W) :=
  [(1, (0x7c000000000000 * 0x10000000000000000 + 0x0), [(0x7c000000000000 * 0x10000000000000000 + 0x0), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab43 : List (ℕ × ℕ × List W) :=
  [(1, (0xfffe0f80000001f * 0x10000000000000000 + 0xad6b5ad6b5ad6b5a), [(0xfffe0f80000001f * 0x10000000000000000 + 0xad6b5ad6b5ad6b5a), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab44 : List (ℕ × ℕ × List W) :=
  [(1, 0x8421084210842108, [0x8421084210842108, (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab45 : List (ℕ × ℕ × List W) :=
  [(3, (0xf07fff0001f003e0 * 0x10000000000000000 + 0x8c6318c6318c6318), [(0xf07fff0001f003e0 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab46 : List (ℕ × ℕ × List W) :=
  [(2, (0xf07fff0001f003e0 * 0x10000000000000000 + 0x8c6318c6318c6318), [(0xf07fff0001f003e0 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab47 : List (ℕ × ℕ × List W) :=
  [(2, (0xf07fff0001f003e0 * 0x10000000000000000 + 0x8c6318c6318c6318), [(0xf07fff0001f003e0 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab48 : List (ℕ × ℕ × List W) :=
  [(1, (0xf07fff0001f003e0 * 0x10000000000000000 + 0x8c6318c6318c6318), [(0xf07fff0001f003e0 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab49 : List (ℕ × ℕ × List W) :=
  [(1, 0x842108421084210, [0x842108421084210, (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab50 : List (ℕ × ℕ × List W) :=
  [(3, (0x7fe0003e007c00 * 0x10000000000000000 + 0xce739ce739ce739c), [(0x7fe0003e007c00 * 0x10000000000000000 + 0xce739ce739ce739c), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab51 : List (ℕ × ℕ × List W) :=
  [(2, (0x7fe0003e007c00 * 0x10000000000000000 + 0xce739ce739ce739c), [(0x7fe0003e007c00 * 0x10000000000000000 + 0xce739ce739ce739c), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab52 : List (ℕ × ℕ × List W) :=
  [(2, (0x7fe0003e007c00 * 0x10000000000000000 + 0xce739ce739ce739c), [(0x7fe0003e007c00 * 0x10000000000000000 + 0xce739ce739ce739c), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab53 : List (ℕ × ℕ × List W) :=
  [(1, (0x7fe0003e007c00 * 0x10000000000000000 + 0xce739ce739ce739c), [(0x7fe0003e007c00 * 0x10000000000000000 + 0xce739ce739ce739c), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab54 : List (ℕ × ℕ × List W) :=
  [(1, (0xfffe0ffc00f801f * 0x10000000000000000 + 0x318c6318c6318c63), [(0xfffe0ffc00f801f * 0x10000000000000000 + 0x318c6318c6318c63), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab55 : List (ℕ × ℕ × List W) :=
  [(1, (0xf003ff07c1ff83e0 * 0x10000000000000000 + 0x94a5294a5294a529), [(0xf003ff07c1ff83e0 * 0x10000000000000000 + 0x94a5294a5294a529), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab56 : List (ℕ × ℕ × List W) :=
  [(1, (0x3e007fe0ffc00 * 0x10000000000000000 + 0x5ad6b5ad6b5ad6b5), [(0x3e007fe0ffc00 * 0x10000000000000000 + 0x5ad6b5ad6b5ad6b5), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab57 : List (ℕ × ℕ × List W) :=
  [(1, (0xfffc1ff801f003ff * 0x10000000000000000 + 0xa5294a5294a5294a), [(0xfffc1ff801f003ff * 0x10000000000000000 + 0xa5294a5294a5294a), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294)])]

def tab58 : List (ℕ × ℕ × List W) :=
  [(1, (0xffc00f83e007c1f * 0x10000000000000000 + 0x6b5ad6b5ad6b5ad6), [(0xffc00f83e007c1f * 0x10000000000000000 + 0x6b5ad6b5ad6b5ad6), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108)])]

def tab59 : List (ℕ × ℕ × List W) :=
  [(2, (0xf0001f003ff07fe0 * 0x10000000000000000 + 0xce739ce739ce739c), [(0xf0001f003ff07fe0 * 0x10000000000000000 + 0xce739ce739ce739c), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842)])]

def tab60 : List (ℕ × ℕ × List W) :=
  [(1, (0xf0001f003ff07fe0 * 0x10000000000000000 + 0xce739ce739ce739c), [(0xf0001f003ff07fe0 * 0x10000000000000000 + 0xce739ce739ce739c), (0xf0001f0001f003e0 * 0x10000000000000000 + 0x8421084210842108), (0x3e007c00 * 0x10000000000000000 + 0x4a5294a5294a5294), (0xff80000000007fff * 0x10000000000000000 + 0x1084210842108421), (0x3fff8000 * 0x10000000000000000 + 0x2108421084210842), (0x1fffc0000000 * 0x10000000000000000 + 0x4210842108421084), (0x7fe00000000000 * 0x10000000000000000 + 0x8c6318c6318c6318), (0x3e007c00f8000 * 0x10000000000000000 + 0x1084210842108421), (0xffc00f80000001f * 0x10000000000000000 + 0x2108421084210842)])]

def table : List (ℕ × ℕ × List W) := tab0 ++ tab1 ++ tab2 ++ tab3 ++ tab4 ++ tab5 ++ tab6 ++ tab7 ++ tab8 ++ tab9 ++ tab10 ++ tab11 ++ tab12 ++ tab13 ++ tab14 ++ tab15 ++ tab16 ++ tab17 ++ tab18 ++ tab19 ++ tab20 ++ tab21 ++ tab22 ++ tab23 ++ tab24 ++ tab25 ++ tab26 ++ tab27 ++ tab28 ++ tab29 ++ tab30 ++ tab31 ++ tab32 ++ tab33 ++ tab34 ++ tab35 ++ tab36 ++ tab37 ++ tab38 ++ tab39 ++ tab40 ++ tab41 ++ tab42 ++ tab43 ++ tab44 ++ tab45 ++ tab46 ++ tab47 ++ tab48 ++ tab49 ++ tab50 ++ tab51 ++ tab52 ++ tab53 ++ tab54 ++ tab55 ++ tab56 ++ tab57 ++ tab58 ++ tab59 ++ tab60

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf0 : tab0.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf1 : tab1.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf2 : tab2.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf3 : tab3.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf4 : tab4.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf5 : tab5.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf6 : tab6.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf7 : tab7.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf8 : tab8.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf9 : tab9.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf10 : tab10.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf11 : tab11.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf12 : tab12.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf13 : tab13.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf14 : tab14.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf15 : tab15.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf16 : tab16.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf17 : tab17.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf18 : tab18.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf19 : tab19.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf20 : tab20.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf21 : tab21.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf22 : tab22.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf23 : tab23.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf24 : tab24.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf25 : tab25.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf26 : tab26.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf27 : tab27.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf28 : tab28.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf29 : tab29.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf30 : tab30.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf31 : tab31.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf32 : tab32.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf33 : tab33.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf34 : tab34.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf35 : tab35.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf36 : tab36.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf37 : tab37.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf38 : tab38.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf39 : tab39.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf40 : tab40.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf41 : tab41.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf42 : tab42.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf43 : tab43.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf44 : tab44.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf45 : tab45.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf46 : tab46.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf47 : tab47.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf48 : tab48.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf49 : tab49.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf50 : tab50.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf51 : tab51.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf52 : tab52.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf53 : tab53.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf54 : tab54.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf55 : tab55.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf56 : tab56.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf57 : tab57.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf58 : tab58.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf59 : tab59.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf60 : tab60.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem leaf_all : table.all (fun c => !(optimized 9 c.1 c.2.1 c.2.2)) = true := by
  simp only [table, List.all_append, leaf0, leaf1, leaf2, leaf3, leaf4, leaf5, leaf6, leaf7, leaf8, leaf9, leaf10, leaf11, leaf12, leaf13, leaf14, leaf15, leaf16, leaf17, leaf18, leaf19, leaf20, leaf21, leaf22, leaf23, leaf24, leaf25, leaf26, leaf27, leaf28, leaf29, leaf30, leaf31, leaf32, leaf33, leaf34, leaf35, leaf36, leaf37, leaf38, leaf39, leaf40, leaf41, leaf42, leaf43, leaf44, leaf45, leaf46, leaf47, leaf48, leaf49, leaf50, leaf51, leaf52, leaf53, leaf54, leaf55, leaf56, leaf57, leaf58, leaf59, leaf60, Bool.and_self]

def optT (e last : ℕ) (ws : List W) : Bool := if (e, last, ws) ∈ table then false else optimized 9 e last ws

theorem optT_eq : optT = optimized 9 := by
  funext e last ws
  unfold optT
  split_ifs with h
  · have hc := List.all_eq_true.mp leaf_all _ h
    dsimp only at hc
    revert hc
    cases optimized 9 e last ws <;> simp
  · rfl

def optRoot (e last : ℕ) (ws : List W) : Bool :=
  scoreGuard e ws && (ws == [goal] || (pairs ws).any (fun (a, b, r) => dispatch e last optT a b r))

theorem optRoot_eq : optRoot = optimized 10 := by
  funext e last ws
  simp only [optRoot, optT_eq, optimized]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 80000000 in
theorem all_front : inputs.sublists.all
    (fun l => decide (11 < l.length) || (cuts l != -1) || !(optRoot (11 - l.length) 0 l)) = true := by
  decide +kernel

theorem no_build {k : Nat} (hs : k ≤ 10) (hb : build basicOps goal k inputs.toFinset) : False := by
  obtain ⟨gs, hlen, hord, S, hsub, hl⟩ := normalize_build BitVec.toNat hb
  have hlenk : gs.length ≤ 10 := Nat.le_trans hlen hs
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := chain_card hl
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hcuts : cuts l = -1 := cuts_full (hlS ▸ hl)
  have hsearch := optimized_complete 10 l (11 - l.length) 0 gs hnd hlenk (by omega) hord (hlS ▸ hl)
  rw [← optRoot_eq] at hsearch
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp all_front l hmem
  have h4 : decide (11 < l.length) = false := by simp; omega
  have h5 : (cuts l != -1) = false := by simp [hcuts]
  rw [h4, h5, hsearch] at hrow
  exact Bool.noConfusion hrow


abbrev Supply (av : Finset W) (x : W) : Prop := x=0 ∨ x=BitVec.allOnes 128 ∨ x∈av
theorem classifyPair {av : Finset W} {a b z : W} (ha : Supply av a) (hb : Supply av b)
    (h : z = a &&& b ∨ z = a ||| b) : Supply av z ∨ ∃ i∈av, ∃ j∈av, i≠j ∧ z∈basicOps i j := by
  have hrep : represents av [a,b] := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ha
    · obtain rfl := List.mem_singleton.mp hu
      exact hb
  have hn : possible [a,b] z := by
    rcases h with rfl | rfl <;> simp [possible]
  rcases classify hrep hn with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr h))
  · exact Or.inr h
end PEqualNP.Outside.L_meta_25467.Donor4

namespace PEqualNP.Outside.L_meta_25467.Punctured
open WordEngine Rep9102 Rep9102.Orbit Rep9102.Project

theorem mappedRun {m t : Nat} (f : Nat → Donor4.W) (ft : f t=Donor4.goal)
    (andF : ∀ a b, f (a &&& b) = f a &&& f b) (orF : ∀ a b, f (a ||| b) = f a ||| f b)
    (k : Nat) {S : Finset Nat} (run : LiveWord m t k 0 S) (av : Finset Donor4.W)
    (hs : ∀ w∈S, Donor4.Supply av (f w)) : Donor4.build Donor4.basicOps Donor4.goal k av := by
  induction k generalizing S av with
  | zero =>
    obtain ⟨_,rfl,_⟩ := run
    have h := hs t (Finset.mem_singleton_self _)
    rw [ft] at h
    rcases h with h | h | h
    · exact ((by decide : Donor4.goal ≠ 0) h).elim
    · exact ((by decide : Donor4.goal ≠ BitVec.allOnes 128) h).elim
    · exact h
  | succ k ih =>
    rcases run with ⟨u,A,x,impossible,_⟩ | ⟨U,x,y,op,rfl,_,_,_,_,tail⟩
    · omega
    have old (w) (hw : w∈U) : Donor4.Supply av (f w) := hs w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
    have form : f (binWord op x y)=f x &&& f y ∨ f (binWord op x y)=f x ||| f y := by
      cases op
      · exact Or.inl (andF x y)
      · exact Or.inr (orF x y)
    rcases Donor4.classifyPair (hs x (Finset.mem_insert_self _ _))
        (hs y (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))) form with simple | ⟨a,ha,b,hb,ne,q⟩
    · apply Or.inl (ih tail av ?_)
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact simple
      · exact old _ hw
    · apply Or.inr ⟨a,ha,b,hb,ne,_,q,ih tail _ ?_⟩
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
      · exact (old _ hw).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))

def reword (ls : List Nat) (w : Nat) : Nat :=
  match ls with
  | [] => 0
  | j::js => Nat.bit (w.testBit j) (reword js w)
theorem rewordGates (ls : List Nat) (x y : Nat) :
    reword ls (x &&& y) = reword ls x &&& reword ls y ∧
    reword ls (x ||| y) = reword ls x ||| reword ls y := by
  induction ls with
  | nil => simp [reword]
  | cons j js ih => exact ⟨by simp [reword,Nat.land_bit,ih.1], by simp [reword,Nat.lor_bit,ih.2]⟩
def sam (ls : List Nat) (w : Nat) : Donor4.W := BitVec.ofNat 128 (reword ls w)
def patch2 : List Nat := [18,24,6,0,1,18,24,6,0,1,18,24,6,0,1,18,24,6,0,1,18,24,6,0,1,18,24,6,0,1,18,24,6,0,1,18,24,6,0,1,18,24,6,0,1,18,24,6,0,1,18,24,6,0,1,18,24,6,0,1,18,24,6,0,19,19,19,19,19,15,15,15,15,15,16,16,16,16,16,23,23,23,23,23,20,20,20,20,20,21,21,21,21,21,8,8,8,8,8,9,9,9,9,9,5,5,5,5,5,3,3,3,3,3,4,4,4,4,4,19,19,19,19,19,15,15,15,15]
def patch3 : List Nat := [12,24,6,0,1,12,24,6,0,1,12,24,6,0,1,12,24,6,0,1,12,24,6,0,1,12,24,6,0,1,12,24,6,0,1,12,24,6,0,1,12,24,6,0,1,12,24,6,0,1,12,24,6,0,1,12,24,6,0,1,12,24,6,0,14,14,14,14,14,10,10,10,10,10,11,11,11,11,11,22,22,22,22,22,20,20,20,20,20,21,21,21,21,21,7,7,7,7,7,9,9,9,9,9,5,5,5,5,5,2,2,2,2,2,4,4,4,4,4,14,14,14,14,14,10,10,10,10]
def patch4 : List Nat := [12,18,6,0,1,12,18,6,0,1,12,18,6,0,1,12,18,6,0,1,12,18,6,0,1,12,18,6,0,1,12,18,6,0,1,12,18,6,0,1,12,18,6,0,1,12,18,6,0,1,12,18,6,0,1,12,18,6,0,1,12,18,6,0,13,13,13,13,13,10,10,10,10,10,11,11,11,11,11,17,17,17,17,17,15,15,15,15,15,16,16,16,16,16,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,2,2,2,2,2,3,3,3,3,3,13,13,13,13,13,10,10,10,10]
def slotsU (i : Fin 3) := (![patch2,patch3,patch4] : Fin 3 → List Nat) i
def sqMask (i : Fin 3) : Nat := (![0x1bd837b,0x1705ef7,0x7bdef] : Fin 3 → Nat) i

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nearFour (i : Fin 3) : AOLower (sqMask i) (Subfloor.rawOn (sqMask i)) (THere &&& sqMask i) 11 := by
  have facts := (by decide +kernel : ∀ i : Fin 3,
    let m := sqMask i
    let f := sam (slotsU i)
    (Subfloor.rawOn m).all (fun w => w &&& m == w) = true ∧
    properWord m (THere &&& m) ∧ f (THere &&& m) = Donor4.goal ∧
    (Subfloor.rawOn m).all (fun w => decide ((f w=0) ∨ f w=BitVec.allOnes 128 ∨ f w∈Donor4.inputs.toFinset)) = true) i
  obtain ⟨masked,proper,ft,cover⟩ := facts
  intro vs built hit
  obtain ⟨k,S,cap,run,sub⟩ := extractAO (stockMaskedOfCheck masked) built hit proper
  by_contra small
  apply Donor4.no_build (k:=k) (by omega)
  apply mappedRun (sam (slotsU i)) ft _ _ k run
  · intro x y; simpa [sam,(rewordGates (slotsU i) x y).1]
  · intro x y; simpa [sam,(rewordGates (slotsU i) x y).2]
  · intro w hw; exact of_decide_eq_true (List.all_eq_true.mp cover w (sub w hw))

def dd (i : Fin 5) := Subfloor.dropMask i
def ll (row : Bool) (i : Fin 5) := if row then Subfloor.omitRowMask i else Subfloor.omitColMask i

theorem fiveSquares (i : Fin 5) : AOLower (dd i) (Subfloor.rawOn (dd i)) (THere &&& dd i) 11 := by
  fin_cases i
  · exact (by decide +kernel : THere &&& dd 0 = Rep9102.T &&& dd 0) ▸ Subfloor.allFour 0
  · exact (by decide +kernel : THere &&& dd 1 = Rep9102.T &&& dd 1) ▸ Subfloor.allFour 1
  · exact nearFour 0
  · exact nearFour 1
  · exact nearFour 2
def removes (m s : Word) : Prop :=
  ∃ p n : Fin 25, (THere &&& m).testBit p.val = true ∧ (THere &&& m).testBit n.val = false ∧
    ∀ w ∈ Subfloor.rawOn m, w.testBit p.val = true → w.testBit n.val = false → maskedFlat s w
instance (m s) : Decidable (removes m s) := by unfold removes; infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem allLines (row : Bool) (i : Fin 5) :
    AOLower (ll row i) (Subfloor.rawOn (ll row i)) (THere &&& ll row i) 12 := by
  let m := ll row i
  let s := dd i
  have properties := (by decide +kernel : ∀ r : Bool, ∀ v : Fin 5,
    let m := ll r v
    let s := dd v
    (Subfloor.rawOn m).all (fun w => w &&& m == w) = true ∧
    properWord m (THere &&& m) ∧ ¬maskedFlat s (THere &&& m) ∧
    (THere &&& m) &&& s = THere &&& s ∧
    (Subfloor.rawOn m).all (fun w => availableB s (Subfloor.rawOn s) (w &&& s)) = true ∧ removes m s) row i
  obtain ⟨masked,proper,nonflat,restrict,sources,p,n,pos,neg,sep⟩ := properties
  intro vs built hit
  obtain ⟨k,S,budget,live,sub⟩ := extractAO (stockMaskedOfCheck masked) built hit proper
  obtain ⟨w,hw,yes,no⟩ := liveDirected live pos neg
  have flat : w ∈ flatSet s S := Finset.mem_filter.mpr ⟨hw,sep w (sub w hw) yes no⟩
  have posCard := Finset.card_pos.mpr ⟨w,flat⟩
  have supply : ∀ x ∈ projectedStock s S, AvailableWord s ([] ++ Subfloor.rawOn s) x := by
    intro x hx
    simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image] at hx
    rcases hx with rfl | rfl | ⟨a,ha,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact suppliesOfCheck sources a (sub a ha)
  have cut := Project.cut live nonflat (show AOBuild s (Subfloor.rawOn s) [] from trivial) supply (restrict ▸ fiveSquares i)
  simp only [List.length_nil,Nat.zero_add] at cut
  change 11 + (flatSet s S).card ≤ k at cut
  omega
def floorM (i : Fin 15) : Word :=
  let v := Fin.ofNat 5 (i.val/3)
  if i.val%3=0 then ll true v else if i.val%3=1 then ll false v else dd v
def floorN (i : Fin 15) := if i.val%3=2 then 11 else 12
theorem maskFloor (i : Fin 15) :
   AOLower (floorM i) (Subfloor.rawOn (floorM i)) (THere &&& floorM i) (floorN i) := by
  unfold floorM floorN
  dsimp only
  split <;> rename_i h
  · rw [if_neg (by omega : i.val%3 ≠ 2)]
    exact allLines true _
  · split <;> rename_i h'
    · rw [if_neg (by omega : i.val%3 ≠ 2)]
      exact allLines false _
    · rw [if_pos (by omega : i.val%3 = 2)]
      exact fiveSquares _

def pCut (id : Fin 15) (extras : List Word) (s : RowState) : Bool :=
  let m := floorM id
  match cheapPrep m (Subfloor.rawOn m) (extras ++ s.2.1.map (· &&& m)) with
  | none => false
  | some vs => decide (vs.length + s.1 < floorN id + flatCount m s.2.1)
theorem pCutOpen (id : Fin 15) (extras : List Word) (s : RowState)
    (h : MonoViable (fullMask 25) THere s) : pCut id extras s = false := by
  obtain ⟨nd,k,cap,live⟩ := h
  let m := floorM id
  have nonflat := (by decide +kernel : ∀ q : Fin 15, ¬maskedFlat (floorM q) THere) id
  unfold pCut
  cases he : cheapPrep (floorM id) (Subfloor.rawOn (floorM id)) (extras ++ s.2.1.map (· &&& floorM id)) with
  | none => rfl
  | some vs =>
    obtain ⟨built,covered⟩ := cheapPrep_spec he
    have supply : ∀ x ∈ projectedStock m s.2.1.toFinset, AvailableWord m (vs ++ Subfloor.rawOn m) x := by
      intro x hx
      simp only [projectedStock,visibleWords,Finset.mem_insert,Finset.mem_image,List.mem_toFinset] at hx
      rcases hx with rfl | rfl | ⟨v,hv,rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact covered _ (List.mem_append_right _ (List.mem_map_of_mem hv))
    have bound := Project.cut live nonflat built supply (maskFloor id)
    have eq := flatCountCard (floorM id) nd
    simp only [decide_eq_false_iff_not,not_lt]
    omega

def nodes : Array (Nat × List Word) := #[(13,[31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856]),(12,[992,31744,1015808,1082431,2164802,4329604,8659208,17318416,32505856]),(11,[992,1015808,1082431,2164802,4357252,8659208,17318416,32505856]),(10,[992,1082431,2164802,4357252,9412872,17318416,32505856]),(9,[992,1082431,2164802,4357252,9412872,33047056]),(10,[992,1015808,1082431,2164802,4357252,8659208,33047056]),(11,[992,31744,1082431,2164802,4329604,9412872,17318416,32505856]),(10,[992,31744,1082431,2164802,4329604,9412872,33047056]),(11,[992,31744,1015808,1082431,2164802,4329604,8659208,33047056]),(12,[992,31744,1015808,1082401,2164831,4329604,8659208,17318416,32505856]),(11,[992,1015808,1082401,2164831,4357252,8659208,17318416,32505856]),(10,[992,1082401,2164831,4357252,9412872,17318416,32505856]),(9,[992,1082401,2164831,4357252,9412872,33047056]),(10,[992,1015808,1082401,2164831,4357252,8659208,33047056]),(11,[992,31744,1082401,2164831,4329604,9412872,17318416,32505856]),(10,[992,31744,1082401,2164831,4329604,9412872,33047056]),(11,[992,31744,1015808,1082401,2164831,4329604,8659208,33047056]),(12,[31,31744,1015808,1082401,2165730,4329604,8659208,17318416,32505856]),(11,[31,1015808,1082401,2165730,4357252,8659208,17318416,32505856]),(10,[31,1082401,2165730,4357252,9412872,17318416,32505856]),(9,[31,1082401,2165730,4357252,9412872,33047056]),(10,[31,1015808,1082401,2165730,4357252,8659208,33047056]),(11,[31,31744,1082401,2165730,4329604,9412872,17318416,32505856]),(10,[31,31744,1082401,2165730,4329604,9412872,33047056]),(11,[31,31744,1015808,1082401,2165730,4329604,8659208,33047056]),(12,[31,992,1015808,1082401,2164802,4357252,8659208,17318416,32505856]),(11,[31,992,1082401,2164802,4357252,9412872,17318416,32505856]),(10,[31,992,1082401,2164802,4357252,9412872,33047056]),(11,[31,992,1015808,1082401,2164802,4357252,8659208,33047056]),(12,[31,992,31744,1082401,2164802,4329604,9412872,17318416,32505856]),(11,[31,992,31744,1082401,2164802,4329604,9412872,33047056]),(12,[31,992,31744,1015808,1082401,2164802,4329604,8659208,33047056])]
def states (i:Nat) : Option RowState := (nodes[i]?).map (fun n => (n.1,n.2,[]))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
def rules : Array (Nat × List Nat) := #[(17,[]),(3,[]),(0,[]),(3,[1082399]),(1,[]),(2,[]),(6,[1081407]),(4,[1082429]),(3,[1082399,4357124]),(1,[4356228]),(2,[4356224]),(4,[1082429,4355204]),(7,[1082427]),(8,[1081403]),(9,[1049663,4226180]),(1,[4356228,9380104]),(2,[4356224,9380096]),(3,[1082399,4357124,9412616]),(0,[4357248,9412864]),(4,[1082429,4355204,9347336]),(8,[1081403,9273608]),(6,[1081407,9404680]),(7,[1082427,9281800]),(11,[1049655,4217988]),(10,[1082423,4349060]),(12,[33855,162948,1024264]),(1,[4356228,9380104,31998480]),(2,[4356224,9380096,31998464]),(3,[1082399,4357124,9412616,33046544]),(0,[4357248,9412864,33047040]),(4,[1082429,4355204,9347336,30949904]),(8,[1081403,9273608,28836368]),(11,[1049655,4217988,24134160]),(16,[4]),(13,[1082415,4340868,8888584]),(16,[3]),(0,[4357248]),(12,[33855,162948]),(3,[1082399,4357124,33046544]),(1,[4356228,31998480]),(2,[4356224,31998464]),(4,[1082429,4355204,30949904]),(7,[1082427,28852752]),(8,[1081403,28836368]),(9,[1049663,4226180,32522768]),(10,[1082423,4349060,24658448]),(0,[4357248,33047040]),(6,[1081407,33030672]),(16,[5]),(13,[1082415,4340868]),(16,[2]),(9,[1049663]),(3,[1082399,9412616]),(1,[9380104]),(2,[9380096]),(4,[1082429,9347336]),(0,[9412864]),(11,[1049655]),(10,[1082423]),(12,[33855,1024264]),(3,[1082399,9412616,33046544]),(1,[9380104,31998480]),(2,[9380096,31998464]),(4,[1082429,9347336,30949904]),(6,[1081407,9404680,33030672]),(7,[1082427,9281800,28852752]),(0,[9412864,33047040]),(11,[1049655,24134160]),(16,[7]),(13,[1082415,8888584]),(16,[6]),(12,[33855]),(3,[1082399,33046544]),(1,[31998480]),(2,[31998464]),(4,[1082429,30949904]),(9,[1049663,32522768]),(10,[1082423,24658448]),(0,[33047040]),(16,[8]),(13,[1082415]),(16,[1]),(3,[2164767]),(1,[2164830]),(6,[2162783]),(4,[]),(3,[2164767,4357124]),(1,[2164830,4356228]),(4,[4355204]),(9,[2099295,4226180]),(7,[2164827]),(8,[2162779]),(1,[2164830,4356228,9380104]),(3,[2164767,4357124,9412616]),(8,[2162779,9273608]),(11,[2099287,4217988]),(13,[2164815,4340868,8888584]),(4,[4355204,9347336]),(12,[67679,162948,1024264]),(6,[2162783,9404680]),(7,[2164827,9281800]),(10,[2164823,4349060]),(1,[2164830,4356228,9380104,31998480]),(3,[2164767,4357124,9412616,33046544]),(8,[2162779,9273608,28836368]),(11,[2099287,4217988,24134160]),(14,[67663,146564,499976]),(16,[12]),(16,[11]),(13,[2164815,4340868]),(12,[67679,162948]),(3,[2164767,4357124,33046544]),(1,[2164830,4356228,31998480]),(4,[4355204,30949904]),(9,[2099295,4226180,32522768]),(7,[2164827,28852752]),(8,[2162779,28836368]),(10,[2164823,4349060,24658448]),(14,[67663,146564]),(6,[2162783,33030672]),(16,[13]),(16,[10]),(9,[2099295]),(3,[2164767,9412616]),(1,[2164830,9380104]),(4,[9347336]),(11,[2099287]),(13,[2164815,8888584]),(12,[67679,1024264]),(10,[2164823]),(3,[2164767,9412616,33046544]),(1,[2164830,9380104,31998480]),(4,[9347336,30949904]),(6,[2162783,9404680,33030672]),(7,[2164827,9281800,28852752]),(11,[2099287,24134160]),(14,[67663,499976]),(16,[15]),(16,[14]),(13,[2164815]),(12,[67679]),(3,[2164767,33046544]),(1,[2164830,31998480]),(4,[30949904]),(9,[2099295,32522768]),(10,[2164823,24658448]),(14,[67663]),(16,[16]),(16,[9]),(0,[2165728]),(1,[2165698]),(5,[]),(6,[2163682]),(0,[2165728,4357248]),(1,[2165698,4356228]),(5,[4355076]),(7,[2165602]),(8,[2163554]),(9,[2100194,4226180]),(0,[2165728,4357248,9412864]),(1,[2165698,4356228,9380104]),(5,[4355076,9347080]),(3,[4357124,9412616]),(8,[2163554,9273608]),(6,[2163682,9404680]),(7,[2165602,9281800]),(11,[2099938,4217988]),(10,[2165474,4349060]),(12,[68578,162948,1024264]),(0,[2165728,4357248,9412864,33047040]),(1,[2165698,4356228,9380104,31998480]),(5,[4355076,9347080,30949392]),(8,[2163554,9273608,28836368]),(11,[2099938,4217988,24134160]),(16,[20]),(13,[2165218,4340868,8888584]),(16,[19]),(3,[4357124]),(12,[68578,162948]),(0,[2165728,4357248,33047040]),(1,[2165698,4356228,31998480]),(5,[4355076,30949392]),(7,[2165602,28852752]),(8,[2163554,28836368]),(9,[2100194,4226180,32522768]),(10,[2165474,4349060,24658448]),(3,[4357124,33046544]),(6,[2163682,33030672]),(16,[21]),(13,[2165218,4340868]),(16,[18]),(9,[2100194]),(0,[2165728,9412864]),(1,[2165698,9380104]),(5,[9347080]),(3,[9412616]),(11,[2099938]),(10,[2165474]),(12,[68578,1024264]),(0,[2165728,9412864,33047040]),(1,[2165698,9380104,31998480]),(5,[9347080,30949392]),(6,[2163682,9404680,33030672]),(7,[2165602,9281800,28852752]),(3,[9412616,33046544]),(11,[2099938,24134160]),(16,[23]),(13,[2165218,8888584]),(16,[22]),(12,[68578]),(0,[2165728,33047040]),(1,[2165698,31998480]),(5,[30949392]),(9,[2100194,32522768]),(10,[2165474,24658448]),(3,[33046544]),(16,[24]),(13,[2165218]),(16,[17]),(6,[]),(7,[]),(8,[]),(9,[4226180]),(8,[9273608]),(6,[9404680]),(7,[9281800]),(11,[4217988]),(10,[4349060]),(12,[162948,1024264]),(3,[4357124,9412616,33046544]),(4,[4355204,9347336,30949904]),(8,[9273608,28836368]),(11,[4217988,24134160]),(16,[27]),(13,[4340868,8888584]),(16,[26]),(12,[162948]),(7,[28852752]),(8,[28836368]),(9,[4226180,32522768]),(10,[4349060,24658448]),(6,[33030672]),(16,[28]),(13,[4340868]),(16,[25]),(9,[]),(11,[]),(10,[]),(12,[1024264]),(6,[9404680,33030672]),(7,[9281800,28852752]),(11,[24134160]),(16,[30]),(13,[8888584]),(16,[29]),(12,[]),(9,[32522768]),(10,[24658448]),(16,[31]),(13,[])]
def pg0 : Array Nat := #[0x0,0x0,0x80100000,0x8000000000000,0x0,0x8000000000800,0x80400851,0x8550089400800,0x80000000,0x8000000000800,0x80000000,0x8000000000800,0x0,0x800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400,0x40000000,0x10000000001000,0x4da0040000000,0x4000000000455,0x40000000,0x4000000000400,0x40000000,0x400,0x40000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x36c000000000000,0x100000000,0x154000000001000,0x1540000000,0x36cdc36cf436c00,0x36c0000000,0x36c000000036c00,0x36c0000000,0x36c000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10000000000000,0x100000000,0x154000000015400,0x3700000000,0x3d4000000037000,0x3d4f73d4fe,0x3d400000003d400,0x0,0x3d400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10000000000000,0x1000,0x100000000,0x10000000000000,0x0,0x10000000001000,0x100000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x154000000000000,0x0,0x15400,0x1540000000,0x154000000015400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3700000000,0x370000000000000,0x3700000000,0x37000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3dc00000003dc00,0x3dc0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3fcff40d023fc00]
def pg1 : Array Nat := #[0x0,0x0,0xc0000000,0xc000000000000,0x100000000,0xc000000001400,0xc0000c00,0xc000000000c00,0xc0000000,0xc000000000c00,0xc0000000,0xc000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10000000001800,0x140000000,0x1c000000001c00,0x18320180000000,0x1800000000180c,0x180000000,0x18000000001800,0x0,0x1800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x14000000001000,0x1c0000000,0x30000000001c00,0x300000000,0xcc3a0cc460cc00,0xcc0000000,0xcc00,0xcc0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000000000000,0x140001400,0x14000000000800,0x80000000,0x8000000001400,0x140000000,0x14000000001000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1c00,0x1c0000000,0x1c000000000000,0x1c0000000,0x1c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x30000000000000,0x0,0x30000000003000,0x300000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xe80000000,0xe800000000e800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1404f11c0000000,0x11c47]
def pg2 : Array Nat := #[0x0,0x0,0x200000000,0x28000000002400,0x20000200000000,0x20000000002000,0x200000000,0x20000000002000,0x200000000,0x2000,0x200000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x240000000,0x2c000000002800,0x2c0000000,0x34000000003000,0x38230380000000,0x38000000003818,0x380000000,0x38000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x28000280009000,0x280000000,0x90000000002800,0x280000000,0x28000000009000,0x240000000,0x2800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2c000000000000,0x2c0000000,0x2c000000000000,0x0,0x2c000000002c00,0x2c0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x180000000,0x18000000003400,0x340000000,0x34000000003000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x60000000000000,0x600000000,0x6000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x94000000000000,0x94250c430]
def pg3 : Array Nat := #[0x0,0x3c000000000000,0x400000000,0x44000440004400,0x440000000,0x44000000004400,0x440000000,0x44000000004400,0x0,0x4400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40000480000000,0x40000000004000,0x400000000,0x40000000004000,0x480000000,0x3c000000004000,0x400000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4c000000004c00,0x4c0000000,0x4c00,0x4c0000000,0x4c000000004c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x50000000000000,0x500000000,0x50000000005400,0x580000000,0x5000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x380000000,0x60000000005c00,0x5c0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x64190882106400]
def pg4 : Array Nat := #[0x0,0x68000000000000,0x6c0000000,0x70000700007000,0x700000000,0x70000000007000,0x700000000,0x70000000007000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x6c000740000000,0x6c000000006c00,0x6c0000000,0x6c000000006c00,0x6c0000000,0x6c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x78000000007800,0x780000000,0x78000000007800,0x780000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7c000000000000,0x7c0000000,0x7c000000007c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800000000,0x8000]
def pg5 : Array Nat := #[0x0,0x0,0x980000000,0xa0000000009c00,0x98000980000000,0x98000000009800,0x980000000,0x98000000009800,0x980000000,0x9800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9c0000000,0xa400000000a000,0xa40000000,0xac00000000a800,0xb0210b00000000,0xb000000000b02d,0xb00000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa0000a0000b800,0xa00000000,0xb800000000a000,0xa00000000,0xa000000000a000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa4000000000000,0xa40000000,0xa4000000000000,0xa40000000,0xa400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xbc0000000,0xac00000000ac00,0xac0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xb400000000b400]
def pg6 : Array Nat := #[0x0,0x0,0xd00000000,0xd800000000d400,0xd0000d00000000,0xd000000000d000,0xd00000000,0xd000000000d000,0xd00000000,0xd000,0xd00000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xd40000000,0xdc00000000d800,0xdc0000000,0x54160542305400,0x540000000,0x54000000005400,0x540000000,0x54000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xd8000d8000e000,0xe00000000,0xd800000000d800,0xd80000000,0xd800000000e000,0xd40000000,0xd800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xdc0000000,0xdc00000000dc00,0x0,0xdc00000000dc00,0xdc0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x580000000,0x5800,0x580000000,0x58000000005800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xe400000000cc00,0xe80000000,0xe400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xec000000000000,0xec3b11444]
def pg7 : Array Nat := #[0x0,0x0,0xf00000000,0xf800000000f400,0xf0000f00000000,0xf000000000f000,0xf00000000,0xf000000000f000,0xf00000000,0xf000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf40000000,0xfc00000000f800,0xfc0000000,0x100411002110000,0x1000000000,0x100000000010000,0x1000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf8000f80010800,0x1080000000,0xf800000000f800,0xf80000000,0xf800000000f800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xfc0000000,0xfc00000000fc00,0xfc0000000,0xfc00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1040000000,0x104000000010400,0x1040000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10c000000010c00]
def pg8 : Array Nat := #[0x0,0x0,0x1200000000,0x120000000000000,0x1240000000,0x120000000012800,0x1200012000,0x120000000012000,0x1200000000,0x120000000012000,0x1200000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x12400000000bc00,0x1280000000,0x12c000000012c00,0xbc300bc0000000,0xbc00000000bc2a,0xbc0000000,0xbc00000000bc00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x128000000012400,0x12c0000000,0xa8000000012c00,0xa80000000,0x1304d1304413000,0x1300000000,0x13000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x138000000000000,0x1280012800,0x128000000013800,0x1380000000,0x128000000012800,0x1280000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x12c00,0x12c0000000,0x12c000000012c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa8000000000000,0xa80000000,0xa800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x134000000000000,0x1340000000]
def pg9 : Array Nat := #[0x0,0x0,0x1480000000,0x148000000000000,0x14c0000000,0x148000000014c00,0x1480014800,0x148000000014800,0x1480000000,0x148000000014800,0x1480000000,0x148000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x14c000000015000,0x14c0000000,0x150000000015400,0x150791500000000,0x15000000001505a,0x1500000000,0x150000000015000,0x0,0x15000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x14c000000014c00,0x1540000000,0x16800000001e800,0x1680000000,0x1e8811e88a1e800,0x1e80000000,0x1e800,0x1e80000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000000000000,0x14c0014c00,0x14c000000000000,0x0,0x14c00,0x14c0000000,0x14c000000014c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000000,0x8000000016800,0x2040000000,0x22c000000000800,0x1540000000,0x23000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x168000000000000,0x0,0x168000000016800,0x1680000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2040000000,0x204000000020400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x22c932300000000,0x2308c]
def pg10 : Array Nat := #[0x0,0x0,0x1580000000,0x15c000000015c00,0x158001580000000,0x158000000015800,0x1580000000,0x158000000015800,0x1580000000,0x15800,0x1580000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x15c0000000,0x160000000015c00,0x1640000000,0x16c000000016800,0x1646c1640000000,0x164000000016465,0x1640000000,0x164000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x15c0015c0009000,0x15c0000000,0x15c00,0x15c0000000,0x15c000000000000,0x15c0000000,0x15c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x16c000000000000,0x16c0000000,0x194000000009000,0x900000000,0x16000000001b400,0x1b80000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1500000000,0x150000000016c00,0x16c0000000,0x16c000000016800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x194000000000000,0x1940000000,0x19400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1b8000000000000,0x1b86e1b478]
def pg11 : Array Nat := #[0x0,0x170000000000000,0x1700000000,0x174001740017400,0x1740000000,0x174000000017400,0x1740000000,0x174000000017400,0x0,0x17400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x170000480000000,0x170000000017000,0x1700000000,0x170000000017000,0x0,0x170000000017000,0x1700000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x178000000017800,0x17c0000000,0x48000000017c00,0x1800000000,0x188000000018400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x178000000000000,0x1780000000,0x178000000018c00,0x1900000000,0x17800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1640000000,0x194000000017c00,0x17c0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x188621806b18800]
def pg12 : Array Nat := #[0x0,0x198000000000000,0x1980000000,0x19c0019c0019c00,0x19c0000000,0x19c000000019c00,0x19c0000000,0x19c000000019c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x198000740000000,0x198000000019800,0x1980000000,0x198000000019800,0x1980000000,0x19800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1a000000001a000,0x1a40000000,0x1a800000001a400,0x1a80000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1a0000000000000,0x1a00000000,0x1a000000001a000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1a40000000,0x1a400]
def pg13 : Array Nat := #[0x0,0x0,0x1bc0000000,0x1c000000001c000,0x1bc001bc0000000,0x1bc00000001bc00,0x1bc0000000,0x1bc00000001bc00,0x1bc0000000,0x1bc00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1c00000000,0x1c400000001c000,0x1c80000000,0x1d000000001cc00,0x1c86b1c80000000,0x1c800000001c875,0x1c80000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1c0001c0000b800,0x1c00000000,0x1c000,0x1c00000000,0x1c000000001c000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1d0000000000000,0x1d00000000,0x1d400000000b800,0x1d80000000,0x1d800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1dc0000000,0x1d000000001d000,0x1d00000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1d400000001d400]
def pg14 : Array Nat := #[0x0,0x0,0x1ec0000000,0x1f000000001f000,0x1ec001ec0000000,0x1ec00000001ec00,0x1ec0000000,0x1ec00000001ec00,0x1ec0000000,0x1ec00,0x1ec0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1f00000000,0x1f400000001f000,0x18c0000000,0x18c6418c6c18c00,0x18c0000000,0x18c000000018c00,0x18c0000000,0x18c000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1f0001f0000e000,0x0,0x1f000000001f000,0x1f00000000,0x1f0000000000000,0x1f00000000,0x1f000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xe0000000000000,0x1900000000,0x1f800000001f800,0xe00000000,0x1f400000001fc00,0x2000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1900000000,0x19000,0x1900000000,0x190000000019000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1f800000001e800,0x2040000000,0x1f800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200000000000000,0x200801fc89]
def pg15 : Array Nat := #[0x0,0x0,0x2080000000,0x20c000000020c00,0x208002080000000,0x208000000020800,0x2080000000,0x208000000020800,0x2080000000,0x20800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c0000000,0x210000000020c00,0x2140000000,0x214862146b21400,0x2140000000,0x214000000021400,0x2140000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c0020c0010800,0x0,0x20c000000020c00,0x20c0000000,0x20c000000020c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x108000000000000,0x2180000000,0x21c000000021c00,0x2200000000,0x22000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2180000000,0x218000000021800,0x2180000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x21c000000021c00]
def pg16 : Array Nat := #[0x0,0x0,0x2340000000,0x234000000000000,0x2380000000,0x234000000023800,0x2340023400,0x234000000023400,0x2340000000,0x234000000023400,0x2340000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x23800000001dc00,0x2380000000,0x1dc000000023c00,0x1dc781dc0000000,0x1dc00000001dc73,0x1dc0000000,0x1dc00000001dc00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x238000000023800,0x23c0000000,0x1cc000000024000,0x1cc0000000,0x240912408924000,0x2400000000,0x24000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x138000000000000,0x2380023800,0x238000000000000,0x0,0x238000000023800,0x2380000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1380000000,0x13800000001cc00,0x2440000000,0x248000000024800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1cc000000000000,0x1cc0000000,0x1cc00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x244000000000000,0x2440000000]
def pg17 : Array Nat := #[0x0,0x0,0x2540000000,0x254000000000000,0x2540000000,0x254000000025496,0x2549700000,0x254000000025400,0x2540000000,0x254000000025400,0x2540000000,0x254000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x258000000026000,0x2580000000,0x25c000000015400,0x260be2600000000,0x26000000002609c,0x2600000000,0x260000000026000,0x0,0x26000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x258000000025800,0x1540000000,0x270000000025c00,0x2700000000,0x2fcc52fcd02fc00,0x2fc0000000,0x2fc00,0x2fc0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x258000000000000,0x2580000000,0x258000000000000,0x0,0x25800,0x2580000000,0x258000000025800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40000000,0x4000000025c00,0x25c0000000,0x25c000000000400,0x1540000000,0x25c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x270000000000000,0x0,0x270000000027000,0x2700000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3140000000,0x314000000031400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x364d83440000000,0x344d1]
def pg18 : Array Nat := #[0x0,0x0,0x2640000000,0x2649a0000026400,0x2640000000,0x26400000002649b,0x2640000000,0x264000000026400,0x2640000000,0x26400,0x2640000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2680000000,0x160000000026800,0x26c0000000,0x274000000027000,0x278b02780000000,0x2780000000278a7,0x2780000000,0x278000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x268000000026800,0x2680000000,0x26800,0x2680000000,0x268000000000000,0x2680000000,0x26800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x26c000000000000,0x26c0000000,0x26c00000002c400,0x2c40000000,0x160000000026c00,0x26c0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2600000000,0x260000000027400,0x2740000000,0x274000000027000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x29c000000000000,0x29c0000000,0x29c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2c8000000000000,0x2c8b22f4bc]
def pg19 : Array Nat := #[0x0,0x27c000000000000,0x27ca000000,0x27ca10000027c00,0x27c0000000,0x27c000000027c00,0x27c0000000,0x27c000000027c00,0x0,0x27c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2800000000,0x280000000028000,0x2800000000,0x280000000028000,0x0,0x280000000028000,0x2800000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x284000000028400,0x2840000000,0x288000000028400,0x2840000000,0x284000000018400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x28c000000000000,0x28c0000000,0x28c000000029000,0x2940000000,0x28c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2780000000,0x29c000000029800,0x2980000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2a0a82bcae2a000]
def pg20 : Array Nat := #[0x0,0x2a4000000000000,0x2a4aa00000,0x2a4ab000002a400,0x2a40000000,0x2a400000002a400,0x2a40000000,0x2a400000002a400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2a80000000,0x2a800000002a800,0x2a80000000,0x2a800000002a800,0x2a80000000,0x2a800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2ac00000002ac00,0x2ac0000000,0x2ac00000002ac00,0x2ac0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2b0000000000000,0x2b00000000,0x2b000000002b000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2b40000000,0x2b400]
def pg21 : Array Nat := #[0x0,0x0,0x2cc0000000,0x2ccb4000002cc00,0x2cc0000000,0x2cc00000002ccb5,0x2cc0000000,0x2cc00000002cc00,0x2cc0000000,0x2cc00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2d00000000,0x1c400000002d000,0x2d40000000,0x2dc00000002d800,0x2e0ae2e00000000,0x2e000000002e0b9,0x2e00000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2d000000002d000,0x2d00000000,0x2d000,0x2d00000000,0x2d000000002d000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2d4000000000000,0x2d40000000,0x2d400000002e800,0x2d40000000,0x2d400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2ec0000000,0x2dc00000002dc00,0x2dc0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2e400000002e400]
def pg22 : Array Nat := #[0x0,0x0,0x3000000000,0x300c10000030000,0x3000000000,0x3000000000300c2,0x3000000000,0x300000000030000,0x3000000000,0x30000,0x3000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3040000000,0x1f4000000030400,0x3080000000,0x290a5290b029000,0x2900000000,0x290000000029000,0x2900000000,0x290000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x304000000030400,0x0,0x304000000030400,0x3040000000,0x304000000000000,0x3040000000,0x30400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x30c000000000000,0x3080000000,0x308000000030800,0x30c0000000,0x1f4000000030800,0x3080000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2940000000,0x29400,0x2940000000,0x294000000029400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x31000000002fc00,0x3140000000,0x31000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x318000000000000,0x318c633cce]
def pg23 : Array Nat := #[0x0,0x0,0x31c0000000,0x31cc80000031c00,0x31c0000000,0x31c000000031cc9,0x31c0000000,0x31c000000031c00,0x31c0000000,0x31c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3200000000,0x210000000032000,0x3240000000,0x328cb328ae32800,0x3280000000,0x328000000032800,0x3280000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x320000000032000,0x0,0x320000000032000,0x3200000000,0x320000000032000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x330000000000000,0x3240000000,0x324000000032400,0x3240000000,0x32400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x32c0000000,0x32c000000032c00,0x32c0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x334000000033400]
def pg24 : Array Nat := #[0x0,0x0,0x3480000000,0x348000000000000,0x3480000000,0x3480000000348d3,0x348d400000,0x348000000034800,0x3480000000,0x348000000034800,0x3480000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x34c00000002ec00,0x34c0000000,0x350000000023c00,0x2ecbc2ec0000000,0x2ec00000002ecb6,0x2ec0000000,0x2ec00000002ec00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x34c000000034c00,0x23c0000000,0x2d8000000035000,0x2d80000000,0x354d6354ce35400,0x3540000000,0x35400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x34c000000000000,0x34c0000000,0x34c000000000000,0x0,0x34c000000034c00,0x34c0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x35c0000000,0x35c000000035000,0x3500000000,0x350000000035000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2d8000000000000,0x2d80000000,0x2d800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x358000000000000,0x3580000000]
def pg25 : Array Nat := #[0x0,0x0,0x90b100000,0x90000000000000,0x90320900000000,0x90000000009009,0x905809079,0x90000000009000,0x900000000,0x90000000009000,0x900000000,0x90000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2400000002c400,0x240000000,0x2c4582c4be2c400,0x2c40000000,0x2c400000002c400,0x2c40000000,0x2c400000002c400,0x0,0x2c400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x24000000002400,0x1600000000,0x370000000016000,0x3740000000,0x378e3378eb37800,0x3780000000,0x37800,0x3780000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x240002400,0x24000000002400,0x0,0x2400,0x240000000,0x24000000002400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1600000000,0x16000,0x1600000000,0x160000000000000,0x1600000000,0x16000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x374000000036c00,0x36c0000000,0x370000000037400,0x3740000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x38c0000000,0x38c000000038c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3ccf23b00000000,0x3b0ec]
def pg26 : Array Nat := #[0x0,0x0,0x48a200000,0x480f0482304800,0x486c0480000000,0x48000000004861,0x480000000,0x48000000004800,0x480000000,0x4800,0x480000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3c0000000,0x288000000003c00,0x28861288b0,0x288000000028800,0x2880000000,0x288000000028800,0x2880000000,0x288000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3c0003c0000000,0x3c0000000,0x3c000000003c00,0x3c0000000,0x3c000000000000,0x3c0000000,0x3c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x184000000000000,0x1840000000,0x184000000018400,0x0,0x184000000018400,0x1840000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x37c0000000,0x380000000037c00,0x37c0000000,0x37c000000038400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x388000000037800,0x38c0000000,0x38800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x390000000000000,0x390e43a8e9]
def pg27 : Array Nat := #[0x0,0x0,0x74e500000,0x741a0742107400,0x746b0740000000,0x740000000074e6,0x740000000,0x74000000007400,0x740000000,0x7400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x680000000,0x394000000006800,0x394e6394ae,0x394000000039400,0x3940000000,0x394000000039400,0x3940000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x68000680000000,0x680000000,0x68000000006800,0x680000000,0x68000000006800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x398000000000000,0x3980000000,0x398000000039800,0x3980000000,0x39800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x39c0000000,0x39c000000039c00,0x39c0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3a000000003a000]
def pg28 : Array Nat := #[0x0,0x0,0xb8ba00000,0xb8000000000000,0xb8300b80000000,0xb800000000b827,0xb8710b878,0xb800000000b800,0xb80000000,0xb800000000b800,0xb80000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9c00000002e800,0x9c0000000,0x2e8712e8bc2e800,0x2e80000000,0x2e800000002e800,0x2e80000000,0x2e800000002e800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9c000000009c00,0x1c40000000,0x3b400000001c400,0x3b80000000,0x3bcf03bce93bc00,0x3bc0000000,0x3bc00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9c0009c00,0x9c000000009c00,0x0,0x9c000000009c00,0x9c0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1c40000000,0x1c400,0x1c40000000,0x1c400000001c400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3b800000003c400,0x3b80000000,0x3b800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3c0000000000000,0x3c00000000]
def pg29 : Array Nat := #[0x0,0x0,0xe0c300000,0xe0000000000000,0xe0460e00000000,0xe000000000e035,0xe07d0e08a,0xe000000000e000,0xe00000000,0xe000000000e000,0xe00000000,0xe0000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xd4000000030c00,0xd40000000,0x30c7d30cd030c00,0x30c0000000,0x30c000000030c00,0x30c0000000,0x30c000000030c00,0x0,0x30c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xd400000000d400,0x1f40000000,0x38000000001f400,0x380e1380eb,0x380000000038000,0x3800000000,0x38000,0x3800000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xd4000d400,0xd4000000000000,0xd40000000,0xd400,0xd40000000,0xd400000000d400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1f400000001f400,0x1f40000000,0x1f4000000000000,0x1f40000000,0x1f400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x384000000038400,0x0,0x384000000038400,0x3840000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3d4000000000000,0x3d80000000,0x3d800000003dc00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3f4fc3e00000000,0x3e0f8]
def pg30 : Array Nat := #[0x0,0x0,0x108cc00000,0x108000000000000,0x108441080000000,0x10800000001083d,0x1088410889,0x108000000010800,0x1080000000,0x108000000010800,0x1080000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf4000000033000,0xf40000000,0x33084330ce33000,0x3300000000,0x330000000033000,0x3300000000,0x330000000033000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf400000000f400,0x2100000000,0x3e4000000021000,0x3e4fa3e4e9,0x3e400000003e400,0x3e40000000,0x3e400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xf4000f400,0xf4000000000000,0xf40000000,0xf400000000f400,0xf40000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x210000000021000,0x2100000000,0x210000000021000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3e800000003e800,0x3e80000000,0x3e800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3ec000000000000,0x3ec0000000]
def pg31 : Array Nat := #[0x0,0x0,0x138d700000,0x138000000000000,0x0,0x138000000013800,0x138491384f,0x1388f1389313800,0x1380000000,0x138000000013800,0x1380000000,0x138000000013800,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x35c00,0x35c0000000,0x124000000012400,0x35cd835c0000000,0x35c000000035c8f,0x35c0000000,0x35c000000035c00,0x35c0000000,0x35c00,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3c4000000000000,0x1240000000,0x23c000000012400,0x23c0000000,0x3c4ed3c4f23c400,0x3c40000000,0x3c400000003c400,0x3c40000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x124000000000000,0x1240000000,0x23c000000023c00,0x3b40000000,0x40000000003b400,0x40101400fc,0x400000000040000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x124000000000000,0x12400,0x1240000000,0x124000000000000,0x1240000000,0x12400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x23c000000000000,0x0,0x23c000000023c00,0x23c0000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3b40000000,0x3b400000003b400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4040000000,0x40400]
def pages := #[pg0,pg1,pg2,pg3,pg4,pg5,pg6,pg7,pg8,pg9,pg10,pg11,pg12,pg13,pg14,pg15,pg16,pg17,pg18,pg19,pg20,pg21,pg22,pg23,pg24,pg25,pg26,pg27,pg28,pg29,pg30,pg31]

def code (i tok : Nat) : Nat × List Nat :=
  let off := ((tok/768)*16+(tok/12)%64)*8 + ((tok/4)%3)*4 + tok%4
  let page := pages[i]?.getD #[]
  let id := ((page[off/6]?.getD 0) >>> ((off%6)*10)) % 1024
  rules[id]?.getD (17,[])
def cutF (i tok : Nat) (s : RowState) : Bool :=
  let r := code i tok
  if r.1<15 then pCut (Fin.ofNat 15 r.1) r.2 s else
    if r.1=15 then Geometry.rectangleReject THere s (r.2.headD 0) else false
theorem openF (i tok : Nat) (s : RowState) (v : MonoViable (fullMask 25) THere s) :
    cutF i tok s = false := by
  unfold cutF
  dsimp only
  split
  · exact pCutOpen _ _ _ v
  · split
    · exact Geometry.rectangleOpen _ v
    · rfl
def edgesF (i tok : Nat) : Option DagLink :=
  let r := code i tok
  if r.1=16 then some (r.2.headD 0,0) else none
def negatives : List Nat := [0,1,6,12,18,24]
def verify (i : Nat) := scan (fullMask 25) THere negatives states 32 #[] edgesF cutF i
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked0 : verify 0 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked1 : verify 1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked2 : verify 2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked3 : verify 3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked4 : verify 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked5 : verify 5 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked6 : verify 6 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked7 : verify 7 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked8 : verify 8 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked9 : verify 9 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked10 : verify 10 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked11 : verify 11 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked12 : verify 12 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked13 : verify 13 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked14 : verify 14 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked15 : verify 15 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked16 : verify 16 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked17 : verify 17 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked18 : verify 18 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked19 : verify 19 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked20 : verify 20 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked21 : verify 21 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked22 : verify 22 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked23 : verify 23 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked24 : verify 24 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked25 : verify 25 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked26 : verify 26 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked27 : verify 27 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked28 : verify 28 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked29 : verify 29 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked30 : verify 30 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem checked31 : verify 31 = true := by decide +kernel
theorem allChecked : ∀ i : Fin 32, verify i.val = true := by
  intro i
  fin_cases i
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
  · exact checked29
  · exact checked30
  · exact checked31
theorem no13 : ¬ PEqualNP.Represents.RepSizeAtMost postedHere 13 := by
  rintro ⟨C,hc,size,hr⟩
  obtain ⟨k,cap,live⟩ := representation_liveHere C hc hr
  let s : RowState := (13,[31,992,31744,1015808,1082401,2164802,4329604,8659208,17318416,32505856],[])
  have bank : s.2.1.toFinset = stockHere.toFinset := by decide +kernel
  rw [←bank] at live
  apply tableSound (m:=fullMask 25) (g:=THere) (neg:=negatives)
    (moves:=#[]) (states:=states) (count:=32) (links:=edgesF) (cut:=cutF)
    (by unfold Masked; decide +kernel : Masked (fullMask 25) (fullMask 25)) (by intro i m h; simp at h)
    (by decide +kernel) openF (fun i hi => allChecked ⟨i,hi⟩) 13 0 s (by decide) rfl rfl k (cap.trans size) live

end PEqualNP.Outside.L_meta_25467.Punctured
open PEqualNP.Outside.L_meta_25467.Punctured in
theorem PEqualNP.Outside.L_meta_25467 : ¬ PEqualNP.Represents.RepSizeAtMost
    (fun (u : Fin 5) (v : Fin 5) => (32435687 : ℕ).testBit (5 * u.val + v.val)) 13 := no13
