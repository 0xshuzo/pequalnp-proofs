import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9792.Interface
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 10000
abbrev P := Fin 24
abbrev F := Fin 44
abbrev X := P → Bool
abbrev Signal := X → Bool
def first : F → P := ![0, 0, 0, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 10, 10, 10, 11, 11, 11, 11, 12, 12, 12, 12]
def second : F → P := ![15, 21, 23, 16, 22, 13, 17, 23, 13, 14, 18, 14, 15, 19, 13, 15, 16, 20, 14, 16, 17, 21, 15, 17, 18, 22, 16, 18, 19, 23, 17, 19, 20, 18, 20, 21, 13, 19, 21, 22, 14, 20, 22, 23]
def ng : P → Nat := ![10518528, 4259840, 8527872, 286720, 573440, 1155072, 2310144, 4620288, 9240576, 1703936, 3407872, 6823936, 13647872, 2092, 4184, 177, 354, 708, 1416, 2832, 5664, 3137, 6274, 4357]
def pick (b : Bool) (i : F) : P := if b then first i else second i
class Orientation where
  flip : F → Bool
variable [Orientation]
def row (i : F) : P := pick (Orientation.flip i) i
def col (i : F) : P := pick (!(Orientation.flip i)) i

def has (p q : P) := (ng p).testBit q.val
def out (p : P) : X := fun j => !(has p j)
def one (q : P) : X := fun j => decide (j=q)
def fires (v : Signal) (i : F) := v (one (col i)) = true ∧ v (out (row i)) = false
def mono (v : Signal) := ∀ x y : X,(∀ q,x q=true → y q=true) → v x=true → v y=true
def raw (q : P) : Signal := fun x => x q
def meet (u v : Signal) : Signal := fun x => u x && v x
def join (u v : Signal) : Signal := fun x => u x || v x
theorem pairUnique : ∀ (i j : F) (b c : Bool),pick b i=pick c j →
    pick (!b) i=pick (!c) j → i=j := by decide +kernel
theorem flags (i j : F) : row i=row j → col i=col j → i=j :=
  pairUnique i j _ _
theorem pickedEdge : ∀ (i : F) (b : Bool),has (pick b i) (pick (!b) i)=true := by decide +kernel
theorem edgeHere (i : F) : has (row i) (col i)=true := pickedEdge i _

theorem common : ∀ (p q a b : P),has p a=true → has p b=true → has q a=true → has q b=true → a≠b → p=q := by decide +kernel

theorem forced {v : Signal} (m : mono v) {i : F} (hi : fires v i) {r : P}
    (off : v (out r)=false) : has r (col i)=true := by
  by_contra ne
  have ex : out r (col i)=true := by simpa [out] using ne
  have sub : ∀ q,one (col i) q=true → out r q=true := by
    intro q eq
    have qeq : q=col i := by simpa [one] using eq
    simpa [qeq] using ex
  have yes := m _ _ sub hi.1
  rw [off] at yes
  contradiction

def uniform (c : F → F) (v : Signal) :=
  ∀ i j,row i=row j → fires v i → fires v j → c i=c j

theorem uniqueRow {v : Signal} (m : mono v) {i j a b : F}
    (ij : row i=row j) (ab : row a=row b) (hij : i≠j) (hab : a≠b)
    (fi : fires v i) (fj : fires v j) (fa : fires v a) (fb : fires v b) : row i=row a := by
  have dif : col i ≠ col j := fun e => hij (flags i j ij e)
  exact common _ _ _ _ (edgeHere i) (by simpa only [ij] using edgeHere j)
    (forced m fi fa.2) (forced m fj fa.2) dif

def palette (c : F → F) : Finset F := univ.image c
theorem recolorCost (c : F → F) (a b : F) :
    (palette c).card ≤ (palette (fun i => if c i=b then a else c i)).card+1 := by
  classical
  let newColor := fun i => if c i=b then a else c i
  have sub : (palette c).erase b ⊆ palette newColor := by
    intro w hw
    obtain ⟨ne,wp⟩ := mem_erase.mp hw
    obtain ⟨i,_,rfl⟩ := mem_image.mp wp
    exact mem_image.mpr ⟨i,mem_univ i,by simp [newColor,ne]⟩
  have le := card_le_card sub
  by_cases h : b∈palette c
  · have er := card_erase_add_one h
    change (palette c).card ≤ (palette newColor).card+1
    omega
  · rw [erase_eq_of_notMem h] at le
    exact Nat.le.step le

theorem chooseColors (c : F → F) (u v : Signal) (good : mono (join u v))
    (uu : uniform c u) (vv : uniform c v) :
    ∃ c' : F → F, uniform c' (join u v) ∧
        (∀ a b,c a=c b → c' a=c' b) ∧ (palette c).card≤(palette c').card+1 := by
  classical
  by_cases old : uniform c (join u v)
  · exact ⟨c,old,fun _ _ eq=>eq,Nat.le_succ _⟩
  unfold uniform at old
  push_neg at old
  obtain ⟨i,j,ij,fi,fj,ne⟩ := old
  have split (a : F) (fa : fires (join u v) a) : fires u a ∨ fires v a := by
    rcases fa with ⟨p,n⟩
    have pos : u (one (col a))=true ∨ v (one (col a))=true := by simpa [join] using p
    have neg : u (out (row a))=false ∧ v (out (row a))=false := by simpa [join] using n
    exact pos.elim (fun h => Or.inl ⟨h,neg.1⟩) (fun h => Or.inr ⟨h,neg.2⟩)
  have dich (a : F) (ar : row a=row i) (here : fires (join u v) a) : c a=c i ∨ c a=c j := by
    rcases split i fi with iu|iv <;> rcases split j fj with ju|jv
    · exact False.elim (ne (uu i j ij iu ju))
    · exact (split a here).elim (fun h=>Or.inl (uu a i ar h iu)) (fun h=>Or.inr (vv a j (ar.trans ij) h jv))
    · exact (split a here).elim (fun h=>Or.inr (uu a j (ar.trans ij) h ju)) (fun h=>Or.inl (vv a i ar h iv))
    · exact False.elim (ne (vv i j ij iv jv))
  let k := fun a : F => if c a=c j then c i else c a
  refine ⟨k,?_,?_,recolorCost c (c i) (c j)⟩
  · intro a b ab fa fb
    by_cases eq : a=b
    · rw [eq]
    have ar : row a=row i := (uniqueRow good ij ab (fun e=>ne (congrArg c e)) eq fi fj fa fb).symm
    have collapse (a : F) (z : c a=c i ∨ c a=c j) : k a=c i := by
      rcases z with z|z <;> simp [k,z]
    exact (collapse a (dich a ar fa)).trans (collapse b (dich b (ab.symm.trans ar) fb)).symm
  · intro a b eq
    simp only [k,eq]

inductive Built : List Signal → Nat → Prop
  | start : Built (List.ofFn raw) 0
  | addAnd {bank n} (old : Built bank n) {u v} (hu : u∈bank) (hv : v∈bank) :
      Built (meet u v :: bank) n
  | addOr {bank n} (old : Built bank n) {u v} (hu : u∈bank) (hv : v∈bank) :
      Built (join u v :: bank) (n+1)

theorem account {bank n} (built : Built bank n) :
    (∀ v∈bank,mono v) ∧ ∃ c : F→F,(∀ v∈bank,uniform c v) ∧ 44≤(palette c).card+n := by
  induction built with
  | start =>
    constructor
    · intro v h
      obtain ⟨q,rfl⟩ := List.mem_ofFn.mp h
      intro x y le val
      exact le q val
    · refine ⟨id,?_,by simp [palette]⟩
      intro v hv
      obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hv
      intro i j r fi fj
      have a : q=col i := by simpa [raw,one] using fi.1
      have b : q=col j := by simpa [raw,one] using fj.1
      exact flags i j r (a.symm.trans b)
  | @addAnd bank n prev u v hu hv ih =>
    obtain ⟨mons,c,valid,num⟩ := ih
    have mg : mono (meet u v) := by
      intro x y le z
      have p : u x=true ∧ v x=true := by simpa [meet] using z
      simp [meet,mons u hu x y le p.1,mons v hv x y le p.2]
    refine ⟨fun w hw => (List.mem_cons.mp hw).elim (fun eq => by simpa only [eq] using mg) (mons w),c,?_,num⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq|old
    · subst w
      intro i j same fi fj
      have pi : u (one (col i))=true ∧ v (one (col i))=true := by simpa [meet] using fi.1
      have pj : u (one (col j))=true ∧ v (one (col j))=true := by simpa [meet] using fj.1
      have bad : u (out (row i))=false ∨ v (out (row i))=false := by
        cases h : u (out (row i)) with
        | false => exact Or.inl rfl
        | true => exact Or.inr (by simpa [meet,h] using fi.2)
      rcases bad with bad|bad
      · exact valid u hu i j same ⟨pi.1,bad⟩ ⟨pj.1,by simpa only [← same] using bad⟩
      · exact valid v hv i j same ⟨pi.2,bad⟩ ⟨pj.2,by simpa only [← same] using bad⟩
    · exact valid w old
  | @addOr bank n prev u v hu hv ih =>
    obtain ⟨mons,c,valid,num⟩ := ih
    have mg : mono (join u v) := by
      intro x y le z
      have p : u x=true ∨ v x=true := by simpa [join] using z
      rcases p with h|h
      · simp [join,mons u hu x y le h]
      · simp [join,mons v hv x y le h]
    obtain ⟨d,fresh,less,count⟩ := chooseColors c u v mg (valid u hu) (valid v hv)
    refine ⟨fun w hw => (List.mem_cons.mp hw).elim (fun eq => by simpa only [eq] using mg) (mons w),d,?_,by omega⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq|old
    · simpa only [eq] using fresh
    · intro i j r a b
      exact less i j (valid w old i j r a b)

def matching : Fin 11 → F := ![5, 9, 0, 3, 20, 24, 13, 17, 35, 39, 29]
theorem disjointMatching : ∀ (i j : Fin 11) (b c : Bool),
    pick b (matching i)=pick c (matching j) → i=j := by decide +kernel

theorem splitCoefficients {bank n k} (built : Built bank n) (center : Fin k → P)
    (coef : Fin k → Signal) (avail : ∀ j,coef j∈bank) (part : F → Fin k)
    (tag : ∀ i,center (part i)=row i) (cover : ∀ i,fires (coef (part i)) i) :
    54 ≤ n+k+(k-1) := by
  classical
  obtain ⟨_,c,uniforms,budget⟩ := account built
  let pick : Fin k → F := fun j => if a : ∃ i : F,part i=j then Classical.choose a else 0
  have repr (i : F) : part (pick (part i))=part i := by
    have a : ∃ j : F,part j=part i := ⟨i,rfl⟩
    simp only [pick,dif_pos a]
    exact Classical.choose_spec a
  have sub : palette c ⊆ univ.image (fun j => c (pick j)) := by
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp hq
    let b := pick (part i)
    have same : part b=part i := repr i
    have sameRow : row b=row i := (tag b).symm.trans ((congrArg center same).trans (tag i))
    refine mem_image.mpr ⟨part i,mem_univ _,?_⟩
    exact uniforms _ (avail (part i)) b i sameRow (by simpa only [same] using cover b) (cover i)
  have cn := card_le_card sub
  have ck : (univ.image (fun j : Fin k =>c (pick j))).card ≤ (univ : Finset (Fin k)).card :=
    Finset.card_image_le
  have inj : Function.Injective (fun m : Fin 11 => part (matching m)) := by
    intro i j eq
    have h : row (matching i)=row (matching j) :=
      ((tag (matching i)).symm.trans (congrArg center eq)).trans (tag (matching j))
    exact disjointMatching i j _ _ h
  have kk := Fintype.card_le_of_injective _ inj
  simp only [card_univ,Fintype.card_fin] at ck kk
  omega



end PEqualNP.Outside.L_meta_9792.Interface
namespace PEqualNP.Outside.L_meta_9792.Interface
open Finset
section Bank
local instance orientLine : Orientation := ⟨fun _ => false⟩
abbrev J := Fin 11
def covered (bank : J → Signal) := ∀ i : F, ∃ j, fires (bank j) i

theorem separation (bank : J → Signal) (decode : P → (J → Bool) → Bool)
    (up : ∀ l a b,(∀ j,a j=true → b j=true) → decode l a=true → decode l b=true)
    (pos : ∀ i : F,decode (row i) (fun j => bank j (one (col i)))=true)
    (neg : ∀ i : F,decode (row i) (fun j => bank j (out (row i)))=false) : covered bank := by
  classical
  intro i
  by_contra! h
  have le : ∀ j,bank j (one (col i))=true → bank j (out (row i))=true := by
    intro j yes
    cases b : bank j (out (row i)) with
    | false => exact (h j ⟨yes,b⟩).elim
    | true => rfl
  have bad := up _ _ _ le (pos i)
  rw [neg i] at bad
  contradiction

theorem sameStar {v : Signal} (m : mono v) {i j : F} (a : fires v i) (b : fires v j) :
    col i = col j ∨ row i = row j := by
  by_cases e : col i=col j
  · exact Or.inl e
  · exact Or.inr (common (row i) (row j) (col i) (col j) (edgeHere i)
      (forced m b a.2) (forced m a b.2) (edgeHere j) e)

theorem matchedSignal (bank : J → Signal) (m : ∀j,mono (bank j)) (cov : covered bank) :
    ∃ w : J → Signal, (∀j,∃k,w j=bank k) ∧
        (∀t,fires (w t) (matching t)) ∧ (∀i : F,∃t,fires (w t) i) := by
  classical
  choose loc yes using cov
  let rep := fun j => loc (matching j)
  have inj : Function.Injective rep := by
    intro a b eq
    have ya := yes (matching a)
    have yb := yes (matching b)
    change loc (matching a) = loc (matching b) at eq
    rw [← eq] at yb
    rcases sameStar (m _) ya yb with e|e
    · exact disjointMatching _ _ true true e
    · exact disjointMatching _ _ false false e
  have sur : Function.Surjective rep := Finite.injective_iff_surjective.mp inj
  refine ⟨fun j => bank (rep j), fun j => ⟨rep j,rfl⟩,fun j => yes _,?_⟩
  intro i
  obtain ⟨j,hj⟩ := sur (loc i)
  exact ⟨j,by simpa only [hj] using yes i⟩

theorem allLine (good : J → Prop)
    (coveredBy : ∀ i : F,∃j,(good j ∧ row i = row (matching j)) ∨
       (¬good j ∧ col i = col (matching j))) : ∀ j,good j := by
  have step (i : F) (j : J)
      (line : ∀ k : J,row i=row (matching k) → k=j)
      (point : ∀ k : J,col i=col (matching k) → good k) : good j := by
    obtain ⟨k,h⟩ := coveredBy i
    rcases h with h|h
    · exact line k h.2 ▸ h.1
    · exact (h.1 (point k h.2)).elim
  have k4 : good 4 := step 30 4 (by decide +kernel) (by
    intro j eq
    have no : ∀ k : J, col 30 ≠ col (matching k) := by decide +kernel
    exact (no j eq).elim)
  have k6 : good 6 := step 31 6 (by decide +kernel) (by
    intro j eq
    have no : ∀ k : J, col 31 ≠ col (matching k) := by decide +kernel
    exact (no j eq).elim)
  have k7 : good 7 := step 32 7 (by decide +kernel) (by
    intro j eq
    have no : ∀ k : J, col 32 ≠ col (matching k) := by decide +kernel
    exact (no j eq).elim)
  have k1 : good 1 := step 40 1 (by decide +kernel) (by
    intro j eq
    have no : ∀ k : J, col 40 ≠ col (matching k) := by decide +kernel
    exact (no j eq).elim)
  have k9 : good 9 := step 42 9 (by decide +kernel) (by
    intro j eq
    have no : ∀ k : J, col 42 ≠ col (matching k) := by decide +kernel
    exact (no j eq).elim)
  have k10 : good 10 := step 43 10 (by decide +kernel) (by
    intro j eq
    have no : ∀ k : J, col 43 ≠ col (matching k) := by decide +kernel
    exact (no j eq).elim)
  have k0 : good 0 := step 8 0 (by decide +kernel) (by
    intro j eq
    have onlyOne : ∀ k : J,col 8=col (matching k) → k=1 := by decide +kernel
    exact (onlyOne j eq).symm ▸ k1)
  have k5 : good 5 := step 10 5 (by decide +kernel) (by
    intro j eq
    have onlyOne : ∀ k : J,col 10=col (matching k) → k=1 := by decide +kernel
    exact (onlyOne j eq).symm ▸ k1)
  have k2 : good 2 := step 12 2 (by decide +kernel) (by
    intro j eq
    have onlyOne : ∀ k : J,col 12=col (matching k) → k=6 := by decide +kernel
    exact (onlyOne j eq).symm ▸ k6)
  have k3 : good 3 := step 16 3 (by decide +kernel) (by
    intro j eq
    have onlyOne : ∀ k : J,col 16=col (matching k) → k=7 := by decide +kernel
    exact (onlyOne j eq).symm ▸ k7)
  have k8 : good 8 := step 21 8 (by decide +kernel) (by
    intro j eq
    have onlyOne : ∀ k : J,col 21=col (matching k) → k=4 := by decide +kernel
    exact (onlyOne j eq).symm ▸ k4)

  intro j
  fin_cases j <;> assumption

theorem rigidity (bank : J → Signal) (mon : ∀j,mono (bank j)) (cov : covered bank) :
    ∃ w : J → Signal, (∀j,∃k,w j=bank k) ∧ ∀ i : F,∃t,
      row (matching t)=row i ∧ fires (w t) i := by
  classical
  obtain ⟨w,live,matchYes,yes⟩ := matchedSignal bank mon cov
  have wm (j : J) : mono (w j) := by
    obtain ⟨k,hk⟩ := live j
    rw [hk]; exact mon _
  let good := fun t => ∀ i : F,fires (w t) i → row i=row (matching t)
  have pure {t : J} (bad : ¬good t) {i : F} (hit : fires (w t) i) :
      col i=col (matching t) := by
    by_contra ne
    have ri := (sameStar (wm t) hit (matchYes t)).resolve_left ne
    apply bad
    intro j hj
    rcases sameStar (wm t) hj (matchYes t) with c|r
    · rcases sameStar (wm t) hj hit with e|e
      · exact (ne (e.symm.trans c)).elim
      · exact e.trans ri
    · exact r
  have forcedLine : ∀ j,good j := by
    apply allLine
    intro i
    obtain ⟨t,ht⟩ := yes i
    by_cases g : good t
    · exact ⟨t,Or.inl ⟨g,g i ht⟩⟩
    · exact ⟨t,Or.inr ⟨g,pure g ht⟩⟩
  refine ⟨w,live,?_⟩
  intro i
  obtain ⟨t,ht⟩ := yes i
  exact ⟨t,(forcedLine t i ht).symm,ht⟩

theorem bankPrice {previous : List Signal} {n : Nat} (b : Built previous n)
    (bank : J → Signal) (live : ∀j,bank j ∈ previous) (cov : covered bank) : 33≤n := by
  classical
  obtain ⟨mons,_⟩ := account b
  obtain ⟨w,hw,good⟩ := rigidity bank (fun j => mons _ (live j)) cov
  choose part rowEq data using good
  have avail (t : J) : w t ∈ previous := by
    obtain ⟨k,h⟩ := hw t
    rw [h]; exact live _
  have z := splitCoefficients b (fun t => row (matching t)) w avail part rowEq data
  omega



open PEqualNP.CircuitLowerBounds
namespace Physical
def step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs++[g]) w=step (run gs w) g := by simp [run,List.foldl_append]
theorem length_run (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [step,ih]; omega
theorem snoc_other (w : List Bool) (v : Bool) (q : Nat) (ne : q≠w.length) :
    (w++[v]).getD q false=w.getD q false := by
  by_cases h : q<w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem snoc_last (w : List Bool) (v : Bool) : (w++[v]).getD w.length false=v := by simp

def separates {I : Type} (X Y : I→List Bool) (T : Finset Nat) :=
  ∀ i,∃ t∈T,(X i).getD t false≠(Y i).getD t false

def useful (g : Gate) : List Nat :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def charge : GateOp → Nat
  | .not => 0
  | _ => 1

def mass (gs : List Gate) := (gs.map fun g => charge g.op).sum
def inverters (gs : List Gate) := (gs.map fun g => 1-charge g.op).sum

theorem mass_split (gs : List Gate) : mass gs + inverters gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have cap : charge g.op≤1 := by cases g.op <;> simp [charge]
    change charge g.op+mass gs+(1-charge g.op+inverters gs)=gs.length+1
    omega

theorem mass_snoc (gs : List Gate) (g : Gate) : mass (gs++[g])=mass gs+charge g.op := by
  simp [mass,List.sum_append]

theorem use_sound (g : Gate) (v : Nat→Bool) :
    g.op.eval (g.inputs.map v)=g.op.eval ((useful g).map v) := by
  rcases g with ⟨op,args⟩
  cases op <;> cases args <;> rfl

theorem use_count (g : Gate) (h : g.inputs.length≤2) : (useful g).length ≤ charge g.op+1 := by
  rcases g with ⟨op,args⟩
  cases op <;> simp_all [useful,charge]

theorem trace {I : Type} (m : Nat) (X Y : I→List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m)
    (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length≤2)
    (S : Finset Nat) (sep : separates (fun i=>run gs (X i)) (fun i=>run gs (Y i)) S) :
    ∃ T : Finset Nat,separates X Y T ∧ T.card≤S.card+mass gs := by
  classical
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,sep,by simp [mass]⟩
  | append_singleton gs g ih =>
    let last := m+gs.length
    let V := fun i => run gs (X i)
    let W := fun i => run gs (Y i)
    have vl (i) : (V i).length=last := by rw [show V i=run gs (X i) by rfl,length_run,(lens i).1]
    have wl (i) : (W i).length=last := by rw [show W i=run gs (Y i) by rfl,length_run,(lens i).2]
    have stay (i : I) (w : Nat) (ne : w≠last) :
        (run (gs++[g]) (X i)).getD w false ≠ (run (gs++[g]) (Y i)).getD w false →
          (V i).getD w false ≠ (W i).getD w false := by
      rw [run_snoc,run_snoc]
      change (V i++[_]).getD w false≠(W i++[_]).getD w false → _
      rw [snoc_other _ _ w (by rwa [vl]),snoc_other _ _ w (by rwa [wl])]
      exact id
    have old : ∀ a∈gs,a.inputs.length≤2 := fun a ha => fan a (by simp [ha])
    by_cases mem : last∈S
    · let R := S.erase last ∪ (useful g).toFinset
      have rsep : separates V W R := by
        intro i
        obtain ⟨w,ws,diff⟩ := sep i
        by_cases eq : w=last
        · subst w
          by_contra! blocked
          have same : (useful g).map (fun t => (V i).getD t false)=(useful g).map (fun t => (W i).getD t false) := by
            apply List.map_congr_left
            intro t ht
            exact blocked t (Finset.mem_union_right _ (List.mem_toFinset.mpr ht))
          change (run (gs++[g]) (X i)).getD last false≠(run (gs++[g]) (Y i)).getD last false at diff
          rw [run_snoc,run_snoc] at diff
          change (V i++[g.op.eval _]).getD last false≠(W i++[g.op.eval _]).getD last false at diff
          rw [←vl i,snoc_last,vl i,←wl i,snoc_last] at diff
          exact diff ((use_sound g _).trans ((congrArg g.op.eval same).trans (use_sound g _).symm))
        · exact ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ws⟩),stay i w eq diff⟩
      obtain ⟨T,st,card⟩ := ih old R rsep
      have maxfan := fan g (by simp)
      have usable := use_count g maxfan
      have len := List.toFinset_card_le (useful g)
      have union : R.card≤(S.erase last).card+(useful g).toFinset.card := Finset.card_union_le _ _
      have erase := Finset.card_erase_add_one mem
      exact ⟨T,st,by rw [mass_snoc]; omega⟩
    · have oldSep : separates V W S := by
        intro i
        obtain ⟨w,ws,h⟩ := sep i
        exact ⟨w,ws,stay i w (fun eq => mem (eq ▸ ws)) h⟩
      obtain ⟨T,st,card⟩ := ih old S oldSep
      exact ⟨T,st,by rw [mass_snoc]; omega⟩


def result {m : Nat} (gs : List Gate) (root : Nat) (x : Fin m→Bool) :=
  (run gs (List.ofFn x)).getD root false
theorem cone {m : Nat} (gs : List Gate) (fan : ∀g∈gs,g.inputs.length≤2) (root : Nat) :
    ∃ S : Finset (Fin m),S.card≤gs.length+1 ∧ ∀ x y : Fin m→Bool,
      (∀ p∈S,x p=y p) → result gs root x=result gs root y := by
  classical
  let I := {p : (Fin m→Bool) × (Fin m→Bool) // result gs root p.1≠result gs root p.2}
  let X := fun p : I => List.ofFn p.val.1
  let Y := fun p : I => List.ofFn p.val.2
  obtain ⟨T,sep,cap⟩ := trace m X Y (by intro i; simp [X,Y])
    gs fan {root} (fun p => ⟨root,by simp,p.property⟩)
  let S := Finset.univ.filter (fun j : Fin m => j.val∈T)
  have le : S.card ≤ T.card := Finset.card_le_card_of_injOn Fin.val
    (fun x hx => (Finset.mem_filter.mp hx).2) (fun _ _ _ _ eq => Fin.ext eq)
  have massLe := mass_split gs
  refine ⟨S,by simp only [Finset.card_singleton] at cap; omega,?_⟩
  intro x y eq
  by_contra ne
  let j : I := ⟨(x,y),ne⟩
  obtain ⟨n,hn,delta⟩ := sep j
  change (List.ofFn x).getD n false ≠ (List.ofFn y).getD n false at delta
  by_cases lt : n<m
  · have e := eq ⟨n,lt⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩)
    have a : n < (List.ofFn x).length := by simpa using lt
    have b : n < (List.ofFn y).length := by simpa using lt
    rw [List.getD_eq_getElem _ _ a,List.getD_eq_getElem _ _ b] at delta
    simp only [List.getElem_ofFn] at delta
    exact delta e
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)] at delta
    exact delta rfl

def kth (i : J) : Fin 22 := ⟨i.val,by have := i.isLt;omega⟩
def lineK (i : J) : Fin 22 := ⟨11+i.val,by have := i.isLt;omega⟩
def put (z y : J→Bool) (v : Fin 22) : Bool :=
  if h : v.val<11 then z ⟨v.val,h⟩ else y ⟨v.val-11,by have := v.isLt;omega⟩
def hot (i : J) : J→Bool := fun k => decide (k=i)
def port (i : F) : J := Fin.ofNat 11 ((row i).val-13)
theorem portMatch : ∀ m : J,port (matching m)=m := by decide +kernel

theorem decoderPrice (bank : J→Signal) (bs : ∀j,mono (bank j))
    (gs : List Gate) (fan : ∀g∈gs,g.inputs.length≤2) (root : Nat)
    (up : ∀ x y : Fin 22→Bool,(∀j,x j=true → y j=true) →
      result gs root x=true → result gs root y=true)
    (yes : ∀ i : F,result gs root (put (fun j => bank j (one (col i))) (hot (port i)))=true)
    (no : ∀ i : F,result gs root (put (fun j => bank j (out (row i))) (hot (port i)))=false)
    (off : ∀ i : F,result gs root (put (fun j => bank j (one (col i))) (fun _=>false))=false) :
    21≤gs.length := by
  classical
  obtain ⟨S,cap,coneEq⟩ := cone (m:=22) gs fan root
  have orient {x y : Fin 22→Bool} (a : result gs root x=true) (b : result gs root y=false) :
      ∃j∈S,x j=true ∧ y j=false := by
    by_contra! blocked
    let u := fun j => x j || y j
    have inc : ∀j,x j=true → u j=true := by intro j h; simp [u,h]
    have same : ∀j∈S,u j=y j := by
      intro j hj
      cases h : x j <;> cases k : y j <;> simp_all [u]
    have clash := (up _ _ inc a).symm.trans ((coneEq u y same).trans b)
    contradiction
  have points (i : F) : ∃j : J,kth j∈S ∧ fires (bank j) i := by
    obtain ⟨j,hj,a,b⟩ := orient (yes i) (no i)
    by_cases t : j.val<11
    · refine ⟨⟨j.val,t⟩,?_,?_⟩
      · exact hj
      · exact ⟨by simpa [put,t] using a,by simpa [put,t] using b⟩
    · have aa : hot (port i) _=true := by simpa [put,t] using a
      have bb : hot (port i) _=false := by simpa [put,t] using b
      rw [aa] at bb
      contradiction
  choose which keep hit using points
  let idx := fun m : J => which (matching m)
  have inj : Function.Injective idx := by
    intro a b h
    change which (matching a)=which (matching b) at h
    have ha := hit (matching a)
    have hb := hit (matching b)
    rw [←h] at hb
    rcases sameStar (bs _) ha hb with eq|eq
    · exact disjointMatching _ _ true true eq
    · exact disjointMatching _ _ false false eq
  have sur := Finite.injective_iff_surjective.mp inj
  have leftAll (j : J) : kth j∈S := by
    obtain ⟨m,rfl⟩ := sur j
    exact keep (matching m)
  have rightAll (j : J) : lineK j∈S := by
    obtain ⟨k,hk,a,b⟩ := orient (yes (matching j)) (off (matching j))
    by_cases t : k.val<11
    · simp only [put,dif_pos t] at a b
      rw [a] at b
      contradiction
    · have h : (⟨k.val-11,by have := k.isLt;omega⟩ : J)=j := by
        simpa [put,t,hot,portMatch] using a
      have e : k=lineK j := Fin.ext (by have eq:=congrArg Fin.val h; dsimp [lineK] at *;omega)
      exact e ▸ hk
  have un : S=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro k
    by_cases t : k.val<11
    · exact leftAll ⟨k.val,t⟩
    · let j : J := ⟨k.val-11,by have := k.isLt;omega⟩
      have e : lineK j=k := Fin.ext (by dsimp [lineK,j];omega)
      exact e ▸ rightAll j
  rw [un] at cap
  simp only [Finset.card_univ,Fintype.card_fin] at cap
  omega
end Physical
end Bank
end PEqualNP.Outside.L_meta_9792.Interface
