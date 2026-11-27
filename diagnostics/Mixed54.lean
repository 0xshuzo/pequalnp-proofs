import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9829.Mixed
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


end PEqualNP.Outside.L_meta_9829.Mixed
