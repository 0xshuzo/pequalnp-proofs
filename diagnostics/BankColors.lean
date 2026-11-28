import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9737.PointColor
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 10000
abbrev P := Fin 13
abbrev F := Fin 48
abbrev X := P → Bool
abbrev Signal := X → Bool
def row : F → P := ![0,0,0,1,1,1,2,2,2,2,3,3,3,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,8,8,8,8,9,9,9,10,10,10,10,11,11,11,11,12,12,12,12]
def col : F → P := ![3,9,11,0,4,10,0,1,5,11,1,2,6,0,2,3,7,1,3,4,8,2,4,5,9,3,5,6,10,4,6,7,11,5,7,8,0,6,8,9,1,7,9,10,2,8,10,11]
def ng : P → Nat := ![2568,1041,2083,70,141,282,564,1128,2256,416,833,1666,3332]

def has (p q : P) := (ng p).testBit q.val
def out (p : P) : X := fun j => !(has p j)
def one (q : P) : X := fun j => decide (j=q)
def fires (v : Signal) (i : F) := v (one (col i)) = true ∧ v (out (row i)) = false
def mono (v : Signal) := ∀ x y : X,(∀ q,x q=true → y q=true) → v x=true → v y=true
def raw (q : P) : Signal := fun x => x q
def meet (u v : Signal) : Signal := fun x => u x && v x
def join (u v : Signal) : Signal := fun x => u x || v x
theorem flags : ∀ (i j : F),row i=row j → col i=col j → i=j := by decide +kernel
theorem edgeHere : ∀ i : F, has (row i) (col i)=true := by decide +kernel
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
  | addBroad {bank n} (old : Built bank n) {u v} (hu : u∈bank) (hv : v∈bank)
      (broad : ∀ p, join u v (out p)=true) : Built (join u v :: bank) n

theorem account {bank n} (built : Built bank n) :
    (∀ v∈bank,mono v) ∧ ∃ c : F→F,(∀ v∈bank,uniform c v) ∧ 48≤(palette c).card+n := by
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
  | @addBroad bank n prev u v hu hv broad ih =>
    obtain ⟨mons,c,valid,num⟩ := ih
    have mg : mono (join u v) := by
      intro x y le z
      have pos : u x=true ∨ v x=true := by simpa [join] using z
      rcases pos with pos|pos
      · simp [join,mons u hu x y le pos]
      · simp [join,mons v hv x y le pos]
    refine ⟨fun w hw => (List.mem_cons.mp hw).elim (fun eq => by simpa only [eq] using mg) (mons w),c,?_,num⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq|prior
    · subst w
      intro i j same fi fj
      have a := fi.2
      rw [broad] at a
      contradiction
    · exact valid w prior
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

theorem charged {bank n} (built : Built bank n) {m : Nat} (owner : Fin m → P)
    (wire : Fin m → Signal) (avail : ∀ j, wire j ∈ bank) (demand : Finset F)
    (cover : ∀ i∈demand, ∃ j, row i=owner j ∧ fires (wire j) i) :
    demand.card≤n+m := by
  classical
  obtain ⟨_,c,val,price⟩ := account built
  let pick (j : Fin m) := if h : ∃ i : F, row i=owner j ∧ fires (wire j) i then Classical.choose h else (0:F)
  have choose (j : Fin m) (i : F) (r : row i=owner j) (on : fires (wire j) i) :
      c i=c (pick j) := by
    have yes : ∃ q : F,row q=owner j ∧ fires (wire j) q := ⟨i,r,on⟩
    have pp : row (pick j)=owner j ∧ fires (wire j) (pick j) := by
      simpa only [pick,dif_pos yes] using Classical.choose_spec yes
    exact val (wire j) (avail j) i (pick j) (r.trans pp.1.symm) on pp.2
  have sub : palette c ⊆ (univ \ demand).image c ∪ univ.image (fun j => c (pick j)) := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    by_cases h : i∈demand
    · obtain ⟨j,r,on⟩ := cover i h
      exact mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,(choose j i r on).symm⟩)
    · exact mem_union_left _ (mem_image.mpr ⟨i,mem_sdiff.mpr ⟨mem_univ _,h⟩,rfl⟩)
  have hcard := (card_le_card sub).trans (card_union_le ..)
  have h1 : ((univ \ demand).image c).card ≤ (univ \ demand).card := card_image_le
  have h2 : (univ.image (fun j => c (pick j))).card≤m := by
    have hh : (univ.image (fun j => c (pick j))).card≤(Finset.univ : Finset (Fin m)).card := Finset.card_image_le
    simpa using hh
  have h3 : (univ \ demand).card+demand.card=48 := by
    simpa using (card_sdiff_add_card_eq_card (subset_univ demand))
  omega
end PEqualNP.Outside.L_meta_9737.PointColor
namespace PEqualNP.Outside.L_meta_9737.LineColor
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 10000
abbrev P := Fin 13
abbrev F := Fin 48
abbrev X := P → Bool
abbrev Signal := X → Bool
def row : F → P := ![3,9,11,0,4,10,0,1,5,11,1,2,6,0,2,3,7,1,3,4,8,2,4,5,9,3,5,6,10,4,6,7,11,5,7,8,0,6,8,9,1,7,9,10,2,8,10,11]
def col : F → P := ![0,0,0,1,1,1,2,2,2,2,3,3,3,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,8,8,8,8,9,9,9,10,10,10,10,11,11,11,11,12,12,12,12]
def ng : P → Nat := ![1046,2092,4184,177,354,708,1416,2832,5664,3137,6274,4357,0]

def has (p q : P) := (ng p).testBit q.val
def out (p : P) : X := fun j => !(has p j)
def one (q : P) : X := fun j => decide (j=q)
def fires (v : Signal) (i : F) := v (one (col i)) = true ∧ v (out (row i)) = false
def mono (v : Signal) := ∀ x y : X,(∀ q,x q=true → y q=true) → v x=true → v y=true
def raw (q : P) : Signal := fun x => x q
def meet (u v : Signal) : Signal := fun x => u x && v x
def join (u v : Signal) : Signal := fun x => u x || v x
theorem flags : ∀ (i j : F),row i=row j → col i=col j → i=j := by decide +kernel
theorem edgeHere : ∀ i : F, has (row i) (col i)=true := by decide +kernel
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
  | addBroad {bank n} (old : Built bank n) {u v} (hu : u∈bank) (hv : v∈bank)
      (broad : ∀ p, join u v (out p)=true) : Built (join u v :: bank) n

theorem account {bank n} (built : Built bank n) :
    (∀ v∈bank,mono v) ∧ ∃ c : F→F,(∀ v∈bank,uniform c v) ∧ 48≤(palette c).card+n := by
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
  | @addBroad bank n prev u v hu hv broad ih =>
    obtain ⟨mons,c,valid,num⟩ := ih
    have mg : mono (join u v) := by
      intro x y le z
      have pos : u x=true ∨ v x=true := by simpa [join] using z
      rcases pos with pos|pos
      · simp [join,mons u hu x y le pos]
      · simp [join,mons v hv x y le pos]
    refine ⟨fun w hw => (List.mem_cons.mp hw).elim (fun eq => by simpa only [eq] using mg) (mons w),c,?_,num⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq|prior
    · subst w
      intro i j same fi fj
      have a := fi.2
      rw [broad] at a
      contradiction
    · exact valid w prior
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

theorem charged {bank n} (built : Built bank n) {m : Nat} (owner : Fin m → P)
    (wire : Fin m → Signal) (avail : ∀ j, wire j ∈ bank) (demand : Finset F)
    (cover : ∀ i∈demand, ∃ j, row i=owner j ∧ fires (wire j) i) :
    demand.card≤n+m := by
  classical
  obtain ⟨_,c,val,price⟩ := account built
  let pick (j : Fin m) := if h : ∃ i : F, row i=owner j ∧ fires (wire j) i then Classical.choose h else (0:F)
  have choose (j : Fin m) (i : F) (r : row i=owner j) (on : fires (wire j) i) :
      c i=c (pick j) := by
    have yes : ∃ q : F,row q=owner j ∧ fires (wire j) q := ⟨i,r,on⟩
    have pp : row (pick j)=owner j ∧ fires (wire j) (pick j) := by
      simpa only [pick,dif_pos yes] using Classical.choose_spec yes
    exact val (wire j) (avail j) i (pick j) (r.trans pp.1.symm) on pp.2
  have sub : palette c ⊆ (univ \ demand).image c ∪ univ.image (fun j => c (pick j)) := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    by_cases h : i∈demand
    · obtain ⟨j,r,on⟩ := cover i h
      exact mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,(choose j i r on).symm⟩)
    · exact mem_union_left _ (mem_image.mpr ⟨i,mem_sdiff.mpr ⟨mem_univ _,h⟩,rfl⟩)
  have hcard := (card_le_card sub).trans (card_union_le ..)
  have h1 : ((univ \ demand).image c).card ≤ (univ \ demand).card := card_image_le
  have h2 : (univ.image (fun j => c (pick j))).card≤m := by
    have hh : (univ.image (fun j => c (pick j))).card≤(Finset.univ : Finset (Fin m)).card := Finset.card_image_le
    simpa using hh
  have h3 : (univ \ demand).card+demand.card=48 := by
    simpa using (card_sdiff_add_card_eq_card (subset_univ demand))
  omega
end PEqualNP.Outside.L_meta_9737.LineColor
