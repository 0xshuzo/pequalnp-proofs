import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10008.Completion
abbrev V := Fin 31
abbrev Sh := Finset V
abbrev Box := Sh × Sh
def avoids (x s : Sh) := ∀p∈s,p∉x
def has (a : List Sh) (s : Sh) (p : V) := ∃x∈a,p∈x ∧ avoids x s
def realizes (a : List Sh) (s : Sh) := ∀p : V,p∉s → has a s p
def deficit (a : List Sh) (s : Sh) (p : V) := p∉s ∧ ¬has a s p

theorem extra (a : List Sh) (x s : Sh) :
    realizes (x::a) s ↔ (∀p,deficit a s p → p∈x) ∧
      ((∃p,deficit a s p) → avoids x s) := by
  classical
  constructor
  · intro ok
    have unique {p} (fail : deficit a s p) : p∈x ∧ avoids x s := by
      obtain ⟨v,member,h⟩ := ok p fail.1
      rcases List.mem_cons.mp member with e|ea
      · simpa [e] using h
      · exact False.elim (fail.2 ⟨v,ea,h⟩)
    exact ⟨fun p h => (unique h).1,fun ⟨p,h⟩ => (unique h).2⟩
  · rintro ⟨owns,clear⟩ p hp
    by_cases old : has a s p
    · rcases old with ⟨v,hv,h⟩
      exact ⟨v,List.mem_cons_of_mem _ hv,h⟩
    · have missing : deficit a s p := ⟨hp,old⟩
      exact ⟨x,by simp,owns p missing,clear ⟨p,missing⟩⟩

-- One unrestricted extra side can fix a whole family precisely when all its
-- required points avoid every block that needs the extra side.
theorem oneFree {I : Type} (a : List Sh) (blocks : I → Sh) :
    (∃x : Sh,∀j,realizes (x::a) (blocks j)) ↔
    ∀ i j p,deficit a (blocks i) p → (∃q,deficit a (blocks j) q) → p∉blocks j := by
  classical
  constructor
  · rintro ⟨x,fit⟩ i j p need bad belongs
    exact ((extra a x (blocks j)).mp (fit j)).2 bad p belongs
      (((extra a x (blocks i)).mp (fit i)).1 p need)
  · intro h
    let x := Finset.univ.filter fun p : V => ∃i,deficit a (blocks i) p
    refine ⟨x,fun j => (extra a x (blocks j)).mpr ⟨?_,?_⟩⟩
    · intro p need
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,need⟩
    · intro bad p hp present
      obtain ⟨i,need⟩ := (Finset.mem_filter.mp present).2
      exact h i j p need bad hp

theorem carrierPencil (a : List Sh) (x s : Sh) {p : V}
    (hp : p∈x) (hs : p∈s) (yes : realizes (x::a) s) : realizes a s := by
  classical
  intro q hq
  by_contra missing
  exact ((extra a x s).mp yes).2 ⟨q,hq,missing⟩ p hs hp

def physical (M : V → V → Bool) (L : List Box) :=
  (∀r∈L,∀p∈r.1,∀j∈r.2,M p j=false) ∧
  ∀p j,M p j=false → ∃r∈L,p∈r.1 ∧ j∈r.2

def line (M : V → V → Bool) (j : V) : Sh := Finset.univ.filter fun p => M p j=true
private theorem inLine (M : V → V → Bool) (j p : V) : p∈line M j ↔ M p j=true := by
  simp [line]

noncomputable def complete (M : V → V → Bool) (a : Sh) : Box := by
  classical
  exact (a,Finset.univ.filter fun j => avoids a (line M j))

theorem build (M : V → V → Bool) (a : List Sh) :
    (∀j,realizes a (line M j)) ↔ physical M (a.map (complete M)) := by
  classical
  constructor
  · intro yes
    constructor
    · intro r hr p hp j hj
      obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
      have avoid := (Finset.mem_filter.mp hj).2
      cases e : M p j with
      | false => rfl
      | true => exact False.elim (avoid p ((inLine M j p).mpr e) hp)
    · intro p j blank
      have h : p∉line M j := by simp [line,blank]
      obtain ⟨z,hz,atP,away⟩ := yes j p h
      exact ⟨complete M z,List.mem_map.mpr ⟨z,hz,rfl⟩,atP,Finset.mem_filter.mpr ⟨Finset.mem_univ _,away⟩⟩
  · rintro ⟨_,cov⟩ j p hp
    have h : M p j=false := by cases e : M p j <;> simp_all [line]
    obtain ⟨r,hr,pr,jr⟩ := cov p j h
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
    exact ⟨z,hz,pr,(Finset.mem_filter.mp jr).2⟩

theorem physicalFree (M : V → V → Bool) (a : List Sh) :
    (∃x,physical M ((x::a).map (complete M))) ↔
    ∀i j p,deficit a (line M i) p → (∃q,deficit a (line M j) q) → p∉line M j := by
  rw [← oneFree a (line M)]
  exact exists_congr fun x => (build M (x::a)).symm

def enumerate (forced : Sh) : List Sh → Sh → List Sh
  | [], b => [b]
  | a::as, b =>
    if Disjoint a forced then enumerate forced as b ++ enumerate forced as (b \ a)
    else enumerate forced as b

noncomputable def leftOver (s : Sh) : List Sh → Sh → Sh
  | [], b => b
  | a::as, b => if Disjoint a s then leftOver s as (b \ a) else leftOver s as b

theorem leftSpec (s : Sh) (as : List Sh) (b : Sh) (p : V) :
    p∈leftOver s as b ↔ p∈b ∧ ¬has as s p := by
  classical
  induction as generalizing b with
  | nil => simp [leftOver,has]
  | cons a as ih =>
    have dis : Disjoint a s ↔ avoids a s := by
      rw [Finset.disjoint_left]
      unfold avoids
      constructor
      · intro h q qs qa; exact h qa qs
      · intro h q qa qs; exact h q qs qa
    have h : has (a::as) s p ↔ (p∈a ∧ avoids a s) ∨ has as s p := by
      simp [has]
    by_cases d : Disjoint a s
    · simp only [leftOver,d,if_true,ih,Finset.mem_sdiff,h,dis.mp d,and_true,not_or]
      tauto
    · have na : ¬avoids a s := fun q => d (dis.mpr q)
      simp [leftOver,d,ih,h,na]

theorem attained (forced s : Sh) (thin : forced⊆s) (as : List Sh) (b : Sh) :
    leftOver s as b ∈ enumerate forced as b := by
  classical
  induction as generalizing b with
  | nil => simp [leftOver,enumerate]
  | cons a as ih =>
    by_cases d : Disjoint a s
    · have ds : Disjoint a forced := Finset.disjoint_left.mpr (fun x hx hf => Finset.disjoint_left.mp d hx (thin hf))
      simp [leftOver,d,enumerate,ds,ih]
    · by_cases ds : Disjoint a forced <;> simp [leftOver,d,enumerate,ds,ih]

theorem lineIsGenerated (as : List Sh) (f s : Sh) (thin : f⊆s) (yes : realizes as s) :
    s∈enumerate f as Finset.univ := by
  classical
  have h : leftOver s as Finset.univ=s := by
    ext p
    rw [leftSpec]
    simp only [Finset.mem_univ,true_and]
    by_cases v : p∈s
    · exact iff_of_true (fun ⟨r,_,pr,ds⟩ => ds p v pr) v
    · exact iff_of_false (fun fail => fail (yes p v)) v
  simpa only [h] using attained f s thin as Finset.univ

def compatible (a b : Sh) : Bool := decide (a=b ∨ (a∩b).card=1)
def six (as : List Sh) (p q : V) := (enumerate {p,q} as Finset.univ).filter fun a => decide (a.card=6)

theorem smallObstruction (as : List Sh) (p q u v : V) (la lb : List Sh)
    (first : (six as p q).all (fun a => decide (a∈la))=true)
    (second : (six as u v).all (fun a => decide (a∈lb))=true)
    (conflict : la.all (fun a => lb.all (fun b => !compatible a b))=true)
    (blocks : V → Sh) (size : ∀j,(blocks j).card=6)
    (join : ∀x y : V,∃j,x∈blocks j ∧ y∈blocks j)
    (pair : ∀i j,compatible (blocks i) (blocks j)=true) :
    ¬∀j,realizes as (blocks j) := by
  classical
  intro fit
  obtain ⟨i,pi,qi⟩ := join p q
  obtain ⟨j,uj,vj⟩ := join u v
  have get {x y : V} {l : List Sh} {b : V} (hx : x∈blocks b) (hy : y∈blocks b)
      (hall : (six as x y).all (fun a => decide (a∈l))=true) : blocks b∈l := by
    have gen := lineIsGenerated as ({x,y}:Sh) (blocks b) (by
      intro w hw
      rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hw : w=x ∨ w=y) with e|e
      · exact e.symm ▸ hx
      · exact e.symm ▸ hy) (fit b)
    have mem : blocks b∈six as x y := List.mem_filter.mpr ⟨gen,by simp [size]⟩
    exact of_decide_eq_true (List.all_eq_true.mp hall _ mem)
  have ia := get pi qi first
  have jb := get uj vj second
  have no := List.all_eq_true.mp (List.all_eq_true.mp conflict _ ia) _ jb
  rw [pair] at no
  contradiction

def sides0 : List Sh := [({4,15,23,29,30} : Sh),({0,1,2,5,8,16,19,22,23,28} : Sh),({1,7,8,9,11,22,29} : Sh),({2,3,4,5,9,17,18,22,26,27} : Sh),({4,5,6,8,10,12,19,20,24,28} : Sh),({3,5,6,9,12,14,15,16,19,27} : Sh),({4,6,7,9,10,13,16,20,28} : Sh),({2,8,9,11,14,15,17,18,21,25,28} : Sh),({5,6,10,14,21,22,23,25,27,29} : Sh),({0,11,12,16,18,21,24,27,28,29,30} : Sh),({1,6,13,14,18,20,23,26} : Sh),({3,8,17,20,21,30} : Sh),({0,1,2,3,7,15,24,25} : Sh),({0,10,13,14,17,18,19,24,27,29} : Sh),({11,13,17,19,25,26} : Sh),({1,2,7,10,11,12,13,16,21,24,26} : Sh),({0,2,7,9,12,18,20,22,26} : Sh)]

def la0 : List Sh := [({2,4,5,6,15,23} : Sh),({2,5,6,12,16,28} : Sh)]

def lb0 : List Sh := [({1,5,6,10,13,19} : Sh),({3,5,6,10,13,19} : Sh),({5,6,10,13,14,19} : Sh),({5,6,10,13,19,26} : Sh)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
private theorem first0 : (six sides0 2 6).all (fun a => decide (a∈la0))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
private theorem second0 : (six sides0 5 13).all (fun a => decide (a∈lb0))=true := by decide +kernel
set_option maxRecDepth 30000 in
private theorem bad0 : la0.all (fun a => lb0.all (fun b => !compatible a b))=true := by decide +kernel
theorem obstruction0 (M : V → V → Bool) (size : ∀j,(line M j).card=6)
    (join : ∀x y : V,∃j,x∈line M j ∧ y∈line M j)
    (pair : ∀i j,compatible (line M i) (line M j)=true) :
    ¬physical M (sides0.map (complete M)) :=
  fun yes => smallObstruction sides0 2 6 5 13 la0 lb0 first0 second0 bad0
    (line M) size join pair ((build M sides0).mpr yes)

def sides1 : List Sh := [({0,1,7,9,13,15,16,17,20,23,26} : Sh),({2,10,13,16,19,24} : Sh),({1,9,19,20,22,23,25,30} : Sh),({5,14,18,19,20,27} : Sh),({2,6,20,21,22,29} : Sh),({6,17,24,27,28,30} : Sh),({0,7,18,21,25,28} : Sh),({2,5,11,26,30} : Sh),({6,7,8,15,19,23} : Sh),({8,9,12,14,21} : Sh),({4,6,11,14,16,23,28} : Sh),({0,1,4,8,11,13,17,18,22,30} : Sh),({3,12,15,16,17,18,25} : Sh),({1,10,11,15,27,29} : Sh),({3,4,5,7,9,11,13,22,27,28} : Sh),({3,4,24,26,29} : Sh),({0,3,5,10,12,23} : Sh)]

def la1 : List Sh := [({0,5,7,18,23,25} : Sh),({0,1,15,18,23,25} : Sh),({0,16,18,19,23,25} : Sh),({0,18,20,23,25,26} : Sh),({0,17,18,23,25,30} : Sh)]

def lb1 : List Sh := [({0,1,9,12,18,25} : Sh),({0,3,9,12,18,25} : Sh),({0,5,9,12,18,25} : Sh),({0,9,12,13,18,25} : Sh),({1,4,9,14,18,25} : Sh),({7,8,9,14,18,25} : Sh),({1,9,11,14,18,25} : Sh),({0,9,12,14,18,25} : Sh),({9,13,14,16,18,25} : Sh),({7,8,9,17,18,25} : Sh),({0,9,12,17,18,25} : Sh),({9,18,20,21,22,25} : Sh),({9,13,17,18,24,25} : Sh),({7,8,9,18,25,26} : Sh),({1,9,13,18,25,26} : Sh),({4,9,14,18,25,26} : Sh),({1,9,17,18,25,27} : Sh),({9,14,17,18,25,28} : Sh),({9,13,17,18,25,30} : Sh),({9,17,18,25,26,30} : Sh)]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
private theorem first1 : (six sides1 18 23).all (fun a => decide (a∈la1))=true := by decide +kernel
set_option maxRecDepth 30000 in
set_option maxHeartbeats 5000000 in
private theorem second1 : (six sides1 9 18).all (fun a => decide (a∈lb1))=true := by decide +kernel
set_option maxRecDepth 30000 in
private theorem bad1 : la1.all (fun a => lb1.all (fun b => !compatible a b))=true := by decide +kernel
theorem obstruction1 (M : V → V → Bool) (size : ∀j,(line M j).card=6)
    (join : ∀x y : V,∃j,x∈line M j ∧ y∈line M j)
    (pair : ∀i j,compatible (line M i) (line M j)=true) :
    ¬physical M (sides1.map (complete M)) :=
  fun yes => smallObstruction sides1 18 23 9 18 la1 lb1 first1 second1 bad1
    (line M) size join pair ((build M sides1).mpr yes)

end PEqualNP.Outside.L_meta_10008.Completion
