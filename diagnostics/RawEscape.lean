import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9737.RectangleBank
abbrev P := Fin 13
abbrev L := Fin 12
def flags : List (Nat × Nat) := [(0,3),(0,9),(0,11),(1,0),(1,4),(1,10),(2,0),(2,1),(2,5),(2,11),(3,1),(3,2),(3,6),(4,0),(4,2),(4,3),(4,7),(5,1),(5,3),(5,4),(5,8),(6,2),(6,4),(6,5),(6,9),(7,3),(7,5),(7,6),(7,10),(8,4),(8,6),(8,7),(8,11),(9,5),(9,7),(9,8),(10,0),(10,6),(10,8),(10,9),(11,1),(11,7),(11,9),(11,10),(12,2),(12,8),(12,10),(12,11)]
def ed (p : P) (l : L) : Prop := (p.val,l.val) ∈ flags
instance (p : P) (l : L) : Decidable (ed p l) := by unfold ed; infer_instance
abbrev Rect := Finset P × Finset L
def grid (x : Finset P) (y : Finset L) : Prop := ∃ p ∈ x, ∃ l ∈ y, ed p l
def hit (r : Rect) (x : Finset P) (y : Finset L) : Prop :=
 (∃ p ∈ x, p∈r.1) ∧ (∃ l ∈ y, l∈r.2)
def cn (p : P) : Finset L := Finset.univ.filter (fun l => ¬ed p l)
def dn (l : L) : Finset P := Finset.univ.filter (fun p => ¬ed p l)
theorem probes {n : Nat} (rect : Fin n → Rect) (dec : (Fin n → Prop) → Prop)
    (mono : ∀ a b, (∀ i, a i → b i) → dec a → dec b)
    (rep : ∀ x y, dec (fun i => hit (rect i) x y) ↔ grid x y)
    {p : P} {l : L} (pe : ed p l) :
    (∃ i, p∈(rect i).1 ∧ l∈(rect i).2 ∧ ∀ t ∈ (rect i).2, ed p t) ∧
    (∃ i, p∈(rect i).1 ∧ l∈(rect i).2 ∧ ∀ t ∈ (rect i).1, ed t l) := by
 classical
 have yes : dec (fun i => hit (rect i) {p} {l}) :=
   (rep _ _).2 ⟨p,by simp,l,by simp,pe⟩
 have noP : ¬dec (fun i => hit (rect i) {p} (cn p)) := by
   intro h
   obtain ⟨p',hp',t,ht,et⟩ := (rep _ _).1 h
   have ep : p'=p := by simpa using hp'
   subst p'
   exact (Finset.mem_filter.mp ht).2 et
 have noL : ¬dec (fun i => hit (rect i) (dn l) {l}) := by
   intro h
   obtain ⟨t,ht,l',hl',et⟩ := (rep _ _).1 h
   have el : l'=l := by simpa using hl'
   subst l'
   exact (Finset.mem_filter.mp ht).2 et
 constructor
 · by_contra miss
   apply noP
   refine mono _ _ ?_ yes
   intro i hi
   obtain ⟨hp,hl⟩ : p∈(rect i).1 ∧ l∈(rect i).2 := by simpa [hit] using hi
   have someBad : ∃ t∈(rect i).2, ¬ed p t := by
     by_contra! allGood
     exact miss ⟨i,hp,hl,allGood⟩
   obtain ⟨t,ht,neg⟩ := someBad
   exact ⟨⟨p,by simp,hp⟩,t,by simpa [cn] using neg,ht⟩
 · by_contra miss
   apply noL
   refine mono _ _ ?_ yes
   intro i hi
   obtain ⟨hp,hl⟩ : p∈(rect i).1 ∧ l∈(rect i).2 := by simpa [hit] using hi
   have someBad : ∃ t∈(rect i).1, ¬ed t l := by
     by_contra! allGood
     exact miss ⟨i,hp,hl,allGood⟩
   obtain ⟨t,ht,neg⟩ := someBad
   exact ⟨⟨t,by simpa [dn] using neg,ht⟩,l,by simp,hl⟩

theorem squareFree : ∀ (p q : P) (l k : L), ed p l → ed p k → ed q l → ed q k → p=q ∨ l=k := by
 decide +kernel
theorem uniquePoint {r : Rect} {p q : P} (l k : L) (ne : l≠k) (h : l∈r.2) (j : k∈r.2)
    (a : ∀ t∈r.2, ed p t) (b : ∀ t∈r.2, ed q t) : p=q :=
 (squareFree p q l k (a _ h) (a _ j) (b _ h) (b _ j)).resolve_right ne
theorem uniqueLine {r : Rect} {l k : L} (p q : P) (ne : p≠q) (h : p∈r.1) (j : q∈r.1)
    (a : ∀ t∈r.1, ed t l) (b : ∀ t∈r.1, ed t k) : l=k :=
 (squareFree p q l k (a _ h) (b _ h) (a _ j) (b _ j)).resolve_left ne
end PEqualNP.Outside.L_meta_9737.RectangleBank

namespace PEqualNP.Outside.L_meta_9737.RectangleBank
def pLinks : Array (Array Nat) := #[#[7669,6626,7149,7676,7161,8191,8191,8191,8191,8180,8169,8191,8191],#[7669,7670,6103,5592,8191,6131,8191,8191,8191,8180,8191,8147,8191],#[7669,7670,8191,3500,4023,8191,4071,8191,8191,8180,8191,8191,8103],#[7493,7670,8191,7676,8030,8046,8191,8142,8191,8180,8191,8191,8191],#[7669,7318,8191,7676,8191,7869,7901,8191,8093,8180,8191,8191,8191],#[7669,7670,7487,7676,8191,8191,7547,7611,8191,7984,8191,8191,8191],#[7669,7670,8191,6268,8191,8191,8191,6903,7031,8180,7799,8191,8191],#[7669,7670,8191,7676,5375,8191,8191,8191,5615,5860,8191,7407,8191],#[7669,7670,8191,7676,8191,2559,8191,8191,8191,3028,3551,8191,6623],#[4533,7670,8191,7676,8191,8191,5118,8191,8191,8180,6078,7102,8191],#[7669,1398,8191,7676,8191,8191,8191,2045,8191,8180,8191,3965,6013],#[3313,7670,3838,7676,8191,8191,8191,8191,4090,8180,8191,8191,7930]]
def lLinks : Array (Array Nat) := #[#[4095,4095,4095,1535,4095,4095,4095,4095,4095,2039,4095,3575],#[3055,4095,4095,4095,3070,4095,4095,4095,4095,4095,4078,4095],#[2013,2014,4095,4095,4095,2044,4095,4095,4095,4095,4095,4060],#[4095,4027,4029,4095,4095,4095,4089,4095,4095,4095,4095,4095],#[3955,4095,3958,3962,4095,4095,4095,4082,4095,4095,4095,4095],#[4095,3815,4095,3821,3829,4095,4095,4095,4069,4095,4095,4095],#[4095,4095,3535,4095,3547,3563,4095,4095,4095,4043,4095,4095],#[4095,4095,4095,2975,4095,2999,3031,4095,4095,4095,3991,4095],#[4095,4095,4095,4095,1855,4095,1903,1967,4095,4095,4095,3887],#[4095,4095,4095,4095,4095,3711,4095,3807,3935,4095,4095,4095],#[3263,4095,4095,4095,4095,4095,3326,4095,3518,3774,4095,4095],#[4095,2431,4095,4095,4095,4095,4095,2557,4095,2941,3453,4095],#[4095,4095,767,4095,4095,4095,4095,4095,1019,4095,1787,2811]]
def pn (l : L) (p : P) := (pLinks[l.val]!)[p.val]!
def ln (p : P) (l : L) := (lLinks[p.val]!)[l.val]!
def commonP (l : L) (p q : P) := ∃ t : L, t≠l ∧ ed p t ∧ ed q t
def commonL (p : P) (l k : L) := ∃ t : P, t≠p ∧ ed t l ∧ ed t k
instance (l : L) (p q : P) : Decidable (commonP l p q) := by unfold commonP; infer_instance
instance (p : P) (l k : L) : Decidable (commonL p l k) := by unfold commonL; infer_instance
theorem pointLinks : ∀ (l:L) (p q:P), (pn l p).testBit q.val=true ↔ commonP l p q := by decide +kernel
theorem lineLinks : ∀ (p:P) (l k:L), (ln p l).testBit k.val=true ↔ commonL p l k := by decide +kernel
def pCount (z : Nat) := ((List.finRange 13).filter (fun p => z.testBit p.val)).length
def lCount (z : Nat) := ((List.finRange 12).filter (fun l => z.testBit l.val)).length
def nontriple (r : L) (a b c : P) :=
 let x := pn r a
 let y := pn r b
 let z := pn r c
 8191 ^^^ ((x &&& y) ||| (x &&& z) ||| (y &&& z))
def nonpair (r : P) (a b : L) := 4095 ^^^ ((ln r a) &&& (ln r b))
set_option maxHeartbeats 0
theorem smallTriples : ∀ (r:L) (a b c:P), a≠b → b≠c → a≠c →
 (pn r a).testBit b.val=false → (pn r a).testBit c.val=false → (pn r b).testBit c.val=false →
 pCount (nontriple r a b c)≤4 := by decide +kernel
theorem smallPairs : ∀ (r:P) (a b:L), a≠b → (ln r a).testBit b.val=false →
 lCount (nonpair r a b)≤4 := by decide +kernel
theorem rawBudget {total pre terminals clean dirty : Nat}
  (sites : 2*terminals+pre≤total+2) (target : total≤58)
  (simpleEdges : 48≤8*pre+4+clean) (disjoint : clean+dirty≤terminals)
  (many : 20≤dirty) : terminals≤27 := by omega
theorem rawLarge {clean dirty wide distinct marked up ul qp ql prepP prepL dupP dupL total : Nat}
    (pq : 13≤qp+up+wide) (lq : 12≤ql+ul+wide) (cover : up+ul≤clean)
    (rankP : qp≤prepP+2+dupL) (rankL : ql≤prepL+1+dupP)
    (dups : dupP+dupL+distinct≤clean+dirty) (mark1 : marked≤dirty) (mark2 : marked≤distinct)
    (circuit : 2*(clean+dirty+wide)+prepP+prepL≤total+2) (many : 20≤marked) :
    60≤total := by omega
end PEqualNP.Outside.L_meta_9737.RectangleBank
