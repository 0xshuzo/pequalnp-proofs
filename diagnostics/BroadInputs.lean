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
theorem mixedPoint {p : P} {bs : Finset L} {l k z : L} (ne : l≠k)
    (hl : l∈bs) (hk : k∈bs) (hz : z∈bs) (el : ed p l) (ek : ed p k) (ez : ¬ed p z) :
    ¬∃ q : P, ∀ t∈bs, ed q t := by
 rintro ⟨q,h⟩
 have pq := (squareFree p q l k el ek (h _ hl) (h _ hk)).resolve_right ne
 exact ez (pq.symm ▸ h _ hz)
theorem mixedLine {l : L} {as' : Finset P} {p q z : P} (ne : p≠q)
    (hp : p∈as') (hq : q∈as') (hz : z∈as') (ep : ed p l) (eq : ed q l) (ez : ¬ed z l) :
    ¬∃ k : L, ∀ t∈as', ed t k := by
 rintro ⟨k,h⟩
 have lk := (squareFree p q l k ep (h _ hp) eq (h _ hq)).resolve_left ne
 exact ez (lk.symm ▸ h _ hz)

section
variable {α β : Type} [DecidableEq α] [DecidableEq β] (N : α → Finset β)
def small (u : Finset β) := ∃ a, u ⊆ N a
def covers (k : Finset α) (u : Finset β) := ∀ x∈u, ∃ a∈k, x∈N a
inductive OrBank : List (Finset β) → Nat → Prop where
 | base (raw : List (Finset β)) (h : ∀ s∈raw, small N s) : OrBank raw 0
 | addSmall {xs n} {a b : Finset β} (built : OrBank xs n) (pa : a∈xs) (pb : b∈xs)
   (h : small N (a∪b)) : OrBank ((a∪b)::xs) n
 | addBroad {xs n} {a b : Finset β} (built : OrBank xs n) (pa : a∈xs) (pb : b∈xs)
   (h : ¬small N (a∪b)) : OrBank ((a∪b)::xs) (n+1)
theorem oneSource {xs : List (Finset β)} {k : Finset α} (bound : ∀ s∈xs, ¬small N s → covers N k s)
    {a : Finset β} (ha : a∈xs) : ∃ t : Finset α, t.card≤1 ∧ covers N (k∪t) a := by
 classical
 by_cases h : small N a
 · obtain ⟨q,hq⟩ := h
   refine ⟨{q},by simp,?_⟩
   intro x hx
   exact ⟨q,by simp,hq hx⟩
 · refine ⟨∅,by simp,?_⟩
   simpa using bound a ha h
theorem allBroad {xs : List (Finset β)} {n : Nat} (b : OrBank N xs n) :
    ∃ k : Finset α, k.card≤2*n ∧ ∀ s∈xs, ¬small N s → covers N k s := by
 classical
 induction b with
 | base raw h =>
   exact ⟨∅,by simp,fun s hs hn => False.elim (hn (h _ hs))⟩
 | addSmall b pa pb h ih =>
   obtain ⟨k,price,old⟩ := ih
   refine ⟨k,price,?_⟩
   intro s hs hn
   rcases List.mem_cons.mp hs with eq|prior
   · exact False.elim (hn (eq.symm ▸ h))
   · exact old s prior hn
 | addBroad b pa pb h ih =>
   obtain ⟨k,price,old⟩ := ih
   obtain ⟨a,ca,ha⟩ := oneSource N old pa
   obtain ⟨d,cd,hd⟩ := oneSource N old pb
   refine ⟨(k∪a)∪d,?_,?_⟩
   · have j := Finset.card_union_le k a
     have m := Finset.card_union_le (k∪a) d
     omega
   · intro s hs hn x hx
     rcases List.mem_cons.mp hs with eq|prior
     · subst s
       rcases Finset.mem_union.mp hx with left|right
       · obtain ⟨q,hq,v⟩ := ha x left
         exact ⟨q,Finset.mem_union_left _ hq,v⟩
       · obtain ⟨q,hq,v⟩ := hd x right
         exact ⟨q,by simpa [Finset.mem_union] using (show (q∈k ∨ q∈a) ∨ q∈d by
            rcases Finset.mem_union.mp hq with j|j
            · exact Or.inl (Or.inl j)
            · exact Or.inr j),v⟩
     · obtain ⟨q,hq,v⟩ := old s prior hn x hx
       exact ⟨q,Finset.mem_union_left _ (Finset.mem_union_left _ hq),v⟩
end
end PEqualNP.Outside.L_meta_9737.RectangleBank
