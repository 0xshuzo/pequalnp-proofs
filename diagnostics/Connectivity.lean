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
def horizon : Finset P := {0,1,3,9}
theorem directions : ∀ p q : P, p∉horizon → ∃ l : L, ed p l ∧ ed q l := by decide +kernel
theorem intersections : ∀ l k : L, ∃ p : P, ed p l ∧ ed p k := by decide +kernel
theorem pointComponents {γ : Type} [DecidableEq γ] (Q : Finset P) (color : P → γ)
    (agree : ∀ p∈Q, ∀ q∈Q, ∀ l : L, ed p l → ed q l → color p=color q) :
    (Q.image color).card≤4 := by
 classical
 by_cases sub : Q⊆horizon
 · exact (Finset.card_image_le.trans (Finset.card_le_card sub)).trans (by decide : horizon.card≤4)
 · have pick : ∃ p∈Q, p∉horizon := by
     by_contra! h
     exact sub h
   obtain ⟨p,hp,off⟩ := pick
   have const : Q.image color⊆{color p} := by
     intro x hx
     obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
     obtain ⟨l,hl,eq⟩ := directions p q off
     simpa only [Finset.mem_singleton] using (agree p hp q hq l hl eq).symm
   have hc := Finset.card_le_card const
   simp only [Finset.card_singleton] at hc
   omega
theorem lineComponents {γ : Type} [DecidableEq γ] (Q : Finset L) (color : L → γ)
    (agree : ∀ l∈Q, ∀ k∈Q, ∀ p : P, ed p l → ed p k → color l=color k) :
    (Q.image color).card≤1 := by
 classical
 by_cases non : Q.Nonempty
 · obtain ⟨l,hl⟩ := non
   have const : Q.image color⊆{color l} := by
     intro x hx
     obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
     obtain ⟨p,j,h⟩ := intersections l k
     simpa only [Finset.mem_singleton] using (agree l hl k hk p j h).symm
   simpa using Finset.card_le_card const
 · rw [Finset.not_nonempty_iff_eq_empty.mp non]; simp
theorem connectivityPrice {clean dirty wide distinct marked up ul qp ql prepP prepL dupP dupL total : Nat}
    (pq : 13≤qp+up+wide) (lq : 12≤ql+ul+wide) (cover : up+ul≤clean)
    (rankP : qp≤prepP+4+dupL) (rankL : ql≤prepL+1+dupP)
    (dups : dupP+dupL+distinct≤clean+dirty) (mark1 : marked≤dirty) (mark2 : marked≤distinct)
    (circuit : 2*(clean+dirty+wide)+prepP+prepL≤total+1) :
    19+2*marked≤total := by omega
end PEqualNP.Outside.L_meta_9737.RectangleBank
