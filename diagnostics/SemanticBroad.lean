import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9737.State
open Finset
variable {α β : Type} [DecidableEq α] [DecidableEq β]
abbrev Sig (β : Type) := (β → Bool) → Bool
def singleton (q : β) : β→Bool := fun j => decide (j=q)
def exterior (N : α→ Finset β) (p : α) : β→Bool := fun j => decide (j∉N p)
def OR (f g : Sig β) : Sig β := fun x => f x || g x
def AND (f g : Sig β) : Sig β := fun x => f x && g x
def inc (f : Sig β) := ∀ x y : β→Bool,(∀ i,x i=true → y i=true) → f x=true → f y=true
def broad (N : α→Finset β) (f : Sig β) := ∀ p, f (exterior N p)=true
def bounds (N : α→Finset β) (K : Finset α) (f : Sig β) :=
 ∀ j, f (singleton j)=true → ∃ p∈K,j∈N p
inductive Trace (N : α→Finset β) : List (Sig β) → Nat → Prop where
 | base (l : List (Sig β)) (mon : ∀ f∈l, inc f) (raw : ∀ f∈l, ¬broad N f) : Trace N l 0
 | meet {l n} {f g : Sig β} (b : Trace N l n) (hf : f∈l) (hg : g∈l) : Trace N (AND f g::l) n
 | join {l n} {f g : Sig β} (b : Trace N l n) (hf : f∈l) (hg : g∈l) (h : ¬broad N (OR f g)) :
   Trace N (OR f g::l) n
 | spread {l n} {f g : Sig β} (b : Trace N l n) (hf : f∈l) (hg : g∈l) :
   Trace N (OR f g::l) (n+1)
theorem monotones {N : α→Finset β} {l n} (b : Trace N l n) : ∀ f∈l,inc f := by
 induction b with
 | base l m _ => exact m
 | @meet l n u v b hf hg ih =>
   intro w hv
   rcases List.mem_cons.mp hv with eq|p
   · subst w
     intro x y le hit
     obtain ⟨a,c⟩ : u x=true ∧ v x=true := by simpa [AND] using hit
     simp [AND,ih _ hf x y le a,ih _ hg x y le c]
   · exact ih w p
 | @join l n u v b hf hg h ih =>
   intro w hv
   rcases List.mem_cons.mp hv with eq|p
   · subst w
     intro x y le hit
     rcases (show u x=true ∨ v x=true by simpa [OR] using hit) with a|c
     · simp [OR,ih _ hf x y le a]
     · simp [OR,ih _ hg x y le c]
   · exact ih w p
 | @spread l n u v b hf hg ih =>
   intro w hv
   rcases List.mem_cons.mp hv with eq|p
   · subst w
     intro x y le hit
     rcases (show u x=true ∨ v x=true by simpa [OR] using hit) with a|c
     · simp [OR,ih _ hf x y le a]
     · simp [OR,ih _ hg x y le c]
   · exact ih w p
theorem source {N : α→Finset β} {f : Sig β} {K : Finset α} (m : inc f)
    (old : broad N f → bounds N K f) :
    ∃ k : Finset α, k.card≤1 ∧ bounds N (K∪k) f := by
 classical
 by_cases b : broad N f
 · exact ⟨∅,by simp,by simpa using old b⟩
 · obtain ⟨p,off⟩ : ∃ p,f (exterior N p)≠true := by
     by_contra! h
     exact b h
   refine ⟨{p},by simp,?_⟩
   intro j on
   refine ⟨p,by simp,?_⟩
   by_contra ne
   refine off (m _ _ ?_ on)
   intro t yes
   have tj : t=j := by simpa [singleton] using yes
   simpa [exterior,tj] using ne
theorem palette {N : α→Finset β} {l n} (b : Trace N l n) :
    ∃ K : Finset α,K.card≤2*n ∧ ∀ f∈l,broad N f → bounds N K f := by
 classical
 induction b with
 | base l mon raw => exact ⟨∅,by simp,fun f hf h => False.elim (raw f hf h)⟩
 | @meet l n u v b hf hg ih =>
   obtain ⟨K,c,old⟩ := ih
   refine ⟨K,c,?_⟩
   intro f h hbr
   rcases List.mem_cons.mp h with eq|prior
   · subst f
     have left : broad N u := by
       intro p
       have pair : u (exterior N p)=true ∧ v (exterior N p)=true := by simpa [AND] using hbr p
       exact pair.1
     intro j on
     have pair : u (singleton j)=true ∧ v (singleton j)=true := by simpa [AND] using on
     exact old _ hf left j pair.1
   · exact old f prior hbr
 | join b hf hg notBroad ih =>
   obtain ⟨K,c,old⟩ := ih
   refine ⟨K,c,?_⟩
   intro f h br
   rcases List.mem_cons.mp h with eq|prior
   · subst f
     exact False.elim (notBroad br)
   · exact old f prior br
 | @spread l n u v b hf hg ih =>
   obtain ⟨K,c,old⟩ := ih
   obtain ⟨a,ca,ha⟩ := source (monotones b _ hf) (old _ hf)
   obtain ⟨d,cd,hd⟩ := source (monotones b _ hg) (old _ hg)
   refine ⟨(K∪a)∪d,?_,?_⟩
   · have x := card_union_le K a
     have y := card_union_le (K∪a) d
     omega
   · intro f h br j on
     rcases List.mem_cons.mp h with eq|prior
     · subst f
       rcases (show u (singleton j)=true ∨ v (singleton j)=true by simpa [OR] using on) with left|right
       · obtain ⟨p,hp,hj⟩ := ha j left
         exact ⟨p,mem_union_left _ hp,hj⟩
       · obtain ⟨p,hp,hj⟩ := hd j right
         refine ⟨p,?_,hj⟩
         rcases mem_union.mp hp with z|z
         · exact mem_union_left _ (mem_union_left _ z)
         · exact mem_union_right _ z
     · obtain ⟨p,hp,hj⟩ := old f prior br j on
       exact ⟨p,mem_union_left _ (mem_union_left _ hp),hj⟩
end PEqualNP.Outside.L_meta_9737.State
