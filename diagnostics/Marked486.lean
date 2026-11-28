import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8869.Geometry
open Finset
theorem mul_self_sub_self (n : ℕ) : n * n - n = n * (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h1 : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
    have h2 : k + 1 - 1 = k := by omega
    rw [h1, h2, Nat.add_sub_cancel]

theorem offDiag_card_eq {α : Type*} [DecidableEq α] (s : Finset α) :
    s.offDiag.card = s.card * (s.card - 1) := by
  rw [Finset.offDiag_card]
  exact mul_self_sub_self s.card

theorem sq_eq_add_mul_pred (n : ℕ) : n ^ 2 = n + n * (n - 1) := by
  by_cases hn : n = 0
  · subst hn
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : k + 1 - 1 = k := by omega
    rw [hk]
    ring

theorem card_filter_product_eq_sum {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (X : Finset A) (Y : Finset B) :
    ((X ×ˢ Y).filter (fun p => p ∈ E)).card =
      ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card := by
  have hS : (X ×ˢ Y).filter (fun p => p ∈ E) =
      X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      exact ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩
    · rintro ⟨a', ha', b', ⟨hb', hab'⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨⟨ha', hb'⟩, hab'⟩
  have hdisj : (X : Set A).PairwiseDisjoint
      (fun a => (Y.filter (fun b => (a, b) ∈ E)).image (fun b => (a, b))) := by
    intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [Finset.mem_image, Finset.mem_filter] at hp₁ hp₂
    obtain ⟨b₁, _, h₁⟩ := hp₁
    obtain ⟨b₂, _, h₂⟩ := hp₂
    exact hne (Prod.mk.inj (h₁.trans h₂.symm)).1
  rw [hS, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_image_of_injective]
  exact fun b₁ b₂ h => (Prod.mk.inj h).2

theorem sum_pairs_le_offDiag {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B))
    (hE : ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (X : Finset A) (Y : Finset B) :
    ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card *
        ((Y.filter (fun b => (a, b) ∈ E)).card - 1) ≤
      Y.card * (Y.card - 1) := by
  have hdisj : (X : Set A).PairwiseDisjoint
      (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag) := by
    intro a₁ _ a₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    simp only [Finset.mem_offDiag, Finset.mem_filter] at hq₁ hq₂
    have hqne : q.1 ≠ q.2 := by tauto
    have h11 : (a₁, q.1) ∈ E := by tauto
    have h12 : (a₁, q.2) ∈ E := by tauto
    have h21 : (a₂, q.1) ∈ E := by tauto
    have h22 : (a₂, q.2) ∈ E := by tauto
    exact hE a₁ a₂ q.1 q.2 hne hqne ⟨h11, h12, h21, h22⟩
  have hsub : X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag) ⊆ Y.offDiag := by
    rw [Finset.biUnion_subset]
    intro a _ q hq
    simp only [Finset.mem_offDiag, Finset.mem_filter] at hq ⊢
    tauto
  calc
    ∑ a ∈ X, (Y.filter (fun b => (a, b) ∈ E)).card *
        ((Y.filter (fun b => (a, b) ∈ E)).card - 1) =
      ∑ a ∈ X, ((Y.filter (fun b => (a, b) ∈ E)).offDiag).card := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (offDiag_card_eq (Y.filter (fun b => (a, b) ∈ E))).symm
    _ = (X.biUnion (fun a => (Y.filter (fun b => (a, b) ∈ E)).offDiag)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ Y.offDiag.card := Finset.card_le_card hsub
    _ = Y.card * (Y.card - 1) := offDiag_card_eq Y

theorem tangent (k : Nat) : 30*k≤k*(k-1)+240 := by
  by_cases h : k≤15
  · interval_cases k <;> decide
  · obtain ⟨x,rfl⟩ : ∃ x,k=x+16 := ⟨k-16,by omega⟩
    have e : x+16-1=x+15 := by omega
    rw [e]
    nlinarith [Nat.zero_le (x*x)]

theorem sparse_side {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (X : Finset A) (Y : Finset B) (sub : E ⊆ X ×ˢ Y)
    (four : ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (yp : 0<Y.card) (ys : Y.card≤240) : E.card+8≤8*(X.card+Y.card) := by
  classical
  let d (a : A) := (Y.filter (fun b => (a,b)∈E)).card
  have el : (X ×ˢ Y).filter (fun e => e ∈ E)=E := by ext e; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
  have summ : E.card=∑ a ∈ X,d a := el ▸ card_filter_product_eq_sum E X Y
  have pairs := sum_pairs_le_offDiag E four X Y
  change ∑ a ∈ X,d a*(d a-1) ≤ Y.card*(Y.card-1) at pairs
  have budget := Finset.sum_le_sum (s:=X) (fun a _ => tangent (d a))
  rw [←Finset.mul_sum,←summ,Finset.sum_add_distrib] at budget
  simp only [Finset.sum_const,Nat.nsmul_eq_mul] at budget
  have last := Nat.mul_le_mul_right (Y.card-1) ys
  have diff : 240*(Y.card-1)+240=240*Y.card := by
    have := Nat.sub_add_cancel (show 1≤Y.card from yp)
    nlinarith
  omega

def SquareFree {A B : Type} (E : Finset (A × B)) : Prop :=
  ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' → ¬ ((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E)

theorem sparse_either {A B : Type} [DecidableEq A] [DecidableEq B] (E : Finset (A × B))
    (four : SquareFree E) (non : E.Nonempty)
    (small : (E.image Prod.fst).card≤240 ∨ (E.image Prod.snd).card≤240) :
    E.card+8≤8*((E.image Prod.fst).card+(E.image Prod.snd).card) := by
  classical
  let X := E.image Prod.fst
  let Y := E.image Prod.snd
  have sub : E ⊆ X ×ˢ Y := fun e he => mem_product.mpr ⟨mem_image_of_mem _ he,mem_image_of_mem _ he⟩
  obtain ⟨e,he⟩ := non
  rcases small with left|right
  · let D := E.image Prod.swap
    have dm (a : A) (b : B) : (b,a)∈D ↔ (a,b)∈E := by
      simp only [D,mem_image,Prod.exists,Prod.swap_prod_mk,Prod.mk.injEq]
      aesop
    have ds : D ⊆ Y ×ˢ X := by
      rintro ⟨b,a⟩ h
      obtain ⟨u,v⟩ := mem_product.mp (sub ((dm a b).mp h))
      exact mem_product.mpr ⟨v,u⟩
    have df : SquareFree D := by
      rintro b b' a a' ne ne' ⟨one,two,three,last⟩
      exact four a a' b b' ne' ne ⟨(dm _ _).mp one,(dm _ _).mp three,(dm _ _).mp two,(dm _ _).mp last⟩
    have upper := sparse_side D Y X ds df (card_pos.mpr ⟨e.1,(mem_product.mp (sub he)).1⟩) left
    have eq : D.card=E.card := card_image_of_injective _ (fun x y h => by simpa using congrArg Prod.swap h)
    change E.card+8≤8*(X.card+Y.card)
    omega
  · exact sparse_side E X Y sub four (card_pos.mpr ⟨e.2,(mem_product.mp (sub he)).2⟩) right
end PEqualNP.Outside.L_meta_8869.Geometry

namespace PEqualNP.Outside.L_meta_8869.Geometry
open Finset
theorem marked_side {A B : Type} [DecidableEq A] [DecidableEq B]
    (E : Finset (A × B)) (X : Finset A) (Y : Finset B) (sub : E ⊆ X ×ˢ Y)
    (four : ∀ a a' : A, ∀ b b' : B, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (yp : 0<Y.card) (ys : Y.card≤242) : E.card≤8*(X.card+Y.card+1) := by
  classical
  let d (a : A) := (Y.filter (fun b => (a,b)∈E)).card
  have el : (X ×ˢ Y).filter (fun e => e ∈ E)=E := by ext e; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
  have summ : E.card=∑ a ∈ X,d a := el ▸ card_filter_product_eq_sum E X Y
  have pairs := sum_pairs_le_offDiag E four X Y
  change ∑ a ∈ X,d a*(d a-1) ≤ Y.card*(Y.card-1) at pairs
  have budget := Finset.sum_le_sum (s:=X) (fun a _ => tangent (d a))
  rw [←Finset.mul_sum,←summ,Finset.sum_add_distrib] at budget
  simp only [Finset.sum_const,Nat.nsmul_eq_mul] at budget
  have last := Nat.mul_le_mul_right (Y.card-1) ys
  have diff : 242*(Y.card-1)+242=242*Y.card := by
    have := Nat.sub_add_cancel (show 1≤Y.card from yp)
    nlinarith
  omega

theorem marked_either {A B : Type} [DecidableEq A] [DecidableEq B] (E : Finset (A × B))
    (four : SquareFree E) (non : E.Nonempty)
    (small : (E.image Prod.fst).card≤242 ∨ (E.image Prod.snd).card≤242) :
    E.card≤8*((E.image Prod.fst).card+(E.image Prod.snd).card+1) := by
  classical
  let X := E.image Prod.fst
  let Y := E.image Prod.snd
  have sub : E ⊆ X ×ˢ Y := fun e he => mem_product.mpr ⟨mem_image_of_mem _ he,mem_image_of_mem _ he⟩
  obtain ⟨e,he⟩ := non
  rcases small with left|right
  · let D := E.image Prod.swap
    have dm (a : A) (b : B) : (b,a)∈D ↔ (a,b)∈E := by
      simp only [D,mem_image,Prod.exists,Prod.swap_prod_mk,Prod.mk.injEq]
      aesop
    have ds : D ⊆ Y ×ˢ X := by
      rintro ⟨b,a⟩ h
      obtain ⟨u,v⟩ := mem_product.mp (sub ((dm a b).mp h))
      exact mem_product.mpr ⟨v,u⟩
    have df : SquareFree D := by
      rintro b b' a a' ne ne' ⟨one,two,three,last⟩
      exact four a a' b b' ne' ne ⟨(dm _ _).mp one,(dm _ _).mp three,(dm _ _).mp two,(dm _ _).mp last⟩
    have upper := marked_side D Y X ds df (card_pos.mpr ⟨e.1,(mem_product.mp (sub he)).1⟩) left
    have eq : D.card=E.card := card_image_of_injective _ (fun x y h => by simpa using congrArg Prod.swap h)
    change E.card≤8*(X.card+Y.card+1)
    omega
  · exact marked_side E X Y sub four (card_pos.mpr ⟨e.2,(mem_product.mp (sub he)).2⟩) right
end PEqualNP.Outside.L_meta_8869.Geometry

namespace PEqualNP.Outside.L_meta_8869.Donor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

variable {n : Nat} {C : Circuit}

theorem binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
theorem opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
theorem opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
end PEqualNP.Outside.L_meta_8869.Donor
namespace PEqualNP.Outside.L_meta_8869.Overlap
open Finset
open Finset in
theorem colors {n} (f : Nat → Fin n × Fin n) (S : Finset Nat) :
    ∃ c : Fin n → Fin n, (∀ j∈S,c (f j).1=c (f j).2) ∧
      n≤S.card+(univ.image c).card := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨id,by simp,by simp⟩
  | @insert j S hj ih =>
    obtain ⟨c,ok,cnt⟩ := ih
    let a := c (f j).1
    let b := c (f j).2
    let up := fun z : Fin n => if z=a then b else z
    let d := up ∘ c
    refine ⟨d,?_,?_⟩
    · intro k hk
      rcases mem_insert.mp hk with rfl|hh
      · change up a=up b
        simp [up]
      · exact congrArg up (ok k hh)
    · have sub : univ.image c ⊆ insert a (univ.image d) := by
        intro t ht
        obtain ⟨u,_,rfl⟩ := mem_image.mp ht
        by_cases eq : c u=a
        · exact mem_insert.mpr (.inl eq)
        · exact mem_insert_of_mem (mem_image.mpr ⟨u,mem_univ _,by simp [d,up,eq]⟩)
      have h := (card_le_card sub).trans (card_insert_le _ _)
      rw [card_insert_of_notMem hj]
      omega

open Finset in
theorem graph_count {n : ℕ} (S : Finset ℕ) (f : ℕ → Fin n × Fin n) (X : Finset (Fin n))
    (hX : ∀ c : Fin n → Fin n, (∀ j∈S,c (f j).1=c (f j).2) →
      ∀ u ∈ X, ∀ v ∈ X, c u=c v) : X.card≤S.card+1 := by
  classical
  rcases X.eq_empty_or_nonempty with rfl|⟨v,hv⟩
  · simp
  obtain ⟨c,ok,hc⟩ := colors f S
  have sub : univ.image c⊆insert (c v) ((univ\X).image c) := by
    intro t ht
    obtain ⟨u,_,rfl⟩ := mem_image.mp ht
    by_cases hu : u∈X
    · exact mem_insert.mpr (.inl (hX c ok u hu v hv))
    · exact mem_insert_of_mem (mem_image.mpr ⟨u,mem_sdiff.mpr ⟨mem_univ _,hu⟩,rfl⟩)
  have hc' := (card_le_card sub).trans (card_insert_le _ _)
  have imgs : ((univ\X).image c).card≤(univ\X).card := card_image_le
  have add := card_sdiff_add_card_eq_card (subset_univ X)
  simp only [card_univ,Fintype.card_fin] at add
  omega

theorem overlap_cost {n s : Nat} (V : Nat → Finset (Fin n)) (a b : Nat → Nat)
    (raw : ∀ w<n,(V w).card≤1) (back : ∀ j<s,a j<n+j ∧ b j<n+j)
    (cont : ∀ j<s,V (n+j)⊆ V (a j) ∪ V (b j)) (w : Nat) (valid : w<n+s) :
    (V w).card + ((range s).filter (fun j => ((V (a j)) ∩ (V (b j))).Nonempty)).card ≤ s+1 := by
  classical
  let common (j : Nat) := ((V (a j)) ∩ (V (b j))).Nonempty
  let F := (range s).filter (fun j => ¬common j)
  have card : F.card+((range s).filter common).card=s := by
    rw [Nat.add_comm]
    simpa only [card_range] using card_filter_add_card_filter_not (s:=range s) common
  by_cases hv : (V w).Nonempty
  · obtain ⟨defaultValue,_⟩ := hv
    let repr (v : Nat) := if h : (V v).Nonempty then h.choose else defaultValue
    have repr_mem {v : Nat} (h : (V v).Nonempty) : repr v∈V v := by simpa [repr,h] using h.choose_spec
    let tag (j : Nat) := (repr (a j),repr (b j))
    have lower := graph_count F tag (V w) (by
      intro color glue
      have reach (v : Nat) : v<n+s → ∀ i∈V v,∀ k∈V v,color i=color k := by
        induction v using Nat.strong_induction_on with
        | ind v ih =>
          intro lim i hi k hk
          by_cases early : v<n
          · rw [Finset.card_le_one.mp (raw v early) _ hi _ hk]
          · obtain ⟨j,rfl⟩ : ∃ j,v=n+j := ⟨v-n,by omega⟩
            have js : j<s := by omega
            obtain ⟨la,lb⟩ := back j js
            have left := ih (a j) la (by omega)
            have right := ih (b j) lb (by omega)
            have across (i : Fin n) (ia : i∈V (a j)) (k : Fin n) (kb : k∈V (b j)) : color i=color k := by
              by_cases overlap : common j
              · obtain ⟨z,hz⟩ := overlap
                obtain ⟨za,zb⟩ := mem_inter.mp hz
                exact (left i ia z za).trans (right z zb k kb)
              · have joint := glue j (mem_filter.mpr ⟨mem_range.mpr js,overlap⟩)
                exact (left i ia _ (repr_mem ⟨i,ia⟩)).trans (joint.trans (right _ (repr_mem ⟨k,kb⟩) k kb))
            rcases mem_union.mp (cont j js hi) with ia|ib <;> rcases mem_union.mp (cont j js hk) with ka|kb
            · exact left _ ia _ ka
            · exact across _ ia _ kb
            · exact (across _ ka _ ib).symm
            · exact right _ ib _ kb
      exact reach w valid)
    change (V w).card+((range s).filter common).card≤s+1
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hv,card_empty,zero_add]
    change ((range s).filter common).card≤s+1
    omega

end PEqualNP.Outside.L_meta_8869.Overlap
namespace PEqualNP.Outside.L_meta_8869
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge Finset
open Classical in
noncomputable def sensitive (m : Nat) (C : Circuit) (w : Nat) : Finset (Fin m) := univ.filter (fun i =>
  ∃ x y : Fin m → Bool,(∀ j,j≠i → x j=y j) ∧ wireVal m C w x≠wireVal m C w y)

theorem sensitive_iff {m : Nat} (C : Circuit) (w : Nat) (i : Fin m) : i∈sensitive m C w ↔
    ∃ x y : Fin m → Bool,(∀ j,j≠i → x j=y j) ∧ wireVal m C w x≠wireVal m C w y := by
  classical
  simp [sensitive]

noncomputable def overlap (m : Nat) (C : Circuit) : Finset Nat :=
  (range C.size).filter (fun j => ((sensitive m C (opnd C j 0)) ∩ sensitive m C (opnd C j 1)).Nonempty)

theorem gate_fun {m : Nat} (C : Circuit) (ao : IsAO2 m C) (j : Nat) (hj : j<C.size) (x : Fin m → Bool) :
    wireVal m C (m+j) x=(gateAt C j).op.eval [wireVal m C (opnd C j 0) x,wireVal m C (opnd C j 1) x] := by
  obtain ⟨a,b,ins⟩ := Donor.binaryInputs ao hj
  have la := ao.2.1 j hj a (by simp [ins])
  have lb := ao.2.1 j hj b (by simp [ins])
  change Donor.val C (List.ofFn x) (m+j)=_
  rw [Donor.val_gate (n:=m) (by simp) hj]
  simp [opnd,ins,la,lb,wireVal,Donor.val]

theorem marked_cost {m : Nat} (C : Circuit) (ao : IsAO2 m C) (w : Nat) (hw : w<m+C.size) :
    (sensitive m C w).card+(overlap m C).card≤C.size+1 := by
  classical
  apply Overlap.overlap_cost (s:=C.size) (sensitive m C) (fun j => opnd C j 0) (fun j => opnd C j 1) _ _ _ w hw
  · intro t ht
    apply card_le_one.mpr
    have unique {i : Fin m} (hi : i∈sensitive m C t) : i=⟨t,ht⟩ := by
      obtain ⟨x,y,agree,ne⟩ := (sensitive_iff ..).mp hi
      by_contra diff
      apply ne
      change Donor.val C (List.ofFn x) t=Donor.val C (List.ofFn y) t
      simpa only [Donor.val_ofFn C x ⟨t,ht⟩,Donor.val_ofFn C y ⟨t,ht⟩] using agree ⟨t,ht⟩ diff.symm
    exact fun i hi k hk => (unique hi).trans (unique hk).symm
  · intro j hj
    exact ⟨Donor.opndBound ao hj 0,Donor.opndBound ao hj 1⟩
  · intro j hj i hi
    obtain ⟨x,y,agree,ne⟩ := (sensitive_iff ..).mp hi
    by_contra miss
    apply ne
    rw [gate_fun C ao j hj,gate_fun C ao j hj]
    have eq (b : Fin 2) (no : i∉sensitive m C (opnd C j b)) :
        wireVal m C (opnd C j b) x=wireVal m C (opnd C j b) y := by
      by_contra uneq
      exact no ((sensitive_iff ..).mpr ⟨x,y,agree,uneq⟩)
    rw [eq 0 (fun h => miss (mem_union_left _ h)),eq 1 (fun h => miss (mem_union_right _ h))]

theorem mark_overlap {m : Nat} (C : Circuit) (ao : IsAO2 m C) (x y : Fin m → Bool) (i : Fin m) (j : Nat)
    (bound : j<C.size) (op : (gateAt C j).op=GateOp.and) (on : wireVal m C (m+j) x=true)
    (agree : ∀ r,r≠i → x r=y r) (both : ∀ b : Fin 2,wireVal m C (opnd C j b) y=false) :
    j∈overlap m C := by
  classical
  rw [gate_fun C ao j bound,op] at on
  simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true,Bool.and_eq_true] at on
  have spec (b : Fin 2) (h : wireVal m C (opnd C j b) x=true) : i∈sensitive m C (opnd C j b) := by
    refine (sensitive_iff ..).mpr ⟨x,y,agree,?_⟩
    rw [h,both]
    decide
  exact mem_filter.mpr ⟨mem_range.mpr bound,i,mem_inter.mpr ⟨spec 0 on.1,spec 1 on.2⟩⟩

abbrev pair {n : Nat} (e : Fin n × Fin n) (r : Fin (n+n)) := decide (r=Fin.castAdd n e.1 ∨ r=Fin.natAdd n e.2)
abbrev quiet {n : Nat} (q : Nat) (R : Fin n → Fin n → Prop) (C : Circuit) := ∀ x : Fin (n+n) → Bool,
  Fintype.card {l : Fin n // x (Fin.natAdd n l)=true} ≤ q →
    (¬∃ p l,R p l ∧ x (Fin.castAdd n p)=true ∧ x (Fin.natAdd n l)=true) → wireVal (n+n) C C.output x=false

theorem single_off {n q : Nat} {R : Fin n → Fin n → Prop} {C : Circuit} (hq : 1≤q) (sound : quiet q R C)
    (v : Fin (n+n)) : wireVal (n+n) C C.output (fun r => decide (r=v))=false := by
  apply sound
  · apply le_trans _ hq
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor
    intro a b
    apply Subtype.ext
    exact Fin.natAdd_injective _ _ ((of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm)
  · rintro ⟨p,l,_,hv,hw⟩
    have eq := (of_decide_eq_true hv).trans (of_decide_eq_true hw).symm
    have h : p.val=n+l.val := congrArg Fin.val eq
    have := p.isLt
    omega

abbrev liveStep {m : Nat} (C : Circuit) (x : Fin m → Bool) (w w' : Nat) : Prop :=
  ∃ k<C.size,w'=m+k ∧ w∈(gateAt C k).inputs ∧ wireVal m C w x=true ∧ wireVal m C w' x=true

theorem first_on {m : Nat} {C : Circuit} {x : Fin m → Bool} {w u : Nat}
    (h : Relation.ReflTransGen (liveStep C x) w u) (yes : wireVal m C u x=true) : wireVal m C w x=true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact yes
  | head step _ _ => obtain ⟨_,_,_,_,hw,_⟩ := step; exact hw

theorem both_marks {n : Nat} (C : Circuit) (ao : IsAO2 (n+n) C) {p l : Fin n} {j k : Nat}
    (accept : wireVal (n+n) C C.output (pair (p,l))=true) (ne : j≠k)
    (jok : j<C.size ∧ (gateAt C j).op=GateOp.and ∧ Relation.ReflTransGen (liveStep C (pair (p,l))) (n+n+j) C.output ∧
      ∀ b : Fin 2,wireVal (n+n) C (opnd C j b) (fun r => decide (r=Fin.castAdd n p))=false)
    (kok : k<C.size ∧ (gateAt C k).op=GateOp.and ∧ Relation.ReflTransGen (liveStep C (pair (p,l))) (n+n+k) C.output ∧
      ∀ b : Fin 2,wireVal (n+n) C (opnd C k b) (fun r => decide (r=Fin.natAdd n l))=false) :
    2≤(overlap (n+n) C).card := by
  classical
  have jmem := mark_overlap C ao (pair (p,l)) _ (Fin.natAdd n l) j jok.1 jok.2.1 (first_on jok.2.2.1 accept)
    (fun r hr => by simp only [pair,Prod.fst,Prod.snd,hr,false_or,or_false]) jok.2.2.2
  have kmem := mark_overlap C ao (pair (p,l)) _ (Fin.castAdd n p) k kok.1 kok.2.1 (first_on kok.2.2.1 accept)
    (fun r hr => by simp only [pair,Prod.fst,Prod.snd,hr,false_or,or_false]) kok.2.2.2
  exact one_lt_card.mpr ⟨j,jmem,k,kmem,ne⟩

theorem essential_endpoints {n q : Nat} {R : Fin n → Fin n → Prop} {C : Circuit}
    (E : Finset (Fin n × Fin n)) (hq : 1≤q) (sound : quiet q R C) (on : ∀ e∈E,wireVal (n+n) C C.output (pair e)=true) :
    (E.image Prod.fst).card+(E.image Prod.snd).card≤(sensitive (n+n) C C.output).card := by
  classical
  let P := (E.image Prod.fst).image (Fin.castAdd n)
  let L := (E.image Prod.snd).image (Fin.natAdd n)
  have dis : Disjoint P L := by
    rw [Finset.disjoint_left]
    intro u hp hl
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨l,_,eq⟩ := Finset.mem_image.mp hl
    have h := congrArg Fin.val eq
    change n+l.val=p.val at h
    omega
  have all : P∪L ⊆ sensitive (n+n) C C.output := by
    intro i hi
    apply (sensitive_iff ..).mpr
    rcases Finset.mem_union.mp hi with pin|lin
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp pin
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨pair e, fun r => decide (r=Fin.natAdd n e.2), fun z hz => by simp only [pair,hz,false_or,or_false],by rw [on e he,single_off hq sound (Fin.natAdd n e.2)]; decide⟩
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp lin
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨pair e, fun r => decide (r=Fin.castAdd n e.1), fun z hz => by simp only [pair,hz,false_or,or_false],by rw [on e he,single_off hq sound (Fin.castAdd n e.1)]; decide⟩
  have bound := card_le_card all
  rw [card_union_of_disjoint dis] at bound
  simpa only [P,L,card_image_of_injective _ (Fin.castAdd_injective n n),card_image_of_injective _ (Fin.natAdd_injective n n)] using bound
theorem exact486 (q n : Nat) (R : Fin n → Fin n → Prop) [DecidableRel R] (C : Circuit)
    (E : Finset (Fin n × Fin n)) (hq : 1≤q) (joinp : ∀ p t,p≠t → ∃! l,R p l ∧ R t l)
    (ao : IsAO2 (n+n) C) (sound : quiet q R C)
    (edges : ∀ e∈E,R e.1 e.2 ∧ wireVal (n+n) C C.output (pair e)=true ∧
       ∃ j k,j≠k ∧ (j<C.size ∧ (gateAt C j).op=GateOp.and ∧ Relation.ReflTransGen (liveStep C (pair e)) (n+n+j) C.output ∧
       ∀ b : Fin 2,wireVal (n+n) C (opnd C j b) (fun r => decide (r=Fin.castAdd n e.1))=false) ∧
       (k<C.size ∧ (gateAt C k).op=GateOp.and ∧ Relation.ReflTransGen (liveStep C (pair e)) (n+n+k) C.output ∧
       ∀ b : Fin 2,wireVal (n+n) C (opnd C k b) (fun r => decide (r=Fin.natAdd n e.2))=false))
    (small : (E.image Prod.fst).card≤242 ∨ (E.image Prod.snd).card≤242 ∨ C.size≤486) :
    E.card≤8*C.size := by
  classical
  by_cases non : E.Nonempty
  · obtain ⟨e,he⟩ := non
    have on (e) (he : e∈E) := (edges e he).2.1
    have valid : C.output<n+n+C.size := by
      by_contra! bad
      have no := Donor.val_ge (C:=C) (by simp : (List.ofFn (pair e)).length=n+n) bad
      have yes := on e he
      change Donor.val C (List.ofFn (pair e)) C.output=true at yes
      rw [no] at yes
      cases yes
    have four : Geometry.SquareFree E := by
      rintro a a' b b' an bn ⟨ab,ab',a'b,a'b'⟩
      obtain ⟨l,_,only⟩ := joinp a a' an
      exact bn ((only b ⟨(edges _ ab).1,(edges _ a'b).1⟩).trans (only b' ⟨(edges _ ab').1,(edges _ a'b').1⟩).symm)
    obtain ⟨j,k,ne,markj,markk⟩ := (edges e he).2.2
    have two := both_marks C ao (on e he) ne markj markk
    have endpoints := essential_endpoints E hq sound on
    have price := marked_cost C ao C.output valid
    have small' : (E.image Prod.fst).card≤242 ∨ (E.image Prod.snd).card≤242 := by omega
    have geo := Geometry.marked_either E four ⟨e,he⟩ small'
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp non]
end PEqualNP.Outside.L_meta_8869
