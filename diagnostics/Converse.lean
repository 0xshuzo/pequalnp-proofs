import Mathlib
import PEqualNP.Defs

namespace PairVariation3501

abbrev Fam (n : ℕ) := Finset (Finset (Fin (n+n)))
def sat {n : ℕ} (A : Fam n) (test : ℕ → Prop) : Prop := ∀ t∈A, ∃ z∈t, test z.val
def pair {n : ℕ} (A : Fam n) (i j : ℕ) := sat A fun z => z=i ∨ z=j

def changes {n : ℕ} (A : Fam n) (color : ℕ → Bool) (d : Bool) :=
  ∃ fix : ℕ → Bool, ¬sat A (fun z => color z≠d ∧ fix z=true) ∧
    sat A (fun z => color z=d ∨ fix z=true)

theorem inc {n : ℕ} {A : Fam n} {P Q : ℕ → Prop} (m : ∀ i, P i → Q i) :
    sat A P → sat A Q := by
  intro h t ht
  obtain ⟨z,hz,p⟩ := h t ht
  exact ⟨z,hz,m _ p⟩

theorem single {n : ℕ} {A : Fam n} (live : A.Nonempty) (color : ℕ → Bool) (u : ℕ)
    (yes : pair A u u) : changes A color (color u) := by
  refine ⟨fun _ => false,?_,?_⟩
  · obtain ⟨t,ht⟩ := live
    intro on
    obtain ⟨_,_,_,bad⟩ := on t ht
    contradiction
  · exact inc (fun i (h : i=u ∨ i=u) => Or.inl (congrArg color (h.elim id id))) yes

theorem same {n : ℕ} {A : Fam n} (live : A.Nonempty) (color : ℕ → Bool) (u v : ℕ)
    (eq : color u=color v) (yes : pair A u v) : changes A color (color u) := by
  refine ⟨fun _ => false,?_,?_⟩
  · obtain ⟨t,ht⟩ := live
    intro on
    obtain ⟨_,_,_,bad⟩ := on t ht
    contradiction
  · apply inc _ yes
    intro i h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl eq.symm

theorem addOne {n : ℕ} {A : Fam n} (color : ℕ → Bool) (u v : ℕ)
    (yes : pair A u v) (no : ¬pair A v v) : changes A color (color u) := by
  refine ⟨fun z => decide (z=v),?_,?_⟩
  · intro low
    exact no (inc (fun z (h : _ ∧ decide (z=v)=true) => Or.inl (of_decide_eq_true h.2)) low)
  · apply inc _ yes
    intro z h
    rcases h with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (by simp)

theorem flipPair {n : ℕ} {A : Fam n} {u v : ℕ} (p : pair A u v) : pair A v u :=
  inc (fun _ h => h.symm) p

theorem commonSide {n : ℕ} {A B : Fam n} (aLive : A.Nonempty) (bLive : B.Nonempty) (color : ℕ → Bool)
    (bad : (∃ u, pair A u u ∧ pair B u u) ∨
      ∃ u v, pair A u v ∧ pair B u v ∧ ¬((pair A u u ∧ pair B v v) ∨ (pair A v v ∧ pair B u u))) :
    ∃ d, changes A color d ∧ changes B color d := by
  rcases bad with ⟨u,h,k⟩|⟨u,v,h,k,unsplit⟩
  · exact ⟨color u,single aLive color u h,single bLive color u k⟩
  by_cases ax : pair A u u
  · have bn : ¬pair B v v := fun b => unsplit (Or.inl ⟨ax,b⟩)
    exact ⟨color u,single aLive color u ax,addOne color u v k bn⟩
  by_cases by' : pair B v v
  · exact ⟨color v,addOne color v u (flipPair h) ax,single bLive color v by'⟩
  by_cases ay : pair A v v
  · have bx : ¬pair B u u := fun b => unsplit (Or.inr ⟨ay,b⟩)
    exact ⟨color v,single aLive color v ay,addOne color v u (flipPair k) bx⟩
  exact ⟨color u,addOne color u v h ay,addOne color u v k by'⟩

def row (n : ℕ) (d : Bool) (fixed : ℕ → Bool) (c : Bool) : List Bool :=
  if d then List.ofFn (fun p : Fin n => fixed p.val) ++ List.replicate n c
  else List.replicate n c ++ List.ofFn (fun l : Fin n => fixed (n+l.val))

theorem readRow (n : ℕ) (d : Bool) (fixed : ℕ → Bool) (c : Bool) (z : Fin (n+n)) :
    (row n d fixed c).getD z.val false = if decide (n≤z.val)=d then c else fixed z.val := by
  have total := z.isLt
  cases d <;> by_cases h : z.val<n
  · have hn : ¬n≤z.val := by omega
    unfold row
    rw [if_neg (by decide),List.getD_append _ _ _ _ (by simpa using h),List.getD_replicate false h]
    simp [hn]
  · have hn : n≤z.val := by omega
    unfold row
    rw [if_neg (by decide),List.getD_append_right _ _ _ _ (by simpa using hn)]
    have hlt : z.val-n<n := by omega
    have hz : n+(z.val-n)=z.val := by omega
    simp [hn,hlt,hz]
  · have hn : ¬n≤z.val := by omega
    unfold row
    rw [if_pos (by decide),List.getD_append _ _ _ _ (by simpa using h)]
    simp [h,hn]
  · have hn : n≤z.val := by omega
    unfold row
    rw [if_pos (by decide),List.getD_append_right _ _ _ _ (by simpa using hn)]
    have lt : z.val-n<n := by omega
    simp only [List.length_ofFn]
    rw [List.getD_replicate false lt]
    simp [hn]

theorem advertised {n : ℕ} (A : Fam n) (d : Bool) (h : changes A (fun i => decide (n≤i)) d) :
    ∃ z : Fin n → Bool,
      let probe (c : Bool) := if d=true then List.ofFn z ++ List.replicate n c
        else List.replicate n c ++ List.ofFn z
      let hit (c : Bool) := ∀ t∈A, ∃ i∈t, (probe c).getD i.val false=true
      ¬ (hit false ↔ hit true) := by
  obtain ⟨fix,low,high⟩ := h
  let z : Fin n → Bool := fun i => if d then fix i.val else fix (n+i.val)
  refine ⟨z,?_⟩
  have sameRow (c : Bool) : (if d=true then List.ofFn z ++ List.replicate n c
      else List.replicate n c ++ List.ofFn z) = row n d fix c := by cases d <;> rfl
  dsimp only
  intro eq
  apply low
  have yes : ∀ t∈A, ∃ i∈t, (row n d fix true).getD i.val false=true := by
    intro t ht
    obtain ⟨i,hi,ok⟩ := high t ht
    refine ⟨i,hi,?_⟩
    rw [readRow]
    by_cases col : decide (n≤i.val)=d
    · simp [col]
    · simpa [col] using ok.resolve_left col
  have out := eq.mpr (by simpa only [sameRow] using yes)
  intro t ht
  obtain ⟨i,hi,ok⟩ := out t ht
  rw [sameRow,readRow] at ok
  exact ⟨i,hi,by by_cases col : decide (n≤i.val)=d <;> simp_all⟩

theorem nonempty {n s : ℕ} (F : ℕ → Fam n)
    (raw : ∀ i : Fin (n+n), F i={{i}})
    (gates : ∀ g<s, ∃ a b, a<b ∧ b<n+n+g ∧ (F (n+n+g)=F a ∪ F b ∨
      F (n+n+g)=(F a).biUnion (fun u => (F b).image (u ∪ ·)))) :
    ∀ w<n+n+s, (F w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases inside : w<n+n
    · have r := raw ⟨w,inside⟩
      change F w = _ at r
      rw [r]; simp
    let g := w-(n+n)
    have j : n+n+g=w := by dsimp [g];omega
    have gs : g<s := by omega
    obtain ⟨a,b,ab,bb,op⟩ := gates g gs
    rw [j] at bb op
    obtain ⟨x,hx⟩ := ih a (ab.trans bb) ((ab.trans bb).trans hw)
    obtain ⟨y,hy⟩ := ih b bb (bb.trans hw)
    rcases op with u|p
    · exact ⟨x,u ▸ Finset.mem_union_left _ hx⟩
    · exact ⟨x∪y,p ▸ Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr ⟨y,hy,rfl⟩⟩⟩


theorem converse (original : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (250 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Finset (Finset (Fin (x2 + x2)))),             x10 < x2 + x2 + x9 →               (∀ (x13 : Fin (x2 + x2)), x11 ↑x13 = {{x13}}) →                 (∀ x14 < x9, ∃ (x16 : ℕ) (x17 : ℕ), x16 < x17 ∧ x17 < x2 + x2 + x14 ∧ (x11 (x2 + x2 + x14) = x11 x16 ∪ x11 x17 ∨ x11 (x2 + x2 + x14) = (x11 x16).biUnion fun (x18 : Finset (Fin (x2 + x2))) => Finset.image (fun (x19 : Finset (Fin (x2 + x2))) => x18 ∪ x19) (x11 x17))) →                   (∀ x15 ∈ x11 x10, ∀ (x17 x18 : Fin x2), x3 x17 x18 → Fin.castAdd x2 x17 ∈ x15 ∨ Fin.natAdd x2 x18 ∈ x15) →                     (∀ (x16 : Finset (Fin x2)), x16.card ≤ x1 → ∃ x18 ∈ x11 x10, (∀ (x19 : Fin x2), Fin.castAdd x2 x19 ∈ x18 ↔ ∃ x20 ∈ x16, x3 x19 x20) ∧ ∀ (x19 : Fin x2), Fin.natAdd x2 x19 ∈ x18 ↔ x19 ∉ x16) →                       (∃ x17 < x9,                           ∃ (x18 : ℕ) (x19 : ℕ),                             x18 < x19 ∧                               x19 < x2 + x2 + x17 ∧                                 x11 (x2 + x2 + x17) = x11 x18 ∪ x11 x19 ∧                                   ∃ (x20 : Bool),                                     ∀ x21 ∈ [x18, x19],                                       ∃ (x23 : Fin x2 → Bool),                                         have x24 : Bool → List Bool := fun (x24 : Bool) => if x20 = Bool.true then List.ofFn x23 ++ List.replicate x2 x24 else List.replicate x2 x24 ++ List.ofFn x23;                                         have x25 : Bool → Prop := fun (x25 : Bool) => ∀ x26 ∈ x11 x21, ∃ x28 ∈ x26, (x24 x25).getD (↑x28) Bool.false = Bool.true;                                         ¬(x25 Bool.false ↔ x25 Bool.true)) →                         x2 * x1 ≤ (100 : ℕ) * x9) : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (s o : ℕ)
      (F : ℕ → Finset (Finset (Fin (N+N)))),
      let H (w i j : ℕ) := ∀ t ∈ F w, ∃ z ∈ t, z.val=i ∨ z.val=j
      let le (a b : ℕ) := ∀ u v, H a u v → H b u v
      let bad (a b : ℕ) := (∃ u, H a u u ∧ H b u u) ∨
        ∃ u v, H a u v ∧ H b u v ∧ ¬((H a u u ∧ H b v v) ∨ (H a v v ∧ H b u u))
      250≤q → N=q^2+q+1 → (∀ l, Fintype.card {p // I p l}=q+1) →
      (∀ p r : Fin N, p≠r → ∃! l, I p l ∧ I r l) →
      o<N+N+s →
      (∀ i : Fin (N+N), F i={{i}}) →
      (∀ g<s, ∃ a b, a<b ∧ b<N+N+g ∧
        (F (N+N+g) = F a ∪ F b ∨ F (N+N+g) = (F a).biUnion (fun u => (F b).image (u ∪ ·)))) →
      (∀ t ∈ F o, ∀ p l, I p l → Fin.castAdd N p ∈ t ∨ Fin.natAdd N l ∈ t) →
      (∀ Y : Finset (Fin N), Y.card≤q → ∃ t ∈ F o,
        (∀ p, Fin.castAdd N p ∈ t ↔ ∃ l∈Y, I p l) ∧ (∀ l, Fin.natAdd N l ∈ t ↔ l∉Y)) →
      (∃ g<s, ∃ a b, a<b ∧ b<N+N+g ∧ F (N+N+g)=F a∪F b ∧
        ¬le a b ∧ ¬le b a ∧ bad a b) → N*q≤100*s := by
  intro q N I inst s o F H le bad hq hn col join ho leaf gates cover canonical obstruction
  apply original q N I hq hn col join s o F ho leaf gates cover canonical
  obtain ⟨g,hg,a,b,ab,bb,eq,_,_,fault⟩ := obstruction
  have bound : b<N+N+s := by omega
  obtain ⟨d,da,db⟩ := commonSide (nonempty F leaf gates a (ab.trans bound))
    (nonempty F leaf gates b bound) (fun i => decide (N≤i)) fault
  refine ⟨g,hg,a,b,ab,bb,eq,d,?_⟩
  intro w hw
  have which : w=a ∨ w=b := by simpa using hw
  rcases which with rfl|rfl
  · exact advertised _ d da
  · exact advertised _ d db

end PairVariation3501
