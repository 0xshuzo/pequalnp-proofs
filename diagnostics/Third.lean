import Mathlib
import PEqualNP.Defs

theorem C4095.geometry : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      (∀ v∉A,(G.neighborSet v).ncard=3) → (∀ a b,G.Adj a b → a∉A) →
      (∀ v (w : G.Walk v v),w.IsCycle → 7≤w.length) →
      ∃ T : Finset (Fin n), (∀ a b,G.Adj a b → a∈T ∨ b∈T) ∧ 3*T.card≤2*Aᶜ.card := by
  intro n G inst A degree iso girth
  classical
  let D := Aᶜ
  let good (S : Finset (Fin n)) := ∀ u∈S, ∀ v∈S, ¬G.Adj u v
  let bank := D.powerset.filter good
  have valid (S : Finset (Fin n)) : S∈bank ↔ S⊆D ∧ good S := by simp [bank]
  have nonempty : bank.Nonempty := ⟨∅,(valid _).mpr ⟨Finset.empty_subset _,by simp [good]⟩⟩
  obtain ⟨I,memI,best⟩ := Finset.exists_max_image bank Finset.card nonempty
  obtain ⟨subI,free⟩ := (valid I).mp memI
  let T := D \ I
  have Tsub : T⊆D := Finset.sdiff_subset
  have away {v : Fin n} (hv : v∈T) : v∉I := (Finset.mem_sdiff.mp hv).2
  have add {S : Finset (Fin n)} {w : Fin n} (h : good S) (z : ∀ j∈S, ¬G.Adj w j) : good (insert w S) := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl|ha <;> rcases Finset.mem_insert.mp hb with rfl|hb
    · exact hab.ne rfl
    · exact z _ hb hab
    · exact z _ ha hab.symm
    · exact h _ ha _ hb hab
  let N (v : Fin n) := I.filter (G.Adj v)
  have nonzero (v : Fin n) (hv : v∈T) : 0<(N v).card := by
    by_contra! empty
    have z (j : Fin n) (hj : j∈I) (edge : G.Adj v j) : False := by
      have hm : j∈N v := Finset.mem_filter.mpr ⟨hj,edge⟩
      have pos := Finset.card_pos.mpr ⟨j,hm⟩
      omega
    have big := best (insert v I) ((valid _).mpr ⟨Finset.insert_subset (Tsub hv) subI,add free z⟩)
    rw [Finset.card_insert_of_notMem (away hv)] at big
    omega
  let P := T.filter (fun v => (N v).card=1)
  have single (v : Fin n) (hv : v∈P) : ∃ i∈I,G.Adj v i ∧ ∀ j∈I,G.Adj v j → j=i := by
    obtain ⟨i,eq⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hv).2
    have hi : i∈N v := by rw [eq]; exact Finset.mem_singleton_self i
    obtain ⟨iI,vi⟩ := Finset.mem_filter.mp hi
    refine ⟨i,iI,vi,?_⟩
    intro j hj vj
    have hN : j∈N v := Finset.mem_filter.mpr ⟨hj,vj⟩
    rwa [eq,Finset.mem_singleton] at hN
  let f (v : P) : I := ⟨(single v.val v.property).choose,(single v.val v.property).choose_spec.1⟩
  have charac (v : P) : G.Adj v.val (f v).val ∧ ∀ j∈I,G.Adj v.val j → j=(f v).val :=
    (single v.val v.property).choose_spec.2
  have boundP : P.card≤I.card := by
    suffices Function.Injective f by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f this
    intro u v same
    apply Subtype.ext
    by_contra different
    let i := (f u).val
    have equal : (f v).val=i := (congrArg Subtype.val same).symm
    obtain ⟨ui,onlyU⟩ := charac u
    obtain ⟨vi,onlyV⟩ := charac v
    rw [equal] at vi onlyV
    have uT := (Finset.mem_filter.mp u.property).1
    have vT := (Finset.mem_filter.mp v.property).1
    have uv : ¬G.Adj u.val v.val := by
      intro edge
      let W : G.Walk u.val u.val := .cons ui (.cons vi.symm (.cons edge.symm .nil))
      have cy : W.IsCycle := by
        rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
        constructor
        · rw [SimpleGraph.Walk.isPath_def]
          simp [W,edge.ne,edge.ne.symm,ui.ne,ui.ne.symm,vi.ne,vi.ne.symm]
        · simp [W]
      have too := girth _ W cy
      simp [W] at too
    let K := I.erase i
    have ksub : K⊆I := Finset.erase_subset _ _
    have ki : good K := fun x hx y hy => free x (ksub hx) y (ksub hy)
    have uc (j : Fin n) (hj : j∈K) (adj : G.Adj u.val j) : False :=
      (Finset.mem_erase.mp hj).1 (onlyU j (ksub hj) adj)
    have vc (j : Fin n) (hj : j∈insert u.val K) (adj : G.Adj v.val j) : False := by
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact uv adj.symm
      · exact (Finset.mem_erase.mp hj).1 (onlyV j (ksub hj) adj)
    have grown := best (insert v.val (insert u.val K)) ((valid _).mpr
      ⟨Finset.insert_subset (Tsub vT) (Finset.insert_subset (Tsub uT) (ksub.trans subI)),add (add ki uc) vc⟩)
    have ku : u.val∉K := fun h => away uT (ksub h)
    have kv : v.val∉insert u.val K := by
      intro h
      rcases Finset.mem_insert.mp h with he|he
      · exact different he.symm
      · exact away vT (ksub he)
    have q : K.card+1=I.card := Finset.card_erase_add_one (f u).property
    rw [Finset.card_insert_of_notMem kv, Finset.card_insert_of_notMem ku] at grown
    omega
  have lv (v : Fin n) (hv : v∈T) : 2 ≤ (N v).card + (if (N v).card=1 then 1 else 0) := by
    have pos := nonzero v hv
    split <;> omega
  have lo := Finset.sum_le_sum lv
  have term : (∑ v∈T, if (N v).card=1 then 1 else 0) = P.card := by simp [P]
  rw [Finset.sum_add_distrib,term] at lo
  simp only [Finset.sum_const,smul_eq_mul] at lo
  have ctl (i : Fin n) (hi : i∈I) : (T.filter (fun v => G.Adj v i)).card≤3 := by
    have sub : T.filter (fun v => G.Adj v i) ⊆ G.neighborFinset i := by
      intro v hm
      exact (G.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hm).2.symm
    have deg : G.degree i=3 := by rw [←G.ncard_neighborSet]; exact degree i (Finset.mem_compl.mp (subI hi))
    simpa only [SimpleGraph.card_neighborFinset_eq_degree,deg] using Finset.card_le_card sub
  have du : (∑ v∈T,(N v).card) = ∑ i∈I,(T.filter (fun v => G.Adj v i)).card := by
    simp only [N,Finset.card_filter]
    rw [Finset.sum_comm]
  have hi := Finset.sum_le_sum ctl
  simp only [Finset.sum_const,smul_eq_mul] at hi
  rw [du] at lo
  have tabs : T.card=D.card-I.card := Finset.card_sdiff_of_subset subI
  have subs := Finset.card_le_card subI
  refine ⟨T,?_,?_⟩
  · intro u v edge
    by_contra! h
    have uD : u∈D := Finset.mem_compl.mpr (iso _ _ edge)
    have vD : v∈D := Finset.mem_compl.mpr (iso _ _ edge.symm)
    have uI : u∈I := by by_contra z;exact h.1 (Finset.mem_sdiff.mpr ⟨uD,z⟩)
    have vI : v∈I := by by_contra z;exact h.2 (Finset.mem_sdiff.mpr ⟨vD,z⟩)
    exact free _ uI _ vI edge
  · change 3*T.card≤2*D.card
    omega
