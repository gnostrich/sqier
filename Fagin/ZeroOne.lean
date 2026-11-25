module

public import Mathlib
public import Fagin.Count
public import Fagin.Rado

@[expose] public section

/-!
# Fagin's zero-one law

We follow the standard route.

* `extSentence i j` is a first-order sentence expressing the extension property for `i`
  vertices that must be adjacent and `j` vertices that must be non-adjacent to a new vertex.
* `extTheory` is the theory of simple graphs together with all extension sentences. The Rado
  graph is a model, every model is infinite, and any two countable models are isomorphic
  (`nonempty_iso_of_extension`). By the Łoś–Vaught test, `extTheory` is complete.
* If the Rado graph satisfies `φ`, then `extTheory ⊨ φ`, so by compactness `φ` follows from
  finitely many axioms, hence from the `K`-extension property for some `K`. Since almost every
  finite graph has the `K`-extension property, almost every finite graph satisfies `φ`.
-/

namespace Fagin

open FirstOrder FirstOrder.Language Filter Topology Cardinal

/-! ### Extension sentences -/

/-- The extension property for tuples: `i` vertices `a` and `j` vertices `b`, such that no `a s`
equals any `b t`, admit a vertex `z` different from all of them, adjacent to all `a s` and to
no `b t`. -/
def TupleExt {V : Type*} (G : SimpleGraph V) (i j : ℕ) : Prop :=
  ∀ (a : Fin i → V) (b : Fin j → V), (∀ s t, a s ≠ b t) →
    ∃ z : V, (∀ s, z ≠ a s) ∧ (∀ t, z ≠ b t) ∧ (∀ s, G.Adj z (a s)) ∧ ∀ t, ¬ G.Adj z (b t)

/-- The body of the extension sentence: the new vertex (variable `Sum.inr ()`) is different
from, adjacent to the first `i` and non-adjacent to the last `j` of the old vertices. -/
noncomputable def extBody (i j : ℕ) :
    Language.graph.Formula ((Empty ⊕ (Fin i ⊕ Fin j)) ⊕ Unit) :=
  let z : Language.graph.Term ((Empty ⊕ (Fin i ⊕ Fin j)) ⊕ Unit) := Term.var (Sum.inr ())
  let x : Fin i ⊕ Fin j → Language.graph.Term ((Empty ⊕ (Fin i ⊕ Fin j)) ⊕ Unit) :=
    fun p => Term.var (Sum.inl (Sum.inr p))
  (Formula.iInf fun s : Fin i => (z.equal (x (Sum.inl s))).not) ⊓
    (Formula.iInf fun t : Fin j => (z.equal (x (Sum.inr t))).not) ⊓
    (Formula.iInf fun s : Fin i => adj.formula₂ z (x (Sum.inl s))) ⊓
    (Formula.iInf fun t : Fin j => (adj.formula₂ z (x (Sum.inr t))).not)

/-- The hypothesis of the extension sentence: no old vertex of the first kind equals one of
the second kind. -/
noncomputable def extHyp (i j : ℕ) : Language.graph.Formula (Empty ⊕ (Fin i ⊕ Fin j)) :=
  Formula.iInf fun st : Fin i × Fin j =>
    ((Term.var (Sum.inr (Sum.inl st.1))).equal (Term.var (Sum.inr (Sum.inr st.2)))).not

/-- The extension sentence for `i` adjacent and `j` non-adjacent vertices. -/
noncomputable def extSentence (i j : ℕ) : Language.graph.Sentence :=
  Formula.iAlls (Fin i ⊕ Fin j) ((extHyp i j).imp (Formula.iExs Unit (extBody i j)))

theorem realize_extSentence {M : Type*} [Language.graph.Structure M] [M ⊨ Theory.simpleGraph]
    (i j : ℕ) : M ⊨ extSentence i j ↔ TupleExt (simpleGraphOfStructure M) i j := by
  simp only [extSentence, Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp, extHyp,
    Formula.realize_iInf, Formula.realize_not, Formula.realize_equal, Term.realize_var,
    Formula.realize_iExs, extBody, Formula.realize_inf, Formula.realize_rel₂, Sum.elim_inr,
    Sum.elim_inl, TupleExt, simpleGraphOfStructure_adj]
  constructor
  · intro h a b hab
    obtain ⟨w, h1, h2, h3, h4⟩ := h (Sum.elim a b) (fun st => hab st.1 st.2)
    exact ⟨w (), h1, h2, h3, h4⟩
  · intro h x hx
    obtain ⟨z, h1, h2, h3, h4⟩ := h (fun s => x (Sum.inl s)) (fun t => x (Sum.inr t))
      (fun s t => hx (s, t))
    exact ⟨fun _ => z, h1, h2, h3, h4⟩

theorem realize_extSentence_structure {V : Type*} (G : SimpleGraph V) (i j : ℕ) :
    @Sentence.Realize _ V G.structure (extSentence i j) ↔ TupleExt G i j := by
  letI := G.structure
  rw [realize_extSentence, SimpleGraph.simpleGraphOfStructure]

theorem tupleExt_of_extensionProperty {V : Type*} {G : SimpleGraph V} {i j k : ℕ}
    (hk : i + j ≤ k) (h : ExtensionProperty G k) : TupleExt G i j := by
  classical
  intro a b hab
  obtain ⟨z, hzA, hzB, hA, hB⟩ := h (Finset.univ.image a) (Finset.univ.image b)
    (by
      rw [Finset.disjoint_left]
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      rintro _ ⟨s, rfl⟩ t ht
      exact hab s t ht.symm)
    (by
      refine le_trans (add_le_add Finset.card_image_le Finset.card_image_le) ?_
      simpa using hk)
  simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists, forall_exists_index,
    forall_apply_eq_imp_iff] at hzA hzB hA hB
  exact ⟨z, fun s h => hzA s h.symm, fun t h => hzB t h.symm, hA, hB⟩

theorem extensionProperty_of_tupleExt {V : Type*} {G : SimpleGraph V}
    (h : ∀ i j, TupleExt G i j) (k : ℕ) : ExtensionProperty G k := by
  intro A B hAB _
  let a : Fin A.card → V := fun s => (A.equivFin.symm s : V)
  let b : Fin B.card → V := fun t => (B.equivFin.symm t : V)
  have ha : ∀ x (hx : x ∈ A), a (A.equivFin ⟨x, hx⟩) = x := fun x hx => by simp [a]
  have hb : ∀ x (hx : x ∈ B), b (B.equivFin ⟨x, hx⟩) = x := fun x hx => by simp [b]
  obtain ⟨z, h1, h2, h3, h4⟩ := h A.card B.card a b (fun s t hst =>
    Finset.disjoint_left.1 hAB (A.equivFin.symm s).2 (hst ▸ (B.equivFin.symm t).2))
  refine ⟨z, fun hz => h1 _ (ha z hz).symm, fun hz => h2 _ (hb z hz).symm,
    fun x hx => ha x hx ▸ h3 _, fun x hx => hb x hx ▸ h4 _⟩

theorem forall_extensionProperty_iff {V : Type*} (G : SimpleGraph V) :
    (∀ k, ExtensionProperty G k) ↔ ∀ i j, TupleExt G i j :=
  ⟨fun h i j => tupleExt_of_extensionProperty le_rfl (h (i + j)),
    extensionProperty_of_tupleExt⟩

/-! ### The theory of graphs with all extension properties -/

/-- The theory of simple graphs with all extension properties. -/
def extTheory : Language.graph.Theory :=
  Theory.simpleGraph ∪ Set.range fun p : ℕ × ℕ => extSentence p.1 p.2

theorem model_extTheory_iff {V : Type*} (G : SimpleGraph V) :
    @Theory.Model _ V G.structure extTheory ↔ ∀ k, ExtensionProperty G k := by
  letI := G.structure
  rw [forall_extensionProperty_iff, extTheory, Theory.model_union_iff]
  simp only [simpleGraph_model G, true_and, Theory.model_iff, Set.forall_mem_range,
    realize_extSentence_structure, Prod.forall]

theorem extensionProperty_of_model {M : Type*} [Language.graph.Structure M] [h : M ⊨ extTheory]
    (k : ℕ) :
    haveI : M ⊨ Theory.simpleGraph := Theory.Model.mono h Set.subset_union_left
    ExtensionProperty (simpleGraphOfStructure M) k := by
  haveI : M ⊨ Theory.simpleGraph := Theory.Model.mono h Set.subset_union_left
  have := (model_extTheory_iff (simpleGraphOfStructure M)).1
    (by rw [structure_simpleGraphOfStructure]; exact h)
  exact this k

theorem infinite_of_model {M : Type*} [Language.graph.Structure M] [M ⊨ extTheory] :
    Infinite M := by
  haveI : M ⊨ Theory.simpleGraph := Theory.Model.mono ‹_› Set.subset_union_left
  by_contra hM
  rw [not_infinite_iff_finite] at hM
  have := Fintype.ofFinite M
  obtain ⟨z, hz, -⟩ := extensionProperty_of_model (M := M) (Finset.univ.card + 0)
    Finset.univ ∅ (Finset.disjoint_empty_right _) le_rfl
  exact hz (Finset.mem_univ z)

/-- A graph isomorphism between models of the theory of simple graphs is an isomorphism of
first-order structures. -/
def equivOfIso {M N : Type*} [Language.graph.Structure M] [Language.graph.Structure N]
    [M ⊨ Theory.simpleGraph] [N ⊨ Theory.simpleGraph]
    (f : simpleGraphOfStructure M ≃g simpleGraphOfStructure N) : M ≃[Language.graph] N where
  toEquiv := f.toEquiv
  map_fun' := fun {_} g => isEmptyElim g
  map_rel' := by
    intro n r x
    rcases r with ⟨⟩
    have e1 : (f.toEquiv.toFun ∘ x) = ![f (x 0), f (x 1)] := by
      ext i; fin_cases i <;> rfl
    have e2 : x = ![x 0, x 1] := by
      ext i; fin_cases i <;> rfl
    rw [e1]
    conv_rhs => rw [e2]
    exact f.map_rel_iff

instance : Countable Language.graph.Symbols := by
  unfold Language.Symbols
  infer_instance

theorem extTheory_categorical : (ℵ₀ : Cardinal.{0}).Categorical extTheory := by
  intro M N hM hN
  have : Countable M := Cardinal.mk_le_aleph0_iff.1 hM.le
  have : Countable N := Cardinal.mk_le_aleph0_iff.1 hN.le
  haveI : M ⊨ Theory.simpleGraph := Theory.Model.mono M.is_model Set.subset_union_left
  haveI : N ⊨ Theory.simpleGraph := Theory.Model.mono N.is_model Set.subset_union_left
  obtain ⟨f⟩ := nonempty_iso_of_extension (simpleGraphOfStructure M) (simpleGraphOfStructure N)
    (extensionProperty_of_model (M := M)) (extensionProperty_of_model (M := N))
  exact ⟨equivOfIso f⟩

theorem rado_model : @Theory.Model _ ℕ radoGraph.structure extTheory :=
  (model_extTheory_iff radoGraph).2 radoGraph_extension

theorem extTheory_isComplete : extTheory.IsComplete :=
  extTheory_categorical.isComplete ℵ₀ extTheory le_rfl
    (by simpa [Language.card] using Cardinal.mk_le_aleph0)
    ⟨@Theory.ModelType.of _ extTheory ℕ radoGraph.structure rado_model _⟩
    (fun M => infinite_of_model (M := M))

theorem extTheory_models_of_rado (φ : Language.graph.Sentence)
    (h : @Sentence.Realize Language.graph ℕ radoGraph.structure φ) : extTheory ⊨ᵇ φ := by
  rcases extTheory_isComplete.2 φ with h' | h'
  · exact h'
  · exfalso
    have := @Theory.ModelsBoundedFormula.realize_sentence _ _ _ h' ℕ radoGraph.structure
      rado_model _
    exact (@Sentence.realize_not _ ℕ radoGraph.structure φ).1 this h

theorem exists_bound (T0 : Finset Language.graph.Sentence) (hT0 : (T0 : Language.graph.Theory) ⊆ extTheory) :
    ∃ K, ∀ ψ ∈ T0, ψ ∈ Theory.simpleGraph ∨ ∃ i j, i + j ≤ K ∧ ψ = extSentence i j := by
  classical
  let f : Language.graph.Sentence → ℕ := fun ψ =>
    if h : ∃ p : ℕ × ℕ, extSentence p.1 p.2 = ψ then h.choose.1 + h.choose.2 else 0
  refine ⟨T0.sup f, fun ψ hψ => ?_⟩
  rcases hT0 hψ with h | h
  · exact Or.inl h
  · right
    have h' : ∃ p : ℕ × ℕ, extSentence p.1 p.2 = ψ := h
    have hle : f ψ ≤ T0.sup f := Finset.le_sup hψ
    simp only [f, dif_pos h'] at hle
    exact ⟨_, _, hle, h'.choose_spec.symm⟩

theorem exists_extensionProperty_realize {φ : Language.graph.Sentence} (hφ : extTheory ⊨ᵇ φ) :
    ∃ K, ∀ (V : Type) (G : SimpleGraph V), ExtensionProperty G K →
      @Sentence.Realize _ V G.structure φ := by
  obtain ⟨T0, hsub, hT0⟩ := Theory.models_iff_finset_models.1 hφ
  obtain ⟨K, hK⟩ := exists_bound T0 hsub
  refine ⟨K, fun V G hG => ?_⟩
  letI := G.structure
  obtain ⟨z, -⟩ := hG ∅ ∅ (Finset.disjoint_empty_left _) (by simp)
  haveI : Nonempty V := ⟨z⟩
  haveI : V ⊨ (T0 : Language.graph.Theory) := by
    rw [Theory.model_iff]
    intro ψ hψ
    rcases hK ψ hψ with h | ⟨i, j, hij, rfl⟩
    · exact Theory.realize_sentence_of_mem _ h
    · rw [realize_extSentence_structure]
      exact tupleExt_of_extensionProperty hij hG
  exact hT0.realize_sentence V

/-! ### Counting -/

theorem graphProb_le_one (φ : Language.graph.Sentence) (n : ℕ) : graphProb φ n ≤ 1 := by
  unfold graphProb
  rw [div_le_one (by positivity), ← card_simpleGraph]
  exact_mod_cast Nat.card_subtype_le _

theorem graphProb_not (φ : Language.graph.Sentence) (n : ℕ) :
    graphProb φ.not n = 1 - graphProb φ n := by
  unfold graphProb
  have hc : Nat.card {G : SimpleGraph (Fin n) //
        @Sentence.Realize Language.graph (Fin n) G.structure φ.not} =
      Nat.card {G : SimpleGraph (Fin n) //
        ¬ @Sentence.Realize Language.graph (Fin n) G.structure φ} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun G => @Sentence.realize_not _ _ G.structure φ)
  have hs := Nat.card_congr (Equiv.sumCompl fun G : SimpleGraph (Fin n) =>
    @Sentence.Realize Language.graph (Fin n) G.structure φ)
  rw [Nat.card_sum, card_simpleGraph] at hs
  have h2 : (2 : ℝ) ^ n.choose 2 ≠ 0 := by positivity
  rw [hc, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h2]
  exact_mod_cast (add_comm _ _).trans hs

/-- If the Rado graph satisfies `φ`, then almost every finite graph satisfies `φ`. -/
theorem tendsto_one_of_rado (φ : Language.graph.Sentence)
    (h : @Sentence.Realize Language.graph ℕ radoGraph.structure φ) :
    Tendsto (graphProb φ) atTop (𝓝 1) := by
  obtain ⟨K, hK⟩ := exists_extensionProperty_realize (extTheory_models_of_rado φ h)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (extension_almost_sure K) tendsto_const_nhds
    (fun n => ?_) (graphProb_le_one φ)
  unfold graphProb
  gcongr
  exact Nat.card_le_card_of_injective (fun G => ⟨G.1, hK _ G.1 G.2⟩)
    (fun G H h => Subtype.ext (congrArg Subtype.val h))

/-- If the Rado graph does not satisfy `φ`, then almost no finite graph satisfies `φ`. -/
theorem tendsto_zero_of_not_rado (φ : Language.graph.Sentence)
    (h : ¬ @Sentence.Realize Language.graph ℕ radoGraph.structure φ) :
    Tendsto (graphProb φ) atTop (𝓝 0) := by
  have h1 := tendsto_one_of_rado φ.not ((@Sentence.realize_not _ ℕ radoGraph.structure φ).2 h)
  have h2 : graphProb φ = fun n => 1 - graphProb φ.not n := by
    funext n; rw [graphProb_not]; ring
  rw [h2]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h1

/-- Fagin's zero-one law: the probability that `G(n, 1/2)` satisfies a first-order sentence
tends to `0` or to `1`. -/
theorem zero_one_law (φ : Language.graph.Sentence) :
    Tendsto (graphProb φ) atTop (𝓝 0) ∨ Tendsto (graphProb φ) atTop (𝓝 1) := by
  by_cases h : @Sentence.Realize Language.graph ℕ radoGraph.structure φ
  · exact Or.inr (tendsto_one_of_rado φ h)
  · exact Or.inl (tendsto_zero_of_not_rado φ h)

end Fagin
