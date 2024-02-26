From category Require Import
  base
  setoid
  category
  sets
  terminal
  functor
  limit
  prod.

Section Limits.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Class hasLimits (C : Category) :=
    {
      has_limits : ∀ {D : Category} (J : D [⇒] C), Limit J;
    }.

  Class hasProducts (C : Category) :=
    {
      has_products : ∀ {D : Type} `{!EqDecision D} (J : D → C), Prod J;
    }.

  Class hasTerminal (C : Category) :=
    {
      has_terminal : Terminal C;
    }.

  Class hasBinaryProducts (C : Category) :=
    {
      has_binary_products : ∀ (X Y : C), BinProd X Y;
    }.

  Class hasFiniteProducts (C : Category) :=
    {
      has_finite_products_binary_product : hasBinaryProducts C;
      has_finite_products_terminal : hasTerminal C;
    }.

  Global Instance LimitsProducts (C : Category)
    : hasLimits C → hasProducts C.
  Proof.
    intros H.
    constructor.
    intros ???.
    apply DiscreteLimitProd.
    apply H.
  Defined.

  Global Instance ProductsTerminal (C : Category)
    : hasProducts C → hasTerminal C.
  Proof.
    intros H.
    constructor.
    apply EmptyLimit.
    apply ProdDiscreteLimit.
    apply H.
  Defined.

  Global Instance ProductsBinaryProducts (C : Category)
    : hasProducts C → hasBinaryProducts C.
  Proof.
    intros H.
    constructor.
    intros X Y.
    apply DiscreteLimitBinProd.
    apply ProdDiscreteLimit.
    apply H.
  Defined.
End Limits.

Notation "'lim' J '@' C" := (cone_obj (terminal_obj (limit_obj (@has_limits C _ _ J)))) (at level 50) : cat_scope.
Notation "'Π' J '@' C" := (@has_products C _ _ _ J) (at level 50) : cat_scope.
Notation "X '×ₒ' Y '@' C" := (@has_binary_products C _ X Y) (at level 50, left associativity) : cat_scope.
Notation "! '@' C" := (projT1 (@terminal_proj _ (@has_terminal C _) _)) (at level 50) : cat_scope.
Notation "𝟙 '@' C" := (@terminal_obj _ (@has_terminal C _)) (at level 50) : cat_scope.

Section Aux.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Program Definition ArrProdCone {D : Type}
    `{!EqDecision D}
    {C : Category}
    `{!hasProducts C}
    (f : D → C)
    (g : D → C)
    (h : DiscreteFun f [↣] DiscreteFun g)
    : ConeArr _ (ConeReindex _ _ h (ProdCone (Π f @ C))) (ProdCone (Π g @ C)) :=
    {|
      cone_arr := (projT1 (prod_ump _ (Π g @ C) (Π f @ C) (h ∘ (proj_arr _ (Π f @ C)))));
    |}.
  Next Obligation.
    intros; simpl.
    pose proof (fst (projT2 (prod_ump _ (Π g @ C) (Π f @ C) (h ∘ (proj_arr _ (Π f @ C))))) j) as H.
    rewrite H.
    reflexivity.
  Qed.

  Definition ArrProd {D : Type}
    `{!EqDecision D}
    {C : Category}
    `{!hasProducts C}
    (f : D → C)
    (g : D → C)
    (h : (DiscreteFun f [↣] DiscreteFun g))
    : ((Π f @ C) [~>] (Π g @ C))
    := (projT1 (prod_ump _ (Π g @ C) (Π f @ C) (h ∘ (proj_arr _ (Π f @ C))))).

  Program Definition ArrBinProd
    {C : Category}
    `{!hasBinaryProducts C}
    {X₁ Y₁ X₂ Y₂ : C}
    : (X₁ [~>] Y₁) [→] (X₂ [~>] Y₂) [→] (X₁ ×ₒ X₂ @ C [~>] Y₁ ×ₒ Y₂ @ C) :=
    λₛ f, λₛ g, (projT1 (bin_prod_ump Y₁ Y₂ (Y₁ ×ₒ Y₂ @ C) (X₁ ×ₒ X₂ @ C)
                           (f ∘ π₁)
                           (g ∘ π₂))).
  Next Obligation.
    intros; simpl.
    apply (snd (projT2 (bin_prod_ump Y₁ Y₂ (Y₁ ×ₒ Y₂ @ C) (X₁ ×ₒ X₂ @ C)
                          (f ∘ π₁)
                          (a₁ ∘ π₂)))).
    split.
    - apply (proj1
               (fst
                  (projT2
                     (bin_prod_ump Y₁ Y₂ (Y₁ ×ₒ Y₂ @ C) (X₁ ×ₒ X₂ @ C)
                        (f ∘ π₁)
                        (a₂ ∘ π₂))))).
    - rewrite H.
      apply (proj2
               (fst
                  (projT2
                     (bin_prod_ump Y₁ Y₂ (Y₁ ×ₒ Y₂ @ C) (X₁ ×ₒ X₂ @ C)
                        (f ∘ π₁)
                        (a₂ ∘ π₂))))).
  Qed.
  Next Obligation.
    intros; simpl.
    intros a.
    apply (snd (projT2 (bin_prod_ump Y₁ Y₂ (Y₁ ×ₒ Y₂ @ C) (X₁ ×ₒ X₂ @ C)
                          (a₁ ∘ π₁)
                          (a ∘ π₂)))).
    split.
    - rewrite H.
      apply (proj1
               (fst
                  (projT2
                     (bin_prod_ump Y₁ Y₂ (Y₁ ×ₒ Y₂ @ C) (X₁ ×ₒ X₂ @ C)
                        (a₂ ∘ π₁)
                        (a ∘ π₂))))).
    - apply (proj2
               (fst
                  (projT2
                     (bin_prod_ump Y₁ Y₂ (Y₁ ×ₒ Y₂ @ C) (X₁ ×ₒ X₂ @ C)
                        (a₂ ∘ π₁)
                        (a ∘ π₂))))).
  Qed.

  Lemma ArrBinProdComp {C : Category}
    `{!hasBinaryProducts C}
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
    {f₁ : X₁ [~>] Y₁}
    {f₂ : X₂ [~>] Y₂}
    {g₁ : Y₁ [~>] Z₁}
    {g₂ : Y₂ [~>] Z₂}
    : (ArrBinProd g₁ g₂ ∘ ArrBinProd f₁ f₂)
        ≡ ArrBinProd (g₁ ∘ f₁) (g₂ ∘ f₂).
  Proof.
    unfold ArrBinProd.
    simpl.
    rewrite (snd (projT2 (@bin_prod_ump C _ _ _ _ _ _))
               (ArrBinProd g₁ g₂)).
    - rewrite (snd (projT2 (@bin_prod_ump C _ _ _ _ _ _))
                 (ArrBinProd f₁ f₂)).
      + rewrite (snd (projT2 (@bin_prod_ump C _ _ _ _ _ _))); [reflexivity |].
        split.
        * simpl.
          rewrite <-arrow_comp_assoc.
          rewrite <-(proj1 (fst (projT2 (@bin_prod_ump _ _ _ (Z₁ ×ₒ Z₂ @ C) _ _ _)))).
          rewrite !arrow_comp_assoc.
          rewrite <-(proj1 (fst (projT2 (@bin_prod_ump _ _ _ (Y₁ ×ₒ Y₂ @ C) _ _ _)))).
          reflexivity.
        * simpl.
          rewrite <-arrow_comp_assoc.
          rewrite <-(proj2 (fst (projT2 (@bin_prod_ump _ _ _ (Z₁ ×ₒ Z₂ @ C) _ _ _)))).
          rewrite !arrow_comp_assoc.
          rewrite <-(proj2 (fst (projT2 (@bin_prod_ump _ _ _ (Y₁ ×ₒ Y₂ @ C) _ _ _)))).
          reflexivity.
      + split.
        * simpl; now rewrite <-(proj1 (fst (projT2 (@bin_prod_ump _ _ _ (Y₁ ×ₒ Y₂ @ C) _ _ _)))).
        * simpl; now rewrite <-(proj2 (fst (projT2 (@bin_prod_ump _ _ _ (Y₁ ×ₒ Y₂ @ C) _ _ _)))).
    - split.
      + simpl; now rewrite <-(proj1 (fst (projT2 (@bin_prod_ump _ _ _ (Z₁ ×ₒ Z₂ @ C) _ _ _)))).
      + simpl; now rewrite <-(proj2 (fst (projT2 (@bin_prod_ump _ _ _ (Z₁ ×ₒ Z₂ @ C) _ _ _)))).
  Qed.

  Program Definition ArrBinUnrec {C : Category}
    `{!hasBinaryProducts C}
    {X Y Z : C}
    : (X [~>] Y) [→] (X [~>] Z) [→] (X [~>] (Y ×ₒ Z @ C))
    := λₛ f, λₛ g, projT1 (@bin_prod_ump C Y Z (Y ×ₒ Z @ C) X f g).
  Next Obligation.
    intros; simpl.
    apply (snd (projT2 (@bin_prod_ump C Y Z (Y ×ₒ Z @ C) X f a₁))).
    split.
    - apply (proj1 (fst (projT2 (@bin_prod_ump C Y Z (Y ×ₒ Z @ C) X f a₂)))).
    - rewrite H.
      apply (proj2 (fst (projT2 (@bin_prod_ump C Y Z (Y ×ₒ Z @ C) X f a₂)))).
  Qed.
  Next Obligation.
    intros; simpl.
    intros a.
    apply (snd (projT2 (@bin_prod_ump C Y Z (Y ×ₒ Z @ C) X a₁ a))).
    split.
    - rewrite H.
      apply (proj1 (fst (projT2 (@bin_prod_ump C Y Z (Y ×ₒ Z @ C) X a₂ a)))).
    - apply (proj2 (fst (projT2 (@bin_prod_ump C Y Z (Y ×ₒ Z @ C) X a₂ a)))).
  Qed.

  Program Definition DiagonalArr {C : Category}
    `{!hasBinaryProducts C}
    {X : C} : X [~>] (X ×ₒ X @ C)
    := projT1 (@bin_prod_ump C X X (X ×ₒ X @ C) X ı ı).

  Definition invπ₁ {C : Category} `{!hasTerminal C} `{!hasBinaryProducts C} {X : C}
    : X [~>] X ×ₒ (𝟙 @ C) @ C
    := projT1 (@bin_prod_ump C X (𝟙 @ C) (X ×ₒ 𝟙 @ C @ C) X ı (! @ C)).

  Definition invπ₂ {C : Category} `{!hasTerminal C} `{!hasBinaryProducts C} {X : C}
    : X [~>] (𝟙 @ C) ×ₒ X @ C
    := projT1 (@bin_prod_ump C (𝟙 @ C) X (𝟙 @ C ×ₒ X @ C) X (! @ C) ı).

  Lemma invProp1 {C : Category} `{!hasTerminal C} `{!hasBinaryProducts C} {X : C}
    : π₁ ∘ (@invπ₁ C _ _ X) ≡ ı.
  Proof.
    unfold invπ₁.
    unfold π₁.
    now rewrite <-(proj1 (fst (projT2 (@bin_prod_ump C X (𝟙 @ C) (X ×ₒ 𝟙 @ C @ C) X ı (! @ C))))).
  Qed.

  Lemma invProp2 {C : Category} `{!hasTerminal C} `{!hasBinaryProducts C} {X : C}
    : π₂ ∘ (@invπ₂ C _ _ X) ≡ ı.
  Proof.
    unfold invπ₂.
    unfold π₂.
    now rewrite <-(proj2 (fst (projT2 (@bin_prod_ump C (𝟙 @ C) X (𝟙 @ C ×ₒ X @ C) X (! @ C) ı)))).
  Qed.

  Lemma DiagProp1 {C : Category} `{!hasBinaryProducts C} {X : C}
    : π₁ ∘ (@DiagonalArr C _ X) ≡ ı.
  Proof.
    unfold π₁.
    unfold DiagonalArr.
    now rewrite <-(proj1 (fst (projT2 (@bin_prod_ump C X X (X ×ₒ X @ C) X ı ı)))).
  Qed.

  Lemma DiagProp2 {C : Category} `{!hasBinaryProducts C} {X : C}
    : π₂ ∘ (@DiagonalArr C _ X) ≡ ı.
  Proof.
    unfold π₂.
    unfold DiagonalArr.
    now rewrite <-(proj2 (fst (projT2 (@bin_prod_ump C X X (X ×ₒ X @ C) X ı ı)))).
  Qed.
End Aux.

Notation "'⟨' f ',' g '⟩'" := (ArrBinUnrec f g) (at level 50) : cat_scope.
Notation "'⟨' f '×ₐ' g '⟩'" := (ArrBinProd f g) (at level 50) : cat_scope.
Notation "'δₐ'" := (DiagonalArr) (at level 50) : cat_scope.
