From category Require Import
                      base
                      setoid
                      category
                      sets
                      terminal
                      functor
                      limit
                      prod
                      classes.limits
                      exp.

Section Exp.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Class hasExp (C : Category) `{!hasBinaryProducts C} :=
    {
      has_exp : ∀ (X Y : C), Exp X Y;
    }.
End Exp.

Notation "X '⇒' Y '@' C" := (@has_exp C _ _ Y X) (at level 50) : cat_scope.

Section Aux.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Program Definition Curry
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    : (X ×ₒ Y @ C [~>] Z) [→] (X [~>] (Y ⇒ Z @ C))
    := λₛ f, projT1 (exp_ump Z Y (Y ⇒ Z @ C) X f).
  Next Obligation.
    intros; simpl.
    apply (snd (projT2 (exp_ump Z Y (Y ⇒ Z @ C) X a₁))).
    rewrite H1.
    apply (fst (projT2 (exp_ump Z Y (Y ⇒ Z @ C) X a₂))).
  Qed.

  Program Definition Uncurry
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    : (X [~>] (Y ⇒ Z @ C)) [→] (X ×ₒ Y @ C [~>] Z)
    := λₛ f, (eval ∘ ⟨ f ×ₐ ı ⟩).
  Next Obligation.
    intros; simpl.
    f_equiv.
    apply (snd (projT2 (bin_prod_ump (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) (X ×ₒ Y @ C)
                          (a₁ ∘ π₁)
                          (ı ∘ π₂)))).
    split.
    - rewrite H1.
      apply (proj1 (fst (projT2 (bin_prod_ump (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) (X ×ₒ Y @ C)
                                   (a₂ ∘ π₁)
                                   (ı ∘ π₂))))).
    - rewrite <-(proj2 (fst (projT2 (bin_prod_ump (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) (X ×ₒ Y @ C)
                                      (a₂ ∘ π₁)
                                      (ı ∘ π₂))))).
      now rewrite arrow_comp_id_l.
  Qed.

  Lemma CurryUnique
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    (f : X ×ₒ Y @ C [~>] Z)
    : Σ! (g : (X [~>] (Y ⇒ Z @ C))), f ≡ eval ∘ ⟨ g ×ₐ ı ⟩.
  Proof.
    exists (Curry f).
    split.
    - now rewrite <-(fst (projT2 (exp_ump Z Y (Y ⇒ Z @ C) X f))).
    - intros x' H'.
      simpl.
      apply (snd (projT2 (exp_ump Z Y (Y ⇒ Z @ C) X f))).
      now rewrite H'.
  Defined.

  Lemma CurryUncurry
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    (f : X [~>] (Y ⇒ Z @ C))
    : Curry (Uncurry f) ≡ f.
  Proof.
    unfold Curry, Uncurry; simpl.
    rewrite (snd (projT2 (@exp_ump _ _ Z Y (Y ⇒ Z @ C) _ _))); [reflexivity |].
    f_equiv.
    reflexivity.
  Qed.

  Lemma UncurryCurry
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    (f : X ×ₒ Y @ C [~>] Z)
    : Uncurry (Curry f) ≡ f.
  Proof.
    unfold Curry, Uncurry; simpl.
    rewrite (snd (projT2 (@bin_prod_ump _ (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) _ _ _))).
    - symmetry.
      apply (fst (projT2 (@exp_ump _ _ Z Y (Y ⇒ Z @ C) X f))).
    - rewrite ->arrow_comp_id_l.
      split.
      + rewrite (snd (projT2 (@exp_ump _ _ Z Y (Y ⇒ Z @ C) _ _)) (Curry f)).
        * simpl; now rewrite <-(proj1 (fst (projT2 (@bin_prod_ump C (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) _ _ _)))).
        * apply (fst (projT2 (CurryUnique f))).
      + rewrite (snd (projT2 (@exp_ump _ _ Z Y (Y ⇒ Z @ C) _ _)) (Curry f)).
        * simpl; rewrite <-(proj2 (fst (projT2 (@bin_prod_ump C (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) _ _ _)))).
          now rewrite arrow_comp_id_l.
        * apply (fst (projT2 (CurryUnique f))).
  Qed.

  Program Definition binProjAssoc {C : Category}
    `{hasBinaryProducts C}
    {X Y Z : C}
    : (X ×ₒ Y @ C) ×ₒ Z @ C [~>] X ×ₒ (Y ×ₒ Z @ C) @ C
    := ⟨π₁ ∘ π₁, ⟨π₂ ×ₐ ı⟩⟩.

  Program Definition binProjAssocInv {C : Category}
    `{hasBinaryProducts C}
    {X Y Z : C}
    : X ×ₒ (Y ×ₒ Z @ C) @ C [~>] (X ×ₒ Y @ C) ×ₒ Z @ C
    := ⟨⟨ı ×ₐ π₁⟩, π₂ ∘ π₂⟩.

  (* Lemma binProjAssocIso1 {C : Category} *)
  (*   `{hasBinaryProducts C} *)
  (*   {X Y Z : C} *)
  (*   : @binProjAssocInv _ _ X Y Z ∘ @binProjAssoc _ _ X Y Z ≡ ı. *)
  (* Proof. *)
  (*   unfold binProjAssoc, binProjAssocInv. *)
  (*   rewrite <-(snd (projT2 (bin_prod_ump _ _ (X ×ₒ Y @ C ×ₒ Z @ C) *)
  (*                            (X ×ₒ Y @ C ×ₒ Z @ C) *)
  (*                            (π₁ ∘ ı) *)
  (*                            (π₂ ∘ ı))) *)
  (*               ((⟨ ⟨ ı ×ₐ π₁ ⟩, π₂ ∘ π₂ ⟩) ∘ (⟨ π₁ ∘ π₁, ⟨ π₂ ×ₐ ı ⟩ ⟩))). *)
  (*   - now apply (snd (projT2 (bin_prod_ump (X ×ₒ Y @ C) Z (X ×ₒ Y @ C ×ₒ Z @ C) (X ×ₒ Y @ C ×ₒ Z @ C) (π₁ ∘ ı) (π₂ ∘ ı)))). *)
  (*   - split. *)
  (*     + rewrite <-arrow_comp_assoc. *)
  (*       rewrite ArrBinUnrec1. *)
  (*       rewrite arrow_comp_id_r. *)

  (*       admit. *)
  (*     + rewrite <-arrow_comp_assoc. *)
  (*       rewrite ArrBinUnrec2.         *)
  (*       rewrite arrow_comp_assoc. *)
  (*       rewrite !ArrBinUnrec2. *)
  (*       rewrite <-(proj2 (fst (projT2 (bin_prod_ump Y Z (Y ×ₒ Z @ C) (X ×ₒ Y @ C ×ₒ Z @ C) (π₂ ∘ π₁) (ı ∘ π₂))))). *)
  (*       now rewrite arrow_comp_id_l, arrow_comp_id_r. *)
  (* Admitted. *)

  Program Definition ExpCompose
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    : (Y ⇒ Z @ C) ×ₒ (X ⇒ Y @ C) @ C [~>] X ⇒ Z @ C
    := projT1 (exp_ump Z X (X ⇒ Z @ C)
                 ((Y ⇒ Z @ C) ×ₒ (X ⇒ Y @ C) @ C)
                 (eval ∘ ⟨π₁ ∘ π₁, eval ∘ ⟨π₂ ∘ π₁, π₂⟩⟩)).

  Program Definition ExpId {C : Category}
    `{hasTerminal C}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X : C}
    : 𝟙 @ C [~>] X ⇒ X @ C
    := projT1 (exp_ump X X (X ⇒ X @ C) (𝟙 @ C) π₂).

  (* Lemma ExpIdL {C : Category} *)
  (*   `{hasTerminal C} *)
  (*   `{hasBinaryProducts C} *)
  (*   `{hasExp C} *)
  (*   {X Y : C} *)
  (*   (f : 𝟙 @ C [~>] X ⇒ Y @ C) *)
  (*   : ExpCompose ∘ (⟨ f, ExpId ⟩ : 𝟙 @ C [~>] ((X ⇒ Y @ C) ×ₒ (X ⇒ X @ C) @ C)) ≡ f. *)
  (* Proof. *)
  (*   rewrite <-(CurryUncurry f). *)

  (*   unfold ExpCompose. *)
  (*   pose proof (snd (projT2 (exp_ump Y X (X ⇒ Y @ C) (X ⇒ Y @ C ×ₒ X ⇒ X @ C @ C) *)
  (*                              (eval ∘ (⟨ π₁ ∘ π₁, eval ∘ (⟨ π₂ ∘ π₁, π₂ ⟩)⟩))))). *)
  (*   - reflexivity. *)
  (*   - rewrite ArrBinUnrecProp. *)
  (*     rewrite <-arrow_comp_assoc. *)

  (*     pose proof (snd (projT2 (exp_ump Y X (X ⇒ Y @ C) *)
  (*                                (X ⇒ Y @ C ×ₒ X ⇒ X @ C @ C) *)
  (*                                (eval ∘ (⟨ π₁ ∘ π₁, eval ∘ (⟨ π₂ ∘ π₁, π₂ ⟩)⟩))))). *)


  Program Definition ExpUnique
    {C : Category}
    `{hasBinaryProducts C}
    (X Y : C) (a b : Exp X Y)
    : Isomorphism a b :=
    {|
      iso1 := (projT1 (@exp_ump _ _ X Y b a eval));
      iso2 := (projT1 (@exp_ump _ _ X Y a b eval));
    |}.
  Next Obligation.
    intros ? ? X Y a b.
    pose proof (fst (projT2 (@exp_ump _ _ X Y b a eval))) as H'.
    rewrite ->(fst (projT2 (@exp_ump _ _ X Y a b eval))) in H'.
    rewrite arrow_comp_assoc in H'.
    rewrite ArrBinProdComp in H'.
    rewrite arrow_comp_id_l in H'.
    rewrite <-(snd (projT2 (@exp_ump _ _ X Y a a eval)) _ H'); clear H'.
    apply (snd (projT2 (@exp_ump _ _ X Y a a eval)) ı).
    simpl.
    rewrite (snd (projT2 (@bin_prod_ump C a Y (a ×ₒ Y @ C) _ _ _)));
      [symmetry; apply arrow_comp_id_r |].
    now rewrite !arrow_comp_id_l !arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros ? ? X Y a b.
    pose proof (fst (projT2 (@exp_ump _ _ X Y a b eval))) as H'.
    rewrite ->(fst (projT2 (@exp_ump _ _ X Y b a eval))) in H'.
    rewrite arrow_comp_assoc in H'.
    rewrite ArrBinProdComp in H'.
    rewrite arrow_comp_id_l in H'.
    rewrite <-(snd (projT2 (@exp_ump _ _ X Y b b eval)) _ H'); clear H'.
    apply (snd (projT2 (@exp_ump _ _ X Y b b eval)) ı).
    simpl.
    rewrite (snd (projT2 (@bin_prod_ump C b Y (b ×ₒ Y @ C) _ _ _)));
      [symmetry; apply arrow_comp_id_r |].
    now rewrite !arrow_comp_id_l !arrow_comp_id_r.
  Qed.

  Program Definition pick {C : Category}
    `{!hasTerminal C} `{!hasBinaryProducts C} `{!hasExp C} {X : C} :
    X [~>] (𝟙 @ C ⇒ X @ C) := (Curry π₁).

  Lemma UncurryComp {C : Category}
    `{!hasBinaryProducts C} `{!hasExp C}
    {W X Y Z : C}
    {f : X [~>] Y ⇒ Z @ C} {g : W [~>] X} :
    Uncurry (f ∘ g) ≡ Uncurry f ∘ ⟨ g ×ₐ ı ⟩.
  Proof.
    unfold Uncurry.
    Opaque ArrBinProd.
    simpl.
    rewrite arrow_comp_assoc.
    f_equiv.
    rewrite <-((snd (projT2
                      (bin_prod_ump (Y ⇒ Z @ C) Y
                         (Y ⇒ Z @ C ×ₒ Y @ C)
                         (W ×ₒ Y @ C) (f ∘ g ∘ π₁) (ı ∘ π₂))))
                ((⟨ f ×ₐ ı ⟩) ∘ (⟨ g ×ₐ ı ⟩))).
    - reflexivity.
    - Transparent ArrBinProd.
      split.
      + rewrite <-arrow_comp_assoc.
        simpl.
        rewrite <-(proj1 (fst (projT2
                                (bin_prod_ump (Y ⇒ Z @ C) Y
                                   (Y ⇒ Z @ C ×ₒ Y @ C) (X ×ₒ Y @ C)
                                   (f ∘ π₁) (ı ∘ π₂))))).
        rewrite ->2 arrow_comp_assoc.
        f_equiv.
        now rewrite <-(proj1 (fst (projT2
                                    (bin_prod_ump X Y (X ×ₒ Y @ C)
                                       (W ×ₒ Y @ C) (g ∘ π₁) (ı ∘ π₂))))).
      + rewrite arrow_comp_id_l.
        rewrite <-arrow_comp_assoc.
        simpl.
        rewrite <-(proj2 (fst (projT2
                                (bin_prod_ump (Y ⇒ Z @ C) Y
                                   (Y ⇒ Z @ C ×ₒ Y @ C) (X ×ₒ Y @ C)
                                   (f ∘ π₁) (ı ∘ π₂))))).
        rewrite arrow_comp_id_l.
        rewrite <-(proj2 (fst (projT2
                                (bin_prod_ump X Y (X ×ₒ Y @ C)
                                   (W ×ₒ Y @ C) (g ∘ π₁) (ı ∘ π₂))))).
        now rewrite arrow_comp_id_l.
  Qed.

  Opaque ArrBinProd.

  Program Definition ExpFunctor {C : Category}
    `{!hasBinaryProducts C}
    `{!hasExp C} : ((C op) × C) [⇒] C :=
    {|
      FO A := (fst A) ⇒ (snd A) @ C;
      functor.fmap A B := λₛ f, (projT1 (@exp_ump C _ _ _ ((fst B) ⇒ (snd B) @ C) ((fst A) ⇒ (snd A) @ C)
                                           ((snd f) ∘ eval ∘ ⟨(arrow_id ((fst A) ⇒ (snd A) @ C)) ×ₐ (fst f)⟩)));
    |}.
  Next Obligation.
    intros; simpl.
    destruct A as [A1 A2]; destruct B as [B1 B2].
    destruct a₁ as [f1 f2]; destruct a₂ as [g1 g2].
    simpl in *.
    destruct H as [H1 H2].
    apply (snd (projT2 (exp_ump B2 B1 (B1 ⇒ B2 @ C) (A1 ⇒ A2 @ C)
                          (f2 ∘ eval ∘ (⟨ ı ×ₐ f1 ⟩))))).
    rewrite H2.
    rewrite H1.
    clear H1 H2.
    apply (fst (projT2 (exp_ump B2 B1 (B1 ⇒ B2 @ C) (A1 ⇒ A2 @ C)
                          (g2 ∘ eval ∘ (⟨ ı ×ₐ g1 ⟩))))).
  Qed.
  Next Obligation.
    intros; simpl.
    destruct A as [A1 A2].
    simpl.
    apply (snd (projT2 (exp_ump A2 A1 (A1 ⇒ A2 @ C) (A1 ⇒ A2 @ C)
                          (ı ∘ eval ∘ (⟨ ı ×ₐ ı ⟩)))) ı).
    rewrite arrow_comp_id_l.
    f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    destruct A as [A1 A2]; destruct B as [B1 B2]; destruct C0 as [C1 C2];
      destruct f as [f1 f2]; destruct g as [g1 g2].
    simpl in *.
    apply (snd (projT2 (exp_ump C2 C1 (C1 ⇒ C2 @ C) (A1 ⇒ A2 @ C)
                          (f2 ∘ g2 ∘ eval ∘ (⟨ ı ×ₐ g1 ∘ f1 ⟩))))).
    rewrite <-ArrBinProdCompL.
    rewrite <-ArrBinProdCompR.
    rewrite <-arrow_comp_assoc.
    rewrite <-arrow_comp_assoc.
    rewrite <-(fst (projT2 (exp_ump C2 C1 (C1 ⇒ C2 @ C) (B1 ⇒ B2 @ C) (f2 ∘ eval ∘ (⟨ ı ×ₐ f1 ⟩))))).
    rewrite !arrow_comp_assoc.
    f_equiv.
    assert (g2 ∘ (eval ∘ ((⟨ ı ×ₐ g1 ⟩) ∘ (⟨ ı ×ₐ f1 ⟩)))
              ≡
              (g2 ∘ eval ∘ (⟨ ı ×ₐ g1 ⟩)) ∘ (⟨ ı ×ₐ f1 ⟩)) as ->.
    { now rewrite !arrow_comp_assoc. }
    assert (g2 ∘ eval ∘ (⟨ ı ×ₐ g1 ⟩) ∘ (⟨ ı ×ₐ f1 ⟩)
              ≡ eval ∘ (⟨ projT1 (exp_ump B2 B1 (B1 ⇒ B2 @ C) (A1 ⇒ A2 @ C) (g2 ∘ eval ∘ (⟨ ı ×ₐ g1 ⟩))) ×ₐ ı ⟩)
              ∘ (⟨ ı ×ₐ f1 ⟩)) as ->.
    { do 2 f_equiv. apply (fst (projT2 (exp_ump B2 B1 (B1 ⇒ B2 @ C) (A1 ⇒ A2 @ C) (g2 ∘ eval ∘ (⟨ ı ×ₐ g1 ⟩))))). }
    rewrite arrow_comp_assoc.
    f_equiv.
    rewrite ArrBinProdCompL.
    rewrite ArrBinProdCompR.
    rewrite !arrow_comp_id_l.
    reflexivity.
  Qed.

  Program Definition ExpFunctorL {C : Category}
    `{!hasBinaryProducts C}
    `{!hasExp C} (B : C) : (C op) [⇒] C :=
    {|
      FO A := ExpFunctor (A, B);
      functor.fmap A B' := λₛ f, (@fmap (C op × C) C ExpFunctor (A, B) (B', B) (f, ı));
    |}.
  Next Obligation.
    intros; simpl.
    pose proof (ExpFunctor_obligation_1 C _ _ (A, B) (B', B) (a₁, ı) (a₂, ı)) as G.
    simpl in G.
    apply G.
    now split.
  Qed.
  Next Obligation.
    intros; simpl.
    pose proof (ExpFunctor_obligation_2 C _ _ (A, B)) as G.
    simpl in G.
    apply G.
  Qed.
  Next Obligation.
    intros; simpl.
    pose proof (ExpFunctor_obligation_3 C _ _ (A, B) (B0, B) (C0, B)) as G.
    simpl in G.
    specialize (G (f, ı) (g, ı)).
    simpl in G.
    rewrite <-G.
    simpl in *.
    symmetry.
    apply (snd (projT2 (exp_ump B C0 (C0 ⇒ B @ C) (A ⇒ B @ C) (ı ∘ ı ∘ eval ∘ (⟨ ı ×ₐ g ∘ f ⟩))))).
    rewrite arrow_comp_id_l.
    apply (fst (projT2 (exp_ump B C0 (C0 ⇒ B @ C) (A ⇒ B @ C) (ı ∘ eval ∘ (⟨ ı ×ₐ g ∘ f ⟩))))).
  Qed.

  Program Definition ExpFunctorR {C : Category}
    `{!hasBinaryProducts C}
    `{!hasExp C} (B : C op) : C [⇒] C :=
    {|
      FO A := ExpFunctor (B, A);
      functor.fmap A B' := λₛ f, (@fmap (C op × C) C ExpFunctor (B, A) (B, B') (ı, f));
    |}.
  Next Obligation.
    intros; simpl.
    pose proof (ExpFunctor_obligation_1 C _ _ (B, A) (B, B') (ı, a₁) (ı, a₂)) as G.
    simpl in G.
    apply G.
    now split.
  Qed.
  Next Obligation.
    intros; simpl.
    pose proof (ExpFunctor_obligation_2 C _ _ (B, A)) as G.
    simpl in G.
    apply G.
  Qed.
  Next Obligation.
    intros; simpl.
    pose proof (ExpFunctor_obligation_3 C _ _ (B, A) (B, B0) (B, C0)) as G.
    simpl in G.
    specialize (G (ı, f) (ı, g)).
    simpl in G.
    rewrite <-G.
    simpl in *.
    symmetry.
    apply (snd (projT2 (exp_ump C0 B (B ⇒ C0 @ C) (B ⇒ A @ C) (f ∘ g ∘ eval ∘ (⟨ ı ×ₐ ı ∘ ı ⟩))))).
    rewrite arrow_comp_id_l.
    apply (fst (projT2 (exp_ump C0 B (B ⇒ C0 @ C) (B ⇒ A @ C) (f ∘ g ∘ eval ∘ (⟨ ı ×ₐ ı ⟩))))).
  Qed.

  Transparent ArrBinProd.

End Aux.

Notation "'λ⟨' f '⟩'" := (Curry f) (at level 50) : cat_scope.
