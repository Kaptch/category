From category Require Import
  base
  setoid
  sets
  category
  functor.

Section Hom.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.

  Program Definition Hom : ((C op) × C)%cat [⇒] SetoidCat :=
    {|
      FO X := (@Arr C (fst X) (snd X));
      fmap A B := λₛ f, λₛ g, snd f ∘ g ∘ fst f;
    |}.
  Next Obligation.
    now intros [? ?] [? ?] [? ?] ? ? ->.
  Qed.
  Next Obligation.
    intros [? ?] [? ?] [? ?] [? ?] [H1 H2] ?.
    simpl in *.
    f_equiv; [| assumption].
    f_equiv.
    now rewrite H2.
  Qed.
  Next Obligation.
    intros [? ?] ?; simpl.
    now rewrite arrow_comp_id_l arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros [? ?] [? ?] [? ?] [? ?] [? ?] ?; simpl.
    unfold compose; simpl.
    now rewrite !arrow_comp_assoc.
  Qed.

  Program Definition HomR (c : C op) : C [⇒] SetoidCat :=
    {|
      FO X := Hom (c, X);
      fmap A B := λₛ f, λₛ g, f ∘ g;
    |}.
  Next Obligation.
    intros; simpl.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    now do 2 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    now rewrite arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    unfold compose; simpl.
    now rewrite arrow_comp_assoc.
  Qed.

  Program Definition HomL (c : C) : C op [⇒] SetoidCat :=
    {|
      FO X := Hom (X, c);
      fmap A B := λₛ f, λₛ g, g ∘ f;
    |}.
  Next Obligation.
    intros; simpl.
    now do 2 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    now rewrite arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    unfold compose; simpl.
    now rewrite arrow_comp_assoc.
  Qed.

  Program Definition Yoneda_Fun (F : C op [⇒] SetoidCat) : C op [⇒] SetoidCat :=
    {|
      FO c := (HomL c) [↣] F;
      fmap A B := λₛ f :: @Arr C B A, λₛ x, λₙ y, ((x y) ∘ (λₛ z, (f ∘ z)));
    |}.
  Next Obligation.
    intros; simpl.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose.
    pose proof (eta_comp x) as H1.
    simpl in H1.
    unfold compose in H1; simpl in H1.
    rewrite <-H1.
    f_equiv.
    now rewrite arrow_comp_assoc.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose; simpl.
    pose proof (eta_comp a₁ B _ a) as H1.
    simpl in H1.
    unfold compose in H1; simpl in H1.
    rewrite H1.
    pose proof (eta_comp a₂ B _ a) as H2.
    simpl in H2.
    unfold compose in H2; simpl in H2.
    rewrite H2.
    do 2 f_equiv.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose; simpl.
    pose proof (eta_comp a B _ a0) as H1.
    simpl in H1.
    unfold compose in H1; simpl in H1.
    rewrite H1.
    pose proof (eta_comp a B _ a0) as H2.
    simpl in H2.
    unfold compose in H2; simpl in H2.
    rewrite H2.
    do 2 f_equiv.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    rewrite arrow_comp_id_l.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    rewrite arrow_comp_assoc.
    reflexivity.
  Qed.

  Program Definition Yoneda_1 (F : C op [⇒] SetoidCat)
    : (Yoneda_Fun F) [↣] F
    := λₙ c, (λₛ x, x c ı).
  Next Obligation.
    intros; simpl.
    simpl.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    pose proof (eta_comp a X Y f) as H1.
    simpl in H1.
    unfold compose in H1; simpl in H1.
    rewrite <-H1.
    rewrite arrow_comp_id_l arrow_comp_id_r.
    reflexivity.
  Qed.

  Program Definition Yoneda_2 (F : C op [⇒] SetoidCat)
    : F [↣] (Yoneda_Fun F)
    := λₙ c, (λₛ x, λₙ z, λₛ f, (fmap F f x)).
  Next Obligation.
    intros; simpl.
    intros; simpl.
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    unfold compose.
    rewrite (@fmap_comp (C op) SetoidCat F _ _ _ f a x).
    simpl; unfold compose; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    simpl in *.
    rewrite (@fmap_comp (C op) SetoidCat F _ _ _ a0 f).
    simpl.
    reflexivity.
  Qed.

  Lemma Yoneda_12 (F : C op [⇒] SetoidCat) : (Yoneda_2 F) ∘ (Yoneda_1 F) ≡ ı.
  Proof.
    intros x f.
    intros y.
    intros ?; simpl.
    pose proof (eta_comp (Yoneda_1 F) _ _ a) as H.
    simpl in H.
    unfold compose in H.
    simpl in H.
    rewrite <-H.
    clear.
    unfold Yoneda_Fun in f.
    simpl in *.
    now rewrite arrow_comp_id_r.
  Qed.

  Lemma Yoneda_21 (F : C op [⇒] SetoidCat) : (Yoneda_1 F) ∘ (Yoneda_2 F) ≡ ı.
  Proof.
    intros x f.
    rewrite (@fmap_id (C op) SetoidCat F x f).
    simpl; unfold id; reflexivity.
  Qed.
End Hom.
