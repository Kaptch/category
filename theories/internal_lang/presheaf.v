From category Require Import
  base
  setoid
  category
  sets
  terminal
  functor
  limit
  prod
  exp
  pullback
  subobject
  classes.limits
  classes.exp
  classes.subobject
  instances.sets
  instances.presheaf.

Declare Scope logic.
Delimit Scope logic_scope with logic.

Section IntLogic.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.

  Program Definition DiscretePSh (D : Type)
    : PSh C :=
    {|
      FO _ := [D];
      fmap A B := λₛ f, ı;
    |}.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.

  Definition GlobalSections : Functor (PSh C) SetoidCat := hom.HomR (𝟙 @ (PSh C)).

  Program Definition trueI : 𝟙 @ (PSh C) [~>] Ω @ (PSh C)
    := PSh_true_arr.

  Program Definition falseI : 𝟙 @ (PSh C) [~>] Ω @ (PSh C)
    := λₙ _, λₛ _, λᵢ _, λₛ _, False.
  Next Obligation.
    intros; simpl in *.
    reflexivity.
  Qed.
  Next Obligation.
    intros; now simpl in *.
  Qed.
  Next Obligation.
    intros; now simpl in *.
  Qed.
  Next Obligation.
    intros; now simpl in *.
  Qed.

  Program Definition eqI {X : PSh C} : X ×ₒ X @ (PSh C) [~>] Ω @ (PSh C)
    := λₙ x, λₛ y, λᵢ p, λₛ t, (fmap X t (fst y) ≡ fmap X t (snd y)).
  Next Obligation.
    intros; simpl in *.
    now rewrite H.
  Qed.
  Next Obligation.
    intros ?? [? ?] ?????; simpl in *.
    rewrite (@fmap_comp _ _ X _ _ _ g f); simpl.
    unfold compose; simpl.
    now rewrite H.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros d f.
    now rewrite (fst H), (snd H).
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros [? ?] ? g.
    rewrite (@fmap_comp _ _ X _ _ _ g f).
    reflexivity.
  Qed.

  Program Definition conjI : (Ω @ (PSh C)) ×ₒ (Ω @ (PSh C)) @ (PSh C) [~>] Ω @ (PSh C) :=
    λₙ x, λₛ y, λᵢ p, λₛ t, (fst y p t) ∧ (snd y p t).
  Next Obligation.
    intros; simpl in *.
    now rewrite H.
  Qed.
  Next Obligation.
    intros; simpl in *.
    split; now apply sieve_closed.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros; simpl.
    now rewrite (fst H), (snd H).
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros; simpl.
    split; now intros H.
  Qed.

  Program Definition disjI : (Ω @ (PSh C)) ×ₒ (Ω @ (PSh C)) @ (PSh C) [~>] Ω @ (PSh C) :=
    λₙ x, λₛ y, λᵢ p, λₛ t, (fst y p t) ∨ (snd y p t).
  Next Obligation.
    intros; simpl in *.
    now rewrite H.
  Qed.
  Next Obligation.
    intros ?????? [|]; simpl in *; [left | right];
      now apply sieve_closed.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros; simpl.
    now rewrite (fst H), (snd H).
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros; simpl.
    split; now intros H.
  Qed.

  Program Definition implI : (Ω @ (PSh C)) ×ₒ (Ω @ (PSh C)) @ (PSh C) [~>] Ω @ (PSh C) :=
    λₙ x, λₛ y, λᵢ p, λₛ t, (∀ q (e : q [~>] p), fst y q (t ∘ e) → snd y q (t ∘ e)).
  Next Obligation.
    intros; simpl in *.
    split; intros G q e J.
    - rewrite <-H.
      apply G.
      rewrite H.
      apply J.
    - rewrite H.
      apply G.
      rewrite <-H.
      apply J.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros q e' K.
    rewrite arrow_comp_assoc.
    apply H.
    rewrite <-arrow_comp_assoc.
    apply K.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros d f.
    split; intros G q e J.
    - rewrite <-(snd H).
      apply G.
      now rewrite (fst H).
    - rewrite (snd H).
      apply G.
      now rewrite <-(fst H).
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros a d f'.
    split; intros J q e K.
    - rewrite arrow_comp_assoc.
      apply J.
      rewrite <-arrow_comp_assoc.
      apply K.
    - rewrite <-arrow_comp_assoc.
      apply J.
      rewrite arrow_comp_assoc.
      apply K.
  Qed.

  Program Definition allI {X : PSh C} : (X ⇒ (Ω @ (PSh C)) @ (PSh C)) [~>] Ω @ (PSh C) :=
    λₙ x, λₛ y, λᵢ p, λₛ t, ∀ q (e : q [~>] p), ∀ (r : X q), (y q (t ∘ e) r q ı).
  Next Obligation.
    intros; simpl in *.
    split; intros q e r r'.
    - simpl in *.
      unshelve erewrite <-(@arr_ext C X PSh_sieve x y e (a₁ ∘ r) (a₂ ∘ r) _ r' r' _ e ı).
      + now rewrite H.
      + reflexivity.
      + apply q.
    - simpl in *.
      unshelve erewrite (@arr_ext C X PSh_sieve x y e (a₁ ∘ r) (a₂ ∘ r) _ r' r' _ e ı).
      + now rewrite H.
      + reflexivity.
      + apply q.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros q e' r.
    unshelve erewrite (@arr_ext C X PSh_sieve x y q (f ∘ g ∘ e') (f ∘ (g ∘ e')) _ r r _ q ı).
    - now rewrite arrow_comp_assoc.
    - reflexivity.
    - apply (H q (g ∘ e') r).
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros d f; split; intros G q e r; apply H, G.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros a d f'; split; intros G q e r.
    - unshelve erewrite (@arr_ext C X PSh_sieve _ a q (f ∘ f' ∘ e) (f ∘ (f' ∘ e)) _ r r _ q ı).
      + now rewrite arrow_comp_assoc.
      + reflexivity.
      + apply G.
    - unshelve erewrite <-(@arr_ext C X PSh_sieve _ a q (f ∘ f' ∘ e) (f ∘ (f' ∘ e)) _ r r _ q ı).
      + now rewrite arrow_comp_assoc.
      + reflexivity.
      + apply G.
  Qed.

  Program Definition existI {X : PSh C} : (X ⇒ (Ω @ (PSh C)) @ (PSh C)) [~>] Ω @ (PSh C) :=
    λₙ x, λₛ y, λᵢ p, λₛ t, ∃ (r : X p), y p t r p ı.
  Next Obligation.
    intros; simpl in *.
    split; intros [r G]; exists r.
    - now unshelve erewrite <-(@arr_ext C X PSh_sieve x y p a₁ a₂ H r r _ p ı).
    - now unshelve erewrite (@arr_ext C X PSh_sieve x y p a₁ a₂ H r r _ p ı).
  Qed.
  Next Obligation.
    intros; simpl in *.
    destruct H as [r H].
    exists (fmap X g r).
    rewrite (@arr_fmap C X PSh_sieve x y d e g f r e ı).
    simpl.
    rewrite arrow_comp_id_r.
    pose proof (@sieve_closed C _ (y d f r) d e ı g H) as K.
    rewrite arrow_comp_id_l in K.
    apply K.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros d f.
    split; intros [r G]; exists r; now apply H.
  Qed.
  Next Obligation.
    intros; simpl in *; intros a d f'; split; intros [r G]; exists r; apply G.
  Qed.

  Program Definition pureI (P : Prop) : 𝟙 @ (PSh C) [~>] Ω @ (PSh C) :=
    λₙ x, λₛ y, λᵢ p, λₛ t, P.
  Next Obligation.
    intros; simpl in *.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl in *.
    assumption.
  Qed.
  Next Obligation.
    intros; simpl in *.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl in *.
    reflexivity.
  Qed.

  Program Definition intuit_all : ∀ A, (A → (GlobalSections (Ω @ PSh C))) → (GlobalSections (Ω @ PSh C))
  := λ A f, λₙ x, λₛ γ, λᵢ d, λₛ g, ∀ q (e : q [~>] d) (r : A), f r x γ q (g ∘ e).
  Next Obligation.
    intros; simpl.
    split; intros.
    - now rewrite <-H.
    - now rewrite H.
  Qed.
  Next Obligation.
    intros.
    intros q e' r'.
    rewrite arrow_comp_assoc.
    apply (H q (g ∘ e') r').
  Qed.
  Next Obligation.
    intros; simpl.
    intros; split; intros.
    - apply (setoid_arr_eq _ _ ((η f r) x) a₁ a₂ H q (f0 ∘ e)).
      apply H0.
    - apply (setoid_arr_eq _ _ ((η f r) x) a₁ a₂ H q (f0 ∘ e)).
      apply H0.
  Qed.
  Next Obligation.
    intros.
    intros ???.
    split; intros.
    - intros ???.
      specialize (H q e r).
      setoid_rewrite (eta_comp (f r) _ _ f0 a q (f1 ∘ e)) in H.
      simpl in H.
      simpl.
      rewrite arrow_comp_assoc.
      apply H.
    - intros ???.
      specialize (H q e r).
      rewrite (eta_comp (f r) _ _ f0 a q (f1 ∘ e)).
      simpl in H.
      simpl.
      rewrite <-arrow_comp_assoc.
      apply H.
  Qed.

  Program Definition intuit_exist : ∀ A, (A → (GlobalSections (Ω @ PSh C))) → (GlobalSections (Ω @ PSh C))
  := λ A f, λₙ x, λₛ γ, λᵢ p, λₛ t, ∃ (r : A), f r x γ p t.
  Next Obligation.
    intros; simpl.
    split; intros [r G]; exists r.
    - now rewrite <-H.
    - now rewrite H.
  Qed.
  Next Obligation.
    intros; simpl.
    simpl in H.
    destruct H as [r H].
    exists r.
    apply (@sieve_closed _ _ ((η f r) x γ) _ _ _ g H).
  Qed.
  Next Obligation.
    intros; simpl.
    intros; split; intros [r G]; exists r.
    - apply (setoid_arr_eq _ _ ((η f r) x) a₁ a₂ H).
      apply G.
    - apply (setoid_arr_eq _ _ ((η f r) x) a₁ a₂ H).
      apply G.
  Qed.
  Next Obligation.
    intros.
    intros ???.
    split; intros.
    - destruct H as [r H].
      exists r.
      rewrite (eta_comp (f r) _ _ f0 a d f1) in H.
      apply H.
    - destruct H as [r H].
      exists r.
      rewrite (eta_comp (f r) _ _ f0 a d f1).
      apply H.
  Qed.

  Program Definition true {Γ : PSh C} : Γ [~>] Ω @ (PSh C)
    := trueI ∘ (! @ (PSh C)).
  Definition false {Γ : PSh C} : Γ [~>] Ω @ (PSh C)
    := falseI ∘ (! @ (PSh C)).
  Definition eq {Γ A : PSh C} (t u : Γ [~>] A) : Γ [~>] Ω @ (PSh C)
    := eqI ∘ ⟨ t , u ⟩.
  Definition conj {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) : Γ [~>] Ω @ (PSh C)
    := conjI ∘ ⟨ P , Q ⟩.
  Definition disj {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) : Γ [~>] Ω @ (PSh C)
    := disjI ∘ ⟨ P , Q ⟩.
  Definition impl {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) : Γ [~>] Ω @ (PSh C)
    := implI ∘ ⟨ P , Q ⟩.
  Definition all {Γ : PSh C} A (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) : Γ [~>] Ω @ (PSh C)
    := allI ∘ λ⟨ P ⟩.
  Definition exist {Γ : PSh C} A (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) : Γ [~>] Ω @ (PSh C)
    := existI ∘ λ⟨ P ⟩.
  Definition pure {Γ : PSh C} (P : Prop) : Γ [~>] Ω @ (PSh C)
    := pureI P ∘ (! @ (PSh C)).

  Notation "'⊤ᵢ'" := true : logic_scope.
  Notation "'⊥ᵢ'" := false : logic_scope.
  Infix "≡ᵢ" := eq (at level 70, no associativity) : logic_scope.
  Infix "∧ᵢ" := conj (at level 80, right associativity) : logic_scope.
  Infix "∨ᵢ" := disj (at level 85, right associativity) : logic_scope.
  Infix "→ᵢ" := impl (at level 90, right associativity) : logic_scope.
  Notation "∀ᵢ[ A ] P" := (all A P)
                            (at level 95, P at level 95, format "∀ᵢ[ A ]  P") : logic_scope.
  Notation "∃ᵢ[ A ] P" := (exist A P)
                            (at level 95, P at level 95, format "∃ᵢ[ A ]  P") : logic_scope.
  Notation "∀ᵢ x , P" :=
    (intuit_all _ (λ x, P)) (at level 95) : logic_scope.
  Notation "∃ᵢ x , P" :=
    (intuit_exist _ (λ x, P)) (at level 95) : logic_scope.
  Notation "'⌜' P '⌝ᵢ'" := (pure P) : logic_scope.

  Definition entails {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) : Prop :=
    ∀ n γ m f, P n γ m f → Q n γ m f.

  Infix "⊢ᵢ" := entails (at level 99, no associativity) : logic_scope.

  Local Open Scope logic_scope.

  Lemma entails_refl {Γ : PSh C} (P : Γ [~>] Ω @ (PSh C)) :
    P ⊢ᵢ P.
  Proof.
    now intros n γ m f Px.
  Qed.

  Lemma entails_trans {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    P ⊢ᵢ Q →
    Q ⊢ᵢ R →
    P ⊢ᵢ R.
  Proof.
    intros H1 H2 n γ m f Px.
    apply H2, H1, Px.
  Qed.

  Lemma entails_subst {Γ A : PSh C} (t : Γ [~>] A) (P Q : A [~>] Ω @ (PSh C)) :
    P ⊢ᵢ Q →
    P ∘ t ⊢ᵢ Q ∘ t.
  Proof.
    now intros H n γ m f Ptx; apply H.
  Qed.

  Lemma eq_refl {Γ A : PSh C} (t : Γ [~>] A) :
    ⊤ᵢ ⊢ᵢ t ≡ᵢ t.
  Proof.
    intros ?????.
    simpl.
    reflexivity.
  Qed.

  Lemma eq_sym {Γ A : PSh C} (t u : Γ [~>] A) :
    t ≡ᵢ u ⊢ᵢ u ≡ᵢ t.
  Proof.
    intros n γ m f H; simpl.
    rewrite H.
    reflexivity.
  Qed.

  Lemma eq_trans {Γ A : PSh C} (t u v : Γ [~>] A) :
    t ≡ᵢ u ∧ᵢ u ≡ᵢ v ⊢ᵢ t ≡ᵢ v.
  Proof.
    intros n γ m f [H1 H2]; simpl in *.
    now rewrite H1, H2.
  Qed.

  Lemma eq_subst {Γ A B : PSh C} (t u : Γ [~>] A) (D : A [~>] B) :
    t ≡ᵢ u ⊢ᵢ D ∘ t ≡ᵢ D ∘ u.
  Proof.
    intros n γ m f He; simpl in *.
    unfold compose; simpl.
    rewrite <-(@eta_comp _ _ _ _ D n m f ((η u) n γ)).
    rewrite <-(@eta_comp _ _ _ _ D n m f ((η t) n γ)).
    simpl.
    unfold compose; simpl.
    f_equiv.
    apply He.
  Qed.

  Lemma eq_coerce {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) :
    P ≡ᵢ Q ∧ᵢ P ⊢ᵢ Q.
  Proof.
    intros n γ m f [He HP]; simpl in *.
    specialize (He m ı).
    rewrite arrow_comp_id_r in He.
    now apply He.
  Qed.

  Lemma true_intro {Γ : PSh C} {P : Γ [~>] Ω @ (PSh C)} :
    P ⊢ᵢ ⊤ᵢ.
  Proof.
    now intros.
  Qed.

  Lemma false_elim {Γ : PSh C} {P : Γ [~>] Ω @ (PSh C)} :
    ⊥ᵢ ⊢ᵢ P.
  Proof.
    now intros.
  Qed.

  Lemma conj_intro {Γ : PSh C} {R P Q : Γ [~>] Ω @ (PSh C)} :
    R ⊢ᵢ P →
    R ⊢ᵢ Q →
    R ⊢ᵢ P ∧ᵢ Q.
  Proof.
    intros HP HQ n γ m f Rx; simpl.
    split; [apply HP | apply HQ]; assumption.
  Qed.

  Lemma conj_elim_l {Γ : PSh C} {P Q : Γ [~>] Ω @ (PSh C)} :
    P ∧ᵢ Q ⊢ᵢ P.
  Proof.
    intros n γ m f [Px Qx].
    simpl in *.
    assumption.
  Qed.

  Lemma conj_elim_r {Γ : PSh C} {P Q : Γ [~>] Ω @ (PSh C)} :
    P ∧ᵢ Q ⊢ᵢ Q.
  Proof.
    intros n γ m f [Px Qx].
    simpl in *.
    assumption.
  Qed.

  Lemma disj_intro_l {Γ : PSh C} {P Q : Γ [~>] Ω @ (PSh C)} :
    P ⊢ᵢ P ∨ᵢ Q.
  Proof.
    intros n γ m f Px; left; simpl in *.
    assumption.
  Qed.

  Lemma disj_intro_r {Γ : PSh C} {P Q : Γ [~>] Ω @ (PSh C)} :
    Q ⊢ᵢ P ∨ᵢ Q.
  Proof.
    intros n γ m f Px; right; simpl in *.
    assumption.
  Qed.

  Lemma disj_elim {Γ : PSh C} {P Q R : Γ [~>] Ω @ (PSh C)} :
    P ⊢ᵢ R →
    Q ⊢ᵢ R →
    P ∨ᵢ Q ⊢ᵢ R.
  Proof.
    intros HP HQ n γ m f [Px | Qx]; [apply HP | apply HQ]; assumption.
  Qed.

  Lemma impl_intro {Γ : PSh C} {P Q R : Γ [~>] Ω @ (PSh C)} :
    R ∧ᵢ P ⊢ᵢ Q →
    R ⊢ᵢ P →ᵢ Q.
  Proof.
    intros H n γ m f Rx j Hj Px; simpl in *.
    apply (H n γ j (f ∘ Hj)).
    split.
    - apply sieve_closed.
      apply Rx.
    - apply Px.
  Qed.

  Lemma impl_elim {Γ : PSh C} {P Q : Γ [~>] Ω @ (PSh C)} :
    (P →ᵢ Q) ∧ᵢ P ⊢ᵢ Q.
  Proof.
    intros n γ m f [H Px]; simpl in *.
    specialize (H m ı).
    assert (Px' : (η P) n γ m (f ∘ ı)).
    { now rewrite arrow_comp_id_r. }
    specialize (H Px').
    rewrite arrow_comp_id_r in H.
    apply H.
  Qed.

  Lemma all_intro {Γ A : PSh C} (R : Γ [~>] Ω @ (PSh C)) (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) :
    R ∘ π₁ ⊢ᵢ P →
    R ⊢ᵢ ∀ᵢ[A] P.
  Proof.
    intros H n γ m f Rx j Hj y; simpl.
    apply H; simpl.
    unfold compose; simpl.
    apply (@eta_comp _ _ _ _ R _ _ (f ∘ Hj) γ j ı).
    simpl.
    rewrite arrow_comp_id_r.
    apply sieve_closed.
    apply Rx.
  Qed.

  Lemma all_elim {Γ A : PSh C} (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) (t : Γ [~>] A) :
    ∀ᵢ[A] P ⊢ᵢ P ∘ ⟨ ı , t ⟩.
  Proof.
    intros n γ m f H; simpl.
    unfold compose; simpl.
    unfold id; simpl.
    simpl in f.
    specialize (H m ı ((η t) m (fmap Γ f γ))).
    simpl in H.
    pose proof (eta_comp P _ _ (f ∘ ı) (γ, (η t) n γ) m ı) as G.
    simpl in G.
    unfold compose in G.
    simpl in G.
    rewrite <-(arrow_comp_id_r f).
    rewrite <-(arrow_comp_id_r (f ∘ ı)).
    apply G.
    assert ((η P) m (fmap Γ (f ∘ ı) γ, fmap A (f ∘ ı) ((η t) n γ)) m ı
                  ≡ (η P) m (fmap Γ (f ∘ ı) γ, (η t) m (fmap Γ f γ)) m ı) as ->; [| apply H].
    {
      apply (@setoid_arr_eq _ _ ((η P) m)).
      split; [reflexivity |].
      rewrite (eta_comp t _ _ f γ).
      simpl.
      unfold compose; simpl.
      f_equiv.
      now rewrite arrow_comp_id_r.
    }
  Qed.

  Lemma exist_intro {Γ A : PSh C} (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) (t : Γ [~>] A) :
    P ∘ (⟨ ı , t ⟩) ⊢ᵢ ∃ᵢ[A] P.
  Proof.
    intros n γ m f Px.
    exists (t m (fmap Γ f γ)).
    simpl in Px; unfold compose, id in Px; simpl in Px.
    simpl.
    assert ((η P) m (fmap Γ f γ, (η t) m (fmap Γ f γ)) m ı ≡
              (η P) m (fmap Γ f γ, fmap A f ((η t) n γ)) m ı) as ->.
    {
      apply (@setoid_arr_eq _ _ ((η P) m)).
      split; [reflexivity | simpl].
      apply (eta_comp t _ _ f).
    }
    assert (G : (η P) m (fmap (bin_prod_obj _ _ (Γ ×ₒ A @ PSh C)) f (γ, (η t) n γ)) m ı);
      [| apply G].
    rewrite (eta_comp P _ _ f (γ, (η t) n γ) m ı).
    simpl.
    apply sieve_closed.
    apply Px.
  Qed.

  Lemma exist_elim {Γ A} (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) (Q : Γ [~>] Ω @ (PSh C)) :
    P ⊢ᵢ Q ∘ π₁ → ∃ᵢ[A] P ⊢ᵢ Q.
  Proof.
    intros H n γ m f [y Py]; simpl in *.
    unfold compose in *; simpl in *.
    pose proof (H m ((fmap Γ f γ), y) m ı) as J.
    simpl in J.
    pose proof (eta_comp Q _ _ f γ m ı) as J'.
    simpl in J'.
    unfold compose in J'.
    rewrite arrow_comp_id_r in J'.
    apply J'.
    apply J.
    apply Py.
  Qed.

  Lemma pure_intro {Γ : PSh C} {P : Γ [~>] Ω @ (PSh C)} {Q : Prop} (q : Q) :
    P ⊢ᵢ ⌜ Q ⌝ᵢ.
  Proof.
    intros H n γ m f.
    apply q.
  Qed.

  Lemma pure_elim {Γ : PSh C} {P : Γ [~>] Ω @ (PSh C)}
    (φ : Prop) : (φ → ⊤ᵢ ⊢ᵢ P) → (⌜ φ ⌝ᵢ) ⊢ᵢ P.
  Proof.
    intros H n γ m f G.
    apply H.
    - apply G.
    - constructor.
  Qed.

  Lemma intuit_all_intro {A} P (Ψ : A → (GlobalSections (Ω @ PSh C)))
    : (∀ a, P ⊢ᵢ Ψ a) → P ⊢ᵢ ∀ᵢ a, Ψ a.
  Proof.
    intros H.
    intros ????????.
    apply sieve_closed.
    now apply H.
  Qed.

  Lemma intuit_all_elim {A} {Ψ : A → (GlobalSections (Ω @ PSh C))} a
    : (∀ᵢ a, Ψ a) ⊢ᵢ Ψ a.
  Proof.
    intros n γ m f H.
    specialize (H m ı a).
    rewrite arrow_comp_id_r in H.
    apply H.
  Qed.

  Lemma intuit_exist_intro {A} {Ψ : A → (GlobalSections (Ω @ PSh C))} a
    : Ψ a ⊢ᵢ ∃ᵢ a, Ψ a.
  Proof.
    intros n γ m f H.
    exists a.
    apply H.
  Qed.

  Lemma intuit_exist_elim {A} (Φ : A → (GlobalSections (Ω @ PSh C))) Q
    : (∀ a, Φ a ⊢ᵢ Q) → (∃ᵢ a, Φ a) ⊢ᵢ Q.
  Proof.
    intros H n γ m f [r G].
    apply (H r n γ m f G).
  Qed.

  Opaque entails true false conj disj impl all exist pure intuit_all intuit_exist.

  Lemma false_elim' {Γ : PSh C} (R P : Γ [~>] Ω @ (PSh C)) :
    R ⊢ᵢ ⊥ᵢ →
    R ⊢ᵢ P.
  Proof.
    intros H.
    eapply entails_trans; [apply H |].
    apply false_elim.
  Qed.

  Lemma conj_true_l_inv {Γ : PSh C} (P : Γ [~>] Ω @ (PSh C)) :
    P ⊢ᵢ ⊤ᵢ ∧ᵢ P.
  Proof.
    apply conj_intro; [apply true_intro | apply entails_refl].
  Qed.

  Lemma conj_true_r_inv {Γ : PSh C} (P : Γ [~>] Ω @ (PSh C)) :
    P ⊢ᵢ P ∧ᵢ ⊤ᵢ.
  Proof.
    apply conj_intro; [apply entails_refl | apply true_intro].
  Qed.

  Lemma conj_comm {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) :
    P ∧ᵢ Q ⊢ᵢ Q ∧ᵢ P.
  Proof.
    apply conj_intro.
    - apply conj_elim_r.
    - apply conj_elim_l.
  Qed.

  Lemma conj_mono {Γ : PSh C} (P P' Q Q' : Γ [~>] Ω @ (PSh C)) :
    P ⊢ᵢ P' →
    Q ⊢ᵢ Q' →
    P ∧ᵢ Q ⊢ᵢ P' ∧ᵢ Q'.
  Proof.
    intros H1 H2.
    apply conj_intro.
    - eapply entails_trans; [| apply H1].
      apply conj_elim_l.
    - eapply entails_trans; [| apply H2].
      apply conj_elim_r.
  Qed.

  Lemma conj_mono_l {Γ : PSh C} (P P' Q : Γ [~>] Ω @ (PSh C)) :
    P ⊢ᵢ P' →
    P ∧ᵢ Q ⊢ᵢ P' ∧ᵢ Q.
  Proof.
    intros H.
    eapply conj_mono.
    - apply H.
    - apply entails_refl.
  Qed.

  Lemma conj_mono_r {Γ : PSh C} (P Q Q' : Γ [~>] Ω @ (PSh C)) :
    Q ⊢ᵢ Q' →
    P ∧ᵢ Q ⊢ᵢ P ∧ᵢ Q'.
  Proof.
    intros H.
    eapply conj_mono.
    - apply entails_refl.
    - apply H.
  Qed.

  Lemma conj_elim_l' {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ᵢ P ∧ᵢ Q →
    R ⊢ᵢ P.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply conj_elim_l.
  Qed.

  Lemma conj_elim_r' {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ᵢ P ∧ᵢ Q →
    R ⊢ᵢ P.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply conj_elim_l.
  Qed.

  Lemma disj_false_l {Γ : PSh C} (P : Γ [~>] Ω @ (PSh C)) :
    ⊥ᵢ ∨ᵢ P ⊢ᵢ P.
  Proof.
    eapply disj_elim.
    - apply false_elim.
    - apply entails_refl.
  Qed.

  Lemma disj_false_r {Γ : PSh C} (P : Γ [~>] Ω @ (PSh C)) :
    P ∨ᵢ ⊥ᵢ ⊢ᵢ P.
  Proof.
    eapply disj_elim.
    - apply entails_refl.
    - apply false_elim.
  Qed.

  Lemma disj_comm {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) :
    P ∨ᵢ Q ⊢ᵢ Q ∨ᵢ P.
  Proof.
    eapply disj_elim.
    - apply disj_intro_r.
    - apply disj_intro_l.
  Qed.

  Lemma disj_mono {Γ : PSh C} (P P' Q Q' : Γ [~>] Ω @ (PSh C)) :
    P ⊢ᵢ P' →
    Q ⊢ᵢ Q' →
    P ∨ᵢ Q ⊢ᵢ P' ∨ᵢ Q'.
  Proof.
    intros H1 H2.
    apply disj_elim.
    - apply entails_trans with P'.
      + apply H1.
      + apply disj_intro_l.
    - apply entails_trans with Q'.
      + apply H2.
      + apply disj_intro_r.
  Qed.

  Lemma disj_mono_l {Γ : PSh C} (P P' Q : Γ [~>] Ω @ (PSh C)) :
    P ⊢ᵢ P' →
    P ∨ᵢ Q ⊢ᵢ P' ∨ᵢ Q.
  Proof.
    intros H.
    apply disj_mono.
    - apply H.
    - apply entails_refl.
  Qed.

  Lemma disj_mono_r {Γ : PSh C} (P Q Q' : Γ [~>] Ω @ (PSh C)) :
    Q ⊢ᵢ Q' →
    P ∨ᵢ Q ⊢ᵢ P ∨ᵢ Q'.
  Proof.
    intros H.
    apply disj_mono.
    - apply entails_refl.
    - apply H.
  Qed.

  Lemma disj_intro_l' {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ᵢ P →
    R ⊢ᵢ P ∨ᵢ Q.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply disj_intro_l.
  Qed.

  Lemma disj_intro_r' {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ᵢ Q →
    R ⊢ᵢ P ∨ᵢ Q.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply disj_intro_r.
  Qed.

  Lemma impl_elim' {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ᵢ P →ᵢ Q →
    R ∧ᵢ P ⊢ᵢ Q.
  Proof.
    intros H.
    eapply entails_trans.
    - apply conj_mono_l, H.
    - apply impl_elim.
  Qed.

  Lemma entails_impl {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) :
    P ⊢ᵢ Q →
    ⊤ᵢ ⊢ᵢ P →ᵢ Q.
  Proof.
    intros H.
    apply impl_intro.
    apply entails_trans with P.
    - apply conj_elim_r.
    - apply H.
  Qed.

  Lemma impl_entails {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) :
    ⊤ᵢ ⊢ᵢ P →ᵢ Q →
    P ⊢ᵢ Q.
  Proof.
    intros H.
    apply entails_trans with (⊤ᵢ ∧ᵢ P).
    - apply conj_true_l_inv.
    - apply impl_elim', H.
  Qed.

  Lemma all_elim' {Γ A} (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) (t : Γ [~>] A) (R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ᵢ ∀ᵢ[A] P →
    R ⊢ᵢ P ∘ ⟨ ı , t ⟩.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply all_elim.
  Qed.

  Lemma exist_intro' {Γ A} (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) (t : Γ [~>] A) (R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ᵢ P ∘ (⟨ ı , t ⟩) →
    R ⊢ᵢ ∃ᵢ[A] P.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply exist_intro.
  Qed.

  Lemma soundness {P : Prop} (n : C) :
    ⊤ᵢ ⊢ᵢ @pure (𝟙 @ (PSh C)) P → P.
  Proof.
    intros H.
    apply (H n Point n ı).
    constructor.
  Qed.

  Lemma soundness_eq {A B : PSh C} (t u : 𝟙 @ (PSh C) [~>] A) :
    ⊤ᵢ ⊢ᵢ t ≡ᵢ u → t ≡ u.
  Proof.
    intros H.
    intros x.
    assert (G : (η ⊤ᵢ) x Point x ı).
    { constructor. }
    pose proof (H x Point x ı G) as J.
    simpl in J.
    rewrite (@fmap_id _ _ A x ((η t) x Point)) in J.
    rewrite (@fmap_id _ _ A x ((η u) x Point)) in J.
    simpl in J.
    unfold id in J.
    intros x'.
    rewrite PointUnique.
    apply J.
  Qed.

  Program Definition Subobject {X : PSh C} (P : X [~>] Ω @ (PSh C)) : PSh C
    := {|
      FO x := SubsetSetoid (X x) (λ y, P x y x ı);
      fmap A B := λₛ f :: @Arr C B A, λₛ T :: {x : X A | (η P) A x A ı},
        @Specif.exist (X B) _ (fmap X f (proj1_sig T)) _;
    |}.
  Next Obligation.
    intros; simpl in *.
    pose proof (eta_comp P _ _ f (proj1_sig T) B ı) as H.
    simpl in H.
    unfold compose in H.
    simpl in H.
    destruct T as [T1 T2].
    simpl in *.
    apply H.
    apply sieve_closed.
    pose proof (@sieve_closed C _ ((η P) A T1) _ _ ı f T2) as T3.
    rewrite arrow_comp_id_l in T3.
    apply T3.
  Defined.
  Next Obligation.
    intros; simpl in *.
    now rewrite H.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros [a1 a2].
    simpl.
    now rewrite H.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros [a1 a2].
    simpl.
    apply (@fmap_id _ _ X A a1).
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros [a1 a2].
    simpl.
    apply (@fmap_comp _ _ X _ _ _ f g a1).
  Qed.

  Notation "'Σᵢ' P" := (Subobject P) (at level 50).
  Notation "Σᵢ[ X ] P" := (@Subobject X P)
                            (at level 20, right associativity, format "Σᵢ[ X ]  P").

  Program Definition msub {X} (P : X [~>] Ω @ (PSh C)) : Σᵢ P [~>] X
    := λₙ x, λₛ y, proj1_sig y.
  Next Obligation.
    intros; simpl in *.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros [a1 a2]; unfold compose; simpl.
    reflexivity.
  Qed.

  Lemma msub_true {X} (P : X [~>] Ω @ (PSh C)) : P ∘ msub P ≡ trueI ∘ (! @ (PSh C)).
  Proof.
    intros n x.
    simpl.
    intros d f; unfold compose; simpl.
    split.
    - constructor.
    - intros _.
      destruct x as [? ?]; simpl.
      pose proof (@sieve_closed C _ ((η P) n x) _ _ ı f s) as T.
      rewrite arrow_comp_id_l in T.
      apply T.
  Qed.

  Program Definition restr_cod {X Y} {P : X [~>] Ω @ (PSh C)} (f : Y [~>] X)
    (H : P ∘ f ≡ trueI ∘ (! @ (PSh C))) : Y [~>] Σᵢ P :=
    λₙ x, λₛ y, @Specif.exist _ _ (f x y) _.
  Next Obligation.
    intros; simpl in *.
    unfold compose in H.
    now rewrite H.
  Qed.
  Next Obligation.
    intros; simpl in *.
    now rewrite H0.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros a.
    rewrite (eta_comp f _ _ f0 a).
    reflexivity.
  Qed.

  Lemma msub_restr_cod {X Y} {P : X [~>] Ω @ (PSh C)} {f : Y [~>] X}
    (H : P ∘ f ≡ trueI ∘ (! @ (PSh C))) : msub P ∘ restr_cod f H ≡ f.
  Proof.
    intros n; simpl in *.
    intros a; unfold compose; simpl.
    reflexivity.
  Qed.

  Lemma restr_cod_unique {X Y} {P : X [~>] Ω @ (PSh C)} {f : Y [~>] X} {h : Y [~>] Σᵢ P}
    (e : msub P ∘ h ≡ f) : { H : P ∘ f ≡ trueI ∘ (! @ (PSh C)) | h ≡ restr_cod f H }.
  Proof.
    unshelve eexists.
    - rewrite <-e, <-arrow_comp_assoc, msub_true, arrow_comp_assoc.
      rewrite (snd (projT2 (@terminal_proj (PSh C) (𝟙 @ (PSh C)) Y)) ((! @ PSh C) ∘ h)); [| constructor].
      reflexivity.
    - simpl.
      intros X' a.
      rewrite <-(e X' a).
      simpl.
      unfold compose; simpl.
      reflexivity.
  Qed.

End IntLogic.

Notation "'⊤ᵢ'" := true : logic_scope.
Notation "'⊥ᵢ'" := false : logic_scope.
Infix "≡ᵢ" := eq (at level 70, no associativity) : logic_scope.
Infix "∧ᵢ" := conj (at level 80, right associativity) : logic_scope.
Infix "∨ᵢ" := disj (at level 85, right associativity) : logic_scope.
Infix "→ᵢ" := impl (at level 90, right associativity) : logic_scope.
Notation "∀ᵢ[ A ] P" := (all A P)
                          (at level 95, P at level 95, format "∀ᵢ[ A ]  P") : logic_scope.
Notation "∃ᵢ[ A ] P" := (exist A P)
                          (at level 95, P at level 95, format "∃ᵢ[ A ]  P") : logic_scope.
Notation "∀ᵢ x , P" :=
  (intuit_all _ (λ x, P)) (at level 95) : logic_scope.
Notation "∃ᵢ x , P" :=
  (intuit_exist _ (λ x, P)) (at level 95) : logic_scope.
Notation "'⌜' P '⌝ᵢ'" := (pure P) : logic_scope.

Infix "⊢ᵢ" := entails (at level 99, no associativity) : logic_scope.
