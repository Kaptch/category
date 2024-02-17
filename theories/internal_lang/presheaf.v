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
  Notation "'⌜' P '⌝'" := (pure P) : logic_scope.

  Definition entails {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) : Prop :=
    ∀ n γ, P n γ n ı → Q n γ n ı.

  Infix "⊢" := entails (at level 99, no associativity) : logic_scope.

  Local Open Scope logic_scope.

  Lemma entails_refl {Γ : PSh C} (P : Γ [~>] Ω @ (PSh C)) :
    P ⊢ P.
  Proof.
    now intros n x Px.
  Qed.

  Lemma entails_trans {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    P ⊢ Q →
    Q ⊢ R →
    P ⊢ R.
  Proof.
    intros H1 H2 n x Px.
    apply H2, H1, Px.
  Qed.

  Lemma entails_subst {Γ A : PSh C} (t : Γ [~>] A) (P Q : A [~>] Ω @ (PSh C)) :
    P ⊢ Q →
    P ∘ t ⊢ Q ∘ t.
  Proof.
    now intros H n x Ptx; apply H.
  Qed.

  Lemma eq_refl {Γ A : PSh C} (t : Γ [~>] A) :
    ⊤ᵢ ⊢ t ≡ᵢ t.
  Proof.
    intros ???.
    simpl.
    reflexivity.
  Qed.

  Lemma eq_sym {Γ A : PSh C} (t u : Γ [~>] A) :
    t ≡ᵢ u ⊢ u ≡ᵢ t.
  Proof.
    intros n x H; simpl.
    rewrite H.
    reflexivity.
  Qed.

  Lemma eq_trans {Γ A : PSh C} (t u v : Γ [~>] A) :
    t ≡ᵢ u ∧ᵢ u ≡ᵢ v ⊢ t ≡ᵢ v.
  Proof.
    intros n x [H1 H2]; simpl in *.
    now rewrite H1, H2.
  Qed.

  Lemma eq_subst {Γ A B : PSh C} (t u : Γ [~>] A) (D : A [~>] B) :
    t ≡ᵢ u ⊢ D ∘ t ≡ᵢ D ∘ u.
  Proof.
    intros n x He; simpl in *.
    unfold compose; simpl.
    rewrite <-(@eta_comp _ _ _ _ D n n ı ((η u) n x)).
    rewrite <-(@eta_comp _ _ _ _ D n n ı ((η t) n x)).
    simpl.
    unfold compose; simpl.
    f_equiv.
    apply He.
  Qed.

  Lemma eq_coerce {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) :
    P ≡ᵢ Q ∧ᵢ P ⊢ Q.
  Proof.
    intros n x [He HP]; simpl in *.
    specialize (He n ı).
    rewrite arrow_comp_id_l in He.
    now apply He.
  Qed.

  Lemma true_intro {Γ : PSh C} {P : Γ [~>] Ω @ (PSh C)} :
    P ⊢ ⊤ᵢ.
  Proof.
    now intros.
  Qed.

  Lemma false_elim {Γ : PSh C} {P : Γ [~>] Ω @ (PSh C)} :
    ⊥ᵢ ⊢ P.
  Proof.
    now intros.
  Qed.

  Lemma conj_intro {Γ : PSh C} {R P Q : Γ [~>] Ω @ (PSh C)} :
    R ⊢ P →
    R ⊢ Q →
    R ⊢ P ∧ᵢ Q.
  Proof.
    intros HP HQ n x Rx; simpl.
    split; [apply HP | apply HQ]; assumption.
  Qed.

  Lemma conj_elim_l {Γ : PSh C} {P Q : Γ [~>] Ω @ (PSh C)} :
    P ∧ᵢ Q ⊢ P.
  Proof.
    intros n x [Px Qx].
    simpl in *.
    assumption.
  Qed.

  Lemma conj_elim_r {Γ : PSh C} {P Q : Γ [~>] Ω @ (PSh C)} :
    P ∧ᵢ Q ⊢ Q.
  Proof.
    intros n x [Px Qx].
    simpl in *.
    assumption.
  Qed.

  Lemma disj_intro_l {Γ : PSh C} {P Q : Γ [~>] Ω @ (PSh C)} :
    P ⊢ P ∨ᵢ Q.
  Proof.
    intros n x Px; left; simpl in *.
    assumption.
  Qed.

  Lemma disj_intro_r {Γ : PSh C} {P Q : Γ [~>] Ω @ (PSh C)} :
    Q ⊢ P ∨ᵢ Q.
  Proof.
    intros n x Px; right; simpl in *.
    assumption.
  Qed.

  Lemma disj_elim {Γ : PSh C} {P Q R : Γ [~>] Ω @ (PSh C)} :
    P ⊢ R →
    Q ⊢ R →
    P ∨ᵢ Q ⊢ R.
  Proof.
    intros HP HQ n x [Px | Qx]; [apply HP | apply HQ]; assumption.
  Qed.

  Lemma impl_intro {Γ : PSh C} {P Q R : Γ [~>] Ω @ (PSh C)} :
    R ∧ᵢ P ⊢ Q →
    R ⊢ P →ᵢ Q.
  Proof.
    intros H n x Rx j Hj Px; simpl in *.
    specialize (H j (fmap Γ Hj x)).
    simpl in H.
    rewrite arrow_comp_id_l.
    rewrite arrow_comp_id_l in Px.
    pose proof (@eta_comp _ _ _ _ Q _ _ Hj x j ı) as G.
    simpl in G.
    unfold compose in G; simpl in G.
    rewrite arrow_comp_id_r in G.
    apply G; clear G.
    apply H.
    split.
    - apply (@eta_comp _ _ _ _ R _ _ Hj x j ı).
      simpl.
      apply sieve_closed.
      pose proof (@sieve_closed C _ ((η R) n x) n j ı Hj Rx) as K.
      rewrite arrow_comp_id_l in K.
      apply K.
    - apply (@eta_comp _ _ _ _ P _ _ Hj x j ı).
      simpl.
      now rewrite arrow_comp_id_r.
  Qed.

  Lemma impl_elim {Γ : PSh C} {P Q : Γ [~>] Ω @ (PSh C)} :
    (P →ᵢ Q) ∧ᵢ P ⊢ Q.
  Proof.
    intros n x [H Px]; simpl in *.
    specialize (H n ı).
    assert (Px' : (η P) n x n (ı ∘ ı)).
    { now rewrite arrow_comp_id_l. }
    specialize (H Px').
    rewrite arrow_comp_id_l in H.
    apply H.
  Qed.

  Lemma all_intro {Γ A : PSh C} (R : Γ [~>] Ω @ (PSh C)) (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) :
    R ∘ bin_proj_arr₁ _ _ _ ⊢ P →
    R ⊢ ∀ᵢ[A] P.
  Proof.
    intros H n x Rx j Hj y; simpl.
    apply H; simpl.
    unfold compose; simpl.
    apply (@eta_comp _ _ _ _ R _ _ (ı ∘ Hj) x j ı).
    simpl.
    rewrite arrow_comp_id_l, arrow_comp_id_r.
    pose proof (@sieve_closed C _ ((η R) n x) n j ı Hj Rx) as K.
    rewrite arrow_comp_id_l in K.
    apply K.
  Qed.

  Lemma all_elim {Γ A : PSh C} (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) (t : Γ [~>] A) :
    ∀ᵢ[A] P ⊢ P ∘ ⟨ ı , t ⟩.
  Proof.
    intros n x H; simpl in *.
    unfold compose; simpl.
    unfold id; simpl.
    specialize (H n ı ((η t) n x)).
    eapply (@setoid_arr_eq _ _ ((η P) n)); [| apply H].
    split; [| reflexivity].
    simpl.
    rewrite arrow_comp_id_l.
    now rewrite (@fmap_id (C op) SetoidCat Γ n x).
  Qed.

  Lemma exist_intro {Γ A : PSh C} (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) (t : Γ [~>] A) :
    P ∘ (⟨ ı , t ⟩) ⊢ ∃ᵢ[A] P.
  Proof.
    intros n x Px; simpl in *.
    exists (t n x).
    unfold compose in Px; simpl in Px.
    eapply (@setoid_arr_eq _ _ ((η P) n)); [| apply Px].
    split; [| reflexivity].
    simpl.
    now rewrite (@fmap_id (C op) SetoidCat Γ n x).
  Qed.

  Lemma exist_elim {Γ A} (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) (Q : Γ [~>] Ω @ (PSh C)) :
    P ⊢ Q ∘ bin_proj_arr₁ _ _ _ → ∃ᵢ[A] P ⊢ Q.
  Proof.
    intros H n x [y Py]; simpl in *.
    unfold compose in *; simpl in *.
    apply (H n (x, y)).
    assert ((η P) n (x, y) n ı ≡ (η P) n (fmap Γ ı x, y) n ı) as ->; [| assumption].
    apply (@setoid_arr_eq _ _ ((η P) n)).
    split; simpl.
    - symmetry.
      apply (@fmap_id (C op) SetoidCat Γ n x).
    - reflexivity.
  Qed.

  Lemma pure_intro {Γ : PSh C} {P : Γ [~>] Ω @ (PSh C)} {Q : Prop} (q : Q) :
    P ⊢ ⌜ Q ⌝.
  Proof.
    intros H n x.
    apply q.
  Qed.

  Opaque entails true false conj disj impl all exist pure.

  Lemma false_elim' {Γ : PSh C} (R P : Γ [~>] Ω @ (PSh C)) :
    R ⊢ ⊥ᵢ →
    R ⊢ P.
  Proof.
    intros H.
    eapply entails_trans; [apply H |].
    apply false_elim.
  Qed.

  Lemma conj_true_l_inv {Γ : PSh C} (P : Γ [~>] Ω @ (PSh C)) :
    P ⊢ ⊤ᵢ ∧ᵢ P.
  Proof.
    apply conj_intro; [apply true_intro | apply entails_refl].
  Qed.

  Lemma conj_true_r_inv {Γ : PSh C} (P : Γ [~>] Ω @ (PSh C)) :
    P ⊢ P ∧ᵢ ⊤ᵢ.
  Proof.
    apply conj_intro; [apply entails_refl | apply true_intro].
  Qed.

  Lemma conj_comm {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) :
    P ∧ᵢ Q ⊢ Q ∧ᵢ P.
  Proof.
    apply conj_intro.
    - apply conj_elim_r.
    - apply conj_elim_l.
  Qed.

  Lemma conj_mono {Γ : PSh C} (P P' Q Q' : Γ [~>] Ω @ (PSh C)) :
    P ⊢ P' →
    Q ⊢ Q' →
    P ∧ᵢ Q ⊢ P' ∧ᵢ Q'.
  Proof.
    intros H1 H2.
    apply conj_intro.
    - eapply entails_trans; [| apply H1].
      apply conj_elim_l.
    - eapply entails_trans; [| apply H2].
      apply conj_elim_r.
  Qed.

  Lemma conj_mono_l {Γ : PSh C} (P P' Q : Γ [~>] Ω @ (PSh C)) :
    P ⊢ P' →
    P ∧ᵢ Q ⊢ P' ∧ᵢ Q.
  Proof.
    intros H.
    eapply conj_mono.
    - apply H.
    - apply entails_refl.
  Qed.

  Lemma conj_mono_r {Γ : PSh C} (P Q Q' : Γ [~>] Ω @ (PSh C)) :
    Q ⊢ Q' →
    P ∧ᵢ Q ⊢ P ∧ᵢ Q'.
  Proof.
    intros H.
    eapply conj_mono.
    - apply entails_refl.
    - apply H.
  Qed.

  Lemma conj_elim_l' {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ P ∧ᵢ Q →
    R ⊢ P.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply conj_elim_l.
  Qed.

  Lemma conj_elim_r' {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ P ∧ᵢ Q →
    R ⊢ P.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply conj_elim_l.
  Qed.

  Lemma disj_false_l {Γ : PSh C} (P : Γ [~>] Ω @ (PSh C)) :
    ⊥ᵢ ∨ᵢ P ⊢ P.
  Proof.
    eapply disj_elim.
    - apply false_elim.
    - apply entails_refl.
  Qed.

  Lemma disj_false_r {Γ : PSh C} (P : Γ [~>] Ω @ (PSh C)) :
    P ∨ᵢ ⊥ᵢ ⊢ P.
  Proof.
    eapply disj_elim.
    - apply entails_refl.
    - apply false_elim.
  Qed.

  Lemma disj_comm {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) :
    P ∨ᵢ Q ⊢ Q ∨ᵢ P.
  Proof.
    eapply disj_elim.
    - apply disj_intro_r.
    - apply disj_intro_l.
  Qed.

  Lemma disj_mono {Γ : PSh C} (P P' Q Q' : Γ [~>] Ω @ (PSh C)) :
    P ⊢ P' →
    Q ⊢ Q' →
    P ∨ᵢ Q ⊢ P' ∨ᵢ Q'.
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
    P ⊢ P' →
    P ∨ᵢ Q ⊢ P' ∨ᵢ Q.
  Proof.
    intros H.
    apply disj_mono.
    - apply H.
    - apply entails_refl.
  Qed.

  Lemma disj_mono_r {Γ : PSh C} (P Q Q' : Γ [~>] Ω @ (PSh C)) :
    Q ⊢ Q' →
    P ∨ᵢ Q ⊢ P ∨ᵢ Q'.
  Proof.
    intros H.
    apply disj_mono.
    - apply entails_refl.
    - apply H.
  Qed.

  Lemma disj_intro_l' {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ P →
    R ⊢ P ∨ᵢ Q.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply disj_intro_l.
  Qed.

  Lemma disj_intro_r' {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ Q →
    R ⊢ P ∨ᵢ Q.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply disj_intro_r.
  Qed.

  Lemma impl_elim' {Γ : PSh C} (P Q R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ P →ᵢ Q →
    R ∧ᵢ P ⊢ Q.
  Proof.
    intros H.
    eapply entails_trans.
    - apply conj_mono_l, H.
    - apply impl_elim.
  Qed.

  Lemma entails_impl {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) :
    P ⊢ Q →
    ⊤ᵢ ⊢ P →ᵢ Q.
  Proof.
    intros H.
    apply impl_intro.
    apply entails_trans with P.
    - apply conj_elim_r.
    - apply H.
  Qed.

  Lemma impl_entails {Γ : PSh C} (P Q : Γ [~>] Ω @ (PSh C)) :
    ⊤ᵢ ⊢ P →ᵢ Q →
    P ⊢ Q.
  Proof.
    intros H.
    apply entails_trans with (⊤ᵢ ∧ᵢ P).
    - apply conj_true_l_inv.
    - apply impl_elim', H.
  Qed.

  Lemma all_elim' {Γ A} (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) (t : Γ [~>] A) (R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ ∀ᵢ[A] P →
    R ⊢ P ∘ ⟨ ı , t ⟩.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply all_elim.
  Qed.

  Lemma exist_intro' {Γ A} (P : Γ ×ₒ A @ (PSh C) [~>] Ω @ (PSh C)) (t : Γ [~>] A) (R : Γ [~>] Ω @ (PSh C)) :
    R ⊢ P ∘ (⟨ ı , t ⟩) →
    R ⊢ ∃ᵢ[A] P.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply exist_intro.
  Qed.

  Lemma soundness {P : Prop} (n : C) :
    ⊤ᵢ ⊢ @pure (𝟙 @ (PSh C)) P → P.
  Proof.
    intros H.
    apply (H n Point).
    constructor.
  Qed.

  Lemma soundness_eq {A B : PSh C} (t u : 𝟙 @ (PSh C) [~>] A) :
    ⊤ᵢ ⊢ t ≡ᵢ u → t ≡ u.
  Proof.
    intros H.
    intros x.
    assert (G : (η ⊤ᵢ) x Point x ı).
    { constructor. }
    pose proof (H x Point G) as J.
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

  Inductive LogicSyntax : ∀ (Γ : PSh C), Type :=
  | LS_pure Γ (p : Prop) : LogicSyntax Γ
  | LS_false Γ : LogicSyntax Γ
  | LS_true Γ : LogicSyntax Γ
  | LS_eq Γ {A} (a b : Γ [~>] A) : LogicSyntax Γ
  | LS_xist Γ {A} (a : LogicSyntax (Γ ×ₒ A @ PSh C)) : LogicSyntax Γ
  | LS_all Γ {A} (a : LogicSyntax (Γ ×ₒ A @ PSh C)) : LogicSyntax Γ
  | LS_conj Γ (a b : LogicSyntax Γ) : LogicSyntax Γ
  | LS_disj Γ (a b : LogicSyntax Γ) : LogicSyntax Γ
  | LS_impl Γ (a b : LogicSyntax Γ) : LogicSyntax Γ.

  (* Program Definition LogicF : PSh (PSh C) := *)
  (*   {| *)
  (*     FO X := [ LogicSyntax X ]; *)
  (*     fmap A B := λₛ f, λₛ x, _; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   intros A B f x; simpl. *)


  Fixpoint LogicInterp {Γ : PSh C} (t : LogicSyntax Γ) :
    Γ [~>] (Ω @ PSh C) :=
    match t in (LogicSyntax Γ') return (Γ' [~>] (Ω @ PSh C)) with
    | LS_pure Γ' p => pure p
    | LS_false Γ' => false
    | LS_true Γ' => true
    | LS_eq Γ' a b => eq a b
    | LS_xist Γ' a => exist _ (LogicInterp a)
    | LS_all Γ' a => all _ (LogicInterp a)
    | LS_conj Γ' a b => conj (LogicInterp a) (LogicInterp b)
    | LS_disj Γ' a b => disj (LogicInterp a) (LogicInterp b)
    | LS_impl Γ' a b => impl (LogicInterp a) (LogicInterp b)
    end.

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
Notation "'⌜' P '⌝'" := (pure P) : logic_scope.

Infix "⊢" := entails (at level 99, no associativity) : logic_scope.
