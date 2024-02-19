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
  instances.sets
  instances.presheaf
  sgdt.nat.

From stdpp Require Import
  base
  numbers.

Require Import classes.limits.
Require Import classes.exp.
Require Import classes.subobject.
Require Import internal_lang.presheaf.

Section compat.

  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.
  Local Open Scope logic_scope.

  Class Dist A := dist : nat → relation A.
  Global Hint Mode Dist ! : typeclass_instances.
  Notation NonExpansive f := (∀ n, Proper (dist n ==> dist n) f).
  Notation NonExpansive2 f := (∀ n, Proper (dist n ==> dist n ==> dist n) f).

  Definition PROP : Type := GlobalSections (Ω @ tree).
  Local Instance PROP_EQUIV : Equiv PROP := λ a b, ∀ n γ, a n γ n ı ≡ b n γ n ı.
  Local Instance PROP_DIST : Dist PROP := λ n a b, (a n) ≡ (b n).
  Definition bi_entails : PROP → PROP → Prop := λ a b, a ⊢ b.
  Definition bi_emp : PROP := true.
  Definition bi_pure : Prop → PROP := pure.
  Definition bi_and : PROP → PROP → PROP := conj.
  Definition bi_or : PROP → PROP → PROP := disj.
  Definition bi_impl : PROP → PROP → PROP := impl.
  Definition bi_later : PROP → PROP := later.
  Program Definition bi_forall : ∀ A, (A → PROP) → PROP
  := λ A f, λₙ x, λₛ γ, λᵢ d, λₛ g, ∀ q (e : q [~>] d) (r : A), f r x γ q (g ∘ e).
  Next Obligation.
    intros; simpl.
    now rewrite H.
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
    - apply (setoid_arr_eq _ _ ((η f r) x) a₁ a₂ H q (Nat.le_trans q d x e f0)).
      apply H0.
    - apply (setoid_arr_eq _ _ ((η f r) x) a₁ a₂ H q (Nat.le_trans q d x e f0)).
      apply H0.
  Qed.
  Next Obligation.
    intros.
    intros ???.
    split; intros.
    - intros ???.
      specialize (H q e r).
      rewrite (eta_comp (f r) _ _ f0 a q (f1 ∘ e)) in H.
      simpl in H.
      simpl.
      erewrite (proof_irrel (Nat.le_trans q d X e (Nat.le_trans d Y X f1 f0))).
      apply H.
    - intros ???.
      specialize (H q e r).
      rewrite (eta_comp (f r) _ _ f0 a q (f1 ∘ e)).
      simpl in H.
      simpl.
      erewrite (proof_irrel (Nat.le_trans q Y X (Nat.le_trans q d Y e f1) f0)).
      apply H.
  Qed.
  Program Definition bi_exist : ∀ A, (A → PROP) → PROP
  := λ A f, λₙ x, λₛ γ, λᵢ p, λₛ t, ∃ (r : A), f r x γ p t.
  Next Obligation.
    intros; simpl.
    now rewrite H.
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

  Close Scope logic_scope.

  Bind Scope bi_scope with PROP.
  Local Infix "⊢" := bi_entails.
  Local Notation "▷ P" := (bi_later P) (at level 50) : bi_scope.
  Local Notation "'emp'" := bi_emp : bi_scope.
  Local Notation "'True'" := (bi_pure True) : bi_scope.
  Local Notation "'False'" := (bi_pure False) : bi_scope.
  Local Notation "'⌜' φ '⌝'" := (bi_pure φ%type%stdpp) : bi_scope.
  Local Infix "∧" := bi_and : bi_scope.
  Local Infix "∨" := bi_or : bi_scope.
  Local Infix "→" := bi_impl : bi_scope.
  Local Notation "∀ x .. y , P" :=
    (bi_forall _ (λ x, .. (bi_forall _ (λ y, P%logic)) ..)) : bi_scope.
  Local Notation "∃ x .. y , P" :=
    (bi_exist _ (λ x, .. (bi_exist _ (λ y, P%logic)) ..)) : bi_scope.

  Lemma bi_mixin_forall_intro {A} P (Ψ : A → PROP) : (∀ a, P ⊢ Ψ a) → P ⊢ ∀ a, Ψ a.
  Proof.
    intros H.
    intros ??????.
    apply sieve_closed.
    now apply H.
  Qed.
  Lemma bi_mixin_forall_elim {A} {Ψ : A → PROP} a : (∀ a, Ψ a) ⊢ Ψ a.
  Proof.
    intros n γ H.
    specialize (H n ı a).
    rewrite arrow_comp_id_l in H.
    apply H.
  Qed.
  Lemma bi_mixin_exist_intro {A} {Ψ : A → PROP} a : Ψ a ⊢ ∃ a, Ψ a.
  Proof.
    intros n γ H.
    exists a.
    apply H.
  Qed.
  Lemma bi_mixin_exist_elim {A} (Φ : A → PROP) Q : (∀ a, Φ a ⊢ Q) → (∃ a, Φ a) ⊢ Q.
  Proof.
    intros H n γ [r G].
    apply (H r n γ G).
  Qed.
  Lemma bi_mixin_forall_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (bi_forall A).
  Proof.
    intros ??????.
    split; intros G; intros q e r.
    - rewrite <-(H r a q (f ∘ e)).
      apply G.
    - rewrite (H r a q (f ∘ e)).
      apply G.
  Qed.
  Lemma bi_mixin_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (bi_exist A).
  Proof.
    intros ??????.
    split; intros [r G]; exists r.
    - apply (H r a d f).
      apply G.
    - apply (H r a d f).
      apply G.
  Qed.
  Lemma bi_mixin_equiv_entails (P Q : PROP) : (PROP_EQUIV P Q) ↔ (P ⊢ Q) ∧ (Q ⊢ P).
  Proof.
    split.
    - intros H.
      split.
      + intros n γ G.
        rewrite <-(H n γ).
        apply G.
      + intros n γ G.
        rewrite (H n γ).
        apply G.
    - intros [H1 H2].
      intros n γ.
      split; intros G.
      + apply H1.
        apply G.
      + apply H2.
        apply G.
  Qed.
  Definition bi_mixin_pure_intro (φ : Prop) P : φ → P ⊢ ⌜ φ ⌝ := pure_intro.
  Definition bi_mixin_pure_elim' (φ : Prop) P : (φ → True ⊢ P) → ⌜ φ ⌝ ⊢ P := pure_elim φ.
  Definition bi_mixin_and_elim_l P Q : P ∧ Q ⊢ P := conj_elim_l.
  Definition bi_mixin_and_elim_r P Q : P ∧ Q ⊢ Q := conj_elim_r.
  Definition bi_mixin_and_intro P Q R : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R := conj_intro.
  Definition bi_mixin_or_intro_l P Q : P ⊢ P ∨ Q := disj_intro_l.
  Definition bi_mixin_or_intro_r P Q : Q ⊢ P ∨ Q := disj_intro_r.
  Definition bi_mixin_or_elim P Q R : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R := disj_elim.
  Definition bi_mixin_impl_intro_r P Q R : (P ∧ Q ⊢ R) → P ⊢ (bi_impl Q R) := impl_intro.
  Lemma bi_mixin_impl_elim_l' P Q R : (P ⊢ bi_impl Q R) → P ∧ Q ⊢ R.
  Proof.
    intros H.
    apply impl_elim'.
    apply H.
  Qed.
  Lemma bi_mixin_entails_po : PreOrder bi_entails.
  Proof.
    constructor.
    - intros X.
      apply entails_refl.
    - intros X Y Z.
      apply entails_trans.
  Qed.
  Lemma bi_mixin_pure_ne n : Proper (iff ==> dist n) bi_pure.
  Proof.
    intros P Q H γ m f.
    apply H.
  Qed.
  Lemma bi_mixin_and_ne : NonExpansive2 bi_and.
  Proof.
    intros n P Q H X Y G γ m f.
    split.
    - intros J.
      split; simpl.
      + rewrite <-(H γ m f).
        apply J.
      + rewrite <-(G γ m f).
        apply J.
    - intros J.
      split; simpl.
      + rewrite (H γ m f).
        apply J.
      + rewrite (G γ m f).
        apply J.
  Qed.
  Lemma bi_mixin_or_ne : NonExpansive2 bi_or.
  Proof.
    intros n P Q H X Y G γ m f.
    split.
    - intros J.
      destruct J as [J | J].
      + left.
        rewrite <-(H γ m f).
        apply J.
      + right.
        rewrite <-(G γ m f).
        apply J.
    - intros J.
      destruct J as [J | J].
      + left.
        rewrite (H γ m f).
        apply J.
      + right.
        rewrite (G γ m f).
        apply J.
  Qed.
  Lemma bi_mixin_impl_ne : NonExpansive2 bi_impl.
  Proof.
    intros n P Q H X Y G γ m f.
    split.
    - intros J.
      intros q e K.
      apply (G γ q (f ∘ e)).
      apply J.
      rewrite (H γ q (f ∘ e)).
      apply K.
    - intros J.
      intros q e K.
      apply (G γ q (f ∘ e)).
      apply J.
      rewrite <-(H γ q (f ∘ e)).
      apply K.
  Qed.
  Transparent later.
  Definition bi_mixin_later_mono P Q : (P ⊢ Q) → ▷ P ⊢ ▷ Q := later_mono P Q.
  Definition bi_mixin_later_intro P : P ⊢ ▷ P := later_intro P.
  Lemma bi_mixin_later_ne : NonExpansive bi_later.
  Proof.
    intros n P Q H γ m f.
    split.
    - intros G.
      destruct m as [| m].
      + constructor.
      + simpl.
        simpl in G.
        erewrite <-(H γ m _).
        apply G.
    - intros G.
      destruct m as [| m].
      + constructor.
      + simpl.
        simpl in G.
        erewrite (H γ m _).
        apply G.
  Qed.
  Lemma bi_mixin_later_false_em P : ▷ P ⊢ ▷ False ∨ (▷ False → P).
  Proof.
    intros ???.
    destruct n as [| n].
    - now left.
    - right.
      intros q e G.
      destruct q as [| q].
      + simpl.
        erewrite (proof_irrel (Nat.le_trans 0 (S n) (S n) e (le_n (S n)))).
        apply (@sieve_closed _ _ ((η P) (S n) γ) _ 0 _ (le_0_n _) H).
      + exfalso; apply G.
  Qed.
  Lemma bi_mixin_later_forall_2 {A} (Φ : A → PROP) : (∀ a, (bi_later (Φ a))) ⊢ ▷ ∀ a, Φ a.
  Proof.
    intros n γ H.
    destruct n as [| n].
    - constructor.
    - intros q e r.
      simpl.
      erewrite (proof_irrel (Nat.le_trans q n (S n) e (le_Sn_le n (S n) (le_n (S n))))).
      apply (H (S q) (le_n_S _ _ e) r).
  Qed.
  Lemma bi_mixin_later_exist_false {A} (Φ : A → PROP) :
    (▷ ∃ a, Φ a) ⊢ ▷ False ∨ (∃ a, bi_later (Φ a)).
  Proof.
    intros n γ H.
    destruct n as [| n].
    - now left.
    - right.
      destruct H as [r H].
      exists r.
      simpl.
      erewrite (proof_irrel (le_Sn_le n (S n) (le_n (S n)))).
      apply H.
  Qed.
  Opaque later.

End compat.
