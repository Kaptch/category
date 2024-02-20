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

Require Import classes.limits.
Require Import classes.exp.
Require Import classes.subobject.
Require Import internal_lang.presheaf.

From iris.bi Require Export bi.

Section adj.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Program Definition OfeArrSetoid (A B : ofe) : Setoid.
  Proof.
    unshelve econstructor.
    - apply (ofe_mor A B).
    - intros f g.
      apply (f ≡ g)%stdpp.
    - apply _.
  Defined.

  Program Definition OfeCat : Category :=
    {|
      Obj := ofe;
      Arr A B := OfeArrSetoid A B;
    |}.
  Next Obligation.
    intros; simpl.
    refine (λne x, x).
  Defined.
  Next Obligation.
    intros; simpl.
    unshelve econstructor.
    - intros f.
      unshelve econstructor.
      + intros g.
        unshelve econstructor.
        * intros x.
          apply f, g, x.
        * solve_proper.
      + solve_proper.
    - solve_proper.
  Defined.
  Next Obligation.
    intros; simpl.
    intros ?; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; reflexivity.
  Qed.

  Program Definition UnOFE' (O : OfeCat) : tree :=
    {|
      FO _ := {| setoid_carrier := ofe_car O; setoid_eq := ofe_equiv O |};
      functor.fmap A B := λₛ _, idS;
    |}.
  Next Obligation.
    intros; simpl; intros ?.
    apply (@ofe_equivalence O).
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    apply (@ofe_equivalence O).
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    apply (@ofe_equivalence O).
  Qed.

  Program Definition UnOFE : OfeCat [⇒] tree :=
    {|
      FO X := UnOFE' X;
      functor.fmap A B := λₛ f, λₙ x, λₛ y, f y;
    |}.
  Next Obligation.
    intros; simpl.
    apply (@ofe_equivalence B).
    now rewrite H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?.
    apply (@ofe_equivalence B).
  Qed.
  Next Obligation.
    intros; simpl.
    intros n a.
    f_equiv.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros n a.
    apply (@ofe_equivalence A).
  Qed.
  Next Obligation.
    intros; simpl.
    intros n a.
    apply (@ofe_equivalence C).
  Qed.

  (* Program Definition NuOFE' (X : tree) : OfeCat. *)
  (* Proof. *)
  (*   unshelve econstructor. *)
  (*   - apply (GlobalSections X). *)
  (*   - intros n x y. *)
  (*     apply (x n Point ≡ y n Point). *)
  (*   - intros x y. *)
  (*     apply (x ≡ y). *)
  (*   - split. *)
  (*     + intros x y. *)
  (*       split. *)
  (*       * intros H n. *)
  (*         apply H. *)
  (*       * intros H. *)
  (*         intros n γ. *)
  (*         apply H0. *)
  (*         simpl in H0. *)
  (*     apply setoid_equiv. *)
  (*     simpl. *)
  (*     apply _. *)

  (* Program Definition NuOFE : tree [⇒] OfeCat := *)
  (*   {| *)
  (*     FO X := UnOFE' X; *)
  (*     functor.fmap A B := λₛ f, λₙ x, λₛ y, f y; *)
  (*   |}. *)

End adj.

Section compat.

  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.
  Local Open Scope logic_scope.

  Local Definition PROP : Type := GlobalSections (Ω @ tree).

  Local Instance PROP_EQUIV : Equiv PROP := λ a b, ∀ n γ, a n γ n ı ≡ b n γ n ı.
  Local Instance PROP_DIST : Dist PROP := λ n a b, (a n) ≡ (b n).
  Local Definition PROP_entails : PROP → PROP → Prop := λ a b, a ⊢ᵢ b.

  Lemma intuit_all_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (intuit_all A).
  Proof.
    intros ??????.
    split; intros G; intros q e r.
    - rewrite <-(H r a q (f ∘ e)).
      apply G.
    - rewrite (H r a q (f ∘ e)).
      apply G.
  Qed.

  Lemma intuit_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (intuit_exist A).
  Proof.
    intros ??????.
    split; intros [r G]; exists r.
    - apply (H r a d f).
      apply G.
    - apply (H r a d f).
      apply G.
  Qed.

  Lemma equiv_entails (P Q : PROP) : (PROP_EQUIV P Q) ↔ (PROP_entails P Q) ∧ (PROP_entails Q P).
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

  Lemma entails_po : PreOrder PROP_entails.
  Proof.
    constructor.
    - intros X.
      apply entails_refl.
    - intros X Y Z.
      apply entails_trans.
  Qed.

  Lemma pure_ne n : Proper (iff ==> dist n) pure.
  Proof.
    intros P Q H γ m f.
    apply H.
  Qed.

  Lemma conj_ne : NonExpansive2 conj.
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

  Lemma disj_ne : NonExpansive2 disj.
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

  Lemma impl_ne : NonExpansive2 presheaf.impl.
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

  Transparent nat.later.

  Lemma later_ne : NonExpansive nat.later.
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

  Opaque nat.later.

  Close Scope logic_scope.

  Lemma psh_nat_bi_mixin :
    BiMixin
      PROP_entails true pure conj disj presheaf.impl
      (@intuit_all NatCat) (@intuit_exist NatCat) conj presheaf.impl.
  Proof.
    split.
    - exact: entails_po.
    - exact: equiv_entails.
    - exact: pure_ne.
    - exact: conj_ne.
    - exact: disj_ne.
    - exact: impl_ne.
    - exact: intuit_all_ne.
    - exact: intuit_exist_ne.
    - exact: conj_ne.
    - exact: impl_ne.
    - intros; now apply pure_intro.
    - intros; now apply pure_elim.
    - intros; now apply conj_elim_l.
    - intros; now apply conj_elim_r.
    - intros; now apply conj_intro.
    - intros; now apply disj_intro_l.
    - intros; now apply disj_intro_r.
    - intros; now apply disj_elim.
    - intros; now apply impl_intro.
    - intros; now apply impl_elim'.
    - intros; now apply intuit_all_intro.
    - intros; now apply intuit_all_elim.
    - intros; now apply intuit_exist_intro.
    - intros; now apply intuit_exist_elim.
    - intros P P' Q Q' H1 H2. apply conj_intro.
      + by eapply entails_trans; first apply conj_elim_l.
      + by eapply entails_trans; first apply conj_elim_r.
    - intros P. apply conj_intro.
      + apply true_intro.
      + apply entails_refl.
    - intros P. apply conj_elim_r.
    - intros P Q. apply conj_intro; [ apply conj_elim_r | apply conj_elim_l ].
    - intros P Q R. apply conj_intro; [| apply conj_intro].
      + eapply entails_trans; first apply conj_elim_l. by apply conj_elim_l.
      + eapply entails_trans; first apply conj_elim_l. by apply conj_elim_r.
      + apply conj_elim_r.
    - now intros; apply impl_intro.
    - now intros; apply impl_elim'.
  Qed.

  Lemma psh_nat_bi_persistently_mixin :
    BiPersistentlyMixin
      PROP_entails true conj
      (@intuit_exist NatCat) conj id.
  Proof.
    split.
    - unfold id; now intros ????.
    - done.
    - now unfold id.
    - done.
    - now unfold id.
    - now unfold id.
    - intros; apply conj_elim_l.
    - now unfold id.
  Qed.

  Lemma psh_nat_bi_later_mixin :
    BiLaterMixin
      PROP_entails pure disj presheaf.impl
      (@intuit_all NatCat) (@intuit_exist NatCat) conj id nat.later.
  Proof.
    split.
    - apply later_ne.
    - exact: later_mono.
    - exact: later_intro.
    - exact: @later_intuit_forall.
    - exact: @later_intuit_exist_false.
    - intros P Q.
      apply conj_intro; apply later_mono.
      + apply conj_elim_l.
      + apply conj_elim_r.
    - intros P Q.
      apply (entails_trans _ (intuit_all _ (λ b : bool, nat.later (if b then P else Q)))).
      { apply intuit_all_intro=> -[].
        - apply conj_elim_l.
        - apply conj_elim_r.
      }
      eapply entails_trans.
      + apply later_intuit_forall.
      + apply later_mono.
        apply conj_intro.
        * refine (intuit_all_elim Datatypes.true).
        * refine (intuit_all_elim Datatypes.false).
    - now unfold id.
    - now unfold id.
    - exact: later_false_em.
  Qed.

  (* why? *)
  Lemma PROP_OFE : OfeMixin PROP.
  Proof.
    split.
    - intros x y.
      split.
      + intros H n γ m f.
        pose proof (H n γ).
        admit.
      + intros H n.
        admit.
    - intros n.
      unfold dist.
      unfold PROP_DIST.
      split.
      + now intros a.
      + now intros a b H.
      + intros a b c H G.
        etransitivity; eassumption.
    - intros n m x y H f.
      intros γ p g.
      simpl in g.
      assert (fg : p <= n).
      {
        etransitivity.
        - apply g.
        - apply Nat.lt_le_incl, f.
      }
      pose proof (H Point p fg).
      admit.
  Admitted.

  Lemma PROP_COFE : Cofe (Ofe PROP PROP_OFE).
  Proof.
    unshelve econstructor.
    - intros c.
      admit.
    - admit.
  Admitted.

  Canonical Structure TreePropI : bi.
  Proof.
    refine {|
      bi_bi_mixin := psh_nat_bi_mixin;
      bi_bi_persistently_mixin := psh_nat_bi_persistently_mixin;
      bi_bi_later_mixin := psh_nat_bi_later_mixin;
      |}.
    apply PROP_COFE.
  Defined.

  Global Instance PROP_pure_forall : BiPureForall PROP.
  Proof.
    intros A ϕ.
    intros ???.
    unfold bi_pure.
    intros a.
    apply (H n ı a).
  Qed.

  Transparent nat.later.

  (* Global Instance PROP_later_contractive : BiLaterContractive TreePropI. *)
  (* Proof. *)
  (*   intros n P Q H a i f. *)
  (*   destruct i as [| i]. *)
  (*   - done. *)
  (*   - unfold bi_later, nat.later. *)
  (*     simpl. *)
  (*     split; intros G. *)
  (*     + destruct n as [| n]. *)
  (*       * inversion f. *)
  (*       * destruct H. *)
  (*         simpl in f. *)
  (* Admitted. *)

  Opaque nat.later.

  Lemma PROP_plainly_mixin : BiPlainlyMixin TreePropI id.
  Proof.
    split; try done.
    - intros; unfold id, plainly.
      intros ??????.
      apply H.
    - intros P Q. apply conj_elim_l.
  Qed.

  Global Instance PROP_plainlyC : BiPlainly TreePropI :=
    {| bi_plainly_mixin := PROP_plainly_mixin |}.

  (* Lemma PROP_internal_eq_mixin : BiInternalEqMixin TreePropI (@PROP_internal_eq). *)
  (* Proof. *)
  (*   split. *)
  (*   - exact: internal_eq_ne. *)
  (*   - exact: @internal_eq_refl. *)
  (*   - exact: @internal_eq_rewrite. *)
  (*   - exact: @fun_ext. *)
  (*   - exact: @sig_eq. *)
  (*   - exact: @discrete_eq_1. *)
  (*   - exact: @later_eq_1. *)
  (*   - exact: @later_eq_2. *)
  (* Qed. *)
  (* Global Instance PROP_internal_eq : BiInternalEq TreePropI := *)
  (*   {| bi_internal_eq_mixin := PROP_internal_eq_mixin |}. *)

  (* Global Instance PROP_prop_ext : BiPropExt TreePropI. *)
  (* Proof. exact: prop_ext_2. Qed. *)

  Global Instance PROP_affine : BiAffine TreePropI | 0.
  Proof. intros P. exact: pure_intro. Qed.

  Global Instance PROP_plain (P : PROP) : Plain P | 0.
  Proof.
    intros ???.
    unfold id.
    done.
  Qed.

  Global Instance PROP_persistent (P : PROP) : Persistent P.
  Proof.
    intros ???.
    unfold id.
    done.
  Qed.

  Global Instance PROP_plainly_exist_1 : BiPlainlyExist TreePropI.
  Proof.
    intros ???.
    unfold id.
    done.
  Qed.
End compat.

Module PROP.
  Section restate.
    Lemma pure_soundness φ : (⊢@{TreePropI} ⌜ φ ⌝) → φ.
    Proof.
      apply soundness.
      apply 0.
    Qed.

    (* Lemma internal_eq_soundness {A : tree} (x y : GlobalSections A) : (⊢@{TreePropI} x ≡ y) → x ≡ y. *)
    (* Proof. apply internal_eq_soundness. Qed. *)

    Lemma later_soundness (P : TreePropI) : (⊢ ▷ P) → ⊢ P.
    Proof.
      intros H.
      apply later_elim.
      apply H.
    Qed.

  End restate.
End PROP.

Opaque PROP_entails.

Require Import iris.proofmode.proofmode.

Example test1 {A B : PROP} : ⊢ ∀ n : nat, ⌜n < 0⌝ -∗ A ∗ B -∗ True.
Proof.
  iIntros (n) "%H (a & b)".
  iPureIntro.
  constructor.
Qed.

Example test2 : ⊢@{TreePropI} ⌜∀ n : nat, n >= 0⌝.
Proof.
  iPureIntro.
  lia.
Qed.

Example test3 : ∀ n : nat, n >= 0.
Proof.
  apply PROP.pure_soundness.
  apply test2.
Qed.
