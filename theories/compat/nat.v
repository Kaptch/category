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

  Program Definition OfeArrSetoid (A B : ofe) : Setoid :=
    {|
      setoid_carrier := (ofe_mor A B);
      setoid_eq X Y := (ofe_equiv _ X Y);
    |}.

  Program Definition OfeCat : Category :=
    {|
      Obj := ofe;
      Arr A B := OfeArrSetoid A B;
      arrow_id A := λne x, x;
      arrow_comp A B C :=
        λₛ (f : OfeArrSetoid B C), λₛ (g : OfeArrSetoid A B), λne x, f (g x);
    |}.
  Next Obligation.
    intros; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros; simpl; solve_proper.
  Qed.
  Next Obligation.
    intros; simpl; solve_proper.
  Qed.
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
      FO U := {|
               setoid_carrier := ofe_car O;
               setoid_eq A B := ∀ n, n <= U → ofe_dist O n A B
             |};
      functor.fmap A B := λₛ f, λₛ s, s;
    |}.
  Next Obligation.
    intros.
    split.
    - intros ???.
      reflexivity.
    - intros ?????.
      symmetry.
      now apply H.
    - intros ???????.
      etransitivity.
      + now apply H.
      + now apply H0.
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    apply (H n (transitivity H0 f)).
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    reflexivity.
  Qed.

  Program Definition UnOFE : OfeCat [⇒] tree :=
    {|
      FO X := UnOFE' X;
      functor.fmap A B := λₛ f, λₙ x, λₛ y, f y;
    |}.
  Next Obligation.
    intros; simpl.
    intros.
    now rewrite (H n H0).
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    f_equiv.
    now rewrite H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    reflexivity.
  Qed.

  Program Definition NuOFE' (X : tree) : OfeCat
    := {|
      ofe_car := GlobalSections X;
      ofe_dist (n : NatCat) x y := ∀ n' (f : n' [~>] n), (x n') ≡ (y n');
      ofe_equiv x y := ∀ a n, x a n ≡ y a n;
    |}.
  Next Obligation.
    intros.
    split.
    - intros; simpl.
      split.
      + intros H n m f ?.
        now rewrite H.
      + intros H m a.
        apply (H m m (reflexivity m) a).
    - intros n.
      split.
      + unfold dist.
        now intros ?.
      + unfold dist.
        intros ?????.
        symmetry; now apply H.
      + unfold dist.
        intros ??? H G ??.
        etransitivity.
        * now apply H.
        * now apply G.
    - unfold dist.
      intros.
      apply (H n').
      eapply arrow_comp.
      + apply Nat.lt_le_incl.
        apply H0.
      + apply f.
  Qed.

  Program Definition NuOFE : tree [⇒] OfeCat :=
    {|
      FO X := NuOFE' X;
      functor.fmap A B := λₛ f, λne x, λₙ t, λₛ r, (f t) (x t r);
    |}.
  Next Obligation.
    intros; simpl.
    now rewrite H.
  Qed.
  Next Obligation.
    intros.
    intros ?.
    simpl.
    rewrite <-(eta_comp f _ _ f0 ((η x) X a)).
    simpl.
    f_equiv.
    rewrite <-(eta_comp x _ _ f0 a).
    simpl.
    f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?????.
    simpl.
    intros ?.
    f_equiv.
    now apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ???; simpl.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ???; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ???; simpl.
    reflexivity.
  Qed.

End adj.

Section compat.

  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.
  Local Open Scope logic_scope.

  Local Definition PROP : Type := GlobalSections (Ω @ tree).

  Local Instance PROP_EQUIV : Equiv PROP
    := λ x y, (ofe_equiv (NuOFE (Ω @ tree)) x y).

  Local Instance PROP_DIST : Dist PROP
    := λ n x y, (ofe_dist (NuOFE (Ω @ tree)) n x y).

  Lemma PROP_OFE : OfeMixin PROP.
  Proof.
    split.
    - intros x y.
      split.
      + intros H n m f γ d g.
        apply (H m γ d g).
      + intros H n γ m f.
        apply (H n n ı γ m f).
    - intros n.
      unfold dist.
      unfold PROP_DIST.
      split.
      + now intros a.
      + now intros a b H.
      + intros a b c H G m f γ m' g.
        etransitivity.
        * apply (H m f γ m' g).
        * apply (G m f γ m' g).
    - intros n m x y H f.
      intros p g γ q h.
      unshelve eapply (H p _ γ q h).
      simpl.
      transitivity m.
      + apply g.
      + apply Nat.lt_le_incl, f.
  Qed.

  Canonical Structure PROPO : ofe := Ofe PROP PROP_OFE.

  Program Definition PROP_compl : Compl PROPO
    := λ c, λₙ n, λₛ γ, c n n γ.
  Next Obligation.
    intros; simpl.
    intros ??.
    apply (@setoid_arr_eq _ _ ((η c n) n) a₁ a₂ H d f).
  Qed.
  Next Obligation.
    intros.
    intros ???.
    simpl.
    rewrite <-(eta_comp (c X) _ _ f a d f0).
    simpl.
    match goal with
    | |- context G [@Build_NatTrans ?T ?d ?e ?q ?r ?f] =>
        set (s := @Build_NatTrans T d e q r f)
    end.
    rewrite <-(chain_cauchy c Y X f Y ı s d f0).
    reflexivity.
  Qed.

  Program Definition PROP_COFE : Cofe PROPO
    := {| compl := PROP_compl |}.
  Next Obligation.
    intros n c.
    simpl.
    unfold PROP_compl.
    intros m f γ p g; simpl.
    rewrite (chain_cauchy c m n f m ı γ p g).
    reflexivity.
  Qed.

  Local Definition PROP_entails : PROP → PROP → Prop := λ a b, a ⊢ᵢ b.

  Lemma intuit_all_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (intuit_all A).
  Proof.
    intros ????????.
    split; intros G; intros q e r.
    - rewrite <-(H r n' f a q (f0 ∘ e)).
      apply (G q e).
    - rewrite (H r n' f a q (f0 ∘ e)).
      apply (G q e).
  Qed.

  Lemma intuit_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (intuit_exist A).
  Proof.
    intros ????????.
    split; intros [r G]; exists r.
    - rewrite <-(H r n' f a d).
      apply G.
    - rewrite (H r n' f a d).
      apply G.
  Qed.

  Lemma equiv_entails (P Q : PROP) : (PROP_EQUIV P Q)
                                       ↔ (PROP_entails P Q) ∧ (PROP_entails Q P).
  Proof.
    split.
    - intros H.
      split.
      + intros n γ m f G.
        rewrite <-(H n γ m f).
        apply G.
      + intros n γ m f G.
        rewrite (H n γ m f).
        apply G.
    - intros [H1 H2].
      intros n γ m f.
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
    intros P Q H γ n' e ??.
    apply H.
  Qed.

  Lemma conj_ne : NonExpansive2 conj.
  Proof.
    intros n P Q H X Y G γ n' e ??.
    split.
    - intros J.
      split; simpl.
      + rewrite <-(H γ n' e d f).
        apply J.
      + rewrite <-(G γ n' e d f).
        apply J.
    - intros J.
      split; simpl.
      + rewrite (H γ n' e d f).
        apply J.
      + rewrite (G γ n' e d f).
        apply J.
  Qed.

  Lemma disj_ne : NonExpansive2 disj.
  Proof.
    intros n P Q H X Y G γ n' e ??.
    split.
    - intros J.
      destruct J as [J | J].
      + left.
        rewrite <-(H γ n' e d f).
        apply J.
      + right.
        rewrite <-(G γ n' e d f).
        apply J.
    - intros J.
      destruct J as [J | J].
      + left.
        rewrite (H γ n' e d f).
        apply J.
      + right.
        rewrite (G γ n' e d f).
        apply J.
  Qed.

  Lemma impl_ne : NonExpansive2 presheaf.impl.
  Proof.
    intros n P Q H X Y G γ ????.
    split.
    - intros J.
      intros q e K.
      rewrite <-(G γ f a q).
      apply J.
      rewrite (H γ f a q).
      apply K.
    - intros J.
      intros q e K.
      rewrite (G γ f a q).
      apply J.
      rewrite <-(H γ f a q).
      apply K.
  Qed.

  Transparent nat.later.

  Lemma later_ne : NonExpansive nat.later.
  Proof.
    intros n P Q H m γ f ??.
    split.
    - intros G.
      destruct d as [| d].
      + constructor.
      + simpl.
        simpl in G.
        rewrite <-(H m γ f d).
        apply G.
    - intros G.
      destruct d as [| d].
      + constructor.
      + simpl.
        simpl in G.
        erewrite (H m γ f d).
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

  Canonical Structure TreePropI : bi.
  Proof.
    refine {|
        bi_ofe_mixin := ofe_mixin_of PROP;
        bi_cofe_aux := PROP_COFE;
        bi_bi_mixin := psh_nat_bi_mixin;
        bi_bi_persistently_mixin := psh_nat_bi_persistently_mixin;
        bi_bi_later_mixin := psh_nat_bi_later_mixin;
      |}.
  Defined.

  Global Instance PROP_pure_forall : BiPureForall PROP.
  Proof.
    intros A ϕ.
    intros ?????.
    unfold bi_pure.
    intros a.
    apply (H m ı a).
  Qed.

  Global Instance PROP_BiLöb : BiLöb TreePropI.
  Proof.
    intros P H.
    apply (later_loeb _ H).
  Qed.

  Lemma PROP_plainly_mixin : BiPlainlyMixin TreePropI id.
  Proof.
    split; try done.
    - intros; unfold id, plainly.
      intros ????????.
      apply (H n' f a d f0).
    - intros P Q. apply conj_elim_l.
  Qed.

  Global Instance PROP_plainlyC : BiPlainly TreePropI :=
    {| bi_plainly_mixin := PROP_plainly_mixin |}.

  (* Program Definition element {A : PSh NatCat} (a : GlobalSections A) *)
  (*   : 𝟙 @ tree [~>] A := λₙ x, a x. *)
  (* Next Obligation. *)
  (*   intros; simpl. *)
  (*   intros ?; simpl. *)
  (*   rewrite <-(eta_comp a _ _ f a0). *)
  (*   simpl. *)
  (*   f_equiv. *)
  (*   intros []. *)
  (* Qed. *)

  Program Definition UnOFE_elem {A : ofe} (a : A)
    : GlobalSections (UnOFE A) :=
    λₙ _, λₛ _, a.
  Next Obligation.
    intros; now simpl.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    reflexivity.
  Qed.

  Local Program Definition PROP_internal_eq {A : ofe} (a1 a2 : A) : PROP
    := ((UnOFE_elem a1) ≡ᵢ (UnOFE_elem a2))%logic.

  Lemma internal_eq_ne (A : ofe) : NonExpansive2 (@PROP_internal_eq A).
  Proof.
    intros n x x' Hx y y' Hy m f ? p g; simpl.
    clear a.
    simpl in *.
    split; intros Hz; intros q Q.
    - rewrite <-(dist_le _ _ _ _ Hx); [| lia].
      rewrite <-(dist_le _ _ _ _ Hy); [| lia].
      now apply Hz.
    - rewrite (dist_le _ _ _ _ Hx); [| lia].
      rewrite (dist_le _ _ _ _ Hy); [| lia].
      now apply Hz.
  Qed.

  Local Program Definition liftPred {A : ofe} (Ψ : A → TreePropI)
    {HΨ : NonExpansive Ψ}
    : UnOFE A [~>] (Ω @ tree) := λₙ x, λₛ y, (Ψ y x Point).
  Next Obligation.
    intros; simpl.
    intros; simpl.
    split; intros G.
    - apply (HΨ x a₁ a₂ (H x (le_n x))); [apply ı | apply G].
    - apply (HΨ x a₁ a₂ (H x (le_n x))); [apply ı | apply G].
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    rewrite <-(eta_comp (Ψ a) _ _ f Point d f0).
    simpl.
    unshelve eapply (@setoid_arr_eq _ _ (Ψ a Y) _ _ _ d f0).
    intros [].
  Qed.

  Lemma PROP_internal_eq_mixin : BiInternalEqMixin TreePropI (@PROP_internal_eq).
  Proof.
    split.
    - apply internal_eq_ne.
    - intros.
      eapply entails_trans.
      + apply true_intro.
      + apply (@eq_refl NatCat (𝟙 @ tree) (UnOFE A) (UnOFE_elem a)).
    - intros.
      eapply entails_trans.
      + apply (@eq_subst NatCat (𝟙 @ tree) (UnOFE A) (Ω @ tree)
                 (UnOFE_elem a) (UnOFE_elem b) (liftPred Ψ)).
      + apply impl_intro.
        intros ???? [H0 H1].
        simpl in *.
        rewrite (@setoid_arr_eq _ _ ((η Ψ b) n) γ Point (PointUnique γ) m f).
        erewrite proof_irrel.
        apply (H0 m (le_n _)).
        erewrite proof_irrel.
        apply (proj1 (@setoid_arr_eq _ _ ((η Ψ a) n) γ Point (PointUnique γ) m f) H1).
    - intros.
      intros ??????? x.
      simpl in *.
      apply (H n0 H0 x n0 (le_n _)).
    - intros ? ? [? ?] [? ?].
      intros ???????.
      simpl in *.
      now apply H.
    - intros.
      intros ???? G.
      unfold bi_pure.
      simpl.
      apply H.
      apply (G 0).
      apply le_0_n.
    - intros ??? ? ??? G.
      simpl in G.
      unfold bi_later.
      simpl.
      apply (@later_eq_inv (𝟙 @ tree) (UnOFE A) (UnOFE_elem x) (UnOFE_elem y)).
      simpl.
      destruct n as [| n]; simpl.
      + inversion f; subst.
        destruct (Nat.le_0_r 0) as [G1 G2].
        now rewrite (proof_irrel (G1 f) Logic.eq_refl).
      + destruct m as [| m]; simpl.
        * reflexivity.
        * intros.
          apply (G (S n0) (le_n_S _ _ H)).
          apply Arith_prebase.le_lt_n_Sm, le_n.
    - intros.
      intros ???? H.
      unfold bi_later in H.
      simpl in H.
      pose proof (@later_eq (𝟙 @ tree) (UnOFE A) (UnOFE_elem x) (UnOFE_elem y) n γ m f H) as G.
      destruct n as [| n]; simpl in *.
      + inversion f; subst.
        intros ? J; inversion J; subst.
        constructor.
        intros ? J'; inversion J'.
      + destruct m as [| m]; simpl in *.
        * intros ? J; inversion J; subst.
          constructor.
          intros ? J'; inversion J'.
        * intros p P.
          constructor.
          intros q Q.
          simpl.
          apply G.
          lia.
  Qed.

  Global Instance PROP_internal_eq_inst : BiInternalEq TreePropI :=
    {| bi_internal_eq_mixin := PROP_internal_eq_mixin |}.

  (* Global Instance PROP_prop_ext : BiPropExt TreePropI. *)
  (* Proof. *)
  (*   intros ?????? [H1 H2]. *)
  (*   unfold internal_eq, bi_internal_eq_internal_eq. *)
  (*   simpl. *)
  (*   intros r R. *)
  (*   intros ?????. *)
  (*   simpl in *. *)
  (*   split; intros H. *)
  (*   (* - pose proof (H1 d).  *) *)
  (*   (*   simpl in H0. *) *)
  (* Admitted. *)

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

    Lemma internal_eq_soundness {A : ofe} (x y : A) : (⊢@{TreePropI} x ≡ y) → x ≡ y.
    Proof.
      intros ?.
      apply equiv_dist.
      intros n.
      apply (@soundness_eq NatCat (UnOFE A) (UnOFE A)
               (UnOFE_elem x) (UnOFE_elem y) H n Point n (le_n _)).
    Qed.

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

Example test1 {A B : PROP} : ⊢ ∀ n : nat, ⌜n < 0⌝ -∗ A ∗ B -∗ A.
Proof.
  iIntros (n) "%H (a & b)".
  iApply "a".
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

Example test4 {A : ofe} : ⊢@{TreePropI} (∃ (y : A), ∀ x, x ≡ y) -∗ (∀ x, ∃ (y : A), x ≡ y).
Proof.
  iIntros "(%y & H)".
  iIntros (x).
  iExists y.
  iApply "H".
Qed.
