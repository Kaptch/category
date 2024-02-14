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
  instances.presheaf.

From stdpp Require Import
  base.

From category Require Import
  ordinals.set_ordinals
  ordinals.set_model
  (* ordinals.set_sets *)
  ordinals.arithmetic
  ordinals.set_functions
  ordinals.stepindex.

Require Import classes.limits.
Require Import classes.exp.
Require Import classes.subobject.
Require Import internal_lang.presheaf.

Section Ord.
  Context (SI : indexT).

  Program Definition OrdCatArrSetoid (A B : SI) : Setoid :=
    {|
      setoid_carrier := A ⪯ B;
      setoid_eq (X Y : A ⪯ B) := True;
    |}.
  Next Obligation.
    intros; split.
    - intros ?; constructor.
    - intros ???; constructor.
    - intros ?????; constructor.
  Qed.

  Program Definition OrdCat : Category :=
    {|
      Obj := SI;
      Arr A B := OrdCatArrSetoid A B;
      arrow_id A := rc_refl _ A;
      arrow_comp A B C := (λₛ f, λₛ g, transitivity g f)%setoid;
    |}.
  Next Obligation.
    intros; simpl in *.
    constructor.
  Qed.
  Next Obligation.
    intros; simpl in *.
    constructor.
  Qed.
  Next Obligation.
    intros; simpl in *.
    constructor.
  Qed.
  Next Obligation.
    intros; simpl in *.
    constructor.
  Qed.
  Next Obligation.
    intros; simpl in *.
    constructor.
  Qed.

End Ord.

Section Transfinite.


End Transfinite.

Section ToposOfTrees.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context (SI : indexT).

  Definition tree := PSh ((OrdCat SI)).

  Global Program Instance Tree_Index_Rec_Lim_Ext (X : tree)
    : index_rec_lim_ext (λ (α : limit_idx) (_ : ∀ β : SI, β ≺ α → Setoid), X (limit_index α))
    := {|
      index_rec_lim_ext_proofs := _;
      index_rec_lim_ext_function := _;
    |}.
  Next Obligation.
    intros; reflexivity.
  Defined.
  Next Obligation.
    intros; reflexivity.
  Defined.

  Program Definition LaterObj (X : tree) (i : SI) : Setoid
    := (@index_rec SI (const Setoid)
          ([ unit ])
          (λ i' _, X i')
          (λ α _, X (limit_index α)) i).

  Program Definition Next' (X : tree) : ∀ (i : SI), (X i) [→] LaterObj X i.
  Proof.
    apply (@index_rec SI (λ (i : SI), (X i) [→] LaterObj X i)).
    - rewrite /LaterObj index_rec_zero.
      refine (λₛ _, (tt : [ unit ])).
      intros; reflexivity.
    - intros α H.
      rewrite /LaterObj index_rec_succ.
      apply (functor.fmap X (rc_subrel _ _ _ (index_succ_greater α))).
    - intros α H.
      rewrite /LaterObj index_rec_lim.
      apply idS.
  Defined.

  Program Definition LaterRestrZero (X : tree) : ∀ α : OrdCat SI, (α [~>] zero) [→] LaterObj X zero [→] LaterObj X α
  := λ α, λₛ H, _.
  Next Obligation.
    intros X α H.
    assert (α = zero) as ->; [| refine (λₛ x, x); intros; assumption ].
    simpl in H.
    apply index_zero_is_unique.
    intros β contra.
    apply (index_lt_zero_is_normal β (index_lt_le_trans _ _ _ contra H)).
  Defined.
  Next Obligation.
    intros; simpl.
    now rewrite (proof_irrel a₁ a₂).
  Qed.

  Program Definition LaterRestrSucc (X : tree) :
    ∀ α : OrdCat SI,
    (∀ β : OrdCat SI, β ⪯ α → LaterObj X α [→] LaterObj X β)
    → ∀ β : OrdCat SI, (β [~>] succ α) [→] LaterObj X (succ α) [→] LaterObj X β
  := λ α H β, λₛ H, _.
  Next Obligation.
    intros X α H β G.
    unfold LaterObj at 1.
    erewrite index_rec_succ; [| apply _].
    simpl in *.
    destruct (index_le_lt_eq_dec β (succ α) G) as [K | K].
    - rewrite <-index_succ_iff in K.
      pose proof (H β K).
      unshelve econstructor.
      + intros X1.
        apply X0.
        now apply Next'.
      + intros; simpl.
        now do 2 f_equiv.
    - rewrite K.
      unfold LaterObj at 1.
      erewrite index_rec_succ; [| apply _].
      apply idS.
  Defined.
  Next Obligation.
    intros; simpl.
    intros a.
    unfold LaterRestrSucc_obligation_1.
    simpl in *.
    case_match.
    - case_match.
      + unshelve erewrite (proof_irrel i i0).
        * apply index_lt_irrel.
        * reflexivity.
      + subst.
        exfalso.
        rewrite (proof_irrel a₁ a₂) in H1.
        rewrite H2 in H1.
        done.
    - case_match.
      + subst.
        exfalso.
        rewrite (proof_irrel a₁ a₂) in H1.
        rewrite H2 in H1.
        done.
      + subst.
        unshelve erewrite (proof_irrel e0 eq_refl).
        * eapply eq_pi.
          apply index_eq_dec.
        * unfold eq_rect_r.
          simpl.
          reflexivity.
  Qed.

  Program Definition LaterRestrLim (X : tree) :
    ∀ α : limit_idx,
    (∀ β : OrdCat SI, β ≺ α → ∀ α0 : OrdCat SI, (α0 [~>] β) [→] LaterObj X β [→] LaterObj X α0)
    → ∀ α0 : OrdCat SI, (α0 [~>] limit_index α) [→] LaterObj X α [→] LaterObj X α0
  := λ α H β, λₛ H', _.
  Next Obligation.
    intros X α H β G.
    unfold LaterObj at 1.
    erewrite index_rec_lim; [| apply _].
    simpl in *.
    destruct (index_le_lt_eq_dec β α G) as [K | K].
    - unshelve econstructor.
      + intros X'.
        eapply H.
        * apply K.
        * simpl.
          constructor.
        * apply Next'.
          apply (@functor.fmap _ _ X (limit_index α) β G X').
      + intros; simpl.
        now do 3 f_equiv.
    - subst.
      apply Next'.
  Defined.
  Next Obligation.
    intros; simpl.
    intros a.
    unfold LaterRestrLim_obligation_1.
    simpl in *.
    case_match.
    - case_match.
      + unshelve erewrite (proof_irrel i i0).
        * apply index_lt_irrel.
        * match goal with
          | |- context G [eq_rect ?a] => idtac a
          end.
          admit.
      + simpl.
        exfalso.
        rewrite (proof_irrel a₁ a₂) in H1.
        rewrite H2 in H1.
        done.
    - case_match.
      + subst.
        exfalso.
        rewrite (proof_irrel a₁ a₂) in H1.
        rewrite H2 in H1.
        done.
      + subst.
        unshelve erewrite (proof_irrel e0 eq_refl).
        * eapply eq_pi.
          apply index_eq_dec.
        * unfold eq_rect_r.
          simpl.
          reflexivity.
  Admitted.

  Program Definition Later (X : tree) : tree :=
    {|
      FO A := LaterObj X A;
      functor.fmap A B := _;
    |}.
  Next Obligation.
    intros.
    apply (@index_rec SI
             (λ (β : OrdCat SI), ∀ (α : OrdCat SI), (α [~>] β) [→] LaterObj X β [→] LaterObj X α) (LaterRestrZero X) (LaterRestrSucc X) (LaterRestrLim X)).
  Defined.
  Next Obligation.
    intros X.
    intros; simpl in *.
    apply (@index_rec SI (λ A : OrdCat SI op, (λ A0 B : OrdCat SI op, Later_obligation_1 X A0 B) A A ı ≡ ı)).
    - simpl.
      unfold LaterObj at 1.
      simpl.
      intros a.
      unfold Later_obligation_1.
      simpl.
      erewrite index_rec_zero; [| admit].
      simpl.
      unfold LaterRestrZero_obligation_1.
      simpl.
      match goal with
      | |- context G [eq_rect_r _ _ ?a] => unshelve erewrite (proof_irrel a eq_refl)
      end.
      + eapply eq_pi.
        apply index_eq_dec.
      + simpl.
        done.
    - simpl.
      unfold LaterObj at 1.
      simpl.
      intros ? ? a.
      unfold Later_obligation_1.
      simpl.
      erewrite index_rec_succ; [| admit].
      simpl.
      unfold LaterRestrSucc_obligation_1.
      simpl.
      assert (index_le_lt_eq_dec (succ α) (succ α) (rc_refl (≺) (succ α)) = right eq_refl) as ->.
      {
        destruct (index_le_lt_eq_dec (succ α) (succ α) (rc_refl (≺) (succ α))).
        - exfalso.
          by eapply index_lt_irrefl.
        - unshelve erewrite (proof_irrel e eq_refl).
          + eapply eq_pi.
            apply index_eq_dec.
          + reflexivity.
      }
      simpl.
      unfold eq_rect_r.
      simpl.
      unfold eq_rect.
      admit.
    - intros ? ?.
      unfold Later_obligation_1.
      unfold LaterRestrSucc_obligation_1.
      erewrite index_rec_lim; [| admit].
      simpl.
      intros ?.
      unfold LaterRestrLim_obligation_1.
      assert (index_le_lt_eq_dec (α) (α) (rc_refl (≺) (α)) = right (eq_sym eq_refl)) as ->.
      {
        destruct (index_le_lt_eq_dec (α) (α) (rc_refl (≺) (α))).
        - exfalso.
          by eapply index_lt_irrefl.
        - unshelve erewrite (proof_irrel e eq_refl).
          + eapply eq_pi.
            apply index_eq_dec.
          + reflexivity.
      }
      simpl.
      unfold eq_rect_r.
      simpl.
      unfold Next'.

End ToposOfTrees.
