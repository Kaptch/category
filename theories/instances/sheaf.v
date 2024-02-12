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

Require Import Coq.Logic.StrictProp.

From stdpp Require Import
  base.

From category Require Import
  (* ordinals.set_ordinals *)
  (* ordinals.set_model *)
  (*(* ordinals.set_sets *)*)
  (* ordinals.arithmetic *)
  (* ordinals.set_functions *)
  ordinals.stepindex.

Section Ord.
  Context (SI : indexT).

  (* Inductive seq {A : SProp} (a : A) : A → Prop := *)
  (* | srefl : seq a a. *)

  (* Global Instance seq_Equiv {A : SProp} : @Equivalence A seq. *)
  (* Proof. *)
  (*   split. *)
  (*   - intros ?; constructor. *)
  (*   - intros ???; now symmetry. *)
  (*   - intros ???? []. *)
  (*     assumption. *)
  (* Qed. *)

  (* Set Universe Polymorphism. *)
  (* Set Polymorphic Inductive Cumulativity. *)

  Program Definition OrdCatArrSetoid (A B : SI) : Setoid :=
    {|
      setoid_carrier := Squash (A ⪯ B);
      setoid_eq (X Y : Squash (A ⪯ B)) := Squash (X = Y);
    |}.
  Next Obligation.
    intros; split.
    - intros ?; now constructor.
    - intros ???.
      inversion H as [H'].
      destruct H'.
      now constructor.
    - intros ?????.
      inversion H as [H'].
      now destruct H'.
  Qed.
  (* Next Obligation. *)
    (* intros; split. *)
    (* - intros ?; constructor. *)
    (* - intros ???. now symmetry. *)
    (* - intros ?????. etransitivity; eassumption. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros; split. *)
  (*   - intros ?; constructor. *)
  (*   - intros ???; constructor. *)
  (*   - intros ?????; constructor. *)
  (* Qed. *)

  Program Definition OrdCat : Category :=
    {|
      Obj := SI;
      Arr A B := OrdCatArrSetoid A B;
      arrow_id A := rc_refl _ A A eq_refl;
      arrow_comp A B C := (λₛ f, λₛ g, transitivity g f)%setoid;
    |}.
  Next Obligation.
    intros; simpl in *.
    (* now rewrite H. *)
    constructor.
  Qed.
  Next Obligation.
    intros; simpl in *.
    (* now rewrite H. *)
    constructor.
  Qed.
  Next Obligation.
    intros; simpl in *.
    destruct f; subst; reflexivity.
    (* constructor. *)
  Qed.
  Next Obligation.
    intros; simpl in *.
    destruct f; subst; reflexivity.
    (* constructor. *)
  Qed.
  Next Obligation.
    intros; simpl in *.
    destruct f, g, h; subst; simpl; try reflexivity.
  Qed.

End Ord.

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
    := (@index_rec SI (const Setoid) ([ unit ]) (λ i' _, X i') (λ α _, X (limit_index α)) i).

  Program Definition LaterRestrZero (X : tree) : ∀ α : OrdCat SI, (α [~>] zero) [→] LaterObj X zero [→] LaterObj X α
  := λ α, λₛ H, _.
  Next Obligation.
    intros X α H.
    assert (α = zero) as ->; [| refine (λₛ x, x); intros; assumption ].
    apply index_zero_is_unique.
    intros β contra.
    apply (index_lt_zero_is_normal β (index_lt_le_trans _ _ _ contra H)).
  Defined.
  Next Obligation.
    intros; simpl.
    intros a.
    unfold LaterObj in a.
    destruct H.
    simpl in *.
    assert (α = zero) as ->.
    - apply index_zero_is_unique.
      intros β contra.
      apply (index_lt_zero_is_normal β (index_lt_le_trans _ _ _ contra a₁)).
    - reflexivity.
  Qed.


  Program Definition Later (X : tree) : tree :=
    {|
      FO A := LaterObj X A;
      functor.fmap A B := _;
    |}.
  Next Obligation.
    intros X.
    apply (@index_rec SI (λ (β : OrdCat SI), ∀ (α : OrdCat SI), (α [~>] β) [→] LaterObj X β [→] LaterObj X α) (LaterRestrZero X)).
    intros α H β G J.

  Program Definition LaterRestrSucc (X : tree) :
    ∀ α : SI,
    (∀ β : SI, β ⪯ α → LaterObj X α [→] LaterObj X β)
    → ∀ β : SI, β ⪯ succ α → LaterObj X (succ α) [→] LaterObj X β.
  Proof.
    intros α H β G.
    destruct (index_le_lt_eq_dec β (succ α) G) as [K | K].
    - unfold LaterObj at 1.
      erewrite index_rec_succ; [| apply _].
      pose proof (@functor.fmap _ _ (LaterObj X)).

      assert (K' : β ⪯ α).
      { apply index_succ_iff_proj_r2l, K. }

      refine (λₛ J, H _ K' (LaterLift _ _ J)).
      intros; simpl.
      apply H; [apply K' |].
      now apply LaterLift.
    - rewrite K; apply J.
  Defined.

  Program Definition LaterRestr (X : tree) : ∀ β, ∀ α, α ⪯ β → LaterObj X β → LaterObj X α.
  Proof.
    apply (@index_rec SI (λ β, ∀ α, α ⪯ β → LaterObj X β → LaterObj X α) (LaterRestrZero X) (LaterRestrSucc X)).
    intros α H β G J.
  Admitted.

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

      admit.
  Admitted.

End ToposOfTrees.
