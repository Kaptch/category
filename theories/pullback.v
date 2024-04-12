From category Require Import
  base
  setoid
  category
  functor
  limit.

Section PB.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Context {C : Category}.

  Record isCommSquare {X Y Z CS_obj : C}
    (f : X [~>] Z)
    (g : Y [~>] Z)
    (CS_proj1 : CS_obj [~>] X)
    (CS_proj2 : CS_obj [~>] Y) : Prop
    :=
    {
      CS_comm :> f ∘ CS_proj1 ≡ g ∘ CS_proj2;
    }.
  Arguments CS_comm {_ _ _ _ _ _}.

  Record isPullback {X Y Z CS_obj : C}
    (f : X [~>] Z)
    (g : Y [~>] Z)
    (CS_proj1 : CS_obj [~>] X)
    (CS_proj2 : CS_obj [~>] Y) : Type
    := {
      is_pb :> isCommSquare f g CS_proj1 CS_proj2;
      is_pb_ump : ∀ {W} (h : W [~>] X) (j : W [~>] Y),
        isCommSquare f g h j → Σ! (i : W [~>] CS_obj),
        h ≡ CS_proj1 ∘ i ∧ j ≡ CS_proj2 ∘ i;
    }.

  Record Pullback {X Y Z : C}
    (f : X [~>] Z)
    (g : Y [~>] Z) : Type :=
    {
      pb_obj :> C;
      pb_proj1 : pb_obj [~>] X;
      pb_proj2 : pb_obj [~>] Y;
      pb_comm : f ∘ pb_proj1 ≡ g ∘ pb_proj2;
      pb_ump : ∀ {W} (h : W [~>] X) (j : W [~>] Y),
        f ∘ h ≡ g ∘ j → Σ! (i : W [~>] pb_obj),
        h ≡ pb_proj1 ∘ i ∧ j ≡ pb_proj2 ∘ i;
    }.

  Lemma PullbackIsPullback {X Y Z : C}
    {f : X [~>] Z}
    {g : Y [~>] Z} (P : Pullback f g)
    : isPullback f g (pb_proj1 _ _ P) (pb_proj2 _ _ P).
  Proof.
    constructor.
    - constructor.
      apply pb_comm.
    - intros W h j K.
      apply (@pb_ump _ _ _ _ _ P W h j K).
  Qed.

  Program Definition isPullbackPullback {X Y Z W : C}
    {f : X [~>] Z}
    {g : Y [~>] Z}
    {h : W [~>] X}
    {j : W [~>] Y}
    (H : isPullback f g h j) : Pullback f g :=
    {|
      pb_obj := W;
      pb_proj1 := h;
      pb_proj2 := j;
    |}.
  Next Obligation.
    intros X Y Z W f g h j H.
    apply H.
  Qed.
  Next Obligation.
    intros X Y Z W f g h j H.
    intros Q p l k.
    apply (@is_pb_ump _ _ _ _ _ _ _ _ H Q p l).
    constructor.
    apply k.
  Qed.

  Lemma CommSquareRotate {X Y Z W : C}
    {f : X [~>] Z}
    {g : Y [~>] Z}
    {h : W [~>] X}
    {j : W [~>] Y}
    (H : isCommSquare f g h j)
    : isCommSquare g f j h.
  Proof.
    constructor.
    symmetry.
    apply H.
  Qed.

  Lemma PullbackRotate {X Y Z W : C}
    {f : X [~>] Z}
    {g : Y [~>] Z}
    {h : W [~>] X}
    {j : W [~>] Y}
    (H : isPullback f g h j)
    : isPullback g f j h.
  Proof.
    constructor.
    - apply (CommSquareRotate H).
    - intros Q q w K.
      exists (projT1 ((@is_pb_ump _ _ _ _ _ _ _ _ H Q w q) (CommSquareRotate K))).
      split.
      + split.
        * apply (proj2 (fst (projT2 (is_pb_ump f g h j H w q (CommSquareRotate K))))).
        * apply (proj1 (fst (projT2 (is_pb_ump f g h j H w q (CommSquareRotate K))))).
      + intros r R.
        apply (snd (projT2 (is_pb_ump f g h j H w q (CommSquareRotate K))) r).
        split; [apply (proj2 R) | apply (proj1 R)].
  Qed.

  Lemma PullbackCompose {X Y Z W A B : C}
    {f : X [~>] Z}
    {g : Y [~>] Z}
    {h : W [~>] X}
    {j : W [~>] Y}
    {k : A [~>] W}
    {l : B [~>] Y}
    {u : A [~>] B}
    (H : isPullback f g h j)
    (G : isPullback j l k u)
    : isPullback f (g ∘ l) (h ∘ k) u.
  Proof.
    constructor.
    - constructor.
      rewrite <-arrow_comp_assoc.
      rewrite (CS_comm _ _ (is_pb _ _ _ _ H)).
      rewrite arrow_comp_assoc.
      rewrite (CS_comm _ _ (is_pb _ _ _ _ G)).
      rewrite arrow_comp_assoc.
      reflexivity.
    - intros Q q w J.
      assert (K : isCommSquare f g q (l ∘ w)).
      {
        constructor.
        rewrite (CS_comm _ _ J).
        rewrite arrow_comp_assoc.
        reflexivity.
      }
      assert (L : isCommSquare j l (projT1 (@is_pb_ump _ _ _ _ _ _ _ _ H Q q (l ∘ w) K)) w).
      {
        constructor.
        rewrite <-(proj2 (fst (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ H Q q (l ∘ w) K)))).
        reflexivity.
      }
      exists (projT1 (@is_pb_ump _ _ _ _ _ _ _ _ G Q (projT1 (@is_pb_ump _ _ _ _ _ _ _ _ H Q q (l ∘ w) K)) w L)).
      split.
      + split.
        * rewrite arrow_comp_assoc.
          rewrite <-(proj1 (fst (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ G Q (projT1 (@is_pb_ump _ _ _ _ _ _ _ _ H Q q (l ∘ w) K)) w L)))).
          apply (proj1 (fst (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ H Q q (l ∘ w) K)))).
        * rewrite <-(proj2 (fst (projT2 (is_pb_ump j l k u G (projT1 (is_pb_ump f g h j H q (l ∘ w) K)) w L)))).
          reflexivity.
      + intros e E.
        apply (snd (projT2 (is_pb_ump j l k u G (projT1 (is_pb_ump f g h j H q (l ∘ w) K)) w L)) e).
        split.
        * apply (snd (projT2 (is_pb_ump f g h j H q (l ∘ w) K)) (k ∘ e)).
          rewrite <-arrow_comp_assoc.
          split; [apply (proj1 E) |].
          rewrite (proj2 E).
          rewrite <-2 arrow_comp_assoc.
          do 2 f_equiv.
          symmetry.
          apply (CS_comm _ _ (is_pb _ _ _ _ G)).
        * apply (proj2 E).
  Qed.

  Lemma PullbackFactor {X Y Z W A B : C}
    {f : X [~>] Z}
    {g : Y [~>] Z}
    {h : W [~>] X}
    {j : W [~>] Y}
    {k : A [~>] W}
    {l : B [~>] Y}
    {u : A [~>] B}
    (H : isPullback f g h j)
    (G : isPullback f (g ∘ l) (h ∘ k) u)
    (J : isCommSquare j l k u)
    : isPullback j l k u.
  Proof.
    constructor.
    - apply J.
    - intros P p o L.
      assert (K : isCommSquare f (g ∘ l) (h ∘ p) o).
      {
        constructor.
        rewrite arrow_comp_assoc. 
        rewrite <-(CS_comm _ _ L).
        rewrite <-2 arrow_comp_assoc.
        do 2 f_equiv.
        apply (is_pb _ _ _ _ H).
      }
      set (q := (@is_pb_ump _ _ _ _ _ _ _ _ G P (h ∘ p) o K)).
      pose proof (fst (projT2 q)) as [H1 H2].
      exists (projT1 q).
      split.
      + split; [| apply H2].
        assert (K' : isCommSquare f g (h ∘ p) (l ∘ o)).
        {
          constructor.
          rewrite <-2 arrow_comp_assoc.
          rewrite (CS_comm _ _ (is_pb _ _ _ _ H)).
          rewrite ->2 arrow_comp_assoc.
          f_equiv.
          apply L.
        }
        rewrite <-(snd (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ H P (h ∘ p) (l ∘ o) K')) p).
        * rewrite <-(snd (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ H P (h ∘ p) (l ∘ o) K')) (k ∘ projT1 q)); [reflexivity |].
          split.
          -- now rewrite ->H1, arrow_comp_assoc.
          -- rewrite ->H2.
             now rewrite <-2 arrow_comp_assoc, (CS_comm _ _ J).
        * split; [now rewrite H1 arrow_comp_assoc |].
          now rewrite <-(CS_comm _ _ L).
      + intros x' X'.
        apply (snd (projT2 q) x').
        split; [| apply (proj2 X')].
        rewrite arrow_comp_assoc.
        rewrite <-(proj1 X').
        reflexivity.
  Qed.

  (* Lemma PullbackUnique {X Y Z : C} *)
  (*   {f : X [~>] Z} *)
  (*   {g : Y [~>] Z} *)
  (*   (a b : Pullback f g) : *)
  (*   Isomorphism a b. *)

End PB.

Section Limit.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.

  Inductive PB_Diagram_Obj : Type :=
  | PB_Diagram_Obj_X : PB_Diagram_Obj
  | PB_Diagram_Obj_Y : PB_Diagram_Obj
  | PB_Diagram_Obj_Z : PB_Diagram_Obj.

  Definition PB_Diagram_Arr (X Y : PB_Diagram_Obj) : Type :=
    match (X, Y) with
    | (PB_Diagram_Obj_X, PB_Diagram_Obj_X) => unit
    | (PB_Diagram_Obj_Y, PB_Diagram_Obj_Y) => unit
    | (PB_Diagram_Obj_Z, PB_Diagram_Obj_Z) => unit
    | (PB_Diagram_Obj_X, PB_Diagram_Obj_Z) => unit
    | (PB_Diagram_Obj_Y, PB_Diagram_Obj_Z) => unit
    | _ => Empty_set
    end.

  Program Definition PB_Diagram_Arr_Setoid (X Y : PB_Diagram_Obj)
    : Setoid := [ PB_Diagram_Arr X Y ].

  Definition PB_Diagram_id (X : PB_Diagram_Obj) : PB_Diagram_Arr_Setoid X X :=
    match X with
    | PB_Diagram_Obj_X => tt
    | PB_Diagram_Obj_Y => tt
    | PB_Diagram_Obj_Z => tt
    end.

  Lemma PB_Diagram_Arr_Z_unit (X : PB_Diagram_Obj)
    : PB_Diagram_Arr X PB_Diagram_Obj_Z = unit.
  Proof.
    destruct X; now unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr.
  Qed.

  Lemma PB_Diagram_Arr_id_unit (X : PB_Diagram_Obj)
    : PB_Diagram_Arr X X = unit.
  Proof.
    destruct X; now unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr.
  Qed.

  Definition PB_Diagram_comp {X Y Z : PB_Diagram_Obj}
    (g : PB_Diagram_Arr_Setoid Y Z)
    (f : PB_Diagram_Arr_Setoid X Y)
    : PB_Diagram_Arr_Setoid X Z.
  Proof.
    destruct X, Y, Z; unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr in *; simpl in *;
      try constructor; try now exfalso.
  Defined.

  Program Definition PB_Diagram_comp_setoid {X Y Z : PB_Diagram_Obj}
    : SetoidArr (PB_Diagram_Arr_Setoid Y Z)
        (SetoidArr (PB_Diagram_Arr_Setoid X Y) (PB_Diagram_Arr_Setoid X Z)) :=
    λₛ g, λₛ f, PB_Diagram_comp g f.
  Next Obligation.
    intros; simpl.
    destruct X, Y, Z; unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr in *; simpl in *;
      try constructor; try now exfalso.
  Qed.
  Next Obligation.
    intros; simpl.
    intros a.
    destruct X, Y, Z; unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr in *; simpl in *;
      try constructor; try now exfalso.
  Qed.

  Program Definition PB_Diagram_Cat : Category :=
    {|
      Obj := PB_Diagram_Obj;
      Arr := PB_Diagram_Arr_Setoid;
      arrow_id A := PB_Diagram_id A;
      arrow_comp A B C := PB_Diagram_comp_setoid;
    |}.
  Next Obligation.
    intros; simpl.
    destruct A, B; unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr in *;
      destruct f; simpl in *; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    destruct A, B; unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr in *;
      destruct f; simpl in *; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    destruct A, B, C, D; unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr in *;
      destruct f, g, h; simpl in *; reflexivity.
  Qed.

  Context {C : Category}.

  Program Definition PB_functor {X Y Z : C} (f : X [~>] Z) (g : Y [~>] Z)
    (H : Pullback f g) : (PB_Diagram_Cat [⇒] C)%functor.
  Proof.
    unshelve econstructor.
    - intros T.
      destruct T.
      + apply X.
      + apply Y.
      + apply Z.
    - intros; simpl.
      unshelve econstructor.
      + intros j.
        destruct A, B, j; unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr in *;
          simpl in *.
        * apply arrow_id.
        * apply f.
        * apply arrow_id.
        * apply g.
        * apply arrow_id.
      + intros; simpl.
        destruct A, B, a₁, a₂; unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr in *;
          simpl in *; reflexivity.
    - intros; simpl.
      destruct A; simpl; reflexivity.
    - intros; simpl.
      destruct A, B, C0, f0, g0; unfold PB_Diagram_Arr_Setoid, PB_Diagram_Arr in *;
        simpl in *; rewrite ?arrow_comp_id_l ?arrow_comp_id_r; reflexivity.
  Defined.

  (* Program Definition Limit_PB (J : (PB_Diagram_Cat [⇒] C)%functor) (l : Limit J) *)
  (*   : Pullback (@fmap PB_Diagram_Cat C J PB_Diagram_Obj_X PB_Diagram_Obj_Z tt) *)
  (*       (@fmap PB_Diagram_Cat C J PB_Diagram_Obj_Y PB_Diagram_Obj_Z tt) *)
  (*   := {| *)
  (*     pb_obj := terminal.terminal_obj (limit_obj l); *)
  (*     pb_proj1 := cone_nat (terminal.terminal_obj (limit_obj l)) PB_Diagram_Obj_X; *)
  (*     pb_proj2 := cone_nat (terminal.terminal_obj (limit_obj l)) PB_Diagram_Obj_Y; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   intros; simpl. *)
  (*   rewrite <-(eta_comp (cone_nat (terminal.terminal_obj (limit_obj l))) *)
  (*               PB_Diagram_Obj_X PB_Diagram_Obj_Z tt). *)
  (*   rewrite <-(eta_comp (cone_nat (terminal.terminal_obj (limit_obj l))) *)
  (*               PB_Diagram_Obj_Y PB_Diagram_Obj_Z tt). *)
  (*   reflexivity. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   intros; simpl. *)
  (* Admitted. *)

  (* Program Definition PB_Cone {X Y Z : C} (f : X [~>] Z) (g : Y [~>] Z) *)
  (*   (H : Pullback f g) : Cone (PB_functor f g H) := *)
  (*   {| *)
  (*     cone_obj := H; *)
  (*     cone_nat := (λₙ x, _)%functor; *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   intros; simpl. *)
  (*   destruct x. *)
  (*   - apply pb_proj1. *)
  (*   - apply pb_proj2. *)
  (*   - admit. *)
  (* Admitted. *)
  (* Next Obligation. *)
  (* Admitted. *)

  (* Lemma PB_Limit {X Y Z : C} (f : X [~>] Z) (g : Y [~>] Z) *)
  (*   (H : Pullback f g) : Limit (PB_functor f g H). *)
  (* Admitted. *)

End Limit.

Arguments CS_comm {_ _ _ _ _ _ _}.
Arguments is_pb {_ _ _ _ _ _}.
Arguments is_pb_ump {_ _ _ _ _ _ _}.
