From category Require Import base setoid category.

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
End PB.

Arguments CS_comm {_ _ _ _ _ _ _}.
Arguments is_pb {_ _ _ _ _ _}.
Arguments is_pb_ump {_ _ _ _ _ _ _}.
