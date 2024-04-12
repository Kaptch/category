From category Require Import
  base
  setoid
  category
  sets
  initial
  colimit
  terminal
  functor
  classes.limits.

Section Colimits.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Class hasInitial (C : Category) :=
    {
      has_initial : Initial C;
    }.

  Class hasColimits (C : Category) :=
    {
      has_colimits : ∀ {D : Category} (J : D [⇒] C), Colimit J;
    }.

  Global Instance terminalInitialOp {C : Category} {HC : hasInitial C}
    : hasTerminal (C op).
  Proof.
    constructor.
    unshelve econstructor.
    - simpl.
      apply (@has_initial C HC).
    - simpl.
      intros X.
      apply (@initial_proj C has_initial X).
  Defined.

End Colimits.

Notation "'colim' J '@' C" := (cocone_obj (initial_obj (colimit_obj (@has_colimits C _ _ J)))) (at level 50) : cat_scope.
Notation "? '@' C" := (projT1 (@initial_proj _ (@has_initial C _) _)) (at level 50) : cat_scope.
Notation "𝟘 '@' C" := (@initial_obj _ (@has_initial C _)) (at level 50) : cat_scope.
