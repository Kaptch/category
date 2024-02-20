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
  base
  numbers.

Require Import classes.limits.
Require Import classes.exp.
Require Import classes.subobject.
Require Import internal_lang.presheaf.

Section Nat.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.
  Local Open Scope logic_scope.

  Program Definition NatCatArrSetoid (A B : nat) : Setoid :=
    {|
      setoid_carrier := (A <= B);
      setoid_eq (X Y : (A <= B)) := X = Y;
    |}.

  Program Definition NatCat : Category :=
    {|
      Obj := nat;
      Arr A B := NatCatArrSetoid A B;
      arrow_id A := (le_n A);
      arrow_comp A B C := (λₛ f, λₛ g, (Nat.le_trans _ _ _ g f))%setoid;
    |}.
  Next Obligation.
    intros; simpl.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply proof_irrel.
  Qed.

  Definition tree := PSh NatCat.
  Notation "🌲" := tree.

  Ltac elim_eq_irrel := match goal with
                        | |- context G [eq_rect_r _ _ ?a] =>
                            try rewrite (proof_irrel a eq_refl)
                        end.

  Lemma fmap_irrel {X : tree} {n m : NatCat} (f g : n [~>] m)
    (x : X m) : functor.fmap X f x ≡ functor.fmap X g x.
  Proof.
    simpl in *.
    now rewrite (proof_irrel f g).
  Qed.

  Program Definition LaterSetoid (X : tree) (i : nat) : Setoid
    := match i with
       | 0 => ([ unit ])%setoid
       | S i' => X i'
       end.

  Definition LaterFmap (X : tree) (n m : nat) (H : n <= m) :
    LaterSetoid X m [→] LaterSetoid X n.
  Proof.
    induction m.
    - apply Nat.le_0_r in H.
      rewrite H.
      apply idS.
    - induction n.
      + simpl.
        unshelve econstructor.
        * intros; constructor.
        * intros; reflexivity.
      + apply le_S_n in H.
        apply (functor.fmap X H).
  Defined.

  Program Definition LaterObj (X : tree) : tree :=
    {|
      FO A := LaterSetoid X A;
      functor.fmap A B := λₛ f, LaterFmap X B A f;
    |}.
  Next Obligation.
    intros; simpl.
    intros a.
    do 2 f_equiv.
    apply proof_irrel.
  Qed.
  Next Obligation.
    intros; simpl.
    intros.
    destruct A.
    - simpl.
      elim_eq_irrel.
      reflexivity.
    - simpl.
      rewrite (fmap_irrel (le_S_n A A (le_n (S A))) ı a).
      apply (@fmap_id _ _ X A a).
  Qed.
  Next Obligation.
    intros; simpl.
    destruct A, B, C; simpl; intros D;
      repeat elim_eq_irrel.
    - reflexivity.
    - exfalso.
      simpl in *.
      lia.
    - exfalso.
      simpl in *.
      lia.
    - exfalso.
      simpl in *.
      lia.
    - reflexivity.
    - exfalso.
      simpl in *.
      lia.
    - reflexivity.
    - pose proof (@fmap_comp _ _ X _ _ _ (le_S_n _ _ f) (le_S_n _ _ g) D) as H.
      rewrite <-H.
      simpl.
      do 2 f_equiv.
      apply proof_irrel.
  Qed.

  Program Definition Later : tree [⇒] tree :=
    {|
      FO A := LaterObj A;
      functor.fmap A B := λₛ f, λₙ x,
        nat_rect (λ x' : nat, LaterObj A x' [~>] LaterObj B x') idS
          (λ (x' : nat) _, (η f) x') x;
    |}.
  Next Obligation.
    intros; simpl.
    intros a.
    destruct X, Y; simpl.
    - destruct (Nat.le_0_r 0) as [G1 G2].
      assert (G1 f0 = Logic.eq_refl) as ->.
      { apply proof_irrel. }
      simpl.
      reflexivity.
    - exfalso.
      simpl in *.
      lia.
    - reflexivity.
    - rewrite <-(eta_comp f _ _ (le_S_n Y X f0) a).
      reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ??.
    destruct X as [| X].
    - reflexivity.
    - simpl.
      apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros [| X] ?; simpl; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros [| X] ?; simpl; reflexivity.
  Qed.

  Notation "'▶'" := (Later) (at level 0) : logic_scope.

  Program Definition NextFun (X : tree) : ∀ (i : nat), (X i) [→] ▶ X i
  := λ i, λₛ T, (functor.fmap (▶ X) (le_S i i (le_n i)) T).
  Next Obligation.
    intros; simpl.
    now f_equiv.
  Qed.

  Program Definition next {X : tree} : X [↣] (▶ X)
    := λₙ n, NextFun X n.
  Next Obligation.
    - intros; simpl.
      intros a.
      destruct X0, Y.
      + simpl.
        elim_eq_irrel.
        reflexivity.
      + exfalso.
        simpl in *.
        lia.
      + reflexivity.
      + pose proof (@fmap_comp _ _ X _ _ _ (le_S_n Y (S Y) (le_S (S Y) (S Y) (le_n (S Y)))) f) as H.
        simpl in H.
        rewrite <-H.
        pose proof (@fmap_comp _ _ X _ _ _ (le_S_n Y X0 f) (le_S_n X0 (S X0) (le_S (S X0) (S X0) (le_n (S X0))))) as H'.
        simpl in H'.
        rewrite <-H'.
        do 2 f_equiv.
        apply proof_irrel.
  Qed.

  Definition Contractive (X Y : tree) (ϕ : X [↣] Y) :=
    sigT (λ g : ▶ X [↣] Y, ϕ ≡ g ∘ next).

  Program Fixpoint FixPointwise (X : tree)
    (ϕ : X [↣] X)
    (g : ▶ X [↣] X)
    (H : ϕ ≡ g ∘ next)
    (i : nat) : (𝟙 @ tree)%cat i [~>] X i
    := match i with
       | 0 => λₛ _, (g 0 tt)
       | S i' => λₛ x, (g (S i')) (FixPointwise X ϕ g H i' Point)
       end.
  Next Obligation.
    intros; simpl; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Defined.

  Program Definition Fix (X : tree) (ϕ : X [↣] X) (H : Contractive X X ϕ)
    : (𝟙 @ tree)%cat [↣] X :=
    match H with
    | existT g H => λₙ o, λₛ n, (FixPointwise X ϕ g H o n)
    end.
  Next Obligation.
    intros; simpl.
    now rewrite H1.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    revert Y f.
    induction X0; intros Y f; destruct Y; simpl.
    * rewrite <-(eta_comp g _ _ f ()).
      simpl.
      f_equiv.
      constructor.
    * exfalso.
      simpl in f.
      lia.
    * set (ggg := setoid_arr _ _) at 5.
      rewrite <-(eta_comp g _ _ f ggg).
      simpl.
      reflexivity.
    * set (ggg := setoid_arr _ _) at 6.
      rewrite <-(eta_comp g _ _ f ggg).
      simpl; f_equiv.
      subst ggg.
      rewrite <-(IHX0 _ Y (le_S_n Y X0 f)).
      f_equiv.
      intros [].
  Qed.

  Lemma FixCorrect (X : tree) (ϕ : X [↣] X) (H : Contractive X X ϕ)
    : ϕ ∘ (Fix X ϕ H) ≡ (Fix X ϕ H).
  Proof.
    destruct H as [g H].
    intros x.
    induction x.
    + simpl.
      intros _.
      simpl.
      rewrite (H 0 _).
      reflexivity.
    + simpl; intros _.
      rewrite (H (S x) ((η g) (S x) (FixPointwise X ϕ g H x Point))).
      simpl.
      f_equiv.
      rewrite <-(eta_comp g _ _
                  (le_S_n x (S x) (le_S (S x) (S x) (le_n (S x))))
                  (FixPointwise X ϕ g H x Point)).
      assert (functor.fmap (▶ X)
                (le_S_n x (S x) (le_S (S x) (S x) (le_n (S x))))
                ≡ next x) as ->.
      {
        simpl.
        intros ?.
        simpl.
        do 2 f_equiv.
        apply proof_irrel.
      }
      rewrite <-(H x (FixPointwise X ϕ g H x Point)).
      apply IHx.
  Qed.

  Lemma FixUnique (X : tree) (ϕ : X [↣] X) (H : Contractive X X ϕ)
    : unique_setoid (λ t : (𝟙 @ tree)%cat [↣] X, ϕ ∘ t ≡ t) (Fix X ϕ H).
  Proof.
    split.
    - apply FixCorrect.
    - pose proof (FixCorrect X ϕ H) as C.
      destruct H as [g H].
      intros x' G.
      intros i.
      intros ?.
      rewrite (@PointUnique NatCat i a); clear a.
      induction i.
      + simpl.
        rewrite <-(G 0 Point).
        simpl.
        rewrite <-(H 0 ((η x') 0 Point)).
        now f_equiv.
      + simpl.
        rewrite <-(G (S i) Point).
        simpl.
        rewrite (H (S i) ((η x') (S i) Point)).
        simpl.
        f_equiv.
        rewrite IHi.
        rewrite <-(eta_comp x' _ _
                    (le_S_n i (S i) (le_S (S i) (S i) (le_n (S i)))) Point).
        simpl.
        f_equiv.
        symmetry.
        apply PointUnique.
  Qed.

  Program Definition FixProperty
    (X : tree) (ϕ : X [↣] X) (H : Contractive X X ϕ)
    : Σ! (t : (𝟙 @ tree)%cat [↣] X) , ϕ ∘ t ≡ t
    := existT (Fix X ϕ H) (FixUnique X ϕ H).

  Lemma NextNatIso1 : (! @ tree) ∘ next ≡ ı.
  Proof.
    intros x.
    intros a.
    rewrite (@PointUnique NatCat x ((η (@arrow_id (FunCat _ _) ((𝟙 @ tree)))) x a)).
    apply PointUnique.
  Qed.

  Lemma NextNatIso2 : next ∘ (! @ tree) ≡ ı.
  Proof.
    intros x.
    destruct x as [| x].
    - now destruct 1.
    - intros a.
      rewrite (@PointUnique NatCat x ((η (@arrow_id (FunCat _ _) ((𝟙 @ tree)))) x a)).
      apply PointUnique.
  Qed.

  Program Definition mfix {X : tree} (f : ▶ X [~>] X) : 𝟙 @ tree [~>] X
    := (Fix X (f ∘ next) (existT f (reflexivity (f ∘ next)))).

  Notation "μ( f )" := (mfix f) (at level 0, format "μ( f )") : logic_scope.

  Lemma mfix_fix {X} (f : ▶ X [~>] X) : f ∘ next ∘ μ(f) ≡ μ(f).
  Proof.
    apply FixCorrect.
  Qed.

  Lemma mfix_unique {X} {f : ▶ X [~>] X} {h : 𝟙 @ tree [~>] X}
    (e : f ∘ next ∘ h ≡ h) : h ≡ μ(f).
  Proof.
    unshelve epose proof (FixUnique X (f ∘ next) (existT f _)) as H.
    - apply (reflexivity (f ∘ next)).
    - unfold mfix.
      symmetry.
      apply (snd H h e).
  Qed.

  Program Definition LaterProd {X Y}
    : ((▶ X) ×ₒ (▶ Y) @ tree) [~>] (▶ (X ×ₒ Y @ tree))
    := λₙ n,
      (nat_rect
         (λ x,
           bin_prod_obj _ _ ((▶ X) ×ₒ (▶ Y) @ tree) x
             [~>]
             (▶ ((X ×ₒ Y @ tree))) x)
         (constS _) _ n).
  Next Obligation.
    intros; constructor.
  Defined.
  Next Obligation.
    intros; simpl.
    apply idS.
  Defined.
  Next Obligation.
    intros ?? [| n] [| m] f [? ?]; simpl.
    - destruct (Nat.le_0_r 0) as [G1 G2].
      assert (G1 f = Logic.eq_refl) as ->.
      { apply proof_irrel. }
      simpl.
      reflexivity.
    - exfalso.
      simpl in *.
      lia.
    - reflexivity.
    - split.
      + reflexivity.
      + reflexivity.
  Qed.

  Definition LaterApp {X Y} : ▶ (X ⇒ Y @ tree) [~>] ▶ X ⇒ ▶ Y @ tree
    := Curry (functor.fmap Later eval ∘ LaterProd).

  Definition fixI {X} : ▶ X ⇒ X @ tree [~>] X
    := (eval
         ∘ ⟨(mfix (λ⟨eval ∘ (⟨π₂ , eval ∘ ⟨ LaterApp ×ₐ next ⟩⟩)⟩) ∘ (! @ tree)), ı ⟩).

  Program Definition laterI : Ω @ tree [~>] Ω @ tree :=
    λₙ x, λₛ y, λᵢ p, λₛ t,
      match p as n return ((n : NatCat) [~>] x → PropSetoid) with
      | 0 => λ _ : (0 : NatCat) [~>] x, True
      | S n => λ t0 : (S n : NatCat) [~>] x, y n (le_Sn_le n x t0)
      end t.
  Next Obligation.
    intros; simpl.
    destruct p; simpl.
    - reflexivity.
    - rewrite (proof_irrel (le_Sn_le p x a₁) (le_Sn_le p x a₂)).
      reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    revert H.
    revert d f g.
    destruct e; simpl; intros.
    - constructor.
    - destruct d.
      + exfalso.
        lia.
      + pose proof (@sieve_closed _ _ y d e (le_Sn_le d x f) (le_S_n _ _ g) H) as J.
        simpl in J.
        erewrite proof_irrel.
        apply J.
  Qed.
  Next Obligation.
    intros; simpl.
    intros d.
    destruct d; intros f.
    - reflexivity.
    - apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ???.
    destruct d; simpl.
    - reflexivity.
    - erewrite (proof_irrel
                 (Nat.le_trans d Y X (le_Sn_le d Y f0) f)
                 (le_Sn_le d X (Nat.le_trans (S d) Y X f0 f))).
      reflexivity.
  Qed.

  Definition later {Γ : tree} (P : Γ [~>] Ω @ tree) : Γ [~>] Ω @ tree
    := laterI ∘ P.

  Notation "'▷ᵢ' P" := (later P) (at level 80) : logic_scope.

  Lemma later_intro {Γ} (P : Γ [~>] Ω @ tree) :
    P ⊢ᵢ ▷ᵢ P.
  Proof.
    intros [| n] x Px; simpl.
    - constructor.
    - pose proof (@sieve_closed _ _ ((η P) (S n) x) (S n) n ı (le_Sn_le n (S n) (le_n (S n))) Px) as J.
      simpl in J.
      erewrite proof_irrel.
      apply J.
  Qed.

  Lemma later_mono {Γ} (P Q : Γ [~>] Ω @ tree) :
    P ⊢ᵢ Q →
    ▷ᵢ P ⊢ᵢ ▷ᵢ Q.
  Proof.
    intros H [| n] x Px; simpl in *.
    - done.
    - specialize (H n (functor.fmap Γ (le_Sn_le n (S n) (le_n (S n))) x)).
      simpl in H.
      rewrite (proof_irrel (le_Sn_le n (S n) (le_n (S n)))
                 (Nat.le_trans n n (S n) (le_n n) (le_Sn_le n (S n) (le_n (S n))))).
      apply (proj1 (eta_comp Q _ _ (le_Sn_le n (S n) (le_n (S n))) x n ı)).
      simpl.
      apply H.
      apply (proj2 (eta_comp P _ _ (le_Sn_le n (S n) (le_n (S n))) x n ı)).
      simpl.
      erewrite proof_irrel.
      apply Px.
  Qed.

  Lemma later_elim (P : 𝟙 @ tree [~>] Ω @ tree) :
    ⊤ᵢ ⊢ᵢ ▷ᵢ P →
    ⊤ᵢ ⊢ᵢ P.
  Proof.
    intros H n a _.
    pose proof (H (S n) Point I) as J.
    simpl in J.
    epose proof (eta_comp P _ _ (le_Sn_le n (S n) (le_n (S n))) Point n ı) as K.
    simpl in K.
    match goal with
    | H : context G [@Build_NatTrans ?T ?d ?e ?q ?r ?f] |- _ =>
        set (s := @Build_NatTrans T d e q r f)
    end.
    assert ((η P) n (s : NatTransSetoid _ _ _ _) n (le_n n) ≡ (η P) n a n ı) as KKK.
    - subst s.
      apply (setoid_arr_eq _ _ ((η P) n)).
      intros [].
    - rewrite <-KKK.
      apply K.
      erewrite proof_irrel.
      apply J.
  Qed.

  Lemma later_loeb {Γ} (P : Γ [~>] Ω @ tree) :
    ▷ᵢ P ⊢ᵢ P →
    ⊤ᵢ ⊢ᵢ P.
  Proof.
    intros H n x _.
    induction n as [| n IHn]; simpl.
    - now apply (H 0).
    - apply (H (S n)); simpl.
      pose proof (IHn (functor.fmap Γ (le_Sn_le n (S n) (le_n (S n))) x)) as J.
      pose proof (proj1 (eta_comp P _ _ (le_Sn_le n (S n) (le_n (S n))) x n ı) J) as J'.
      simpl in J'.
      erewrite proof_irrel.
      apply J'.
  Qed.

  Lemma later_eq {Γ A} (t u : Γ [~>] A) :
    ▷ᵢ (t ≡ᵢ u) ⊢ᵢ next ∘ t ≡ᵢ next ∘ u.
  Proof.
    intros n x He; simpl in *.
    destruct n as [| n]; simpl.
    - destruct (Nat.le_0_r 0) as [G1 G2].
      assert (G1 (le_n 0) = Logic.eq_refl) as ->.
      { apply proof_irrel. }
      simpl.
      reflexivity.
    - rewrite <-(@fmap_comp _ _ A _ _ _ (le_S_n n n (le_n (S n)))
                  (le_S_n n (S n) (le_S (S n) (S n) (le_n (S n)))) ((η t) (S n) x)).
      rewrite <-(@fmap_comp _ _ A _ _ _ (le_S_n n n (le_n (S n)))
                  (le_S_n n (S n) (le_S (S n) (S n) (le_n (S n)))) ((η u) (S n) x)).
      simpl.
      erewrite proof_irrel at 1.
      erewrite proof_irrel at 1.
      apply He.
  Qed.

  Lemma later_eq_inv {Γ A} (t u : Γ [~>] A) :
    next ∘ t ≡ᵢ next ∘ u ⊢ᵢ ▷ᵢ (t ≡ᵢ u).
  Proof.
    intros n x H.
    destruct n as [| n].
    - done.
    - simpl in *.
      rewrite <-(@fmap_comp _ _ A _ _ _ (le_S_n n n (le_n (S n)))
                  (le_S_n n (S n) (le_S (S n) (S n) (le_n (S n)))) ((η t) (S n) x)) in H.
      rewrite <-(@fmap_comp _ _ A _ _ _ (le_S_n n n (le_n (S n)))
                  (le_S_n n (S n) (le_S (S n) (S n) (le_n (S n)))) ((η u) (S n) x)) in H.
      simpl in H.
      erewrite proof_irrel at 1.
      erewrite proof_irrel at 1.
      apply H.
  Qed.

  Lemma later_false_em {Γ} (P : Γ [~>] Ω @ tree) : ▷ᵢ P ⊢ᵢ ▷ᵢ ⊥ᵢ ∨ᵢ (▷ᵢ ⊥ᵢ →ᵢ P).
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

  Lemma later_intuit_forall {A} (Φ : A → (GlobalSections (Ω @ tree)))
    : (∀ᵢ a, (▷ᵢ (Φ a))) ⊢ᵢ ▷ᵢ ∀ᵢ a, Φ a.
  Proof.
    intros n γ H.
    destruct n as [| n].
    - constructor.
    - intros q e r.
      simpl.
      erewrite (proof_irrel (Nat.le_trans q n (S n) e (le_Sn_le n (S n) (le_n (S n))))).
      apply (H (S q) (le_n_S _ _ e) r).
  Qed.

  Lemma later_intuit_exist_false {A} (Φ : A → (GlobalSections (Ω @ tree))) :
    (▷ᵢ ∃ᵢ a, Φ a) ⊢ᵢ ▷ᵢ ⊥ᵢ ∨ᵢ (∃ᵢ a, ▷ᵢ (Φ a)).
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

  Lemma later_intro' {Γ} (P R : Γ [~>] Ω @ tree) :
    R ⊢ᵢ P →
    R ⊢ᵢ ▷ᵢ P.
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply later_intro.
  Qed.

  Lemma later_mono' {Γ} : Proper ((@entails _ Γ) ==> (@entails _ Γ)) later.
  Proof.
    intros P R H.
    apply later_mono.
    apply H.
  Qed.

  Lemma later_loeb' {Γ} (P : Γ [~>] Ω @ tree) :
    (▷ᵢ P ⊢ᵢ P) → (⊤ᵢ ⊢ᵢ P).
  Proof.
    intros H.
    apply later_loeb.
    apply H.
  Qed.

  Lemma later_false_em' {Γ} (R P : Γ [~>] Ω @ tree)
    : R ⊢ᵢ ▷ᵢ P →
      R ⊢ᵢ ▷ᵢ ⊥ᵢ ∨ᵢ (▷ᵢ ⊥ᵢ →ᵢ P).
  Proof.
    intros H.
    eapply entails_trans.
    - apply H.
    - apply later_false_em.
  Qed.

End Nat.
