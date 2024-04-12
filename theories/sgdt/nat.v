From category Require Import
  base
  setoid
  category
  sets
  initial
  terminal
  functor
  limit
  colimit
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
Require Import classes.colimits.
Require Import classes.exp.
Require Import classes.subobject.
Require Import classes.enrichment.
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

  Program Definition cover_arrow_nat {n : NatCat} : (0 : NatCat) [~>] n := le_0_n _.

  Program Definition step_arrow_nat {n : NatCat} : n [~>] (S n) := le_S _ _ (le_n _).

  Program Definition down_arrow_nat {n m : NatCat}
    (f : (S n : NatCat) [~>] S m)
    : n [~>] m := le_S_n _ _ f.

  Program Definition up_arrow_nat {n m : NatCat}
    (f : n [~>] m)
    : (S n : NatCat) [~>] S m := le_n_S _ _ f.

  Definition tree := PSh NatCat.

  Ltac elim_eq_irrel := match goal with
                        | |- context G [eq_rect_r _ _ ?a] =>
                            try rewrite (proof_irrel a Logic.eq_refl)
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
    destruct m.
    - apply Nat.le_0_r in H.
      rewrite H.
      apply idS.
    - destruct n.
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
      repeat (elim_eq_irrel; simpl).
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
      elim_eq_irrel.
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
    - now intros [].
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
    intros n γ [| m] f Px.
    - constructor.
    - simpl.
      pose proof (@sieve_closed _ _ ((η P) n γ) (S m) m f (le_Sn_le m (S m) (le_n (S m))) Px) as J.
      simpl in J.
      erewrite proof_irrel.
      apply J.
  Qed.

  Lemma later_mono {Γ} (P Q : Γ [~>] Ω @ tree) :
    P ⊢ᵢ Q →
    ▷ᵢ P ⊢ᵢ ▷ᵢ Q.
  Proof.
    intros H n γ [| m] f Px; simpl in *.
    - constructor.
    - apply H.
      apply Px.
  Qed.

  Lemma later_elim (P : 𝟙 @ tree [~>] Ω @ tree) :
    ⊤ᵢ ⊢ᵢ ▷ᵢ P →
    ⊤ᵢ ⊢ᵢ P.
  Proof.
    intros H n γ m f _.
    specialize (H (S n) Point (S m) (le_n_S _ _ f) I).
    simpl in H.
    epose proof (eta_comp P _ _ (le_Sn_le n (S n) (le_n (S n))) Point m f) as K.
    simpl in K.
    match goal with
    | H : context G [@Build_NatTrans ?T ?d ?e ?q ?r ?f] |- _ =>
        set (s := @Build_NatTrans T d e q r f)
    end.
    assert ((η P) n (s : NatTransSetoid _ _ _ _) m f ≡ (η P) n γ m f) as KKK.
    - subst s.
      apply (setoid_arr_eq _ _ ((η P) n)).
      intros [].
    - rewrite <-KKK.
      subst s.
      apply K.
      erewrite proof_irrel.
      apply H.
  Qed.

  Lemma later_loeb {Γ} (P : Γ [~>] Ω @ tree) :
    ▷ᵢ P ⊢ᵢ P →
    ⊤ᵢ ⊢ᵢ P.
  Proof.
    intros H n γ m f _.
    revert n γ f.
    induction m as [| m IHn]; intros n γ f; simpl.
    - pose proof (H 0 (functor.fmap Γ f γ) 0 ı I) as J.
      rewrite ->(eta_comp P _ _ f γ 0 ı) in J.
      simpl in J.
      erewrite proof_irrel.
      apply J.
    - apply (H n γ (S m) f).
      simpl.
      apply IHn.
  Qed.

  Lemma later_eq {Γ A} (t u : Γ [~>] A) :
    ▷ᵢ (t ≡ᵢ u) ⊢ᵢ next ∘ t ≡ᵢ next ∘ u.
  Proof.
    intros n γ m f He.
    destruct m as [| m].
    - destruct n as [| n]; simpl.
      + destruct (Nat.le_0_r 0) as [G1 G2].
        inversion f; subst.
        assert (G1 f = Logic.eq_refl) as ->.
        { apply proof_irrel. }
        simpl.
        reflexivity.
      + reflexivity.
    - destruct n as [| n]; simpl.
      + inversion f.
      + simpl in He.
        rewrite <-(@fmap_comp _ _ A _ _ _ (le_S_n m n f)
                    (le_S_n n (S n) (le_S (S n) (S n) (le_n (S n))))
                    ((η t) (S n) γ)).
        rewrite <-(@fmap_comp _ _ A _ _ _ (le_S_n m n f)
                    (le_S_n n (S n) (le_S (S n) (S n) (le_n (S n))))
                    ((η u) (S n) γ)).
        simpl.
        erewrite proof_irrel at 1.
        erewrite proof_irrel at 1.
        apply He.
  Qed.

  Lemma later_eq_inv {Γ A} (t u : Γ [~>] A) :
    next ∘ t ≡ᵢ next ∘ u ⊢ᵢ ▷ᵢ (t ≡ᵢ u).
  Proof.
    intros n γ m f H.
    destruct m as [| m].
    - done.
    - simpl.
      destruct n as [| n].
      + inversion f.
      + simpl in H.
        rewrite <-(@fmap_comp _ _ A _ _ _ (le_S_n m n f)
                    (le_S_n n (S n) (le_S (S n) (S n) (le_n (S n))))
                    ((η t) (S n) γ)) in H.
        rewrite <-(@fmap_comp _ _ A _ _ _ (le_S_n m n f)
                    (le_S_n n (S n) (le_S (S n) (S n) (le_n (S n))))
                    ((η u) (S n) γ)) in H.
        simpl in H.
        erewrite proof_irrel at 1.
        erewrite proof_irrel at 1.
        apply H.
  Qed.

  Lemma later_false_em {Γ} (P : Γ [~>] Ω @ tree) : ▷ᵢ P ⊢ᵢ ▷ᵢ ⊥ᵢ ∨ᵢ (▷ᵢ ⊥ᵢ →ᵢ P).
  Proof.
    intros ?????.
    destruct m as [| m].
    - now left.
    - right.
      intros q e G.
      destruct q as [| q].
      + simpl in H.
        simpl.
        erewrite proof_irrel.
        apply (@sieve_closed _ _ ((η P) n γ) m 0 (Le.le_Sn_le_stt _ _ f) (le_0_n _)).
        apply H.
      + exfalso; apply G.
  Qed.

  Lemma later_intuit_forall {A} (Φ : A → (GlobalSections (Ω @ tree)))
    : (∀ᵢ a, (▷ᵢ (Φ a))) ⊢ᵢ ▷ᵢ ∀ᵢ a, Φ a.
  Proof.
    intros n γ m f H.
    destruct m as [| m].
    - constructor.
    - intros q e r.
      simpl.
      erewrite proof_irrel.
      apply (H (S q) (le_n_S _ _ e) r).
  Qed.

  Lemma later_intuit_exist_false {A} (Φ : A → (GlobalSections (Ω @ tree))) :
    (▷ᵢ ∃ᵢ a, Φ a) ⊢ᵢ ▷ᵢ ⊥ᵢ ∨ᵢ (∃ᵢ a, ▷ᵢ (Φ a)).
  Proof.
    intros n γ m f H.
    destruct m as [| m].
    - now left.
    - right.
      destruct H as [r H].
      exists r.
      simpl.
      erewrite proof_irrel.
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

Section Temp2.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Local Opaque has_limits.
  Local Opaque has_terminal.

  
End Temp2.

Section Temp1.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Local Opaque has_limits.
  Local Opaque has_terminal.
  Local Opaque quote.
  Local Opaque unquote.

  Definition Dist {X Y : tree} (n : NatCat) (f g : X [~>] Y) :=
    ∀ n' (δ : n' < n), (f n') ≡ (g n').

  Lemma DistMono {X Y : tree} (n : NatCat) (f g : X [~>] Y)
    : ∀ m (δ : m [~>] n), Dist n f g → Dist m f g.
  Proof.
    intros m δ H n' γ.
    apply H, (δ ∘ γ).
  Qed.

  Local Instance DistEquiv {X Y : tree} : ∀ n, Equivalence (@Dist X Y n).
  Proof.
    intros n.
    split.
    - intros ???.
      reflexivity.
    - intros ?? H ??.
      symmetry.
      now apply H.
    - intros ??? H G ??.
      etransitivity.
      + now apply H.
      + now apply G.
  Qed.

  Definition DistLift {X Y : (tree op) × tree} (n : NatCat) (f g : X [~>] Y) : Prop
    := ∀ n' (δ : n' < n), (fst f n' ≡ fst g n') ∧ (snd f n' ≡ snd g n').

  Lemma DistLiftMono {X Y : (tree op) × tree} (n : NatCat) (f g : X [~>] Y)
    : ∀ m (δ : m [~>] n), DistLift n f g → DistLift m f g.
  Proof.
    intros m δ H n' γ.
    apply H, (δ ∘ γ).
  Qed.

  Local Instance DistLiftEquiv {X Y : (tree op) × tree} : ∀ n, Equivalence (@DistLift X Y n).
  Proof.
    intros n.
    split.
    - intros ???.
      split; reflexivity.
    - intros ?? H ??.
      split; symmetry; now apply H.
    - intros ??? H G ??; split; (etransitivity; [now apply H | now apply G]).
  Qed.

  Definition LocallyContractive (F : ((tree op) × tree) [⇒] tree)
    := ∀ {X Y : ((tree op) × tree)} (f g : X [~>] Y) n,
    DistLift n f g → Dist (S n) (functor.fmap F f) (functor.fmap F g).

  Lemma DistZeroContractive (F : ((tree op) × tree) [⇒] tree)
    (FC : LocallyContractive F) {A B} (f g : A [~>] B) : Dist 0 (functor.fmap F f) (functor.fmap F g).
  Proof.
    intros ? δ.
    inversion δ; subst.
  Qed.

  Lemma DistSuccContractive (F : ((tree op) × tree) [⇒] tree)
    (FC : LocallyContractive F) {A B} (f g : A [~>] B) n :
    DistLift n f g →
    Dist (S n) (functor.fmap F f) (functor.fmap F g).
  Proof.
    intros H ? δ.
    apply (FC A B f g n H n' δ).
  Qed.

  Lemma fmap_id' {X Y : Category} {G : Functor X Y}
    : ∀ {A} (f : A [~>] A), f ≡ ı → functor.fmap G f ≡ ı.
  Proof.
    intros ? f ->.
    apply fmap_id.
  Qed.

  Lemma DistCongL {X Y : tree} (n : NatCat) (f g : X [~>] Y)
    : ∀ f', f ≡ f' → Dist n f' g → Dist n f g.
  Proof.
    intros f' H G.
    intros m δ.
    rewrite (H m).
    now apply G.
  Qed.

  Lemma DistCongR {X Y : tree} (n : NatCat) (f g : X [~>] Y)
    : ∀ g', g ≡ g' → Dist n f g' → Dist n f g.
  Proof.
    intros f' H G.
    intros m δ.
    rewrite (H m).
    now apply G.
  Qed.

  Context (F : ((tree op) × tree) [⇒] tree).
  Context (FC : LocallyContractive F).
  Context (base : 𝟙 @ tree [~>] F (𝟙 @ tree, 𝟙 @ tree)).

  Fixpoint Tower (n : NatCat) : tree :=
    match n with
    | 0 => F (𝟙 @ tree, 𝟙 @ tree)
    | S n' => F (Tower n', Tower n')
    end.

  Record TowerSolution (β : NatCat) :=
    {
      e : ∀ γ (δ : γ [~>] β), (Tower γ) [↣] (Tower β);
      e_id : e β ı ≡ ı;
      p : ∀ γ (δ : γ [~>] β), (Tower β) [↣] (Tower γ);
      p_id : p β ı ≡ ı;
      ep : ∀ γ (δ : γ [~>] β), p γ δ ∘ e γ δ ≡ ı;
      pe : ∀ γ (δ : γ [~>] β), Dist γ (e γ δ ∘ p γ δ) ı;
    }.

  Program Definition Solution (n : NatCat) : TowerSolution n.
  Proof using F FC base.
    induction n as [| n IH].
    - unshelve econstructor.
      + intros ? H.
        assert (γ = 0) as ->.
        { now inversion H. }
        apply ı.
      + intros ? H.
        assert (γ = 0) as ->.
        { now inversion H. }
        apply ı.
      + intros ? H.
        reflexivity.
      + intros ? H.
        reflexivity.
      + intros γ H.
        assert (γ = 0) as ->.
        { now inversion H. }
        intros ??; simpl.
        rewrite (proof_irrel _ Logic.eq_refl).
        simpl.
        reflexivity.
      + intros γ H.
        assert (γ = 0) as ->.
        { now inversion H. }
        intros ???; simpl.
        rewrite (proof_irrel _ Logic.eq_refl).
        simpl.
        reflexivity.
    - unshelve econstructor.
      + intros γ H.
        simpl in H.
        simpl.
        destruct γ as [| γ'].
        * simpl in *.
          apply (functor.fmap F).
          simpl.
          split; [apply (! @ tree) |].
          apply (e _ IH 0 cover_arrow_nat ∘ base).
        * apply (@functor.fmap _ _ F
                   (Tower γ', Tower γ')
                   (Tower n, Tower n)
                   ((p _ IH γ' (down_arrow_nat H)), (e _ IH γ' (down_arrow_nat H)))).
      + intros γ H.
        simpl in H.
        simpl.
        destruct γ as [| γ'].
        * simpl in *.
          apply (functor.fmap F).
          simpl.
          split; [| apply (! @ tree)].
          apply (e _ IH 0 cover_arrow_nat ∘ base).
        * simpl.
          apply (@functor.fmap _ _ F
                   (Tower n, Tower n)
                   (Tower γ', Tower γ')
                   ((e _ IH γ' (down_arrow_nat H)), (p _ IH γ' (down_arrow_nat H)))).
      + apply fmap_id'.
        assert (down_arrow_nat ı = ı) as ->.
        { apply proof_irrel. }
        split.
        * rewrite (p_id n IH).
          reflexivity.
        * rewrite (e_id n IH).
          reflexivity.
      + apply fmap_id'.
        assert (down_arrow_nat ı = ı) as ->.
        { apply proof_irrel. }
        split.
        * rewrite (e_id n IH).
          reflexivity.
        * rewrite (p_id n IH).
          reflexivity.
      + intros [| γ] ?.
        * cbn zeta.
          set (e n IH 0 cover_arrow_nat ∘ base) as t.
          etransitivity; [symmetry; apply fmap_comp |].
          apply fmap_id'.
          split.
          -- simpl.
             intros X a.
             rewrite PointUnique.
             symmetry.
             apply PointUnique.
          -- simpl.
             intros X a.
             rewrite PointUnique.
             symmetry.
             apply PointUnique.
        * set (e n IH γ (down_arrow_nat δ)) as t1.
          set (p n IH γ (down_arrow_nat δ)) as t2.
          etransitivity; [symmetry; apply fmap_comp |].
          set (s1 := (t1, t2) : (@Arr (ProdCat (Op tree) tree) (Tower n, Tower n) (Tower γ, Tower γ))).
          set (s2 := (t2, t1) : (@Arr (ProdCat (Op tree) tree) (Tower γ, Tower γ) (Tower n, Tower n))).
          assert (s1 ∘ s2 ≡ (t2 ∘ t1, t2 ∘ t1)) as ->.
          {
            subst s1 s2.
            simpl.
            split; reflexivity.
          }
          clear s1 s2.
          set (s := (t2 ∘ t1) : (@Arr tree (Tower γ) (Tower γ))).
          assert (s ≡ ı) as HEQ.
          {
            subst s t1 t2.
            apply (ep n IH γ (down_arrow_nat δ)).
          }
          clearbody s.
          apply fmap_id'.
          split; intros X a; rewrite (HEQ X a); reflexivity.
      + intros [| γ].
        * intros δ.
          cbn zeta.
          set (e n IH 0 cover_arrow_nat ∘ base) as t.
          eapply DistCongL; [symmetry; apply fmap_comp |].
          eapply DistCongR; [symmetry; apply fmap_id |].
          now apply DistZeroContractive.
        * intros δ.
          set (e n IH γ (down_arrow_nat δ)) as t1.
          set (p n IH γ (down_arrow_nat δ)) as t2.
          eapply DistCongL; [symmetry; apply fmap_comp |].
          eapply DistCongR; [symmetry; apply fmap_id |].
          apply DistSuccContractive; [apply FC |].
          intros n' δ'; split; simpl; subst t1 t2; intros a;
            apply (pe n IH γ (down_arrow_nat δ) n' δ' a).
  Defined.

  (* Lemma Tower_comp1 {n m p : NatCat} (a : n [~>] m) (b : m [~>] p) *)
  (*   : (e p (Solution p) n (b ∘ a)) ≡ (e p (Solution p) m b) ∘ (e m (Solution m) n a) *)
  (* with Tower_comp2 {n m p' : NatCat} (a : n [~>] m) (b : m [~>] p') *)
  (*   : (p p' (Solution p') n (b ∘ a)) ≡ (p m (Solution m) n a) ∘ (p p' (Solution p') m b). *)
  (* Proof. *)
  (*   - destruct p. *)
  (*     + simpl in b; inversion b; subst. *)
  (*       simpl in a; inversion a; subst. *)
  (*       assert ((a : (0 : NatCat) [~>] 0) ≡ ı) as ->. *)
  (*       { apply proof_irrel. } *)
  (*       assert ((b : (0 : NatCat) [~>] 0) ≡ ı) as ->. *)
  (*       { apply proof_irrel. } *)
  (*       rewrite arrow_comp_id_l. *)
  (*       rewrite e_id. *)
  (*       rewrite arrow_comp_id_l. *)
  (*       reflexivity. *)
  (*     + destruct m. *)
  (*       * simpl in a; inversion a; subst. *)
  (*         assert ((a : (0 : NatCat) [~>] 0) ≡ ı) as ->. *)
  (*         { apply proof_irrel. } *)
  (*         rewrite e_id. *)
  (*         rewrite ->2 arrow_comp_id_r. *)
  (*         reflexivity. *)
  (*       * admit. *)
  (*   - destruct p'. *)
  (*     + simpl in b; inversion b; subst. *)
  (*       simpl in a; inversion a; subst. *)
  (*       assert ((a : (0 : NatCat) [~>] 0) ≡ ı) as ->. *)
  (*       { apply proof_irrel. } *)
  (*       assert ((b : (0 : NatCat) [~>] 0) ≡ ı) as ->. *)
  (*       { apply proof_irrel. } *)
  (*       rewrite arrow_comp_id_l. *)
  (*       rewrite p_id. *)
  (*       rewrite arrow_comp_id_l. *)
  (*       reflexivity. *)
  (*     + destruct m. *)
  (*       * simpl in a; inversion a; subst. *)
  (*         assert ((a : (0 : NatCat) [~>] 0) ≡ ı) as ->. *)
  (*         { apply proof_irrel. } *)
  (*         rewrite p_id. *)
  (*         rewrite arrow_comp_id_l, arrow_comp_id_r. *)
  (*         reflexivity. *)
  (*       * admit. *)
  (* Admitted. *)

  Program Definition Tower_fmap {n m : NatCat} (H : n [~>] m)
    : Tower n [~>] Tower m := (e _ (Solution m) n H).

  Program Definition Tower_fmap_inv {n m : NatCat} (H : m [~>] n)
    : Tower n [~>] Tower m := (p _ (Solution n) m H).

  Program Definition TowerF : NatCat [⇒] tree :=
    {|
      FO X := Tower X;
      functor.fmap A B := λₛ f, Tower_fmap f;
    |}.
  Next Obligation.
    intros ???? ->.
    reflexivity.
  Qed.
  Next Obligation.
    intros A X a; simpl.
    unfold Tower_fmap.
    rewrite (e_id A (Solution A) X a).
    reflexivity.
  Qed.
  Next Obligation.
    intros ??? f g. cbn beta.
    unfold Tower_fmap.
    simpl setoid_arr.
    admit.
  Admitted.

  Program Definition solution_iso : Isomorphism (lim TowerF @ tree) (colim TowerF @ tree) :=
    {|
      iso1 := λₙ x, λₛ Xx, _;
    |}.
  Next Obligation.
    intros x Xx.
    simpl.
    exists x.
    apply Xx.
    constructor.
  Defined.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Program Definition under_approximation : Cone TowerF :=
    {|
      cone_obj := F (lim TowerF @ tree, lim TowerF @ tree);
    |}.
  Next Obligation.
  Admitted.

  Program Definition over_approximation : Cocone TowerF :=
    {|
      cocone_obj := F (lim TowerF @ tree, lim TowerF @ tree);
    |}.
  Next Obligation.
  Admitted.

  Lemma solution_correct (s : tree) : Isomorphism ((lim TowerF @ tree)) (F ((lim TowerF @ tree), (lim TowerF @ tree))).
  Proof.
    unshelve econstructor.
    - pose proof (iso1 solution_iso).
      admit.
    - pose proof (iso2 solution_iso).
      admit.
    - admit.
    - admit.
  Admitted.

End Temp1.

(* (* Record StrongFunctor (C D : Category) *) *)
(* (*   `{!hasBinaryProducts C} *) *)
(* (*   `{!hasExp C} *) *)
(* (*   `{!hasTerminal C} *) *)
(* (*   `{!SelfEnrichment C} *) *)
(* (*   `{!hasBinaryProducts D} *) *)
(* (*   `{!hasExp D} *) *)
(* (*   `{!hasTerminal D} *) *)
(* (*   `{!SelfEnrichment D} := *) *)
(* (*   { *) *)
(* (*     SFO :> C [⇒] D; *) *)
(* (*     Sfmap {A B : C} (f : (𝟙 @ C) [~>] (A ⇒ B @ C)) *) *)
(* (*     : 𝟙 @ D [~>] (SFO A ⇒ SFO B @ D); *) *)
(* (*     Sfmap_id {A : C} *) *)
(* (*     : Sfmap (quote (arrow_id A)) ≡ quote (arrow_id (SFO A)); *) *)
(* (*     Sfmap_comp {A B C : C} (g : B [~>] C) (f : A [~>] B) *) *)
(* (*     : Sfmap (quote (g ∘ f)) ≡ HOM_COMP ∘ (⟨(Sfmap (quote g)), (Sfmap (quote f))⟩); *) *)
(* (*     Sfmap_decompose {A B : C} (f : A [~>] B) *) *)
(* (*     : Sfmap (quote f) ≡ quote (functor.fmap SFO f); *) *)
(* (*   }. *)   *)

(* Record IsomorphismUnpacked {C : Category} {X Y : C} *)
(*   (f : X [~>] Y) (g : Y [~>] X) := *)
(*   { *)
(*     unpack_iso12 : g ∘ f ≡ ı; *)
(*     unpack_iso21 : f ∘ g ≡ ı; *)
(*   }. *)

(* Record αIsomorphism {X Y : tree} (f : X [~>] Y) (g : Y [~>] X) (α : NatCat) := *)
(*   { *)
(*     αiso : ∀ (β : NatCat), (S β : NatCat) [~>] α *)
(*                            → IsomorphismUnpacked (f (S β)) (g (S β)); *)
(*   }. *)

(* Section Temp. *)
(*   Local Open Scope setoid_scope. *)
(*   Local Open Scope cat_scope. *)
(*   Local Open Scope functor_scope. *)

(*   Lemma ContractiveZ {X Y : tree} {ϕ : X [↣] Y} {HC : Contractive X Y ϕ} *)
(*     : ∃ t, ϕ 0 ≡ constS t. *)
(*   Proof. *)
(*     destruct HC as [ψ H]. *)
(*     assert (G : ∃ t, (η (ψ ∘ next)) 0 ≡ constS t). *)
(*     { *)
(*       simpl. *)
(*       exists ((η ψ) 0 ()). *)
(*       done. *)
(*     } *)
(*     destruct G as [t G]. *)
(*     exists t. *)
(*     rewrite (H 0). *)
(*     apply G. *)
(*   Qed. *)

(*   Lemma ContractiveS {X Y : tree} {ϕ : X [↣] Y} *)
(*     {HC : Contractive X Y ϕ} *)
(*     (n : NatCat) *)
(*     : ϕ (S n) ≡ projT1 HC (S n) ∘ functor.fmap X step_arrow_nat. *)
(*   Proof. *)
(*     rewrite (projT2 HC (S n)). *)
(*     intros a; simpl. *)
(*     do 3 f_equiv. *)
(*     apply proof_irrel. *)
(*   Qed. *)

(*   Opaque has_terminal. *)
(*   Opaque ArrBinUnrec. *)

(*   Record Strong (F : tree [⇒] tree) := *)
(*     { *)
(*       strength (A : tree op) (B : tree) *)
(*       :> HOM tree PShEnrichment (A, B) [~>] HOM tree PShEnrichment ((F A), (F B)); *)
(*       strength_decomp {A B : tree} {f : A [~>] B} *)
(*       : (strength A B ∘ (quote tree PShEnrichment f)) *)
(*           ≡ quote tree PShEnrichment (functor.fmap F f); *)
(*       (* strength_natural {A A' B B' : tree} *) *)
(*       (*   (f : A [~>] B) (g : A' [~>] A) (h : B [~>] B') *) *)
(*       (* : True; *) *)
(*     }. *)

(*   Definition PSh_dist {X : tree} (n : NatCat) (x y : GlobalSections X) := *)
(*     ∀ n' (f : n' [~>] n), (x n') ≡ (y n'). *)

(*   Record LocallyContractive (F : tree [⇒] tree) (FS : Strong F) := *)
(*     { *)
(*       contractive {X Y : tree} {x y : 𝟙 @ tree [~>] (HOM tree PShEnrichment (X, Y))} {n} : *)
(*       @PSh_dist (HOM tree PShEnrichment (X, Y)) n x y → *)
(*       @PSh_dist (HOM tree PShEnrichment (F X, F Y)) (S n) (strength F FS _ _ ∘ x) (strength F FS _ _ ∘ y); *)
(*     }. *)

(*   Definition strong (F' : tree [⇒] tree) *)
(*     := ∀ A B, sigT (λ (g : (A ⇒ B @ tree) [~>] (F' A ⇒ F' B @ tree)), *)
(*                   ∀ (f : A [~>] B), g ∘ (λ⟨f ∘ π₂⟩ : 𝟙 @ tree [~>] (A ⇒ B @ tree)) *)
(*                                       ≡ λ⟨functor.fmap F' f ∘ π₂⟩). *)

(*   Definition locally_contractive (F : tree [⇒] tree) *)
(*     {FS : strong F} := ∀ A B, Contractive _ _ (projT1 (FS A B)). *)

(*   Program Definition st (F' : tree [⇒] tree) (FS : strong F') *)
(*     : F' (𝟙 @ tree)  [~>] F' (F' (𝟙 @ tree)) *)
(*     := λₙ x, λₛ y, (projT1 (FS (𝟙 @ tree) (F' (𝟙 @ tree))) x *)
(*                             (λₖ Γ, λₛ σ, λₛ k, *)
(*                               (functor.fmap (F' (𝟙 @ tree)) σ y)) *)
(*                             x ı y). *)
(*   Next Obligation. *)
(*     intros; simpl. *)
(*     reflexivity. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     intros; simpl. *)
(*     intros ?. *)
(*     rewrite H. *)
(*     reflexivity. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     intros. *)
(*     intros ?????. *)
(*     simpl. *)
(*     pose proof (@fmap_comp _ _ (F' (𝟙 @ tree)) _ _ _ δ₂ δ₁) as HEQ. *)
(*     simpl in HEQ. *)
(*     rewrite HEQ. *)
(*     reflexivity. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     intros ????? H. *)
(*     cbn beta. *)
(*     f_equiv; [| assumption]. *)
(*     f_equiv. *)
(*     match goal with *)
(*     | |- context G [setoid_arr ?b ?a] => *)
(*         set (f := setoid_arr b a) *)
(*     end. *)
(*     match goal with *)
(*     | |- context G [setoid_arr ?b ?a] => *)
(*         set (g := setoid_arr b a) *)
(*     end. *)
(*     assert (G : f ≡ g). *)
(*     { *)
(*       subst f g. apply setoid_arr_eq. intros ???; simpl. *)
(*       now apply setoid_arr_eq. *)
(*     } *)
(*     intros ??. *)
(*     apply (G x). *)
(*   Qed. *)
(*   Next Obligation. *)
(*     intros. *)
(*     intros ?. *)
(*     Opaque has_terminal. *)
(*     Opaque arrow_id. *)
(*     simpl. *)
(*     match goal with *)
(*     | |- context G [@arr ?f ?e ?d ?c ?b] => *)
(*         set (g1 := @arr f e d c b) *)
(*     end. *)
(*     match goal with *)
(*     | |- context G [@arr ?f ?e ?d ?c ?b] => *)
(*         set (g2 := @arr f e d c b) *)
(*     end. *)
(*     epose proof (@arr_fmap _ _ _ _ g2 X Y f ı a) as HEQ1. *)
(*     subst g2. *)
(*     rewrite <-HEQ1; clear HEQ1. *)
(*     rewrite arrow_comp_id_r. *)
(*     match goal with *)
(*     | |- context G [@arr ?f ?e ?d ?c ?b] => *)
(*         set (g2 := @arr f e d c b) *)
(*     end. *)
(*     subst g1 g2. *)
(*     match goal with *)
(*     | |- context G [@Build_RemFun ?f ?e ?d ?c ?b ?g] => *)
(*         set (h1 := @Build_RemFun f e d c b g) *)
(*     end. *)
(*     match goal with *)
(*     | |- context G [@Build_RemFun ?f ?e ?d ?c ?b ?g] => *)
(*         set (h2 := @Build_RemFun f e d c b g) *)
(*     end. *)
(*     pose proof (eta_comp (η projT1 (FS (𝟙 @ tree) (F' (𝟙 @ tree)))) *)
(*                   X Y f h2 Y ı (functor.fmap (F' (𝟙 @ tree)) f a)) as HEQ. *)
(*     simpl in HEQ. *)
(*     Transparent arrow_id. *)
(*     simpl in HEQ. *)
(*     rewrite (proof_irrel (Nat.le_trans Y Y X (le_n _) f) f) in HEQ. *)
(*     rewrite <-HEQ; clear HEQ. *)
(*     subst h1 h2. *)
(*     simpl. *)
(*     apply (@setoid_arr_eq _ _ ((η projT1 (FS (𝟙 @ tree) (F' (𝟙 @ tree)))) Y)). *)
(*     intros ???; simpl. *)
(*     rewrite (@fmap_comp _ _ (F' (𝟙 @ tree)) _ _ _ δ f a). *)
(*     reflexivity. *)
(*   Qed. *)

(*   Record IsomorphismUnpacked {C : Category} {X Y : C} *)
(*     (f : X [~>] Y) (g : Y [~>] X) := *)
(*     { *)
(*       unpack_iso12 : g ∘ f ≡ ı; *)
(*       unpack_iso21 : f ∘ g ≡ ı; *)
(*     }. *)

(*   Record αIsomorphism {X Y : tree} (f : X [~>] Y) (g : Y [~>] X) (α : NatCat) := *)
(*     { *)
(*       αiso : ∀ (β : NatCat), (S β : NatCat) [~>] α → IsomorphismUnpacked (f (S β)) (g (S β)); *)
(*     }. *)

(*   (* Lemma locally_contractive_iso' (F : tree [⇒] tree) *) *)
(*   (*   {Fs : Strong F} {Fc : LocallyContractive F Fs} (n : NatCat) *) *)
(*   (*   (X Y : tree) *) *)
(*   (*   (f : X [~>] Y) (g : Y [~>] X) *) *)
(*   (*   (H : αIsomorphism f g n) : *) *)
(*   (*   αIsomorphism (functor.fmap F f) (functor.fmap F g) (S n). *) *)
(*   (* Proof. *) *)
(*   (*   constructor. *) *)
(*   (*   intros β p. *) *)
(*   (*   Opaque PArr. *) *)
(*   (*   Opaque next. *) *)
(*   (*   constructor; intros a. *) *)
(*   (*   - simpl. *) *)
(*   (*     pose proof (@strength_decomp F Fs X Y f (S β) Point (S β) ı a) as G. *) *)
(*   (*     simpl in G. *) *)
(*   (*     rewrite <-G. *) *)
(*   (*     pose proof (@strength_decomp F Fs Y X g (S β) Point (S β) ı) as G'. *) *)
(*   (*     simpl in G'. *) *)
(*   (*     rewrite <-G'. *) *)
(*   (*     match goal with *) *)
(*   (*     | |- context G [@Build_RemFun ?f ?e ?d ?c ?b ?g] => *) *)
(*   (*         set (h1 := @Build_RemFun f e d c b g : PArr Y X (S β)) *) *)
(*   (*     end. *) *)
(*   (*     match goal with *) *)
(*   (*     | |- context G [@Build_RemFun ?f ?e ?d ?c ?b ?g] => *) *)
(*   (*         set (h2 := @Build_RemFun f e d c b g : PArr X Y (S β)) *) *)
(*   (*     end. *) *)
(*   (*     pose proof ((Fs Y X)). *) *)
(*   (* Admitted. *) *)

(*   Lemma αIsoAnyZ {X Y : tree} (f : X [~>] Y) (g : Y [~>] X) *)
(*     : αIsomorphism f g 0. *)
(*   Proof. *)
(*     constructor. *)
(*     intros ? H. *)
(*     inversion H. *)
(*   Qed. *)

(*   Lemma locally_contractive_iso (F : tree [⇒] tree) *)
(*     {Fs : strong F} {Fc : @locally_contractive F Fs} (n : NatCat) *)
(*     (X Y : tree) *)
(*     (f : X [~>] Y) (g : Y [~>] X) *)
(*     (H : αIsomorphism f g n) : *)
(*     αIsomorphism (functor.fmap F f) (functor.fmap F g) (S n). *)
(*   Proof. *)
(*     constructor. *)
(*     intros β p. *)
(*     Opaque PArr. *)
(*     Opaque next. *)
(*     constructor; intros a. *)
(*     - simpl. *)
(*       pose proof (projT2 (Fs Y X) g (S β) Point (S β) ı) as HEQ1. *)
(*       simpl in HEQ1. *)
(*       rewrite <-HEQ1. *)
(*       clear HEQ1. *)
(*       match goal with *)
(*       | |- context G [@Build_RemFun ?f ?e ?d ?c ?b ?g] => *)
(*           set (h1 := @Build_RemFun f e d c b g : PArr Y X (S β)) *)
(*       end. *)
(*       pose proof (projT2 (Fc Y X) (S β) h1 (S β) ı) as HEQ2. *)
(*       simpl in HEQ2. *)
(*       rewrite HEQ2. *)
(*       clear HEQ2. *)
(*       pose proof (projT2 (Fs X Y) f (S β) Point (S β) ı) as HEQ1. *)
(*       simpl in HEQ1. *)
(*       rewrite <-HEQ1. *)
(*       clear HEQ1. *)
(*       match goal with *)
(*       | |- context G [@Build_RemFun ?f ?e ?d ?c ?b ?g] => *)
(*           set (h2 := @Build_RemFun f e d c b g : PArr X Y (S β)) *)
(*       end. *)
(*       pose proof (projT2 (Fc X Y) (S β) h2 (S β) ı) as HEQ2. *)
(*       simpl in HEQ2. *)
(*       rewrite HEQ2. *)
(*       clear HEQ2. *)
(*       set (b := (le_S_n β (S β) (le_S (S β) (S β) (le_n (S β)))) : (β [~>] S β)). *)
(*       clearbody b. *)
(*       set (c := (le_n (S β)) : ((S β : NatCat) [~>] S β)). *)
(*       clearbody c. *)
(*       match goal with *)
(*       | |- context G [@arr ?f ?e ?d ?c ?b ?a] => *)
(*           set (g1 := @arr f e d c b a) *)
(*       end. *)
(*       match goal with *)
(*       | |- context G [@arr ?f ?e ?d ?c ?b ?a] => *)
(*           set (g2 := @arr f e d c b a) *)
(*       end. *)
(*       assert (g1 c (g2 c a) *)
(*                 ≡ *)
(*                 ((g1 c) *)
(*                 ∘ *)
(*                 (g2 c)) a) as ->. *)
(*       { reflexivity. } *)
(*       subst g1 g2. *)
(*   Admitted. *)

(* End Temp. *)

(* Module RDE2. *)
(*   Local Open Scope setoid_scope. *)
(*   Local Open Scope cat_scope. *)
(*   Local Open Scope functor_scope. *)

(*   (* (* (* 🤡 unfolding control 🤡 *) *) *) *)
(*   (* Opaque has_limits. *) *)
(*   (* Opaque has_terminal. *) *)
(*   (* Opaque has_exp. *) *)
(*   (* Opaque has_binary_products. *) *)
(*   (* Opaque π₁. *) *)
(*   (* Opaque π₂. *) *)
(*   (* Opaque Uncurry. *) *)
(*   (* Opaque Curry. *) *)
(*   (* Opaque ArrBinProd. *) *)
(*   (* Opaque ArrBinUnrec. *) *)
(*   (* Opaque Later. *) *)
(*   (* Opaque arrow_comp. *) *)
(*   (* Opaque arrow_id. *) *)
(*   (* (* (* 🤡🤡🤡 *) *) *) *)

(*   Context (F : ((tree op) × tree) [⇒] tree). *)

(*   Fixpoint Tower (n : NatCat) : tree := *)
(*     match n with *)
(*     | 0 => 𝟙 @ tree *)
(*     | S n' => F (Tower n', Tower n') *)
(*     end. *)

(*   Context (base : 𝟙 @ tree [~>] F (𝟙 @ tree, 𝟙 @ tree)). *)

(*   Opaque has_limits. *)
(*   Opaque has_terminal. *)
(*   Opaque has_exp. *)
(*   Opaque has_binary_products. *)

(*   Fixpoint p (n : NatCat) : Tower (S n) [~>] Tower n *)
(*   with e (n : NatCat) : Tower n [~>] Tower (S n). *)
(*   Proof. *)
(*     - destruct n as [| n]. *)
(*       + apply (! @ tree). *)
(*       + apply (@functor.fmap _ _ F (Tower (S n), Tower (S n)) (Tower n, Tower n) *)
(*                  ((e n), (p n))). *)
(*     - destruct n as [| n]. *)
(*       + apply base. *)
(*       + apply (@functor.fmap _ _ F (Tower n, Tower n) (Tower (S n), Tower (S n)) *)
(*                  ((p n), (e n))). *)
(*   Defined. *)

(*   Lemma ep (n : NatCat) : p n ∘ e n ≡ ı. *)
(*   Proof. *)
(*     induction n as [| n IH]. *)
(*     - rewrite <-(snd (projT2 (@terminal_proj tree (𝟙 @ tree) (𝟙 @ tree))) *)
(*                   (p 0 ∘ e 0)); *)
(*         [| constructor]. *)
(*       now apply (snd (projT2 (@terminal_proj tree (𝟙 @ tree) (𝟙 @ tree))) *)
(*                    (arrow_id (𝟙 @ tree))). *)
(*     - intros X a; simpl. *)
(*       set (t1 := (e n, p n) : @Arr (tree op × tree) (Tower (S n), Tower (S n)) *)
(*                                 (Tower n, Tower n)). *)
(*       set (t2 := (p n, e n) : @Arr (tree op × tree) (Tower n, Tower n) *)
(*                                 (Tower (S n), Tower (S n))). *)
(*       pose proof (@fmap_comp (tree op × tree) tree F *)
(*                     (Tower n, Tower n) *)
(*                     (Tower (S n), Tower (S n)) *)
(*                     _ *)
(*                     t1 *)
(*                     t2 *)
(*                     X a *)
(*         ) as H1. *)
(*       subst t1 t2. *)
(*       rewrite <-H1. *)
(*       clear H1. *)
(*       match goal with *)
(*       | |- context G [@setoid_arr _ _ ?b] => *)
(*           match b with *)
(*           | context H [@setoid_arr _ _ _ ?i] => *)
(*               set (q1 := i) *)
(*           end *)
(*       end. *)
(*       assert (H2 : q1 ≡ ı). *)
(*       { subst q1; simpl; split; intros b Y; now rewrite (IH b Y). } *)
(*       rewrite (@setoid_arr_eq _ _ (functor.fmap F) q1 _ H2 X a). *)
(*       apply (@fmap_id _ _ F _ X a). *)
(*   Qed. *)

(*   Lemma pe (n : NatCat) : αIsomorphism (p n) (e n) n. *)
(*   Proof. *)
(*     induction n as [| n IH]. *)
(*     - apply αIsoAnyZ. *)
(*     - constructor; intros β δ. *)
(*       constructor. *)
(*       + simpl. *)
(*         intros a. *)
(*         (* pose proof (locally_contractive_iso F Fs). *) *)
(*         admit. *)
(*       + intros a; simpl. *)
(*         apply (ep (S n) (S β) a). *)
(*   Admitted. *)

(*   Program Definition Tower_fmap {n m : NatCat} (H : n [~>] m) *)
(*     : Tower n [~>] Tower m. *)
(*   Proof. *)
(*     revert n H. *)
(*     induction m as [| m IHn]; intros n H. *)
(*     - destruct n as [| n]. *)
(*       + apply ı. *)
(*       + exfalso. *)
(*         inversion H. *)
(*     - destruct n as [| n]. *)
(*       + apply (e m ∘ IHn 0 cover_arrow_nat). *)
(*       + eapply (e m ∘ (IHn n (down_arrow_nat H)) ∘ p n). *)
(*   Defined. *)

(*   Lemma Tower_fmap_proper : *)
(*     ∀ (A B : NatCat) (a₁ a₂ : A [~>] B), *)
(*     a₁ ≡ a₂ → *)
(*     Tower_fmap a₁ ≡ Tower_fmap a₂. *)
(*   Proof. *)
(*     intros A B; revert A. *)
(*     induction B as [| B IH]; intros A a₁ a₂ H. *)
(*     - destruct A as [| A]. *)
(*       + intros; reflexivity. *)
(*       + exfalso. *)
(*         inversion a₁. *)
(*     - destruct A as [| A]; simpl; intros. *)
(*       + reflexivity. *)
(*       + apply (setoid_arr_eq _ _ ((η e B) X)). *)
(*         rewrite H. *)
(*         reflexivity. *)
(*   Qed. *)

(*   Lemma Tower_fmap_id {n : NatCat} *)
(*     : @Tower_fmap n n ı ≡ ı. *)
(*   Proof. *)
(*     induction n as [| n IH]. *)
(*     - simpl. *)
(*       by intros X a. *)
(*     - simpl. *)
(*       assert ((down_arrow_nat ı) = ı) as ->. *)
(*       { apply proof_irrel. } *)
(*       intros X a. *)
(*       assert ((e n ∘ Tower_fmap ı ∘ p n) X a *)
(*                 ≡ (e n ∘ p n) X a) as ->. *)
(*       { *)
(*         apply (@setoid_arr_eq _ _ ((η e n) X) *)
(*                  ((η Tower_fmap ı) X ((η p n) X a)) *)
(*                  ((η p n) X a)). *)
(*         apply IH. *)
(*       } *)
(*       admit. *)
(*   Admitted. *)

(* End RDE2. *)

(* Module RDE1. *)
(*   Local Open Scope setoid_scope. *)
(*   Local Open Scope cat_scope. *)
(*   Local Open Scope functor_scope. *)

(*   (* (* (* 🤡 unfolding control 🤡 *) *) *) *)
(*   (* Opaque has_limits. *) *)
(*   Opaque has_terminal. *)
(*   (* Opaque has_exp. *) *)
(*   (* Opaque has_binary_products. *) *)
(*   (* Opaque π₁. *) *)
(*   (* Opaque π₂. *) *)
(*   (* Opaque Uncurry. *) *)
(*   (* Opaque Curry. *) *)
(*   (* Opaque ArrBinProd. *) *)
(*   (* Opaque ArrBinUnrec. *) *)
(*   (* Opaque Later. *) *)
(*   (* Opaque arrow_comp. *) *)
(*   (* Opaque arrow_id. *) *)
(*   (* (* (* 🤡🤡🤡 *) *) *) *)

(*   Record RDE_solution (F : tree [⇒] tree) : Type := *)
(*     { *)
(*       solution :> tree; *)
(*       solution_correct : solution ≃ (F solution); *)
(*       solution_unique : ∀ x : tree, x ≃ (F x) → solution ≃ x; *)
(*     }. *)

(*   Context (F : tree [⇒] tree). *)
(*   Context (base : 𝟙 @ tree [~>] F (𝟙 @ tree)). *)
(*   Context (Fs : strong F). *)
(*   Context (FS : Strong F). *)
(*   Context (Fc : @locally_contractive F Fs). *)

(*   Fixpoint Tower (n : NatCat) : tree := *)
(*     match n with *)
(*     | 0 => F (𝟙 @ tree) *)
(*     | S n' => F (Tower n') *)
(*     end. *)

(*   Program Definition st' *)
(*     : F (𝟙 @ tree)  [~>] F (F (𝟙 @ tree)) *)
(*     := (eval ∘ ⟨(@strength F FS (𝟙 @ tree) (F (𝟙 @ tree)) ∘ (@pick tree _ _ _ (F (𝟙 @ tree)))) ×ₐ ı⟩ ∘ δₐ). *)

(*   Fixpoint Tower_e (n : NatCat) : Tower n [~>] Tower (S n). *)
(*   Proof. *)
(*     destruct n as [| n]. *)
(*     - apply (st'). *)
(*     - apply (functor.fmap F (Tower_e n)). *)
(*   Defined. *)

(*   Fixpoint Tower_p (n : NatCat) : Tower (S n) [~>] Tower n. *)
(*   Proof. *)
(*     destruct n as [| n]. *)
(*     - apply (functor.fmap F (! @ tree)). *)
(*     - apply (functor.fmap F (Tower_p n)). *)
(*   Defined. *)

(*   Program Definition Tower_fmap {n m : NatCat} (H : n [~>] m) *)
(*     : Tower n [~>] Tower m. *)
(*   Proof. *)
(*     revert n H. *)
(*     induction m as [| m IHn]; intros n H. *)
(*     - destruct n as [| n]. *)
(*       + apply ı. *)
(*       + exfalso. *)
(*         inversion H. *)
(*     - destruct n as [| n]. *)
(*       + apply (Tower_e m ∘ IHn 0 cover_arrow_nat). *)
(*       + eapply (Tower_e m ∘ (IHn n (down_arrow_nat H)) ∘ Tower_p n). *)
(*   Defined. *)

(*   Program Definition Tower_fmap_inv {n m : NatCat} (H : m [~>] n) *)
(*     : Tower n [~>] Tower m. *)
(*   Proof. *)
(*     revert m H. *)
(*     induction n as [| n IHn]; intros m H. *)
(*     - destruct m as [| m]. *)
(*       + apply ı. *)
(*       + exfalso. *)
(*         inversion H. *)
(*     - destruct m as [| m]. *)
(*       + apply (IHn 0 cover_arrow_nat ∘ Tower_p n). *)
(*       + eapply (Tower_e m ∘ (IHn m (down_arrow_nat H)) ∘ Tower_p n). *)
(*   Defined. *)

(*   Lemma Tower_fmap_proper : *)
(*     ∀ (A B : NatCat) (a₁ a₂ : A [~>] B), *)
(*     a₁ ≡ a₂ → *)
(*     Tower_fmap a₁ ≡ Tower_fmap a₂. *)
(*   Proof. *)
(*     intros A B; revert A. *)
(*     induction B as [| B IH]; intros A a₁ a₂ H. *)
(*     - destruct A as [| A]. *)
(*       + intros; reflexivity. *)
(*       + exfalso. *)
(*         inversion a₁. *)
(*     - destruct A as [| A]; simpl; intros. *)
(*       + reflexivity. *)
(*       + apply (setoid_arr_eq _ _ ((η Tower_e B) X)). *)
(*         rewrite H. *)
(*         reflexivity. *)
(*   Qed. *)

(*   Opaque has_terminal. *)

(*   Lemma Tower_pe {n : NatCat} *)
(*     : Tower_e n ∘ Tower_p n ≡ ı *)
(*   with Tower_ep {n : NatCat} *)
(*     : Tower_p n ∘ Tower_e n ≡ ı. *)
(*   Proof. *)
(*     { *)
(*       destruct n as [| n]; intros X a. *)
(*       - unfold Tower_p, Tower_e. *)
(*         simpl. *)
(*         (* pose proof (projT2 (Fs (𝟙 @ tree) (F (𝟙 @ tree)))) as H. *) *)
(*         (* simpl in H. *) *)
(*         epose proof (@strength_decomp F FS (𝟙 @ tree) (F (𝟙 @ tree))). *)
(*         simpl in H. *)

(*         admit. *)
(*       - simpl. *)
(*         rewrite <-(@fmap_comp _ _ F _ _ _ (Tower_e n) (Tower_p n) X a). *)
(*         pose proof (Tower_pe n) as H. *)
(*         rewrite (@setoid_arr_eq _ _ (functor.fmap F) _ _ H X a); clear H. *)
(*         simpl in a. *)
(*         rewrite (@fmap_id _ _ F (F (Tower n)) X a). *)
(*         done. *)
(*     } *)
(*     { *)
(*       destruct n as [| n]; intros X a. *)
(*       - unfold Tower_p, Tower_e. *)
(*         simpl. *)
(*         pose proof (projT2 (Fs (𝟙 @ tree) (F (𝟙 @ tree)))) as H. *)
(*         simpl in H. *)
(*         admit. *)
(*       - simpl. *)
(*         rewrite <-(@fmap_comp _ _ F _ _ _ (Tower_p n) (Tower_e n) X a). *)
(*         pose proof (Tower_ep n) as H. *)
(*         rewrite (@setoid_arr_eq _ _ (functor.fmap F) _ _ H X a); clear H. *)
(*         simpl in a. *)
(*         rewrite (@fmap_id _ _ F (Tower n) X a). *)
(*         done. *)
(*     } *)
(*   Admitted. *)

(*   Lemma Tower_fmap_id {n : NatCat} *)
(*     : @Tower_fmap n n ı ≡ ı. *)
(*   Proof. *)
(*     induction n as [| n IH]. *)
(*     - simpl. *)
(*       by intros X a. *)
(*     - simpl. *)
(*       assert ((down_arrow_nat ı) = ı) as ->. *)
(*       { apply proof_irrel. } *)
(*       intros X a. *)
(*       assert ((Tower_e n ∘ Tower_fmap ı ∘ Tower_p n) X a *)
(*                 ≡ (Tower_e n ∘ Tower_p n) X a) as ->. *)
(*       { *)
(*         apply (@setoid_arr_eq _ _ ((η Tower_e n) X) *)
(*                  ((η Tower_fmap ı) X ((η Tower_p n) X a)) *)
(*                  ((η Tower_p n) X a)). *)
(*         apply IH. *)
(*       } *)
(*       apply Tower_pe. *)
(*   Qed. *)

(*   Lemma Tower_fmap_comp {n m p : NatCat} *)
(*     (f : n [~>] m) (g : m [~>] p) : *)
(*     Tower_fmap (g ∘ f) ≡ Tower_fmap g ∘ Tower_fmap f. *)
(*   Proof. *)
(*     revert n p f g. *)
(*     induction m as [| m IH]; intros n p f g. *)
(*     - destruct n as [| n]. *)
(*       + intros X a; simpl. *)
(*         assert (f = ı) as ->. *)
(*         { apply proof_irrel. } *)
(*         pose proof (@arrow_comp_id_r NatCat 0 p g) as J. *)
(*         simpl in J. *)
(*         simpl. *)
(*         rewrite J. *)
(*         reflexivity. *)
(*       + exfalso. *)
(*         inversion f. *)
(*     - destruct p as [| p]. *)
(*       + exfalso. *)
(*         inversion g. *)
(*       + intros X a. *)
(*         destruct n as [| n]; simpl. *)
(*         * apply (setoid_arr_eq _ _ ((η Tower_e p) X)). *)
(*           pose proof (IH 0 p cover_arrow_nat (down_arrow_nat g) X a) as J. *)
(*           simpl in J. *)
(*           assert (cover_arrow_nat *)
(*               = (Nat.le_trans 0 m p (le_0_n m) (le_S_n m p g))) as ->. *)
(*           { apply proof_irrel. } *)
(*           rewrite J; clear J. *)
(*           apply (setoid_arr_eq _ _ ((η Tower_fmap (le_S_n m p g)) X)). *)
(*           rewrite (@Tower_ep m X ((η Tower_fmap (le_0_n m)) X a)). *)
(*           simpl. *)
(*           reflexivity. *)
(*         * apply (setoid_arr_eq _ _ ((η Tower_e p) X)). *)
(*           Transparent arrow_comp. *)
(*           simpl. *)
(*           assert ((down_arrow_nat (Nat.le_trans (S n) (S m) (S p) f g)) *)
(*                   = (Nat.le_trans n m p (le_S_n n m f) (le_S_n m p g))) as ->. *)
(*           { apply proof_irrel. } *)
(*           rewrite (IH n p (le_S_n n m f) (le_S_n m p g) X ((η Tower_p n) X a)). *)
(*           simpl. *)
(*           apply (setoid_arr_eq _ _ ((η Tower_fmap (le_S_n m p g)) X)). *)
(*           rewrite (@Tower_ep m X ((η Tower_fmap (le_S_n n m f)) X ((η Tower_p n) X a))). *)
(*           simpl. *)
(*           reflexivity. *)
(*           Opaque arrow_comp. *)
(*   Qed. *)

(*   Program Definition TowerF : NatCat [⇒] tree := *)
(*     {| *)
(*       FO X := Tower X; *)
(*       functor.fmap A B := λₛ f, Tower_fmap f; *)
(*       fmap_id A := Tower_fmap_id; *)
(*     |}. *)
(*   Next Obligation. *)
(*     apply Tower_fmap_proper. *)
(*   Qed. *)
(*   Next Obligation. *)
(*     intros; simpl. *)
(*     apply Tower_fmap_comp. *)
(*   Qed. *)

(*   Definition F_solution : tree := lim TowerF @ tree. *)

(*   Program Definition overapprox_cone : Cone TowerF := *)
(*     {| *)
(*       cone_obj := F (lim TowerF @ tree); *)
(*       cone_nat := λₙ x, *)
(*         nat_rect *)
(*           (λ x' : NatCat, (Δ F (lim TowerF @ tree)) x' [~>] TowerF x') *)
(*           (base ∘ ! @ tree) *)
(*           (λ (x' : NatCat) (IX : (Δ F (lim TowerF @ tree)) x' [~>] TowerF x'), *)
(*             (Tower_e x') ∘ IX) *)
(*           x; *)
(*     |}. *)
(*   Next Obligation. *)
(*     intros X Y; revert X. *)
(*     induction Y as [| Y IY]; intros X f. *)
(*     - destruct X as [| X]. *)
(*       + simpl; intros; reflexivity. *)
(*       + exfalso. *)
(*         inversion f. *)
(*     - destruct X as [| X]. *)
(*       + simpl; intros X a. *)
(*         apply (setoid_arr_eq _ _ ((η Tower_e Y) X)). *)
(*         rewrite (IY 0 (le_0_n _) X a). *)
(*         simpl. *)
(*         reflexivity. *)
(*       + simpl; intros Z a. *)
(*         apply (setoid_arr_eq _ _ ((η Tower_e Y) Z)). *)
(*         rewrite (IY X (le_S_n _ _ f) Z a). *)
(*         simpl. *)
(*         apply (setoid_arr_eq _ _ ((η Tower_fmap (le_S_n X Y f)) Z)). *)
(*         match goal with *)
(*         | |- context G [?b ≡ _] => set (c := b) *)
(*         end. *)
(*         rewrite <-(@Tower_ep X Z c). *)
(*         simpl. *)
(*         reflexivity. *)
(*   Qed. *)

(*   Program Definition underapprox_cone (x : NatCat) : Cone TowerF := *)
(*     {| *)
(*       cone_obj := Tower x; *)
(*       cone_nat := λₙ x, _; *)
(*     |}. *)
(*   Next Obligation. *)
(*     intros x y. *)
(*     simpl. *)
(*     destruct (decide (x <= y)) as [l | r]. *)
(*     - apply Tower_fmap. *)
(*       apply l. *)
(*     - assert (r' : y [~>] x). *)
(*       { simpl. apply Nat.lt_le_incl. apply not_le. apply r. } *)
(*       apply Tower_fmap_inv. *)
(*       apply r'. *)
(*   Defined. *)
(*   Next Obligation. *)
(*     intros; simpl. *)
(*     unfold underapprox_cone_obligation_1. *)
(*     destruct (decide (x <= Y)) as [l | r]; *)
(*       destruct (decide (x <= X)) as [l' | r']. *)
(*     - intros; simpl. *)
(*       simpl in f. *)
(*       Transparent arrow_comp. *)
(*       simpl. *)
(*       admit. *)
(*     - admit. *)
(*     - admit. *)
(*     - admit. *)
(*   Admitted. *)

(*   Transparent has_limits. *)

(*   Program Definition solution' : Limit TowerF := PSh_hasLimits TowerF. *)

(*   Program Definition F_iso1 : lim TowerF @ tree [~>] F (lim TowerF @ tree) *)
(*     := λₙ x, _. *)
(*   Next Obligation. *)
(*     intros x. *)
(*     etransitivity. *)
(*     - apply ((cone_nat (terminal_obj (limit_obj (PSh_hasLimits TowerF)))) x). *)
(*     - pose proof ((functor.fmap F (cone_arr (projT1 *)
(*                                                (@terminal_proj _ *)
(*                                                   (limit_obj (PSh_hasLimits TowerF)) (underapprox_cone x)))))). *)
(*       pose proof (Tower_e x x). *)
(*       simpl Tower in X0. *)
(*       simpl in X. *)
(*       apply (X x ∘ X0). *)
(*   Defined. *)
(*   Next Obligation. *)
(*     intros; simpl. *)
(*     intros; simpl. *)
(*     unfold F_iso1_obligation_1. *)
(*     simpl. *)
(*   Admitted. *)

(*   Program Definition F_iso2 : F (lim TowerF @ tree) [~>] lim TowerF @ tree *)
(*     := (cone_arr (projT1 *)
(*                     (@terminal_proj _ *)
(*                        (limit_obj (PSh_hasLimits TowerF)) overapprox_cone))). *)

(*   Program Definition F_solution_correct : ((lim TowerF @ tree) ≃ F (lim TowerF @ tree)) *)
(*     := {| *)
(*       iso1 := F_iso1; *)
(*       iso2 := F_iso2; *)
(*       |}. *)
(*   Next Obligation. *)
(*   Admitted. *)
(*   Next Obligation. *)
(*   Admitted. *)

(*   Program Definition another_cone (s : tree) (H : s ≃ F s) : Cone TowerF := *)
(*     {| *)
(*       cone_obj := s; *)
(*       cone_nat := λₙ x, λₙ y, λₛ z, *)
(*         _; *)
(*     |}. *)
(*   Next Obligation. *)
(*     intros s H. *)
(*     intros x y z. *)
(*     simpl in *. *)
(*     pose proof (iso1 H y z). *)
(*   Admitted. *)
(*   Next Obligation. *)
(*   Admitted. *)
(*   Next Obligation. *)
(*   Admitted. *)
(*   Next Obligation. *)
(*   Admitted. *)

(*   Program Definition another_cone_terminal (s : tree) (H : s ≃ F s) *)
(*     : Terminal (ConeCat TowerF) := *)
(*     {| *)
(*       terminal_obj := another_cone s H; *)
(*     |}. *)
(*   Next Obligation. *)
(*     intros. *)
(*     unshelve econstructor. *)
(*     - simpl in *. *)
(*       admit. *)
(*     - admit. *)
(*   Admitted. *)

(*   Program Definition another_cone_limit (s : tree) (H : s ≃ F s) *)
(*     : Limit TowerF := {| limit_obj := another_cone_terminal s H; |}. *)

(*   Lemma F_solution_unique : (∀ x : tree, x ≃ F x → (lim TowerF @ tree) ≃ x). *)
(*   Proof. *)
(*     intros x H. *)
(*     pose proof (LimitUnique TowerF solution' (another_cone_limit x H)) as J. *)
(*     simpl in J. *)
(*     refine {| *)
(*         iso1 := (cone_arr (iso1 J)); *)
(*         iso2 := (cone_arr (iso2 J)); *)
(*         iso12 := (iso12 J); *)
(*         iso21 := (iso21 J); *)
(*       |}. *)
(*   Qed. *)

(*   Program Definition F_solved : RDE_solution F := *)
(*     {| *)
(*       solution := lim TowerF @ tree; *)
(*       solution_correct := F_solution_correct; *)
(*       solution_unique := F_solution_unique *)
(*     |}. *)

(* End RDE1. *)
