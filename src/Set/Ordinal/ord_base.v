Require Import init.

Require Export set_order.
Require Import function.
Require Import set.
Require Import nat.

Declare Scope ord_scope.
Delimit Scope ord_scope with ord.

Record ord_type := make_ord_type {
    ord_U : Type;
    ord_le : ord_U → ord_U → Prop;
    ord_antisym : Antisymmetric ord_le;
    ord_wo : WellOrdered ord_le;
}.

Ltac get_ord_wo A :=
    pose proof (ord_antisym A);
    pose proof (ord_wo A).

Theorem ord_zero_ex A : ord_U A → ∃ z, ∀ x, ord_le A z x.
Proof.
    get_ord_wo A.
    intros a.
    assert (∃ x : ord_U A, all x) as S_ex by (exists a; exact true).
    pose proof (well_ordered all S_ex) as [z [C0 z_min]]; clear C0.
    exists z.
    intros x.
    apply z_min.
    exact true.
Qed.
Definition ord_zero {A} (H : ord_U A) := ex_val (ord_zero_ex A H).
Theorem ord_zero_le {A} {H : ord_U A}: ∀ x, ord_le A (ord_zero H) x.
Proof.
    intros x.
    unfold ord_zero.
    unpack_ex_val z z_ex z_le; rewrite z_ex.
    apply z_le.
Qed.
Theorem ord_zero_eq {A} (H1 H2 : ord_U A) : ord_zero H1 = ord_zero H2.
Proof.
    get_ord_wo A.
    apply antisym; apply ord_zero_le.
Qed.

Theorem ord_zero_iso {A} {B} (H : ord_U A) :
    ∀ f : ord_U A → ord_U B, Bijective f →
    (∀ a b, (ord_le A) a b ↔ (ord_le B) (f a) (f b)) →
    f (ord_zero H) = ord_zero (f H).
Proof.
    intros f f_bij f_iso.
    get_ord_wo B.
    apply antisym; try apply ord_zero_le.
    pose (f' := bij_inv f).
    rewrite <- (inverse_eq2 _ _ (bij_inv_inv _) (ord_zero (f H))).
    rewrite <- f_iso.
    apply ord_zero_le.
Qed.

Definition initial_segment_set (A : ord_type) (x : ord_U A) :=
    λ a, ord_le A a x ∧ a ≠ x.
Definition initial_segment_le (A : ord_type) (x : ord_U A) :=
    λ (a b : set_type (initial_segment_set A x)), ord_le A [a|] [b|].
Lemma initial_segment_antisym : ∀ (A : ord_type) (x : ord_U A),
    Antisymmetric (initial_segment_le A x).
Proof.
    intros A x.
    get_ord_wo A.
    split.
    intros a b ab ba.
    apply set_type_eq.
    apply antisym; assumption.
Qed.
Lemma initial_segment_wo : ∀ (A : ord_type) (x : ord_U A),
    WellOrdered (initial_segment_le A x).
Proof.
    intros A x.
    get_ord_wo A.
    split.
    intros S [y Sy].
    pose (S' (a : ord_U A) := ∃ H : (initial_segment_set A x a), S [_|H]).
    assert (∃ x, S' x) as S'_nempty.
    {
        exists [y|].
        exists [|y].
        destruct y.
        exact Sy.
    }
    pose proof (well_ordered S' S'_nempty) as [m [[Am Sm] m_minimal]].
    exists [_|Am].
    split.
    +   exact Sm.
    +   intros z Sz.
        apply m_minimal.
        exists [|z].
        destruct z; exact Sz.
Qed.
Definition ord_initial_segment (A : ord_type) (x : ord_U A)
    := make_ord_type _ _ (initial_segment_antisym A x) (initial_segment_wo A x).

Theorem ord_iso_le : ∀ (A : ord_type) f, Injective f →
    (∀ a b, (ord_le A) a b ↔ (ord_le A) (f a) (f b)) →
    ∀ x, ord_le A x (f x).
Proof.
    intros A f f_inj f_iso x.
    get_ord_wo A.
    classic_contradiction x_gt.
    pose (S x := ¬ord_le A x (f x)).
    assert (∃ x, S x) as S_nempty.
    {
        exists x.
        unfold S.
        exact x_gt.
    }
    specialize (well_ordered S S_nempty) as [b [Sb b_min]].
    apply Sb.
    apply b_min.
    unfold S.
    rewrite <- f_iso.
    exact Sb.
Qed.

(* begin hide *)
Section OrdEquiv.

Let ord_eq A B := ∃ f, Bijective f ∧
                       ∀ a b, (ord_le A) a b ↔ (ord_le B) (f a) (f b).
Local Infix "~" := ord_eq.

Lemma ord_eq_reflexive : ∀ A, A ~ A.
Proof.
    intros A.
    exists identity.
    split.
    -   exact identity_bijective.
    -   intros a b.
        reflexivity.
Qed.
Instance ord_eq_reflexive_class : Reflexive _ := {
    refl := ord_eq_reflexive
}.

Lemma ord_eq_symmetric : ∀ A B, A ~ B → B ~ A.
Proof.
    intros A B [f [f_bij f_iso]].
    exists (bij_inv f).
    split.
    -   apply bij_inv_bij.
    -   intros a b.
        pose proof (bij_inv_inv f) as inv.
        apply inverse_symmetric in inv.
        split.
        +   intros ab.
            apply f_iso.
            do 2 rewrite (inverse_eq1 _ _ inv).
            exact ab.
        +   intros ab.
            apply f_iso in ab.
            do 2 rewrite (inverse_eq1 _ _ inv) in ab.
            exact ab.
Qed.
Instance ord_eq_symmetric_class : Symmetric _ := {
    sym := ord_eq_symmetric
}.

Lemma ord_eq_transitive : ∀ A B C, A ~ B → B ~ C → A ~ C.
Proof.
    intros A B C [f [f_bij f_iso]] [g [g_bij g_iso]].
    exists (λ x, g (f x)).
    split.
    -   apply bij_comp; assumption.
    -   intros a b.
        rewrite f_iso.
        rewrite g_iso.
        reflexivity.
Qed.
Instance ord_eq_transitive_class : Transitive _ := {
    trans := ord_eq_transitive
}.

End OrdEquiv.
(* end hide *)
Definition ord_equiv := make_equiv _
    ord_eq_reflexive_class ord_eq_symmetric_class ord_eq_transitive_class.
Notation "a ~ b" := (eq_equal ord_equiv a b) : ord_scope.

Notation "'ord'" := (equiv_type ord_equiv).

(* begin hide *)
Open Scope ord_scope.
(* end hide *)
Theorem ord_niso_init : ∀ A x, ¬(A ~ ord_initial_segment A x).
Proof.
    intros A x [f [f_bij f_iso]].
    pose (f' a := [f a|]).
    assert (Injective f') as f'_inj.
    {
        split.
        intros a b eq.
        apply f_bij.
        apply set_type_eq.
        exact eq.
    }
    assert (∀ a b, ord_le A a b ↔ ord_le A (f' a) (f' b)) as f'_iso
        by apply f_iso.
    pose proof (ord_iso_le A f' f'_inj f'_iso x) as leq.
    pose proof [|f x] as [fx_leq fx_neq].
    change (f' x) with [f x|] in leq.
    get_ord_wo A.
    pose proof (antisym fx_leq leq).
    contradiction.
Qed.

Theorem ord_iso_init_eq : ∀ A B C x,
    B ~ ord_initial_segment A x → C ~ ord_initial_segment A x → B ~ C.
Proof.
    intros A B C x [f [f_bij f_iso]] [g [g_bij g_iso]].
    pose (g' := bij_inv g).
    exists (λ x, g' (f x)).
    split.
    -   apply bij_comp; try assumption.
        apply bij_inv_bij.
    -   intros a b.
        rewrite f_iso.
        rewrite g_iso.
        pose proof (bij_inv_inv g) as g_inv.
        do 2 rewrite (inverse_eq2 _ _ g_inv).
        reflexivity.
Qed.

(* begin hide *)
Lemma ord_init_iso_eq1 : ∀ A x y,
    ord_initial_segment A x ~ ord_initial_segment A y → ord_le A y x.
Proof.
    intros A x y eq.
    get_ord_wo A.
    classic_contradiction xy.
    assert (initial_segment_set A y x) as x_in.
    {
        unfold initial_segment_set.
        classic_case (x = y).
        -   subst.
            destruct (connex y y); contradiction.
        -   destruct (connex x y); try contradiction.
            split; assumption.
    }
    assert (ord_initial_segment A x ~ ord_initial_segment (ord_initial_segment A y) [_|x_in]).
    {
        assert (∀ a : set_type (initial_segment_set A x),
                initial_segment_set A y [a|]) as all_in1.
        {
            intros [a a_eq].
            unfold initial_segment_set in *; cbn.
            destruct x_in as [xy_eq xy_neq], a_eq as [ax_eq ax_neq].
            split.
            -   exact (trans ax_eq xy_eq).
            -   intros ay.
                subst.
                contradiction.
        }
        assert (∀ a : set_type (initial_segment_set A x),
            initial_segment_set (ord_initial_segment A y) [x|x_in] [_|all_in1 a])
        as all_in2.
        {
            intros [a a_eq].
            unfold initial_segment_set in *; cbn.
            unfold initial_segment_le; cbn.
            destruct a_eq as [a_leq a_neq].
            split; try exact a_leq.
            intros neq.
            inversion neq.
            contradiction.
        }
        exists (λ x, [_|all_in2 x]); cbn.
        split.
        1: split; split.
        -   intros a b ab.
            apply set_type_eq; inversion ab; reflexivity.
        -   intros [[b b_y] b_x].
            unfold initial_segment_set in b_x.
            cbn in b_x.
            assert (initial_segment_set A x b) as b_x2.
            {
                split; try apply b_x.
                destruct b_x.
                intro contr.
                subst.
                apply H2.
                apply set_type_eq; reflexivity.
            }
            exists [_|b_x2].
            apply set_type_eq.
            do 2 rewrite set_value_simpl.
            apply set_type_eq.
            reflexivity.
        -   intros a b.
            unfold initial_segment_le; cbn.
            reflexivity.
    }
    apply eq_symmetric in eq.
    pose proof (eq_transitive ord_equiv).
    pose proof (trans eq H1) as contr.
    apply ord_niso_init in contr.
    exact contr.
Qed.
(* end hide *)
Theorem ord_init_iso_eq : ∀ A x y,
    ord_initial_segment A x ~ ord_initial_segment A y → x = y.
Proof.
    intros A x y eq.
    get_ord_wo A.
    apply antisym.
    -   apply eq_symmetric in eq.
        apply ord_init_iso_eq1.
        exact eq.
    -   apply ord_init_iso_eq1.
        exact eq.
Qed.

(* begin hide *)
Lemma ord_iso_unique_le : ∀ (A B : ord_type) f g, Bijective f → Bijective g →
    (∀ a b, (ord_le A) a b ↔ (ord_le B) (f a) (f b)) →
    (∀ a b, (ord_le A) a b ↔ (ord_le B) (g a) (g b)) →
    ∀ x, ord_le B (f x) (g x).
Proof.
    intros A B f g f_bij g_bij f_iso g_iso x.
    pose (f' := bij_inv f).
    pose (h x := f' (g x)).
    assert (ord_le A x (h x)) as leq.
    {
        apply ord_iso_le.
        -   split.
            intros a b eq.
            unfold h in eq.
            apply (bij_inv_bij f) in eq.
            apply g_bij in eq.
            exact eq.
        -   intros a b.
            unfold h.
            rewrite (f_iso (f' (g a))).
            do 2 rewrite (inverse_eq2 _ _ (bij_inv_inv f)).
            apply g_iso.
    }
    unfold h in leq.
    apply f_iso in leq.
    rewrite (inverse_eq2 _ _ (bij_inv_inv f)) in leq.
    exact leq.
Qed.
(* end hide *)
Theorem ord_iso_unique : ∀ (A B : ord_type) f g, Bijective f → Bijective g →
    (∀ a b, (ord_le A) a b ↔ (ord_le B) (f a) (f b)) →
    (∀ a b, (ord_le A) a b ↔ (ord_le B) (g a) (g b)) →
    f = g.
Proof.
    intros A B f g f_bij g_bij f_iso g_iso.
    apply functional_ext.
    intros x.
    get_ord_wo B.
    apply antisym; apply ord_iso_unique_le; assumption.
Qed.
Theorem ord_iso_id : ∀ A f, Bijective f →
    (∀ a b, (ord_le A) a b ↔ (ord_le A) (f a) (f b)) →
    f = identity.
Proof.
    intros A f f_bij f_iso.
    apply ord_iso_unique; try assumption.
    -   exact identity_bijective.
    -   reflexivity.
Qed.

Theorem ord_iso_strict :
   ∀ {A B f}, Bijective f →
   (∀ a b : ord_U A, ord_le A a b ↔ ord_le B (f a) (f b)) →
   (∀ a b : ord_U A, strict (ord_le A) a b ↔ strict (ord_le B) (f a) (f b)).
Proof.
    intros A B f f_bij f_iso a b.
    split.
    -   intros ab.
        split.
        +   rewrite <- f_iso.
            apply ab.
        +   intro contr.
            apply f_bij in contr.
            subst.
            destruct ab; contradiction.
    -   intros ab.
        split.
        +   rewrite f_iso.
            apply ab.
        +   intro contr.
            subst.
            destruct ab; contradiction.
Qed.

(* begin hide *)
Close Scope ord_scope.
(* end hide *)
Definition nat_to_ord_type (n : nat) :=
    make_ord_type (set_type (λ m, m < n)) le
    set_type_le_antisym_class set_type_le_wo_class.
Definition nat_to_ord (n : nat) :=
    to_equiv ord_equiv (nat_to_ord_type n).
