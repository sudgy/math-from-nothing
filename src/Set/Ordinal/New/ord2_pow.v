Require Import init.

Require Export ord2_mult.
Require Import set_induction.

Open Scope ord_scope.

Definition ord_zero {A : ord_type} (x : A) : A :=
    ex_val (well_ordered all (ex_intro _ x true)).

Theorem ord_zero_le {A : ord_type} : ∀ x y : A, ord_zero x ≤ y.
Proof.
    intros x y.
    unfold ord_zero.
    rewrite_ex_val z [C0 z_least]; clear C0.
    apply z_least.
    exact true.
Qed.

Theorem ord_zero_eq {A : ord_type} : ∀ x y : A, ord_zero x = ord_zero y.
Proof.
    intros x y.
    apply antisym; apply ord_zero_le.
Qed.

Theorem ord_zero_iso {A B : ord_type} :
    ∀ f : ord_iso A B, ∀ x, f (ord_zero x) = ord_zero (f x).
Proof.
    intros f x.
    apply antisym.
    -   rewrite <- (bij_inv_eq2 f).
        apply homo_le.
        apply ord_zero_le.
    -   apply ord_zero_le.
Qed.

Definition ord_fin_support {A B : ord_type} (f : A → B) :=
    simple_finite (set_type (λ x, f x ≠ ord_zero (f x))).

Record ord_pow_type (A B : ord_type) := make_ord_pow {
    ord_pow_f :> B → A;
    ord_pow_fin : ord_fin_support ord_pow_f;
}.

Arguments make_ord_pow {A B}.
Arguments ord_pow_f {A B}.
Arguments ord_pow_fin {A B}.

Theorem ord_pow_eq : ∀ {A B : ord_type} {C D : ord_pow_type A B},
    (∀ x, C x = D x) → C = D.
Proof.
    intros A B [Cf C_fin] [Df D_fin] eq.
    cbn in *.
    apply functional_ext in eq.
    subst.
    rewrite (proof_irrelevance C_fin D_fin).
    reflexivity.
Qed.

Theorem eq_ord_pow : ∀ {A B : ord_type} {C D : ord_pow_type A B},
    C = D → ∀ x, C x = D x.
Proof.
    intros A B C D eq.
    subst.
    reflexivity.
Qed.

Definition ord_pow_lt {A B : ord_type} (C D : ord_pow_type A B) :=
    ∃ x, C x < D x ∧ ∀ y, x < y → C y = D y.

Global Instance ord_pow_order A B : Order (ord_pow_type A B) := {
    le C D := C = D ∨ ord_pow_lt C D
}.

Lemma ord_pow_lt_simpl {A B} (C D : ord_pow_type A B) : C < D ↔ ord_pow_lt C D.
Proof.
    split; intros ltq.
    -   destruct ltq as [leq neq].
        unfold le in leq; cbn in leq.
        destruct leq as [eq|leq].
        +   contradiction.
        +   exact leq.
    -   split.
        +   right.
            exact ltq.
        +   intros contr.
            subst D.
            destruct ltq as [x [ltq H]].
            contradiction (irrefl _ ltq).
Qed.

Global Instance ord_pow_antisym A B : Antisymmetric (U := ord_pow_type A B) le.
Proof.
    split.
    intros f g fg gf.
    apply ord_pow_eq.
    intros x.
    destruct fg as [eq|fg]; [>subst; reflexivity|].
    destruct gf as [eq|gf]; [>subst; reflexivity|].
    destruct fg as [a [a_ltq a_eq]].
    destruct gf as [b [b_ltq b_eq]].
    destruct (trichotomy a b) as [[ltq|eq]|ltq].
    -   specialize (a_eq _ ltq).
        rewrite a_eq in b_ltq.
        contradiction (irrefl _ b_ltq).
    -   subst.
        contradiction (irrefl _ (trans a_ltq b_ltq)).
    -   specialize (b_eq _ ltq).
        rewrite b_eq in a_ltq.
        contradiction (irrefl _ a_ltq).
Qed.

Lemma ord_pow_max_ex {A B} :
    ∀ f : ord_pow_type A B, (∃ x, f x ≠ ord_zero (f x)) →
    ∃ x, f x ≠ ord_zero (f x) ∧ ∀ y, x < y → f y = ord_zero (f y).
Proof.
    intros f [x x_neq].
    pose proof (simple_finite_max (ord_pow_fin f) [x|x_neq]) as [m m_max].
    exists [m|].
    split; [>exact [|m]|].
    intros y y_gt.
    classic_contradiction neq.
    specialize (m_max [y|neq]).
    unfold le in m_max; cbn in m_max.
    contradiction (irrefl _ (le_lt_trans m_max y_gt)).
Qed.

Definition ord_pow_max {A B}
    (f : ord_pow_type A B) (e : ∃ x, f x ≠ ord_zero (f x))
    := ex_val (ord_pow_max_ex f e).

Lemma ord_pow_max_nz : ∀ {A B} (f : ord_pow_type A B) e,
    f (ord_pow_max f e) ≠ ord_zero (f (ord_pow_max f e)).
Proof.
    intros A B f e.
    unfold ord_pow_max.
    apply (ex_proof (ord_pow_max_ex f e)).
Qed.

Lemma ord_pow_max_gt : ∀ {A B} (f : ord_pow_type A B) e,
    ∀ y, ord_pow_max f e < y → f y = ord_zero (f y).
Proof.
    intros A B f e.
    unfold ord_pow_max.
    apply (ex_proof (ord_pow_max_ex f e)).
Qed.

Module OrdPowWo.
Section OrdPowWo.

Context (A B : ord_type).
Context (S : ord_pow_type A B → Prop) e (Se : S e).

Lemma zero_least : ∀ z, S z → (∀ x, z x = ord_zero (z x)) → is_least le S z.
Proof.
    intros z Sz z_zero.
    split; [>exact Sz|].
    intros f Sf.
    unfold le; cbn.
    classic_case (z = f) as [eq|neq]; [>left; exact eq|].
    right.
    unfold ord_pow_lt.
    assert (∃ x, f x ≠ ord_zero (f x)) as nz_ex.
    {
        classic_contradiction contr.
        rewrite not_ex in contr.
        apply neq.
        apply ord_pow_eq.
        intros x.
        rewrite (z_zero x).
        specialize (contr x).
        rewrite not_not in contr.
        rewrite contr.
        apply ord_zero_eq.
    }
    exists (ord_pow_max _ nz_ex).
    split.
    -   rewrite z_zero.
        split; [>apply ord_zero_le|].
        symmetry.
        rewrite (ord_zero_eq (z _) (f (ord_pow_max f nz_ex))).
        apply ord_pow_max_nz.
    -   intros y ltq.
        symmetry.
        rewrite z_zero.
        rewrite (ord_zero_eq (z y) (f y)).
        exact (ord_pow_max_gt f nz_ex _ ltq).
Qed.

Section NotZero.

Context (z_nex : ¬(∃ z, S z ∧ ∀ x, z x = ord_zero (z x))).
Context (β : ord) (β_eq : β = to_ord B).
Context (IHβ : ∀ γ, γ < β → ∀ B, γ = to_ord B
        → ∀ (S : ord_pow_type A B → Prop), (∃ e, S e) → ∃ m, is_least le S m).

Lemma nz_ex : ∀ f, S f → ∃ x, f x ≠ ord_zero (f x).
Proof.
    intros f Sf.
    rewrite not_ex in z_nex.
    specialize (z_nex f).
    rewrite not_and_impl in z_nex.
    specialize (z_nex Sf).
    rewrite not_all in z_nex.
    exact z_nex.
Qed.

Definition get_max f (H : S f) := ord_pow_max _ (nz_ex f H).
Definition is_max b := ∃ f H, get_max f H = b.

Lemma b_ex : ∃ b, is_max b.
Proof.
    exists (get_max e Se).
    exists e, Se.
    reflexivity.
Qed.

Definition b := ex_val (well_ordered is_max b_ex).
Lemma b_is_max : is_max b.
Proof.
    apply (ex_proof (well_ordered is_max b_ex)).
Qed.
Lemma b_least_max : is_least le is_max b.
Proof.
    apply (ex_proof (well_ordered is_max b_ex)).
Qed.

Definition b_aligned f := S f ∧ ∀ a, b < a → f a = ord_zero (f a).
Lemma b_aligned_S : ∀ f, b_aligned f → S f.
Proof.
    intros f f_align.
    apply f_align.
Qed.
Lemma b_aligned_zero : ∀ f, b_aligned f → ∀ a, b < a → f a = ord_zero (f a).
Proof.
    intros f f_align.
    apply f_align.
Qed.

Definition is_max_value a := ∃ f, b_aligned f ∧ f b = a.

Lemma a_ex : ∃ a, is_max_value a.
Proof.
    destruct b_is_max as [f [Sg g_eq]].
    exists (f b).
    exists f.
    split; [>|reflexivity].
    unfold b_aligned.
    split; [>exact Sg|].
    intros a ltq.
    rewrite <- g_eq in ltq.
    apply ord_pow_max_gt in ltq.
    exact ltq.
Qed.

Definition a := ex_val (well_ordered is_max_value a_ex).
Lemma a_is_max_value : is_max_value a.
Proof.
    apply (ex_proof (well_ordered is_max_value a_ex)).
Qed.
Lemma a_least_max_value : is_least le is_max_value a.
Proof.
    apply (ex_proof (well_ordered is_max_value a_ex)).
Qed.

Definition ab_aligned f := b_aligned f ∧ f b = a.
Lemma ab_b_aligned_S : ∀ f, ab_aligned f → b_aligned f.
Proof.
    intros f f_align.
    apply f_align.
Qed.
Lemma ab_aligned_S : ∀ f, ab_aligned f → S f.
Proof.
    intros f f_align.
    apply f_align.
Qed.
Lemma ab_aligned_zero : ∀ f, ab_aligned f → ∀ a, b < a → f a = ord_zero (f a).
Proof.
    intros f f_align.
    apply f_align.
Qed.
Lemma ab_aligned_eq : ∀ f, ab_aligned f → f b = a.
Proof.
    intros f f_align.
    apply f_align.
Qed.

Lemma b_aligned_lt : ∀ f g, S g → b_aligned f → ¬b_aligned g → f < g.
Proof.
    intros f g Sg f_align g_align.
    rewrite ord_pow_lt_simpl.
    unfold b_aligned in g_align.
    rewrite not_and_impl in g_align.
    specialize (g_align Sg).
    rewrite not_all in g_align.
    destruct g_align as [x xH].
    rewrite not_impl in xH.
    destruct xH as [x_gt x_neq].
    pose (gm := ord_pow_max _ (ex_intro _ x x_neq)).
    exists gm.
    assert (x ≤ gm) as xgm.
    {
        classic_contradiction ltq.
        rewrite nle_lt in ltq.
        apply ord_pow_max_gt in ltq.
        contradiction.
    }
    split.
    -   assert (f gm = ord_zero (f gm)) as fgm.
        {
            apply f_align.
            exact (lt_le_trans x_gt xgm).
        }
        rewrite fgm.
        split; [>apply ord_zero_le|].
        rewrite (ord_zero_eq (f gm) (g gm)).
        symmetry; apply ord_pow_max_nz.
    -   intros y y_gt.
        pose proof (trans x_gt (le_lt_trans xgm y_gt)) as yb.
        rewrite (b_aligned_zero _ f_align) by exact yb.
        apply ord_pow_max_gt in y_gt.
        rewrite y_gt.
        apply ord_zero_eq.
Qed.

Lemma ab_aligned_lt : ∀ f g, S g → ab_aligned f → ¬ab_aligned g → f < g.
    intros f g Sg f_align g_align.
    unfold ab_aligned in g_align.
    rewrite not_and in g_align.
    classic_case (b_aligned g) as [g_align'|g_align'].
    2: exact (b_aligned_lt f g Sg (land f_align) g_align').
    rewrite ord_pow_lt_simpl.
    destruct g_align as [g_align|neq].
    1: contradiction.
    exists b.
    split.
    -   rewrite ab_aligned_eq by exact f_align.
        rewrite neq_sym in neq.
        split; [>|exact neq].
        apply a_least_max_value.
        unfold is_max_value.
        exists g.
        split; [>exact g_align'|reflexivity].
    -   intros y ltq.
        rewrite (ab_aligned_zero _ f_align) by exact ltq.
        rewrite (b_aligned_zero _ g_align') by exact ltq.
        apply ord_zero_eq.
Qed.

Definition restrict_base (f : ord_pow_type A B)
    (x : sub_ord_type (initial_segment b)) := f [x|].

Lemma restrict_finite : ∀ f, ord_fin_support (restrict_base f).
Proof.
    intros f.
    apply (simple_finite_trans _ _ (ord_pow_fin f)).
    unfold restrict_base.
    assert (∀ x : set_type (λ x : sub_ord_type (initial_segment b),
        f [x|] ≠ ord_zero (f [x|])), f [[x|]|] ≠ ord_zero (f [[x|]|]))
        as x_in.
    {
        intros [[x x_lt] x_neq].
        cbn in *.
        exact x_neq.
    }
    exists (λ x, [[[x|]|] | x_in x]).
    split; cbn.
    intros [[x]] [[y]] eq; cbn in *.
    do 2 apply set_type_eq2.
    apply set_type_eq in eq; cbn in eq.
    exact eq.
Qed.

Definition restrict f := make_ord_pow (restrict_base f) (restrict_finite f).

Definition S' (f : ord_pow_type A (sub_ord_type (initial_segment b)))
    := ∃ f', ab_aligned f' ∧ restrict f' = f.

Lemma restrict_inj : ∀ f g, ab_aligned f → ab_aligned g →
    restrict f = restrict g → f = g.
Proof.
    intros f g f_align g_align eq.
    apply ord_pow_eq.
    intros x.
    destruct (trichotomy x b) as [[ltq|eq']|ltq].
    +   assert (restrict f [x|ltq] = restrict g [x|ltq]) as eq'.
        {
            rewrite eq.
            reflexivity.
        }
        unfold restrict in eq'; cbn in eq'.
        unfold restrict_base in eq'.
        exact eq'.
    +   subst x.
        rewrite (rand g_align).
        apply f_align.
    +   rewrite (ab_aligned_zero _ f_align) by exact ltq.
        rewrite (ab_aligned_zero _ g_align) by exact ltq.
        apply ord_zero_eq.
Qed.

Lemma ord_pow_wo_nz : ∃ m, is_least le S m.
Proof.
    specialize (IHβ (to_ord (sub_ord_type (initial_segment b)))).
    prove_parts IHβ.
    {
        rewrite β_eq.
        rewrite ord_lt_simpl.
        exists b.
        apply refl.
    }
    specialize (IHβ _ Logic.eq_refl).
    specialize (IHβ S').
    pose proof a_is_max_value as [e' [e'_aligned e'_ex]].
    prove_parts IHβ.
    {
        exists (restrict e').
        exists e'.
        split; [>|reflexivity].
        split.
        +   exact e'_aligned.
        +   exact e'_ex.
    }
    destruct IHβ as [h' [[h [h_align h'_eq]] h_least]].
    subst h'.
    exists h.
    split; [>apply h_align|].
    intros g Sg.
    classic_case (ab_aligned g) as [g_align|g_not_align].
    2: apply (ab_aligned_lt _ _ Sg h_align g_not_align).
    specialize (h_least (restrict g)).
    prove_parts h_least.
    {
        exists g.
        split; [>exact g_align|reflexivity].
    }
    destruct h_least as [eq|ltq].
    -   left.
        apply restrict_inj; assumption.
    -   right.
        destruct ltq as [[x xb] [x_lt x_gt]].
        unfold initial_segment in xb.
        exists x.
        split.
        +   unfold restrict in x_lt; cbn in x_lt.
            unfold restrict_base in x_lt; cbn in x_lt.
            exact x_lt.
        +   intros y lt.
            destruct (trichotomy y b) as [[ltq|eq]|ltq].
            *   specialize (x_gt [y|ltq]).
                prove_parts x_gt.
                1: apply set_type_lt; exact lt.
                unfold restrict in x_gt; cbn in x_gt.
                unfold restrict_base in x_gt; cbn in x_gt.
                exact x_gt.
            *   subst y.
                rewrite ab_aligned_eq by exact h_align.
                rewrite ab_aligned_eq by exact g_align.
                reflexivity.
            *   rewrite (ab_aligned_zero _ h_align) by exact ltq.
                rewrite (ab_aligned_zero _ g_align) by exact ltq.
                apply ord_zero_eq.
Qed.

End NotZero.
End OrdPowWo.
End OrdPowWo.

Global Instance ord_pow_wo A B : WellOrdered (U := ord_pow_type A B) le.
Proof.
    split.
    remember (to_ord B) as β.
    revert B Heqβ.
    induction β as [β IHβ] using transfinite_induction.
    intros B Heqβ S [e Se].
    classic_case (∃ z, S z ∧ ∀ x, z x = ord_zero (z x)) as [z_ex|z_nex].
    -   destruct z_ex as [z [Sz z_zero]].
        exists z.
        apply OrdPowWo.zero_least; assumption.
    -   exact (OrdPowWo.ord_pow_wo_nz A B S e Se z_nex β Heqβ IHβ).
Qed.

Notation "A ⊙ B" := (make_ord_type _ (ord_pow_order A B) _ _).

Lemma ord_pow_type_zero {A B} (f : A ⊙ B) : ∀ x, ord_zero f x = ord_zero (f x).
Proof.
    intros x.
    classic_contradiction contr.
    pose (zf (b : B) := ord_zero (f x)).
    assert (z_fin : ord_fin_support zf).
    {
        exists 1.
        exists (λ _, [0|nat_one_pos]).
        split.
        intros [a a_neq].
        contradiction a_neq.
        apply ord_zero_eq.
    }
    pose (z := make_ord_pow zf z_fin).
    assert (z < ord_zero f) as ltq.
    {
        apply ord_pow_lt_simpl.
        assert (∃ b, ord_zero f b ≠ ord_zero (ord_zero f b)) as b_ex.
        {
            exists x.
            rewrite (ord_zero_eq (ord_zero f x) (f x)).
            exact contr.
        }
        exists (ord_pow_max (ord_zero f) b_ex).
        split.
        -   split; [>apply (ord_zero_le)|].
            intros eq.
            cbn in eq.
            unfold zf in eq.
            apply (ord_pow_max_nz (ord_zero f) b_ex).
            rewrite <- eq.
            apply ord_zero_eq.
        -   intros y ltq.
            apply ord_pow_max_gt in ltq.
            rewrite ltq.
            apply ord_zero_eq.
    }
    pose proof (ord_zero_le f z) as leq.
    contradiction (irrefl _ (le_lt_trans leq ltq)).
Qed.

Section OrdPowWd.

Context {A B C D} (f : ord_iso A B) (g : ord_iso D C).
Context (h : ord_pow_type A C).
Definition ord_pow_wd_f_base (d : D) := f (h (g d)).

Lemma ord_pow_wd_fin : ord_fin_support ord_pow_wd_f_base.
Proof.
    unfold ord_pow_wd_f_base.
    apply (simple_finite_trans _ _ (ord_pow_fin h)).
    assert (∀ x, f (h (g x)) ≠ ord_zero (f (h (g x))) →
        h (g x) ≠ ord_zero (h (g x))) as nz.
    {
        intros x neq eq.
        rewrite eq in neq at 1.
        rewrite ord_zero_iso in neq.
        contradiction.
    }
    exists (λ x, [g [x|] | nz [x|] [|x]]).
    split.
    intros a b eq.
    rewrite set_type_eq2 in eq.
    apply inj in eq.
    apply set_type_eq.
    exact eq.
Qed.

Definition ord_pow_wd_f := make_ord_pow ord_pow_wd_f_base ord_pow_wd_fin.

End OrdPowWd.

Lemma ord_pow_wd : ∀ A B C D, A ~ B → C ~ D → A ⊙ C ~ B ⊙ D.
Proof.
    intros A B C D [f] g.
    apply sym in g.
    destruct g as [g].
    split.
    exists (ord_pow_wd_f f g).
    -   pose (f' := make_ord_iso _ _
            (bij_inv f) (bij_inv_bij f) (homo_le_inv f)).
        pose (g' := make_ord_iso _ _
            (bij_inv g) (bij_inv_bij g) (homo_le_inv g)).
        apply (inverse_ex_bijective _ (ord_pow_wd_f f' g')).
        split.
        +   intros h.
            apply ord_pow_eq.
            intros x.
            unfold f', g', ord_pow_wd_f, ord_pow_wd_f_base; cbn.
            rewrite bij_inv_eq1.
            apply bij_inv_eq2.
        +   intros h.
            apply ord_pow_eq.
            intros x.
            unfold f', g', ord_pow_wd_f, ord_pow_wd_f_base; cbn.
            rewrite bij_inv_eq2.
            apply bij_inv_eq1.
    -   split.
        intros a b [eq|ltq].
        1: left; subst; apply ord_pow_eq; reflexivity.
        right.
        destruct ltq as [x [x_lt x_gt]].
        exists (bij_inv g x); cbn.
        split.
        +   unfold ord_pow_wd_f_base.
            rewrite bij_inv_eq2.
            apply homo_lt.
            exact x_lt.
        +   intros y y_gt.
            unfold ord_pow_wd_f_base.
            apply f_equal.
            apply x_gt.
            apply (homo_lt (f := g)) in y_gt.
            rewrite bij_inv_eq2 in y_gt.
            exact y_gt.
Qed.

Definition ord_pow := binary_op (binary_self_wd ord_pow_wd).
Infix "^" := ord_pow : ord_scope.

Theorem ord_pow_zero : ∀ α : ord, α ^ 0 = 1.
Proof.
    intros A.
    equiv_get_value A.
    unfold zero, one, ord_pow; equiv_simpl.
    split.
    exists (λ _, Single).
    1: split.
    all: split; cbn.
    -   intros a b eq.
        apply ord_pow_eq; cbn.
        intros x.
        contradiction (empty_false x).
    -   intros y.
        pose (f (x : (make_ord_type empty_type _ _ _))
            := False_rect A (empty_false x)).
        assert (ord_fin_support f) as f_fin.
        {
            cbn in f.
            unfold ord_fin_support; cbn.
            exists 0.
            exists (λ x, False_rect _ (empty_false [x|])).
            split.
            intros [a].
            contradiction (empty_false a).
        }
        exists (make_ord_pow f f_fin).
        apply singleton_type_eq.
    -   intros a b leq.
        apply refl.
Qed.

Theorem zero_ord_pow : ∀ α : ord, 0 ≠ α → 0 ^ α = 0.
Proof.
    intros A A_nz.
    symmetry.
    equiv_get_value A.
    unfold zero at 2, ord_pow; equiv_simpl.
    apply ord_false_0.
    intros f.
    apply A_nz.
    apply ord_false_0.
    intros a.
    contradiction (empty_false (f a)).
Qed.

Theorem ord_pow_one : ∀ α : ord, α ^ 1 = α.
Proof.
    intros A.
    equiv_get_value A.
    unfold one, ord_pow; equiv_simpl.
    split.
    exists (λ f : (A ⊙ make_ord_type singleton_type _ _ _), f Single).
    1: split.
    all: split.
    -   intros a b eq.
        apply ord_pow_eq; cbn.
        intros x.
        rewrite (singleton_type_eq x Single).
        exact eq.
    -   intros y.
        pose (f (_ : make_ord_type singleton_type _ _ _) := y).
        assert (ord_fin_support f) as f_fin.
        {
            unfold ord_fin_support; cbn.
            exists 1.
            exists (λ _, [0|nat_one_pos]).
            split.
            intros a b eq.
            apply set_type_eq.
            apply singleton_type_eq.
        }
        exists (make_ord_pow f f_fin).
        unfold f; cbn.
        reflexivity.
    -   intros f g leq.
        destruct leq as [eq|ltq].
        1: subst; apply refl.
        destruct ltq as [x [ltq fg]].
        rewrite (singleton_type_eq Single x).
        apply ltq.
Qed.

Theorem one_ord_pow : ∀ α : ord, 1 ^ α = 1.
Proof.
    intros A.
    equiv_get_value A.
    unfold one, ord_pow; equiv_simpl.
    split.
    exists (λ _, Single).
    1: split.
    all: split; cbn.
    -   intros f g eq.
        apply ord_pow_eq.
        intros x.
        apply singleton_type_eq.
    -   intros y.
        assert (ord_fin_support (λ x : A,
            (Single : make_ord_type singleton_type _ _ _))) as fin.
        {
            exists 1.
            exists (λ _, [0|nat_one_pos]).
            split.
            intros [a a_neq].
            contradiction (a_neq (singleton_type_eq _ _)).
        }
        exists (make_ord_pow _ fin).
        apply singleton_type_eq.
    -   intros a b leq.
        apply refl.
Qed.

Theorem ord_pow_plus : ∀ α β γ : ord, α ^ (β + γ) = α ^ β * α ^ γ.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold plus, mult, ord_pow; equiv_simpl.
    split.
    pose (fl (f : A ⊙ (B ⊕ C)) (b : B) := f (inl b)).
    pose (fr (f : A ⊙ (B ⊕ C)) (c : C) := f (inr c)).
    assert (fl_fin : ∀ f, ord_fin_support (fl f)).
    {
        intros f.
        apply (simple_finite_trans _ _ (ord_pow_fin f)).
        exists (λ x, [inl [x|] | ([|x] : f _ ≠ ord_zero _)]).
        split.
        intros a b eq.
        rewrite set_type_eq2 in eq.
        apply (inl_eq [a|]) in eq.
        apply set_type_eq.
        exact eq.
    }
    assert (fr_fin : ∀ f, ord_fin_support (fr f)).
    {
        intros f.
        apply (simple_finite_trans _ _ (ord_pow_fin f)).
        exists (λ x, [inr [x|] | ([|x] : f _ ≠ ord_zero _)]).
        split.
        intros a b eq.
        rewrite set_type_eq2 in eq.
        apply (inr_eq [a|]) in eq.
        apply set_type_eq.
        exact eq.
    }
    exists (λ f, (make_ord_pow (fl f) (fl_fin f),
                  make_ord_pow (fr f) (fr_fin f))).
    1: split.
    all: split.
    -   intros f g eq.
        apply prod_split in eq as [eq1' eq2'].
        pose proof (eq_ord_pow eq1') as eq1.
        pose proof (eq_ord_pow eq2') as eq2.
        clear eq1' eq2'.
        cbn in eq1, eq2.
        apply ord_pow_eq.
        intros [b|c].
        +   apply eq1.
        +   apply eq2.
    -   intros g.
        pose (f (x : B ⊕ C) := match x with
            | inl b => fst g b
            | inr c => snd g c
            end).
        assert (f_fin : ord_fin_support f).
        {
            pose proof (ord_pow_fin (fst g)) as gl_fin.
            pose proof (ord_pow_fin (snd g)) as gr_fin.
            pose proof (simple_finite_sum _ _ gl_fin gr_fin) as g_fin.
            apply (simple_finite_trans _ _ g_fin).
            clear gl_fin gr_fin g_fin.
            assert (∀ x, f (inl x) ≠ ord_zero (f (inl x)) →
                fst g x ≠ ord_zero (fst g x)) as in1 by trivial.
            assert (∀ x, f (inr x) ≠ ord_zero (f (inr x)) →
                snd g x ≠ ord_zero (snd g x)) as in2 by trivial.
            exists (λ x, match x with
                | [inl b|H] => inl [b | in1 b H]
                | [inr c|H] => inr [c | in2 c H]
                end).
            split.
            intros [[b1|c1] neq1] [[b2|c2] neq2]; cbn; intros eq.
            -   apply (inl_eq [_|_]) in eq.
                rewrite set_type_eq2 in eq.
                apply set_type_eq2.
                apply f_equal.
                exact eq.
            -   contradiction (inlr_neq eq).
            -   contradiction (inrl_neq eq).
            -   apply (inr_eq [_|_]) in eq.
                rewrite set_type_eq2 in eq.
                apply set_type_eq2.
                apply f_equal.
                exact eq.
        }
        exists (make_ord_pow f f_fin).
        apply prod_combine; cbn.
        all: apply ord_pow_eq; cbn.
        all: reflexivity.
    -   intros f g leq.
        destruct leq as [eq|ltq].
        1: subst g; apply refl.
        destruct ltq as [x [x_lt x_gt]].
        destruct x as [b|c].
        +   right.
            split.
            *   right.
                exists b; cbn.
                split.
                --  exact x_lt.
                --  intros y y_gt.
                    apply x_gt.
                    apply inl_lt.
                    exact y_gt.
            *   apply ord_pow_eq.
                intros x; cbn.
                apply x_gt.
                apply inlr_lt.
        +   left.
            rewrite ord_pow_lt_simpl.
            exists c; cbn.
            split.
            *   exact x_lt.
            *   intros y y_lt.
                apply x_gt.
                apply inr_lt.
                exact y_lt.
Qed.

Theorem ord_pow_pow : ∀ α β γ : ord, (α ^ β) ^ γ = α ^ (β * γ).
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold ord_pow, mult; equiv_simpl.
    split.
    pose (h (f : (A ⊙ B) ⊙ C) (x : B ⊗ C) := f (snd x) (fst x)).
    assert (h_fin : ∀ f, ord_fin_support (h f)).
    {
        intros f.
    }

Theorem ord_pow_gt_one : ∀ α β : ord, 1 < α → 1 < β → 1 < α ^ β.

Theorem ord_pow_lt : ∀ α β γ : ord, 1 < α → β < γ → α ^ β < α ^ γ.
(* Simplify to 1 < α ^ δ *)

Theorem ord_pow_le : ∀ α β γ : ord, 1 ≤ α → β ≤ γ → α ^ β ≤ α ^ γ.
Proof.
(* Should be easy from ord_pow_lt *)

Theorem le_ord_pow : ∀ α β γ : ord, α ≤ β → α ^ γ ≤ β ^ γ.

Theorem eq_ord_pow_eq : ∀ α β γ : ord, 1 < α → α ^ β = α ^ γ → β = γ.
(* Should be easy from ord_pow_lt *)

Close Scope ord_scope.
