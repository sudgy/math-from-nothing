Require Import init.

Require Export ord_base.
Require Import set_function.
Require Import equivalence.
Require Import zorn.
Require Import zorn_function.
Require Import nat.

(* begin hide *)
Section OrdOrder.

Local Open Scope ord_scope.

Let ord_le A B := A ~ B ∨ ∃ x, A ~ (ord_initial_segment B x).
Local Infix "≦" := ord_le.

Lemma ord_le_wd_one : ∀ A B C D, A ~ B → C ~ D → A ≦ C → B ≦ D.
Proof.
    intros A B C D AB CD [AC|[x ACx]].
    -   left.
        apply eq_symmetric in AB.
        pose proof (eq_transitive ord_equiv).
        exact (trans AB (trans AC CD)).
    -   right.
        apply eq_symmetric in AB.
        destruct AB as [f [f_bij f_iso]],
                 CD as [g [g_bij g_iso]],
                ACx as [h [h_bij h_iso]].
        exists (g x); cbn.
        assert (∀ a : ord_U (ord_initial_segment C x),
                initial_segment_set D (g x) (g [a|])) as Cx_Dx.
        {
            intros [a Ca]; cbn.
            unfold initial_segment_set in *.
            split.
            -   apply g_iso.
                apply Ca.
            -   intro contr.
                apply g_bij in contr.
                destruct Ca; contradiction.
        }
        pose (g' x := [_|Cx_Dx x]).
        assert (Bijective g') as g'_bij.
        {
            split; split.
            -   intros a b ab.
                apply set_type_eq.
                apply g_bij.
                unfold g' in ab.
                inversion ab.
                reflexivity.
            -   intros [b bx].
                pose proof (sur g b) as [a a_eq].
                pose proof bx as ax.
                rewrite <- a_eq in ax.
                destruct ax as [ax anx].
                apply g_iso in ax.
                assert (a ≠ x) as anx2 by (intro contr; subst; contradiction).
                exists [a|(make_and ax anx2)].
                apply set_type_eq; cbn.
                exact a_eq.
        }
        exists (λ x, g' (h (f x))).
        split.
        +   do 2 apply bij_comp; try assumption.
            apply identity_bijective.
        +   intros a b.
            split.
            *   intros ab.
                apply g_iso.
                apply h_iso.
                apply f_iso.
                exact ab.
            *   intros ab.
                apply g_iso in ab.
                apply h_iso in ab.
                apply f_iso in ab.
                exact ab.
Qed.
Lemma ord_le_wd : ∀ A B C D, A ~ B → C ~ D → (A ≦ C) = (B ≦ D).
Proof.
    intros A B C D AB CD.
    apply propositional_ext.
    split.
    -   apply ord_le_wd_one; assumption.
    -   pose proof (eq_symmetric ord_equiv) as sym.
        apply ord_le_wd_one; apply sym; assumption.
Qed.

End OrdOrder.

Global Instance ord_order : Order ord := {
    le := binary_op ord_le_wd;
}.

Open Scope ord_scope.
(* end hide *)
Theorem ord_le_lt : ∀ α β, (α ≤ β) = (α = β ∨ α < β).
Proof.
    intros α β.
    classic_case (α = β) as [eq|neq].
    {
        subst.
        apply propositional_ext; split.
        -   intros; left; trivial.
        -   intros H; clear H.
            equiv_get_value β; unfold le; equiv_simpl.
            left; exists identity.
            split; try apply identity_bijective.
            intros a b; reflexivity.
    }
    revert neq.
    equiv_get_value α β.
    unfold strict, le; equiv_simpl.
    intros neq.
    apply propositional_ext; split.
    -   intros [eq|leq]; try contradiction.
        right.
        split; try assumption.
        right.
        exact leq.
    -   intros [eq|[leq req]]; try contradiction; try assumption.
Qed.

Theorem ord_lt_initial : ∀ A B,
    (to_equiv ord_equiv A < to_equiv ord_equiv B) =
    (∃ x, A ~ (ord_initial_segment B x)).
Proof.
    intros A B.
    unfold strict, le; equiv_simpl.
    apply propositional_ext; split.
    -   intros [[eq|leq] neq].
        +   contradiction.
        +   exact leq.
    -   intros leq.
        split.
        +   right; exact leq.
        +   destruct leq as [x [f [f_bij f_iso]]].
            intros [g [g_bij g_iso]].
            pose (g' := bij_inv g).
            pose proof (bij_inv_bij g) as g'_bij.
            pose (h x := f (g' x)).
            apply (ord_niso_init B x).
            exists h.
            split.
            1: split; split.
            *   intros a b eq.
                apply g'_bij.
                apply f_bij.
                exact eq.
            *   intros c.
                pose proof (sur f c) as [b b_eq].
                pose proof (sur (bij_inv g) b) as [a a_eq].
                exists a.
                rewrite <- b_eq, <- a_eq.
                reflexivity.
            *   intros a b.
                pose proof (bij_inv_inv g) as g'_inv.
                rewrite <- (inverse_eq2 _ _ g'_inv a) at 1.
                rewrite <- (inverse_eq2 _ _ g'_inv b) at 1.
                rewrite <- g_iso.
                rewrite f_iso.
                reflexivity.
Qed.

(* begin hide *)
Module OrdConnex.
Section OrdConnex.

Notation "'to_ord' A" := (to_equiv ord_equiv A) (at level 10).

Variables A B : ord_type.
Hypothesis AB : ¬(to_ord A < to_ord B).
Hypothesis BA : ¬(to_ord B < to_ord A).

Record piece := make_piece {
    piece_f : set_function_type (ord_U A) (ord_U B);
    piece_inj : Injective (set_function piece_f);
    piece_iso : ∀ a b, (ord_le A) [a|] [b|] ↔
                (ord_le B) (piece_f⟨a⟩) (piece_f⟨b⟩);
    piece_bot1 : ∀ a b, domain piece_f a → ¬domain piece_f b → ord_le A a b;
    piece_bot2 : ∀ a b, (∃ x, piece_f⟨x⟩ = a) → ¬(∃ x, piece_f⟨x⟩ = b)
                → ord_le B a b;
}.

Definition piece_le f g := func_le (piece_f f) (piece_f g).
Local Instance piece_le_class : Order _ := {
    le := piece_le
}.
Lemma piece_le_refl : ∀ f, f ≤ f.
Proof.
    unfold le; cbn; unfold piece_le; cbn.
    intros f.
    apply refl.
Qed.
Local Instance piece_le_reflexive : Reflexive le := {
    refl := piece_le_refl
}.
Lemma piece_le_antisym : ∀ f g, f ≤ g → g ≤ f → f = g.
Proof.
    unfold le; cbn; unfold piece_le; cbn.
    intros f g fg gf.
    pose proof (antisym fg gf).
    destruct f as [f f_inj f_iso f_bot]; cbn in *.
    destruct g as [g g_inj g_iso g_bot]; cbn in *.
    subst.
    apply f_equal4; apply proof_irrelevance.
Qed.
Local Instance piece_le_antisym_class : Antisymmetric le := {
    antisym := piece_le_antisym
}.
Lemma piece_le_trans : ∀ f g h, f ≤ g → g ≤ h → f ≤ h.
Proof.
    unfold le; cbn; unfold piece_le; cbn.
    intros f g h fg gh.
    exact (trans fg gh).
Qed.
Local Instance piece_le_trans_class : Transitive le := {
    trans := piece_le_trans
}.

Section ZornPiece.

Variable F : piece → Prop.
Hypothesis F_chain : is_chain le F.

Definition F_union_set x := ∃ f, F f ∧ domain (piece_f f) x.
Definition F_union_f (x : set_type (F_union_set)) :=
    piece_f (ex_val [|x])⟨[_|rand (ex_proof [|x])]⟩.

Lemma F_union_inj : Injective F_union_f.
Proof.
    split.
    intros a b ab.
    unfold F_union_f in ab.
    unfold ex_val, ex_proof in ab.
    destruct (ex_to_type [|a]) as [f [Ff fa]]; cbn in *.
    destruct (ex_to_type [|b]) as [g [Fg gb]]; cbn in *.
    destruct (F_chain _ _ Ff Fg) as [fg|gf].
    -   destruct fg as [sub fg].
        rewrite fg in ab; cbn in *.
        apply (piece_inj g) in ab.
        apply set_type_eq.
        inversion ab.
        reflexivity.
    -   destruct gf as [sub gf].
        rewrite gf in ab; cbn in *.
        apply (piece_inj f) in ab.
        apply set_type_eq.
        inversion ab.
        reflexivity.
Qed.

Lemma F_union_iso : ∀ a b, (ord_le A) [a|] [b|] ↔
                (ord_le B) (F_union_f a) (F_union_f b).
Proof.
    intros a b.
    unfold F_union_f, ex_val, ex_proof.
    destruct (ex_to_type [|a]) as [f [Ff fa]]; cbn in *.
    destruct (ex_to_type [|b]) as [g [Fg gb]]; cbn in *.
    destruct (F_chain _ _ Ff Fg) as [fg|gf].
    -   destruct fg as [sub fg].
        rewrite fg; cbn.
        rewrite <- (piece_iso g); cbn.
        reflexivity.
    -   destruct gf as [sub gf].
        rewrite gf; cbn.
        rewrite <- (piece_iso f); cbn.
        reflexivity.
Qed.

Lemma F_union_bot1 : ∀ a b, F_union_set a → ¬F_union_set b → ord_le A a b.
Proof.
    intros a b [f [Ff fa]] nFb.
    apply (piece_bot1 f); try assumption.
    intros fb.
    unfold F_union_set in nFb.
    rewrite not_ex in nFb.
    specialize (nFb f).
    rewrite not_and in nFb.
    destruct nFb; contradiction.
Qed.

Lemma F_union_bot2 : ∀ a b, (∃ x, F_union_f x = a) → ¬(∃ x, F_union_f x = b)
    → ord_le B a b.
Proof.
    intros a b [x xa] nxb.
    unfold F_union_f, ex_val, ex_proof in *.
    destruct (ex_to_type [|x]) as [f [Ff fx]]; cbn in *.
    apply (piece_bot2 f a b).
    -   exists [_|fx].
        rewrite (proof_irrelevance _ fx) in xa.
        exact xa.
    -   intros [y yb].
        apply nxb; clear nxb.
        assert (F_union_set [y|]) as Fy.
        {
            exists f.
            split; try assumption.
            exact [|y].
        }
        exists [_|Fy]; cbn.
        destruct (ex_to_type Fy) as [g [Fg gy]]; cbn in *.
        subst b.
        destruct (F_chain _ _ Ff Fg) as [fg|gf].
        +   destruct fg as [sub fg].
            rewrite fg.
            apply f_equal.
            apply set_type_eq; reflexivity.
        +   destruct gf as [sub gf].
            rewrite gf.
            apply f_equal.
            apply set_type_eq; reflexivity.
Qed.

Definition F_union_func := make_set_function F_union_set F_union_f.

Local Open Scope set_scope.

Lemma zorn_piece : has_upper_bound le F.
Proof.
    exists (make_piece
        F_union_func F_union_inj F_union_iso F_union_bot1 F_union_bot2).
    intros f Ff.
    unfold le; cbn; unfold piece_le; cbn.
    assert (domain (piece_f f) ⊆ domain F_union_func) as sub.
    {
        intros x fx.
        exists f.
        split; assumption.
    }
    exists sub.
    intros x.
    unfold F_union_func, F_union_f; cbn.
    unfold ex_val, ex_proof.
    destruct (ex_to_type (sub [x|] [|x])) as [g [Fg gx]]; cbn.
    destruct (F_chain f g Ff Fg) as [fg|gf].
    -   destruct fg as [sub2 fg].
        rewrite fg.
        apply f_equal.
        apply set_type_eq; reflexivity.
    -   destruct gf as [sub2 gf].
        rewrite gf.
        apply f_equal.
        apply set_type_eq; reflexivity.
Qed.

End ZornPiece.

Definition f := ex_val (zorn piece_le zorn_piece).

Lemma f_max : ∀ g, ¬(f < g).
Proof.
    intros g fg.
    unfold f, ex_val in fg.
    destruct (ex_to_type (zorn piece_le zorn_piece)) as [f f_max].
    cbn in *.
    exact (f_max g fg).
Qed.

Section AllInF.

Variable a' : ord_U A.
Hypothesis not_in' : ¬domain (piece_f f) a'.

Local Open Scope set_scope.

Definition Sa y := ¬domain (piece_f f) y.
Lemma Sa_nempty : ∃ x, Sa x.
Proof.
    exists a'.
    exact not_in'.
Qed.
Lemma a_ex : ∃ a, Sa a ∧ ∀ x, Sa x → ord_le A a x.
Proof.
    get_ord_wo A.
    pose proof (well_ordered Sa Sa_nempty) as [a [a_in a_min]].
    exists a.
    split; assumption.
Qed.
Definition a := ex_val a_ex.
Lemma not_in : ¬domain (piece_f f) a.
Proof.
    unfold a.
    unfold ex_val.
    destruct (ex_to_type a_ex) as [a [Sa a_H]]; cbn.
    exact Sa.
Qed.
Lemma a_min : ∀ x, Sa x → ord_le A a x.
Proof.
    unfold a.
    unfold ex_val.
    destruct (ex_to_type a_ex) as [a [Sa a_H]]; cbn.
    exact a_H.
Qed.

Lemma b_ex_base : ∃ b, ∀ a, piece_f f⟨a⟩ ≠ b.
Proof.
    classic_contradiction contr.
    apply BA.
    rewrite ord_lt_initial.
    pose (S y := ¬domain (piece_f f) y).
    assert (∃ x, S x) as S_nempty by (exists a; exact not_in).
    get_ord_wo A.
    specialize (well_ordered S S_nempty) as [x [Sx x_min]].
    exists x.
    clear AB BA.
    apply ord_eq_symmetric.
    assert (∀ a : ord_U (ord_initial_segment A x), domain (piece_f f) [a|]) as sub.
    {
        intros [a [a_leq a_neq]]; cbn in *.
        pose proof (piece_bot1 f).
        classic_contradiction contr2.
        specialize (x_min _ contr2).
        pose proof (antisym a_leq x_min).
        contradiction.
    }
    pose (f' a := piece_f f⟨[_|sub a]⟩).
    exists f'.
    split.
    1: split; split.
    -   intros a b eq.
        apply (piece_inj f) in eq.
        apply set_type_eq; inversion eq.
        reflexivity.
    -   intros b.
        rewrite not_ex in contr.
        specialize (contr b).
        rewrite not_all in contr.
        destruct contr as [a contr].
        rewrite not_not in contr.
        assert (initial_segment_set A x [a|]) as xa.
        {
            split.
            -   exact (piece_bot1 f [a|] x [|a] Sx).
            -   intros eq; subst x.
                unfold S in Sx.
                destruct a; contradiction.
        }
        exists [_|xa].
        subst b.
        unfold f'.
        apply f_equal.
        apply set_type_eq.
        reflexivity.
    -   intros a b.
        cbn; unfold initial_segment_le.
        unfold f'.
        rewrite <- (piece_iso f).
        reflexivity.
Qed.
Lemma b_ex : ∃ b, (∀ a, piece_f f⟨a⟩ ≠ b) ∧
           (∀ b', (∀ a, piece_f f⟨a⟩ ≠ b') → ord_le B b b').
Proof.
    get_ord_wo B.
    pose proof (well_ordered _ b_ex_base) as [b [Sb b_min]].
    exists b.
    split; assumption.
Qed.
Definition b := ex_val b_ex.
Lemma b_not : ∀ a, piece_f f⟨a⟩ ≠ b.
Proof.
    unfold b, ex_val.
    destruct (ex_to_type b_ex); cbn in *.
    apply a0.
Qed.
Lemma b_min : ∀ b', (∀ a, piece_f f⟨a⟩ ≠ b') → ord_le B b b'.
Proof.
    unfold b, ex_val.
    destruct (ex_to_type b_ex); cbn in *.
    apply a0.
Qed.

Lemma a_gt : ∀ x : set_type (domain (piece_f f)), ord_le A [x|] a.
Proof.
    intros [x x_in].
    apply (piece_bot1 f); try assumption.
    apply not_in.
Qed.
Lemma b_gt : ∀ x, ord_le B (piece_f f⟨x⟩) b.
Proof.
    intros x.
    apply (piece_bot2 f).
    -   exists x; reflexivity.
    -   intros [y y_eq].
        pose proof (b_not y).
        contradiction.
Qed.
Lemma a_ngt : ∀ x : set_type (domain (piece_f f)), ¬ord_le A a [x|].
Proof.
    intros x gt.
    pose proof (a_gt x).
    get_ord_wo A.
    pose proof (antisym gt H).
    pose proof not_in.
    rewrite H2 in H3.
    destruct x; contradiction.
Qed.
Lemma b_ngt : ∀ x, ¬ord_le B b (piece_f f⟨x⟩).
Proof.
    intros x gt.
    pose proof (b_gt x).
    get_ord_wo B.
    pose proof (antisym H gt).
    pose proof (b_not x).
    contradiction.
Qed.

Definition S x := domain (piece_f f) x ∨ a = x.
Definition Sf (x : set_type S) : ord_U B.
    destruct (or_to_strong _ _ [|x]).
    -   exact (piece_f f⟨[_|d]⟩).
    -   exact b.
Defined.

Local Ltac or_case a := destruct (or_to_strong (domain (piece_f f) [a|])).

Lemma Sf_inj : Injective Sf.
Proof.
    split.
    intros x y eq.
    unfold Sf in eq.
    or_case x; or_case y; cbn in *.
    -   apply (piece_inj f) in eq.
        apply set_type_eq; inversion eq; reflexivity.
    -   apply b_not in eq.
        contradiction.
    -   symmetry in eq.
        apply b_not in eq.
        contradiction.
    -   apply set_type_eq.
        rewrite <- e, <- e0.
        reflexivity.
Qed.

Lemma Sf_iso : ∀ a b, (ord_le A) [a|] [b|] ↔ (ord_le B) (Sf a) (Sf b).
Proof.
    intros x y.
    unfold Sf.
    or_case x; or_case y; cbn in *.
    -   rewrite <- (piece_iso f).
        reflexivity.
    -   rewrite <- e; clear e y.
        split.
        +   intros leq.
            apply b_gt.
        +   intros leq.
            pose proof (a_gt [_|d]).
            cbn in H.
            exact H.
    -   rewrite <- e; clear e.
        split; intro eq.
        +   pose proof (a_ngt [_|d]).
            contradiction.
        +   apply b_ngt in eq.
            contradiction.
    -   rewrite <- e, <- e0.
        split.
        +   intros.
            get_ord_wo B.
            destruct (connex b b); assumption.
        +   intros.
            get_ord_wo A.
            destruct (connex a a); assumption.
Qed.

Lemma Sf_bot1 : ∀ a b, S a → ¬S b → ord_le A a b.
Proof.
    intros x y Sx Sy.
    unfold S in Sy.
    rewrite not_or in Sy.
    destruct Sy as [fy ay].
    destruct Sx as [fx|ax].
    -   apply (piece_bot1 f); assumption.
    -   subst x.
        apply a_min.
        exact fy.
Qed.

Lemma Sf_bot2 : ∀ a b, (∃ x, Sf x = a) → ¬(∃ x, Sf x = b) → ord_le B a b.
Proof.
    intros x y xx nyy.


    destruct xx as [[m Sm] m_eq].
    subst x.
    unfold Sf.
    or_case [m|Sm]; cbn in *.
    -   apply (piece_bot2 f).
        +   exists [m|d]; reflexivity.
        +   intros [x x_y].
            rewrite not_ex in nyy.
            assert (S [x|]) as Sx by (left; destruct x; assumption).
            specialize (nyy [_|Sx]).
            unfold Sf in nyy; cbn in *.
            or_case x.
            *   destruct x; cbn in *.
                rewrite (proof_irrelevance _ d0) in x_y.
                contradiction.
            *   pose proof not_in.
                rewrite e in H.
                destruct x; contradiction.
    -   subst m.
        apply b_min.
        intros x.
        rewrite not_ex in nyy.
        assert (S [x|]) as Sx.
        {
            left.
            destruct x; assumption.
        }
        specialize (nyy [_|Sx]).
        unfold Sf in nyy; cbn in *.
        or_case x; cbn in *.
        +   destruct x; cbn in *.
            rewrite (proof_irrelevance _ d).
            exact nyy.
        +   clear Sx.
            pose proof not_in.
            rewrite e in H.
            destruct x; contradiction.
Qed.

Lemma all_in_f_base : False.
Proof.
    pose (f' := make_piece
        (make_set_function S Sf) Sf_inj Sf_iso Sf_bot1 Sf_bot2).
    apply (f_max f').
    split.
    -   unfold le; cbn; unfold piece_le.
        assert (domain (piece_f f) ⊆ S) as sub.
        {
            intros x fx.
            left; exact fx.
        }
        exists sub.
        intros x.
        unfold f', Sf; cbn.
        or_case x; cbn in *.
        +   apply f_equal.
            apply set_type_eq; reflexivity.
        +   exfalso.
            pose proof not_in.
            rewrite e in H.
            destruct x; contradiction.
    -   intros f_eq.
        pose proof not_in as not_in2.
        rewrite f_eq in not_in2.
        unfold piece_f in not_in2; cbn in not_in2.
        unfold S in not_in2.
        rewrite not_or in not_in2.
        destruct not_in2; contradiction.
Qed.

End AllInF.

Lemma all_in_f : ∀ a, domain (piece_f f) a.
Proof.
    intros a.
    classic_contradiction contr.
    exact (all_in_f_base a contr).
Qed.

Definition f' x := (piece_f f) ⟨[_|all_in_f x]⟩.

Lemma f'_sur : Surjective f'.
Proof.
    split.
    intros b.
    classic_contradiction no_a.
    apply AB.
    rewrite ord_lt_initial.
    pose (S y := ¬(∃ x, f' x = y)).
    assert (∃ x, S x) as S_nempty by (exists b; exact no_a).
    get_ord_wo B.
    pose proof (well_ordered S S_nempty) as [x [Sx x_min]].
    clear S_nempty b no_a.
    assert (∀ a, S a → ord_le B x a) as x_min2.
    {
        intros a Sa.
        classic_case (a = x) as [eq|neq].
        -   subst.
            destruct (connex x x); assumption.
        -   exact (x_min a Sa).
    }
    clear x_min; rename x_min2 into x_min.
    assert (∀ a, ord_le B x a → S a) as le_S2.
    {
        intros y leq [a a_eq].
        assert (∃ x, piece_f f⟨x⟩ = y) as bot_ex.
        {
            exists [_|all_in_f a].
            exact a_eq.
        }
        assert (¬(∃ a, piece_f f⟨a⟩ = x)) as bot_nex.
        {
            intros [b b_eq].
            subst x.
            unfold S in Sx.
            rewrite not_ex in Sx.
            specialize (Sx [b|]).
            apply Sx.
            destruct b as [b b_in].
            unfold f'; cbn.
            rewrite (proof_irrelevance _ b_in).
            reflexivity.
        }
        pose proof (piece_bot2 f _ _ bot_ex bot_nex) as leq2.
        pose proof (antisym leq leq2).
        subst.
        unfold S in Sx.
        rewrite not_ex in Sx.
        specialize (Sx a).
        contradiction.
    }
    exists x.
    assert (∀ a, initial_segment_set B x (f' a)) as f'_lt.
    {
        intros a.
        unfold initial_segment_set.
        split.
        -   assert (¬S (f' a)) as Sa.
            {
                intros contr.
                unfold S in contr.
                rewrite not_ex in contr.
                specialize (contr a).
                contradiction.
            }
            classic_contradiction contr.
            apply Sa.
            apply le_S2.
            destruct (connex x (f' a)); try assumption.
            contradiction.
        -   unfold S in Sx.
            rewrite not_ex in Sx.
            apply Sx.
    }
    pose (g x := [_|f'_lt x]).
    exists g.
    split.
    1: split; split.
    *   intros a b eq.
        unfold g, f' in eq.
        inversion eq as [eq2].
        pose proof (piece_inj f).
        pose proof (inj [_|all_in_f a] [_|all_in_f b] eq2).
        inversion H2.
        reflexivity.
    *   intros b.
        classic_contradiction Sb'.
        assert (S [b|]) as Sb.
        {
            intros [a a_eq].
            rewrite not_ex in Sb'.
            apply (Sb' a).
            apply set_type_eq.
            exact a_eq.
        }
        clear Sb'.
        specialize (x_min _ Sb).
        destruct b as [b b_leq]; cbn in *.
        destruct b_leq as [b_leq b_neq].
        pose proof (antisym b_leq x_min).
        contradiction.
    *   intros a b.
        pose proof (piece_iso f [_|all_in_f a] [_|all_in_f b]) as iso.
        cbn in iso.
        rewrite iso.
        reflexivity.
Qed.

Lemma ord_le_connex : ¬(to_ord A < to_ord B) → ¬(to_ord B < to_ord A) →
    to_ord A = to_ord B.
Proof.
    equiv_simpl.
    exists f'.
    split.
    -   split; split.
        +   intros a b ab.
            apply (piece_inj f) in ab.
            inversion ab.
            reflexivity.
        +   apply f'_sur.
    -   intros a b.
        unfold f'.
        exact (piece_iso f [_|all_in_f a] [_|all_in_f b]).
Qed.


End OrdConnex.
End OrdConnex.

Lemma ord_le_connex : ∀ α β, {α ≤ β} + {β ≤ α}.
Proof.
    intros α β.
    classic_case (α = β) as [eq|neq].
    {
        subst.
        left.
        equiv_get_value β; unfold le; equiv_simpl.
        left; exists identity; split; try apply identity_bijective.
        reflexivity.
    }
    classic_case (α ≤ β) as [αβ|αβ]; try (left; exact αβ).
    classic_case (β ≤ α) as [βα|βα]; try (right; exact βα).
    rewrite ord_le_lt in *.
    rewrite ord_le_lt.
    rewrite not_or in αβ.
    rewrite not_or in βα.
    destruct αβ as [C0 αβ]; clear C0.
    destruct βα as [C0 βα]; clear C0.
    exfalso.
    apply neq; clear neq.
    equiv_get_value α β.
    apply OrdConnex.ord_le_connex; assumption.
Qed.
Global Instance ord_le_connex_class : Connex le := {
    connex := ord_le_connex
}.

Lemma ord_le_antisymmetric : ∀ α β, α ≤ β → β ≤ α → α = β.
Proof.
    intros α β αβ βα.
    rewrite ord_le_lt in αβ.
    rewrite ord_le_lt in βα.
    destruct αβ as [C0|αβ]; try exact C0.
    destruct βα as [C0|βα]; try (symmetry; exact C0).
    exfalso.
    equiv_get_value α β.
    rewrite ord_lt_initial in αβ.
    rewrite ord_lt_initial in βα.
    destruct αβ as [a [f [f_bij f_iso]]].
    destruct βα as [b [g [g_bij g_iso]]].
    pose (h x := [g [f x|]|]).
    assert (Injective h) as h_inj.
    {
        split.
        intros x y eq.
        apply f_bij.
        apply set_type_eq.
        apply g_bij.
        apply set_type_eq.
        exact eq.
    }
    assert (∀ a b, ord_le α a b ↔ ord_le α (h a) (h b)) as h_iso.
    {
        intros x y.
        unfold h.
        split.
        -   intros eq.
            apply f_iso in eq.
            apply g_iso in eq.
            exact eq.
        -   intros eq.
            apply f_iso.
            apply g_iso.
            exact eq.
    }
    pose proof (ord_iso_le _ h h_inj h_iso b) as leq1.
    assert (initial_segment_set α b (h b)) as leq2.
    {
        unfold h.
        destruct (g [f b|]).
        exact set_proof.
    }
    destruct leq2 as [leq2 neq].
    get_ord_wo α.
    pose proof (antisym leq2 leq1).
    contradiction.
Qed.
Global Instance ord_le_antisym_class : Antisymmetric le := {
    antisym := ord_le_antisymmetric
}.

Lemma ord_le_transitive : ∀ α β γ, α ≤ β → β ≤ γ → α ≤ γ.
Proof.
    intros α β γ.
    repeat rewrite ord_le_lt.
    intros [αβ|αβ] [βγ|βγ]; try subst.
    -   left; trivial.
    -   right; assumption.
    -   right; assumption.
    -   right.
        equiv_get_value α β γ.
        rewrite ord_lt_initial in βγ.
        rewrite ord_lt_initial in αβ.
        rewrite ord_lt_initial.
        destruct βγ as [c [f [f_bij f_iso]]].
        destruct αβ as [b [g [g_bij g_iso]]].
        exists [f b|].
        assert (∀ x, initial_segment_set γ [f b|] [f [g x|]|]) as fg_in.
        {
            intros x.
            destruct (g x) as [gx [gx_le gx_neq]].
            split.
            -   apply f_iso.
                exact gx_le.
            -   cbn.
                intro contr.
                apply set_type_eq in contr.
                apply f_bij in contr.
                contradiction.
        }
        exists (λ x, [_|fg_in x]).
        split.
        1: split; split.
        +   intros x y eq; cbn in *.
            inversion eq as [eq2].
            apply set_type_eq in eq2.
            apply f_bij in eq2.
            apply set_type_eq in eq2.
            apply g_bij in eq2.
            exact eq2.
        +   intros z.
            assert (initial_segment_set γ c [z|]) as z_c.
            {
                get_ord_wo γ.
                destruct z as [z [z_leq z_neq]]; cbn in *.
                destruct (f b) as [fb fb_eq]; cbn in *.
                split.
                -   apply (trans z_leq).
                    apply fb_eq.
                -   intros contr.
                    subst z.
                    destruct fb_eq as [fb_leq fb_neq].
                    pose proof (antisym z_leq fb_leq).
                    contradiction.
            }
            pose proof (sur f [_|z_c]) as [y y_eq].
            assert (initial_segment_set β b y) as y_b.
            {
                split.
                -   rewrite f_iso.
                    rewrite y_eq.
                    apply [|z].
                -   intro contr.
                    subst.
                    destruct [|z].
                    apply H0.
                    destruct z as [z z_in]; cbn in *.
                    rewrite y_eq.
                    reflexivity.
            }
            pose proof (sur g [_|y_b]) as [x x_eq].
            exists x.
            destruct z as [z z_in]; cbn in *.
            apply set_type_eq; cbn.
            rewrite x_eq; cbn.
            rewrite y_eq; cbn.
            reflexivity.
        +   intros x y.
            rewrite g_iso.
            cbn.
            exact (f_iso [g x|] [g y|]).
Qed.
Global Instance ord_le_trans_class : Transitive le := {
    trans := ord_le_transitive
}.
(* end hide *)
Local Notation "'to_ord' A" := (to_equiv ord_equiv A) (at level 10).
Theorem ord_lt_init : ∀ A x, to_ord (ord_initial_segment A x) < to_ord A.
Proof.
    intros A x.
    rewrite ord_lt_initial.
    exists x.
    apply eq_reflexive.
Qed.

Definition ords_lt_set α := λ β, β < α.
Definition ords_lt_le α (β γ : set_type (ords_lt_set α)) := [β|] ≤ [γ|].

(* begin hide *)
Module OrdsLtWo.
Section OrdsLtWo.

Variable A : ord_type.
Local Notation "'to_ord' A" := (to_equiv ord_equiv A) (at level 10).

Lemma f'_range_in : ∀ x, ords_lt_set (to_ord A) (to_ord (ord_initial_segment A x)).
Proof.
    intros x.
    apply ord_lt_init.
Qed.

Definition f' (x : ord_U A) := [to_ord (ord_initial_segment A x)|f'_range_in x].

Lemma f'_inj : Injective f'.
Proof.
    split.
    intros a b eq.
    unfold f' in eq.
    apply set_type_eq in eq; cbn in eq.
    equiv_simpl in eq.
    apply ord_init_iso_eq in eq.
    exact eq.
Qed.

Lemma f'_sur : Surjective f'.
Proof.
    split.
    intros [β β_lt].
    equiv_get_value β.
    unfold ords_lt_set in β_lt.
    pose proof β_lt as β_lt2.
    rewrite ord_lt_initial in β_lt2.
    destruct β_lt2 as [x x_eq].
    exists x.
    unfold f'.
    apply set_type_eq; cbn.
    equiv_simpl.
    apply eq_symmetric in x_eq.
    exact x_eq.
Qed.

Lemma f'_bij : Bijective f'.
Proof.
    split.
    -   exact f'_inj.
    -   exact f'_sur.
Qed.
Definition f := bij_inv f' (f_bij := f'_bij).

Lemma f_ex : ∀ β, ∃ x, to_ord (ord_initial_segment A x) = [β|] ∧ f β = x.
Proof.
    intros β.
    assert (∃ x, f' x = β) as eq.
    {
        destruct β as [β β_in].
        unfold ords_lt_set in β_in.
        equiv_get_value β.
        rename β into B.
        pose proof β_in as B_in.
        rewrite ord_lt_initial in B_in.
        destruct B_in as [x B_in].
        exists x.
        unfold f'.
        apply set_type_eq; cbn.
        symmetry.
        equiv_simpl.
        exact B_in.
    }
    destruct eq as [x x_eq].
    subst β.
    exists x.
    split.
    -   unfold f'; cbn.
        reflexivity.
    -   apply inverse_eq1.
        apply bij_inv_inv.
Qed.

Lemma f_iso : ∀ X Y, [X|] < [Y|] → ord_le A (f X) (f Y).
Proof.
    intros X Y XY.
    pose proof (f_ex X) as [x [x_eq x_eq2]].
    pose proof (f_ex Y) as [y [y_eq y_eq2]].
    rewrite x_eq2, y_eq2; clear x_eq2 y_eq2.
    destruct X as [X X_lt], Y as [Y Y_lt].
    change [[X|X_lt]|] with X in *.
    change [[Y|Y_lt]|] with Y in *.
    get_ord_wo A.
    rewrite <- x_eq, <- y_eq in XY.
    rename XY into eq.
    rewrite ord_lt_initial in eq.
    destruct eq as [[z z_lt] z_eq].
    assert (ord_le A x z) as leq.
    {
        classic_contradiction nleq.
        assert (initial_segment_set A x z) as z_x.
        {
            split.
            -   destruct (connex z x); try assumption; contradiction.
            -   intros eq; subst.
                destruct (connex x x); contradiction.
        }
        clear nleq.
        unfold initial_segment_set in *.
        assert (ord_initial_segment (ord_initial_segment A y) [z|z_lt] ~
                ord_initial_segment A z) as eq.
        {
            cbn.
            assert (∀ x : set_type (initial_segment_set (ord_initial_segment A y)
                [z|z_lt]), initial_segment_set A z [[x|]|]) as all_in.
            {
                clear.
                intros [[a a_y] a_z].
                unfold initial_segment_set in *; cbn in *.
                unfold initial_segment_le in a_z; cbn in *.
                destruct a_z as [eq1 eq2].
                split; try exact eq1.
                intros eq; subst.
                apply eq2.
                apply set_type_eq; reflexivity.
            }
            exists (λ x, [_|all_in x]).
            split.
            1: split; split.
            -   intros a b eq.
                apply set_type_eq.
                apply (land set_type_eq).
                inversion eq.
                reflexivity.
            -   intros [b b_z].
                assert (initial_segment_set A y b) as b_y.
                {
                    split.
                    -   exact (trans (land b_z) (land z_lt)).
                    -   intros contr.
                        subst b.
                        destruct b_z as [yz yz_neq].
                        pose proof (antisym yz (land z_lt)).
                        contradiction.
                }
                assert (initial_segment_set (ord_initial_segment A y) [z|z_lt]
                    [b|b_y]) as b_in.
                {
                    unfold initial_segment_set.
                    unfold ord_initial_segment; cbn; unfold initial_segment_le.
                    cbn.
                    destruct b_z as [b_z b_neq].
                    split; try assumption.
                    intro contr.
                    inversion contr.
                    contradiction.
                }
                exists [_|b_in].
                apply set_type_eq; reflexivity.
            -   intros a b.
                unfold initial_segment_le; cbn.
                reflexivity.
        }
        pose proof (eq_transitive ord_equiv).
        pose proof (trans z_eq eq).
        apply ord_init_iso_eq in H2.
        symmetry in H2.
        destruct z_x; contradiction.
    }
    destruct z_lt as [z_lt].
    exact (trans leq z_lt).
Qed.

Lemma ords_lt_wo_base : WellOrdered (ords_lt_le (to_ord A)).
Proof.
    split.
    intros S [[B B_in] SB].
    unfold ords_lt_set in B_in.
    pose (b := f [B|B_in]).
    pose (S' x := ∃ C, S C ∧ f C = x).
    assert (∃ x, S' x) as S'_nempty.
    {
        exists b.
        unfold S'.
        exists [B|B_in].
        split; try assumption.
        unfold b.
        reflexivity.
    }
    get_ord_wo A.
    pose proof (well_ordered S' S'_nempty) as [x [S'x x_min]].
    destruct S'x as [X [SX X_eq]].
    exists X.
    split; try assumption.
    intros Y SY.
    specialize (x_min (f Y)).
    prove_parts x_min.
    {
        unfold S'.
        exists Y.
        split; try assumption; reflexivity.
    }
    rewrite <- X_eq in x_min.
    unfold ords_lt_le.
    classic_contradiction contr.
    rewrite nle_lt in contr.
    pose proof (f_iso _ _ contr) as leq.
    pose proof (antisym leq x_min) as eq.
    apply (bij_inv_bij f') in eq.
    rewrite <- set_type_eq in eq.
    destruct contr; contradiction.
Qed.


End OrdsLtWo.

Lemma ords_lt_wo : ∀ α, WellOrdered (ords_lt_le α).
Proof.
    intros α.
    equiv_get_value α.
    apply ords_lt_wo_base.
Qed.

End OrdsLtWo.

Open Scope set_scope.

Lemma ord_le_wo : ∀ S : ord → Prop, (∃ α, S α) → ∃ α, is_least le S α.
Proof.
    intros S [α Sα].
    classic_case (is_least le S α) as [α_least|α_nleast].
    -   exists α.
        split; try assumption.
        intros δ Sδ.
        apply α_least.
        exact Sδ.
    -   pose proof (OrdsLtWo.ords_lt_wo α) as wo.
        pose (S' (x : set_type (ords_lt_set α)) := S [x|]).
        assert (∃ β, S' β) as S'_nempty.
        {
            unfold is_least in α_nleast.
            rewrite not_and in α_nleast.
            destruct α_nleast as [C0|H]; try contradiction.
            rewrite not_all in H.
            destruct H as [β H].
            rewrite not_impl in H.
            destruct H as [Sβ eq].
            rewrite nle_lt in eq.
            exists [β|eq].
            exact Sβ.
        }
        pose proof (well_ordered S' S'_nempty) as [β [S'β β_min]].
        exists [β|].
        split; try apply S'β.
        intros δ Sδ.
        classic_case (α ≤ δ) as [δ_leq|δ_ltq].
        +   apply (trans2 δ_leq).
            apply [|β].
        +   rewrite nle_lt in δ_ltq.
            assert (ords_lt_set α δ) as δ_in.
            {
                destruct β as [β β_leq]; cbn in *.
                unfold ords_lt_set in *.
                exact δ_ltq.
            }
            apply (β_min [_|δ_in]).
            exact Sδ.
Qed.
Global Instance ord_le_wo_class : WellOrdered le := {
    well_ordered := ord_le_wo
}.

Lemma nat_to_ord_lt1 : ∀ a b, a < b → nat_to_ord a < nat_to_ord b.
Proof.
    intros a b leq.
    unfold nat_to_ord.
    rewrite ord_lt_initial.
    exists [a|leq].
    assert (∀ n : ord_U (nat_to_ord_type a), initial_segment_set
        (nat_to_ord_type b) [a | leq] [[n|]|trans [|n] leq]) as n_in.
    {
        intros [n n_lt].
        split; cbn.
        -   unfold le; cbn.
            apply n_lt.
        -   intro contr.
            inversion contr.
            destruct n_lt; contradiction.
    }
    exists (λ x, [_|n_in x]); cbn.
    split.
    split; split.
    -   intros m n eq.
        apply set_type_eq.
        inversion eq.
        reflexivity.
    -   intros [[n n_lt1] n_lt2].
        unfold initial_segment_set in n_lt2; cbn in n_lt2.
        destruct n_lt2 as [n_lt2 n_neq].
        unfold le in n_lt2; cbn in n_lt2.
        assert (n ≠ a) as n_neq2.
        {
            intro contr; subst.
            apply n_neq.
            apply set_type_eq.
            reflexivity.
        }
        exists [n|make_and n_lt2 n_neq2].
        do 2 apply (land set_type_eq).
        reflexivity.
    -   intros [m m_lt] [n n_lt].
        unfold le; cbn.
        reflexivity.
Qed.
(* end hide *)
Theorem nat_to_ord_lt : ∀ a b, (nat_to_ord a < nat_to_ord b) = (a < b).
Proof.
    intros a b.
    apply propositional_ext; split; try apply nat_to_ord_lt1.
    intros eq.
    classic_contradiction contr.
    rewrite nlt_le in contr.
    classic_case (b = a).
    -   subst.
        destruct eq; contradiction.
    -   pose proof (nat_to_ord_lt1 _ _ (make_and contr n)) as eq2.
        pose proof (trans eq eq2) as [c d].
        contradiction.
Qed.

Theorem nat_to_ord_eq : ∀ a b, nat_to_ord a = nat_to_ord b → a = b.
Proof.
    intros a b eq.
    destruct (trichotomy a b) as [[leq|req]|leq]; try exact req; exfalso.
    -   rewrite <- nat_to_ord_lt in leq.
        destruct leq; contradiction.
    -   symmetry in eq.
        rewrite <- nat_to_ord_lt in leq.
        destruct leq; contradiction.
Qed.
Theorem nat_to_ord_neq : ∀ a b, a ≠ b → nat_to_ord a ≠ nat_to_ord b.
Proof.
    intros a b neq eq.
    apply nat_to_ord_eq in eq.
    contradiction.
Qed.

Theorem nat_to_ord_le : ∀ a b, (nat_to_ord a ≤ nat_to_ord b) = (a ≤ b).
Proof.
    intros a b.
    classic_case (a = b) as [eq|neq].
    {
        subst.
        apply propositional_ext.
        split; intro; apply refl.
    }
    apply propositional_ext; split; intro leq.
    -   apply nat_to_ord_neq in neq.
        assert (nat_to_ord a < nat_to_ord b) as eq by (split; assumption).
        rewrite nat_to_ord_lt in eq.
        apply eq.
    -   assert (a < b) as eq by (split; assumption).
        rewrite <- nat_to_ord_lt in eq.
        apply eq.
Qed.
(* begin hide *)
Close Scope ord_scope.
Close Scope set_scope.
(* end hide *)
