Require Import init.

Require Export group_category.
Require Export group_subgroup.
Require Export mult_div.

Require Export card.

Section Lagrange.

Context {G : Group} (H : Subgroup G).

Local Open Scope card_scope.

Definition left_coset_by (a : G) := image_under (λ h, a + h) H.
Definition left_coset := image left_coset_by.

Theorem lagrange : |set_type H| * |set_type left_coset| = |G|.
Proof.
    unfold mult; equiv_simpl.
    exists (λ p : _ * _ left_coset, ex_val [|snd p] + [fst p|]).
    split; split.
    -   intros [[h1 h1_in] [A A_coset]] [[h2 h2_in] [B B_coset]]; cbn.
        intros eq.
        pose proof (ex_proof A_coset : A = left_coset_by (ex_val A_coset))
            as A_eq.
        pose proof (ex_proof B_coset : B = left_coset_by (ex_val B_coset))
            as B_eq.
        assert (A = B) as AB_eq.
        {
            rewrite A_eq, B_eq.
            apply antisym.
            -   intros x [a [Ha x_eq]].
                rewrite x_eq.
                exists (h2 - h1 + a).
                split.
                +   apply subgroup_plus; [>apply subgroup_plus|].
                    *   exact h2_in.
                    *   apply subgroup_neg.
                        exact h1_in.
                    *   exact Ha.
                +   rewrite plus_assoc.
                    apply rplus.
                    rewrite plus_assoc.
                    rewrite <- plus_lrmove.
                    exact eq.
            -   intros x [a [Ha x_eq]].
                rewrite x_eq.
                exists (h1 - h2 + a).
                split.
                +   apply subgroup_plus; [>apply subgroup_plus|].
                    *   exact h1_in.
                    *   apply subgroup_neg.
                        exact h2_in.
                    *   exact Ha.
                +   rewrite plus_assoc.
                    apply rplus.
                    rewrite plus_assoc.
                    rewrite <- plus_lrmove.
                    symmetry; exact eq.
        }
        subst B.
        apply prod_combine; cbn; rewrite set_type_eq2; [>|reflexivity].
        rewrite (proof_irrelevance A_coset B_coset) in eq.
        apply plus_lcancel in eq.
        exact eq.
    -   intros y.
        assert (left_coset (left_coset_by y)) as y_coset
            by (exists y; reflexivity).
        pose (y' := ex_val y_coset).
        assert (H (-y' + y)) as y'_in.
        {
            pose proof (ex_proof y_coset
                : left_coset_by y = left_coset_by y') as y_eq.
            assert (left_coset_by y' y) as y_in.
            {
                rewrite <- y_eq.
                exists 0.
                split; [>apply subgroup_zero|].
                symmetry; apply plus_rid.
            }
            destruct y_in as [h [Hh eq]].
            rewrite eq.
            rewrite plus_llinv.
            exact Hh.
        }
        exists ([_|y'_in], [_|y_coset]); cbn.
        fold y'.
        apply plus_lrinv.
Qed.

Theorem lagrange_div : |set_type H| ∣ |G|.
Proof.
    exists (|set_type left_coset|).
    rewrite mult_comm.
    exact lagrange.
Qed.

End Lagrange.
