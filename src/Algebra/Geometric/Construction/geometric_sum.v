Require Import init.

Require Export geometric_universal.
Require Import algebra_category.
Require Import category_initterm.

Section GeometricSum.

Context {U : CRingObj} {V : ModuleObj U}.
Context (B : set_type (bilinear_form (V := V))).

Local Notation geo := (geometric_algebra B).
Local Notation φ := (vector_to_geo B).

Let S (x : geo) := ∃ l : ulist (U * list V), x =
    ulist_sum (ulist_image (λ p, fst p · list_prod (list_image φ (snd p))) l).

(** TODO: Make subalgebras easier to define *)

Lemma S_plus_in : ∀ a b, S a → S b → S (a + b).
Proof.
    intros a b [u a_eq] [v b_eq]; subst a b.
    exists (u + v).
    rewrite ulist_image_conc, ulist_sum_plus.
    reflexivity.
Qed.

Lemma S_zero_in : S 0.
Proof.
    exists ⟦⟧.
    rewrite ulist_image_end, ulist_sum_end.
    reflexivity.
Qed.

Lemma S_scalar_in : ∀ a v, S v → S (a · v).
Proof.
    intros a v [l v_eq]; subst v.
    exists (ulist_image (λ p, (a * fst p, snd p)) l).
    rewrite <- ulist_sum_scalar.
    apply f_equal.
    do 2 rewrite ulist_image_comp.
    apply f_equal2; [>|reflexivity].
    apply functional_ext.
    intros [b v]; cbn.
    apply scalar_comp.
Qed.

Lemma S_neg_in : ∀ a, S a → S (-a).
Proof.
    intros a a_in.
    apply (S_scalar_in (-1)) in a_in.
    rewrite scalar_neg_one in a_in.
    exact a_in.
Qed.

Lemma S_mult_in : ∀ a b, S a → S b → S (a * b).
Proof.
    intros a b [u a_eq] [v b_eq]; subst a b.
    induction u as [|a u] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_lanni.
        apply S_zero_in.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite rdist.
    apply S_plus_in; [>|exact IHu].
    clear u IHu.
    induction v as [|b v] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite mult_ranni.
        apply S_zero_in.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite ldist.
    apply S_plus_in; [>|exact IHv].
    clear v IHv.
    rewrite scalar_lmult, scalar_rmult.
    do 2 apply S_scalar_in.
    rewrite <- list_prod_conc.
    rewrite <- list_image_conc.
    exists ⟦(1, snd a + snd b)⟧.
    rewrite ulist_image_add, ulist_image_end.
    rewrite ulist_sum_add, ulist_sum_end.
    cbn.
    rewrite scalar_id, plus_rid.
    reflexivity.
Qed.

Lemma S_one_in : S 1.
Proof.
    exists ⟦(1, [])⟧.
    rewrite ulist_image_add, ulist_sum_add; cbn.
    rewrite ulist_image_end, ulist_sum_end.
    rewrite plus_rid.
    rewrite list_image_end, list_prod_end.
    rewrite scalar_id.
    reflexivity.
Qed.

Local Instance S_plus : Plus (set_type S) := {
    plus a b := [_|S_plus_in _ _ [|a] [|b]]
}.
Local Instance S_zero : Zero (set_type S) := {
    zero := [_|S_zero_in]
}.
Local Instance S_neg : Neg (set_type S) := {
    neg a := [_|S_neg_in _ [|a]]
}.
Local Instance S_plus_assoc : PlusAssoc (set_type S).
Proof.
    split.
    intros a b c.
    apply set_type_eq.
    apply plus_assoc.
Qed.
Local Instance S_plus_comm : PlusComm (set_type S).
Proof.
    split.
    intros a b.
    apply set_type_eq.
    apply plus_comm.
Qed.
Local Instance S_plus_lid : PlusLid (set_type S).
Proof.
    split.
    intros a.
    apply set_type_eq.
    apply plus_lid.
Qed.
Local Instance S_plus_linv : PlusLinv (set_type S).
Proof.
    split.
    intros a.
    apply set_type_eq.
    apply plus_linv.
Qed.
Local Instance S_scalar : ScalarMult U (set_type S) := {
    scalar_mult a v := [_|S_scalar_in a _ [|v]]
}.
Local Instance S_scalar_id : ScalarId U (set_type S).
Proof.
    split.
    intros v.
    apply set_type_eq.
    apply scalar_id.
Qed.
Local Instance S_scalar_ldist : ScalarLdist U (set_type S).
Proof.
    split.
    intros a u v.
    apply set_type_eq.
    apply scalar_ldist.
Qed.
Local Instance S_scalar_rdist : ScalarRdist U (set_type S).
Proof.
    split.
    intros a b v.
    apply set_type_eq.
    apply scalar_rdist.
Qed.
Local Instance S_scalar_comp : ScalarComp U (set_type S).
Proof.
    split.
    intros a b v.
    apply set_type_eq.
    apply scalar_comp.
Qed.
Local Instance S_mult : Mult (set_type S) := {
    mult a b := [_|S_mult_in _ _ [|a] [|b]]
}.
Local Instance S_ldist : Ldist (set_type S).
Proof.
    split.
    intros a b c.
    apply set_type_eq.
    apply ldist.
Qed.
Local Instance S_rdist : Rdist (set_type S).
Proof.
    split.
    intros a b c.
    apply set_type_eq.
    apply rdist.
Qed.
Local Instance S_mult_assoc : MultAssoc (set_type S).
Proof.
    split.
    intros a b c.
    apply set_type_eq.
    apply mult_assoc.
Qed.
Local Instance S_one : One (set_type S) := {
    one := [_|S_one_in]
}.
Local Instance S_mult_lid : MultLid (set_type S).
Proof.
    split.
    intros a.
    apply set_type_eq.
    apply mult_lid.
Qed.
Local Instance S_mult_rid : MultRid (set_type S).
Proof.
    split.
    intros a.
    apply set_type_eq.
    apply mult_rid.
Qed.
Local Instance S_scalar_lmult : ScalarLMult U (set_type S).
Proof.
    split.
    intros a u v.
    apply set_type_eq.
    apply scalar_lmult.
Qed.
Local Instance S_scalar_rmult : ScalarRMult U (set_type S).
Proof.
    split.
    intros a u v.
    apply set_type_eq.
    apply scalar_rmult.
Qed.
Let S_algebra := make_algebra U
    (make_module U _ S_plus S_zero S_neg S_plus_assoc S_plus_comm S_plus_lid
        S_plus_linv S_scalar S_scalar_id S_scalar_ldist S_scalar_rdist
        S_scalar_comp)
    S_mult S_ldist S_rdist S_mult_assoc S_one S_mult_lid S_mult_rid
    S_scalar_lmult S_scalar_rmult : Algebra U.

Lemma vector_to_S_in : ∀ v, S (φ v).
Proof.
    intros v.
    exists ⟦(1, [v])⟧.
    rewrite ulist_image_add, ulist_sum_add.
    rewrite ulist_image_end, ulist_sum_end.
    rewrite plus_rid.
    cbn.
    rewrite list_prod_single.
    rewrite scalar_id.
    reflexivity.
Qed.

Let vector_to_S (v : V) : set_type S := [_|vector_to_S_in v].

Lemma vector_to_S_plus : ∀ u v,
    vector_to_S (u + v) = vector_to_S u + vector_to_S v.
Proof.
    intros u v.
    apply set_type_eq.
    unfold vector_to_S.
    cbn.
    rewrite module_homo_plus.
    reflexivity.
Qed.

Lemma vector_to_S_scalar : ∀ a v, vector_to_S (a · v) = a · vector_to_S v.
Proof.
    intros a v.
    apply set_type_eq.
    unfold vector_to_S.
    cbn.
    rewrite module_homo_scalar.
    reflexivity.
Qed.

Let vector_to_S_homo := make_module_homomorphism U V (algebra_module S_algebra)
    vector_to_S vector_to_S_plus vector_to_S_scalar.

Lemma S_contract : ∀ v, vector_to_S_homo v * vector_to_S_homo v = [B|] v v · 1.
Proof.
    intros v.
    apply set_type_eq.
    unfold vector_to_S_homo; cbn.
    unfold vector_to_S.
    unfold mult; cbn.
    apply geo_contract.
Qed.

Definition S_to_geo := make_to_geo B S_algebra vector_to_S_homo S_contract.

Theorem S_universal : @initial (TO_GEO B) S_to_geo.
Proof.
    unfold initial, S_to_geo; cbn.
    intros [A f f_contr].
    unfold to_geo_set; cbn.
    apply singleton_ex; [>split|].
    -   apply ex_set_type.
        pose proof (geometric_universal B (make_to_geo _ A f f_contr)) as h_ex.
        apply ex_singleton in h_ex as [h1 h1_eq].
        cbn in h1, h1_eq.
        unfold to_geo_set in h1_eq; cbn in h1_eq.
        pose (h2 (x : S_algebra) := h1 [x|]).
        assert (∀ u v, h2 (u + v) = h2 u + h2 v) as h2_plus.
        {
            intros u v.
            apply algebra_homo_plus.
        }
        assert (∀ a v, h2 (a · v) = a · h2 v) as h2_scalar.
        {
            intros a v.
            apply algebra_homo_scalar.
        }
        assert (∀ u v, h2 (u * v) = h2 u * h2 v) as h2_mult.
        {
            intros u v.
            apply algebra_homo_mult.
        }
        assert (h2 1 = 1) as h2_one.
        {
            apply algebra_homo_one.
        }
        exists (make_algebra_homomorphism
            _ _ _ h2 h2_plus h2_scalar h2_mult h2_one).
        intros x.
        cbn.
        unfold h2.
        unfold vector_to_S; cbn.
        apply h1_eq.
    -   intros [f1 f1_eq] [f2 f2_eq].
        rewrite set_type_eq2.
        apply algebra_homomorphism_eq.
        intros v.
        assert (∃ l : ulist (U * list V), v =
            ulist_sum (ulist_image (λ p, fst p · list_prod
            (list_image vector_to_S (snd p))) l)) as v_eq.
        {
            destruct v as [v [l v_eq]]; subst v.
            exists l.
            apply set_type_eq; cbn.
            induction l as [|v l] using ulist_induction.
            {
                do 2 rewrite ulist_image_end.
                do 2 rewrite ulist_sum_end.
                reflexivity.
            }
            do 2 rewrite ulist_image_add.
            do 2 rewrite ulist_sum_add.
            rewrite IHl.
            apply rplus.
            clear l IHl.
            destruct v as [a l]; cbn.
            unfold scalar_mult at 2; cbn.
            apply f_equal; clear a.
            induction l as [|a v].
            {
                do 2 rewrite list_image_end.
                do 2 rewrite list_prod_end.
                reflexivity.
            }
            do 2 rewrite list_image_add, list_prod_add.
            rewrite IHv.
            unfold mult at 2; cbn.
            reflexivity.
        }
        destruct v_eq as [l v_eq]; subst v.
        induction l as [|[a v] l] using ulist_induction.
        {
            rewrite ulist_image_end, ulist_sum_end.
            do 2 rewrite algebra_homo_zero.
            reflexivity.
        }
        rewrite ulist_image_add, ulist_sum_add; cbn.
        do 2 rewrite algebra_homo_plus.
        rewrite IHl.
        apply rplus.
        clear l IHl.
        do 2 rewrite algebra_homo_scalar.
        apply f_equal.
        induction v as [|v l].
        {
            rewrite list_image_end, list_prod_end.
            do 2 rewrite algebra_homo_one.
            reflexivity.
        }
        rewrite list_image_add, list_prod_add.
        do 2 rewrite algebra_homo_mult.
        rewrite IHl.
        apply rmult; clear l IHl.
        rewrite f1_eq, f2_eq.
        reflexivity.
Qed.

Theorem geo_sum : ∀ x, S x.
Proof.
    intros x.
    pose proof (initial_unique _ _ (geometric_universal B) (S_universal))
        as [[f f_eq] [[g g_eq] [fg gf]]].
    cbn in *.
    rewrite set_type_eq2 in fg.
    rewrite set_type_eq2 in gf.
    unfold to_geo_set in f_eq, g_eq.
    cbn in f_eq, g_eq.
    inversion fg as [fg_eq].
    inversion gf as [gf_eq].
    clear fg gf.
    pose proof (func_eq _ _ fg_eq) as fg.
    pose proof (func_eq _ _ gf_eq) as gf.
    cbn in fg, gf.
    clear fg_eq gf_eq.
    rewrite <- gf.
    pose proof [|f x] as [l l_eq].
    exists l.
    rewrite <- (gf (ulist_sum _)).
    apply f_equal.
    apply set_type_eq.
    rewrite l_eq; clear l_eq.
    induction l as [|[a v] l] using ulist_induction.
    {
        rewrite ulist_image_end.
        do 2 rewrite ulist_sum_end.
        rewrite algebra_homo_zero.
        reflexivity.
    }
    rewrite ulist_image_add.
    do 2 rewrite ulist_sum_add; cbn.
    rewrite algebra_homo_plus.
    unfold plus at 2; cbn.
    rewrite IHl.
    apply rplus.
    clear l IHl.
    rewrite algebra_homo_scalar.
    unfold scalar_mult at 2; cbn.
    apply f_equal.
    induction v as [|v l].
    {
        rewrite list_image_end, list_prod_end.
        rewrite algebra_homo_one.
        reflexivity.
    }
    rewrite list_image_add, list_prod_add.
    rewrite algebra_homo_mult.
    unfold mult at 2; cbn.
    rewrite IHl at 1.
    apply rmult.
    clear l IHl.
    rewrite f_eq.
    reflexivity.
Qed.

End GeometricSum.
