Require Import init.

Require Export linear_base.
Require Import linear_multilinear.
Require Import nat.
Require Import card.
Require Import set.
Require Import list.
Require Import plus_sum.

(** This is a very diffenent definition of a tensor algebra than usual.  Really,
I'm trying to beeline to constructing geometric algebra, so I'm only doing what
is absolutely necessary to reach that goal.  This construction is much easier to
deal with than the traditional constructions.
*)

Section TensorAlgebra.

Variables U V : Type.

Context `{
    UP : Plus U,
    UZ : Zero U,
    UN : Neg U,
    @PlusComm U UP,
    @PlusAssoc U UP,
    @PlusLid U UP UZ,
    @PlusLinv U UP UZ UN,
    UM : Mult U,
    UO : One U,
    @Ldist U UP UM,
    @MultComm U UM,
    @MultAssoc U UM,
    @MultLid U UM UO,

    VP : Plus V,
    VZ : Zero V,
    VN : Neg V,
    @PlusComm V VP,
    @PlusAssoc V VP,
    @PlusLid V VP VZ,
    @PlusLinv V VP VZ VN,

    SM : ScalarMult U V,
    @ScalarId U V UO SM,
    @ScalarLdist U V VP SM,
    @ScalarRdist U V UP VP SM
}.

Existing Instance multilinear_plus.
Existing Instance multilinear_plus_comm.
Existing Instance multilinear_plus_assoc.
Existing Instance multilinear_zero.
Existing Instance multilinear_plus_lid.
Existing Instance multilinear_neg.
Existing Instance multilinear_plus_linv.
Existing Instance multilinear_scalar_mult.
Existing Instance multilinear_scalar_comp.
Existing Instance multilinear_scalar_id.
Existing Instance multilinear_scalar_ldist.
Existing Instance multilinear_scalar_rdist.

Local Open Scope card_scope.

(* TODO: Generalize this inifinite direct product to more general situations *)
Definition tensor_algebra_base := (∀ k, multilinear_type k).
Definition tensor_finite (A : tensor_algebra_base) :=
    finite (|set_type (λ k, 0 ≠ A k)|).
Definition tensor_algebra := set_type tensor_finite.

Definition multilinear_type_k_eq k n (A : multilinear_type k) (eq : n = k) :
        (multilinear_type n).
    rewrite eq.
    exact A.
Defined.

Definition multilinear_to_tensor_base {k} (A : multilinear_type k) :
    tensor_algebra_base := λ n, match (strong_excluded_middle (n = k)) with
    | strong_or_left H => multilinear_type_k_eq k n A H
    | _ => 0
    end.

Lemma multilinear_to_tensor_finite {k} :
        ∀ A : multilinear_type k, tensor_finite (multilinear_to_tensor_base A).
    intros A.
    apply (le_lt_trans2 (nat_is_finite 1)).
    unfold nat_to_card, le; equiv_simpl.
    exists (λ _, [0|nat_0_lt_1]).
    intros [a a_neq] [b b_neq] eq; clear eq.
    unfold multilinear_to_tensor_base in *.
    apply set_type_eq; cbn.
    classic_case (a = k) as [ak|ak];
    classic_case (b = k) as [bk|bk].
    1: subst; reflexivity.
    all: contradiction.
Qed.

Definition multilinear_to_tensor {k} (A : multilinear_type k) :=
    [_|multilinear_to_tensor_finite A].

Lemma tensor_plus_finite : ∀ A B : tensor_algebra,
        tensor_finite (λ k, [A|] k + [B|] k).
    intros [A A_fin] [B B_fin]; cbn.
    apply fin_nat_ex in A_fin as [m m_eq].
    apply fin_nat_ex in B_fin as [n n_eq].
    assert (finite (nat_to_card m + nat_to_card n)) as mn_fin.
    {
        rewrite nat_to_card_plus.
        apply nat_is_finite.
    }
    apply (le_lt_trans2 mn_fin).
    rewrite m_eq, n_eq.
    clear m m_eq n n_eq mn_fin.
    unfold plus at 2, le; equiv_simpl.
    assert (∀ (n : set_type (λ k, 0 ≠ A k + B k)), {0 ≠ A [n|]} + {0 ≠ B [n|]})
        as n_in.
    {
        intros [n n_neq]; cbn.
        classic_case (0 = A n) as [Anz|Anz].
        -   right.
            rewrite <- Anz in n_neq.
            rewrite plus_lid in n_neq.
            exact n_neq.
        -   left; exact Anz.
    }
    exists (λ n, match (n_in n) with
        | strong_or_left  H => inl [[n|]|H]
        | strong_or_right H => inr [[n|]|H]
    end).
    intros a b eq.
    destruct (n_in a) as [neq1|neq1]; destruct (n_in b) as [neq2|neq2].
    all: inversion eq as [eq2].
    all: apply set_type_eq; exact eq2.
Qed.

Instance tensor_plus : Plus tensor_algebra := {
    plus A B := [_|tensor_plus_finite A B]
}.

Program Instance tensor_plus_comm : PlusComm tensor_algebra.
Next Obligation.
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_comm.
Qed.

Program Instance tensor_plus_assoc : PlusAssoc tensor_algebra.
Next Obligation.
    unfold plus; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_assoc.
Qed.

Lemma tensor_zero_finite : tensor_finite (λ k, 0).
    unfold tensor_finite.
    assert (|set_type (λ k : nat, (zero (U := multilinear_type k)) ≠ 0)| = 0)
        as eq.
    {
        apply card_false_0.
        intros [a neq].
        contradiction.
    }
    rewrite eq.
    apply nat_is_finite.
Qed.

Instance tensor_zero : Zero tensor_algebra := {
    zero := [_|tensor_zero_finite]
}.

Program Instance tensor_plus_lid : PlusLid tensor_algebra.
Next Obligation.
    unfold plus, zero; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_lid.
Qed.

Lemma tensor_neg_finite : ∀ A : tensor_algebra, tensor_finite (λ k, -[A|] k).
    intros [A A_fin]; cbn.
    apply fin_nat_ex in A_fin as [n n_eq].
    apply (le_lt_trans2 (nat_is_finite n)).
    rewrite n_eq; clear n n_eq.
    unfold le; equiv_simpl.
    assert (∀ (n : set_type (λ k, 0 ≠ - A k)), 0 ≠ A [n|]) as n_in.
    {
        intros [n n_neq]; cbn.
        intros eq.
        rewrite <- eq in n_neq.
        rewrite neg_zero in n_neq.
        contradiction.
    }
    exists (λ n, [[n|]|n_in n]).
    intros a b eq.
    apply eq_set_type in eq; cbn in eq.
    apply set_type_eq in eq; cbn in eq.
    exact eq.
Qed.

Instance tensor_neg : Neg tensor_algebra := {
    neg A := [_|tensor_neg_finite A]
}.

Program Instance tensor_plus_linv : PlusLinv tensor_algebra.
Next Obligation.
    unfold plus, neg, zero; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply plus_linv.
Qed.

Lemma tensor_scalar_finite : ∀ α (A : tensor_algebra),
        tensor_finite (λ k, α · [A|] k).
    intros α [A A_fin]; cbn.
    apply fin_nat_ex in A_fin as [n n_eq].
    apply (le_lt_trans2 (nat_is_finite n)).
    rewrite n_eq; clear n n_eq.
    unfold le; equiv_simpl.
    assert (∀ (n : set_type (λ k, 0 ≠ α · A k)), 0 ≠ A [n|]) as n_in.
    {
        intros [n n_neq]; cbn.
        intros eq.
        rewrite <- eq in n_neq.
        rewrite scalar_ranni in n_neq.
        contradiction.
    }
    exists (λ n, [[n|]|n_in n]).
    intros a b eq.
    apply eq_set_type in eq; cbn in eq.
    apply set_type_eq in eq; cbn in eq.
    exact eq.
Qed.

Instance tensor_scalar : ScalarMult U tensor_algebra := {
    scalar_mult α A := [_|tensor_scalar_finite α A]
}.

Program Instance tensor_scalar_comp : ScalarComp U tensor_algebra.
Next Obligation.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_comp.
Qed.

Program Instance tensor_scalar_id : ScalarId U tensor_algebra.
Next Obligation.
    unfold scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_id.
Qed.

Program Instance tensor_scalar_ldist : ScalarLdist U tensor_algebra.
Next Obligation.
    unfold plus, scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_ldist.
Qed.

Program Instance tensor_scalar_rdist : ScalarRdist U tensor_algebra.
Next Obligation.
    unfold plus at 2, scalar_mult; cbn.
    apply set_type_eq; cbn.
    apply functional_ext.
    intros n.
    apply scalar_rdist.
Qed.
(*
Definition tensor_grade (A : tensor_algebra) k := ∀ n, n ≠ k → 0 = [A|] n.
*)
Lemma tensor_grade_project_finite : ∀ (A : tensor_algebra) k,
        tensor_finite (λ n, If n = k then [A|] n else 0).
    intros [A A_fin] k; cbn.
    apply (le_lt_trans2 (nat_is_finite 1)).
    unfold nat_to_card, le; equiv_simpl.
    exists (λ x, [0|nat_0_lt_1]).
    intros [a a_eq] [b b_eq] eq; clear eq.
    apply set_type_eq; cbn.
    do 2 case_if.
    -   subst.
        reflexivity.
    -   contradiction.
    -   contradiction.
    -   contradiction.
Qed.

Definition tensor_grade_project (A : tensor_algebra) k :=
    [_|tensor_grade_project_finite A k].
(*
Theorem tensor_grade_project_eq : ∀ A k,
    [tensor_grade_project A k|] = [A|] k.
*)
Definition homogeneous_tensor A := ∃ k (M : multilinear_type k),
    A = multilinear_to_tensor M.

Theorem tensor_project_homogeneous :
        ∀ A k, homogeneous_tensor (tensor_grade_project A k).
    intros A k.
    exists k, ([A|] k).
    apply set_type_eq; cbn.
    unfold multilinear_to_tensor_base; cbn.
    apply functional_ext.
    intros x.
    classic_case (x = k) as [eq|neq].
    -   unfold multilinear_type_k_eq; cbn.
        subst; cbn.
        reflexivity.
    -   reflexivity.
Qed.

Theorem tensor_decompose_grade : ∀ A,
        ∃ (l : list (set_type homogeneous_tensor)),
        A = list_sum (list_image l (λ x, [x|])).
    intros a.
    destruct a as [af af_fin].

    classic_case (∃ k, 0 ≠ af k) as [af_nz|af_z].
    2: {
        rewrite not_ex in af_z.
        setoid_rewrite not_not in af_z.
        exists list_end.
        apply set_type_eq; cbn.
        unfold zero; cbn.
        apply functional_ext.
        intros x.
        rewrite af_z.
        reflexivity.
    }
    pose proof (finite_well_ordered_set_max _ af_fin af_nz)
        as [n [n_nz n_greatest]].
    exists (func_to_list
        (λ k, [_|tensor_project_homogeneous [af|af_fin] k]) (nat_suc n)).
    apply set_type_eq; cbn.
    apply functional_ext.
    intros x.
    unfold plus; cbn.
    assert ([list_sum
       (list_image (A := set_type homogeneous_tensor)
          (func_to_list
             (λ k : nat,
                [tensor_grade_project [af | af_fin] k
                | tensor_project_homogeneous [af | af_fin] k]) n)
          (λ x0 : set_type homogeneous_tensor, [x0 | ])) | ] x =
          list_sum
              (func_to_list (λ k, [tensor_grade_project [af | af_fin] k|] x) n))
        as eq.
    {
        clear n_nz n_greatest.
        nat_induction n.
        -   unfold zero; cbn.
            reflexivity.
        -   cbn in *.
            rewrite <- IHn.
            unfold plus at 1; cbn.
            reflexivity.
    }
    rewrite eq; clear eq.
    cbn.
    clear af_nz n_nz.
    revert af af_fin n_greatest.
    nat_induction n.
    -   intros.
        unfold zero at 8; cbn.
        rewrite plus_rid.
        case_if.
        +   reflexivity.
        +   symmetry; classic_contradiction contr.
            specialize (n_greatest _ contr).
            apply nat_le_zero_eq in n_greatest.
            symmetry in n_greatest; contradiction.
    -   intros.
        cbn.
        pose (af' := [af|af_fin]-tensor_grade_project [af|af_fin] (nat_suc n)).
        assert (∀ y, 0 ≠ [af'|] y → y <= n) as af'_n_greatest.
        {
            clear IHn.
            intros y neq.
            rewrite <- nat_lt_suc_le.
            split.
            -   apply n_greatest.
                unfold af' in neq.
                unfold tensor_grade_project, plus, neg in neq; cbn in neq.
                case_if.
                +   rewrite plus_rinv in neq.
                    contradiction.
                +   rewrite neg_zero, plus_rid in neq.
                    exact neq.
            -   intros contr; subst y.
                apply neq; clear neq.
                unfold af'.
                unfold tensor_grade_project; cbn.
                unfold zero; cbn.
                apply set_type_eq; cbn.
                apply functional_ext.
                intros y.
                unfold plus, neg; cbn.
                case_if.
                +   rewrite plus_rinv.
                    reflexivity.
                +   contradiction.
        }
        specialize (IHn [af'|] [|af'] af'_n_greatest).
        assert (af x = [af'|] x
                + [tensor_grade_project [af|af_fin] (nat_suc n)|] x)
            as eq.
        {
            unfold af'.
            unfold plus at 2; cbn.
            unfold neg; cbn.
            rewrite plus_rlinv.
            reflexivity.
        }
        rewrite eq; clear eq.
        rewrite plus_comm.
        rewrite IHn at 1; clear IHn.
        cbn.
        apply f_equal2.
        2: apply f_equal2.
        +   unfold af', tensor_grade_project; cbn.
            unfold plus at 2, neg; cbn.
            case_if.
            *   rewrite plus_rinv, plus_rid.
                reflexivity.
            *   reflexivity.
        +   unfold af', tensor_grade_project; cbn.
            unfold plus at 1 3, neg; cbn.
            case_if.
            *   subst.
                case_if.
                --  contradiction (nat_neq_suc _ e).
                --  rewrite neg_zero, plus_rid.
                    rewrite plus_lid.
                    reflexivity.
            *   reflexivity.
        +   unfold af', tensor_grade_project; cbn.
            unfold plus at 1 3, neg; cbn.
            apply f_equal.
            apply func_to_list_eq.
            intros m m_lt.
            case_if.
            2: reflexivity.
            case_if.
            *   exfalso; clear - m_lt e e0.
                subst.
                rewrite <- nle_lt in m_lt.
                apply m_lt.
                apply nat_le_suc.
            *   rewrite neg_zero, plus_rid, plus_lid.
                reflexivity.
Qed.

Instance tensor_mult : Mult tensor_algebra := {
    mult A B := list_sum (list_prod2 (λ A' B',
        (multilinear_to_tensor (multilinear_mult
            (ex_val (ex_proof [|A']))
            (ex_val (ex_proof [|B']))
        ))) (ex_val (tensor_decompose_grade A))
            (ex_val (tensor_decompose_grade B)))
}.

End TensorAlgebra.
