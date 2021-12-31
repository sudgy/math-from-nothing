Require Import init.

Require Import Coq.Init.Tactics.

Require Import tensor_product_universal.
Require Import tensor_product_isomorphisms.
Require Import tensor_product_assoc.
Require Import module_category.

Require Import nat.
Require Import set.
Require Import list.
Require Import unordered_list.
Require Import plus_sum.

Section TensorPower.

Context {F : CRing} (V : Module F).

Local Arguments cat_compose : simpl never.
Local Arguments cat_id : simpl never.

Infix "⊗" := tensor_product.

Fixpoint tensor_power (n : nat) :=
    match n with
    | nat_zero => cring_module F
    | nat_suc n' => V ⊗ tensor_power n'
    end.

Let TPP a := module_plus (tensor_power a).
Let TPZ a := module_zero (tensor_power a).
Let TPN a := module_neg (tensor_power a).
Let TPPC a := module_plus_comm (tensor_power a).
Let TPPA a := module_plus_assoc (tensor_power a).
Let TPPZ a := module_plus_lid (tensor_power a).
Let TPPN a := module_plus_linv (tensor_power a).
Let TPSM a := module_scalar (tensor_power a).
Let TPSMO a := module_scalar_id (tensor_power a).
Let TPSML a := module_scalar_ldist (tensor_power a).
Let TPSMR a := module_scalar_rdist (tensor_power a).
Let TPSMC a := module_scalar_comp (tensor_power a).
Let TP2P a b := module_plus (tensor_power a ⊗ tensor_power b).
Let TP2Z a b := module_zero (tensor_power a ⊗ tensor_power b).
Let TP2SM a b := module_scalar (tensor_power a ⊗ tensor_power b).

Existing Instances TPP TPZ TPN TPPC TPPA TPPZ TPPN TPSM TPSMO TPSML TPSMR TPSMC
    TP2P TP2Z TP2SM.

Record generic_tensor_power := make_generic_tensor_power {
    generic_tensor_power_n : nat;
    generic_tensor_power_t : module_V (tensor_power generic_tensor_power_n);
}.

Definition to_generic_tensor {n} (A : module_V (tensor_power n))
    := make_generic_tensor_power n A.

Definition tensor_power_nat_eq {m n : nat} (eq : m = n)
        : cat_morphism (MODULE F) (tensor_power m) (tensor_power n).
    rewrite eq.
    exact 𝟙.
Defined.

Theorem tensor_power_eq_generic : ∀ m n (eq : m = n) A B,
        to_generic_tensor A = to_generic_tensor B →
        module_homo_f (tensor_power_nat_eq eq) A = B.
    intros m n eq A B AB.
    (* I honestly don't know what I'm doing in this proof *)
    inversion AB.
    inversion_sigma.
    subst B.
    rewrite (proof_irrelevance H1_ eq).
    clear H0 H1_ AB.
    destruct eq; cbn.
    reflexivity.
Qed.

Theorem tensor_power_eq : ∀ n (A B : module_V (tensor_power n)),
        to_generic_tensor A = to_generic_tensor B → A = B.
    intros n A B eq.
    assert (n = n) as eq' by reflexivity.
    assert (module_homo_f (tensor_power_nat_eq eq') A = A) as eq2.
    {
        apply tensor_power_eq_generic.
        reflexivity.
    }
    rewrite <- eq2 at 1.
    apply tensor_power_eq_generic.
    exact eq.
Qed.

Lemma generic_tensor_eq_generic : ∀ m n (eq : m = n) A,
        to_generic_tensor (module_homo_f (tensor_power_nat_eq eq) A) =
        to_generic_tensor A.
    intros m n eq A.
    destruct eq.
    cbn.
    unfold cat_id; cbn.
    reflexivity.
Qed.

Lemma to_generic_tensor_plus : ∀ {m n}
        {A C : module_V (tensor_power m)}
        {B D : module_V (tensor_power n)},
        to_generic_tensor C = to_generic_tensor D →
        to_generic_tensor A = to_generic_tensor B →
        to_generic_tensor (A + C) = to_generic_tensor (B + D).
    intros m n A C B D CD AB.
    inversion AB.
    inversion CD.
    inversion_sigma.
    subst B D.
    rewrite (proof_irrelevance H3_ H1_).
    clear H3_ H0 H2 AB CD.
    destruct H1_; cbn.
    reflexivity.
Qed.

Fixpoint tensor_power_mult1 (n : nat)
    : cat_morphism (MODULE F) ((tensor_power n) ⊗ V) (tensor_power (nat_suc n))
:=
    match n with
    | nat_zero => tensor_product_comm_homo (cring_module F) V
    | nat_suc n' =>
        tensor_product_riso_homo V
            (tensor_power n' ⊗ V)
            (tensor_power (nat_suc n'))
            (tensor_power_mult1 n') ∘
        tensor_product_assoc_inv_homo V (tensor_power n') V
    end.

Fixpoint tensor_power_mult (m n : nat)
    : cat_morphism (MODULE F)
        (tensor_power m ⊗ tensor_power n)
        (tensor_power (m + n))
:=
    match n with
    | nat_zero =>
        tensor_power_nat_eq (Logic.eq_sym (plus_rid m)) ∘
        tensor_product_rid_homo (tensor_power m)
    | nat_suc n' =>
        tensor_power_mult (nat_suc m) n' ∘
        tensor_product_liso_homo
            (tensor_power m ⊗ V)
            (tensor_power (nat_suc m))
            (tensor_power n')
            (tensor_power_mult1 m) ∘
        tensor_product_assoc_homo
            (tensor_power m)
            V
            (tensor_power n')
    end.

Theorem tensor_power_mult1_iso :
        ∀ n, isomorphism (C0 := MODULE F) (tensor_power_mult1 n).
    intros n.
    induction n.
    -   cbn.
        apply tensor_product_comm_iso.
    -   cbn.
        apply compose_isomorphism.
        +   apply tensor_product_riso_iso.
            exact IHn.
        +   apply tensor_product_assoc_inv_iso.
Qed.

Theorem tensor_power_mult_iso :
        ∀ m n, isomorphism (C0 := MODULE F) (tensor_power_mult m n).
    intros m n.
    revert m.
    induction n; intros.
    -   cbn.
        apply compose_isomorphism.
        +   unfold tensor_power_nat_eq, Logic.eq_rect_r, Logic.eq_rect.
            destruct (Logic.eq_sym _).
            apply id_isomorphism.
        +   apply tensor_product_rid_iso.
    -   cbn.
        repeat apply compose_isomorphism.
        +   exact (IHn (nat_suc m)).
        +   apply tensor_product_liso_iso.
            apply tensor_power_mult1_iso.
        +   apply tensor_product_assoc_iso.
Qed.

Fixpoint vectors_to_power (l : list (module_V V))
    : module_V (tensor_power (list_size l))
:=  match l with
    | list_end => @one _ (cring_one F)
    | a :: l' => tensor_mult V (tensor_power (list_size l'))
        a (vectors_to_power l')
    end.

Let tensor_mult' {a b} A B
    := tensor_mult (tensor_power a) (tensor_power b) A B.

Local Infix "⊗'" := tensor_mult' (at level 40, no associativity).

Let f {a b} A := module_homo_f (tensor_power_mult a b) A.

Lemma f_plus : ∀ a b (A B : module_V (tensor_power a ⊗ tensor_power b)),
        f (A + B) = f A + f B.
    intros a b A B.
    unfold f.
    apply (@module_homo_plus _ _ _ (tensor_power_mult a b)).
Qed.
Lemma f_scalar : ∀ a b A (B : module_V (tensor_power a ⊗ tensor_power b)),
        f (A · B) = A · f B.
    intros a b A B.
    unfold f.
    apply (@module_homo_scalar _ _ _ (tensor_power_mult a b)).
Qed.
Lemma f_zero : ∀ a b,
        f (zero (U := module_V (tensor_power a ⊗ tensor_power b))) = 0.
    intros a b.
    apply module_homo_zero.
Qed.

Lemma tensor_ldist' :
    ∀ a b (A : module_V (tensor_power a)) (B C : module_V (tensor_power b)),
        A ⊗' (B + C) = A ⊗' B + A ⊗' C.
    intros a b A B C.
    apply tensor_ldist.
Qed.
Lemma tensor_rdist' :
    ∀ a b (A B : module_V (tensor_power a)) (C : module_V (tensor_power b)),
        (A + B) ⊗' C = A ⊗' C + B ⊗' C.
    intros a b A B C.
    apply tensor_rdist.
Qed.
Lemma tensor_lanni' :
    ∀ a b (A : module_V (tensor_power b)),
        (@zero _ (module_zero (tensor_power a))) ⊗' A =
        (@zero _ (module_zero (tensor_power a ⊗ tensor_power b))).
    intros a b A.
    apply tensor_product_lanni.
Qed.
Lemma tensor_ranni' :
    ∀ a b (A : module_V (tensor_power a)),
        A ⊗' (@zero _ (module_zero (tensor_power b))) =
        (@zero _ (module_zero (tensor_power a ⊗ tensor_power b))).
    intros a b A.
    apply tensor_product_ranni.
Qed.
Lemma tensor_lscalar' :
        ∀ α a b (A : module_V (tensor_power a)) (B : module_V (tensor_power b)),
        (α · A) ⊗' B = α · (A ⊗' B).
    intros α a b A B.
    apply tensor_lscalar.
Qed.
Lemma tensor_rscalar' :
        ∀ α a b (A : module_V (tensor_power a)) (B : module_V (tensor_power b)),
        A ⊗' (α · B) = α · (A ⊗' B).
    intros α a b A B.
    apply tensor_rscalar.
Qed.

Definition generic_tensor_mult (A B : generic_tensor_power) :=
    make_generic_tensor_power _ (f
    (tensor_mult _ _ (generic_tensor_power_t A) (generic_tensor_power_t B))).

Theorem generic_tensor_mult_eq : ∀ {m n}
        {v1 v2 : module_V V} {B1 : module_V (tensor_power m)}
        {B2 : module_V (tensor_power n)},
        v1 = v2 → to_generic_tensor B1 = to_generic_tensor B2 →
        @to_generic_tensor (nat_suc m) (tensor_mult _ _ v1 B1) =
        @to_generic_tensor (nat_suc n) (tensor_mult _ _ v2 B2).
    intros m n v1 v2 B1 B2 eq1 eq2.
    subst v2.
    inversion eq2.
    reflexivity.
Qed.

Theorem generic_tensor_scalar_eq : ∀ {m n}
        {A : module_V (tensor_power m)} {B : module_V (tensor_power n)} α,
        to_generic_tensor A = to_generic_tensor B →
        to_generic_tensor (α · A) = to_generic_tensor (α · B).
    intros m n A B α eq.
    inversion eq.
    reflexivity.
Qed.

Lemma to_generic_tensor_f_eq : ∀ {a1 a2 b1 b2 A1 A2 B1 B2},
        to_generic_tensor A1 = to_generic_tensor A2 →
        to_generic_tensor B1 = to_generic_tensor B2 →
        to_generic_tensor (@f a1 b1 (A1 ⊗' B1)) =
        to_generic_tensor (@f a2 b2 (A2 ⊗' B2)).
    intros a1 a2 b1 b2 A1 A2 B1 B2 eq1 eq2.
    inversion eq1.
    inversion eq2.
    reflexivity.
Qed.

Theorem vectors_to_power_mult : ∀ l1 l2,
        f (vectors_to_power l1 ⊗' vectors_to_power l2)
        = module_homo_f (tensor_power_nat_eq (list_size_plus l1 l2))
            (vectors_to_power (l1 ++ l2)).
    intros l1 l2.
    symmetry; apply tensor_power_eq_generic.
    revert l1.
    induction l2; intros.
    -   rewrite list_conc_end.
        cbn.
        unfold f; cbn.
        unfold zero at 4; cbn.
        destruct (Logic.eq_sym (plus_lid_rid_ (list_size l1))); cbn.
        rewrite cat_lid.
        change (module_homo_f (tensor_product_rid_homo _)) with
            (tensor_product_rid_f (tensor_power (list_size l1))).
        unfold tensor_mult'; rewrite (tensor_product_rid_eq (tensor_power _)).
        rewrite scalar_id.
        reflexivity.
    -   rewrite list_add_conc.
        rewrite list_conc_assoc.
        rewrite IHl2; clear IHl2.
        rewrite <- list_add_conc.
        unfold f at 2; cbn.
        unfold cat_compose; cbn.
        change (module_homo_f (tensor_product_assoc_homo _ _ _)) with
            (tensor_product_assoc_f (tensor_power (list_size l1)) V
                (tensor_power (list_size l2))).
        unfold tensor_mult' at 2;
            rewrite (tensor_product_assoc_eq (tensor_power (list_size l1))).
        change (module_homo_f (tensor_product_liso_homo _ _ _ _)) with
            (tensor_product_liso_f (tensor_power (list_size l1) ⊗ V)
                (V ⊗ tensor_power (list_size l1)) (tensor_power (list_size l2))
                (tensor_power_mult1 (list_size l1))).
        rewrite tensor_product_liso_eq.
        change (module_homo_f (tensor_power_mult _ _)) with
            (@f (nat_suc (list_size l1)) (list_size l2)).
        change (tensor_mult (V ⊗ tensor_power (list_size l1))
            (tensor_power (list_size l2))) with
            (@tensor_mult' (nat_suc (list_size l1)) (list_size l2)).
        assert (∀ l, nat_suc (list_size l) = list_size (l ++ a :: list_end)) as n_eq.
        {
            intros l.
            rewrite list_size_conc.
            reflexivity.
        }
        symmetry in n_eq.
        pose (X := module_homo_f (tensor_power_mult1 (list_size l1))
            (tensor_mult (tensor_power (list_size l1)) V (vectors_to_power l1)
            a)).
        change (module_homo_f (tensor_power_mult1 (list_size l1))
            (tensor_mult (tensor_power (list_size l1)) V (vectors_to_power l1)
            a)) with X.
        assert (module_homo_f (tensor_power_nat_eq (n_eq l1))
                (vectors_to_power (l1 ++ a :: list_end)) = X) as eq.
        {
            unfold X; clear X.
            induction l1.
            -   apply tensor_power_eq_generic.
                cbn.
                unfold zero at 6; cbn.
                change (module_homo_f (tensor_product_comm_homo _ _)) with
                    (tensor_product_comm_f (cring_module F) V).
                rewrite tensor_product_comm_eq.
                reflexivity.
            -   cbn.
                unfold cat_compose; cbn.
                fold (tensor_product_assoc_inv_f V (tensor_power (list_size l1)) V).
                rewrite tensor_product_assoc_inv_eq.
                fold (tensor_product_riso_f V (tensor_power (list_size l1) ⊗ V)
                    (V ⊗ tensor_power (list_size l1))
                    (tensor_power_mult1 (list_size l1))).
                rewrite tensor_product_riso_eq.
                pose (X := module_homo_f (tensor_power_mult1 (list_size l1))
                    (tensor_mult (tensor_power (list_size l1)) V
                    (vectors_to_power l1) a)).
                fold X in IHl1.
                change (module_homo_f (tensor_power_mult1 (list_size l1))
                    (tensor_mult (tensor_power (list_size l1)) V
                    (vectors_to_power l1) a)) with X.
                rewrite <- IHl1; clear IHl1 X.
                apply (tensor_power_eq_generic _ _ (n_eq (a0 :: l1))).
                change (V ⊗ tensor_power (list_size l1)) with
                    (tensor_power (nat_suc (list_size l1))).
                apply generic_tensor_mult_eq.
                1: reflexivity.
                rewrite generic_tensor_eq_generic.
                reflexivity.
        }
        rewrite <- eq; clear eq X.
        apply (@to_generic_tensor_f_eq
            (list_size (l1 ++ a :: list_end))
            (nat_suc (list_size l1))
        ).
        2: reflexivity.
        rewrite generic_tensor_eq_generic.
        reflexivity.
Qed.

Definition simple_tensor_power n (A : module_V (tensor_power n)) :=
    ∃ α (l : set_type (λ l : list (module_V V), list_size l = n)),
    A = α · module_homo_f (tensor_power_nat_eq [|l]) (vectors_to_power [l|]).

Theorem tensor_power_sum : ∀ {n} (A : module_V (tensor_power n)),
        ∃ l : ulist (set_type (simple_tensor_power n)),
        A = ulist_sum (ulist_image l (λ x, [x|])).
    intros n A.
    nat_induction n.
    -   assert (simple_tensor_power 0 A) as A_in.
        {
            unfold simple_tensor_power.
            exists A.
            assert (@list_size (module_V V) list_end = 0) as eq by reflexivity.
            exists [list_end|eq].
            cbn.
            rewrite <- @module_homo_scalar.
            unfold scalar_mult; cbn.
            unfold zero at 6; cbn.
            pose (X1 := cring_mult_lid).
            pose (X2 := cring_mult_comm).
            rewrite mult_rid.
            symmetry; apply tensor_power_eq_generic.
            reflexivity.
        }
        exists ([A|A_in] ::: ulist_end).
        rewrite ulist_image_add, ulist_sum_add.
        rewrite ulist_image_end, ulist_sum_end.
        rewrite plus_rid.
        reflexivity.
    -   cbn in A.
        pose proof (tensor_sum _ _ A) as [l l_eq]; subst A.
        induction l using ulist_induction.
        +   exists ulist_end.
            do 2 rewrite ulist_image_end.
            reflexivity.
        +   destruct IHl as [l' IHl].
            destruct a as [a' [a [A eq]]]; subst a'; cbn.
            specialize (IHn A) as [lA A_eq].
            assert (∀ B : set_type (simple_tensor_power n),
                simple_tensor_power (nat_suc n) (tensor_mult _ _ a [B|]))
                as a_in.
            {
                intros [B [α [Bl B_eq]]]; cbn.
                subst B.
                exists α.
                assert (list_size (a :: [Bl|]) = nat_suc n) as Bl_eq.
                {
                    cbn.
                    rewrite [|Bl].
                    reflexivity.
                }
                exists [a :: [Bl|]|Bl_eq].
                cbn.
                rewrite (tensor_rscalar V).
                apply f_equal.
                symmetry; apply (tensor_power_eq_generic _ _ Bl_eq).
                apply generic_tensor_mult_eq.
                1: reflexivity.
                rewrite generic_tensor_eq_generic.
                reflexivity.
            }
            pose (laA := ulist_image lA (λ x, [_|a_in x])).
            exists (laA +++ l').
            rewrite ulist_image_conc.
            change (V ⊗ tensor_power n) with (tensor_power (nat_suc n)).
            rewrite ulist_sum_plus.
            rewrite <- IHl; clear IHl.
            rewrite ulist_image_add, ulist_sum_add; cbn.
            apply rplus.
            rewrite A_eq.
            unfold laA.
            rewrite ulist_image_comp; cbn.
            clear A A_eq laA a_in.
            induction lA using ulist_induction.
            *   do 2 rewrite ulist_image_end, ulist_sum_end.
                apply tensor_product_ranni.
            *   do 2 rewrite ulist_image_add, ulist_sum_add.
                rewrite (tensor_ldist V).
                apply lplus.
                exact IHlA.
Qed.

Lemma tensor_power_rscalar : ∀ n
        (A : module_V (tensor_power n)) (B : module_V (tensor_power 0)),
        module_homo_f (tensor_power_nat_eq (plus_rid n)) (f (A ⊗' B)) = B · A.
    intros n A B.
    apply tensor_power_eq_generic.
    unfold f; cbn.
    unfold zero at 4; cbn.
    destruct (Logic.eq_sym (plus_lid_rid_ n)); cbn.
    rewrite cat_lid.
    change (module_homo_f (tensor_product_rid_homo _)) with
        (tensor_product_rid_f (tensor_power n)).
    unfold tensor_mult'; rewrite (tensor_product_rid_eq (tensor_power n)).
    reflexivity.
Qed.

Lemma tensor_power_lscalar : ∀ n
        (A : module_V (tensor_power 0)) (B : module_V (tensor_power n)),
        f (A ⊗' B) = A · B.
    intros n A B.
    pose proof (tensor_power_sum A) as [lA A_eq].
    pose proof (tensor_power_sum B) as [lB B_eq].
    subst A B.
    induction lB as [|B lB] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite tensor_ranni'.
        rewrite scalar_ranni.
        apply module_homo_zero.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite tensor_ldist'.
    rewrite f_plus.
    rewrite scalar_ldist.
    rewrite IHlB; clear IHlB.
    apply rplus; clear lB.
    induction lA as [|A lA] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite tensor_lanni'.
        rewrite scalar_lanni.
        apply module_homo_zero.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite tensor_rdist'.
    rewrite f_plus.
    rewrite scalar_rdist.
    rewrite IHlA; clear IHlA.
    apply rplus; clear lA.
    destruct A as [A' [α [lA A_eq]]]; subst A'; cbn.
    destruct B as [B' [β [lB B_eq]]]; subst B'; cbn.
    rewrite tensor_lscalar', tensor_rscalar'.
    do 2 rewrite f_scalar.
    pose (UM := cring_mult).
    pose (UMC := cring_mult_comm).
    unfold scalar_mult at 4; cbn.
    unfold zero at 15; cbn.
    rewrite <- scalar_comp.
    apply f_equal.
    rewrite (scalar_comp _ β).
    rewrite (mult_comm _ β).
    rewrite <- scalar_comp.
    apply f_equal.
    apply tensor_power_eq.
    pose proof (generic_tensor_eq_generic _ _ [|lA] (vectors_to_power [lA|])) as eq1.
    pose proof (generic_tensor_eq_generic _ _ [|lB] (vectors_to_power [lB|])) as eq2.
    rewrite (to_generic_tensor_f_eq eq1 eq2); clear eq1 eq2.
    rewrite vectors_to_power_mult.
    rewrite generic_tensor_eq_generic.
    destruct lA as [lA lA_size]; cbn.
    destruct lA.
    2: inversion lA_size.
    cbn.
    cbn in lA_size.
    assert (module_homo_f (tensor_power_nat_eq lA_size) (@one _ (cring_one F))
        = (@one _ (cring_one F))) as eq.
    {
        apply tensor_power_eq_generic.
        reflexivity.
    }
    rewrite eq; clear eq.
    rewrite scalar_id.
    rewrite generic_tensor_eq_generic.
    reflexivity.
Qed.

Theorem tensor_power_mult_assoc : ∀ a b c A B C,
    module_homo_f (tensor_power_nat_eq (plus_assoc _ _ _))
    (module_homo_f (tensor_power_mult a (b + c))
        (tensor_mult (tensor_power a) (tensor_power (b + c))
            A
            (module_homo_f (tensor_power_mult b c)
                (tensor_mult (tensor_power b) (tensor_power c) B C))))
    =
    module_homo_f (tensor_power_mult (a + b) c)
        (tensor_mult (tensor_power (a + b)) (tensor_power c)
            (module_homo_f (tensor_power_mult a b)
                (tensor_mult (tensor_power a) (tensor_power b) A B))
            C).
    intros a b c A B C.
    apply tensor_power_eq_generic.
    cbn.
    change (tensor_mult (tensor_power a) (tensor_power b) A B)
        with (tensor_mult' A B).
    change (tensor_mult (tensor_power b) (tensor_power c) B C)
        with (tensor_mult' B C).
    change (module_homo_f (tensor_power_mult a b) (A ⊗' B)) with (f (A ⊗' B)).
    change (module_homo_f (tensor_power_mult b c) (B ⊗' C)) with (f (B ⊗' C)).
    change (tensor_mult (tensor_power a) (tensor_power (b + c)) A (f (B ⊗' C)))
        with (tensor_mult' A (f (B ⊗' C))).
    change (tensor_mult (tensor_power (a + b)) (tensor_power c) (f (A ⊗' B)) C)
        with (tensor_mult' (f (A ⊗' B)) C).
    change (module_homo_f (tensor_power_mult a (b + c)) (A ⊗' (f (B ⊗' C))))
        with (f (A ⊗' (f (B ⊗' C)))).
    change (module_homo_f (tensor_power_mult (a + b) c) (f (A ⊗' B) ⊗' C))
        with (f (f (A ⊗' B) ⊗' C)).
    pose proof (tensor_power_sum A) as [lA A_eq]; subst A.
    induction lA as [|A lA] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite tensor_lanni'.
        do 2 rewrite f_zero.
        rewrite tensor_lanni'.
        rewrite f_zero.
        rewrite plus_assoc.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    do 2 rewrite tensor_rdist'.
    do 2 rewrite f_plus.
    rewrite tensor_rdist'.
    rewrite f_plus.
    apply (to_generic_tensor_plus IHlA); clear IHlA lA.
    pose proof (tensor_power_sum B) as [lB B_eq]; subst B.
    induction lB as [|B lB] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        rewrite tensor_lanni'.
        rewrite tensor_ranni'.
        do 2 rewrite f_zero.
        rewrite tensor_lanni'.
        rewrite tensor_ranni'.
        do 2 rewrite f_zero.
        rewrite plus_assoc.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    rewrite tensor_ldist'.
    rewrite tensor_rdist'.
    do 2 rewrite f_plus.
    rewrite tensor_rdist'.
    rewrite f_plus.
    rewrite tensor_ldist'.
    rewrite f_plus.
    apply (to_generic_tensor_plus IHlB); clear IHlB lB.
    pose proof (tensor_power_sum C) as [lC C_eq]; subst C.
    induction lC as [|C lC] using ulist_induction.
    {
        rewrite ulist_image_end, ulist_sum_end.
        do 2 rewrite tensor_ranni'.
        do 2 rewrite f_zero.
        rewrite tensor_ranni'.
        rewrite f_zero.
        rewrite plus_assoc.
        reflexivity.
    }
    rewrite ulist_image_add, ulist_sum_add.
    do 2 rewrite tensor_ldist'.
    do 2 rewrite f_plus.
    rewrite tensor_ldist'.
    rewrite f_plus.
    apply (to_generic_tensor_plus IHlC); clear IHlC lC.
    destruct A as [A' [α [lA A_eq]]]; cbn.
    remember (vectors_to_power [lA|]) as A.
    destruct B as [B' [β [lB B_eq]]]; cbn.
    remember (vectors_to_power [lB|]) as B.
    destruct C as [C' [γ [lC C_eq]]]; cbn.
    remember (vectors_to_power [lC|]) as C.
    subst A' B' C'.
    do 2 rewrite tensor_lscalar'.
    rewrite tensor_rscalar'.
    do 3 rewrite f_scalar.
    do 2 rewrite tensor_rscalar'.
    do 2 rewrite f_scalar.
    rewrite tensor_lscalar'.
    rewrite (tensor_rscalar' β).
    do 2 rewrite f_scalar.
    do 2 rewrite tensor_lscalar'.
    rewrite tensor_rscalar'.
    do 3 rewrite f_scalar.
    do 3 apply generic_tensor_scalar_eq.
    pose proof (generic_tensor_eq_generic _ _ [|lA] A) as eq1.
    pose proof (generic_tensor_eq_generic _ _ [|lB] B) as eq2.
    pose proof (generic_tensor_eq_generic _ _ [|lC] C) as eq3.
    pose proof (to_generic_tensor_f_eq eq1 eq2) as eq12.
    pose proof (to_generic_tensor_f_eq eq2 eq3) as eq23.
    rewrite (to_generic_tensor_f_eq eq1 eq23).
    rewrite (to_generic_tensor_f_eq eq12 eq3).
    clear eq1 eq2 eq3 eq12 eq23.
    subst A B C.
    rewrite vectors_to_power_mult.
    pose proof (generic_tensor_eq_generic _ _ (list_size_plus [lB|] [lC|])
        (vectors_to_power ([lB|] ++ [lC|]))) as eq.
    rewrite (to_generic_tensor_f_eq (Logic.eq_refl _) eq); clear eq.
    rewrite vectors_to_power_mult.
    rewrite generic_tensor_eq_generic.
    rewrite vectors_to_power_mult.
    pose proof (generic_tensor_eq_generic _ _ (list_size_plus [lA|] [lB|])
        (vectors_to_power ([lA|] ++ [lB|]))) as eq.
    rewrite (to_generic_tensor_f_eq eq (Logic.eq_refl _)); clear eq.
    rewrite vectors_to_power_mult.
    rewrite generic_tensor_eq_generic.
    rewrite list_conc_assoc.
    reflexivity.
Qed.

End TensorPower.
