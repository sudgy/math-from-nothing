Require Import init.

Require Import zorn_real_base.
Require Import zorn_real_arch.

Require Import preorder.
Require Import order_def.
Require Import set.
Require Import nat_abstract.

Module AofZornUb.
Section AofZornUb.

Variable F : ArchOrderedField → Prop.
Variable F_chain : is_chain le F.

Section NotEmpty.

Variable F' : set_type F.

Lemma F_chain2 : ∀ A B : set_type F, {[A|] <= [B|]} + {[B|] <= [A|]}.
Proof.
    intros A B.
    apply or_to_strong.
    apply F_chain.
    -   exact [|A].
    -   exact [|B].
Qed.

Record ub_base := make_ub_base {
    ub_A : set_type F;
    ub_x : set_type (aof_set [ub_A|]);
}.

Lemma ub_base_max : ∀ B C : set_type F, ∃ (A : set_type F) f g,
    arch_ordered_homo [B|] [A|] f ∧
    arch_ordered_homo [C|] [A|] g.
Proof.
    intros B C.
    destruct (F_chain2 B C) as [[f f_homo]|[f f_homo]].
    -   exists C, f, identity.
        split.
        +   exact f_homo.
        +   apply identity_arch_ordered_homo.
    -   exists B, identity, f.
        split.
        +   apply identity_arch_ordered_homo.
        +   exact f_homo.
Qed.

Section Eq.

Definition ub_eq (a b : ub_base) := ∀ (A : set_type F) f g,
    arch_ordered_homo [ub_A a|] [A|] f → arch_ordered_homo [ub_A b|] [A|] g
    → f (ub_x a) = g (ub_x b).
Local Infix "~" := ub_eq.

Local Program Instance ub_eq_reflexive : Reflexive ub_eq.
Next Obligation.
    intros A f g f_homo g_homo.
    apply arch_ordered_homo_eq; assumption.
Qed.

Local Program Instance ub_eq_symmetric : Symmetric ub_eq.
Next Obligation.
    rename H into eq.
    intros A f g f_homo g_homo.
    symmetry.
    apply eq; assumption.
Qed.

Local Program Instance ub_eq_transitive : Transitive ub_eq.
Next Obligation.
    rename H into xy, H0 into yz.
    unfold ub_eq in *.
    intros A f g f_homo g_homo.
    destruct (F_chain2 A (ub_A y)) as [[h h_homo]|[h h_homo]].
    -   specialize (xy (ub_A y) (λ x, h (f x)) identity).
        specialize (yz (ub_A y) identity (λ x, h (g x))).
        prove_parts xy.
        3: prove_parts yz.
        2, 3: apply identity_arch_ordered_homo.
        1, 2: apply arch_ordered_homo_compose.
        1, 2, 3, 4: assumption.
        unfold identity in *; cbn in xy, yz.
        rewrite yz in xy.
        apply arch_ordered_homo_inj in xy; [>|exact h_homo].
        exact xy.
    -   specialize (xy A f h f_homo h_homo).
        specialize (yz A h g h_homo g_homo).
        rewrite yz in xy.
        exact xy.
Qed.

End Eq.

Local Existing Instances ub_eq_reflexive ub_eq_symmetric ub_eq_transitive.

Definition ub_equiv := make_equiv _
        ub_eq_reflexive ub_eq_symmetric ub_eq_transitive.

Local Notation "'ub'" := (equiv_type ub_equiv).
Local Infix "~" := (eq_equal ub_equiv).

Definition ub_bin
    (op : ∀ F, set_type (aof_set F) →
               set_type (aof_set F) →
               set_type (aof_set F))
    (a b : ub_base) :=
    match (F_chain2 (ub_A a) (ub_A b)) with
    | strong_or_left H => make_ub_base
        (ub_A b)
        (op [ub_A b|] (ex_val H (ub_x a)) (ub_x b))
    | strong_or_right H => make_ub_base
        (ub_A a)
        (op [ub_A a|] (ub_x a) (ex_val H (ub_x b)))
    end.

Lemma ub_bin_eq : ∀ op a b,
    (∀ F G f x y, arch_ordered_homo F G f → f (op F x y) = op G (f x) (f y)) →
    ∀ (A : set_type F) f g,
    arch_ordered_homo [ub_A a|] [A|] f → arch_ordered_homo [ub_A b|] [A|] g →
    ub_bin op a b ~ make_ub_base A (op [A|] (f (ub_x a)) (g (ub_x b))).
Proof.
    intros op a b op_homo A f g f_homo g_homo.
    unfold ub_bin.
    destruct (F_chain2 (ub_A a) (ub_A b)) as [leq|leq].
    all: rewrite_ex_val h h_homo.
    all: cbn; unfold ub_eq; cbn.
    all: intros B i j i_homo j_homo.
    -   rewrite op_homo by exact i_homo.
        rewrite op_homo by exact j_homo.
        apply f_equal2.
        1: apply (arch_ordered_homo_eq (λ x, i (h x)) (λ x, j (f x))).
        3: apply (arch_ordered_homo_eq i (λ x, j (g x))).
        1, 2, 4: apply arch_ordered_homo_compose.
        all: assumption.
    -   rewrite op_homo by exact i_homo.
        rewrite op_homo by exact j_homo.
        apply f_equal2.
        1: apply (arch_ordered_homo_eq i (λ x, j (f x))).
        3: apply (arch_ordered_homo_eq (λ x, i (h x)) (λ x, j (g x))).
        2, 3, 4: apply arch_ordered_homo_compose.
        all: assumption.
Qed.

Lemma ub_bin_wd : ∀ op a b c d,
    (∀ F G f x y, arch_ordered_homo F G f → f (op F x y) = op G (f x) (f y)) →
    a ~ b → c ~ d → ub_bin op a c ~ ub_bin op b d.
Proof.
    intros op a b c d op_homo ab cd.
    pose proof (ub_base_max (ub_A a) (ub_A c)) as [A [f [g [f_homo g_homo]]]].
    pose proof (ub_bin_eq op a c op_homo A f g f_homo g_homo) as eq1.
    pose proof (ub_base_max (ub_A b) (ub_A d)) as [B [h [i [h_homo i_homo]]]].
    pose proof (ub_bin_eq op b d op_homo B h i h_homo i_homo) as eq2.
    apply sym in eq2.
    apply (trans eq1).
    apply (trans2 eq2).
    clear eq1 eq2.
    intros C j k j_homo k_homo; cbn in *.
    rewrite op_homo by exact j_homo.
    rewrite op_homo by exact k_homo.
    apply f_equal2.
    -   apply (ab _ (λ x, j (f x)) (λ x, k (h x))).
        all: apply arch_ordered_homo_compose; assumption.
    -   apply (cd _ (λ x, j (g x)) (λ x, k (i x))).
        all: apply arch_ordered_homo_compose; assumption.
Qed.

(* The reason for proving associativity in general but not the other
* properties common to addition and subtraction is that associativity is the
* only one with a long enough proof to make the extra work for generalization
* worthwhile *)
Lemma ub_bin_assoc : ∀ op,
    (∀ F G f x y, arch_ordered_homo F G f → f (op F x y) = op G (f x) (f y)) →
    (∀ F x y z, op F x (op F y z) = op F (op F x y) z) →
    ∀ a b c, ub_bin op a (ub_bin op b c) ~ ub_bin op (ub_bin op a b) c.
Proof.
    intros op op_homo op_assoc a b c.
    pose proof (ub_base_max (ub_A b) (ub_A c))
        as [BC [bcf [bcg [bcf_homo bcg_homo]]]].
    pose proof (ub_base_max (ub_A a) BC)
        as [A_BC [a_bcf [a_bcg [a_bcf_homo a_bcg_homo]]]].
    pose proof (ub_bin_eq _ b c op_homo BC bcf bcg bcf_homo bcg_homo) as eq1.
    cbn in eq1.
    pose proof (refl a) as eq2.
    pose proof (ub_bin_wd op _ _ _ _ op_homo eq2 eq1) as eq3.
    apply (trans eq3).
    clear eq1 eq2 eq3.
    pose (bc := make_ub_base BC (op [BC|] (bcf (ub_x b)) (bcg (ub_x c)))).
    pose proof (ub_bin_eq _ a bc op_homo _
        a_bcf a_bcg a_bcf_homo a_bcg_homo) as eq1.
    apply (trans eq1); cbn.
    clear eq1.

    pose proof (ub_base_max (ub_A a) (ub_A b))
        as [AB [abf [abg [abf_homo abg_homo]]]].
    pose proof (ub_base_max AB (ub_A c))
        as [AB_C [ab_cf [ab_cg [ab_cf_homo ab_cg_homo]]]].
    pose proof (ub_bin_eq _ a b op_homo AB abf abg abf_homo abg_homo) as eq1.
    cbn in eq1.
    pose proof (refl c) as eq2.
    pose proof (ub_bin_wd op _ _ _ _ op_homo eq1 eq2) as eq3.
    apply sym in eq3.
    apply (trans2 eq3).
    clear eq1 eq2 eq3.
    pose (ab := make_ub_base AB (op [AB|] (abf (ub_x a)) (abg (ub_x b)))).
    pose proof (ub_bin_eq _ ab c op_homo _
        ab_cf ab_cg ab_cf_homo ab_cg_homo) as eq1.
    apply sym in eq1.
    apply (trans2 eq1); cbn.
    clear eq1.

    clear ab bc.
    intros D f g f_homo g_homo; cbn in *.
    rewrite op_homo by exact f_homo.
    rewrite op_homo by exact a_bcg_homo.
    rewrite op_homo by exact f_homo.
    pose proof (aof_plus_assoc [D|]).
    rewrite op_assoc.
    rewrite op_homo by exact g_homo.
    rewrite op_homo by exact ab_cf_homo.
    rewrite op_homo by exact g_homo.
    apply f_equal2.
    1: apply f_equal2.
    -   apply (arch_ordered_homo_eq
            (λ x, f (a_bcf x)) (λ x, g (ab_cf (abf x)))).
        all: apply arch_ordered_homo_compose.
        3: apply arch_ordered_homo_compose.
        all: assumption.
    -   apply (arch_ordered_homo_eq
            (λ x, f (a_bcg (bcf x))) (λ x, g (ab_cf (abg x)))).
        all: apply arch_ordered_homo_compose.
        1, 3: apply arch_ordered_homo_compose.
        all: assumption.
    -   apply (arch_ordered_homo_eq
            (λ x, f (a_bcg (bcg x))) (λ x, g (ab_cg x))).
        all: apply arch_ordered_homo_compose.
        1: apply arch_ordered_homo_compose.
        all: assumption.
Qed.

Definition ub_plus_base := ub_bin (λ F, @plus _ (aof_plus F)).
Local Infix "⊕" := ub_plus_base.

Lemma ub_plus_wd : ∀ a b c d, a ~ b → c ~ d → a ⊕ c ~ b ⊕ d.
Proof.
    intros a b c d.
    apply ub_bin_wd; clear a b c d.
    intros A B f x y f_homo.
    apply f_homo.
Qed.

Definition ub_neg_base (a : ub_base) :=
    make_ub_base (ub_A a) (@neg _ (aof_neg [ub_A a|]) (ub_x a)).
Local Notation "⊖ a" := (ub_neg_base a).

Lemma ub_neg_wd : ∀ a b, a ~ b → ⊖a ~ ⊖b.
Proof.
    intros a b eq A f g f_homo g_homo.
    cbn.
    rewrite arch_ordered_homo_neg by exact f_homo.
    rewrite arch_ordered_homo_neg by exact g_homo.
    apply f_equal.
    apply eq; assumption.
Qed.

Local Instance ub_plus : Plus ub := {
    plus := binary_self_op ub_plus_wd
}.

Local Instance ub_zero : Zero ub := {
    zero := to_equiv_type ub_equiv (make_ub_base F' (@zero _ (aof_zero [F'|])))
}.

Local Instance ub_neg : Neg ub := {
    neg := unary_self_op ub_neg_wd
}.

Lemma ub_plus_homo : ∀ F G f x y,
    arch_ordered_homo F G f →
    f (@plus _ (aof_plus F) x y) = @plus _ (aof_plus G) (f x) (f y).
Proof.
    intros F1 F2 f x y f_homo.
    apply f_homo.
Qed.

Local Program Instance ub_plus_comm : PlusComm ub.
Next Obligation.
    equiv_get_value a b.
    unfold plus; equiv_simpl.
    pose proof (ub_base_max (ub_A a) (ub_A b)) as [A [f [g [f_homo g_homo]]]].
    pose proof (ub_bin_eq _ a b ub_plus_homo A f g f_homo g_homo) as eq1.
    pose proof (ub_bin_eq _ b a ub_plus_homo A g f g_homo f_homo) as eq2.
    apply sym in eq2.
    apply (trans eq1).
    apply (trans2 eq2).
    clear eq1 eq2.
    intros B h i h_homo i_homo; cbn in *.
    rewrite ub_plus_homo by exact h_homo.
    rewrite ub_plus_homo by exact i_homo.
    pose proof (aof_plus_comm [B|]).
    rewrite plus_comm.
    apply f_equal2.
    all: apply arch_ordered_homo_eq; assumption.
Qed.

Local Program Instance ub_plus_assoc : PlusAssoc ub.
Next Obligation.
    equiv_get_value a b c.
    unfold plus; equiv_simpl.
    apply ub_bin_assoc.
    -   exact ub_plus_homo.
    -   intros A x y z.
        apply (aof_plus_assoc A).
Qed.

Local Program Instance ub_plus_lid : PlusLid ub.
Next Obligation.
    equiv_get_value a.
    unfold plus, zero; equiv_simpl.
    pose proof (ub_base_max F' (ub_A a)) as [A [f [g [f_homo g_homo]]]].
    pose (z := make_ub_base F' (@zero _ (aof_zero [F'|]))).
    apply (trans (ub_bin_eq _ z _ ub_plus_homo A f g f_homo g_homo)).
    intros B h i h_homo i_homo; cbn in *.
    rewrite (land f_homo).
    pose proof (aof_plus_lid [A|]).
    rewrite plus_lid.
    apply (arch_ordered_homo_eq (λ x, h (g x))).
    1: apply arch_ordered_homo_compose.
    all: assumption.
Qed.

Local Program Instance ub_plus_linv : PlusLinv ub.
Next Obligation.
    equiv_get_value a.
    unfold plus, neg, zero; equiv_simpl.
    unfold ub_neg_base.
    pose proof (identity_arch_ordered_homo [ub_A a|]) as id_homo.
    pose (na := make_ub_base (ub_A a) (@neg _ (aof_neg [ub_A a|]) (ub_x a))).
    apply (trans (ub_bin_eq _ na a ub_plus_homo
        (ub_A a) identity identity id_homo id_homo)).
    intros A f g f_homo g_homo; cbn in *.
    unfold identity.
    pose (APZ := aof_zero [ub_A a|]).
    pose (APN := aof_plus_linv [ub_A a|]).
    rewrite plus_linv.
    rewrite (land g_homo).
    apply f_homo.
Qed.

Definition ub_mult_base := ub_bin (λ F, @mult _ (aof_mult F)).
Local Infix "⊗" := ub_mult_base.

Lemma ub_mult_wd : ∀ a b c d, a ~ b → c ~ d → a ⊗ c ~ b ⊗ d.
Proof.
    intros a b c d.
    apply ub_bin_wd; clear a b c d.
    intros A B f x y f_homo.
    apply f_homo.
Qed.

Definition ub_div_base (a : ub_base) :=
    make_ub_base (ub_A a)
        (If @zero _ (aof_zero [ub_A a|]) = ub_x a
        then ub_x a
        else @div _ (aof_div [ub_A a|]) (ub_x a)).
Local Notation "⊘ a" := (ub_div_base a).

Lemma ub_div_wd : ∀ a b, a ~ b → ⊘a ~ ⊘b.
Proof.
    intros a b eq A f g f_homo g_homo.
    cbn.
    specialize (eq A f g f_homo g_homo).
    do 2 case_if.
    -   exact eq.
    -   rewrite <- e in eq.
        rewrite (land f_homo) in eq.
        rewrite <- (land g_homo) in eq.
        apply arch_ordered_homo_inj in eq; [>|exact g_homo].
        contradiction.
    -   rewrite <- e in eq.
        rewrite (land g_homo) in eq.
        rewrite <- (land f_homo) in eq.
        apply arch_ordered_homo_inj in eq; [>|exact f_homo].
        symmetry in eq.
        contradiction.
    -   rewrite arch_ordered_homo_div by assumption.
        rewrite arch_ordered_homo_div by assumption.
        apply f_equal.
        exact eq.
Qed.

Local Instance ub_mult : Mult ub := {
    mult := binary_self_op ub_mult_wd
}.

Local Instance ub_one : One ub := {
    one := to_equiv_type ub_equiv (make_ub_base F' (@one _ (aof_one [F'|])))
}.

Local Instance ub_div : Div ub := {
    div := unary_self_op ub_div_wd
}.

Lemma ub_mult_homo : ∀ F G f x y,
    arch_ordered_homo F G f →
    f (@mult _ (aof_mult F) x y) = @mult _ (aof_mult G) (f x) (f y).
Proof.
    intros F1 F2 f x y f_homo.
    apply f_homo.
Qed.

Local Program Instance ub_mult_comm : MultComm ub.
Next Obligation.
    equiv_get_value a b.
    unfold mult; equiv_simpl.
    pose proof (ub_base_max (ub_A a) (ub_A b)) as [A [f [g [f_homo g_homo]]]].
    pose proof (ub_bin_eq _ a b ub_mult_homo A f g f_homo g_homo) as eq1.
    pose proof (ub_bin_eq _ b a ub_mult_homo A g f g_homo f_homo) as eq2.
    apply sym in eq2.
    apply (trans eq1).
    apply (trans2 eq2).
    clear eq1 eq2.
    intros B h i h_homo i_homo; cbn in *.
    rewrite ub_mult_homo by exact h_homo.
    rewrite ub_mult_homo by exact i_homo.
    pose proof (aof_mult_comm [B|]).
    rewrite mult_comm.
    apply f_equal2.
    all: apply arch_ordered_homo_eq; assumption.
Qed.

Local Program Instance ub_mult_assoc : MultAssoc ub.
Next Obligation.
    equiv_get_value a b c.
    unfold mult; equiv_simpl.
    apply ub_bin_assoc.
    -   exact ub_mult_homo.
    -   intros A x y z.
        apply (aof_mult_assoc A).
Qed.

Local Program Instance ub_ldist : Ldist ub.
Next Obligation.
    equiv_get_value a b c.
    unfold plus, mult; equiv_simpl.

    pose proof (ub_base_max (ub_A b) (ub_A c))
        as [BC [bcf [bcg [bcf_homo bcg_homo]]]].
    pose proof (ub_bin_eq _ b c ub_plus_homo
        BC bcf bcg bcf_homo bcg_homo) as eq1; cbn in eq1.
    pose proof (refl a) as eq2.
    pose proof (ub_mult_wd _ _ _ _ eq2 eq1) as eq3; cbn in eq3.
    apply (trans eq3).
    clear eq1 eq2 eq3.
    pose (bc := make_ub_base BC
        (@plus _ (aof_plus [BC|]) (bcf (ub_x b)) (bcg (ub_x c)))).
    pose proof (ub_base_max (ub_A a) BC)
        as [A_BC [a_bcf [a_bcg [a_bcf_homo a_bcg_homo]]]].
    pose proof (ub_bin_eq _ a bc ub_mult_homo _
        a_bcf a_bcg a_bcf_homo a_bcg_homo) as eq1.
    apply (trans eq1); cbn.
    clear eq1 bc.

    pose proof (ub_base_max (ub_A a) (ub_A b))
        as [AB [abf [abg [abf_homo abg_homo]]]].
    pose proof (ub_base_max (ub_A a) (ub_A c))
        as [AC [acf [acg [acf_homo acg_homo]]]].
    pose proof (ub_bin_eq _ a b ub_mult_homo
        AB abf abg abf_homo abg_homo) as eq1; cbn in eq1.
    pose proof (ub_bin_eq _ a c ub_mult_homo
        AC acf acg acf_homo acg_homo) as eq2; cbn in eq2.
    pose proof (ub_plus_wd _ _ _ _ eq1 eq2) as eq3; cbn in eq3.
    apply sym in eq3.
    apply (trans2 eq3).
    clear eq1 eq2 eq3.
    pose (ab := make_ub_base AB
        (@mult _ (aof_mult [AB|]) (abf (ub_x a)) (abg (ub_x b)))).
    pose (ac := make_ub_base AC
        (@mult _ (aof_mult [AC|]) (acf (ub_x a)) (acg (ub_x c)))).
    pose proof (ub_base_max AB AC)
        as [ABC [abcf [abcg [abcf_homo abcg_homo]]]].
    pose proof (ub_bin_eq _ ab ac ub_plus_homo _
        abcf abcg abcf_homo abcg_homo) as eq1.
    apply sym in eq1.
    apply (trans2 eq1); cbn.
    clear eq1 ab ac.

    unfold ub_eq; cbn.
    intros D f g f_homo g_homo.
    rewrite (land (rand (rand a_bcg_homo))).
    rewrite (land (rand (rand (rand f_homo)))).
    rewrite (land (rand (rand f_homo))).
    pose proof (aof_ldist [D|]).
    rewrite ldist.
    rewrite (land (rand (rand (rand abcf_homo)))).
    rewrite (land (rand (rand (rand abcg_homo)))).
    rewrite (land (rand (rand g_homo))).
    do 2 rewrite (land (rand (rand (rand g_homo)))).
    do 2 apply f_equal2.
    -   apply (arch_ordered_homo_eq (λ x, f (a_bcf x)) (λ x, g (abcf (abf x)))).
        all: apply arch_ordered_homo_compose.
        3: apply arch_ordered_homo_compose.
        all: assumption.
    -   apply (arch_ordered_homo_eq (λ x, f (a_bcg (bcf x))) (λ x, g (abcf (abg x)))).
        all: apply arch_ordered_homo_compose.
        1, 3: apply arch_ordered_homo_compose.
        all: assumption.
    -   apply (arch_ordered_homo_eq (λ x, f (a_bcf x)) (λ x, g (abcg (acf x)))).
        all: apply arch_ordered_homo_compose.
        3: apply arch_ordered_homo_compose.
        all: assumption.
    -   apply (arch_ordered_homo_eq (λ x, f (a_bcg (bcg x))) (λ x, g (abcg (acg x)))).
        all: apply arch_ordered_homo_compose.
        1, 3: apply arch_ordered_homo_compose.
        all: assumption.
Qed.

Local Program Instance ub_mult_lid : MultLid ub.
Next Obligation.
    equiv_get_value a.
    unfold mult, one; equiv_simpl.
    pose proof (ub_base_max F' (ub_A a)) as [A [f [g [f_homo g_homo]]]].
    pose (o := make_ub_base F' (@one _ (aof_one [F'|]))).
    apply (trans (ub_bin_eq _ o _ ub_mult_homo A f g f_homo g_homo)).
    intros B h i h_homo i_homo; cbn in *.
    rewrite (land (rand f_homo)).
    pose proof (aof_mult_lid [A|]).
    rewrite mult_lid.
    apply (arch_ordered_homo_eq (λ x, h (g x))).
    1: apply arch_ordered_homo_compose.
    all: assumption.
Qed.

Local Program Instance ub_mult_linv : MultLinv ub.
Next Obligation.
    rename H into a_nz.
    equiv_get_value a.
    unfold mult, div, one; equiv_simpl.
    unfold ub_div_base.
    case_if.
    1: {
        unfold zero in a_nz; equiv_simpl in a_nz.
        exfalso; apply a_nz.
        intros A f g f_homo g_homo; cbn in *.
        rewrite <- e.
        rewrite (land f_homo), (land g_homo).
        reflexivity.
    }
    pose proof (identity_arch_ordered_homo [ub_A a|]) as id_homo.
    pose (na := make_ub_base (ub_A a) (@div _ (aof_div [ub_A a|]) (ub_x a))).
    apply (trans (ub_bin_eq _ na a ub_mult_homo
        (ub_A a) identity identity id_homo id_homo)).
    intros A f g f_homo g_homo; cbn in *.
    unfold identity.
    pose (APZ := aof_zero [ub_A a|]).
    pose (APO := aof_one [ub_A a|]).
    pose (APN := aof_mult_linv [ub_A a|]).
    rewrite mult_linv by exact n.
    rewrite (land (rand g_homo)).
    apply f_homo.
Qed.

Definition ub_le_base (a b : ub_base) := ∀ (A : set_type F) f g,
    arch_ordered_homo [ub_A a|] [A|] f → arch_ordered_homo [ub_A b|] [A|] g
    → @le _ (aof_le [A|]) (f (ub_x a))  (g (ub_x b)).
Local Infix "≦" := ub_le_base.

Lemma ub_le_wd_1 : ∀ a b c d, a ~ b → c ~ d → a ≦ c → b ≦ d.
Proof.
    cbn; unfold ub_eq, ub_le_base.
    intros a b c d ab cd ac A f g f_homo g_homo.
    pose proof (ub_base_max (ub_A a) A)
        as [AB [abf [abg [abf_homo abg_homo]]]].
    pose proof (ub_base_max (ub_A c) A)
        as [CD [cdf [cdg [cdf_homo cdg_homo]]]].
    specialize (ab _ _ _ abf_homo
        (arch_ordered_homo_compose _ _ _ _ _ f_homo abg_homo)).
    specialize (cd _ _ _ cdf_homo
        (arch_ordered_homo_compose _ _ _ _ _ g_homo cdg_homo)).
    cbn in ab, cd.
    pose proof (ub_base_max AB CD) as [E [ef [eg [ef_homo eg_homo]]]].
    specialize (ac E (λ x, ef (abf x)) (λ x, eg (cdf x))).
    prove_parts ac.
    1, 2: apply arch_ordered_homo_compose; assumption.
    cbn in ac.
    rewrite ab, cd in ac.
    pose (EO := aof_le [E|]).
    assert (ef (abg (f (ub_x b))) <= ef (abg (g (ub_x d)))) as leq.
    {
        applys_eq ac.
        apply (arch_ordered_homo_eq (λ x, ef (abg x)) (λ x, (eg (cdg x)))).
        all: apply arch_ordered_homo_compose; assumption.
    }
    unfold EO in leq.
    rewrite <- (rand (rand (rand (rand ef_homo)))) in leq.
    rewrite <- (rand (rand (rand (rand abg_homo)))) in leq.
    exact leq.
Qed.
Lemma ub_le_wd : ∀ a b c d, a ~ b → c ~ d → (a ≦ c) = (b ≦ d).
    intros a b c d ab cd.
    apply propositional_ext.
    split; apply ub_le_wd_1; auto; try apply eq_symmetric; auto.
Qed.

Local Instance ub_order : Order ub := {
    le := binary_op ub_le_wd;
}.

Local Program Instance ub_le_antisym : Antisymmetric le.
Next Obligation.
    rename H into xy, H0 into yx.
    equiv_get_value x y.
    unfold le in *; cbn in *.
    equiv_simpl; equiv_simpl in xy; equiv_simpl in yx.
    intros A f g f_homo g_homo.
    specialize (xy A f g f_homo g_homo).
    specialize (yx A g f g_homo f_homo).
    pose proof (aof_le_antisym [A|]).
    exact (antisym xy yx).
Qed.
Local Program Instance ub_le_trans : Transitive le.
Next Obligation.
    rename H into xy, H0 into yz.
    equiv_get_value x y z.
    unfold le in *.
    equiv_simpl; equiv_simpl in xy; equiv_simpl in yz.
    intros A f g f_homo g_homo.
    pose proof (ub_base_max A (ub_A y)) as [B [h [i [h_homo i_homo]]]].
    specialize (yz B i (λ x, h (g x)) i_homo).
    prove_parts yz; [>apply arch_ordered_homo_compose; assumption|].
    specialize (xy B (λ x, h (f x)) i).
    prove_parts xy; [>apply arch_ordered_homo_compose;assumption|exact i_homo|].
    cbn in xy, yz.
    pose proof (aof_le_trans [B|]).
    pose proof (trans xy yz) as xz.
    rewrite <- (rand (rand (rand (rand h_homo)))) in xz.
    exact xz.
Qed.
Local Program Instance ub_le_connex : Connex le.
Next Obligation.
    classic_case (x <= y) as [leq|nleq].
    1: left; exact leq.
    right.
    equiv_get_value x y.
    unfold le in *; equiv_simpl; equiv_simpl in nleq.
    intros A Af Ag Af_homo Ag_homo.
    classic_contradiction contr.
    apply nleq.
    intros B Bf Bg Bf_homo Bg_homo.
    pose proof (aof_le_antisym [A|]).
    pose proof (aof_le_connex [A|]).
    rewrite nle_lt in contr.
    destruct contr as [leq neq]; clear neq.
    pose proof (ub_base_max A B) as [C [Cf [Cg [Cf_homo Cg_homo]]]].
    rewrite (rand (rand (rand (rand Cg_homo)))).
    rewrite (rand (rand (rand (rand Cf_homo)))) in leq.
    applys_eq leq.
    -   apply (arch_ordered_homo_eq (λ x, Cg (Bf x)) (λ x, Cf (Ag x))).
        all: apply arch_ordered_homo_compose; assumption.
    -   apply (arch_ordered_homo_eq (λ x, Cg (Bg x)) (λ x, Cf (Af x))).
        all: apply arch_ordered_homo_compose; assumption.
Qed.
Local Program Instance ub_le_lplus : OrderLplus ub.
Next Obligation.
    rename H into leq.
    equiv_get_value a b c.
    unfold plus, le; equiv_simpl.
    unfold le in leq; equiv_simpl in leq.
    pose proof (ub_base_max (ub_A c) (ub_A a))
        as [A [Af [Ag [Af_homo Ag_homo]]]].
    pose proof (ub_base_max (ub_A c) (ub_A b))
        as [B [Bf [Bg [Bf_homo Bg_homo]]]].
    pose proof (ub_bin_eq _ c a ub_plus_homo A Af Ag Af_homo Ag_homo) as eq1.
    pose proof (ub_bin_eq _ c b ub_plus_homo B Bf Bg Bf_homo Bg_homo) as eq2.
    cbn in eq1, eq2.
    apply sym in eq1, eq2.
    apply (ub_le_wd_1 _ _ _ _ eq1 eq2).
    clear eq1 eq2.
    intros C Cf Cg Cf_homo Cg_homo; cbn in *.
    specialize (leq C (λ x, Cf (Ag x)) (λ x, Cg (Bg x))).
    prove_parts leq.
    1, 2: apply arch_ordered_homo_compose; assumption.
    cbn in leq.
    pose (CP := aof_plus [C|]).
    pose proof (aof_le_lplus [C|]).
    apply le_lplus with (Cf (Af (ub_x c))) in leq.
    rewrite (land (rand (rand Cf_homo))).
    rewrite (land (rand (rand Cg_homo))).
    applys_eq leq.
    apply f_equal2; [>|reflexivity].
    apply (arch_ordered_homo_eq (λ x, Cg (Bf x)) (λ x, Cf (Af x))).
    all: apply arch_ordered_homo_compose; assumption.
Qed.
Local Program Instance ub_le_mult : OrderMult ub.
Next Obligation.
    rename H into a_pos, H0 into b_pos.
    equiv_get_value a b.
    unfold zero, le, mult; equiv_simpl.
    pose proof (ub_base_max (ub_A a) (ub_A b)) as
        [A [Af [Ag [Af_homo Ag_homo]]]].
    pose proof (ub_bin_eq _ a b ub_mult_homo A Af Ag Af_homo Ag_homo) as eq.
    cbn in eq.
    apply sym in eq.
    apply (ub_le_wd_1 _ _ _ _ (refl _) eq); clear eq.
    intros B Bf Bg Bf_homo Bg_homo; cbn in *.
    rewrite (land Bf_homo).
    rewrite (land (rand (rand (rand Bg_homo)))).
    pose proof (aof_le_mult [B|]).
    pose (BZ := aof_zero [B|]).
    pose (BO := aof_le [B|]).
    assert (∀ x f, arch_ordered_homo _ _ f → 0 <= to_equiv_type ub_equiv x →
        0 <= Bg (f (ub_x x))) as lemma.
    {
        clear - Bg_homo.
        intros x f f_homo x_pos.
        unfold zero, le in x_pos; equiv_simpl in x_pos.
        pose proof (ub_base_max (ub_A x) F') as [C [Cf [Cg [Cf_homo Cg_homo]]]].
        specialize (x_pos C Cg Cf Cg_homo Cf_homo).
        cbn in x_pos.
        rewrite (land Cg_homo) in x_pos.
        rewrite <- (land Cf_homo) in x_pos.
        rewrite <- (rand (rand (rand (rand Cf_homo)))) in x_pos.
        rewrite <- (land Bg_homo).
        unfold BO.
        rewrite <- (rand (rand (rand (rand Bg_homo)))).
        rewrite <- (land f_homo).
        rewrite <- (rand (rand (rand (rand f_homo)))).
        exact x_pos.
    }
    apply le_mult; apply lemma; assumption.
Qed.

Let F'NT := aof_not_trivial [F'|].
Local Existing Instance F'NT.

Local Program Instance ub_not_trivial : NotTrivial ub := {
    not_trivial_a := to_equiv_type ub_equiv (make_ub_base F' not_trivial_a);
    not_trivial_b := to_equiv_type ub_equiv (make_ub_base F' not_trivial_b);
}.
Next Obligation.
    equiv_simpl.
    intros eq.
    specialize (eq F' identity identity).
    prove_parts eq.
    1, 2: apply identity_arch_ordered_homo.
    cbn in eq.
    apply not_trivial in eq.
    exact eq.
Qed.

Local Instance ub_arch : Archimedean ub.
    apply field_impl_arch1.
    intros x.
    equiv_get_value x.
    pose (xP := aof_plus [ub_A x|]).
    pose (xZ := aof_zero [ub_A x|]).
    pose (xN := aof_neg [ub_A x|]).
    pose (xPC := aof_plus_comm [ub_A x|]).
    pose (xPA := aof_plus_assoc [ub_A x|]).
    pose (xPZ := aof_plus_lid [ub_A x|]).
    pose (xPN := aof_plus_linv [ub_A x|]).
    pose (xM := aof_mult [ub_A x|]).
    pose (xE := aof_one [ub_A x|]).
    pose (xD := aof_div [ub_A x|]).
    pose (xMC := aof_mult_comm [ub_A x|]).
    pose (xMA := aof_mult_assoc [ub_A x|]).
    pose (xL := aof_ldist [ub_A x|]).
    pose (xME := aof_mult_lid [ub_A x|]).
    pose (xMD := aof_mult_linv [ub_A x|]).
    pose (xO := aof_le [ub_A x|]).
    pose (xOA := aof_le_antisym [ub_A x|]).
    pose (xOT := aof_le_trans [ub_A x|]).
    pose (xOC := aof_le_connex [ub_A x|]).
    pose (xOP := aof_le_lplus [ub_A x|]).
    pose (xOM := aof_le_mult [ub_A x|]).
    pose (xNT := aof_not_trivial [ub_A x|]).
    pose (xA := aof_arch [ub_A x|]).
    pose proof (archimedean1 (ub_x x)) as [n [leq neq]].
    exists n.
    assert (nat_to_abstract n = to_equiv_type ub_equiv
        (make_ub_base (ub_A x) (nat_to_abstract n))) as eq.
    {
        clear leq neq.
        nat_induction n.
        -   do 2 rewrite nat_to_abstract_zero.
            unfold zero at 1; equiv_simpl.
            intros A f g f_homo g_homo; cbn.
            rewrite (land g_homo).
            apply f_homo.
        -   cbn.
            rewrite IHn; clear IHn.
            unfold one at 1, plus at 1; equiv_simpl.
            pose proof (ub_base_max F' (ub_A x))
                as [A [Af [Ag [Af_homo Ag_homo]]]].
            pose (o := make_ub_base F' (@one _ (aof_one [F'|]))).
            pose (n' := make_ub_base _ (nat_to_abstract n)).
            apply (trans (ub_bin_eq _ o n'
                ub_plus_homo A Af Ag Af_homo Ag_homo)); cbn.
            intros B Bf Bg Bf_homo Bg_homo; cbn in *.
            rewrite (land (rand (rand Bf_homo))).
            rewrite (land (rand (rand Bg_homo))).
            rewrite (land (rand (Af_homo))).
            rewrite (land (rand (Bf_homo))).
            rewrite (land (rand (Bg_homo))).
            apply f_equal.
            apply (arch_ordered_homo_eq (λ x, Bf (Ag x))).
            1: apply arch_ordered_homo_compose.
            all: assumption.
    }
    rewrite eq.
    split.
    -   unfold le; equiv_simpl.
        intros A f g f_homo g_homo; cbn in *.
        replace f with g.
        2: apply arch_ordered_homo_uni; assumption.
        apply g_homo.
        exact leq.
    -   equiv_simpl.
        intros contr.
        apply neq.
        specialize (contr (ub_A x) identity identity
            (identity_arch_ordered_homo _) (identity_arch_ordered_homo _)).
        cbn in contr.
        exact contr.
Qed.

Definition ub_ex := aof_ex ub.

End NotEmpty.

Local Existing Instances ub_eq_reflexive ub_eq_symmetric ub_eq_transitive.

Theorem aof_zorn_ub_ex : has_upper_bound le F.
Proof.
    classic_case (∃ F', F F') as [F'|F'_nex].
    -   destruct F' as [F' FF'].
        exists (ub_ex [F'|FF']).
        intros A FA.
        unfold le; cbn.
        exists (λ x, aof_ex_f (to_equiv_type ub_equiv (make_ub_base [A|FA] x))).
        split; [>|split; [>|split; [>|split]]].
        +   unfold zero at 2; cbn.
            apply f_equal.
            unfold zero at 2; equiv_simpl.
            intros B f g f_homo g_homo; cbn in *.
            rewrite (land g_homo).
            apply f_homo.
        +   unfold one at 2; cbn.
            apply f_equal.
            unfold one at 2; equiv_simpl.
            intros B f g f_homo g_homo; cbn in *.
            rewrite (land (rand g_homo)).
            apply f_homo.
        +   intros a b.
            unfold plus at 2; cbn.
            apply f_equal.
            do 2 rewrite aof_ex_f_eq1.
            unfold plus at 2; equiv_simpl.
            pose (a' := make_ub_base [A|FA] a).
            pose (b' := make_ub_base [A|FA] b).
            pose proof (ub_bin_eq _ a' b' ub_plus_homo [A|FA] identity identity)
                as eq; cbn in eq.
            prove_parts eq.
            1, 2: apply identity_arch_ordered_homo.
            apply sym in eq.
            exact eq.
        +   intros a b.
            unfold mult at 2; cbn.
            apply f_equal.
            do 2 rewrite aof_ex_f_eq1.
            unfold mult at 2; equiv_simpl.
            pose (a' := make_ub_base [A|FA] a).
            pose (b' := make_ub_base [A|FA] b).
            pose proof (ub_bin_eq _ a' b' ub_mult_homo [A|FA] identity identity)
                as eq; cbn in eq.
            prove_parts eq.
            1, 2: apply identity_arch_ordered_homo.
            apply sym in eq.
            exact eq.
        +   intros a b.
            unfold le at 2; cbn.
            do 2 rewrite aof_ex_f_eq1.
            unfold le at 2; equiv_simpl.
            split.
            *   intros leq B f g f_homo g_homo; cbn in *.
                rewrite (arch_ordered_homo_uni _ _ f g f_homo g_homo).
                apply g_homo.
                exact leq.
            *   intros leq.
                specialize (leq [A|FA] identity identity).
                prove_parts leq.
                1, 2: apply identity_arch_ordered_homo.
                unfold identity in leq; cbn in leq.
                exact leq.
    -   exists rat_aof.
        intros A FA.
        exfalso; apply F'_nex.
        exists A.
        exact FA.
Qed.

End AofZornUb.
End AofZornUb.

Definition real_aof := ex_val (preorder_zorn _ AofZornUb.aof_zorn_ub_ex).

Definition real := set_type (aof_set real_aof).
Definition real_plus := aof_plus real_aof.
Definition real_zero := aof_zero real_aof.
Definition real_neg := aof_neg real_aof.
Definition real_plus_comm := aof_plus_comm real_aof.
Definition real_plus_assoc := aof_plus_assoc real_aof.
Definition real_plus_lid := aof_plus_lid real_aof.
Definition real_plus_linv := aof_plus_linv real_aof.
Definition real_mult := aof_mult real_aof.
Definition real_one := aof_one real_aof.
Definition real_div := aof_div real_aof.
Definition real_mult_comm := aof_mult_comm real_aof.
Definition real_mult_assoc := aof_mult_assoc real_aof.
Definition real_ldist := aof_ldist real_aof.
Definition real_mult_lid := aof_mult_lid real_aof.
Definition real_mult_linv := aof_mult_linv real_aof.
Definition real_le := aof_le real_aof.
Definition real_le_antisym := aof_le_antisym real_aof.
Definition real_le_trans := aof_le_trans real_aof.
Definition real_le_connex := aof_le_connex real_aof.
Definition real_le_lplus := aof_le_lplus real_aof.
Definition real_le_mult := aof_le_mult real_aof.
Definition real_not_trivial := aof_not_trivial real_aof.
Definition real_arch := aof_arch real_aof.
Global Existing Instances real_plus real_zero real_neg real_plus_comm
    real_plus_assoc real_plus_lid real_plus_linv real_mult real_one real_div
    real_mult_comm real_mult_assoc real_ldist real_mult_lid real_mult_linv
    real_le real_le_antisym real_le_trans real_le_connex real_le_lplus
    real_le_mult real_not_trivial real_arch.

Theorem real_maximal : ∀ A, (∃ f, arch_ordered_homo real_aof A f) →
    ∃ f, arch_ordered_homo A real_aof f.
Proof.
    intros A f_ex.
    unfold real_aof in *.
    rewrite_ex_val R R_max.
    exact (R_max A f_ex).
Qed.
(* Proving completeness from this is going to be quite an effort *)
