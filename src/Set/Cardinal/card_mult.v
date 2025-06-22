Require Import init.

Require Export card_base.
Require Import card_order.
Require Import card_plus.
Require Import set.
Require Import function.
Require Export mult_ring.
Require Import nat.

(* begin hide *)
Open Scope card_scope.
(* end hide *)
Lemma card_mult_wd : ∀ A B C D, A ~ B → C ~ D → (A * C ~ B * D)%type.
Proof.
    intros A B C D [f f_bij] [g g_bij].
    exists (λ x, (f (fst x), g (snd x))).
    split; split.
    -   intros [a1 c1] [a2 c2] eq.
        inversion eq as [[eq1 eq2]].
        apply f_bij in eq1.
        apply g_bij in eq2.
        rewrite eq1, eq2.
        reflexivity.
    -   intros [b d].
        pose proof (sur f b) as [a a_eq].
        pose proof (sur g d) as [c c_eq].
        exists (a, c).
        cbn.
        rewrite a_eq, c_eq.
        reflexivity.
Qed.
Global Instance card_mult_class : Mult card := {
    mult := binary_op (binary_self_wd (f := prod_type) (E := card_equiv)card_mult_wd)
}.

Theorem card_mult_type : ∀ A B, |(A*B)%type| = |A| * |B|.
Proof.
    intros A B.
    unfold mult; cbn.
    rewrite binary_op_eq.
    reflexivity.
Qed.

(* begin hide *)
Lemma card_mult_assoc : ∀ κ μ ν, κ * (μ * ν) = (κ * μ) * ν.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold mult; equiv_simpl.
    exists (λ x, ((fst x, fst (snd x)), snd (snd x))).
    split; split.
    -   intros [a1 [b1 c1]] [a2 [b2 c2]] eq.
        cbn in eq.
        inversion eq.
        reflexivity.
    -   intros [[a b] c].
        exists (a, (b, c)).
        cbn.
        reflexivity.
Qed.
Global Instance card_mult_assoc_class : MultAssoc card := {
    mult_assoc := card_mult_assoc
}.

Lemma card_mult_comm : ∀ κ μ, κ * μ = μ * κ.
Proof.
    intros A B.
    equiv_get_value A B.
    unfold mult; equiv_simpl.
    exists (λ x, (snd x, fst x)).
    split; split.
    -   intros [a1 b1] [a2 b2] eq.
        cbn in eq.
        inversion eq.
        reflexivity.
    -   intros [b a].
        exists (a, b).
        cbn.
        reflexivity.
Qed.
Global Instance card_mult_comm_class : MultComm card := {
    mult_comm := card_mult_comm
}.

Lemma card_mult_lanni : ∀ κ, 0 * κ = 0.
Proof.
    intros A.
    equiv_get_value A.
    unfold zero; cbn.
    unfold nat_to_card, mult; equiv_simpl.
    assert (set_type (λ x : nat, x < 0) → False) as xf.
    {
        intros [x x_lt].
        exact (not_neg x_lt).
    }
    exists (λ x, False_rect _ (xf (fst x))).
    split; split.
    -   intros [x a].
        contradiction (xf x).
    -   intros x.
        contradiction (xf x).
Qed.
Global Instance card_mult_lanni_class : MultLanni card := {
    mult_lanni := card_mult_lanni
}.

Global Instance card_one : One card := {
    one := nat_to_card 1
}.

Lemma card_mult_lid : ∀ κ, 1 * κ = κ.
Proof.
    intros A.
    equiv_get_value A.
    unfold one; cbn.
    unfold nat_to_card, mult; equiv_simpl.
    exists (λ x, snd x).
    split; split.
    -   intros [[x x_lt] a] [[y y_lt] b] eq.
        cbn in eq.
        rewrite eq; clear eq.
        apply f_equal2; try reflexivity.
        apply set_type_eq; cbn.
        unfold one in x_lt, y_lt; cbn in x_lt, y_lt.
        rewrite nat_lt_suc_le in x_lt.
        rewrite nat_lt_suc_le in y_lt.
        change nat_zero with (0 : nat) in x_lt.
        change nat_zero with (0 : nat) in y_lt.
        apply all_neg_eq in x_lt.
        apply all_neg_eq in y_lt.
        subst.
        reflexivity.
    -   intros a.
        assert (zero (U := nat) < 1) as z_lt.
        {
            split.
            -   apply nat_pos.
            -   intro contr; inversion contr.
        }
        exists ([0|z_lt], a).
        reflexivity.
Qed.
Global Instance card_mult_lid_class : MultLid card := {
    mult_lid := card_mult_lid
}.

Lemma card_ldist : ∀ κ μ ν, κ * (μ + ν) = κ * μ + κ * ν.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold plus, mult; equiv_simpl.
    exists (λ x, match (snd x) with
                 | inl b => inl (fst x, b)
                 | inr c => inr (fst x, c)
                 end).
    split; split.
    -   intros [a1 [b1|c1]] [a2 [b2|c2]] eq; cbn in eq.
        all: inversion eq.
        all: reflexivity.
    -   intros [[a b]|[a c]].
        +   exists (a, inl b).
            cbn.
            reflexivity.
        +   exists (a, inr c).
            cbn.
            reflexivity.
Qed.
Global Instance card_ldist_class : Ldist card := {
    ldist := card_ldist
}.
(* end hide *)
Theorem card_0_false : ∀ A, (|A| = 0) = (A → False).
Proof.
    intros A.
    unfold zero; cbn.
    unfold nat_to_card; equiv_simpl.
    apply propositional_ext; split.
    -   intros [f f_bij] a.
        destruct (f a) as [x x_lt].
        exact (not_neg x_lt).
    -   intros af.
        exists (empty_function _ _ af).
        apply empty_bij.
        intros [x x_lt].
        exact (not_neg x_lt).
Qed.

Theorem card_mult_zero : ∀ κ μ, κ * μ = 0 → {κ = 0} + {μ = 0}.
Proof.
    intros A B eq.
    equiv_get_value A B.
    unfold mult in eq; equiv_simpl in eq.
    apply or_to_strong.
    do 2 rewrite card_0_false.
    rewrite card_0_false in eq.
    classic_case (A → False) as [H|a]; try (left; exact H).
    classic_case (B → False) as [H|b]; try (right; exact H).
    apply not_not_type in a.
    apply not_not_type in b.
    contradiction (eq (a, b)).
Qed.

Theorem card_le_lmult : ∀ {κ μ} ν, κ ≤ μ → ν * κ ≤ ν * μ.
Proof.
    intros A B C.
    equiv_get_value A B C.
    unfold le, mult; equiv_simpl.
    intros [f f_inj].
    exists (λ x, (fst x, f (snd x))).
    split.
    intros [c1 a1] [c2 a2] eq.
    cbn in eq.
    inversion eq as [[eq1 eq2]].
    apply f_inj in eq2.
    rewrite eq2.
    reflexivity.
Qed.
(* begin hide *)
Lemma card_le_lmult_pos : ∀ κ μ ν, zero ≤ ν → κ ≤ μ → ν * κ ≤ ν * μ.
Proof.
    intros κ μ ν ν_pos.
    apply card_le_lmult.
Qed.
Global Instance card_le_lmult_pos_class : OrderLmult card := {
    le_lmult_pos := card_le_lmult_pos
}.
(* end hide *)
Theorem card_le_rmult : ∀ {κ μ} ν, κ ≤ μ → κ * ν ≤ μ * ν.
Proof.
    intros κ μ ν.
    apply le_rmult_pos.
    apply card_le_zero.
Qed.

Theorem singleton_size {U} : ∀ a : U, |set_type ❴a❵| = 1.
Proof.
    intros a.
    unfold one; cbn.
    unfold nat_to_card; equiv_simpl.
    pose proof (nat_lt_suc 0) as one_pos.
    exists (λ x, [0|one_pos]).
    split; split.
    -   intros [x x_eq] [y y_eq] eq; clear eq.
        apply set_type_eq; cbn.
        rewrite <- x_eq, <- y_eq.
        reflexivity.
    -   intros [y y_lt].
        exists [a|Logic.eq_refl a].
        apply set_type_eq; cbn.
        apply nat_lt_one_eq.
        exact y_lt.
Qed.

Theorem card_one_eq {U} : |U| = 1 → ∀ a b : U, a = b.
Proof.
    intros U_one a b.
    unfold one in U_one; cbn in U_one.
    unfold nat_to_card in U_one; equiv_simpl in U_one.
    destruct U_one as [f [f_inj f_sur]].
    apply f_inj.
    destruct (f a) as [m m_lt].
    destruct (f b) as [n n_lt].
    apply set_type_eq; cbn.
    apply nat_lt_one_eq in m_lt, n_lt.
    subst.
    reflexivity.
Qed.
Theorem card_one_ex {U} : |U| = 1 → U.
Proof.
    intros U_one.
    apply card_nz_ex.
    rewrite U_one.
    clear U U_one.
    intros contr.
    symmetry in contr.
    unfold zero, one in contr; cbn in contr.
    unfold nat_to_card in contr; equiv_simpl in contr.
    destruct contr as [f [f_inj f_sur]].
    contradiction (nat_lt_0_false (f [0|nat_one_pos])).
Qed.

Theorem card_unique_one {U} : U → (∀ a b : U, a = b) → |U| = 1.
Proof.
    intros a eq.
    unfold one; cbn.
    unfold nat_to_card; equiv_simpl.
    exists (λ _, [0|nat_one_pos]).
    split; split.
    -   intros x y eq'.
        apply eq.
    -   intros z.
        exists a.
        destruct z as [z z_lt].
        apply set_type_eq; cbn.
        apply nat_lt_one_eq in z_lt.
        exact z_lt.
Qed.
(* begin hide *)
Close Scope card_scope.
(* end hide *)
