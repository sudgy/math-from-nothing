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
Lemma card_mult_wd : ∀ A B C D, A ~ B → C ~ D → prod A C ~ prod B D.
    intros A B C D [f f_bij] [g g_bij].
    exists (λ x, (f (fst x), g (snd x))).
    split.
    -   intros [a1 c1] [a2 c2] eq.
        inversion eq as [[eq1 eq2]].
        apply f_bij in eq1.
        apply g_bij in eq2.
        rewrite eq1, eq2.
        reflexivity.
    -   intros [b d].
        pose proof (rand f_bij b) as [a a_eq].
        pose proof (rand g_bij d) as [c c_eq].
        exists (a, c).
        cbn.
        rewrite a_eq, c_eq.
        reflexivity.
Qed.
Instance card_mult_class : Mult card := {
    mult := binary_self_op card_mult_wd
}.

Theorem card_mult_type : ∀ A B, |(A*B)%type| = |A| * |B|.
    intros A B.
    unfold mult; cbn.
    rewrite equiv_binary_self_op.
    reflexivity.
Qed.

(* begin hide *)
Lemma card_mult_assoc : ∀ κ μ ν, κ * (μ * ν) = (κ * μ) * ν.
    intros A B C.
    equiv_get_value A B C.
    unfold mult; equiv_simpl.
    exists (λ x, ((fst x, fst (snd x)), snd (snd x))).
    split.
    -   intros [a1 [b1 c1]] [a2 [b2 c2]] eq.
        cbn in eq.
        inversion eq.
        reflexivity.
    -   intros [[a b] c].
        exists (a, (b, c)).
        cbn.
        reflexivity.
Qed.
Instance card_mult_assoc_class : MultAssoc card := {
    mult_assoc := card_mult_assoc
}.

Lemma card_mult_comm : ∀ κ μ, κ * μ = μ * κ.
    intros A B.
    equiv_get_value A B.
    unfold mult; equiv_simpl.
    exists (λ x, (snd x, fst x)).
    split.
    -   intros [a1 b1] [a2 b2] eq.
        cbn in eq.
        inversion eq.
        reflexivity.
    -   intros [b a].
        exists (a, b).
        cbn.
        reflexivity.
Qed.
Instance card_mult_comm_class : MultComm card := {
    mult_comm := card_mult_comm
}.

Lemma card_mult_lanni : ∀ κ, 0 * κ = 0.
    intros A.
    equiv_get_value A.
    unfold zero; cbn.
    unfold nat_to_card, mult; equiv_simpl.
    assert (set_type (λ x : nat, x < 0) → False) as xf.
    {
        intros [x x_lt].
        exact (nat_lt_zero _ x_lt).
    }
    exists (λ x, False_rect _ (xf (fst x))).
    split.
    -   intros [x a].
        contradiction (xf x).
    -   intros x.
        contradiction (xf x).
Qed.
Instance card_mult_lanni_class : MultLanni card := {
    mult_lanni := card_mult_lanni
}.

Instance card_one : One card := {
    one := nat_to_card 1
}.

Lemma card_mult_lid : ∀ κ, 1 * κ = κ.
    intros A.
    equiv_get_value A.
    unfold one; cbn.
    unfold nat_to_card, mult; equiv_simpl.
    exists (λ x, snd x).
    split.
    -   intros [[x x_lt] a] [[y y_lt] b] eq.
        cbn in eq.
        rewrite eq; clear eq.
        apply f_equal2; try reflexivity.
        apply set_type_eq; cbn.
        unfold one in x_lt, y_lt; cbn in x_lt, y_lt.
        rewrite nat_lt_suc_le in x_lt.
        rewrite nat_lt_suc_le in y_lt.
        apply nat_le_zero_eq in x_lt.
        apply nat_le_zero_eq in y_lt.
        subst.
        reflexivity.
    -   intros a.
        assert (zero (U := nat) < 1) as z_lt.
        {
            split.
            -   apply nat_le_zero.
            -   intro contr; inversion contr.
        }
        exists ([0|z_lt], a).
        reflexivity.
Qed.
Instance card_mult_lid_class : MultLid card := {
    mult_lid := card_mult_lid
}.

Lemma card_ldist : ∀ κ μ ν, κ * (μ + ν) = κ * μ + κ * ν.
    intros A B C.
    equiv_get_value A B C.
    unfold plus, mult; equiv_simpl.
    exists (λ x, match (snd x) with
                 | inl b => inl (fst x, b)
                 | inr c => inr (fst x, c)
                 end).
    split.
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
Instance card_ldist_class : Ldist card := {
    ldist := card_ldist
}.
(* end hide *)
Theorem card_0_false : ∀ A, (|A| = 0) = (A → False).
    intros A.
    unfold zero; cbn.
    unfold nat_to_card; equiv_simpl.
    apply propositional_ext; split.
    -   intros [f f_bij] a.
        destruct (f a) as [x x_lt].
        exact (nat_lt_zero _ x_lt).
    -   intros af.
        exists (empty_function _ _ af).
        apply empty_bij.
        intros [x x_lt].
        exact (nat_lt_zero _ x_lt).
Qed.

Theorem card_mult_zero : ∀ κ μ, κ * μ = 0 → {κ = 0} + {μ = 0}.
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

Theorem card_le_lmult : ∀ {κ μ} ν, κ <= μ → ν * κ <= ν * μ.
    intros A B C.
    equiv_get_value A B C.
    unfold le, mult; equiv_simpl.
    intros [f f_inj].
    exists (λ x, (fst x, f (snd x))).
    intros [c1 a1] [c2 a2] eq.
    cbn in eq.
    inversion eq as [[eq1 eq2]].
    apply f_inj in eq2.
    rewrite eq2.
    reflexivity.
Qed.
(* begin hide *)
Lemma card_le_lmult_pos : ∀ κ μ ν, zero <= ν → κ <= μ → ν * κ <= ν * μ.
    intros κ μ ν ν_pos.
    apply card_le_lmult.
Qed.
Instance card_le_lmult_pos_class : OrderLmult card := {
    le_lmult_pos := card_le_lmult_pos
}.
(* end hide *)
Theorem card_le_rmult : ∀ {κ μ} ν, κ <= μ → κ * ν <= μ * ν.
    intros κ μ ν.
    apply le_rmult_pos.
    apply card_le_zero.
Qed.

Theorem singleton_size {U} : ∀ a : U, |set_type (singleton a)| = 1.
    intros a.
    unfold one; cbn.
    unfold nat_to_card; equiv_simpl.
    pose proof (nat_lt_suc 0) as one_pos.
    exists (λ x, [0|one_pos]).
    split.
    -   intros [x x_eq] [y y_eq] eq; clear eq.
        apply set_type_eq; cbn.
        rewrite <- x_eq, <- y_eq.
        reflexivity.
    -   intros [y y_lt].
        exists [a|refl a].
        apply set_type_eq; cbn.
        apply nat_lt_1.
        exact y_lt.
Qed.
(* begin hide *)
Close Scope card_scope.
(* end hide *)
