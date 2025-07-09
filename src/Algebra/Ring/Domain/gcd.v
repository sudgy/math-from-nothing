Require Import init.

Require Export mult_div.
Require Export domain_category.

Definition common_divisor {U} `{Mult U} a b d := d ∣ a ∧ d ∣ b.
Definition is_gcd {U} `{Mult U} a b d
    := common_divisor a b d ∧ ∀ d', common_divisor a b d' → d' ∣ d.

Class GCDDomain (U : IntegralDomain) := {
    gcd : U → U → U;
    gcd_cd : ∀ a b, common_divisor a b (gcd a b);
    gcd_greatest :
        ∀ a b, (0 ≠ a ∨ 0 ≠ b) → ∀ d, common_divisor a b d → d ∣ (gcd a b)
}.

Section GCD.

Context {U : IntegralDomain}.

Theorem gcd_associates :
    ∀ a b d1 d2 : U, is_gcd a b d1 → is_gcd a b d2 → associates d1 d2.
Proof.
    intros a b d1 d2 [d1_cd d1_gcd] [d2_cd d2_gcd].
    specialize (d1_gcd d2 d2_cd).
    specialize (d2_gcd d1 d1_cd).
    split; assumption.
Qed.

Context `{GCDDomain U}.

Theorem gcd_gcd : ∀ a b, (0 ≠ a ∨ 0 ≠ b) → is_gcd a b (gcd a b).
Proof.
    intros a b nz.
    split.
    -   apply gcd_cd.
    -   intros d d_common.
        apply gcd_greatest; assumption.
Qed.

Lemma gcd_div_comm : ∀ a b, (0 ≠ a ∨ 0 ≠ b) → gcd a b ∣ gcd b a.
Proof.
    intros a b nz.
    apply gcd_greatest.
    -   rewrite or_comm.
        exact nz.
    -   unfold common_divisor.
        rewrite and_comm.
        apply gcd_cd.
Qed.
Theorem gcd_comm : ∀ a b, (0 ≠ a ∨ 0 ≠ b) → associates (gcd a b) (gcd b a).
Proof.
    intros a b nz.
    split; apply gcd_div_comm.
    2: rewrite or_comm.
    all: exact nz.
Qed.

Theorem irreducible_prime : ∀ p : U, irreducible p → prime p.
Proof.
    intros p [p_nz [p_nu p_irr]].
    split; [>exact p_nz|].
    split; [>exact p_nu|].
    intros a b p_div.
    pose (d := gcd (p * b) (a * b)).
    classic_case (0 = b) as [b_z|b_nz].
    {
        right.
        rewrite <- b_z.
        apply divides_zero.
    }
    classic_case (0 = a * b) as [ab_z|ab_nz].
    {
        apply mult_zero in ab_z as [a_z|b_z]; [>|contradiction].
        left.
        rewrite <- a_z.
        apply divides_zero.
    }
    assert (0 ≠ d) as d_nz.
    {
        intros contr.
        pose proof (gcd_cd (p * b) (a * b)) as [d1 d2].
        unfold d in contr.
        rewrite <- contr in d2.
        apply div_zero in d2.
        contradiction.
    }
    pose proof (mult_div_lself p b) as p_div2.
    pose proof (mult_div_rself b p) as b_div1.
    pose proof (mult_div_rself b a) as b_div2.
    pose proof (gcd_greatest _ _ (make_ror ab_nz) _ (make_and p_div2 p_div))
        as pd.
    pose proof (gcd_greatest _ _ (make_ror ab_nz) _ (make_and b_div1 b_div2))
        as bd.
    fold d in pd, bd.
    destruct pd as [u pd], bd as [v bd].
    classic_case (unit v) as [v_u|v_nu].
    -   destruct v_u as [v' eq].
        rewrite <- bd in pd.
        apply lmult with v' in pd.
        do 2 rewrite mult_assoc in pd.
        rewrite eq in pd.
        rewrite mult_lid in pd.
        right.
        exists (v' * u).
        exact pd.
    -   assert (p ∣ v) as pv.
        {
            pose proof (gcd_cd (p * b) (a * b)) as [d1 d2].
            fold d in d1, d2.
            rewrite <- bd in d1.
            apply (div_rcancel _ _ _ b_nz) in d1.
            destruct d1 as [c vp].
            assert (unit c) as c_u.
            {
                classic_contradiction contr.
                apply (p_irr c v contr v_nu).
                symmetry; exact vp.
            }
            destruct c_u as [c' c_eq].
            exists c'.
            apply lmult with c' in vp.
            rewrite mult_assoc in vp.
            rewrite c_eq in vp.
            rewrite mult_lid in vp.
            symmetry; exact vp.
        }
        left.
        pose proof (gcd_cd (p * b) (a * b)) as [d1 d2]; clear d1.
        fold d in d2.
        rewrite <- bd in d2.
        apply div_rcancel in d2; [>|exact b_nz].
        exact (trans pv d2).
Qed.

End GCD.
