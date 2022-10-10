Require Import init.

Require Export relation.
Require Import order_mult.

Definition is_least {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → op x y.
Definition is_greatest {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → op y x.
Definition is_minimal {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → y ≠ x → ¬(op y x).
Definition is_maximal {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := S x ∧ ∀ y, S y → y ≠ x → ¬(op x y).
Definition is_lower_bound {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := ∀ y, S y → op x y.
Definition is_upper_bound {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := ∀ y, S y → op y x.
Definition is_infimum {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := is_lower_bound op S x ∧ ∀ y, is_lower_bound op S y → op y x.
Definition is_supremum {U} (op : U → U → Prop) (S : U → Prop) (x : U)
    := is_upper_bound op S x ∧ ∀ y, is_upper_bound op S y → op x y.
Definition has_least {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_least op S x.
Definition has_greatest {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_greatest op S x.
Definition has_minimal {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_minimal op S x.
Definition has_maximal {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_maximal op S x.
Definition has_lower_bound {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_lower_bound op S x.
Definition has_upper_bound {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_upper_bound op S x.
Definition has_infimum {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_infimum op S x.
Definition has_supremum {U} (op : U → U → Prop) (S : U → Prop)
    := ∃ x, is_supremum op S x.

Definition open_interval {U} `{Order U} a b := λ x, a < x ∧ x < b.
Definition open_closed_interval {U} `{Order U} a b := λ x, a < x ∧ x ≤ b.
Definition closed_open_interval {U} `{Order U} a b := λ x, a ≤ x ∧ x < b.
Definition closed_interval {U} `{Order U} a b := λ x, a ≤ x ∧ x ≤ b.
Definition open_inf_interval {U} `{Order U} a := λ x, a < x.
Definition closed_inf_interval {U} `{Order U} a := λ x, a ≤ x.
Definition inf_open_interval {U} `{Order U} a := λ x, x < a.
Definition inf_closed_interval {U} `{Order U} a := λ x, x ≤ a.

Class WellOrdered {U} (op : U → U → Prop) := {
    well_ordered : ∀ S : U → Prop, (∃ x, S x) → ∃ x, is_least op S x
}.

Class WellOrder U `{
    WOT : TotalOrder U,
    WOW : WellOrdered U le
}.

Class SupremumComplete {U} (op : U → U → Prop) := {
    sup_complete : ∀ S : U → Prop, (∃ x, S x) →
        has_upper_bound op S → has_supremum op S
}.

Definition is_chain {U} (op : U → U → Prop) (S : U → Prop)
    := ∀ a b : U, S a → S b → op a b ∨ op b a.

Definition well_orders {U} (op : U → U → Prop) :=
    inhabited (Connex op) ∧
    inhabited (Antisymmetric op) ∧
    inhabited (Transitive op) ∧
    inhabited (WellOrdered op).

(* begin hide *)
Section WellOrders.
(* end hide *)
Context {U : Type} {op : U → U → Prop} `{
    Connex U op,
    Antisymmetric U op,
    Transitive U op,
    WellOrdered U op
}.

Theorem wo_wo : well_orders op.
Proof.
    repeat (split; try assumption).
Qed.

Theorem upper_bound_leq : ∀ S a b,
    ¬is_upper_bound op S a → is_upper_bound op S b → strict op a b.
Proof.
    intros S a b Sa Sb.
    split; [>|intro; subst; contradiction].
    unfold is_upper_bound in *.
    rewrite not_all in Sa.
    destruct Sa as [x Sa].
    rewrite not_impl in Sa.
    rewrite nle_lt in Sa.
    destruct Sa as [Sx [ax ax']].
    specialize (Sb x Sx).
    exact (trans ax Sb).
Qed.

Theorem lower_bound_leq : ∀ S a b,
    ¬is_lower_bound op S a → is_lower_bound op S b → strict op b a.
Proof.
    intros S a b Sa Sb.
    split; [>|intro; subst; contradiction].
    unfold is_lower_bound in *.
    rewrite not_all in Sa.
    destruct Sa as [x Sa].
    rewrite not_impl in Sa.
    rewrite nle_lt in Sa.
    destruct Sa as [Sx [ax ax']].
    specialize (Sb x Sx).
    exact (trans Sb ax).
Qed.

(* begin hide *)
End WellOrders.

Section SupremumComplete.

Context {U} `{
    OrderedField U,
    @SupremumComplete U le,
    @Dense U le
}.
(* end hide *)
Theorem inf_complete : ∀ S : U → Prop, (∃ x, S x) →
    has_lower_bound le S → has_infimum le S.
Proof.
    intros S S_ex S_lower.
    pose (S' x := S (-x)).
    pose proof (sup_complete S') as S'_sup.
    prove_parts S'_sup.
    {
        destruct S_ex as [x Sx].
        exists (-x).
        unfold S'.
        rewrite neg_neg.
        exact Sx.
    }
    {
        destruct S_lower as [x x_lower].
        exists (-x).
        intros y S'y.
        specialize (x_lower (-y) S'y).
        rewrite le_half_rneg.
        exact x_lower.
    }
    destruct S'_sup as [α [α_ub α_lub]].
    exists (-α).
    split.
    -   intros x Sx.
        rewrite le_half_lneg.
        apply α_ub.
        unfold S'.
        rewrite neg_neg.
        exact Sx.
    -   intros y y_lower.
        rewrite le_half_rneg.
        apply α_lub.
        intros x S'x.
        rewrite le_half_rneg.
        apply y_lower.
        exact S'x.
Qed.

Theorem supremum_upper : ∀ (S : U → Prop) (α : U),
    is_supremum le S α ↔ is_supremum le (λ x, ¬is_upper_bound le S x) α.
Proof.
    intros S α.
    split; intros [α_upper α_least].
    -   split.
        +   intros x x_nupper.
            unfold is_upper_bound in *.
            rewrite not_all in x_nupper.
            destruct x_nupper as [y x_nupper].
            rewrite not_impl in x_nupper.
            destruct x_nupper as [Sy xy].
            rewrite nle_lt in xy.
            apply (lt_le_trans xy).
            apply α_upper.
            exact Sy.
        +   intros y y_upper.
            classic_contradiction ltq.
            rewrite nle_lt in ltq.
            pose proof (dense _ _ ltq) as [z [z_lt z_gt]].
            assert (¬is_upper_bound le S z) as z_nupper.
            {
                intros contr.
                apply α_least in contr.
                destruct (le_lt_trans contr z_gt); contradiction.
            }
            apply y_upper in z_nupper.
            destruct (lt_le_trans z_lt z_nupper); contradiction.
    -   split.
        +   intros x Sx.
            classic_contradiction ltq.
            rewrite nle_lt in ltq.
            pose proof (dense _ _ ltq) as [z [z_lt z_gt]].
            assert (¬is_upper_bound le S z) as z_nupper.
            {
                intros contr.
                apply contr in Sx.
                destruct (le_lt_trans Sx z_gt); contradiction.
            }
            apply α_upper in z_nupper.
            destruct (lt_le_trans z_lt z_nupper); contradiction.
        +   intros y y_upper.
            apply α_least.
            intros z z_nupper.
            unfold is_upper_bound in z_nupper.
            rewrite not_all in z_nupper.
            destruct z_nupper as [a z_nupper].
            rewrite not_impl, nle_lt in z_nupper.
            destruct z_nupper as [Sa za].
            apply y_upper in Sa.
            apply (lt_le_trans za Sa).
Qed.

Theorem has_supremum_upper : ∀ (S : U → Prop),
    has_supremum le S ↔ has_supremum le (λ x, ¬is_upper_bound le S x).
Proof.
    intros S.
    split; intros [α α_sup].
    all: exists α.
    -   rewrite <- supremum_upper.
        exact α_sup.
    -   rewrite supremum_upper.
        exact α_sup.
Qed.
(* begin hide *)
End SupremumComplete.
(* end hide *)
