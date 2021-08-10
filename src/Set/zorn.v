Require Import init.
Require Export order_def.
Require Import set_base.
Require Import set_type.
Require Import function.

(* begin hide *)
Module BourbakiModule.
Section Bourbaki.

Local Open Scope set_scope.

Context {U : Type}.
Variable (op : U → U → Prop).
Context `{
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op
}.

Local Instance op_le : Order U := {
    le := op
}.

Variable a : U.
Hypothesis chain_sup : ∀ S : U → Prop, is_chain op S → has_supremum op S.
Variable f : U → U.
Hypothesis f_ge : ∀ x, op x (f x).

Definition admissable (A : U → Prop) :=
    A a ∧
    (λ y, ∃ x, A x ∧ f x = y) ⊆ A ∧
    ∀ F, F ≠ ∅ → is_chain op F → F ⊆ A → (∀ x, is_supremum le F x → A x).

Definition M (x : U) := ∀ A : U → Prop, admissable A → A x.

Lemma M_admissable : admissable M.
    repeat split.
    -   intros A [A_a C].
        apply A_a.
    -   intros y [x [x_in eq]] A A_ad.
        apply A_ad.
        exists x.
        split; try assumption.
        apply x_in.
        exact A_ad.
    -   intros F F_nempty F_chain F_sub x x_sup A A_ad.
        apply (rand (rand A_ad) F F_nempty F_chain).
        +   apply (trans F_sub).
            intros y y_in.
            apply y_in.
            exact A_ad.
        +   exact x_sup.
Qed.

Lemma M_sub_admissable : ∀ M0, M0 ⊆ M → admissable M0 → M0 = M.
    intros M0 M0_sub M0_admissable.
    apply antisym; try assumption.
    intros x x_in.
    apply x_in.
    exact M0_admissable.
Qed.

Lemma MfM : ∀ x, M x → M (f x).
    intros x Mx.
    apply M_admissable.
    exists x.
    split.
    -   exact Mx.
    -   reflexivity.
Qed.

Definition A x := M x ∧ a <= x.
Lemma A_sub : A ⊆ M.
    intros x x_in.
    apply x_in.
Qed.
Lemma A_admissable : admissable A.
    split.
    2: split.
    -   split; try apply refl.
        apply (land M_admissable).
    -   intros y [x [x_in x_eq]].
        split.
        +   rewrite <- x_eq.
            apply MfM.
            apply x_in.
        +   destruct x_in as [Mx eq].
            apply (trans eq).
            rewrite <- x_eq.
            apply f_ge.
    -   intros F F_nempty F_chain F_sub w w_sup.
        split.
        +   apply (rand (rand M_admissable) F F_nempty F_chain).
            *   apply (trans F_sub).
                exact A_sub.
            *   exact w_sup.
        +   apply not_empty_ex in F_nempty as [x x_in].
            specialize (F_sub _ x_in).
            apply (trans (rand F_sub)).
            apply w_sup.
            exact x_in.
Qed.
Lemma a_first : is_least le M a.
    pose proof (M_sub_admissable _ A_sub A_admissable) as AM.
    rewrite <- AM.
    split.
    -   exact (land A_admissable).
    -   intros y y_in.
        apply y_in.
Qed.

Definition P x := ∀ y, M y → y < x → f y <= x.

Definition B x z := M z ∧ (z <= x ∨ f x <= z).
Lemma B_sub : ∀ x, B x ⊆ M.
    intros x y y_in.
    apply y_in.
Qed.
Lemma B_admissable : ∀ x, M x → P x → admissable (B x).
    change op with le in *.
    intros x Mx Px.
    split.
    2: split.
    -   split.
        +   apply (land M_admissable).
        +   left.
            apply a_first.
            exact Mx.
    -   intros fz [z [Bz z_eq]].
        destruct Bz as [Mz eqs].
        rewrite <- z_eq; clear z_eq.
        split.
        +   apply MfM.
            exact Mz.
        +   destruct eqs as [eq|eq].
            *   classic_case (z = x).
                --  right.
                    rewrite e.
                    apply refl.
                --  left.
                    exact (Px z Mz (make_and eq n)).
            *   right.
                apply (trans eq (f_ge _)).
    -   intros F F_nempty F_chain F_sub w w_lub.
        split.
        +   apply (rand (rand M_admissable) F); try assumption.
            apply (trans F_sub (B_sub x)).
        +   classic_case (∀ z, F z → z <= x).
            *   destruct w_lub as [w_ub w_lub].
                specialize (w_lub _ l).
                left; exact w_lub.
            *   rewrite not_all in n.
                (* TODO: MORE EXTENSIONAL REWRITING *)
                destruct n as [z n].
                rewrite not_impl in n.
                destruct n as [Fz n].
                pose proof (F_sub _ Fz) as Bz.
                destruct Bz as [Mz [eq|eq]]; try contradiction.
                right.
                apply (trans eq).
                apply w_lub.
                exact Fz.
Qed.
Lemma BM : ∀ x, M x → P x → B x = M.
    intros x Mx Px.
    apply M_sub_admissable.
    -   apply B_sub.
    -   apply B_admissable; assumption.
Qed.
Lemma z_P : ∀ x, M x → P x → ∀ z, M z → z <= x ∨ f x <= z.
    intros x Mx Px z Mz.
    rewrite <- (BM x) in Mz; try assumption.
    apply Mz.
Qed.

Definition C x := M x ∧ P x.
Lemma C_sub : C ⊆ M.
    intros x x_in.
    apply x_in.
Qed.
Lemma C_admissable : admissable C.
    change op with le in *.
    split.
    2: split.
    -   split.
        +   apply (land M_admissable).
        +   intros z Mz [eq1 neq].
            pose proof (rand a_first z Mz) as eq2.
            pose proof (antisym eq1 eq2).
            contradiction.
    -   intros y [x [Cx x_eq]].
        rewrite <- x_eq; clear x_eq y.
        split.
        +   apply MfM.
            apply Cx.
        +   intros y My y_lt.
            destruct Cx as [Mx Px].
            destruct (z_P x Mx Px y My) as [eq|eq].
            *   classic_case (y = x); try (subst; apply refl).
                specialize (Px y My (make_and eq n)).
                exact (trans Px (f_ge _)).
            *   pose proof (lt_le_trans y_lt eq) as contr.
                destruct contr; contradiction.
    -   intros F F_nempty F_cahin F_sub w w_sup.
        assert (M w) as Mw.
        {
            apply (rand (rand M_admissable) F); try assumption.
            apply (trans F_sub).
            apply C_sub.
        }
        split; try exact Mw.
        intros y My eq.
        assert (∃ z, F z ∧ y <= z) as [z [Fz z_eq]].
        {
            classic_contradiction contr.
            rewrite not_ex in contr.
            setoid_rewrite not_and in contr.
            assert (is_upper_bound le F y) as y_upper.
            {
                intros z Fz.
                specialize (contr z) as [C|leq]; try contradiction.
                pose proof (F_sub _ Fz) as [Mz Pz].
                pose proof (z_P z Mz Pz y My) as [C|leq2];try contradiction.
                exact (trans (f_ge _) leq2).
            }
            pose proof (rand w_sup _ y_upper) as leq.
            pose proof (lt_le_trans eq leq) as neq.
            destruct neq; contradiction.
        }
        pose proof (F_sub _ Fz) as [Mz Pz].
        classic_case (y = z).
        +   subst.
            pose proof (z_P z Mz Pz w Mw) as [leq|leq].
            *   pose proof (lt_le_trans eq leq) as contr.
                destruct contr; contradiction.
            *   exact leq.
        +   specialize (Pz y My (make_and z_eq n)).
            apply (trans Pz).
            apply w_sup.
            exact Fz.
Qed.
Lemma all_P : M ⊆ P.
    pose proof (M_sub_admissable _ C_sub C_admissable) as CM.
    rewrite <- CM.
    apply inter_rsub.
Qed.

Lemma M_chain : is_chain le M.
    change op with le in *.
    intros x y Mx My.
    classic_case (y <= x).
    -   right; exact l.
    -   left.
        apply (trans (f_ge _)).
        pose proof Mx as Px; apply all_P in Px.
        pose proof My as By; rewrite <- (BM x Mx Px) in By.
        destruct By as [C [eq|eq]]; clear C.
        +   contradiction.
        +   exact eq.
Qed.

Theorem bourbaki : ∃ x, f x = x.
    change op with le in *.
    assert (M ≠ ∅) as M_nempty.
    {
        intros contr.
        pose proof (land M_admissable) as a_in.
        rewrite contr in a_in.
        contradiction a_in.
    }
    pose proof (rand (rand M_admissable) M M_nempty M_chain (refl _))
        as sup_in.
    specialize (chain_sup M M_chain) as [x x_lub].
    exists x.
    apply antisym; try apply f_ge.
    specialize (sup_in x x_lub).
    apply x_lub.
    apply M_admissable.
    exists x.
    split; try assumption.
    reflexivity.
Qed.

End Bourbaki.
End BourbakiModule.
Section Bourbaki.

Context {U : Type}.
Variable (op : U → U → Prop).
Context `{
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op
}.
(* end hide *)
Theorem bourbaki : U → (∀ S, is_chain op S → has_supremum op S) →
        ∀ f, (∀ x, op x (f x)) → ∃ x, f x = x.
    apply BourbakiModule.bourbaki; assumption.
Qed.

(* begin hide *)
End Bourbaki.



Module HausdorffModule.
Section Hausdorff.

Local Open Scope set_scope.

Context {U : Type}.
Variable (op : U → U → Prop).
Context `{
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op
}.

Local Instance op_le : Order U := {
    le := op
}.

Hypothesis not_hausdorff
        : ∀ G : U → Prop, is_chain le G → ∃ F, is_chain le F ∧ G ⊂ F.

Definition A F := is_chain le F.
Local Instance sub_le : Order (U → Prop) := {
    le := subset
}.

Definition g := make_set_function A (λ X, ex_val (not_hausdorff [X|] [|X])).
Lemma g_in_A : ∀ X, A (g⟨X⟩).
    intros X.
    unfold g; cbn.
    unpack_ex_val Y Y_ex HY; rewrite Y_ex.
    apply HY.
Qed.
Definition g2 X := [_|g_in_A X].

Lemma g_in : ∀ X, X < g2 X.
    intros X.
    unfold g2, g; cbn.
    split.
    -   intros x Xx; cbn.
        unpack_ex_val Y Y_ex HY; rewrite Y_ex.
        destruct HY as [Y_chain X_sub_Y].
        apply X_sub_Y.
        exact Xx.
    -   intros contr.
        destruct X as [X X_chain].
        inversion contr as [eq]; clear contr.
        rewrite_ex_val X' X_eq.
        subst X'.
        apply X_eq.
        reflexivity.
Qed.

Lemma chain_supremum : ∀ S : set_type A → Prop,
        is_chain le S → has_supremum le S.
    intros S S_chain.
    pose (W x := ∃ X, S X ∧ [X|] x).
    assert (is_chain le W) as W_chain.
    {
        intros a b Wa Wb.
        destruct Wa as [Y [SY Ya]].
        destruct Wb as [Z [SZ Za]].
        specialize (S_chain Y Z SY SZ) as [YZ|ZY].
        -   apply YZ in Ya.
            exact ([|Z] a b Ya Za).
        -   apply ZY in Za.
            exact ([|Y] a b Ya Za).
    }
    exists [W|W_chain].
    split.
    -   intros X SX x Xx; cbn.
        exists X.
        split; assumption.
    -   intros Y Y_ub x Wx.
        destruct Wx as [X [SX Xx]].
        specialize (Y_ub X SX).
        apply Y_ub.
        exact Xx.
Qed.

Theorem hausdorff : False.
    assert (A ∅) as empty_in.
    {
        intros a b a_in b_in.
        contradiction a_in.
    }
    pose proof (bourbaki le [∅|empty_in] chain_supremum g2 (λ X, land (g_in X)))
        as [[X X_chain] X_eq].
    pose proof (g_in [X|X_chain]) as eq.
    rewrite X_eq in eq.
    apply eq.
    reflexivity.
Qed.

End Hausdorff.
End HausdorffModule.
Section Hausdorff.

Context {U : Type}.
Variable (op : U → U → Prop).
Context `{
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op
}.

Local Open Scope set_scope.
(* end hide *)
Theorem hausdorff : ∃ M : U → Prop,
        is_chain op M ∧ (∀ F : U → Prop, is_chain op F → ¬(M ⊂ F)).
    classic_contradiction contr.
    apply (HausdorffModule.hausdorff op).
    intros G G_chain.
    rewrite not_ex in contr.
    setoid_rewrite not_and in contr.
    specialize (contr G) as [C|contr]; try contradiction.
    rewrite not_all in contr.
    (* TODO: MORE EXTENSIONAL REWRITING *)
    destruct contr as [F contr].
    exists F.
    rewrite not_impl in contr.
    rewrite not_not in contr.
    exact contr.
Qed.

(* begin hide *)
End Hausdorff.



Module ZornModule.
Section Zorn.

Context {U : Type}.
Variable (op : U → U → Prop).
Context `{
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op
}.

Local Instance op_le : Order U := {
    le := op
}.

Hypothesis all_upper : ∀ F : U → Prop, is_chain le F → has_upper_bound le F.

Theorem zorn : ∃ a, ∀ x, ¬(a < x).
    pose proof (hausdorff le) as [A [A_chain A_max]].
    pose proof (all_upper A A_chain) as [a a_upper].
    exists a.
    intros x contr.
    assert (¬A x) as Ax.
    {
        intro Ax.
        specialize (a_upper _ Ax).
        pose proof (le_lt_trans a_upper contr) as [C1 C2].
        contradiction.
    }
    pose (B y := A y ∨ x = y).
    assert (is_chain le B) as B_chain.
    {
        intros m n Bm Bn.
        destruct Bm as [Am|mx]; destruct Bn as [An|nx].
        -   apply A_chain; assumption.
        -   subst n.
            left.
            apply (trans (a_upper _ Am)).
            apply contr.
        -   subst m.
            right.
            apply (trans (a_upper _ An)).
            apply contr.
        -   subst m n.
            left; apply refl.
    }
    apply (A_max _ B_chain).
    split.
    -   intros y Ay.
        left; exact Ay.
    -   intros eq.
        rewrite eq in Ax.
        unfold B in Ax.
        rewrite not_or in Ax.
        destruct Ax.
        contradiction.
Qed.

End Zorn.
End ZornModule.
Section Zorn.

Context {U : Type}.
Variable (op : U → U → Prop).
Context `{
    Reflexive U op,
    Antisymmetric U op,
    Transitive U op
}.

Local Instance zorn_order : Order U := {le := op}.
(* end hide *)
Theorem zorn : (∀ F : U → Prop, is_chain le F → has_upper_bound le F) →
        ∃ a : U, ∀ x : U, ¬ a < x.
    apply ZornModule.zorn; assumption.
Qed.

(* begin hide *)
End Zorn.
(* end hide *)
