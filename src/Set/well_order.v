Require Import init.

Require Import zorn.
Require Import zorn_function.
Require Export order_def.
Require Import set_base.
Require Import set_type.
Require Import set_function.

(* begin hide *)
Module WellOrderModule.
Section WellOrder.

Local Open Scope set.

Context {U : Type}.

Definition S (A : bin_set_function_type U Prop)
    := well_orders (bin_set_function A).
Local Instance bin_order : Order (bin_set_function_type U Prop):= {
    le A B := bin_func_le A B
}.
Local Instance S_order : Order (set_type S) := {
    le A B :=
        ∃ sub : ([A|] ≤ [B|]),
        ∀ (a : set_type (bin_domain [A|])) (b : set_type (bin_domain [B|])),
            ¬bin_domain [A|] [b|] → [B|]⟨[_|ex_val sub [a|] [|a]], b⟩
}.
Lemma S_order_refl : ∀ A, A ≤ A.
Proof.
    intros [A [[A_con] [[A_antisym] [[A_trans] [[A_well]]]]]].
    exists (refl A).
    intros a b Ab.
    cbn in *.
    destruct b.
    contradiction.
Qed.
Local Instance S_order_refl_class : Reflexive le := {
    refl := S_order_refl
}.
Lemma S_order_antisym : ∀ A B, A ≤ B → B ≤ A → A = B.
Proof.
    intros [A A_wo] [B B_wo] [AB AB2] [BA BA2].
    apply set_type_eq; cbn in *.
    apply antisym; assumption.
Qed.
Local Instance S_order_antisym_class : Antisymmetric le := {
    antisym := S_order_antisym
}.
Lemma S_order_trans : ∀ A B C, A ≤ B → B ≤ C → A ≤ C.
Proof.
    intros [A A_wo] [B B_wo] [C C_wo] [AB AB2] [BC BC2].
    unfold le in *; cbn in *.
    exists (trans AB BC).
    intros a c Ac.
    classic_case (A = B) as [BC_eq|BC_neq].
    2: classic_case (bin_domain B [c|]) as [Bc|Bc].
    -   subst B.
        specialize (BC2 a c Ac).
        rewrite (proof_irrelevance _ BC).
        exact BC2.
    -   clear BC2.
        specialize (AB2 a [_|Bc] Ac).
        destruct BC as [BC_sub BC].
        rewrite BC in AB2; cbn in *.
        pose proof (BC_sub [a|] (ex_val AB [a|] [|a])) as Ca.
        rewrite (proof_irrelevance _ Ca).
        rewrite (proof_irrelevance _ Ca) in AB2.
        assert (c = [[c|]|BC_sub [c|] Bc]) as eq
            by (apply set_type_eq; reflexivity).
        rewrite eq.
        exact AB2.
    -   assert (∃ b : set_type (bin_domain B), ¬bin_domain A [b|]) as [b Ab].
        {
            clear AB2 BC BC2 c Ac Bc a C C_wo.
            classic_contradiction contr.
            rewrite not_ex in contr.
            assert (∀ a : set_type (bin_domain B), bin_domain A [a|]) as contr'.
            {
                intros a.
                rewrite <- (not_not (bin_domain A [a|])).
                exact (contr a).
            }
            apply BC_neq.
            apply antisym; try assumption.
            unfold bin_func_le.
            assert (bin_domain B ⊆ bin_domain A) as sub.
            {
                intros b Bb.
                exact (contr' [_|Bb]).
            }
            exists sub.
            intros a b.
            destruct AB as [C0 AB].
            specialize (AB [_|contr' a] [_|contr' b]); cbn in *.
            rewrite (proof_irrelevance _ (contr' a)).
            rewrite (proof_irrelevance _ (contr' b)).
            rewrite AB.
            apply f_equal2; apply set_type_eq; reflexivity.
        }
        clear BC_neq.
        specialize (AB2 a b Ab).
        specialize (BC2 b c Bc).
        remember (ex_val (trans AB BC) [a|] [|a]) as Ca; clear HeqCa.
        remember (ex_val AB [a|] [|a]) as Ba; clear HeqBa.
        remember (ex_val BC [b|] [|b]) as Cb; clear HeqCb.
        destruct BC as [C0 BC].
        rewrite BC in AB2; cbn in *.
        rewrite (proof_irrelevance _ Ca) in AB2.
        rewrite (proof_irrelevance _ Cb) in AB2.
        destruct C_wo as [C_connex [C_antisym [[C_trans]]]].
        exact (trans AB2 BC2).
Qed.
Local Instance S_order_trans_class : Transitive le := {
    trans := S_order_trans
}.

Section CreateUpperBound.

Variable C : set_type S → Prop.
Hypothesis C_chain : is_chain le C.

Lemma S_all_equal : ∀ F G : set_type S, C F → C G → ∀ a b
    (Fa : bin_domain [F|] a) (Fb : bin_domain [F|] b)
    (Ga : bin_domain [G|] a) (Gb : bin_domain [G|] b),
    [F|]⟨[a|Fa], [b|Fb]⟩ = [G|]⟨[a|Ga], [b|Gb]⟩.
Proof.
    intros F G CF CG a b Fa Fb Ga Gb.
    destruct (C_chain F G CF CG) as [FG|GF].
    -   destruct FG as [FG C0]; clear C0.
        destruct FG as [sub FG].
        specialize (FG [_|Fa] [_|Fb]); cbn in FG.
        rewrite (proof_irrelevance _ Ga) in FG.
        rewrite (proof_irrelevance _ Gb) in FG.
        exact FG.
    -   destruct GF as [GF C0]; clear C0.
        destruct GF as [sub GF].
        specialize (GF [_|Ga] [_|Gb]); cbn in GF.
        rewrite (proof_irrelevance _ Fa) in GF.
        rewrite (proof_irrelevance _ Fb) in GF.
        symmetry; exact GF.
Qed.

Definition S_union_set x := ∃ X, C X ∧ bin_domain [X|] x.

Lemma S_union_func_ex : ∀ a b : set_type S_union_set,
    ∃ X, C X ∧ bin_domain [X|] [a|] ∧ bin_domain [X|] [b|].
Proof.
    intros [a [X [CX Xa]]] [b [Y [CY Yb]]]; cbn.
    destruct (C_chain X Y CX CY) as [sub|sub].
    -   destruct sub as [sub f_sub].
        apply sub in Xa.
        exists Y.
        repeat split; assumption.
    -   destruct sub as [sub f_sub].
        apply sub in Yb.
        exists X.
        repeat split; assumption.
Qed.

Definition S_union_le a b :=
    let P := S_union_func_ex a b in
    [ex_val P|]⟨
        [_|land (rand (ex_proof P))],
        [_|rand (rand (ex_proof P))]
    ⟩.

Local Instance S_union_order : Order (set_type S_union_set) := {
    le := S_union_le
}.

Ltac make_definitions a b PF F CF Fa Fb :=
    let Fx' := fresh in
    pose (PF := S_union_func_ex a b);
    pose (F := ex_val PF);
    pose (FX' := ex_proof PF);
    change (ex_type_val (ex_to_type PF)) with F in FX';
    destruct FX' as [CF [Fa Fb]].

Lemma S_union_le_connex : ∀ a b, {a ≤ b} + {b ≤ a}.
Proof.
    intros a b.
    apply or_to_strong.
    unfold le; cbn; unfold S_union_le; cbn.
    make_definitions a b PF F CF Fa Fb.
    make_definitions b a PG G CG Ga Gb.
    fold PF PG F G.
    rewrite (proof_irrelevance _ Fa).
    rewrite (proof_irrelevance _ Fb).
    rewrite (proof_irrelevance _ Ga).
    rewrite (proof_irrelevance _ Gb).
    destruct [|F] as [[[F_connex]] C0]; clear C0.
    destruct (F_connex [_|Fa] [_|Fb]) as [leq|leq].
    1: left; exact leq.
    right.
    rewrite <- (S_all_equal F G CF CG _ _ Fb Fa).
    exact leq.
Qed.

Lemma S_union_le_antisym : ∀ a b, a ≤ b → b ≤ a → a = b.
Proof.
    intros a b ab ba.
    unfold le in ab, ba; cbn in ab, ba; unfold S_union_le in *; cbn in ab, ba.
    make_definitions a b PF F CF Fa Fb.
    make_definitions b a PG G CG Ga Gb.
    fold PF PG F G in ab, ba.
    rewrite (proof_irrelevance _ Fa) in ab.
    rewrite (proof_irrelevance _ Fb) in ab.
    rewrite (proof_irrelevance _ Ga) in ba.
    rewrite (proof_irrelevance _ Gb) in ba.
    destruct [|F] as [C0 [[[F_antisym]] C1]]; clear C0 C1.
    rewrite <- (S_all_equal F G CF CG _ _ Fb Fa) in ba.
    specialize (F_antisym _ _ ab ba).
    apply set_type_eq.
    inversion F_antisym.
    reflexivity.
Qed.

Lemma S_union_le_trans : ∀ a b c, a ≤ b → b ≤ c → a ≤ c.
Proof.
    intros a b c ab bc.
    unfold le; unfold le in ab, bc; cbn in *.
    unfold S_union_le in *; cbn in *.
    make_definitions a b PF F CF Fa Fb.
    make_definitions b c PG G CG Gb Gc.
    make_definitions a c PH H CH Ha Hc.
    fold PF PG PH F G H in ab, bc.
    fold PF PG PH F G H.
    rewrite (proof_irrelevance _ Fa) in ab.
    rewrite (proof_irrelevance _ Fb) in ab.
    rewrite (proof_irrelevance _ Gb) in bc.
    rewrite (proof_irrelevance _ Gc) in bc.
    rewrite (proof_irrelevance _ Ha).
    rewrite (proof_irrelevance _ Hc).
    destruct (C_chain F G CF CG) as [[[FG C0] C1]|[[GF C0] C1]]; clear C0 C1.
    -   specialize (FG _ Fa) as Ga; clear FG.
        rewrite (S_all_equal F G CF CG _ _ _ _ Ga Gb) in ab.
        rewrite (S_all_equal H G CH CG _ _ _ _ Ga Gc).
        destruct [|G] as [C0 [C1 [[[G_trans]] C2]]]; clear C0 C1 C2.
        exact (G_trans _ _ _ ab bc).
    -   specialize (GF _ Gc) as Fc; clear GF.
        rewrite (S_all_equal G F CG CF _ _ _ _ Fb Fc) in bc.
        rewrite (S_all_equal H F CH CF _ _ _ _ Fa Fc).
        destruct [|F] as [C0 [C1 [[[F_trans]] C2]]]; clear C0 C1 C2.
        exact (F_trans _ _ _ ab bc).
Qed.

Lemma S_union_le_wo : ∀ A : set_type (S_union_set) → Prop,
    (∃ M : set_type (S_union_set), A M)
    → ∃ M : set_type (S_union_set), is_least le A M.
Proof.
    intros A [b Ab].
    destruct [|b] as [F [CF Fb]].
    destruct [|F] as [[F_connex] [C1 [C2 [[F_wo]]]]]; clear C1 C2.
    assert (bin_domain [F|] ⊆ S_union_set) as F_sub_S.
    {
        intros x Fx.
        exists F.
        split; assumption.
    }
    pose (BA (x : set_type (bin_domain [F|])) := A [_|F_sub_S [x|] [|x]]).
    assert (∃ x, BA x) as BA_nempty.
    {
        exists [_|Fb].
        unfold BA; cbn.
        destruct b as [b b_in]; cbn.
        rewrite (proof_irrelevance _ b_in).
        exact Ab.
    }
    specialize (F_wo BA BA_nempty) as [a [BAa a_min]].
    pose proof (F_sub_S [a|] [|a]) as Sa.
    exists [_|Sa].
    split.
    -   unfold BA in BAa.
        rewrite (proof_irrelevance _ Sa) in BAa.
        exact BAa.
    -   intros y Ay.
        pose proof [|y] as [G [CG Gy]].
        make_definitions [[a|]|Sa] y PH H CH Hy Ha.
        unfold le; cbn; unfold S_union_le; cbn.
        fold PH.
        change (ex_val PH) with H.
        rewrite (proof_irrelevance _ Hy).
        rewrite (proof_irrelevance _ Ha).
        classic_case (bin_domain [F|] [y|]) as [Fy|Fy].
        +   specialize (a_min [_|Fy]).
            prove_parts a_min.
            {
                unfold BA; cbn.
                rewrite set_type_simpl.
                exact Ay.
            }
            destruct a as [a Fa].
            rewrite (S_all_equal _ _ CF CH _ _ _ _ Hy Ha) in a_min.
            exact a_min.
        +   destruct (C_chain _ _ CF CG) as [FG|GF].
            *   destruct FG as [FG FG_add].
                specialize (FG_add a [_|Gy] Fy).
                rewrite (S_all_equal _ _ CG CH _ _ _ _ Hy Ha) in FG_add.
                cbn in FG_add.
                exact FG_add.
            *   destruct GF as [GF C0]; clear C0.
                destruct GF as [sub C0]; clear C0.
                apply sub in Gy.
                contradiction.
Qed.

Definition S_union_le_func := make_bin_set_function S_union_set S_union_le.

Lemma S_union_le_func_wo : S S_union_le_func.
Proof.
    repeat split.
    -   apply S_union_le_connex.
    -   apply S_union_le_antisym.
    -   apply S_union_le_trans.
    -   apply S_union_le_wo.
Qed.

Lemma S_all_upper : has_upper_bound le C.
Proof.
    exists [_|S_union_le_func_wo].
    intros F CF.
    assert ([F|] ≤ S_union_le_func) as sub.
    {
        assert (bin_domain [F|] ⊆ S_union_set) as sub.
        {
            intros x Fx.
            exists F.
            split; assumption.
        }
        exists sub.
        intros a b.
        unfold S_union_le_func; cbn.
        unfold S_union_le; cbn.
        pose proof (sub [a|] [|a]) as Sa.
        pose proof (sub [b|] [|b]) as Sb.
        rewrite (proof_irrelevance _ Sa).
        rewrite (proof_irrelevance _ Sb).
        make_definitions [[a|]|Sa] [[b|]|Sb] PG G CG Ga Gb.
        fold PG G.
        destruct a, b.
        apply S_all_equal; assumption.
    }
    exists sub.
    intros a b Fb; cbn in *.
    unfold S_union_le; cbn.
    pose proof (ex_val sub [a|] [|a]) as Sa.
    rewrite (proof_irrelevance _ Sa).
    make_definitions [[a|]|Sa] b PG G CG Ga Gb.
    cbn in *.
    destruct (C_chain F G CF CG) as [FG|GF]; try assumption.
    -   destruct FG as [sub2 FG].
        specialize (FG a [_|Gb] Fb).
        rewrite (proof_irrelevance _ Ga) in FG.
        rewrite (proof_irrelevance _ Ga).
        rewrite (proof_irrelevance _ Gb).
        exact FG.
    -   destruct GF as [[sub2]].
        apply sub2 in Gb.
        contradiction.
Qed.

End CreateUpperBound.

Definition A := ex_val (zorn le S_all_upper).

Section All.

Variable x : U.
Hypothesis not_max : ¬bin_domain [A|] x.

Definition A'_set := bin_domain [A|] ∪ ❴x❵.
Definition A'_set_proof (a : set_type A'_set) :
        {bin_domain [A|] [a|]} + { ❴x❵ [a|]}.
    apply or_to_strong.
    exact [|a].
Qed.
Definition A'_func (a b : set_type A'_set) :=
    match A'_set_proof b with
    | strong_or_left Ab =>
        match A'_set_proof a with
        | strong_or_left Aa => [A|]⟨[_|Aa], [_|Ab]⟩
        | _ => False
        end
    | _ => True
    end.

Local Instance A'_order : Order (set_type A'_set) := {
    le := A'_func
}.

Lemma A'_connex : ∀ a b, {a ≤ b} + {b ≤ a}.
Proof.
    intros a b.
    unfold le; cbn; unfold A'_func; cbn.
    apply or_to_strong.
    destruct (A'_set_proof b).
    1: destruct (A'_set_proof a).
    -   destruct [|A] as [[[A_connex]] C0]; clear C0.
        destruct (A_connex [_|b1] [_|b0]).
        +   left; assumption.
        +   right; assumption.
    -   right; trivial.
    -   left; trivial.
Qed.

Lemma A'_antisym : ∀ a b, a ≤ b → b ≤ a → a = b.
Proof.
    intros a b ab ba.
    unfold le in *; cbn in *; unfold A'_func in *; cbn in *.
    destruct (A'_set_proof a) as [Aa|xa]; destruct (A'_set_proof b) as [Ab|xb].
    -   destruct [|A] as [C0 [[[A_antisym]] C1]]; clear C0 C1.
        specialize (A_antisym _ _ ab ba).
        apply set_type_eq.
        inversion A_antisym.
        reflexivity.
    -   contradiction.
    -   contradiction.
    -   rewrite singleton_eq in xa, xb.
        rewrite xa in xb.
        apply set_type_eq.
        exact xb.
Qed.
Local Instance A'_antisym_class : Antisymmetric le := {
    antisym := A'_antisym
}.

Lemma A'_trans : ∀ a b c, a ≤ b → b ≤ c → a ≤ c.
Proof.
    intros a b c ab bc.
    unfold le in *; cbn in *; unfold A'_func in *; cbn in *.
    destruct (A'_set_proof c) as [Ac|xc].
    -   destruct (A'_set_proof b) as [Ab|xb].
        +   destruct (A'_set_proof a) as [Aa|xa].
            *   destruct [|A] as [C0 [C1 [[[A_trans]] C2]]]; clear C0 C1 C2.
                exact (A_trans _ _ _ ab bc).
            *   contradiction.
        +   contradiction.
    -   trivial.
Qed.

Lemma A'_sub : bin_domain [A|] ⊆ A'_set.
Proof.
    intros a Aa.
    left.
    exact Aa.
Qed.

Lemma A'_wo : ∀ A : set_type (A'_set) → Prop,
    (∃ M : set_type (A'_set), A M)
    → ∃ M : set_type (A'_set), is_least le A M.
Proof.
    intros S [a Sa].
    destruct [|A] as [C0 [C1 [C2 [[A_wo]]]]]; clear C0 C1 C2.
    pose (S' x := S [_|A'_sub [x|] [|x]]).
    classic_case (∃ m, S' m) as [exM|nexM].
    -   specialize (A_wo S' exM) as [m [S'm m_max]].
        exists [_|A'_sub _ [|m]].
        split.
        +   apply S'm.
        +   intros y Sy.
            unfold le; cbn; unfold A'_func; cbn.
            pose proof (A'_sub _ [|m]) as A'm.
            rewrite (proof_irrelevance _ A'm).
            destruct (A'_set_proof [_|A'm]); cbn in *.
            *   rewrite set_type_simpl.
                destruct (A'_set_proof y); cbn in *.
                --  apply (m_max [_|b0]).
                    destruct y as [y A'y]; cbn.
                    unfold S'; cbn.
                    rewrite (proof_irrelevance _ A'y).
                    exact Sy.
                --  exact true.
            *   rewrite singleton_eq in l.
                destruct m as [m Am]; cbn in *.
                subst m.
                contradiction.
    -   exists a.
        split; try assumption.
        intros [y A'y] Sy.
        destruct A'y as [Ay|xy].
        +   rewrite not_ex in nexM.
            specialize (nexM [_|Ay]).
            unfold S' in nexM.
            cbn in nexM.
            rewrite (proof_irrelevance _ (A'_sub y Ay)) in Sy.
            contradiction.
        +   pose proof xy as xy'.
            rewrite singleton_eq in xy'.
            subst.
            assert (A'_set x) as Ax by (right; reflexivity).
            rewrite (proof_irrelevance _ Ax) in Sy.
            rewrite (proof_irrelevance _ Ax).
            unfold le; cbn; unfold A'_func; cbn.
            destruct (A'_set_proof [x | Ax]); try trivial.
            contradiction.
Qed.

Definition A' := make_bin_set_function A'_set A'_func.

Lemma A'_S : S A'.
Proof.
    repeat split.
    -   apply A'_connex.
    -   apply A'_antisym.
    -   apply A'_trans.
    -   apply A'_wo.
Qed.

Lemma A_all_base : False.
Proof.
    assert (∀ X, ¬A < X) as A_max by apply (ex_proof (zorn le S_all_upper)).
    apply (A_max [A'|A'_S]).
    split.
    -   assert ([A|] ≤ A') as sub.
        {
            exists A'_sub.
            intros a b.
            cbn; unfold A'_func; cbn.
            pose proof (A'_sub [a|] [|a]) as A'a.
            pose proof (A'_sub [b|] [|b]) as A'b.
            rewrite (proof_irrelevance _ A'a).
            rewrite (proof_irrelevance _ A'b).
            destruct (A'_set_proof [_|A'b]).
            1: destruct (A'_set_proof [_|A'a]); cbn in *.
            -   destruct a as [a Aa], b as [b Ab].
                cbn.
                rewrite (proof_irrelevance b1 Aa).
                rewrite (proof_irrelevance b0 Ab).
                reflexivity.
            -   rewrite singleton_eq in l; cbn in l.
                rewrite l in not_max.
                contradiction not_max.
                exact [|a].
            -   rewrite singleton_eq in l; cbn in l.
                rewrite l in not_max.
                contradiction not_max.
                exact [|b].
        }
        exists sub.
        intros a b Ab; cbn in *.
        unfold A'_func.
        destruct (A'_set_proof b).
        +   contradiction.
        +   trivial.
    -   intros eq.
        pose proof not_max as not_max2.
        rewrite eq in not_max2.
        cbn in not_max2.
        unfold A'_set, union in not_max2.
        rewrite not_or in not_max2.
        destruct not_max2 as [C0 neq].
        contradiction neq.
        reflexivity.
Qed.

End All.

Lemma A_all : ∀ x, bin_domain [A|] x.
Proof.
    intros x.
    classic_contradiction Ax.
    exact (A_all_base x Ax).
Qed.

Definition wo_le a b := [A|]⟨[_|A_all a], [_|A_all b]⟩.

Lemma wo_connex : ∀ a b, {wo_le a b} + {wo_le b a}.
Proof.
    intros a b.
    classic_case (wo_le a b).
    -   left; assumption.
    -   right.
        destruct [|A] as [[A_connex]].
        destruct (connex [_|A_all a] [_|A_all b]); try contradiction.
        exact b0.
Qed.
Lemma wo_antisym : ∀ a b, wo_le a b → wo_le b a → a = b.
Proof.
    destruct [|A] as [A_connex [[A_antisym]]].
    intros a b ab ba.
    unfold wo_le in *.
    pose proof (antisym ab ba).
    inversion H0.
    reflexivity.
Qed.
Lemma wo_trans : ∀ a b c, wo_le a b → wo_le b c → wo_le a c.
Proof.
    unfold wo_le.
    destruct [|A] as [A_connex [A_antisym [[A_trans]]]].
    intros a b c ab bc.
    exact (trans ab bc).
Qed.
Lemma wo_well_ordered : ∀ S : U → Prop, (∃ x, S x) → ∃ x, is_least wo_le S x.
Proof.
    intros S [x Sx].
    destruct [|A] as [A_connex [A_antisym [A_trans [[A_wo]]]]].
    pose (S' (y : set_type (bin_domain [A|])) := S [y|]).
    assert (∃ x, S' x) as S'_ex.
    {
        exists [_|A_all x].
        unfold S'; cbn.
        exact Sx.
    }
    specialize (A_wo S' S'_ex) as [[y C0] [y_in y_least]].
    exists y.
    unfold wo_le; cbn.
    split.
    -   apply y_in.
    -   intros a Sa.
        rewrite (proof_irrelevance _ C0).
        apply (y_least [_|A_all a]).
        exact Sa.
Qed.

End WellOrder.
End WellOrderModule.
Section WellOrder.

Context {U : Type}.
(* end hide *)
Definition wo_le := @WellOrderModule.wo_le U.

Instance wo_connex_class : Connex wo_le := {
    connex := WellOrderModule.wo_connex
}.
Instance wo_antisym_class : Antisymmetric wo_le := {
    antisym := WellOrderModule.wo_antisym
}.
Instance wo_trans_class : Transitive wo_le := {
    trans := WellOrderModule.wo_trans
}.
Instance wo_well_ordered_class : WellOrdered wo_le := {
    well_ordered := WellOrderModule.wo_well_ordered
}.

Theorem wo_le_wo : well_orders wo_le.
Proof.
    split; split.
    2: split.
    3: split; split.
    -   exact wo_connex_class.
    -   exact wo_antisym_class.
    -   exact wo_trans_class.
    -   exact wo_well_ordered_class.
Qed.

(* begin hide *)
End WellOrder.
(* end hide *)
