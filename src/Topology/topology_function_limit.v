Require Import init.

Require Export topology_limit.
Require Import topology_axioms.
Require Import topology_continuous.
Require Import topology_subspace.

Definition func_lim_base {U V} `{Topology U, Topology V}
    {A : U → Prop}
    (f : set_type A → V)
    (c : U)
    (l : V)
    :=
    ∀ T : V → Prop, neighborhood l T →
        ∃ S : U → Prop, neighborhood c S ∧
            image_under f (λ x, S [x|] ∧ c ≠ [x|]) ⊆ T.

Definition func_lim {U V} `{Topology U, Topology V}
    {A : U → Prop}
    (f : set_type A → V)
    (c : U)
    (l : V)
    := limit_point A c ∧ func_lim_base f c l.

(* begin hide *)
Section TopologyFunction.

Context {U V} `{Topology U, TV : Topology V, @HausdorffSpace V TV}.

Local Open Scope set_scope.
(* end hide *)

Theorem func_lim_eq : ∀ (A : U → Prop) (f g : set_type A → V) c l,
    func_lim_base f c l → (∀ x, c ≠ [x|] → f x = g x) → func_lim_base g c l.
Proof.
    intros A f g c l A_lim eq.
    intros T Tl.
    specialize (A_lim T Tl) as [S [Sc S_sub]].
    exists S.
    split; [>exact Sc|].
    intros y [x [[Sx c_neq] eq']].
    apply S_sub.
    rewrite <- eq in eq' by exact c_neq.
    exists x.
    repeat split; assumption.
Qed.

Theorem func_lim_unique : ∀ {A : U → Prop} (f : set_type A → V) c l1 l2,
    limit_point A c →
    func_lim_base f c l1 → func_lim_base f c l2 → l1 = l2.
Proof.
    intros A f c l1 l2 c_lim l1_lim l2_lim.
    classic_contradiction contr.
    pose proof (hausdorff_space l1 l2 contr)
        as [T1 [T2 [T1_open [T2_open [Tl1 [Tl2 T12]]]]]].
    specialize (l1_lim T1 (make_and T1_open Tl1)) as [S1 [S1c S1_sub]].
    specialize (l2_lim T2 (make_and T2_open Tl2)) as [S2 [S2c S2_sub]].
    specialize (c_lim (S1 ∩ S2)).
    prove_parts c_lim.
    {
        apply inter_open2.
        -   apply S1c.
        -   apply S2c.
    }
    {
        split.
        -   apply S1c.
        -   apply S2c.
    }
    unfold intersects in c_lim.
    apply not_empty_ex in c_lim as [x [[Ax xc] [S1x S2x]]].
    unfold disjoint in T12.
    apply (empty_not_ex _ T12 (f [x|Ax])).
    split.
    -   apply S1_sub.
        exists [x|Ax]; cbn.
        repeat split.
        +   exact S1x.
        +   exact xc.
    -   apply S2_sub.
        exists [x|Ax]; cbn.
        repeat split.
        +   exact S2x.
        +   exact xc.
Qed.

Theorem func_lim_id : ∀ (A : U → Prop) c,
    func_lim_base (λ x : set_type A, [x|]) c c.
Proof.
    intros A c S Sc.
    exists S.
    split; [>exact Sc|].
    intros y [x [[Sx c_neq] y_eq]].
    rewrite y_eq.
    exact Sx.
Qed.

Theorem constant_func_lim : ∀ (A : U → Prop) c l,
    func_lim_base (λ _ : set_type A, l) c l.
Proof.
    intros A c l T Tl.
    exists all.
    split.
    -   split.
        +   apply all_open.
        +   exact true.
    -   intros y [x [y_in y_eq]].
        rewrite y_eq.
        apply Tl.
Qed.

Theorem func_seq_lim : ∀ (A : U → Prop) (f : set_type A → V) c l,
    func_lim_base f c l → ∀ xn : nat → set_type (A - singleton c),
    seq_lim (λ n, [xn n|]) c → seq_lim (λ n, f [[xn n|] | land [|xn n]]) l.
Proof.
    intros A f c l cl xn xn_lim.
    intros T T_open Tl.
    specialize (cl T (make_and T_open Tl)) as [S [[S_open Sc] S_sub]].
    specialize (xn_lim S S_open Sc) as [N xn_lim].
    exists N.
    intros n n_leq.
    specialize (xn_lim n n_leq).
    apply S_sub.
    exists [[xn n|] | land [|xn n]]; cbn.
    repeat split.
    -   exact xn_lim.
    -   apply [|xn n].
Qed.

Theorem func_lim_restrict : ∀ (A : U → Prop) (f : set_type A → V) c l,
    func_lim_base f c l → ∀ (B : U → Prop),
    func_lim_base (λ x : set_type (A ∩ B), f [[x|] | land [|x]]) c l.
Proof.
    intros A f c l Af B T Tl.
    specialize (Af T Tl) as [S [Sc S_sub]].
    exists S.
    split; [>exact Sc|].
    intros y [[x [Ax Bx]] [[Sx x_neq] y_eq]]; cbn in *.
    apply S_sub.
    exists [x|Ax]; cbn.
    repeat split.
    -   exact Sx.
    -   exact x_neq.
    -   rewrite (proof_irrelevance _ Ax) in y_eq.
        exact y_eq.
Qed.

Existing Instance subspace_topology.

Theorem func_lim_continuous : ∀ (A : U → Prop) (f : set_type A → V) c,
    continuous_at f c ↔ func_lim_base f [c|] (f c).
Proof.
    intros A f c.
    split.
    -   intros f_cont T T_neigh.
        specialize (f_cont T T_neigh) as [S [Sc S_sub]].
        destruct Sc as [S_open Sc].
        destruct S_open as [S' [S'_open S_eq]]; subst S.
        exists S'.
        split; [>split|].
        +   exact S'_open.
        +   exact Sc.
        +   intros y [[x Ax] [[Sx x_neq] y_eq]]; cbn in *.
            apply S_sub.
            exists [x|Ax].
            split; assumption.
    -   intros f_lim T T_neigh.
        specialize (f_lim T T_neigh) as [S [S_neigh S_sub]].
        destruct S_neigh as [S_open Sc].
        exists (to_set_type A S).
        split; [>split|].
        +   apply subspace_open.
            exact S_open.
        +   exact Sc.
        +   intros y [x [Sx y_eq]].
            classic_case (c = x) as [eq|neq].
            {
                subst x.
                rewrite y_eq.
                apply T_neigh.
            }
            apply S_sub.
            exists x; cbn.
            repeat split; try assumption.
            intros contr.
            apply set_type_eq in contr.
            contradiction.
Qed.

Theorem func_lim_set : ∀ (A : U → Prop) (B : V → Prop)
    (f : set_type A → set_type B) c l,
    func_lim_base (λ x, [f x|]) c [l|] → func_lim_base f c l.
Proof.
    intros A B f c l lim.
    intros T' [[T [T_open T'_eq]] Tl]; subst T'.
    specialize (lim T (make_and T_open Tl)) as [S [Sc S_sub]].
    exists S.
    split; [>exact Sc|].
    intros y [[x Ax] [[Sx c_neq] y_eq]]; cbn in *.
    unfold to_set_type; cbn.
    apply S_sub.
    exists [x|Ax]; cbn.
    apply eq_set_type in y_eq.
    repeat split; assumption.
Qed.

Theorem func_lim_subset : ∀ (A B : U → Prop)
    (f : set_type A → V) (g : set_type B → V) c l (H : A ⊆ B),
    (∀ x, f x = g [[x|] | H [x|] [|x]]) →
    func_lim_base g c l → func_lim_base f c l.
Proof.
    intros A B f g c l sub eq g_lim T T_neigh.
    specialize (g_lim T T_neigh) as [S [Sc S_sub]].
    exists S.
    split; [>exact Sc|].
    intros y [[x Ax] [[Sx c_neq] y_eq]]; cbn in *.
    apply S_sub.
    exists [x|sub x Ax]; cbn.
    repeat split.
    -   exact Sx.
    -   exact c_neq.
    -   rewrite eq in y_eq.
        exact y_eq.
Qed.

Theorem func_lim_forget : ∀ (A : U → Prop) (f : set_type A → V) c l,
    func_lim_base (λ x : set_type (λ x, A x ∧ ∀ H, f [x|H] ≠ l),
        f [[x|]|land [|x]]) c l →
    func_lim_base f c l.
Proof.
    intros A f c l lim T T_neigh.
    specialize (lim T T_neigh) as [S [Sc S_sub]].
    exists S.
    split; [>exact Sc|].
    intros y [[x Ax] [[Sx c_neq] y_eq]]; cbn in *.
    classic_case (y = l) as [eq|neq].
    {
        subst l.
        apply T_neigh.
    }
    apply S_sub.
    unfold image_under.
    assert (A x ∧ (∀ H, f [x|H] ≠ l)) as x_in.
    {
        split; [>exact Ax|].
        intros H1.
        rewrite (proof_irrelevance _ Ax).
        rewrite <- y_eq.
        exact neq.
    }
    exists [x|x_in]; cbn.
    repeat split.
    -   exact Sx.
    -   exact c_neq.
    -   rewrite (proof_irrelevance _ Ax).
        exact y_eq.
Qed.
(* begin hide *)
End TopologyFunction.

Section FunctionCompose.

Context {U V W} `{Topology U, Topology V, Topology W}.

Existing Instance subspace_topology.
(* end hide *)

Theorem func_lim_compose : ∀ (A : U → Prop)
    (f : V → W) (g : set_type A → V) c d,
    func_lim_base g c d → continuous_at f d →
    func_lim_base (λ x, f (g x)) c (f d).
Proof.
    intros A f g c d A_lim f_cont.
    intros T Te.
    specialize (f_cont T Te) as [S [Sd S_sub]].
    specialize (A_lim S Sd) as [R [Rc R_sub]].
    exists R.
    split; [>exact Rc|].
    intros z [[x Ax] [[Rx x_neq] z_eq]]; cbn in *.
    apply S_sub.
    exists (g [x|Ax]).
    split.
    -   apply R_sub.
        exists [x|Ax]; cbn.
        repeat split.
        +   exact Rx.
        +   exact x_neq.
    -   exact z_eq.
Qed.

Theorem func_lim_compose2 : ∀ (A : U → Prop) (B : V → Prop)
    (f : set_type B → W) (g : set_type A → set_type B) c d e,
    (∀ x, d ≠ g x) →
    func_lim_base g c d → func_lim_base f [d|] e →
    func_lim_base (λ x, f (g x)) c e.
Proof.
    intros A B f g c d e neq A_lim B_lim.
    intros T Te.
    specialize (B_lim T Te) as [S [Sd S_sub]].
    pose (S' := to_set_type B S).
    assert (neighborhood d S') as S'd.
    {
        split; [>|apply Sd].
        exists S.
        split; [>apply Sd|reflexivity].
    }
    specialize (A_lim S' S'd) as [R [Rc R_sub]].
    exists R.
    split; [>exact Rc|].
    intros z [[x Ax] [[Rx c_neq] z_eq]]; cbn in *.
    apply S_sub.
    exists (g [x|Ax]).
    repeat split.
    -   apply R_sub.
        exists [x|Ax]; cbn.
        repeat split.
        +   exact Rx.
        +   exact c_neq.
    -   intros contr.
        apply set_type_eq in contr.
        apply neq in contr.
        exact contr.
    -   exact z_eq.
Qed.

(* begin hide *)
End FunctionCompose.

Section BasisFunction.

Context {U V} `{TopologyBasis U, TopologyBasis V}.

(* end hide *)
Theorem basis_func_lim : ∀ (A : U → Prop) (f : set_type A → V) c l,
    func_lim_base f c l ↔
    (∀ T, top_basis T → T l → ∃ S, top_basis S ∧ S c ∧
        image_under f (λ x, S [x|] ∧ c ≠ [x|]) ⊆ T).
Proof.
    intros A f c l.
    split.
    -   intros f_lim T T_basis Tx.
        apply basis_open in T_basis.
        specialize (f_lim T (make_and T_basis Tx)) as [S [[S_open Sc] S_sub]].
        specialize (S_open c Sc) as [B [B_basis [Bc B_sub]]].
        exists B.
        repeat split; [>exact B_basis|exact Bc|].
        intros y [[x Ax] [[Bx c_neq] y_eq]]; cbn in *.
        apply S_sub.
        exists [x|Ax]; cbn.
        repeat split.
        +   apply B_sub.
            exact Bx.
        +   exact c_neq.
        +   exact y_eq.
    -   intros all_T.
        intros T [T_open Tl].
        specialize (T_open l Tl) as [B [B_basis [Bl B_sub]]].
        specialize (all_T B B_basis Bl) as [S [S_basis [Sc S_sub]]].
        exists S.
        split.
        +   split; [>|exact Sc].
            apply basis_open.
            exact S_basis.
        +   apply (trans S_sub).
            exact B_sub.
Qed.
(* begin hide *)
End BasisFunction.
(* end hide *)
