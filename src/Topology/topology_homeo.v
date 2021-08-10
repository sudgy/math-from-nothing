Require Import init.

Require Export topology_base.
Require Import topology_continuous.

Definition homeomorphism {U V} `{Topology U, Topology V} (f : U → V) :=
    continuous f ∧ ∃ H : bijective f, continuous (bij_inv f H).

(* begin hide *)
Section Homeomorphism.

Context {U V} `{Topology U, Topology V}.
Variable f : U → V.
(* end hide *)

Theorem homeomorphism_open :
       homeomorphism f ↔ (bijective f ∧ (∀ A, open A ↔ open (image_under f A))).
    split.
    -   intros [cont [bij inv_cont]].
        split; try exact bij.
        rewrite continuous_open in cont.
        rewrite continuous_open in inv_cont.
        intros A.
        split.
        +   intros A_open.
            specialize (inv_cont A A_open).
            rewrite inverse_image_bij_inv in inv_cont.
            exact inv_cont.
        +   intros A_open.
            specialize (cont _ A_open).
            rewrite inverse_image_bij in cont by apply bij.
            exact cont.
    -   intros [bij opens].
        split.
        +   intros x B B_neigh.
            exists (inverse_image f B).
            repeat split.
            *   apply opens.
                rewrite bij_inverse_image by exact bij.
                apply B_neigh.
            *   apply B_neigh.
            *   intros y' [a [Bfa eq]]; subst.
                exact Bfa.
        +   exists bij.
            rewrite continuous_open.
            intros A A_open.
            rewrite inverse_image_bij_inv.
            apply opens.
            exact A_open.
Qed.

(* begin hide *)
End Homeomorphism.
(* end hide *)
