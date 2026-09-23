Require Import isla.aarch64.aarch64.

Section proof.
Context `{!islaG Σ} `{!threadG}.

Lemma test_and_sep (P Q : iProp Σ) :
  (P ∧ Q) -∗ (P ∗ Q).
Proof.
  iIntros "[HP HQ]".
Abort.

Lemma test_and_use (P Q R : iProp Σ) :
  (P ∧ Q) -∗ (P -∗ Q -∗ R) -∗ R.
Proof.
  iIntros "[HP HQ] HR". iApply "HR". iExact "HP". iExact "HQ".
Qed.

End proof.