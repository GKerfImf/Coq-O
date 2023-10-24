Require Import Program.Basics.
Require Import Coq.Init.Nat.
Require Import Lia.

Section Util.

  Definition monotonic (f : nat -> nat) : Prop :=
    forall x x', x <= x' -> f x <= f x'.

End Util.

Section Main.

  Notation "f ∘ g" := (compose f g).

  Inductive ParamCompl (X : Type) : Type :=
  | id__pc (f : X -> nat) : ParamCompl X
  | o__pc : ParamCompl X -> ParamCompl X
  | O__pc : ParamCompl X -> ParamCompl X
  | add__pc : ParamCompl X -> ParamCompl X -> ParamCompl X
  | mul__pc : ParamCompl X -> ParamCompl X -> ParamCompl X
  | exp__pc : ParamCompl X -> ParamCompl X -> ParamCompl X
  | Any__pc : ParamCompl X -> ParamCompl X.

  Notation "⟦ f ⟧" := (@id__pc _ f) (at level 30).
  Notation " 'o' ( f )" := (@o__pc _ f) (at level 50).
  Notation " 'O' ( f )" := (@O__pc _ f) (at level 50).
  Notation " f1 ⊕ f2 " := (@add__pc _ f1 f2) (at level 50).
  Notation " f1 ⊗ f2 " := (@mul__pc _ f1 f2) (at level 50).
  Notation " f1 ↑ f2 " := (@exp__pc _ f1 f2) (at level 50). (* Knuth's up-arrow notation *)
  Notation " 'Any' ( f )" := (@Any__pc _ f) (at level 50).

  Reserved Notation "f ∈p F" (at level 65).
  Fixpoint InParamCompl {X : Type} (f : X -> nat) (F : ParamCompl X) : Prop :=
    match F with
    | ⟦F⟧ => forall x, f x <= F x
    | O(F) => exists g, g ∈p F /\ exists a b,      forall x, f x <= a * g x + b
    | o(F) => exists g, g ∈p F /\ forall a b, exists δ, forall x, a * f x + b <= g x + δ
    | F1⊕F2 => exists g1 g2, g1 ∈p F1 /\ g2 ∈p F2 /\ forall x, f x <= g1 x + g2 x
    | F1⊗F2 => exists g1 g2, g1 ∈p F1 /\ g2 ∈p F2 /\ forall x, f x <= g1 x * g2 x
    | F1↑F2 => exists g1 g2, (forall x, 0 < g1 x) /\ g1 ∈p F1 /\ g2 ∈p F2 /\ forall x, f x <= g1 x ^ g2 x
    | Any(F) => exists G, monotonic G /\ exists g, g ∈p F /\ forall x, f x <= G (g x)
    end
  where "f ∈p F" := (InParamCompl f F).
  Notation "f ∉p F" := (~ InParamCompl f F) (at level 65).

  Definition compl_incl {X : Type} (F G : ParamCompl X) :=
    forall (f : X -> nat), f ∈p F -> f ∈p G.
  Notation "F ⊑ G" := (compl_incl F G) (at level 60).

  Section Lemmas.

    Section BasicInclusion.

      Context {X : Type}.

      Lemma comp_incl_refl:
        forall (F : ParamCompl X),
          F ⊑ F.
      Proof.
        now intros.
      Qed.

      Lemma comp_incl_trans:
        forall (F G H : ParamCompl X),
          F ⊑ G -> G ⊑ H -> F ⊑ H.
      Proof.
        now intros * IN1 IN2; firstorder.
      Qed.

      Lemma comp_incl_f_Of:
        forall (F : ParamCompl X),
          F ⊑ O(F).
      Proof.
        intros ? ? IN.
        exists f; split; auto.
        now exists 1, 0; intros ?; lia.
      Qed.

      Lemma comp_incl_base_ge:
        forall (f g : X -> nat),
          (forall x, f x = g x) ->
          ⟦f⟧ ⊑ ⟦g⟧.
      Proof.
        now intros * LE f IN x; rewrite <-LE.
      Qed.

      Lemma comp_incl_O:
        forall (F G : ParamCompl X),
          F ⊑ G -> O(F) ⊑ O(G).
      Proof.
        intros * SUB f IN.
        destruct IN as (fo & IN & a & b &LE).
        exists fo; split.
        + now apply SUB in IN.
        + now exists a, b.
      Qed.

    End BasicInclusion.

    Section Arithmetic.

      Context {X : Type}.

      (* ------------------------------- Plus ------------------------------- *)

      Lemma comp_incl_plus_compat:
        forall (F1 F2 G1 G2 : ParamCompl X),
          F1 ⊑ F2 -> G1 ⊑ G2 -> F1 ⊕ G1 ⊑ F2 ⊕ G2.
      Proof.
        intros * IN1 IN2 f IN.
        inversion_clear IN as [g1 [g2 [IN3 [IN4 LE]]]].
        now exists g1, g2; eauto.
      Qed.

      Lemma comp_incl_plus_compat_l:
        forall (F G1 G2 : ParamCompl X),
          G1 ⊑ G2 -> F ⊕ G1 ⊑ F ⊕ G2.
      Proof. now intros * IN; apply comp_incl_plus_compat. Qed.

      Lemma comp_incl_plus_compat_r:
        forall (F1 F2 G : ParamCompl X),
          F1 ⊑ F2 -> F1 ⊕ G ⊑ F2 ⊕ G.
      Proof. now intros * IN; apply comp_incl_plus_compat. Qed.

      (* ------------------------------- Mult ------------------------------- *)

      Lemma comp_incl_mult_compat:
        forall (F1 F2 G1 G2 : ParamCompl X),
          F1 ⊑ G1 -> F2 ⊑ G2 -> F1 ⊗ F2 ⊑ G1 ⊗ G2.
      Proof.
        intros * IN1 IN2 f IN.
        inversion_clear IN as [g1 [g2 [IN3 [IN4 LE]]]].
        now exists g1, g2; eauto.
      Qed.

      Lemma comp_incl_mult_compat_l:
        forall (F G1 G2 : ParamCompl X),
          G1 ⊑ G2 -> F ⊗ G1 ⊑ F ⊗ G2.
      Proof. now intros * IN; apply comp_incl_mult_compat. Qed.

      Lemma comp_incl_mult_compat_r:
        forall (F1 F2 G : ParamCompl X),
          F1 ⊑ F2 -> F1 ⊗ G ⊑ F2 ⊗ G.
      Proof. now intros * IN; apply comp_incl_mult_compat. Qed.

    End Arithmetic.

  End Lemmas.

End Main.
