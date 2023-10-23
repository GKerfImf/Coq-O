Require Import Program.Basics.
Require Import Coq.Init.Nat.

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

    Context {X : Type}.

    Lemma comp_incl_refl:
      forall (F : ParamCompl X),
        F ⊑ F.
    Proof.
      now intros.
    Qed.

  End Lemmas.

End Main.
