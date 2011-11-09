Require Import String.

Definition identifier : Set := string.

Record type_operator : Set := mk_type_operator {
  op_name  : identifier;
  op_arity : nat
}.

Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | nil  : ilist 0
  | cons : forall n, A -> ilist n -> ilist (S n).
End ilist.

Implicit Arguments cons [n A].
Implicit Arguments nil [A].

Inductive type : Set :=
| TyVar : identifier -> type
| TyApp (op : type_operator) : ilist type (op_arity op) -> type.

Local Open Scope string_scope.

Definition fun_tyop := mk_type_operator "->" 2.

Definition fun_type x y := TyApp fun_tyop (cons x (cons y nil)).

Record constant : Set := mk_constant {
  const_name : identifier;
  const_type : type
}.

Inductive term : type -> Set :=
| Var (_ : identifier) (ty : type) : term ty
| Const (c : constant) : term (const_type c)
| App : forall x y, term (fun_type x y) -> term x -> term y
| Abs' (_ : identifier) (x : type) : forall y, term y -> term (fun_type x y).

Definition is_var ty (t : term ty) :=
match t with Var _ _ => True | _ => False end.

Definition dest_var ty t : is_var ty t -> identifier * type.
refine (
match t with
| Var n ty => fun _ => (n,ty)
| _ => fun _ => False_rec _ _ end
); auto. Defined.

Definition Abs x (v : term x) : is_var x v -> forall y, term y -> term (fun_type x y) :=
fun p => match dest_var x v p with (n,_) => Abs' n x end.

Definition type_of ty (t : term ty) :=
match t with
| Var _ ty => ty
| Const c  => const_type c
| App x y _ _ => y
| Abs' _ x y _ => fun_type x y end.

Lemma type_of_is_useless : forall ty t, type_of ty t = ty.
induction t; auto. Qed.

Definition bool_tyop := mk_type_operator "bool" 0.

Definition bool_type := TyApp bool_tyop nil.

Definition is_formula ty t := type_of ty t = bool_type.

(* How do I use, say, MSets for the hypothesis set? *)

Require Import Coq.Lists.ListSet.

Check set_add.

Definition singleton (x : term bool_type) : set (term bool_type).
refine (set_add _ x (empty_set _)).

Inductive thm (c : term bool_type) (h : set term bool_type) : Set :=
| Assume t : thm t 

(*
Inductive preterm : Set :=
| Var   : identifier -> type -> preterm
| Const : constant -> preterm
| App   : preterm -> preterm -> preterm
| Abs   : preterm -> preterm -> preterm.

Require Import Coq.Bool.Bool.
Require Import Coq.Program.Program.

I know I probably need to ensure type_operator and type have decidable equality, before the following will work.
But how do I do that?

Program Fixpoint type_of (tm : preterm) : option type :=
match tm with
  | (Var _ ty)  => Some ty
  | (Const c)   => Some (const_type c)
  | (App t1 t2) => match (type_of t1, type_of t2) with
                     | (Some (TyApp op (cons 1 x (cons 0 y nil))), Some x') => 
                         if (op = fun_tyop) && (x = x') then Some y else None
                     | _ => None
                   end
  | (Abs ((Var _ ty) as x) b) => match type_of b with
                                   | Some tb => Some (fun_type ty tb)
                                   | None => None
                                 end
  | (Abs _ _)   => None
end.

Definition term : Set := {tm : preterm | exists ty, type_of tm = Some ty}

(* Can I define terms at once without preterms?

Inductive term : Set :=
| Var   : identifier -> type -> term
| Const : constant -> term
| App   : forall x y, {t1 : term | has_type t1 (fun_type x y) } -> {t2 : term | has_type t2 x} -> term
| Abs   : identifier -> type -> term -> term
with has_type : term -> type -> Prop :=
| Var_has_type   : has_type (Var _ ty) ty
| Const_has_type : has_type (Const c) (const_type c)
| App_has_type   : forall x y, has_type t1 (fun_type x y) -> has_type t2 x -> has_type (App t1 t2) y.
*)

(* What about defining terms and type_of at once, without has_type? *)