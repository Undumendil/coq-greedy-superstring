Require Import ZArith.
Require Import FreeGroups.
Import ListNotations.

Section String.

Definition to_free_group_alphabet(a : Z) : alphabet Z := intro_gen Z a.
Coercion to_free_group_alphabet: Z >-> alphabet.

Definition String := list Z.
Fixpoint to_free_group(s: String) : group_str Z :=
	match s with
	| [] => []
	| a :: w => (a: alphabet Z) :: to_free_group(w)
	end.
Coercion to_free_group: String >-> group_str.

Fixpoint pref(s: String) : String :=
	match s with
	| [] => []
	| [ a ] => []
	| a :: w => a :: pref(w)
	end.

Definition suff(s: String) : String :=
	match s with
	| [] => []
	| a :: w => w
	end.

Definition ladd(s: String) (a: Z) : String := a :: s.
Fixpoint radd(s: String) (a: Z) : String := s ++ [ a ].
(*	match s with
	| [] => [ a ]
	| a :: w => a :: (radd w a)
	end.*)

Fixpoint Str_eq_dec (x y : String) : bool :=
	match x, y with
	| [], [] => true
	| a::A, [] => false
	| [], b::B => false
	| a::A, b::B => (Z.eqb a b) && Str_eq_dec A B
	end.

Theorem str_len_inc : forall (z : Z) (S : String), (length (z :: S)) = 1 + (length S).
Proof.
	intros.
	auto.
Qed.

Theorem str_len_inv : forall (A B : list Z), A = B -> (length A) = (length B).
Proof.
	intros. subst. auto.
Qed.

Theorem str_diff_constr : forall (z : Z) (A : String), [] <> (z :: A).
Proof.
	intros.
	pose proof str_len_inv as Inv.
	specialize Inv with (A := []) (B := (z :: A)).
	intuition.
	pose proof str_len_inc as Inc.
	specialize Inc with (z := z) (S0 := A).
	rewrite Inc in H0.
	discriminate H0.
Qed.

(* TODO: finish the proof *)
Axiom str_eq_dec : forall (x y : String), { x = y } + { x <> y }.
(*Definition str_eq_dec : forall (x y : String),  { x = y } + { x <> y }.
Proof.
	intros.
	induction x as [| x IHX]. 
	destruct y. left. reflexivity.
	right. 
	pose proof str_diff_constr as Con.
	specialize Con with (z := z) (A := y).
	exact Con.
	destruct IHIHX as [P1 | P2].
	right. rewrite P1.
	intuition.
	pose proof str_len_inv as Inv.
	specialize Inv with (A := x :: y) (B := y).
	apply Inv in H.
	pose proof str_len_inc as Inc.
	specialize Inc with (z := x) (S0 := y).
	rewrite H in Inc.
	revert Inc.
	intuition.
	induction y as [| t Y].
	right.
	pose proof str_diff_constr as Con.
	specialize Con with (z := x) (A := IHX).
	revert Con. intuition.

Defined.*)

Fixpoint IsPrefix (x y : String) : bool :=
	match x with
	| [] => true
	| a :: X =>
		match y with
		| [] => false
		| b :: Y =>
			if Z.eq_dec a b then
				IsPrefix X Y
			else
				false
		end
	end.

Fixpoint Overlaps (x y : String) (n : nat) {struct n} : bool :=
	match n with
	| 0 => IsPrefix x y
	| S k => 
		match x with
		| [] => false
		| a :: X => Overlaps X y k
		end
	end.

Fixpoint Superstring' (x y : String) (n : nat) {struct n} : String :=
	match n with
	| 0 => x ++ y
	| S k =>
		match x with
		| [] => y
		| a :: X => 
			if IsPrefix x y then
				match y with
				| [] => [] (* impossible since x is non-empty prefix of y *)
				| b :: Y =>
					a :: Superstring' X Y k (* IsPrefix X Y = true *)
				end
			else
				Superstring' X y k
		end
	end.

Definition Superstring (x y : String) : String :=
	Superstring' x y ((length x) + (length y)).

Fixpoint ListSuperstring' (v : String) (L : list String) : String :=
	match L with
	| [] => v
	| u :: R =>
		(ListSuperstring' (Superstring v u) R)
	end.

Definition ListSuperstring (L : list String) : String :=
	ListSuperstring' [] L.

Fixpoint str_le (x y : String) : bool :=
	match x with
	| [] => true
	| a :: X =>
		match y with
		| [] => false
		| b :: Y =>
			if Z.eq_dec a b then
				str_le X Y
			else
				if Z_lt_dec a b then true else false
		end
	end.

Axiom str_le_dec : forall (x y : String), { str_le x y = true } + { str_le y x = true }.

Fixpoint str_lt (x y : String) : bool :=
	match x with
	| [] => 
		if (length y) =? 0 then
			false
		else
			true
	| a :: X =>
		match y with
		| [] => false
		| b :: Y =>
			if Z.eq_dec a b then
				str_lt X Y
			else
				if Z_lt_dec a b then true else false
		end
	end.

Axiom str_lt_dec : forall (x y : String), { str_lt x y = true } + { str_lt y x = true } + { x = y }.

End String.
