%-----------------------------------------------------------------------------%
% vim: ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2014 Charlie H. McGee IV.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%-----------------------------------------------------------------------------%
% 
% File: datalog_term.m
% Main author: C4Cypher.
% Stability: low.

:- module datalog_term.

:- interface.

:- import_module term.
:- import_module list.
:- import_module map.
:- import_module set.

:- type binding(T, V) == map(V, T).
:- type rename_map(V) == map(V, V).

:- typeclass datalog_term(T, V, S) where [

	% create a new set of variables
	pred new_var_set(S::uo) is det.

	% create a new, unique variable
	pred new_var(V::out, S::in, S::out) is det.

	% return a list of variables in a term
	% return empty list with no vars if term is ground
	pred vars_of(T::in, list(V)::out) is det,
	
	% if root term is a var, return it
	pred to_var(T::in, V::out) is semidet, 
	
	% convert a var into a term
	pred to_term(V::in, T::out) is det,
	
	% find variable bindings that unify terms and add them to the accumulator
	pred unify(T::in, T::in, binding(T, V)::in, binding(T, V)::out) is det,
	
	% Replace var V with term Replacement in term T
	% replace(V, Replacement, !T)
	pred replace(V::in, T::in, T::in, T::out) is det
].

:- instance datalog_term(term(T), var(T), var_supply(T)).

:- func new_var_set = S::uo is det <= datalog_term(T, V, S).
:- func new_var(S::in, S::out) = V::out is det <= datalog_term(T, V, S).
:- func vars_of(T) = list(V) <= datalog_term(T, V, S).
:- func to_var(T) = V is semidet <= datalog_term(T, V, S).
:- func to_term(V) = T <= datalog_term(T, V, S).
:- func unify(T, T, binding(T, V)) = binding(T, V) <= datalog_term(T, V, S).
:- func replace(V, T, T) = T <= datalog_term(T, V, S).

% is_ground(Term) :- vars_of(Term, []).
:- pred is_ground(T::in) is semidet <= datalog_term(T, V, S).

% get the variables in a list of terms and merge them
:- pred vars_of_list(list(T)::in, list(V)::out) is det <= datalog_term(T, V, S).
:- func vars_of_list(list(T)) = list(V)  <= datalog_term(T, V, S).

% Unify lists sequentially, fail if the lists are not equal length
:- pred unify_list(list(T)::in, list(T)::in, binding(T, V)::in, binding(T, V)::out)
	is semidet <= datalog_term(T, V, S).

% Apply a renaming map to a term
:- pred rename(rename_map(V)::in, T::in, T::out) is det <= datalog_term(T, V, S).

% Recursively replace variables with terms from a binding substitution
:- pred bind(binding(T, V)::in, T::in, T::out) is det <= datalog_term(T, V, S).

:- pred bind_list(binding(T, V)::in, list(T)::in, T::out) is det 
	<= datalog_term(T, V, S).


:- implementation.

vars_of(T) = List :- vars_of(T, List).
to_var = Var :- to_var(T, Var).
to_term(Var) = Term :- to_term(Var, Term).
unify(A, B, !.Binding) = !:Binding :- unify(A, B, !Binding).
replace(Var, Replacement, !.Term) = !:Term :- replace(Var, Replacement, !Term).

is_ground(Term) :- vars_of(Term, []).

:- pred insert_merge(list(T)::in, list(T)::in, list(T)::out) is det.

insert_merge([], List, List).

insert_merge([X|Xs], !List) :- 
	if member(X, !.List) 
	then insert_merge(Xs, !List)
	else insert_merge(Xs, [ X | !.List ], !:List).
	
vars_of_list([], []).

vars_of_list([Term | Terms], AllVars) :- 
	vars_of_list(Terms, Vars),
	insert_merge(vars_of(Term), Vars, AllVars).

unify_list([], [], !Binding).

unify_list([X | Xs], [Y | Ys], !Binding) :- 
		unify(X, Y, !Binding),
		unify_list(Xs, Ys, !Binding).

:- pred rename_term_vars(rename_map(V)::in, list(V)::in, T::in, T::out) 
	is det. 
	
rename_term_vars(_, [], !T).

rename_term_vars(Map, [ Var | Vars ], !T) :-
	if contains(Map, Var) 
	then (
		replace(Var, to_term(lookup(Map, Var)), !T),
		rename_term_vars(Map, Vars, !T) 
	) else rename_term_vars(Map, Vars, !T).
	

rename(Map, !Term) :- 
	vars_of(!.Term, Vars),
	rename_term_vars(Map, Vars, !Term).

:- pred bind_vars(binding(T, V)::in, list(V)::in,  

bind(Binding, !Term) :-
	




	
	
