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

:- type binding(T) == map(var(T), T).

:- typeclass datalog_term(T) where [

	% return a list of variables in a term
	% return empty list with no vars if term is ground
	pred vars_of(T::in, list(var(T))::out) is det,
	
	% if root term is a var, return it
	pred to_var(T::in, var(T)::out) is semidet, 
	
	% convert a var into a term
	pred to_term(var(T)::in, T::out) is det,
	
	% find variable bindings that unify terms and add them to the accumulator
	pred unify(T::in, T::in, binding(T)::in, binding(T)::out) is det,
	
	% Replace var V with term Replacement in term T
	% replace(V, Replacement, !T)
	pred replace(var(T)::in, T::in, T::in, T::out) is det
].

:- instance datalog_term(term(T)).

:- func vars_of(T) = list(var(T)) <= datalog_term(T).
:- func to_var(T) = var(T) is semidet <= datalog_term(T).
:- func to_term(var(T)) = T <= datalog_term(T).
:- func unify(T, T, binding(T)) = binding(T) <= datalog_term(T).
:- func replace(var(T), T, T) = T <= datalog_term(T).

% is_ground(Term) :- vars_of(Term, []).
:- pred is_ground(T::in) is semidet <= datalog_term(T).

% get the variables in a list of terms and merge them
:- pred vars_of_list(list(T)::in, list(var(T))::out) is det <= datalog_term(T).
:- func vars_of_list(list(T)) = list(var(T))  <= datalog_term(T).

% Unify lists sequentially, fail if the lists are not equal length
:- pred unify_list(list(T)::in, list(T)::in, binding(T)::in, binding(T)::out)
	is semidet <= datalog_term(T).

% Apply a renaming map to a term
:- pred rename(renaming(T)::in, T::in, T::out) is det <= datalog_term(T).

% Recursively replace variables with terms from a binding substitution
:- pred bind(binding(T)::in, T::in, T::out) is det <= datalog_term(T).

:- pred bind_list(binding(T)::in, list(T)::in, T::out) is det 
	<= datalog_term(T).


:- implementation.

vars_of(T) = List :- vars_of(T, List).
to_var(T) = Var :- to_var(T, Var).
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


	
	
