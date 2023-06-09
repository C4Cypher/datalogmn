%-----------------------------------------------------------------------------%
% vim: ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2014 Charlie H. McGee IV.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%-----------------------------------------------------------------------------%
% 
% File: datalog.m
% Main author: C4Cypher.
% Stability: low.

:- module datalog.

:- interface.

:- import module term.
:- import module list.
:- import module string.
:- import module int.

:- type datalog(T). % Type paratemerized to conform to term(T).
:- type datalog == datalog(generic). 

% Succeeds if the database has no circular dependencies.
:- pred stratified(datalog(T):in) is semidet.

:- func init = datalog(T).

:- pred init(datalog(T)).
:- mode empty_datalog(out) is det.

% relation(name, arity) == name/arity.
% The definitions for relation and atom are abstracted so as to ensure
% memoization of the string values.
:- type relation.

:- pred relation(string, uint, relation).
:- mode relation(in, in, out) is det.
:- mode relation(out, out, in) is det.

:- func relation(string, uint) = relation.
:- mode relation(in, in) = out is det.
:- mode relation(out, out) = in is det.
	
:- pred relation(atom(T)::in, relation::out) is det.
:- func relation(atom(T)) = relation.

% An atom is a combination of a function symbol and a list of terms.
% In implementation, the string symbol will be interned
:- type atom(T). 
:- type atom == atom(generic).

:- pred atom(string, list(term(T)), atom(T)).
:- mode atom(in, in, out) is det.
:- mode atom(out,out, in) is det.

:- func atom(string, list(term(T))) = atom(T).
:- mode atom(in, in) = out is det.
:- mode atom(out, out) = in is det.

:- pred unify_atoms(atom(T)::in, atom(T)in, substitution(T)::in, 
	substitution(T)::out) is det.
	
% True if there are no variables in atom
:- pred ground_atom(atom(T)::in) is semidet.

:- pred atom_vars(atom(T)::in, list(var(T))::out) is det.
:- func atom_vars(atom(T)) = list(var(T)).

:- func relation(atom(T)) = relation.
:- func name(atom(T)) = strong.
:- func arity(atom(T)) = uint.
:- func terms(atom(T)) = list(term(T)).
	
% A literal is an atom or it's negation.
:- type literal(T) ---> positive(atom(T)) ; negative(atom(T)).
:- type literal == literal(generic).

% Syntactic constructor for positive literals. Fails if literal is negated.
% To construct a negative literal use not literal(X, Y) or negation/2
:- pred literal(string, list(term(T)), literal(T)).
:- mode literal(in, in, out) is det.
:- mode literal(out, out, in) is semidet. 

:- func literal(string, list(term(T)) = literal(T).
:- mode literal(in, in) = out is det.
:- mode literal(out, out) = in is semidet.

% negation(X, Y) :- X = not Y.
:- pred negation(literal(T), literal(T)).
:- mode negation(in, out) is det.
:- mode negation(out, in) is det.

:- func not literal(T) = literal(T).
:- mode not in = out is det.
:- mode not out = in is det.

:- pred negated(literal(T)::in) is semidet.
:- pred not_negated(literal(T)::in) is semidet.



:- type clause(T) ---> atom(T) :- list(literal(T)).
:- type clause == clause(generic).

% Fails if the resulting program cannot be stratified
:- pred rule(clause(T)::in, datalog(T)::in, datalog(T)::out) is semidet. 

% Throws an error if the resulting program cannot be stratified
:- pred det_rule(clause(T)::in, datalog(T)::in, datalog(T)::out) is det.

% Adds a rule even if it causes circular dependencies
% Behavior may be undefined
:- pred force_rule(clause(T)::in, datalog(T)::in, datalog(T)::out) is det.

% Add a rule that calls a mercury goal for it's unifications
% for semidet success that does not bind variables, return empty substitution
% Don't pass new variables back in result, either bind variables to
% ground terms or to other variables in the atom.
:- pred primitive_rule( 
	(pred(atom(T)::in, substitution(T)::out is nondet))::in,
	datalog(T)::in,
	datalog(T)::out
) is det.



:- implementation.

