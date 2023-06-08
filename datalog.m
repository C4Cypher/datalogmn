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

:- func init = datalog(T).

:- pred init(datalog(T)).
:- mode empty_datalog(out) is det.

% relation(name, arity) == name/arity.
:- type relation --->
	relation( name :: string, arity :: uint ).
	
:- pred relation(atom(T):in, relation:out) is det.
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

:- pred unify_atoms(atom(T):in, atom(T)in, substitution(T):in, 
	substitution(T):out) is det.
	
% A literal is an atom or it's negation.
:- type literal(T) ---> positive(atom(T)) ; negative(atom(T)).

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

% True if there are no variables in atom
:- pred is_ground(atom(T):in) is semidet.

:- pred vars(atom(T):in, list(var(T)):out) is det.
:- func vars(atom(T)) = list(var(T)).

:- type rule(T)


% pred types that can be passed as primitive rules
:- type primitive == pred(list(term(T)):in, list(term(T)):out) is nondet.

% If the primitive succeeds, return the input.
:- func semidet_to_nondet(pred(list(term(T)):in is semidet)) = primitive.


:- implementation.

