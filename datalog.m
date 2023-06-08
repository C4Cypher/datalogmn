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

:- type datalog. 

/*

% todo: figure out what to do with term(T) typing. 
% Preferably in a dynamic and elegant manner.
% Type warnings and errors are a pain in the ass at compile time if unnececary.
% I should use this aspect of the term library as intended, to ensure type safety.
% Will probably make the term(T) opaque in implementation, converting back 
% to whatever parametric type was fed to it.

 Gonna handle all of this shit internally.
:- type datalog_term == term(datalog).
:- type dlterm == datalog_term.

:- type datalog_variable = var(datalog).
:- type dlvar == datalog_variable.

:- type datalog_substitution == substitution(datalog).
:- type dlsubstitution == datalog_substitution.

:- type datalog_renaming == renaming(datalog).
:- type dlrenaming == datalog_renaming.

*/

:- func init = datalog.

:- pred init(datalog).
:- mode empty_datalog(out) is det.

% relation(name, arity) == name/arity.
:- type relation --->
	relation( name :: string, arity :: uint ).

% We do not care what T is, as datalog will convert the type to it's internal representation 
:- type literal_or_negation ---> 
	some [T] literal(symbol::string, terms::list(term(T))) ;
	not literal.
	
	
:- type literal =< literal_or_negation ---> some [T] literal(symbol::string, terms::list(term(T))).
:- type negation =< literal_or_negation ---> not literal.

:- type head == literal.

:- type body == list(literal_or_negation).

:- pred some [T] literal_vars(literal_or_negation:in, list(var(T)):out) is det.

:- pred some [T] unify_literals(literal:in, literal:in, substitution(T):in, substitution(T):out) is semidet.

:- type clause ---> head :- body. %Do I need this at all? Syntactic sugar?

:- pred negation(literal_or_negation, literal_or_negation).
:- mode negation(in, out) is det.
:- mode negation(out, in) is det.

% negated(X) :- X = functor(atom('not'), [ _ | [] ],_).
:- pred negated(literal_or_negation:in) is semidet.

:- pred stratified(datalog:in) is semidet.

:- type primitive == some [T] pred(list(term(T)):in, list(term(T)):out) is nondet.

% If the primitive succeeds, return the input.
:- func semidet_to_nondet(some [T] pred(list(term(T)):in is semidet)) = primitive.

% Fail if a the rules have no single stable minimal model
:- pred stratify(datalog:in, datalog:out) is semidet.

:- implementation.

: type datalog.