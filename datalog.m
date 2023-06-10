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
:- mode init(out) is det.

:- pred empty_datalog(datalog(T)::in) is semidet.

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
	substitution(T)::out) is semidet.
	
% True if there are no variables in atom
:- pred ground_atom(atom(T)::in) is semidet.
:- pred ground_atom_in_bindings(atom(T)::in, substitution(T)::in) is semidet.

:- pred atom_vars(atom(T)::in, list(var(T))::out) is det.
:- func atom_vars(atom(T)) = list(var(T)).

:- func relation(atom(T)) = relation.
:- func name(atom(T)) = string.
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

:- type primitive == pred(atom(T), substution(T)).
:- inst primitive == (pred(in, out) is nondet).
:- mode primitive_in == in(primitive).
:- mode pi == primitive_in.
:- mode primitive_out == out(primitive).
:- mode po == primitive_out.

% Add a rule that calls a mercury goal for it's unifications
% for semidet success that does not bind variables, return empty substitution
% Don't pass new variables back in result, either bind variables to
% ground terms or to other variables in the atom.
:- pred primitive_rule(relation::in, primitive::pi, datalog(T)::in, 
	datalog(T)::out) is det.
	
% Equivalent to rule(Atom :- [], !Datalog). Using variables instead of ground
% terms in the Atom is not reccomended unless you're binding the same term in
% multiple fields of the atom. 
%
% Not reccomended: foo(X,Y).  
%
% Acceptable: bar(X, X).  
:- pred fact(atom(T)::in, datalog(T)::in, datalog(T)::out) is det.

% ask the database a query
% Any variables in the input atom will be replaced with gound terms in the
% output atom, if any. 
:- pred query(datalog(T)::in, atom(T)::in, atom(T)::out) is nondet.

% Bottom up output of all facts in a bottom up manner
% Not sure if I want to implement this
% :- pred facts(datalog(T)::in, atom(T)::out) is nondet.

:- implementation.

:- import module map.

:- type rule -->
	rule(
		head :: atom(T),
		positive_body :: list(atom(T)),
		negative_body :: list(atom(T))
	) 
;
	primitive(primitive).

:- inst rule --->
	rule(ground, ground, ground);
	primitive(primitive).

:- mode rule_in == in(rule).
:- mode ri == rule_in.

:- mode rule_out == out(rule).
:- mode ro == rule_out.
	
:- type rules == map(relation, rule).

% considered using varset ... but I don't need the added functionality or
% complexity in the internal implementation as the internal vars are supposed
% to be completely opaque to everything but primitves, and even they aren't
% supposed to do anything but bind vars to ground terms or other vars from
% the same set.  I might change my mind if I need to implement stricter rules
% on what a primitive can and cannot do with the input atom.
:- type datalog(T) ----> datalog(rules :: rules, var_supply :: var_supply(T)),

:- init(datalog(map.init,init_var_supply)).
:- init = Datalog :- init(Datalog).

:- empty_datalog(datalog(Rules, Supply)) :-
	is_empty(Rules), Supply = init_var_supply.

% The symbol type is used to intern string names for relations and atoms
% I want symbol lookup to be by refrence instead of by value
:- type symbol ---> symbol_string(string).

:- func symbol(string) = symbol.
:- mode symbol(in) = out is det.
:- mode symbol(out) = in is det.

% table the creation of symbols so that the same string always returns a
% refrence to the same symbol object, instead of constructing a new one
:- pragma memo(symbol(in) = out).

symbol(String) = symbol_string(String).

:- type relation == { symbol, uint }

:- relation(String, Arity, {symbol(String), Arity}).

:- relation(Symbol, Arity) = {symbol(String), Arity}.

:- type atom(T) == {symbol, list(term(T)}.


atom(String, Terms, {symbol(string), Terms}).
atom(String, Terms) = {symbol(string), Terms}.

unify_atoms({Symbol, ListA}, {Symbol, ListB}, !Substitution) :-
	unify_term_list(ListA, ListB, !Substitution).
	
:- pred term_list_is_ground(list(term(T))::in) is semidet.

term_list_is_ground([]).
term_list_is_ground([ X | XS ]) :- is_ground(X), term_list_is_ground(XS).

ground_atom({_, List}) :- term_list_is_ground(List).

:- pred list_ground_in_bindings(list(term(T)::in, substitution(T)::in)
	is semidet.

list_ground_in_bindings([]).
list_ground_in_bindings([ X | XS ], Sub) :-	is_ground_in_bindings(X, Sub), 
	list_ground_in_bindings(XS, Sub).
	
ground_atom_in_bindings({_, List}, Sub) :- list_ground_in_bindings(List, Sub).

atom_vars({_ , Terms}, vars_list(Terms)).
atom_vars({_ , Terms}) = vars_list(Terms).

relation({Symbol, List}) = {Symbol, length(List)}.
name({ symbol_string(Name), _ }) = Name.
arity({_, List}) = length(List).
terms({_, List}) = List.

literal(Name, List, positive({symbol(Name), List})).
literal(Name, List) = positive({symbol(Name), List}).

negation(positive(Atom),negative(Atom)).
negation(negative(Atom),positive(Atom)).

not positive(Atom) = negative(Atom).
not negative(Atom) = positive(Atom).

negated(negative(_)).
not_negated(positive(_)).



