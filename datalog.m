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

:- import_module term.
:- import_module list.
:- import_module string.

:- type datalog(T). % Type paratemerized to conform to term(T).
:- type datalog == datalog(generic). 



:- func init = datalog(T).

:- pred init(datalog(T)).
:- mode init(out) is det.

:- pred empty_datalog(datalog(T)::in) is semidet.

% Type for the string functors of atoms
% When constructing symbols, the string values are interned
:- type symbol.

:- pred symbol(string, symbol).
:- mode symbol(in, out) is det.
:- mode symbol(out,  in) is det.

:- func symbol(string) = symbol.
:- mode symbol(in) = out is det.
:- mode symbol(out) = in is det.

:- type relation ---> symbol/int.

:- pred relation(string, int, relation).
:- mode relation(in, in, out) is det.
:- mode relation(out, out, in) is det.

:- func relation(string, int) = relation.
:- mode relation(in, in) = out is det.
:- mode relation(out, out) = in is det.

% Succeeds if the database has no circular dependencies.
:- pred stratified(datalog(T)::in) is semidet.


:- type stratification --->
	relation >= relation ;
	relation > relation ;
	base(relation).
	
% Nondeterministically returns all of the stratification constraints on
% relations in a Datalog database
% RelationA >= RelationB if RelationA can call RelationB in a positive context
% RelationA >  RelationB if RelationA can call RelationB in a negative context
% base(Relation) if Relation has no dependencies that require it to be
% stratified at a level greater than 0 (in essence not Relation > _)
% Fails on an empty database

:- pred stratification(datalog(T)::in, stratification::out) is nondet.


% An atom is a combination of a function symbol and a list of terms.
% In implementation, the string symbol will be interned
:- type atom(T) == { symbol, list(term(T)) }.
:- type atom == atom(generic).

:- pred atom(string, list(term(T)), atom(T)).
:- mode atom(in, in, out) is det.
:- mode atom(out,out, in) is det.

:- func atom(string, list(term(T))) = atom(T).
:- mode atom(in, in) = out is det.
:- mode atom(out, out) = in is det.

:- pred unify_atoms(atom(T)::in, atom(T)::in, substitution(T)::in, 
	substitution(T)::out) is semidet.
	
% True if there are no variables in atom
:- pred ground_atom(atom(T)::in) is semidet.
:- pred ground_atom_in_bindings(atom(T)::in, substitution(T)::in) is semidet.

:- pred apply_substitution_in_atom(substitution(T)::in, atom(T)::in, 
	atom(T)::out) is det.

:- pred atom_vars(atom(T)::in, list(var(T))::out) is det.
:- func atom_vars(atom(T)) = list(var(T)).

:- func relation(atom(T)) = relation.
:- func name(atom(T)) = string.
:- func arity(atom(T)) = int.
:- func terms(atom(T)) = list(term(T)).
	
% A literal is an atom or it's negation.
:- type literal(T) ---> +atom(T) ; -atom(T).
:- type literal == literal(generic).

% Syntactic constructor for positive literals. Fails if literal is negated.
% To construct a negative literal use not literal(X, Y) or negation/2
:- pred literal(string, list(term(T)), literal(T)).
:- mode literal(in, in, out) is det.
:- mode literal(out, out, in) is semidet. 

:- func literal(string, list(term(T))) = literal(T).
:- mode literal(in, in) = out is det.
:- mode literal(out, out) = in is semidet.

% negation(X, Y) :- X = not Y.
:- pred negation(literal(T), literal(T)).
:- mode negation(in, out) is det.
:- mode negation(out, in) is det.

:- func (not literal(T)) = literal(T).
:- mode (not in) = out is det.
:- mode (not out) = in is det.

:- pred negated(literal(T)::in) is semidet.
:- pred not_negated(literal(T)::in) is semidet.



:- type clause(T) ---> clause( head :: atom(T), body :: list(literal(T))).
:- type clause == clause(generic).

:- func (atom(T) <= list(literal(T))) = clause(T).
:- mode (in <= in) = out is det.
:- mode (out <= out) = in is det.

% Fails if the resulting program cannot be stratified
:- pred rule(clause(T)::in, datalog(T)::in, datalog(T)::out) is semidet. 

% Throws an error if the resulting program cannot be stratified
:- pred det_rule(clause(T)::in, datalog(T)::in, datalog(T)::out) is det.

% Adds a rule even if it causes circular dependencies
% Behavior may be undefined
%
% Note that if a rule is added that renders a datalog database unstratifiable
% any subsequent use of rule/3 will fail and det_rule/3 will throw an error.
:- pred force_rule(clause(T)::in, datalog(T)::in, datalog(T)::out) is det.

% Add a rule that calls a mercury goal for it's unifications
% for semidet success that does not bind variables, return empty substitution
% Don't pass new variables back in result, either bind variables to
% ground terms or to other variables in the atom.
:- pred primitive_rule(relation, 
	pred(atom(T), substitution(T), substitution(T)), 
	datalog(T), datalog(T)).
	
:- mode primitive_rule(in, pred(in, in, out) is nondet, in, out) is det.
	
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

:- import_module map.
:- import_module multi_map.
:- import_module require.
:- import_module maybe.
:- import_module solutions.
:- import_module set.

:- type rule(T) --->
	rule(
		head :: atom(T),
		positive_body :: list(atom(T)),
		negative_body :: list(atom(T))
	) 
;
	primitive(
		pred(atom(T)::in, substitution(T)::in, substitution(T)::out) is nondet
	).

	
:- type rules(T) == multi_map(relation, rule(T)).

% considered using varset ... but I don't need the added functionality or
% complexity in the internal implementation as the internal vars are supposed
% to be completely opaque to everything but primitves, and even they aren't
% supposed to do anything but bind vars to ground terms or other vars from
% the same set.  I might change my mind if I need to implement stricter rules
% on what a primitive can and cannot do with the input atom.
:- type datalog(T) ---> 
	datalog(rules :: rules(T), var_supply :: var_supply(T)).

init(datalog(map.init,init_var_supply)).
init = Datalog :- init(Datalog).

empty_datalog(datalog(Rules, Supply)) :-
	multi_map.is_empty(Rules), Supply = init_var_supply.

% The symbol type is used to intern string names for relations and atoms
% I want symbol lookup to be by refrence instead of by value
:- type symbol == { string }.


% table the creation of symbols so that the same string always returns a
% refrence to the same symbol object, instead of constructing a new one
:- pragma memo(symbol(in, out)).

symbol(String, { String }).


:- pragma memo(symbol(in) = out).

symbol(String) = Symbol :- symbol(String, Symbol).

relation(String, Arity, symbol(String)/Arity).

relation(String, Arity) = symbol(String)/Arity.


atom(String, Terms, {symbol(String), Terms}).
atom(String, Terms) = {symbol(String), Terms}.

unify_atoms({Symbol, ListA}, {Symbol, ListB}, !Substitution) :-
	unify_term_list(ListA, ListB, !Substitution).
	
:- pred term_list_is_ground(list(term(T))::in) is semidet.

term_list_is_ground([]).
term_list_is_ground([ X | XS ]) :- is_ground(X), term_list_is_ground(XS).

ground_atom({_, List}) :- term_list_is_ground(List).

:- pred list_ground_in_bindings(list(term(T))::in, substitution(T)::in)
	is semidet.

list_ground_in_bindings([], _).
list_ground_in_bindings([ X | XS ], Sub) :-	is_ground_in_bindings(X, Sub), 
	list_ground_in_bindings(XS, Sub).
	
ground_atom_in_bindings({_, List}, Sub) :- list_ground_in_bindings(List, Sub).

apply_substitution_in_atom(Sub, { Symbol, !.Terms }, { Symbol, !:Terms }) :-
	apply_rec_substitution_in_terms(Sub, !Terms).

atom_vars({_ , Terms}, vars_list(Terms)).
atom_vars({_ , Terms}) = vars_list(Terms).

relation({Symbol, List}) = Symbol/length(List).
name({ symbol(Name), _ }) = Name.
arity({_, List}) = length(List).
terms({_, List}) = List.

literal(Name, List, +{symbol(Name), List}).
literal(Name, List) = +{symbol(Name), List}.

negation(+Atom,-Atom).
negation(-Atom,+Atom).

(not A) = B :- negation(A,B).

negated(-_).
not_negated(+_).

% More syntax friendly constructor for clause
(Head <= Body) = clause(Head, Body).

% Variable renaming for rule insertion into datalog database

:- pred rename_var(var(T)::in, var(T)::out,
	renaming(T)::in, renaming(T)::out,
	var_supply(T)::in, var_supply(T)::out) is det.
	
rename_var(!Var, !Map, !Supply) :-
	create_var(NewVar, !.Supply, NewSupply),
	search_insert(!.Var, NewVar, FoundVar, !Map),
	(
		if FoundVar = yes(!:Var) 
		then !:Supply = !.Supply
		else !:Var = NewVar, !:Supply = NewSupply
	).
	
:- pred rename_vars(list(var(T))::in, list(var(T))::out,
	renaming(T)::in, renaming(T)::out,
	var_supply(T)::in, var_supply(T)::out) is det.
	
rename_vars([], [], !Map, !Supply).

rename_vars([ !.Var | !.List ], [!:Var | !:List ], !Map, !Supply) :-
	rename_var(!Var, !Map, !Supply),
	rename_vars(!List, !Map, !Supply).
	
:- func rename_var(var(T), renaming(T), renaming(T), 
	var_supply(T), var_supply(T)) = var(T).
:- mode rename_var(in, in, out, in, out) = out is det.
	
rename_var(Old, !Map, !Supply) = New :- rename_var(Old, New, !Map, !Supply).

:- pred rename_atom( atom(T)::in, atom(T)::out, 
	renaming(T)::in, renaming(T)::out,
	var_supply(T)::in, var_supply(T)::out) is det.
	
rename_atom( { Symbol, !.Terms }, { Symbol, !:Terms }, !Map, !Supply) :-
	Vars = vars_list(!.Terms),
	rename_vars(Vars, _, !Map, !Supply),
	apply_renaming_in_terms(!.Map, !Terms).
	
:- pred rename_atoms( list(atom(T))::in, list(atom(T))::out,
	renaming(T)::in, renaming(T)::out,
	var_supply(T)::in, var_supply(T)::out) is det.
	
rename_atoms([], [], !Map, !Supply).

rename_atoms([ !.Atom | !.List ], [ !:Atom | !:List ], !Map, !Supply) :-
	rename_atom(!Atom, !Map, !Supply),
	rename_atoms(!List, !Map, !Supply).


% Stratification
% oh lawd this is an intimidating one, moreso than query eval
% I cranked these out in a fuge, don't know if they're valid or work as
% intended, but I'm proud that I came up with it all.
% Going through Tarjan's Algorithms in a purely declarative functional manner
% would have been tourtured, this seems more elegant, will need to test for 
% correctness

% These calls must be tabled, due to the heavily recursive nature of the dfs
% I'm sure there's a more 'efficient' implementation, goal floundering is
% almost garunteed
 

	
:- pred stratify(rules(T)::in, stratification::out) is nondet.
:- pragma minimal_model(stratify/2).

stratify(Rules, Stratification) :- 
	multi_map.member(Rules, Relation, _), 
	stratify(Rules, Relation, Stratification).
	
:- pred stratify(rules(T)::in, relation::in, stratification::out) is nondet.
:- pragma minimal_model(stratify/3).


stratify(Rules, Relation, Strat) :-
	nondet_search(Rules, Relation, Rule), 
	(	% A >= B if A calls B in it's body in a positive context
		list.member(Atom, positive_body(Rule)),
		BodyRelation = relation(Atom),
		Strat = (Relation >= BodyRelation)
	;	% A > B if A calls B in a negative context
		list.member(Atom, negative_body(Rule)),
		BodyRelation = relation(Atom),
		Strat = (Relation > BodyRelation)
	;	% A >= C :- A >= B, B >= C.
		multi_map.member(Rules, RelationA, _),
		stratify(Rules, Relation, Relation >= RelationA),
		multi_map.member(Rules, RelationB, _),
		stratify(Rules, RelationA, RelationA >= RelationB),
		Strat = (Relation >= RelationB)
	;	% A > C :- A > B, ( B > C ; B >= C ).
		multi_map.member(Rules, RelationA, _),
		stratify(Rules, Relation, Relation > RelationA),
		multi_map.member(Rules, RelationB, _),
		(
			stratify(Rules, RelationA, RelationA > RelationB)
		;
			stratify(Rules, RelationA, RelationA >= RelationB)
		),
		Strat = (Relation > RelationB)
	/*;	% base(A) :- not A > _, not ( A >= B, not base(B) ).
		Strat = base(Relation),	 
		not stratify(Rules, Relation, Relation > _),
		multi_map.member(Rules, OtherRelation, _), 
		not (
			stratify(Rules, Relation >= OtherRelation), 
			OtherStratify = (pred(OtherStrat::out) is nondet :-
				stratify(Rules, OtherRelation, OtherStrat) ),
			StratSet = solutions_set(OtherStratify),
			not set.member(base(OtherRelation), StratSet)
		) */
	).
	
:- pred stratified_rules(rules(T)::in) is semidet.

stratified_rules(Rules) :- not (
	multi_map.member(Rules, RelationA, _),
	multi_map.member(Rules, RelationB, _),
	(
		stratify(Rules, RelationA, RelationA > RelationB),
		(
			stratify(Rules, RelationB, RelationB > RelationA)
		;
			stratify(Rules, RelationB, RelationB >= RelationA)
		)
	;
		stratify(Rules, RelationA, RelationA >= RelationB),
		stratify(Rules, RelationB, RelationB > RelationA)	
	)
).

stratified(datalog(Rules, _)) :- stratified_rules(Rules).

stratification(datalog(Rules, _), Stratification) :- 
	stratify(Rules, Stratification).
	
% Rules, I put this part after stratification due to the stratification 
% checking inherent in rule/3 and det_rule/3

force_rule(clause(Head, Body), datalog(!.Rules, !.Supply), 
	datalog(!:Rules, !:Supply)) :-
	sort_body(Body, Positive, Negative),
	rename_atom(Head, RenHead, init, Ren, !Supply),
	rename_atoms(Positive, RenamedPos, Ren, RenNext, !Supply),
	rename_atoms(Negative, RenamedNeg, RenNext, _, !Supply),
	add(relation(RenHead), rule(RenHead, RenamedPos, RenamedNeg), !Rules).
	
% sort_body(Literals, Positive, Negative)
:- pred sort_body(list(literal(T))::in, 
	list(atom(T))::out, list(atom(T))::out) is det.
	
sort_body([], [], []).

sort_body([+Atom | Literals ], [ Atom | Positive ], Negative) :- 
	sort_body(Literals, Positive, Negative).
	
sort_body([-Atom | Literals ], Positive, [ Atom | Negative ]) :- 
	sort_body(Literals, Positive, Negative).
	
rule(Clause, !Datalog) :- force_rule(Clause, !Datalog), stratified(!.Datalog).

det_rule(Clause, Datalog0, Datalog) :- 
	force_rule(Clause, Datalog0, Datalog1), (
		if stratified(Datalog1) then Datalog1 = Datalog
		else unexpected($module, $pred, 
			"Added rule renders datalog unstratisfiable.")
	).
	
primitive_rule(Relation, Primitive, 
	datalog(!.Rules, Supply), datalog(!:Rules, Supply)) :-
	add(Relation, primitive(Primitive), !Rules).

% Asserted facts in a datalog database will have no impact on the 
% stratifiability of said database because they have no body, rendering
% stratification checking unneccecary.
fact(Atom, !Datalog) :- force_rule(clause(Atom, []), !Datalog).


% Queries 

query(datalog(Rules, VarSupply), Query, Result) :-
	rename_atom(Query, Goal, init, _, VarSupply,_), %Rename variables in query
	subgoal(Rules, [ +Goal ], init, Substitution), % Run query
	ground_atom_in_bindings(Goal, Substitution), %Succeed if results are ground
	apply_substitution_in_atom(Substitution, Goal, Result). %apply substitution

% SLDNF Resolution
:- pred subgoal(rules(T)::in, list(literal(T))::in, substitution(T)::in, 
	substitution(T)::out) is nondet.
	
subgoal(_, [], !Substitution).

subgoal(Rules, [ +Goal | Subgoals ], !Substitution) :-
	nondet_search(Rules, relation(Goal), Rule), (
		Rule = rule(Head, Positive, Negative),
		unify_atoms(Goal, Head, !Substitution),
		append(to_positive(Positive),to_negative(Negative), Body),
		append( Subgoals, Body, NewGoals),
		subgoal(Rules, NewGoals, !Substitution)
	;
		Rule = primitive(P),
		P(Goal, !Substitution),
		subgoal(Rules, Subgoals, !Substitution)
	).
	
subgoal(Rules, [ -Goal | Subgoals ], !Substitution) :-
	not subgoal(Rules, [ +Goal | Subgoals ], !.Substitution, _),
	subgoal(Rules, Subgoals, !Substitution).

% That was a lot simpler than I expected it to be.
	
	
	
:- func to_positive(list(atom(T))) = list(literal(T)).

to_positive([]) = [].
to_positive([ X | XS ]) = [ +X | to_positive(XS) ].

:- func to_negative(list(atom(T))) = list(literal(T)).

to_negative([]) = [].
to_negative([ X | XS ]) = [ -X | to_positive(XS) ].
	



	