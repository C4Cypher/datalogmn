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
	
:- pred relation(literal(T):in, relation:out) is det.
:- func relation(literal(T)) = relation.

:- type literal(T). 
:- type literal == literal(generic).


:- pred literal(string, list(term(T)), literal(T)).
:- mode literal(in, in, out) is det.
:- mode literal(out,out, in) is det.

:- func literal(string, list(term(T))) = literal(T).
:- mode literal(in, in) = out is det.
:- mode literal(out, out) = in is det.




:- type primitive == pred(list(term(T)):in, list(term(T)):out) is nondet.

% If the primitive succeeds, return the input.
:- func semidet_to_nondet(pred(list(term(T)):in is semidet)) = primitive.


:- implementation.

