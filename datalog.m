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

:- func init = datalog.

:- pred init(datalog).
:- mode empty_datalog(out) is det.

% relation(name, arity) == name/arity.
:- type relation --->
	relation( name :: string, arity :: uint ).



:- pred stratified(datalog:in) is semidet.

:- type primitive == some [T] pred(list(term(T)):in, list(term(T)):out) is nondet.

% If the primitive succeeds, return the input.
:- func semidet_to_nondet(some [T] pred(list(term(T)):in is semidet)) = primitive.

% Fail if a the rules have no single stable minimal model
:- pred stratify(datalog:in, datalog:out) is semidet.

:- implementation.

: type datalog.