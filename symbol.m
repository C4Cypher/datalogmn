%-----------------------------------------------------------------------------%
% vim: ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2014 Charlie H. McGee IV.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%-----------------------------------------------------------------------------%
% 
% File: symbol.m
% Main author: C4Cypher.
% Stability: low.

:- module symbol.

:- interface.

% String values are interned
:- type symbol.

:- pred symbol(string, symbol).
:- mode symbol(in, out) is det.
:- mode symbol(out,  in) is det.

:- func symbol(string) = symbol.
:- mode symbol(in) = out is det.
:- mode symbol(out) = in is det.

:- implementation.

% The symbol type is used to intern string names for relations and atoms
% I want symbol lookup to be by refrence instead of by value
:- type symbol == { string }.


% table the creation of symbols so that the same string always returns a
% refrence to the same symbol object, instead of constructing a new one
:- pragma memo(symbol(in, out)).

symbol(String, { String }).

:- pragma memo(symbol(in) = out).

% The symbol type is used to intern string names for relations and atoms
% I want symbol lookup to be by refrence instead of by value
:- type symbol == { string }.


% table the creation of symbols so that the same string always returns a
% refrence to the same symbol object, instead of constructing a new one
:- pragma memo(symbol(in, out)).

symbol(String, { String }).


:- pragma memo(symbol(in) = out).

symbol(String) = Symbol :- symbol(String, Symbol).