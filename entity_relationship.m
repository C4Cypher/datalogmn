%-----------------------------------------------------------------------------%
% vim: ft=mercury
%-----------------------------------------------------------------------------%
% Copyright (C) 2014 Charlie H. McGee IV.
% This file may only be copied under the terms of the GNU Library General
% Public License - see the file COPYING.LIB in the Mercury distribution.
%-----------------------------------------------------------------------------%
% 
% File: entity_relationship.m
% Main author: C4Cypher.
% Stability: low.

:- interface.

:- import_module datalog_term.
:- import_module uint.
:- import_module term.


:- type er_term	--->
	entity(uint) ;
	variable(var(er_term)) ;
	symbol(symbol) ;
	name(string) ;
	stat(int) ;
	scalar(float) ;
	rel
