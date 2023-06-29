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


:- type er_term(T)	--->
	entity(uint) ;
	variable(var(T)) ;
	symbol(symbol) ;
	name(string) ;
	color(string) ;
	stat(int) ;
	scalar(float) ;
	assertion(symbol, entity_term, object_term) ;
	bool_assertion(symbol, entity_term) ;
	not(assertion_term) ;
	and(list(assertion_term)) ;
	or(list(assertion_term)).
	
:- type object_term(T) =< er_term(T) --->
	entity(uint) ;
	variable(var(T)) ;
	name(string) ;
	color(string) ;
	stat(int) ;
	scalar(float).
	
:- type entity_term(T) =< object_term(T) --->
	entity(uint) ;
	variable(var(T)).
	
:- type assertion_term(T) =< er_term	--->
	variable(var(T)) ;
	assertion(symbol, entity_term, object_term) ;
	bool_assertion(symbol, entity_term) ;
	not(assertion_term) ;
	and(list(assertion_term)) ;
	or(list(assertion_term)).
	
:- type positive_assertion_term(T) =< assertion_term	--->
	variable(var(T)) ;
	assertion(symbol, entity_term, object_term) ;
	bool_assertion(symbol, entity_term) ;
	and(list(positive_assertion_term)) ;
	or(list(positive_assertion_term)).

:- type negated_assertion_term(T) =< assertion_term --->
	not(assertion_term).
	

	
	
	
	
