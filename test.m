:- module test.
:- interface.
:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module datalog.
:- import_module list.
:- import_module string.
:- import_module term.
:- import_module term_conversion.
:- import_module solutions.

main(!IO) :-
    % Write your test code or program entry point logic here
    io.write_string("Hello, world!\n", !IO),
	D0 = datalog.init,
	fact(atom("foo", []), D0, D1),
	fact(atom("bar", [ type_to_term(6) ]), D1, D2),
	fact(atom("bar", [ type_to_term(3) ]), D2, D3),
	S = init_var_supply,
	create_var(V, S, _),
	Query = atom("bar", [ variable(V, context_init) ]),
	solutions(query(D3, Query), Answer),
	io.write_string(string(Answer), !IO).