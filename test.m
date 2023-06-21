:- module test.
:- interface.
:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module datalog.
:- import_module list.
:- import_module string.
:- import_module term_conversion.

main(!IO) :-
    % Write your test code or program entry point logic here
    io.write_string("Hello, world!\n", !IO),
	NewDatalog = datalog.init,
	fact(atom("foo", []), NewDatalog, Datalog0),
	fact(atom("bar", [ type_to_term(6) ]), Datalog0, Datalog),  
	io.write_string(string(Datalog), !IO).