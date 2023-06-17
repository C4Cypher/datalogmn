:- module test.
:- interface.
:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

main(!IO) :-
    % Write your test code or program entry point logic here
    io.write_string("Hello, world!\n", !IO).