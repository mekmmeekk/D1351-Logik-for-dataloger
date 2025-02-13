% For SICStus, uncomment line below: (needed for member/2)
use_module(library(lists)).
% Load model, initial state and formula from file.
verify(Input) :-
see(Input), read(T), read(L), read(S), read(F), seen,
check(T, L, S, [], F), !.


%check(T, L, S, U, F).
% T - The transitions in form of adjacency lists
% L - The labeling
% S - Current state
% U - Currently recorded states
% F - CTL Formula to check.

% Should evaluate to true iff the sequent below is valid.
%
% (T,L), S |- F
% U
% To execute: consult('your_file.pl'). verify('input.txt').

% Literals
check(_, L, S, [], X) :-
    member([S, Labeling], L),
    member(X, Labeling), !.
check(_, L, S, [], neg(X)) :-
    member([S, Labeling], L),
    \+member(X, Labeling), !.

% And
check(T, L, S, [], and(X,Y)) :-
    check(T, L, S, [], X),
    check(T, L, S, [], Y), !.
    
% Or1
check(T, L, S, [], or(X,_)) :-
    check(T, L, S, [], X), !.

% Or2
check(T, L, S, [], or(_,Y)) :-
    check(T, L, S, [], Y), !.

% AX 
check(T, L, S, [], ax(X)) :-
    member([S, Transitions], T), %Tar fram lista av direkt nåbara noder
    ax(Transitions, T, L, X), !.

% EX
check(T, L, S, [], ex(X)) :-
    member([S, Transitions], T), %Tar fram lista av direkt nåbara noder
    ex(Transitions, T, L, X), !.

% AG1
check(_, _, S, U, ag(_)) :- %Om noden redan är med i listan U (om den har kontrollerats innan)
    member(S, U), !.

% AG2
check(T, L, S, U, ag(X)) :-
    \+member(S,U),
    check(T, L, S, [], X), %Om X uppfylls i startnoden
    member([S, Transitions], T), %Få fram lista över tillgängliga noder
    ag(Transitions, T, L, [S|U], X), !. %Lägg till att S har kollats o skicka vidare

% EG1
check(_, _, S, U, eg(_)) :- %Om noden redan är med i listan U (om den har kontrollerats innan)
    member(S, U), !.

% EG2
check(T, L, S, U, eg(X)) :-
    check(T, L, S, [], X), %Om X uppfylls i startnoden
    member([S, Transitions], T), %Få fram lista över tillgängliga noder
    eg(Transitions, T, L, [S|U], X), !. %Lägg till att S har kollats o skicka vidare

% EF1
check(T, L, S, U, ef(X)) :- %Om noden inte redan är med i listan U och uppfyller X.
    \+member(S, U),
    check(T, L, S, [], X), !.

% EF2
check(T, L, S, U, ef(X)) :-
    \+member(S, U),
    member([S, Transitions], T), %Få fram lista över tillgängliga noder
    ef(Transitions, T, L, [S|U], X), !. %Lägg till att S har kollats o skicka vidare

% AF1
check(T, L, S, U, af(X)) :- %Om noden inte redan är med i listan U och uppfyller X.
    \+member(S, U),
    check(T, L, S, [], X), !.

% AF2
check(T, L, S, U, af(X)) :-
    \+member(S, U),
    member([S, Transitions], T), %Få fram lista över tillgängliga noder
    af(Transitions, T, L, [S|U], X), !. %Lägg till att S har kollats o skicka vidare



%AX
ax([TransitionsHead|[]], T, L, X) :-
    check(T, L, TransitionsHead, [], X), !.  %Om sista/enda noden uppfyller X 
ax([TransitionsHead|TransitionsTail], T, L, X) :-
    check(T, L, TransitionsHead, [], X),  %Om första noden uppfyller X
    ax(TransitionsTail, T, L, X), !.  % Om de andra nåbara noderna uppfyller det

%EX
ex([], _, _, _) :- fail.  %Om vi bara har en tom lista eller om vi har stegat genom alla nåbara noder upfylls inte ex(X)  
ex([TransitionsHead|TransitionsTail], T, L, X) :-
    check(T, L, TransitionsHead, [], X);  %Om första noden uppfyller X    ELLER
    ex(TransitionsTail, T, L, X), !.  % Om de andra nåbara noderna uppfyller det

%AG2
ag([TransitionsHead|[]], T, L, U, X) :-
    check(T, L, TransitionsHead, U, ag(X)), !.  %Om sista/enda noden uppfyller ag(X) enligt AG1/AG2
ag([TransitionsHead|TransitionsTail], T, L, U, X) :-
    check(T, L, TransitionsHead, U, ag(X)),  %Om första noden uppfyller ag(X) enligt AG1/AG2
    ag(TransitionsTail, T, L, U, X), !. % Om de andra nåbara noderna uppfyller det

%EG2
eg([TransitionsHead|[]], T, L, U, X) :-
    check(T, L, TransitionsHead, U, eg(X)), !.  %Om sista/enda noden uppfyller tillståndet eg(X) enligt EG1/EG2
eg([TransitionsHead|TransitionsTail], T, L, U, X) :-
    check(T, L, TransitionsHead, U, eg(X));  %Om första noden uppfyller eg(X) enligt EG1/EG2   ELLER
    eg(TransitionsTail, T, L, U, X), !. % Om nån av de andra nåbara noderna uppfyller det

%EF2
ef([TransitionsHead|[]], T, L, U, X) :-
    check(T, L, TransitionsHead, U, ef(X)), !.  %Om sista/enda noden uppfyller tillståndet ef(X) enligt EF1/EF2
ef([TransitionsHead|TransitionsTail], T, L, U, X) :-
    check(T, L, TransitionsHead, U, ef(X));  %Om första noden uppfyller ef(X) enligt EF1/EF2   ELLER
    ef(TransitionsTail, T, L, U, X), !. % Om nån av de andra nåbara noderna uppfyller det

%AF2
af([TransitionsHead|[]], T, L, U, X) :-
    check(T, L, TransitionsHead, U, af(X)), !.  %Om sista/enda noden uppfyller tillståndet af(X) enligt AF1/AF2
af([TransitionsHead|TransitionsTail], T, L, U, X) :-
    check(T, L, TransitionsHead, U, af(X)),  %Om första noden uppfyller af(X) enligt AF1/AF2
    af(TransitionsTail, T, L, U, X), !. % Om de andra nåbara noderna uppfyller det