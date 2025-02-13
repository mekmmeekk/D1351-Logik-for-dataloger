%Helper functions
select(X,[X|T],T).
select(X,[Y|T],[Y|R]) :-
    select(X,T,R).

member(X,L) :- select(X,L,_).

%Get the last line of the proof
lastLine([H|[]], H). %base case with one line
lastLine([_|T], LastLine) :-
    lastLine(T, LastLine).
%End of helper functions


%Reading the proof
verify(InputFileName) :-
    see(InputFileName),
    read(Prems), read(Goal), read(Proof),
    seen,
    validate_proof(Prems, Goal, Proof).


%Is the proof valid?
%if yes:
validate_proof(Prems, Goal, Proof) :- 
    proofCorrect(Prems, Proof, []),
    goalMet(Goal, Proof),
    write("Yes"), !.
%if no:
validate_proof(Prems, _, Proof) :- 
    \+ proofCorrect(Prems, Proof, []),
    write("No"),
    fail, !.
validate_proof(_, Goal, Proof) :- 
    \+ goalMet(Goal, Proof),
    write("No"), 
    fail, !.


%Is the proof (not accounting for the goal) correct?
proofCorrect(_, [], _). %base case - end of proof
proofCorrect(Prems, [H|T], PreviousLines) :- 
    rowCorrect(Prems, H, PreviousLines),  %is the current line valid based on the given premises and the checked lines?
    proofCorrect(Prems, T, [H|PreviousLines]).


% Box Detection
% box always starts with an assumption
rowCorrect(Prems, [[Nr, X, assumption]|T], PreviousLinesCopy) :- 
    % check if rest of the box is correct
    % [Nr, boxStart] is added to mark on which line the box starts.
    proofCorrect(Prems, [[Nr, X, assumption]|T], [[Nr, boxStart]|PreviousLinesCopy]). 
    % when the whole box is checked the temporary list is removed and 
    % the whole box is added as one element in the original PreviousLines list.


%premise
% The predicate checks if X is a member of the given list of premises (Prems).
rowCorrect(Prems, [_, X, premise], _) :-
    member(X, Prems).

%assumption
%checking after the [Nr, boxstart] ensures that a box i open,
%correct Nr shows that it is the first assumption
rowCorrect(_, [Nr, _, assumption], PreviousLines) :-
    member([Nr, boxStart], PreviousLines).

%copy
%The copy rule allows a formula from a previous line in the proof
%to be repeated "copied" on a new line.
rowCorrect(_, [_, X, copy(Nr)], PreviousLines) :-
    member([Nr, X, _], PreviousLines).

%andint
% X , Y ––––––  X ∧ Y
rowCorrect(_, [_, and(X,Y), andint(Nr1, Nr2)], PreviousLines) :-
    member([Nr1, X, _], PreviousLines),
    member([Nr2, Y, _], PreviousLines).

%andel1
% X ∧ Y ––––––  X 
rowCorrect(_, [_, X, andel1(Nr)], PreviousLines) :-
    member([Nr, and(X, _), _], PreviousLines).

%andel2
% Y ∧ X ––––––  X
rowCorrect(_, [_, X, andel2(Nr)], PreviousLines) :-
    member([Nr, and(_, X), _], PreviousLines).

%orint1
% X ––––––  X ∨ Y
rowCorrect(_, [_, or(X, _), orint1(Nr)], PreviousLines) :-
    member([Nr, X, _], PreviousLines).

%orint2
% X ––––––  Y ∨ X
rowCorrect(_, [_, or(_, X), orint2(Nr)], PreviousLines) :-
    member([Nr, X, _], PreviousLines).
                 
%orel
% X ∨ Y , [X ... Z],[Y ... Z] –––––– Z
rowCorrect(_, [_, Z, orel(Nr1, Nr2, Nr3, Nr4, Nr5)], PreviousLines) :-
    member([Nr1, or(X, Y), _], PreviousLines),
    member([[Nr2, X, _]|TX], PreviousLines),
    lastLine([[Nr2, X, _]|TX], LastLineX),
    [Nr3, Z, _] = LastLineX,
    member([[Nr4, Y, _]|TY], PreviousLines),
    lastLine([[Nr4, Y, _]|TY], LastLineY),
    [Nr5, Z, _] = LastLineY.

%impint      
% [X ... Y] –––––– X ––> Y
rowCorrect(_, [_, imp(X, Y), impint(Nr1, Nr2)], PreviousLines) :-
    member([[Nr1, X, _]|T], PreviousLines),
    lastLine([[Nr1, X, _]|T], LastLine),
    [Nr2, Y, _] = LastLine.
      
%impel
% X, X ––> Y –––––– Y
rowCorrect(_, [_, Y, impel(Nr1, Nr2)], PreviousLines) :-
    member([Nr1, X, _], PreviousLines),
    member([Nr2, imp(X, Y), _], PreviousLines).

%negint
% [X ... ⊥ ] –––––– ¬ X
rowCorrect(_, [_, neg(X), negint(Nr1, Nr2)], PreviousLines) :-
    member([[Nr1, X, _]|T], PreviousLines),
    lastLine([[Nr1, X, _]|T], LastLine),
    [Nr2, cont, _] = LastLine.            

%negel
% X, ¬ X ––––––  ⊥
rowCorrect(_, [_, cont, negel(Nr1, Nr2)], PreviousLines) :-
    member([Nr1, X, _], PreviousLines),
    member([Nr2, neg(X), _], PreviousLines).

%contel
% ⊥ –––––– X
rowCorrect(_, [_, _, contel(Nr)], PreviousLines) :-
    member([Nr, cont, _], PreviousLines).
                    
%negnegint
% X –––––– ¬¬ X
rowCorrect(_, [_, neg(neg(X)), negnegint(Nr)], PreviousLines) :-
    member([Nr, X, _], PreviousLines).

%negnegel 
% ¬¬ X –––––– X
rowCorrect(_, [_, X, negnegel(Nr)], PreviousLines) :-
    member([Nr, neg(neg(X)), _], PreviousLines).

%mt
% X ––> Y, ¬ Y –––––– ¬ X 
rowCorrect(_, [_, neg(X), mt(Nr1, Nr2)], PreviousLines) :-
    member([Nr1, imp(X, Y), _], PreviousLines),
    member([Nr2, neg(Y), _], PreviousLines).
                    
%pbc
% [¬ X ... ⊥ ] –––––– X
rowCorrect(_, [_, X, pbc(Nr1, Nr2)], PreviousLines) :-
    member([[Nr1, neg(X), _]|T], PreviousLines),
    lastLine([[Nr1, neg(X), _]|T], LastLine),
    [Nr2, cont, _] = LastLine.
         
%lem
%  ––––––  X ∨ ¬ X  
rowCorrect(_, [_, or(X, neg(X)), lem], _).


%Is the last line of the proof matches the goal?
goalMet(Goal, Proof) :-
    lastLine(Proof, LastLine),
    [_, Goal, _] = LastLine.