include "inverse.mzn";
include "alldifferent_except_0.mzn";
include "global_cardinality_low_up_closed.mzn";
include "global_cardinality_closed.mzn";

int: n; % number of court members
set of int: COURT = 1..n;
set of int: COURT_D = 0..n;
int: emperor = 1;
array[COURT] of int: rank;
array[COURT] of int: ability;

int: m; % number of horses
set of int: HORSE = 1..m;
set of int: HORSE_D = 0..m;
 
array[HORSE] of int: beauty;
array[HORSE] of int: speed;

array[COURT,HORSE] of int: enjoy;


array[COURT] of var HORSE_D: horse;
array[HORSE] of var COURT_D: member;
% array[HORSE] of var 0..1: penalty;


          %wiecej czlonkow niz koni, kazdy kon uzyty
constraint (n > m -> 
              % bedzie dokladnie n-m zer, a reszta ma sie pojawic dokladnie raz
            global_cardinality_closed(horse, [h | h in HORSE_D], 
                [n-m] ++ [1 | h in HORSE]))                 
            /\ %wiecej koni, wszyscy jezdza
           (n <= m -> 
             global_cardinality_closed(member, [c | c in COURT_D], [m-n] ++ [1 | c in COURT])); 
             
% channeling, jako ze COURT, HORSE nie maja takiego samego rozmiaru - to tutaj sie robi "inverse" dla niezerowych elementow
constraint forall(c in COURT, h in HORSE)
(
  horse[c] = h <-> member[h] = c
);


% emperor enjoys the most
constraint forall(c in COURT where horse[c] != 0 /\ c != emperor)
(
  enjoy[c, horse[c]] < enjoy[emperor, horse[emperor]]
);

% rank wyzszy to:
constraint forall(c,d in COURT where c != d)
(
  (rank[c] > rank[d]) -> 
    (
      % brudas nie jedzie, lub
      horse[d] = 0
      % nikt nie jedzie, lub
      \/ (horse[c] = 0 /\ horse[d] = 0)
      % piekno konika przynajmniej takie, jak brudasa
      \/ beauty[horse[c]] >= beauty[horse[d]]
    )
);

% speed wyzszy to:
constraint forall(h,i in HORSE where h != i)
(
  (speed[h] > speed[i]) -> 
    (
      % skill jezdzcy konika przynajmniej takie, lub
      ability[member[h]] >= ability[member[i]]
      % szybszy konik nie ma jezdzcy, lub
      \/ member[h] = 0
      % nikt nie jedzie, lub
      \/ (member[h] = 0 /\ member[i] = 0)
%       % omijamy ograniczenie, dodajac kare
%        \/ penalty[i] = 1
      \/ true
    )
);

%If an entry in the array is negative, then the horse cannot be assigned to the court member.
constraint forall(c in COURT where horse[c] != 0)
(
  enjoy[c, horse[c]] > 0
);


var int: penalty;

constraint  penalty = sum(h, i in HORSE where h < i /\ speed[h] > speed[i] /\ ability[member[h]] < ability[member[i]])(100);

var int: obj;
constraint obj = sum(c in COURT where horse[c] != 0)(enjoy[c, horse[c]]) - penalty;
solve maximize obj;


output["horse = \(horse);\n"];
output["obj = \(obj);\n"];