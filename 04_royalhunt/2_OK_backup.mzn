%2 pierwsze przechodza



include "inverse.mzn";
include "alldifferent_except_0.mzn";
include "global_cardinality_low_up_closed.mzn";
include "global_cardinality_closed.mzn";

int: n; % number of court members
set of int: COURT = 1..n;
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
array[HORSE_D] of var COURT: member;
array[HORSE] of var 0..1: penalty;

          % wiecej czlonkow niz koni, kazdy kon uzyty
% constraint (n > m -> 
%               % bedzie dokladnie n-m zer, a reszta ma sie pojawic dokladnie raz
%               global_cardinality_closed(horse, [h | h in HORSE_D], 
%                 [n-m] ++ [1 | h in HORSE])) 
                
%            /\ %wiecej koni, wszyscy jezdza
%            (n <= m -> 
%                % beda tylko prawdziwe koniki, nie ma zerowego
%            global_cardinality_closed(horse, [h | h in HORSE_D], 
%                 [0] ++ [1 | h in HORSE])); 
        
% optymalizacja tego co wyzej
% bedzie dokladnie max(n-m, 0) zer, a reszta ma sie pojawic dokladnie raz
constraint global_cardinality_closed(horse, [h | h in HORSE_D], 
                [max(n-m, 0)] ++ [1 | h in HORSE]); 

constraint inverse(horse, member);


% emperor enjoys the most
constraint forall(m in 2..n where horse[m] != 0)
(
  enjoy[m, horse[m]] < enjoy[emperor, horse[emperor]]
);

% rank wyzszy to:
constraint forall(m,n in COURT where m != n)
(
  (rank[m] > rank[n]) -> 
    (
      % brudas nie jedzie, lub
      horse[n] = 0
      % nikt nie jedzie
      \/ (horse[m] = 0 /\ horse[n] = 0)
      % piekno konika przynajmniej takie, jak brudasa
      \/ beauty[horse[m]] >= beauty[horse[n]]
    )
);

% speed wyzszy to:
constraint forall(h,i in HORSE where h != i)
(
  (speed[h] > speed[i]) -> 
    (
      % skill jezdzcy konika przynajmniej takie, lub
      ability[member[h]] >= ability[member[i]]
      % szybszy konik nie ma jezdzcy
      \/ horse[h] = 0
      % nikt nie jedzie, lub
      \/ (horse[h] = 0 /\ horse[i] = 0)
      % omijamy ograniczenie, dodajac kare
      \/ penalty[i] = 1
    )
);

%If an entry in the array is negative, then the horse cannot be assigned to the court member.
constraint forall(m in COURT where horse[m] != 0)
(
  enjoy[m, horse[m]] > 0
);




var int: obj;
constraint obj = sum(c in COURT where horse[c] != 0)(enjoy[c, horse[c]]) - sum(h in HORSE)(penalty[h]*100);

solve maximize obj;


output["horse = \(horse);\n"];
output["obj = \(obj);\n"];