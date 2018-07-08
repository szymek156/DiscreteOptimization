include "alldifferent.mzn";
% Beauty Trap
% Create the most magnificient feast 
enum DISH;
enum TASTE = {spicy, sour, salty, sweet, umame, bland};
enum TEMP = {hot, cold, warm};
%int: ndish;
%set of int: DISH = 1..ndish;
%set of int: TASTE = 1..6;
%int: spicy = 1; int: sour = 2; int: salty = 3; int: sweet = 4; int: umame = 5; int: bland = 6;
%set of int: TEMP = 1..3;
%int: hot = 1; int: cold = 2; int: warm = 3;


array[DISH] of TASTE: taste;
array[DISH] of TEMP: temp;
array[DISH] of bool: heavy;
array[DISH] of int: value;

int: len; % length of banquet
set of int: COURSE = 1..len;

array[COURSE] of var DISH: dish;

% kazde danie moze wystapic tylko raz
constraint alldifferent(dish);

% nie moze zaoferowac 2 dan o takim zamym smaku pod rzad:
constraint forall (c in 1..(len-1))
(
  taste[dish[c]] != taste[dish[c+1]]
);

% pierwsze ma byc salty, ostatnie sweet:
constraint taste[dish[1]] = salty /\ taste[dish[len]] = sweet;

% po spicy ma być bland or sweet
constraint forall(c in 1..(len-1) where taste[dish[c]] = spicy)
(
  taste[dish[c+1]] = bland \/ taste[dish[c+1]] = sweet
);


% po sour ma być bland or umami
constraint forall(c in 1..(len-1) where taste[dish[c]] = sour)
(
  taste[dish[c+1]] = bland \/ taste[dish[c+1]] = umame
);

% no spicy or umami po sweet
constraint forall(c in 1..(len-1) where taste[dish[c]] = sweet)
(
  taste[dish[c+1]] != spicy /\ taste[dish[c+1]] != umame
);

% nie moze byc 2 heavy pod rzad
constraint forall(c in 1..(len-2))
(
  (heavy[dish[c]] = true /\ heavy[dish[c+1]] = true) -> heavy[dish[c+2]] = false
);

% miedzy hot a cold posilkiem musi byc warm
constraint forall(c,d in 1..len where c < d /\ temp[dish[c]] = hot /\ temp[dish[d]] = cold)
(
  sum(e in (c+1)..d)
  (
    temp[dish[e]] = warm
  ) >= 1
);

var int: obj = 
  sum(i in COURSE)(value[dish[i]]) + 
%   sum(i in 1..(len-1))
%   (
%     (taste[dish[i]] != taste[dish[i+1]]) + (temp[dish[i]] != temp[dish[i+1]]) + (heavy[dish[i]] != heavy[dish[i+1]])
%   );
  sum(i in 1..(len-1))
  (
    taste[dish[i]] != taste[dish[i+1]]
  ) 
  +  
  sum(i in 1..(len-1))
  (
    temp[dish[i]] != temp[dish[i+1]]
  ) 
  +
  sum(i in 1..(len-1))
  (
    heavy[dish[i]] != heavy[dish[i+1]]
  );
  
solve maximize obj;

output["dish = \(dish);\n"];
output["dish taste: "] ++ ["\(taste[dish[i]]), " | i in COURSE] ++ ["\n"];
output["dish temp:  "] ++ ["\(temp[dish[i]]), " | i in COURSE] ++ ["\n"];
output["dish heavy: "] ++ ["\(heavy[dish[i]]), " | i in COURSE] ++ ["\n"];
output["dish value: "] ++ ["\(value[dish[i]]), " | i in COURSE] ++ ["\n"];
output["obj = \(obj);\n"];










