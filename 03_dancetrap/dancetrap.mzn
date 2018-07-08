% Beauty Trap
% Perform the most seductive dance
include "regular.mzn";
include "at_most.mzn";

enum LEGS = {spin, leap, waltz, curtsey, prep, stand};
enum ARMS = {beckon, out, up, wrapped, neutral};
enum FACE = {smile, wink, batt, think, glow, blank};

int: maxlen;
set of int: STEP = 1..maxlen;
array[LEGS] of int: maxlegs;
array[ARMS] of int: maxarms;
array[FACE] of int: maxface;
constraint assert(maxlegs[stand] >= maxlen, "maxlegs[stand] smaller than maxlen");
constraint assert(maxarms[neutral] >= maxlen, "maxarms[neutral] smaller than maxlen");
constraint assert(maxface[blank] >= maxlen, "maxface[blank] smaller than maxlen");
array[LEGS,ARMS] of int: dance_value;
array[ARMS,FACE] of int: entice_value;
constraint assert(dance_value[stand,neutral] = 0, "incorrect dance_value array");
constraint assert(entice_value[neutral,blank] = 0, "incorrect entice_value array");
int: boredom; % how bored each step make the viewer

var STEP: len;
array[STEP] of var LEGS: legs;
array[STEP] of var ARMS: arms;
array[STEP] of var FACE: face;

%%%%%% nogi %%%%%%
% % prep before any leap ??? directly?
% constraint forall(s in 1..len-1)
% (
%   legs[s + 1] = leap -> legs[s] = prep
% );

% % po spin moze tylko curtsey, prep, stand
% constraint forall(s in 1..len-1)
% (
%   legs[s] = spin -> legs[s + 1] in {curtsey, prep, stand}
% );

% % po leap moze tylko spin, waltz, stand
% constraint forall(s in 1..len-1)
% (
%   legs[s] = leap -> legs[s + 1] in {spin, waltz, stand}
% );

% % waltz max 3 razy z rzedu
% constraint forall(s in 1..len-3)
% (
%   legs[s] = waltz /\ legs[s+1] = waltz /\ legs[s+2] = waltz 
%     -> legs[s + 3] != waltz
% );

% % nie moze prep po curtsey
% constraint forall(s in 1..len-1)
% (
%   legs[s] = curtsey -> legs[s + 1] != prep
% );

% % po kazdym waltz a potem curtsey musi byc stand gdzies pomiedzy
% constraint forall(s in 1..len-1)
% (
%   (legs[s] = waltz ->
%     forall(s1 in s+1..len)
%       (legs[s1] = curtsey ->
%         exists(s2 in s+1..s1-1)(legs[s2] = stand)))
% );


% TUTAJ CHYBA LATWIEJ BYLO BY UZYC NFA
constraint regular(legs, 7, card(LEGS), l, 1, {7});
array[1..7, LEGS] of 0..7: l = 
     [| 2,0,4,5,6,7 % eps
      | 0,0,0,5,6,7 % spin
      | 2,0,4,0,0,7 % leap
      | 2,0,4,0,0,7 % waltz
      | 2,0,4,5,0,7 % curtsey
      | 2,3,4,5,6,7 % curtsey
      | 2,0,4,5,6,7 |]; % stand
      
% po kazdym waltz a potem curtsey musi byc stand gdzies pomiedzy
constraint forall(s in 1..len-1)
(
  (legs[s] = waltz ->
    forall(s1 in s+1..len)
      (legs[s1] = curtsey ->
        exists(s2 in s+1..s1-1)(legs[s2] = stand)))
);


% waltz max 3 razy z rzedu
constraint forall(s in 1..len-3)
(
  legs[s] = waltz /\ legs[s+1] = waltz /\ legs[s+2] = waltz 
    -> legs[s + 3] != waltz
);

%%%%%%%% rece %%%%%%%%
% % beckon not as first move
% constraint arms[1] != beckon;

% % beckon only after out or up
% constraint forall(s in 1..len-1)
% (
%   arms[s+1] = beckon -> (arms[s] = out \/ arms[s] = up)
% );

% % wrapped only after beckon or neutral
% constraint forall(s in 1..len-1)
% (
%   arms[s+1] = wrapped -> (arms[s] = beckon \/ arms[s] = neutral)
% );

% % nie moze zrobic 2 takich samych ruchow oprocz neutral
% constraint forall(s in 1..len-1)
% (
%   (arms[s] = neutral /\ arms[s+1] = neutral) \/ arms[s] != arms[s+1]
% );

constraint regular(arms, 6, card(ARMS), d, 1, {6});
array[1..6, ARMS] of 0..6: d = 
     [| 0,3,4,5,6 % eps
      | 0,3,4,5,6 % beckon
      | 2,0,4,0,6 % out
      | 2,3,0,0,6 % up
      | 0,3,4,0,6 % wrapped
      | 0,3,4,5,6 |]; % neutral
      
      

%%%% twarz %%%%
% % nie moze zrobic 2 takich samych gestow oprocz blank
% constraint forall(s in 1..len-1)
% (
%   (face[s] = blank /\ face[s+1] = blank) \/ face[s] != face[s+1]
% );

% % nie moze think po smile albo batt
% constraint forall(s in 1..len-1)
% (
%   face[s] = smile \/ face[s] = batt -> face[s + 1] != batt
% );

%enum FACE = {smile, wink, batt, think, glow, blank};
% minimized automata
% constraint regular(face, 5, card(FACE), f, 1, {5});
% array[1..5, FACE] of 0..5: f = 
%      [| 2,3,4,5  % eps
%       | 0,3,0,5  % smile/batt
%       | 2,0,4,5  % wink/glow
%       | 2,3,0,5  % think
%       | 2,3,4,5|]; % blank


constraint regular(face, 7, card(FACE), f, 1, {7});
array[1..7, FACE] of 0..7: f = 
     [| 2,3,4,5,6,7  % eps
      | 0,3,4,0,6,7  % smile
      | 2,0,4,5,6,7  % wink
      | 2,3,0,0,6,7  % batt
      | 2,3,4,0,6,7  % think
      | 2,3,4,5,0,7  % glow
      | 2,3,4,5,6,7|]; % blank
      

% na koniec tanca jest w pozycji neutralnej
constraint forall(s in len+1..maxlen)
(
  legs[s] = stand /\ arms[s] = neutral 
  /\ face[s] = blank
);

% wywal ruchy niedozwolone
constraint forall(s in 1..len)(dance_value[legs[s], arms[s]] >= 0);
constraint forall(s in 1..len)(entice_value[arms[s], face[s]] >= 0);


% nie moze uzyc ruchu wiecej niz:
% constraint forall(l in LEGS)
% (
%   sum(s in 1..len where legs[s] = l)(1) <= maxlegs[l]
% );

% constraint forall(a in ARMS)
% (
%   sum(s in 1..len where arms[s] = a)(1) <= maxarms[a]
% );


% constraint forall(f in FACE)
% (
%   sum(s in 1..len where face[s] = f)(1) <= maxface[f]
% );

constraint forall(l in LEGS)
(
  at_most(maxlegs[l], legs, l)
);

constraint forall(a in ARMS)
(
  at_most(maxarms[a], arms, a)
);

constraint forall(f in FACE)
(
  at_most(maxface[f], face, f)
);


var int: obj;
constraint obj =  sum(s in 1..len)(dance_value[legs[s], arms[s]])
                + sum(s in 1..len)(entice_value[arms[s], face[s]])
                - len*boredom;



solve maximize obj;








