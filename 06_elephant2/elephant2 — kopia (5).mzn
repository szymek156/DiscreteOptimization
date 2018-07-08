int: T; % maximum time allowed;
set of int: TIME = 1..T;
set of int: TIME0 = 0..T;
int: E; % weight of elephant in STONES;
set of int: STONE = 0..E;

int: G; % number of guards
set of int: GUARD = 1..G;
array[GUARD] of STONE: easy;  
array[GUARD] of STONE: hard;
array[GUARD] of TIME: tired;

GUARD: p; % maximum people on pier;
GUARD: b; % maximum people on boat;

 set of int: ACT = -1..E; % -1 = goto bank, 0 = wait, > 0 carry stones 
%enum: ACT = {to_bank, wait, easy, hard}; % -1 = goto bank, 0 = wait, > 0 carry stones 
%!!! zmienic na enum? go back, wait, easy, hard

enum PLACE = {boat, bank, invalid};

int: wait = 0;
int: to_bank = -1;
array[GUARD,TIME] of var ACT: act;        % action at time t
array[GUARD, TIME0] of var PLACE: place;

var TIME: end;                            % end time;

% guards can go only in one direction

% constraint forall(t in TIME)
% (
%  forall(g in GUARD)
%  (
%    act[g, t] = to_bank \/ act[g, t] = wait
%  ) \/
%  forall(g in GUARD)
%  (
%    act[g, t] > 0 \/ act[g, t] = wait
%  )
% );


% constraint forall(t in TIME)
% (
%  forall(g1, g2 in GUARD where g1 < g2)
%  (
%    act[g1, t] = act[g2, t] \/ (act[g1, t] * act[g2, t]) = 0 % ŹLE! guardy moga nosic rozne ciezary
%  ) 
% );

% constraint forall(t in TIME)
% (
%  forall(g1, g2 in GUARD where g1 < g2)
%  (
%    (act[g1, t] * act[g2, t]) = 0  \/ (act[g1,t] = act[g2, t]) \/ (act[g1, t] > 0 /\ act[g2, t] > 0)
%  ) 
% );

constraint forall(t in TIME)
(
 forall(g1, g2 in GUARD where g1 < g2)
 (
   (act[g1, t] = 0 \/ act[g2, t] = 0 ) \/ (act[g1,t] = act[g2, t]) \/ (act[g1, t] > 0 /\ act[g2, t] > 0)
 ) 
);

% include "all_equal.mzn"
% constraint forall(t in TIME)
%   all_equal([act[g, t] | g in GUARD])
% )

% constraint forall(t in TIME)
% (
%  forall(g in GUARD where act[g, t] != wait)
%  (
%    act[g, t] = to_bank 
%  ) \/
%  forall(g in GUARD where act[g, t] != wait)
%  (
%    act[g, t] > 0
%  )
% );

% limit of how much guards can be on a pier at given time
constraint forall(t in TIME)
(
 sum(g in GUARD)
 (
   act[g, t] != wait
 ) <= p
);

% limit of guards at boat
constraint forall(t in TIME)
(
 sum(g in GUARD)
 (
   place[g, t] = boat
 ) <= b
);

var int: stonesOnBoat;

constraint sum(t in TIME, g in GUARD where act[g, t] > 0)
(
   act[g, t]
) = stonesOnBoat;


% at least E stones on boat
constraint stonesOnBoat >= E;

% Guard can't take more than hard
constraint forall(t in TIME)
(
 forall(g in GUARD)
 (
   act[g, t] <=  hard[g]
 )
);

% there is no point to get easy + 1 stones, get hard, so adding this contrain should shrink searching space
constraint forall(t in TIME, g in GUARD)
(
   act[g, t] in {hard[g], easy[g], wait, to_bank }
);

% after getting hard stones on the board guard has to rest, in meantime he can come back
constraint forall(t1 in 1..T, g in GUARD where act[g,t1] > easy[g])
(
  forall(t2 in t1..min(t1+tired[g], T))
 (
   %act[g, t1 + t2] = wait \/ act[g, t1 + t2] = to_bank
   act[g, t2] <= 0
 ) % zrobic globalcardinality_up
);

% include "disjunctive.mzn";
% constraint forall(g in GUARD, t in TIME, where act[t, g] > easy[g])
% (
%   disjunctive([t | t in TIME], [tired[g] | t in TIME, where act[t, g] > easy[g]])
% );

%include "globalcardinality
%[act[g, t] < 1 | t in 

% at the beginning all guards are in the bank
constraint forall(g in GUARD)
(
  place[g, 0] = bank
);

% channeling, pos i act
% constraint forall(g in GUARD)
% (
%   forall (t in TIME)
%   (
%     if act[g, t] > 0 then 
%       place[g, t-1] = bank /\ place[g, t] = boat 
%     elseif act[g, t] = to_bank then
%       place[g, t-1] = boat /\ place[g, t] = bank 
%     elseif act[g, t] = wait then
%       place[g, t-1] = place[g, t]
      
%     else false
%     endif
%   )
% );



array[1..3, boat..bank] of PLACE: transitions = [|bank, invalid| boat, bank | invalid, boat|];

predicate nex_pos(var ACT: action, var PLACE: prev, var PLACE: current) =
%  let {var int: signum = ((action div abs(action)) +2)} in
  let {var int: signum = action + 2} in
    transitions[signum, prev] = current %/\ current != invalid
  ;

constraint forall(g in GUARD, t in TIME)
(
    if (act[g, t] > 0) then
      nex_pos(1, place[g, t-1], place[g, t])
   else
      nex_pos(act[g, t], place[g, t-1], place[g, t])
   endif
);

constraint forall(t in end+1..T)
(
  forall(g in GUARD)
  (
    act[g, t] = wait
  )
);


%solve minimize end;

solve  :: int_search([end], input_order, indomain_min, complete) minimize end;

%act = array2d(GUARD,TIME,[0, 0, 5, -1, 10, 0, 0, 0, 0, 0, 15, -1, 0, 0, 0, 15, 0, 0, 0, 0]);

%act = array2d(GUARD,TIME,[10, 0, 0, 0, 0, 0, 0, 0, 0, 0,5, -1, 10, 0, 0, 0, 0, 0, 0, 0,5, -1, 10, 0, 0, 0, 0, 0, 0, 0,0, 0, 10, 0, 0, 0, 0, 0, 0, 0]);

 output ["act:\n"];
 output [" " ++ show_int(4, fix(act[g, t])) ++ if t = T then "\n" else "" endif | g in GUARD, t in TIME];

 output ["place:\n"];
 output [" " ++ show(fix(place[g, t])) ++ if t = T then "\n" else "" endif | g in GUARD, t in TIME];


output ["act = array2d(GUARD,TIME,\(act));\n"];
output ["end = \(end);\n"];









%output [show(act)];













