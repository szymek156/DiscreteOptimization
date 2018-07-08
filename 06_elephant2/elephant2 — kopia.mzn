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
enum PLACE = {boat, bank};

int: wait = 0;
int: to_bank = -1;
array[GUARD,TIME] of var ACT: act;        % action at time t
array[GUARD, TIME0] of var PLACE: place;

var TIME: end;                            % end time;

% guards can go only in one direction

constraint forall(t in TIME)
(
 forall(g in GUARD)
 (
   act[g, t] = to_bank \/ act[g, t] = wait
 ) \/
 forall(g in GUARD)
 (
   act[g, t] > 0 \/ act[g, t] = wait
 )
);

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

% after getting hard stones on the board guard has to rest, in meantime he can come back
constraint forall(t1 in 1..T, g in GUARD where act[g,t1] > easy[g])
(
  forall(t2 in 1..tired[g], where t1 + t2 <= T)
 (
   act[g, t1 + t2] = wait \/ act[g, t1 + t2] = to_bank
 ) % zrobic globalcardinality_up
);


% at the beginning all guards are in the bank
constraint forall(g in GUARD)
(
  place[g, 0] = bank
);

% channeling, pos i act
constraint forall(g in GUARD)
(
  forall (t in TIME)
  (
    if act[g, t] > 0 then 
      place[g, t-1] = bank /\ place[g, t] = boat 
    elseif act[g, t] = to_bank then
      place[g, t-1] = boat /\ place[g, t] = bank 
    elseif act[g, t] = wait then
      place[g, t-1] = place[g, t]
      
    else false
    endif
  )
);

constraint forall(t in end+1..T)
(
  forall(g in GUARD)
  (
    act[g, t] = wait
  )
);

solve minimize end;

% act = array2d(GUARD,TIME,[0, 0, 5, -1, 10, 0, 0, 0, 0, 0, 15, -1, 0, 0, 0, 15, 0, 0, 0, 0]);

output ["act:\n"];
output [" " ++ show_int(4, fix(act[g, t])) ++ if t = T then "\n" else "" endif | g in GUARD, t in TIME];

output ["place:\n"];
output [" " ++ show(fix(place[g, t])) ++ if t = T then "\n" else "" endif | g in GUARD, t in TIME];

output ["end " ++ show(fix(end))];










%output [show(act)];













