int: T; % maximum time allowed;
set of int: TIME = 1..T;

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
int: wait = 0;
int: to_bank = -1;
array[GUARD,TIME] of var ACT: act;        % action at time t
var TIME: end;                            % end time;







array[TIME] of var int: boat; % num of stones on boat after action

function var int: num_moved(TIME: t) = sum(g in GUARD)(max( act[g, t], 0 ));




% array[GUARD, TIME] of var bool: onboat;

% function var int: moved_to(var ACT: action, var bool: before) =
%   if action = 0 then before else action > 0 endif;

% % fill onboat
% constraint forall(g in GUARD)(
%   onboat[g, 1] = moved_to(act[g, 1], false)
% );
% constraint forall(g in GUARD, t in 2..T)(
%   onboat[g, t] = moved_to(act[g, t], onboat[g, t-1])
% );


function var -1..1: movediff(var ACT: a) = if a > 0 then 1 else a endif;

array[TIME] of var 0..G: num_onboat;
constraint num_onboat[1] = 0;
constraint forall(t in 2..T)(num_onboat[t] = num_onboat[t-1] +
  sum(g in GUARD)(movediff(act[g, t-1]))
);

% limit of num of guards on boat
% constraint forall(t in TIME)(
%   sum(g in GUARD)(onboat[g, t]) <= b
% );
constraint forall(t in TIME)(
  num_onboat[t] <= b
);

% limit of num of guards on pier
constraint forall(t in TIME)(
  sum(g in GUARD)(act[g, t] != 0) <= p
);

% have to move same direction each time
constraint forall(t in TIME)(
  (forall(g in GUARD)(act[g, t] >= 0)) \/
  (forall(g in GUARD)(act[g, t] <= 0))
);

% for each guard, limit on how many stones moved each time
constraint forall(g in GUARD, t in TIME)(
  act[g, t] <= hard[g]
);

% has to rest after hard
constraint forall(g in GUARD, t in TIME)(
  (act[g, t] > easy[g]) -> let { var int: te = min(T, t+tired[g]) } in
    forall(i in t+1..te)(act[g, i] <= 0)
);

% has to go back after moving
% constraint forall(g in GUARD, t1 in 1..end, t2 in 1..end where t1 < t2)(
%   (act[g, t1] > 0 /\ act[g, t2] > 0) -> exists(t3 in t1..t2)(act[g, t3] < 0)
% );

% constraint forall(g in GUARD, t1 in 1..end, t2 in 1..end where t1 < t2)(
%   (act[g, t1] < 0 /\ act[g, t2] < 0) -> exists(t3 in t1..t2)(act[g, t3] > 0)
% );


function var 1..3: direction(var ACT: a) =
  if a = 0
  then 1
  else
    if a > 0 then 2 else 3 endif
  endif;

% regular version of above
include "regular.mzn";
constraint forall(g in GUARD)(
  regular([direction(act[g, t]) | t in TIME], 2, 3, guard_d, 1, {1, 2})
);
array[1..2, 1..3] of 0..2: guard_d = 
  % wait, to boat, to bank
  [| 1, 2, 0 % at bank
   | 2, 0, 1 % at boat
   |];

% correct number of stones boat
constraint boat[1] = num_moved(1);
constraint forall(t in 2..T)(boat[t] = boat[t-1] + num_moved(t));
% constraint forall(t in end+1..T)(boat[t] = 0);

% has more or equal than E stones in the end
constraint boat[end] >= E;

% only wait after end
constraint forall(g in GUARD, t in end+1..T)(act[g, t] = 0);

solve minimize end;
% constraint end = 3;
% solve satisfy;

% constraint act = array2d(GUARD, TIME, [
%   10, 0, 0, 0, 0, 0, 0, 0, 0, 0,
%   5, -1, 10, 0, 0, 0, 0, 0, 0, 0,
%   5, -1, 10, 0, 0, 0, 0, 0, 0, 0,
%   0, 0, 10, 0, 0, 0, 0, 0, 0, 0,
% ]);

% onboat = array2d(1..4 ,1..10 ,[
%   true, true, true, false, false, false, false, false, false, false,
%   true, false, true, false, false, false, false, false, false, false,
%   true, false, true, false, false, false, false, false, false, false,
%   false, false, true, false, false, false, false, false, false, false]);

% boat = array1d(1..10 ,[20, 18, 48, 0, 0, 0, 0, 0, 0, 0]);

output  ["act = array2d(GUARD, TIME, [\n"] ++
        [show_int(2, fix(act[g, t])) ++ (if t = T then ",\n" else ", " endif) | g in GUARD, t in TIME] ++
        ["]);\n"] ++
["end = \(end);"]