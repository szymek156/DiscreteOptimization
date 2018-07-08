int: T; % maximum time allowed;
set of int: TIME = 1..T;
int: G; % number of guards
int: F;
int: W;

array[TIME] of var -F..F: move_food;      % move food +ve bank to boat, -ve boat to bank
array[TIME] of var -W..W: move_water;     % move water +ve bank to boat, -ve boat to bank
var TIME: end;                            % end time;

array[TIME] of var 0..1: on_boat;
array[TIME] of var 0..F: count_food;      % count food
array[TIME] of var 0..W: count_water;     % count water

% All movements has to be in the same direction
constraint forall(t in 1..end)
(
 (move_food[t] > 0 /\ move_water[t] > 0) \/
 (move_food[t] < 0 /\ move_water[t] < 0)
);

% Guards moves bowls
constraint forall(t in 1..end)
(
 abs(move_food[t]) + abs(move_water[t]) <= G
);

constraint count_food[1] = move_food[1];

constraint forall(t in 2..end)
(
 count_food[t] = count_food[t-1] + move_food[t]
);


% constraint forall(t in TIME)
% (
%   count_food[t] = sum(f in 1..t)(move_food[f])
% );

constraint count_water[1] = move_water[1];

constraint forall(t in 2..end)
(
 count_water[t] = count_water[t-1] + move_water[t]
);

% constraint forall(t in TIME)
% (
%   count_water[t] = sum(f in 1..t)(move_water[f])
% );

constraint count_food[end] = 0 /\ count_water[end] = 0 /\ on_boat[end-1] = 1;

constraint forall(t in end..T)
(
 count_water[t] = 0 /\ count_food[t] = 0
);

% Model elephant movements
% from bank to boat:
constraint on_boat[1] = 0;

constraint forall(t in 2..end)
(
 let
 {
    var 0..F: bank_food = F - count_food[t];
    var 0..W: bank_water = W - count_water[t];
 } in
  if (count_food[t] = count_water[t] /\ count_food[t] > bank_food /\ count_water[t] > bank_water) then
   on_boat[t] = 1
 elseif (on_boat[t-1] = 1 /\ bank_food = bank_water /\ bank_food > count_food[t] /\ bank_water > count_water[t]) then
   on_boat[t] = 0
 else
   on_boat[t] = on_boat[t-1]
 endif
);

% eating, drinking not allowed
constraint forall(t in TIME)
(
 let
 {
    var 0..F: bank_food = F - count_food[t];
    var 0..W: bank_water = W - count_water[t];
 } in
 if (on_boat[t] = 1) then
   (count_food[t] = 0 <-> count_water[t] = 0)
 else
   bank_food = 0 <-> bank_water = 0
 endif
);



solve minimize end;