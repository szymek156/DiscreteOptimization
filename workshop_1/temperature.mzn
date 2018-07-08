array[int] of int: readings;
int: start;

enum decison = {heat, str_heat, cool, str_cool, nothing};
array[decison] of int: decison_cost = [1, 5, 3, 9, 0];
array[decison] of int: decison_temp_change = [1, 4, -2, -5, 0];

array[1..length(readings)] of var decison: choices;
array[1..length(readings) + 1] of var int: temp;
var int: totalCost = sum(d in 1..length(choices)) (decison_cost[choices[d]]);

constraint temp[1] = start;

constraint forall(t in 1..length(temp)-1)
(
  temp[t + 1] = ((temp[t] + readings[t]) div 2) +
    decison_temp_change[choices[t]]
);

% Every read in range 25..30, it is better to declare temp var as 25..30, anyway...
constraint forall(r in 1..length(readings) + 1)
(
  temp[r] >= 25 /\ temp[r] <= 30
);


solve minimize totalCost;
output ["IN start \(start)\n"];
output ["IN readings \(readings)\n"];

output ["temp \(temp)\n"];
output ["choice \(choices)\n"];
output ["cost \(totalCost)"];

%{do_nothing, cool, do_nothing, strongly_heat, strongly_heat};