include "alldifferent.mzn";
include "inverse.mzn";

int: n = 8;

array[1..n] of var 1..n: order;
array[1..n] of var 1..n: difference;
array[1..n] of var 1..n: position;


constraint forall(o in 1..n-1)
(
  abs(order[o]-order[o+1]) = difference[o]
);

constraint abs(position[1] - position[n]) = 1;

constraint alldifferent(difference);

constraint inverse(order, position);

solve satisfy;




% array[1..n] of var 1..n: order;
% array[1..n-1] of var 1..n: difference;

% constraint forall(o in 1..n-1)
% (
%   abs(order[o]-order[o+1]) = difference[o]
% );

% constraint alldifferent(order);
% constraint alldifferent(difference);


% solve satisfy;
