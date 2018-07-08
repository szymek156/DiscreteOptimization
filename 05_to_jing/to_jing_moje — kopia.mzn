

int: nrow;
int: ncol;

set of int: WIDTH  = 1..ncol;
set of int: HEIGHT = 1..nrow;

HEIGHT: start_row;
WIDTH: start_col;

enum TERRAIN = { P, M, F, C, R };

array[1..card(TERRAIN)] of int: delay;

int: timelimit;



array[HEIGHT, WIDTH] of TERRAIN: terrain;
array[HEIGHT, WIDTH] of bool: Jin;
array[HEIGHT, WIDTH] of int: soldier;

int: maxstep;

set of int: PATH = 1..maxstep;

array[PATH] of var WIDTH: x_path;
array[PATH] of var HEIGHT: y_path;
var PATH: path_len;

constraint x_path[1] = start_row /\ y_path[1] = start_col;

%include "global_cardinality.mzn";
%constraint global_cardinality(x_path, [M], [0]);
%include "global_cardinality_low_up.mzn";
%constraint global_cardinality_low_up(x_path, [C], 0, 1);

% no mountains
constraint sum(i in PATH)
(
  terrain[x_path[i], y_path[i]] = M
) = 0;

% at most one city
constraint sum(i in 1..path_len)
(
  terrain[x_path[i], y_path[i]] = C
) <= 1;

% timelimit
constraint sum(i in 1..path_len)
(
  delay[terrain[x_path[i], y_path[i]]]
) <= timelimit;

%has to reach Jin
constraint Jin[x_path[path_len], y_path[path_len]] = true;

%path may be shorter than maxsteps
 constraint forall(i in (path_len+1)..maxstep) (x_path[i] = x_path[path_len] /\ y_path[i] = y_path[path_len]);

%adjacent movements on the grid
%include "sliding_sum.mzn";
%constraint sliding_sum(-1, 1, 2, x_path);
%constraint sliding_sum(-1, 1, 2, y_path);

constraint forall(i in 1..maxstep-1)
(
  let 
  {
    var int: x_diff = abs(x_path[i] - x_path[i+1]), 
    var int: y_diff = abs(y_path[i] - y_path[i+1]) 
  } in
  
    x_diff < 2 /\ % going at most one step, left, up, right, down
    y_diff < 2 /\
    (x_diff + y_diff < 2) % no diagonals
  
);

var int: obj = sum(i in 1..path_len)
(
  soldier[x_path[i], y_path[i]]
) * 1000 + path_len;


%x_path = [1, 2, 3, 4, 5, 6, 6, 6, 5, 4, 3, 3, 3, 3, 4, 5, 6,6,6,6];
%y_path = [1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 4, 5, 6, 6, 6, 6,6,6,6];

output ["obj \(obj)\n"];
output ["\(x_path)\n"];
output ["\(y_path)\n"];
output ["pathlen \(path_len)\n"];

solve minimize obj;

