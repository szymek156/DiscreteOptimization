% Liu Bei forsees that Yuan Shiu will be defeated by Cao Cao
% He needs to find a route to safety in Jin province before the defeat
% But Cao Cao's soldiers are everywhere
int: nrow;
set of int: ROW = 1..nrow;
int: ncol;
set of int: COL = 1..ncol;
% Plains, Mountain, Forest, City, River
enum TERRAIN = { P, M, F, C, R };
array[TERRAIN] of int: delay;
int: timelimit;
array[ROW,COL] of TERRAIN: terrain;
array[ROW,COL] of int: soldier;
array[ROW,COL] of bool: Jin;
int: start_row;
int: start_col;
int: maxstep;
set of int: STEP = 1..maxstep;
set of int: STEP0 = 0..maxstep;
var STEP: steps;
array[ROW,COL] of var STEP0: visit; % which step do we visit position or 0 if not visited

% !!! representing a path as a list of (x,y) where card(list) = steps, so step variables instead of row*col variables
array[STEP] of var COL: row_path;
array[STEP] of var ROW: col_path;


% start at start position
constraint visit[start_row,start_col] = 1;
% only use steps moves
constraint sum(r in ROW, c in COL)(visit[r,c] >= 1) <= steps;

% reach Jin province
% constraint exists(r in ROW, c in COL)(Jin[r,c] /\ visit[r,c] >= 1);
% constraint sum(r in ROW, c in COL)
% (
%  (visit[r,c] > 0 /\ Jin[r,c])
% ) > 0;

% !!!
constraint Jin[row_path[steps], col_path[steps]] = true;

% visit at most one city
% constraint not exists(r1,r2 in ROW, c1,c2 in COL)
%                      ((r1 != r2 \/ c1 != c2)
%                       /\ terrain[r1,c1] = C /\ terrain[r2,c2] = C
%                       /\ visit[r1,c1] >= 1 /\ visit[r2,c2] >= 1);
% constraint sum(r in ROW, c in COL)
% (
%   (visit[r,c] > 0 /\ terrain[r,c] = C)
% ) < 2;
% !!!
% at most one city
constraint sum(i in 1..steps)
(
  terrain[row_path[i], col_path[i]] = C
) <= 1;


% cant enter Mountain
%constraint not exists(r in ROW, c in COL)(terrain[r,c] = M /\ visit[r,c] >= 1);
% constraint sum(r in ROW, c in COL where visit[r,c] > 0)
% (
%    terrain[r,c] = M
% ) = 0;
% constraint forall(r in ROW, c in COL)
% (
%   (visit[r,c] > 0) -> (terrain[r,c] != M )
% );
% !!!
constraint sum(i in 1..steps)
(
  terrain[row_path[i], col_path[i]] = M
) = 0;


% visit only one place in every step
% constraint forall(r1,r2 in ROW, c1,c2 in COL)
%                  (r1 != r2 \/ c1 != c2 
%                   -> (visit[r1,c1] = 0
%                       \/ visit[r2,c2] != visit[r1,c1]));
include "alldifferent_except_0.mzn";
constraint alldifferent_except_0([visit[r,c] | r in ROW, c in COL]);


% steps form a path
% constraint forall(s in 1..steps-1)
%                  (exists(r1, r2 in ROW, c1, c2 in COL)
%                         (abs(r1-r2) + abs(c1-c2) = 1
%                          /\ visit[r1,c1] = s /\ visit[r2,c2] = s+1));
% constraint forall(r1 in ROW, c1 in COL)
% (
%    let {var int: v = visit[r1,c1]} in       
%    (v > 0 /\ v < steps) -> 
%      ((visit[r1-1, c1] = (v+1)) \/
%      (visit[r1+1, c1] = (v+1)) \/
%      (visit[r1, c1-1] = (v+1)) \/
%      (visit[r1, c1+1] = (v+1)))
% );

% !!!
constraint forall(i in 1..steps-1)
(
let
{
  var int: row_diff = abs(row_path[i] - row_path[i+1]),
  var int: col_diff = abs(col_path[i] - col_path[i+1])
} in
   row_diff < 2 /\ % going at most one step, left, up, right, down
  col_diff < 2 /\
  (row_diff + col_diff < 2) % no diagonals
);            
     
                                                   
% no shortcuts
constraint forall(r1,r2 in ROW, c1,c2 in COL)
                (abs(r1-r2) + abs(c1-c2) = 1 ->
                 visit[r1,c1] = 0 \/ visit[r2,c2] = 0 \/
                 abs(visit[r1,c1] - visit[r2,c2]) = 1);
% not too much delay
constraint time <= timelimit;

%var int: time = sum(r in ROW, c in COL)(delay[terrain[r,c]]*(visit[r,c] >= 1));
% !!!
var int: time = sum(i in 1..steps)
(
  delay[terrain[row_path[i], col_path[i]]]
);


% !!! channeling !!!
% visit -> row/col_path
constraint forall(r in ROW, c in COL)
(
  let { var STEP0: step = visit[r, c] } in
  (step = 0) \/ (row_path[step] = r /\ col_path[step] = c)
);

% row/col_path -> visit
constraint forall(s in 1..steps)
(
  visit[row_path[s], col_path[s]] = s
);

% minimize the number of soldiers traversed
solve minimize obj;
var int: obj = sum(r in ROW, c in COL)((visit[r,c] > 0)*soldier[r,c]);
                       
array[TERRAIN] of string: ter = [".", "#", "^", "C", "~"];
output
      ["%"] ++
      [ " " ++ ter[fix(terrain[r,c])] ++ if c = ncol then "\n%" else "" endif
      | r in ROW, c in COL ]
      ++ ["\n%"] ++
      [ if soldier[r,c] > 0 then show_int(2,soldier[r,c]) else " ." endif
        ++ if c = ncol then "\n%" else "" endif
      | r in ROW, c in COL ]
      ++ ["\n"] ++
      ["%"] ++
      [ if fix(visit[r,c]) > 0 then show_int(2,visit[r,c]) else " ." endif
        ++ if c = ncol then "\n%" else "" endif
      | r in ROW, c in COL ]
      ++ ["\nvisit = array2d(ROW,COL,\(visit));\nsteps = \(steps);\ntime = \(time);\nobj = \(obj);"]
      ;
      
      
output ["\n%row_path \(row_path)\n"];
output ["%col_path \(col_path)\n"];