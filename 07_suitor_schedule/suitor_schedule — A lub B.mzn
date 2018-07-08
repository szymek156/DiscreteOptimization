% scheduling suitors
enum SUITOR;
SUITOR: LiuBei; % which suitor is LiuBei
int: n; % number of meetings
set of int: MEETING = 1..n;
array[MEETING] of SUITOR: suitor;

enum ROOM = { Red, Gold, Blue };
array[SUITOR,ROOM] of int: mintime;
array[SUITOR,ROOM] of int: maxtime;
constraint forall(s in SUITOR, r in ROOM)
                 (assert(mintime[s,r] >= 1 /\ maxtime[s,r] >= mintime[s,r], 
                  "error in mintime/maxtime at [\(s),\(r)]\n"));

array[ROOM,ROOM] of int: move;
constraint forall(r in ROOM)(assert(move[r,r] = 0,"move[\(r),\(r)] != 0\n"));

int: ndays; % number of days
set of int: DAY = 1..ndays;
int: earliest; % time for earliest meeting start
int: latest;  % time for end of latest meeting

int: lessontime; % time for kung fu lesson;
int: minsep;     % minimum time between consecutive kung fu lessons

array[ROOM] of int: usedstart;  % time others use each room each day
array[ROOM] of int: useddur;    % durations of others use

enum STAGE = {A,B,C};
STAGE: stage;

set of int: TIME = 0..24*ndays;

array[MEETING] of var TIME: start;
array[MEETING] of var TIME: dur;    % duration in false schedule
array[MEETING] of var ROOM: room;
set of int: KUNGFU = 1..n;
array[KUNGFU] of var int: kungfu;  % start time for each lesson
   % unused lessons have start times after 24*ndays


% she can 'work' :) without overlaping nor interrupting
include "disjunctive.mzn";
constraint disjunctive(start, dur);

% rooms are sometimes out of service

predicate occupied_room(ROOM: room_color) =
  forall(m in MEETING where room[m] = room_color)
  (
   let
    {
      array[DAY] of TIME: room_occupied     = [ usedstart[room_color] + 24*(d-1) | d in DAY];
      array[DAY] of TIME: room_occupied_dur = [ useddur[room_color]              | d in DAY];
    }
    in
      disjunctive([start[m]] ++ room_occupied, [dur[m]] ++ room_occupied_dur)
  );


% shit won't work, 
% MiniZinc: type error: no function or predicate with this signature found: `disjunctive(array[int] of var opt int,array[int] of var opt int)'

% include "disjunctive_opt.mzn";  
% predicate occupied_room(ROOM: room_color) =

%   let
%   {
%     array[DAY] of TIME: room_occupied     = [ usedstart[room_color] + 24*(d-1) | d in DAY];
%     array[DAY] of TIME: room_occupied_dur = [ useddur[room_color]              | d in DAY];
  
%     array[int] of var opt int: room_start = [ start[m] | m in MEETING where room[m] = room_color];
%     array[int] of var opt int: room_dur   = [ dur[m]   | m in MEETING where room[m] = room_color];
%   }
%   in
%     disjunctive(room_occupied ++ room_start, room_occupied_dur ++ room_dur);


constraint occupied_room(Red);
constraint occupied_room(Gold);
constraint occupied_room(Blue);

% duration is between min and max for given room
constraint forall(m in MEETING)
(
  dur[m] >= mintime[suitor[m], room[m]] /\ 
  dur[m] <= maxtime[suitor[m], room[m]]

%    dur[m] in mintime[suitor[m], room[m]]..maxtime[suitor[m], room[m]]
);

% she can 'work' :) only during earliest and latest
constraint forall(m in MEETING)
(
  let 
  { 
    var TIME: start_work = start[m] mod 24,
%     var TIME: end_work   = (start[m] + dur[m]) mod 24
  } in
  
     start_work >= earliest 
  /\ start_work <= latest - dur[m] 
%    /\ end_work <= latest 
%    /\ start_work < end_work
);

% take into account delay between room transitions
% fun fact, you can sort arrays, but turned out it is not needed here
% include "sort_fn.mzn";
% array[MEETING] of var TIME: startSorted;
% constraint startSorted = sort(start);


% channeling variable - array of meetings in ascending order
% for example, for given start:
% start           = [8, 32, 37, 36, 12, 15];
% it ensures that:
% meetingsInOrder = [1, 5,  6,  2,  4,  3];

array[1..n] of var MEETING: meetingsInOrder;
constraint forall(m in 2..n)
(
  let { var MEETING: tell_me;}
  in
    meetingsInOrder[m] = tell_me /\ start[tell_me] > start[meetingsInOrder[m-1]]
);

constraint forall(m in 2..n)
(
  let
  {
    var MEETING: previous = meetingsInOrder[m-1],
    var MEETING: current  = meetingsInOrder[m],
    var int: delay = move[room[previous], room[current]]
  } in
  
%  trace("start[\(current)] [\(start[current]) >= (start[\(previous)] [\(start[previous])] + dur[\(previous)] {\(dur[previous])})\n",
  start[current] >= start[previous] + dur[previous] + delay
);


constraint forall(k in KUNGFU)
(
  kungfu[k] = ndays*24 + 1
);

var int: obj;

constraint sum(m in MEETING where suitor[m] = LiuBei)
(
  dur[m]
) = obj;

%start = [32, 8, 40, 16, 37, 13];
%dur =[4, 4, 2, 2, 3, 3];
%room = [Blue, Blue, Red, Red, Red, Red];
%kungfu = [49, 49, 49, 49, 49, 49];
%obj = 8;
% meetingsInOrder = [1, 5,  6,  2,  4,  3];
solve maximize obj;

output ["start = \(start);\n"];
output ["dur = \(dur);\n"];
output ["room = \(room);\n"];
output ["kungfu = \(kungfu);\n"];
output ["obj = \(obj);\n"];

% output ["meetingsInOrder = \(meetingsInOrder);\n"];
















