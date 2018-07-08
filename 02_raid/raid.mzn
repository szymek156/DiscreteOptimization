% assignment 2
% select a set of raiding warrior
enum WARRIOR;
WARRIOR: dummy; 
enum CLAN; % the clan they belong too

int: l; % minimum raid party size
int: u; % maximum raid party size
int: m; % limit of hatreds

array[WARRIOR] of int: strength;
array[WARRIOR] of CLAN: clan;

array[CLAN,CLAN] of 0..1: hates;

array[1..u] of var WARRIOR: raid;

%var set of WARRIOR: raid;

% card of set >= l
constraint sum(p in raid where p != dummy)(1) >= l;

% allow to repeat dummy on the array: [W2, W1, D, D, D];
constraint forall(i in 1..u-1)(raid[i] >= (raid[i] != dummy) + raid[i+1]);

constraint sum(a, b in 1..u where a < b)(
  hates[clan[raid[a]],clan[raid[b]]]
) <= m;

var int: obj = sum(p in raid)(strength[p]);
solve maximize obj;

%output["raid = \(raid);\n"];
output ["raid = {"] ++ [if fix(raid[i]) != dummy then show(raid[i]) ++ if i < u /\ fix(raid[i+1]) != dummy then ", " else "" endif else "" endif | i in 1..u ] ++ ["};\n"];

output["obj = \(obj);\n"];


% % assignment 2
% % select a set of raiding warrior
% enum WARRIOR;
% WARRIOR: dummy; 
% enum CLAN; % the clan they belong too

% int: l; % minimum raid party size
% int: u; % maximum raid party size
% int: m; % limit of hatreds

% array[WARRIOR] of int: strength;
% array[WARRIOR] of CLAN: clan;

% array[CLAN,CLAN] of 0..1: hates;

% var set of WARRIOR: raid;
% var int: obj = sum(p in raid)(strength[p]);

% constraint card(raid) >= l /\ card(raid) <= u;

% constraint sum(a, b in raid where a < b)(
%   hates[clan[a],clan[b]]
% ) <= m;

% constraint forall(p in raid)(p != dummy);

% solve maximize obj;

% output["raid = \(raid);\n"];
% output["obj = \(obj);\n"];