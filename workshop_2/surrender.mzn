% workshop 2
% select a set of trade negotiation party
enum NEGOTIATOR;
NEGOTIATOR: dummy; 

int: l; % minimum party size
int: u; % maximum party size
int: m; % minimum joint ability

array[NEGOTIATOR] of int: honor;
array[NEGOTIATOR,NEGOTIATOR] of int: joint;

var set of NEGOTIATOR: chosen;
var int: minHonor;
var int: jointPower = sum(a, b in chosen, where a < b)(joint[a,b]);

constraint jointPower >= m;

constraint card(chosen) >= l /\ card(chosen) <= u;

%constraint minHonor = min([honor[c] | c in chosen]);
constraint minHonor = min(c in chosen)(honor[c]);

solve maximize minHonor;

output ["min party size l = \(l)\n"];
output ["max party size u = \(u)\n"];
output ["minimum joint ability m = \(m)\n"];
output ["chosen = \(chosen)\n"];
output ["minHonor = \(minHonor)\n"];
output ["jointPower = \(jointPower)\n"];

