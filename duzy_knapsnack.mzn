enum resources = {IRON, WOOD, BLACKSMITH, CARPENTER};
enum weapons = {AXE, SWORD, PIKE1, PIKE2, CLUB};

array[weapons] of int: power = [11, 18, 15, 17, 11];
array[resources] of int: limit = [5000, 7500, 4000, 3000];

array[weapons, resources] of float: productionCost = array2d(weapons, resources,
                                                            [1.5, 1.0, 1.0, 1.0,
                                                             2.0, 0.0, 2.0, 0.0,
                                                             1.5, 0.5, 1.0, 1.0,
                                                             0.5, 1.0, 0.9, 1.5,
                                                             0.1, 2.5, 0.1, 2.5]);
               

array[weapons] of var int: produce;

constraint forall(weapon in weapons)
(
  produce[weapon] >= 0
);

constraint forall(resource in resources)
(
  sum(weapon in weapons) 
  (
    productionCost[weapon, resource] * produce[weapon] 
  ) <= limit[resource]
);
                                                                                       
solve maximize sum(weapon in weapons)
( 
  produce[weapon] * power[weapon]
)