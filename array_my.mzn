int: n = 10;

array[0..n] of var 0..9: arr;

constraint sum(i in 0..n)(arr[i]) == product(i in 0..n)(arr[i]);
constraint forall(i, j in 0..n where i < j)(arr[i] <= arr[j]);

solve satisfy