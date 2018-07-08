int: n = 30;
int: m = n-1;

array[0..m] of var 0..3: arr;

constraint arr[0] = 0;
constraint arr[m] = 3;
constraint forall(i in 0..(m - 1))(arr[i] + arr[i+1] <= 3);
constraint forall(i in 0..m where i mod 3 = 0)(arr[i] <= 2);
 
solve maximize sum(i in 0..m)(arr[i])