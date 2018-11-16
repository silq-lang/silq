def transpose[a,n:!ℕ](x: (a^n)^n){
	for i in [0..n){
		for j in [0..n){
			(x[i][j],x[j][i]) := (x[j][i], x[i][j]);
		}
	}
	return x;
}
