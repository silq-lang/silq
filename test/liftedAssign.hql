def f[k:!ℕ](x:int[k])lifted: 𝔹 {
	z := dup(x);
    for i in [0..10) {
        z = z+1;
    }
    y := 0:𝔹;
    if z > 10 {
        y = !y;
    }
    return y;
}
