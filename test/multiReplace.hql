def a5_SETUP[k:!N](
	oracle:!N x !N x ((const int[k] x const int[k] x 𝔹) !-> 𝔹), 
	const tt:int[k][]
	) : 𝔹[][] {
		
	(n, r, edgeOracle) := oracle;
	rr := 2^r;
	ee := []:B[][];
	for j in [0..rr) { ee ~= [array(rr,false):B[]]; }

	for j in [0..rr) {
		for i in [0..j) {
			def replace(const a:int[k], const b:int[k], component:𝔹[]){
				component[j] := edgeOracle(a, b, component[j]);
				return component;
			}
			ee[j] := replace(tt[i],tt[j],ee[j]);
			ee[k][j] := edgeOracle(tt[j], tt[k], ee[k][j]);
	}	}

	return ee;
}
