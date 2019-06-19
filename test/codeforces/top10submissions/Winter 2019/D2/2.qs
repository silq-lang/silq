namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        let n = Length(qs);
		for (i in n-1..-1..1) {
			for (j in n-1..-1..i+1) {
				X(qs[j]);
			}
			for (j in i-1..-1..0) {
				(Controlled H) (qs[i..n-1], qs[j]);
			}
			for (j in n-1..-1..i+1) {
				X(qs[j]);
			}
		}
    }
}
