namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[]) : Unit {
        let n = Length(qs);

		mutable Q = qs;
		for (i in 0..n-1) {
			set Q[i] = qs[(i+n-1)%n];
		}

		X(qs[n-1]);
		for (i in n-2..-1..0) {
			(Controlled X) (Q[0..i], qs[i]);
		}
		X(qs[n-1]);

		for (i in 0..n-2) {
			X(qs[i]);
		}
		for (i in n-2..-1..0) {
			(Controlled X) (Q[0..i], qs[i]);
		}
		for (i in 0..n-2) {
			X(qs[i]);
		}
		
		X(qs[n-1]);

		for (i in 1..n-1) {
			CNOT(qs[0],qs[i]);
		}
		H(qs[0]);
		for (i in 1..n-1) {
			CNOT(qs[0],qs[i]);
		}
    }
}
