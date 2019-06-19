namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            using (anc = Qubit[2]) {
				let n = Length(x);
				for (i in 0..n-1) {
					X(anc[1]);
					CCNOT(x[i], anc[1], anc[0]);
					X(anc[1]);
					X(anc[0]);
					CCNOT(x[i], anc[0], anc[1]);
					X(anc[0]);
				}
				X(anc[0]); X(anc[1]);
				CCNOT(anc[0], anc[1], y);
				X(anc[0]); X(anc[1]);
				for (i in 0..n-1) {
					X(anc[0]);
					CCNOT(x[i], anc[0], anc[1]);
					X(anc[0]);
					X(anc[1]);
					CCNOT(x[i], anc[1], anc[0]);
					X(anc[1]);
				}
			}
        }
        adjoint auto;
    }
}