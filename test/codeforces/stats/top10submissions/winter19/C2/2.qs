namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
			let n = Length(x);
			using (anc = Qubit[n-1]) {
				for (p in 1..n-1) {
					for (i in 0..n-p-1) {
						CNOT(x[i+p], x[i]);
					}
					for (i in 0..n-p-1) {
						X(x[i]);
					}
					(Controlled X) (x[0..n-p-1], anc[p-1]);
					for (i in 0..n-p-1) {
						X(x[i]);
					}
					for (i in n-p-1..-1..0) {
						CNOT(x[i+p], x[i]);
					}
				}
				for (p in 1..n-1) {
					X(anc[p-1]);
				}
				X(y);
				(Controlled X) (anc[0..n-2], y);
				for (p in 1..n-1) {
					X(anc[p-1]);
				}
				for (p in 1..n-1) {
					for (i in 0..n-p-1) {
						CNOT(x[i+p], x[i]);
					}
					for (i in 0..n-p-1) {
						X(x[i]);
					}
					(Controlled X) (x[0..n-p-1], anc[p-1]);
					for (i in 0..n-p-1) {
						X(x[i]);
					}
					for (i in n-p-1..-1..0) {
						CNOT(x[i+p], x[i]);
					}
				}
			}
        }
        adjoint auto;
    }
}