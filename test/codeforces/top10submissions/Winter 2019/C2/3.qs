namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

	operation IsNotPeriodicWithPeriod (x : Qubit[], y : Qubit, p: Int) : Unit {
		body (...) {
			let n = Length(x);
			for (i in 0..n-p-1) {CNOT(x[i], x[i+p]); X(x[i+p]);}
			Controlled X(x[p..n-1], y); X(y);
			for (i in 0..n-p-1) {CNOT(x[i], x[i+p]); X(x[i+p]);}
		}
		adjoint auto;
	}
    

    operation Solve (x : Qubit[], y : Qubit) : Unit {
        body (...) {
            let n = Length(x);
			let n1 = n/2 + n % 2;
			using (pers = Qubit[n-n1]) {
				for (p in n1..n-1) {IsNotPeriodicWithPeriod(x, pers[p-n1], p);}
				Controlled X(pers, y);
				X(y);
				for (p in n1..n-1) {Adjoint IsNotPeriodicWithPeriod(x, pers[p-n1], p);}
			}
        }
        adjoint auto;
    }
}