namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

	operation BitwiseRightShift (qs : Qubit[]) : Unit {
		body (...) {
			let n = Length(qs);
			if (n==1) {
				X(qs[0]);
			} else {
				//Controlled X(qs[1..n-1], qs[0]);
				BitwiseRightShift(qs[0..n-2]);
				Controlled X(qs[0..n-2], qs[n-1]);
			}
		}	
		adjoint auto;
		controlled auto;
	}

	operation BitwiseLeftShift (qs : Qubit[]) : Unit {
		body (...) {
			Adjoint BitwiseRightShift(qs);
		}	
		adjoint auto;
		controlled auto;
	}

	operation Perm (qs : Qubit[]) : Unit {
		body (...) {
			let n = Length(qs);
			for (i in 1..n-1) {
				CNOT(qs[0], qs[i]);
			}
		}	
		adjoint auto;
	}

	operation Solve (qs : Qubit[]) : Unit {
        body (...) {
			let n = Length(qs);
			Controlled BitwiseRightShift([qs[n-1]], qs[0..n-2]);
			X(qs[n-1]);
			Controlled BitwiseLeftShift([qs[n-1]], qs[0..n-2]);
			X(qs[n-1]);
			
			Perm(qs);
			H(qs[0]);
			X(qs[n-1]);
			Adjoint Perm(qs);
        }
		adjoint auto;
    }
}