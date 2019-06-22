namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	
	// operation Set (desired: Result, q1: Qubit) : Unit {
    //         let current = M(q1);
    //         if (desired != current) {
    //             X(q1);
    //         }
    // }
	
	// operation Bell (q : Qubit[], sign : Int) : Unit {
	// 		if((sign&&&2) == 2){
	// 			Set(One, q[1]);
	// 			//Z(q[1]);
	// 		}
	// 		if((sign&&&1) == 1){
	// 			X(q[0]);
	// 		}
	// 		H(q[0]);
	// 		CNOT(q[0], q[1]);
    // }
	
	// operation PM (q : Qubit, sign : Int) : Unit {
	// 		if(sign == -1){
	// 			X(q);
	// 		}
	// 		H(q);
    // }


    // operation GG (q : Qubit[], p : Qubit, k : Int) : Unit {
	// 		CNOT(q[k], p);
    // }     
	// operation GG1 (q : Qubit[], p : Qubit) : Unit {
	// 		CNOT(q[1], p);
    // }    
	// operation Popcount (q : Qubit[], p : Qubit) : Unit {
	// 		for(i in 0..Length(q)-1){
	// 			GG(q, p, i);
	// 		}
    // } 	
	// operation S0 (q : Qubit[], p : Qubit) : Unit {
	// 		Set(Zero, p);
    // } 
	// operation S1 (q : Qubit[], p : Qubit) : Unit {
	// 		Set(One, p);
    // }
	//operation Modinc(anc : Qubit[]) : Unit {
	//	body (...) {
	//		let cnt = LittleEndian(anc);
	//		IntegerIncrementLE(1, cnt);
	//		X(anc[0]);
	//		SWAP(anc[0], anc[1]);
	//		X(anc[0]);
	//	}
	//	controlled adjoint auto;
	//}
	//
	//operation Sumup(x : Qubit[], anc : Qubit[]) : Unit {
	//	body (...) {
	//		for(i in 0..Length(x)-1){
	//			let cnt = LittleEndian(anc);
	//			(Controlled Modinc)([x[i]], (anc));
	//		}
	//	}
    //    adjoint auto;
	//
	//}
	//		
	//operation Solve (x : Qubit[], y : Qubit) : Unit {
    //    body (...) {
	//		using (anc = Qubit[2]){
	//			Sumup(x, anc);
	//			ApplyToEachCA(X, anc);
	//			CCNOT(anc[0], anc[1], y);
	//			ApplyToEachCA(X, anc);
	//			(Adjoint Sumup)(x, anc);
	//		}
    //    }
    //    adjoint auto;
    //}
	
	function find_diff(A : Bool[], B : Bool[]) : Int {
		mutable ans = -1;
		for(i in 0..Length(A)-1){
			if(A[i] != B[i] && ans == -1){
				set ans = i;
			}
		}
		return ans;
	}
	
	
	
	operation Setup_01(qs : Qubit[], a : Int, b : Int) : Unit {
		body (...) {
			let A = BoolArrFromPositiveInt(a, Length(qs));
			let B = BoolArrFromPositiveInt(b, Length(qs));
			let m = Length(A);
			let x = find_diff(A, B);
			for(i in 0..Length(qs)-1){
				if(i != x){
					if(A[x] != A[i]){
						if(not A[x]){
							X(qs[x]);
						}
						CNOT(qs[x], qs[i]);
						if(not A[x]){
							X(qs[x]);
						}
					}
					if(B[x] != B[i]){
						if(not B[x]){
							X(qs[x]);
						}
						CNOT(qs[x], qs[i]);
						if(not B[x]){
							X(qs[x]);
						}
					}
				}
			}
			for(i in 1..Length(qs)-1){
				CNOT(qs[0], qs[i]);
			}
		}
		controlled adjoint auto;
	}
	operation R_diag_2(qs : Qubit[], a : Int, b : Int) : Unit {
		body (...) {
			Setup_01(qs, a, b);
			
	        ApplyToEachCA(X, qs[1..Length(qs)-1]);
			// 2.1 seems to work
			(Controlled Ry)(qs[1..Length(qs)-1], (2.1, qs[0]));
	        ApplyToEachCA(X, qs[1..Length(qs)-1]);
			Adjoint Setup_01(qs, a, b);
		}
		controlled adjoint auto;
	}
	
	
	operation Solve (qs : Qubit[]) : Unit {
	
		//(Controlled Ry)(qs[1..Length(qs)-1], (0.7, qs[0]));
		//Setup_01(qs, 1, 2);
		let N = Length(qs);
		let m = 1<<<N;
		//R_diag_2(qs, 1, 2);
		for(i in 1..m-1){
			R_diag_2(qs, m-i, m-i-1);
		}
		
	    //let cnt = LittleEndian(qs);
	    //ModularIncrementLE(1, 7, cnt);
		//for(i in 1..Length(qs)-1){
		//	Controlled H([qs[i]], qs[0]);
		//}
		//ApplyToEachCA(Ry(3e-2, _), qs);
		//let ones = [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0];
		//for(i in 0..len(qs)){
		//	let bits = BigIntToBools(ToBigInt (i));
		//}
		//let fun = StatePreparationPositiveCoefficients(amplitudes);
		//let qsBE = BigEndian(qs);
		//fun(qsBE);
	}
	
	// operation DumpUnitaryToFiles (N : Int, unitary : (Qubit[] => Unit)) : Unit {
    //     let size = 1 <<< N;
        
    //     using (qs = Qubit[N]) {
    //         for (k in 0 .. size - 1) {                
    //             // Prepare k-th basis vector
    //             let binary = BoolArrFromPositiveInt(k, N);
                
    //             //Message($"{k}/{N} = {binary}");
    //             // binary is little-endian notation, so the second vector tried has qubit 0 in state 1 and the rest in state 0
    //             ApplyPauliFromBitString(PauliX, true, binary, qs);
                
    //             // Apply the operation
    //             unitary(qs);
                
    //             // Dump the contents of the k-th column
    //             DumpMachine($"DU_{N}_{k}.txt");
                
    //             ResetAll(qs);
    //         }
    //     }
	// }
	
	// // The operation which is called from C# code
    // operation CallDumpUnitary (N : Int) : Unit {
    //     // make sure the operation passed to DumpUnitaryToFiles matches the number of qubits set in Driver.cs
    //     let unitary = Solve(_);

    //     DumpUnitaryToFiles(N, unitary);
	// }

}