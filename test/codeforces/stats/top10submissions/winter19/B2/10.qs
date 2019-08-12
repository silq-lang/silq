namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	open Microsoft.Quantum.Extensions.Convert;
		
	operation QFT(x : Qubit[]) : Unit {
		body (...) {
			for(i in 0..Length(x)-1){
				H(x[i]);
				for(j in i+1..Length(x)-1){
					(Controlled Rz)([x[i]], (3.1415926535897932384626/ToDouble(1<<<(j-i)), x[j]));
				}
			}
		}
		controlled adjoint auto;
	}
			
	//operation Solve (x : Qubit) : Int {
    //    body (...) {
	//		mutable res = 0;
	//		let omega = 3.1415926535897932384626*2.0/3.0;
	//		Rz(omega/2.0, x);
	//		using (ys = Qubit[6]) {
	//			for(i in 0..Length(ys)-1){
	//				let y = ys[i];
	//				for(j in 1..1<<<i){
	//					//(Controlled Ry)([x], (omega/2.0, y));
	//					(Controlled X)([x], (y));
	//				}
	//			}
	//			(Adjoint QFT)(ys);
	//			for(i in 3..Length(ys)-1){
	//				if(M(ys[i]) == One){
	//					set res = res + (1<<<i);
	//				}
	//			}
	//			//DumpMachine("");
	//			ResetAll(ys);
	//		}
	//		return res;
    //    }
    //}

	//operation Solve (x : Qubit) : Int {
    //    body (...) {
	//		mutable res = 0;
	//		let omega = 3.1415926535897932384626*2.0/3.0;
	//		using(ys = Qubit[3]){
	//			let amplitudes = [0.0, 1.0, 1.0, 0.0, 1.0];
	//			let phases = [0.0, 0.0, omega*2.0, 0.0, omega];
	//			mutable weights = new ComplexPolar[5];
	//			for (idx in 0..4) {
	//				set weights[idx] = ComplexPolar(amplitudes[idx], phases[idx]);
	//			}
	//			let fun = StatePreparationComplexCoefficients(weights);
	//			let num = BigEndian(ys);
	//			fun(num);
	//			for(i in 0..2){
	//				//(Controlled X)([ys[i]], (x));
	//				(Controlled H)([ys[i]], (x));
	//			}
	//			Adjoint fun(num);
	//			
	//			//H(x);
	//			//if(M(x) == Zero){
	//			//	X(x);
	//			//}
	//			DumpMachine("");
	//			for(i in 0..2){
	//				if(M(ys[i]) == One){
	//					set res = res + (1<<<i);
	//				}
	//			}
	//			//DumpMachine("");
	//			
	//			
	//			ResetAll(ys);
	//		}
	//		return res;
    //    }
    //}

	//operation Solve (x : Qubit) : Int {
    //    body (...) {
	//		mutable res = 0;
	//		let omega = 3.1415926535897932384626*2.0/3.0;
	//		Ry(omega/2.0, x);
	//		using(ys = Qubit[2]){
	//			let y = ys[0];
	//			let z = ys[1];
	//			Controlled X([x], y);
	//			Controlled X([x], z);
	//			//DumpMachine("");
	//			//DumpMachine("");
	//			
	//			H(x);
	//			H(y);
	//			if(Measure([PauliY, PauliY, PauliY], [x, y, z]) == Zero){
	//				set res = res + 1;
	//			}
	//			if(Measure([PauliX, PauliX, PauliX], [x, y, z]) == Zero){
	//				set res = res + 2;
	//			}
	//			if(Measure([PauliZ, PauliZ, PauliZ], [x, y, z]) == Zero){
	//				set res = res + 4;
	//			}
	//			
	//			ResetAll(ys);
	//		}
	//		return res;
    //    }
    //}
	//operation Solve (x : Qubit) : Int {
    //    body (...) {
	//		H(x);
	//		Rz(3.1415926535897932384626/2.0, x);
	//		// now we have a tine enselmble
	//		
	//		DumpMachine("");
	//		return 1;
    //    }
    //}
	
	operation Solve (x : Qubit) : Int {
        body (...) {
			mutable res = 0;
			let pi = 3.1415926535897932384626;
			H(x);
			Rz(3.1415926535897932384626/2.0, x);
			// now we have a tine enselmble
			
			using (ys = Qubit[1]){
				let y = ys[0];
				(Controlled Ry)([x], (2.0*0.9553166181245092781638571025, y));
				(Controlled H)([y], x);
				H(x);
				//DumpMachine("");
				if(M(x) == One){
					set res = res + 1;
				}
				if(M(y) == One){
					set res = res + 2;
				}
				ResetAll(ys);
			}
			if(res == 0){
				return 2;
			} else {if(res == 1){
				return 1;
			} else {
				return 0;
			}}
			
			return res;
        }
    }


	// operation MMain(sign: Int) : String {
	// 		mutable mess = "";
	// 		for(it in 0..19){
	// 			using (qubit = Qubit[1]) {
	// 					let amplitudes = [1.0, 1.0];
	// 					let phases = [0.0, 3.14159265358*ToDouble(sign)*2.0/3.0];
	// 					mutable weights = new ComplexPolar[2];
	// 					for (idx in 0..1) {
	// 						set weights[idx] = ComplexPolar(amplitudes[idx], phases[idx]);
	// 					}
	// 					let fun = StatePreparationComplexCoefficients(weights);
	// 					let num = BigEndian(qubit);
	// 					fun(num);
	// 					//DumpMachine("");
	// 					let result = Solve(qubit[0]);
	// 					//DumpMachine("");
						
						
	// 					set mess = mess + $"{sign}={result};#";
	// 					ResetAll(qubit);
	// 			}
	// 		}
	// 		return mess;
	// }
}