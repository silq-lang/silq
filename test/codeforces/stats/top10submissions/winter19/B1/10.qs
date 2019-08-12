namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
	open Microsoft.Quantum.Extensions.Diagnostics;
	
			
	operation Solve (x : Qubit[]) : Int {
        body (...) {
			let amplitudes = [0.0, 1.0, 1.0, 0.0, 1.0];
			let phases = [0.0, 0.0, 3.14159265358*2.0/3.0, 0.0, 3.14159265358*4.0/3.0];
			mutable weights = new ComplexPolar[5];
			for (idx in 0..4) {
				set weights[idx] = ComplexPolar(amplitudes[idx], phases[idx]);
			}
			let fun = StatePreparationComplexCoefficients(weights);
			let num = BigEndian(x);
			Adjoint fun(num);
			if(M(x[0]) == Zero && M(x[1]) == Zero && M(x[2]) == Zero ){
				return 1;
			} else {
				return 0;
			}
        }
    }

	// operation MMain(sign: Int) : String {
	// 		mutable mess = "";
	// 		using (qubit = Qubit[3]) {
	// 				if(sign == 0){
	// 					let amplitudes = [0.0, 1.0, 1.0, 0.0, 1.0];
	// 					let phases = [0.0, 0.0, 3.14159265358*2.0/3.0, 0.0, 3.14159265358*4.0/3.0];
	// 					mutable weights = new ComplexPolar[5];
	// 					for (idx in 0..4) {
	// 						set weights[idx] = ComplexPolar(amplitudes[idx], phases[idx]);
	// 					}
	// 					let fun = StatePreparationComplexCoefficients(weights);
	// 					let num = BigEndian(qubit);
	// 					fun(num);
	// 				} else {
	// 					let amplitudes = [0.0, 1.0, 1.0, 0.0, 1.0];
	// 					let phases = [0.0, 0.0, 3.14159265358*4.0/3.0, 0.0, 3.14159265358*2.0/3.0];
	// 					mutable weights = new ComplexPolar[5];
	// 					for (idx in 0..4) {
	// 						set weights[idx] = ComplexPolar(amplitudes[idx], phases[idx]);
	// 					}
	// 					let fun = StatePreparationComplexCoefficients(weights);
	// 					let num = BigEndian(qubit);
	// 					fun(num);
	// 				}
	// 				DumpMachine("");
	// 				let result = Solve(qubit);
					
					
	// 				set mess = mess + $"{sign}={result};#";
	// 				ResetAll(qubit);
	// 		}
	// 		return mess;
	// }
}