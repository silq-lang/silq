namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (N : Int, Uf : ((Qubit[], Qubit) => ())) : Int[]
    {
        body
        {
            mutable v = new Int[N];
            
            mutable mod = N;
            
            for(i in 1..N){
                if(mod >= 2){
					set mod = mod - 2;
				}
			}
            
            using(qubits = Qubit[N + 1]){
                let qs = qubits[0..(N - 1)];
                let ancilla = qubits[N];
                
                Uf(qs, ancilla);
                
                mutable res = M(ancilla);
                
                if(res == Zero){
                    if(mod == 1){
                        set v[0] = 1;
                    }
                }
                if(res == One){
                    if(mod == 0){
                        set v[0] = 1;
                    }
                }
                
                ResetAll(qubits);
            }
            
            return(v);
        }
    }
}