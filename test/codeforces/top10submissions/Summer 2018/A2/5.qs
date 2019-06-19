namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits : Bool[]) : ()
    {
        body
        {
            H(qs[0]);

	    for(i in 2..Length(bits)){
			if(bits[i - 1] == true){
				CNOT(qs[0], qs[i - 1]);
			}
		}
        }
    }
}