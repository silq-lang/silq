namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (qs : Qubit[], bits0 : Bool[], bits1 : Bool[]) : ()
    {
        body
        {
            mutable flag = 0;
			mutable b0 = ConstantArray(Length(qs), false);
			mutable b1 = ConstantArray(Length(qs), false);
			mutable dif = 0;
			for (i in 0..Length(qs)-1)
			{
				if (flag == 0  &&  bits0[i] == bits1[i]) {
					if (bits0[i] == true)
					{
						X(qs[i]);
					}
				}
				elif (flag == 0  &&  bits0[i] != bits1[i]) {
					set flag = 1;
					set dif = i;
					if (bits0[i] == false) {
						set b0 = bits0;
						set b1 = bits1;
					}
					else {
						set b0 = bits1;
						set b1 = bits0;
					}
					H(qs[i]);
				}
				else {
					if (b0[i] == b1[i]) {
						if (b0[i] == true) {
							X(qs[i]);
						}
					}
					elif (b0[i] == false) {
						CNOT(qs[dif], qs[i]);
					}
					else {
						CNOT(qs[dif], qs[i]);
						X(qs[i]);
					}
				}
			}
        }
    }
}