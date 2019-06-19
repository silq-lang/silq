namespace Solution {
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;

    operation Solve (q : Qubit) : Int
    {
        body
        {
            if (RandomInt(2) == 1)
			{
				let res = M(q);
				if (res == One) {
					return 1;
				}
				else {
					return -1;
				}
			}
			else {
				H(q);
				let res = M(q);
				if (res == One) {
					return 0;
				}
				else {
					return -1;
				}
			}
        }
    }
}