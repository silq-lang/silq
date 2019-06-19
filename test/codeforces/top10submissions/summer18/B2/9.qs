    namespace Solution {
        open Microsoft.Quantum.Primitive;
        open Microsoft.Quantum.Canon;

        operation Solve (qs : Qubit[]) : Int
        {
            body
            {
                let r = BoolArrFromResultArr(MultiM(qs));
				if (r[0] && r[1])
				{
					return 0;
				}
				for (i in 0..Length(r)-1)
				{
					if (r[i])
					{
						return 1;
					}
				}
				return 0;
            }
        }
    }

