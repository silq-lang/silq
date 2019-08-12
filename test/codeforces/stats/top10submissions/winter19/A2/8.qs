namespace Solution
{
    open Microsoft.Quantum.Primitive;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Extensions.Math;
    open Microsoft.Quantum.Extensions.Testing;
    open Microsoft.Quantum.Extensions.Diagnostics;
    open Microsoft.Quantum.Extensions.Convert;

    // operation SolveTest() : Unit 
    // {
    //     using (qs = Qubit[4])
    //     {
    //         mutable bits = new Bool[][4];
            
    //         set bits[0] = [true, false, false, false];
    //         set bits[1] = [false, true, false, false];
    //         set bits[2] = [false, false, true, false];
    //         set bits[3] = [false, false, false, true];

    //         Solve(qs, bits);
    
    //         DumpRegister((), qs);

    //         ResetAll(qs);
    //     }
    // }

    operation Solve(qs: Qubit[], bits: Bool[][]) : Unit
    {
        SolveInternal(qs, bits, 0);
    }
    operation SolveInternal(qs : Qubit[], bits : Bool[][], current: Int) : Unit 
    {
        // DumpRegister((), qs);

        let l = Length(bits);

        mutable trueIndex = new Int[0];
        mutable falseIndex = new Int[0];
    
        for (i in 0 .. l-1) {
            if (bits[i][current]) {
                set trueIndex = trueIndex + [i];
            }
            else {
                set falseIndex = falseIndex + [i];
            }
        }
         
        // Message($"{bits}, {current} {trueIndex} {falseIndex}");

        if (Length(trueIndex) == 0) {
            if (current != Length(qs)-1) {
                SolveInternal(qs, bits, current+1);
            }
        }
        elif (Length(falseIndex) == 0) {            
            for (i in 0 .. current-1) {
                if (bits[0][i] == false) { X(qs[i]); }
            }

            (Controlled X)(qs[0..current-1], qs[current]);

            for (i in 0 .. current-1) {
                if (bits[0][i] == false) { X(qs[i]); }
            }

            if (current != Length(qs)-1) {
                SolveInternal(qs, bits, current+1);
            }
        }
        else {
            let coeff = ToDouble(Length(falseIndex)) / ToDouble(l);

            if (current == 0) {
                Ry(2.0 * ArcCos(Sqrt(coeff)), qs[current]);
            }
            else {
                for (i in 0 .. current-1) {
                    if (bits[0][i] == false) { X(qs[i]); }
                }

                // Message("CONTROLLED RY");
                (Controlled Ry)(qs[0..current-1], (2.0 * ArcCos(Sqrt(coeff)), qs[current]));

                for (i in 0 .. current-1) {
                    if (bits[0][i] == false) { X(qs[i]); }
                }

                // Message("AFTER STATUS");
                // DumpRegister((), qs);
            }

            mutable trueBits = new Bool[][0];
            mutable falseBits = new Bool[][0];

            for (i in trueIndex) {
                set trueBits = trueBits + [bits[i]]; 
            }
            for (i in falseIndex) {
                set falseBits = falseBits + [bits[i]]; 
            }

            if (current != Length(qs)-1) {
                SolveInternal(qs, trueBits, current+1);
                SolveInternal(qs, falseBits, current+1);
            }
        }
    }
}