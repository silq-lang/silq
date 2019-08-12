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
    //     using (qs = Qubit[3])
    //     {
    //         Generate(true, qs);
    //         let v1 = Solve(qs);
    //         Message($"{v1} is zero");

    //         DumpRegister((), qs[1..2]);
    //         ResetAll(qs);

    //         Generate(false, qs);
    //         let v2 = Solve(qs);
    //         Message($"{v2} is one");

    //         DumpRegister((), qs[1..2]);
    //         ResetAll(qs);
    //     }
    // }

    // operation Generate(zero: Bool, qs: Qubit[]) : Unit
    // {
    //     let omega = 2.0 * PI() / 3.0;

    //     X(qs[0]);
    //     Ry(ArcCos(Sqrt(2.0 / 3.0))*2.0, qs[1]);
    //     CNOT(qs[1], qs[0]);
            
    //     if (zero) { Rz(omega, qs[1]); }
    //     else { Rz(omega*2.0, qs[1]); }

    //     (Controlled Ry)([qs[0]], (ArcCos(Sqrt(1.0 / 2.0))*2.0, qs[2]));
    //     if (zero) { Rz(omega*2.0, qs[2]); }
    //     else { Rz(omega, qs[2]); }

    //     CNOT(qs[2], qs[0]);
    // }

    operation Solve(qs: Qubit[]) : Int
    {
        let omega = 2.0 * PI() / 3.0;

        mutable result = 0;

        CNOT(qs[1], qs[2]); 
        // Here |100> + w|0x1> + w2|0(1-x)1>

        CNOT(qs[2], qs[0]);
        X(qs[0]);
        // Here |0> (x) (|00> + w2|x1> + w|(1-x)1>)
        
        if (M(qs[0]) != Zero) {
            Message("Something very wrong..");
        }

        Rz(-omega, qs[2]);

        CNOT(qs[2], qs[1]);
        Rz(-omega, qs[1]);
        CNOT(qs[2], qs[1]);

        (Adjoint Controlled Ry)(
            [qs[2]], 
            (2.0*ArcCos(Sqrt(1.0 / 2.0)), qs[1]));

        Ry(2.0*ArcCos(Sqrt(2.0 / 3.0)), qs[2]);

        let (m1, m2) = (M(qs[1]), M(qs[2]));

        if (m1 == Zero && m2 == One) {
            set result = 0;
        }
        else {
            set result = 1;
        }

        return result;
    }
}