import qft;

def phaseEstimation[k:!N](
    const U:(int[k] !->mfree int[k]), 
    u:int[k], 
    precision:!N) {

    ancilla := 0:int[precision];
    for i in [0..precision) { ancilla[i] := H(ancilla[i]); }

    for i in [0..precision) { 
        if ancilla[i] {
            for l in [0..2^i) {
                u := U(u);
            }
        }
    }

    ancilla := reverse(QFT[precision])(ancilla);
    result := measure(ancilla);
    measure(u);
    return result;
}