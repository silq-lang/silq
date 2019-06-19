def solve(q0:𝔹, q1:𝔹) {
    q0 := rotY(q0, 2.000000*0.61547970867);
    if !q0 {
        q1 := H(q1);
    }
    return (X(q0),q1);
}