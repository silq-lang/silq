import std.random, std.math, std.mathspecial, std.exception;

real sampleFlip(real p){
	return uniform!"[]"(0.0L,1.0L)<=p;
}

real sampleUniformInt(real a,real b){
	enforce(ceil(a)>=long.min && floor(b)<=long.max);
	return uniform!"[]"(cast(long)ceil(a),cast(long)floor(b));
}

real sampleGauss(real μ,real ν){
	return (μ+sqrt(ν)*normalDistributionInverse(uniform!"[]"(0.0L,1.0L)));
}

real sampleUniform(real a,real b){
	return uniform!"[]"(a,b);
}

real sampleLaplace(real μ,real b){
	return μ+b*(2*.uniform!"[]"(0,1)-1)*log(uniform!"(]"(0.0L,1.0L));
}

real sampleRayleigh(real ν){
	return sqrt(-2*ν*log(.uniform!"(]"(0.0L,1.0L)));
}

real samplePareto(real a,real b){
	return b/(.uniform!"(]"(0.0L,1.0L)^^(1.0/a));
}

real sampleGamma(real α,real β){ // Marsaglia & Tang, 2000
	if(α<1) return sampleGamma(1+α,β)*sampleUniform(0,1)^^(1/α);
	real d=α-1.0/3.0,c=1.0/sqrt(9.0*d);
	for(;;){
		real x=sampleGauss(0,1),v=1+c*x,u;
		if(v>0){
			v=v*v*v,u=sampleUniform(0,1);
			if(u<1-0.331*x*x*x*x||log(u)<0.5*x*x+d*(1-v+log(v)))
				return d*v/β;
		}
	}
}

real sampleExponential(real λ){
	return -log(uniform!"(]"(0.0L,1.0L))/λ;
}
