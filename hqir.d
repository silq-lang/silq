import core.exception: AssertError;
import std.conv: ConvOverflowException, text, to;
import std.stdio: File, stderr;
import std.array: Appender, appender, array, join;
import std.string: endsWith;
import std.format: format;
import std.functional: partial;
import std.algorithm: map, filter, canFind, count, all, any, fold;
import std.range: iota, zip, repeat;
import std.utf: byCodeUnit;
import std.bigint: BigInt, toDecimalString;
import std.traits: EnumMembers;
import std.algorithm.mutation: swap, reverse;
import std.math: frexp, isFinite;
import std.meta: AliasSeq;

import util.maybe;

import ast_sem = ast.semantic_;
import ast_exp = ast.expression;
import ast_ty = ast.type;
import ast_decl = ast.declaration;
import ast_scope = ast.scope_;
import ast_lex = ast.lexer;
import ast_conv = ast.conversion;
import ast_low = ast.lowerings;

import ast.lexer: Tok, TokenType;
import ast.expression: Id, Expression, UnaryExp, BinaryExp;
import ast.semantic_: typeForDecl;
import ast.reverse: knownLength;

mixin("alias ast_ty_Nt = ast_ty.\u2115t;");
mixin("alias ast_ty_Zt = ast_ty.\u2124t;");
mixin("alias ast_ty_Qt = ast_ty.\u211at;");
mixin("alias ast_ty_R = ast_ty.\u211d;");
mixin("alias ast_ty_C = ast_ty.\u2102;");

mixin("alias ast_ty_NumericType_Nt = ast_ty.NumericType.\u2115t;");
mixin("alias ast_ty_NumericType_Zt = ast_ty.NumericType.\u2124t;");
mixin("alias ast_ty_NumericType_Qt = ast_ty.NumericType.\u211at;");
mixin("alias ast_ty_NumericType_R = ast_ty.NumericType.\u211d;");
mixin("alias ast_ty_NumericType_C = ast_ty.NumericType.\u2102;");

mixin("alias ast_conv_ZtoFixedConversion = ast_conv.\u2124toFixedConversion;");
mixin("alias ast_conv_UintToNConversion = ast_conv.UintTo\u2115Conversion;");
mixin("alias ast_conv_IntToZConversion = ast_conv.IntTo\u2124Conversion;");

static immutable string opComma = ",";
static immutable string opConcat = "~";
static immutable string opDefine = ":=";
static immutable string opAssign = "\u2190";
static immutable string opConcatAssign = opConcat ~ opAssign;

alias Unit = void[0];
enum unit = Unit.init;

alias IdMap(T) = T[Id];
alias IdSet=IdMap!Unit;

static size_t regCtr = 0;
static size_t lambdaCtr = 0;

static immutable size_t MAX_UNROLL_LENGTH = 16;

private string mangleName(ast_exp.Identifier id) {
	auto b = appender!string;
	bool first = true;
	bool esc = false;
	foreach(c; id.name.byCodeUnit) {
		if((!first && c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_') {
			b.put(c);
		} else {
			esc = true;
			if(!first) b.put('.');
			b.put("0123456789abcdef"[c >> 4]);
			b.put("0123456789abcdef"[c & 15]);
		}
		first = false;
	}
	if(!esc) return id.name;
	return b[];
}

private bool isReturnLambda(ast_decl.FunctionDef parent, ast_decl.FunctionDef child) {
	if(Id.s!"artificial" !in parent.attributes) return false;
	if(parent.body_.s.length != 1) return false;
	auto ret = cast(ast_exp.ReturnExp)parent.body_.s[0];
	if(!ret) return false;
	auto lam = cast(ast_exp.LambdaExp)ret.e;
	if(!lam) return false;
	return lam.fd is child;
}

static immutable string HEX = "0123456789abcdef";
private void escapeStr(Appender!string* o, string val) {
	o.put('"');
	foreach(c; val) {
		if(c == '"' || c == '\\') {
			o.put('\\');
		}
		if(c >= 32 && c <= 126) {
			o.put(c);
			continue;
		}
		o.put('\\');
		if(c < 128) {
			o.put('x');
		} else {
			if(c < (1 << 16)) {
				o.put('u');
			} else {
				o.put('U');
				o.put(HEX[c >> 28]);
				o.put(HEX[(c >> 24) & 15]);
				o.put(HEX[(c >> 20) & 15]);
				o.put(HEX[(c >> 16) & 15]);
			}
			o.put(HEX[(c >> 12) & 15]);
			o.put(HEX[(c >> 8) & 15]);
		}
		o.put(HEX[(c >> 4) & 15]);
		o.put(HEX[c & 15]);
	}
	o.put('"');
}

private static ast_lex.Location locEnd(ast_lex.Location loc) {
	if(!loc.rep) return loc;
	return ast_lex.Location(loc.rep[$-1..$], loc.line + cast(int) loc.rep[0..$-1].byCodeUnit.count!(c => c == '\n'));
}

final class CReg {
	string name;
	immutable size_t index;

	this() scope @safe {
		this.index = regCtr++;
	}

	override string toString() const @safe {
		if(name) {
			return format("$%s.%d", name, index);
		} else {
			return format("$%d", index);
		}
	}

private:
	string asStr;
}

final class QReg {
	string name;
	immutable size_t index;

	this() scope @safe {
		this.index = regCtr++;
	}

	override string toString() const @safe {
		if(name) {
			return format("%%%s.%d", name, index);
		} else {
			return format("%%%d", index);
		}
	}
}

static immutable string ctypeBitvec = "builtin.bitvec";
static immutable string ctypeQtArray = "builtin.qtypes";
static immutable string ctypeSilqTuple = "silq.tuple";
static immutable string ctypeSilqArray = "silq.array";
static immutable string ctypeSilqQFunc = "silq.qfunc";
static immutable string ctypeRTTI = "silq.rtti";

static immutable string opCond = "cond";
static immutable string opAbort = "abort";

static immutable string opCallAsClassicalIndirect = "call_as_classical";
static immutable string opCallClassicalIndirect = "classical_call";
static immutable string opCallMeasureIndirect = "call";
static immutable string opCallMfreeIndirect = "mfree_call";
static immutable string opCallQfreeIndirect = "qfree_call";
static immutable string opCallMfreeRevIndirect = "mfree_call_rev";
static immutable string opCallQfreeRevIndirect = "qfree_call_rev";

private string opCallClassical(string name) {
	if(!name.ptr) return opCallClassicalIndirect;
	assert(name.length > 0);
	return format("classical_call[%s]", name);
}

private string opCallMeasure(string name) {
	if(!name.ptr) return opCallMeasureIndirect;
	assert(name.length > 0);
	return format("call[%s]", name);
}

private string opCallMfree(string name) {
	if(!name.ptr) return opCallMfreeIndirect;
	assert(name.length > 0);
	return format("mfree_call[%s]", name);
}

private string opCallQfree(string name) {
	if(!name.ptr) return opCallQfreeIndirect;
	assert(name.length > 0);
	return format("qfree_call[%s]", name);
}

private string opCallMfreeRev(string name) {
	if(!name.ptr) return opCallMfreeRevIndirect;
	assert(name.length > 0);
	return format("mfree_call_rev[%s]", name);
}

private string opCallQfreeRev(string name) {
	if(!name.ptr) return opCallQfreeRevIndirect;
	assert(name.length > 0);
	return format("qfree_call_rev[%s]", name);
}

static immutable string opAllocError = "qfree_call[qbuiltin.error]";
static immutable string opAllocQubit = "qfree_call[silq_builtin.alloc_qubit]";
static immutable string opAllocBitvec = "qfree_call[qbuiltin.alloc_bitvec]";
static immutable string opAllocUint = "qfree_call[silq_builtin.alloc_uint]";
static immutable string opAllocUnit = "qfree_call[qbuiltin.alloc_unit]";
static immutable string opAllocQubit0 = "qfree_call[qbuiltin.alloc_0]";
static immutable string opAllocQubit1 = "qfree_call[qbuiltin.alloc_1]";
static immutable string opDeallocError = "qfree_call_rev[qbuiltin.error]";
static immutable string opDeallocQubit0 = "qfree_call_rev[qbuiltin.alloc_0]";
static immutable string opDeallocQubit1 = "qfree_call_rev[qbuiltin.alloc_1]";
static immutable string opDeallocBitvec = "qfree_call_rev[qbuiltin.alloc_bitvec]";
static immutable string opDeallocUnit = "qfree_call_rev[qbuiltin.alloc_unit]";
static immutable string opInplaceNot = "qfree_call[qbuiltin.X]";
static immutable string opLiftedNot = "qfree_call[qbuiltin.lifted_X]";
static immutable string opDup = "qfree_call[qbuiltin.dup]";
static immutable string opUndup = "qfree_call_rev[qbuiltin.dup]";
static immutable string opMeasureQubit = "call[qbuiltin.measure_qubit]";
static immutable string opMeasureBitvec = "call[qbuiltin.measure_bitvec]";
static immutable string opMeasureUint = "call[silq_builtin.measure_uint]";
static immutable string opForget = "autoforget";
static immutable string opCSplit = "csplit";
static immutable string opQSplit = "qsplit";
static immutable string opCMerge = "cmerge";
static immutable string opQMerge = "qmerge";
static immutable string opCat = "qfree_call[qbuiltin.cat]";
static immutable string opUncat = "qfree_call_rev[qbuiltin.cat]";
static immutable string opIndexDupI = "qfree_call[silq_builtin.cindex_i]";
static immutable string opIndexDupD = "qfree_call[silq_builtin.cindex_d]";
static immutable string opSliceI = "qfree_call[silq_builtin.cslice_i]";
static immutable string opSliceD = "qfree_call[silq_builtin.cslice_d]";
static immutable string opIndexSwapI = "qfree_call[silq_builtin.cswap_i]";
static immutable string opIndexSwapD = "qfree_call[silq_builtin.cswap_d]";

private string opPack(size_t n) {
	if(n == 0) return opAllocUnit;
	return "qfree_call[qbuiltin.pack]";
}

private string opUnpack(size_t n) {
	if(n == 0) return opDeallocUnit;
	return "qfree_call_rev[qbuiltin.pack]";
}

struct QCapture {
	CReg qtype;
	QReg qreg;
}

final class Value {
	CReg _creg = null;
	QReg _qreg = null;

	FunctionInfo funcInfo;
	CReg[] funcCapR;
	QCGen qfuncQcg;
	CReg[] qfuncCapT;
	QReg[] qfuncCapR;

	@property
	bool hasQuantum() {
		if(qfuncQcg) return true;
		return !!_qreg;
	}

	@property
	bool hasClassical() {
		return !!_creg;
	}

	@property
	CReg creg() {
		return _creg;
	}

	@property
	QReg qreg() {
		auto qcg = qfuncQcg;
		if(!qcg) return _qreg;
		_qreg = qcg.pack(qfuncCapT, qfuncCapR);

		funcInfo = null;
		funcCapR = null;
		qfuncQcg = null;
		qfuncCapT = null;
		qfuncCapR = null;

		if(!_qreg) {
			// quantum component suddenly disappeared?
			// We cannot change hasQuantum after initialization, so create an empty one.
			_qreg = qcg.allocUnit();
		}
		return _qreg;
	}

	override string toString() {
		if(funcInfo) return format("func[%s]", funcInfo.prettyName);
		return format("(%s,%s)", _creg, _qreg);
	}

	static Value newReg(CReg creg, QReg qreg) {
		auto v = new Value();
		v._creg = creg;
		v._qreg = qreg;
		return v;
	}

	static Value newFunction(ScopeWriter sc, FunctionInfo fi, Value[] captures) {
		auto cCapR = appender!(CReg[]);
		auto qCapT = appender!(CReg[]);
		auto qCapR = appender!(QReg[]);
		foreach(i, cap; fi.captures) {
			auto val = captures[i];
			if(cap.hasClassical) {
				cCapR.put(val.creg);
			} else if(val.hasClassical) {
				assert(0, "Capture has no classical component but argument does");
			}
			if(val.hasQuantum) {
				assert(cap.hasQuantum, "Capture has no quantum component but argument does");
				assert(val.qreg);
				qCapT.put(sc.getQType(typeForDecl(cap.innerDecl), val));
				qCapR.put(val.qreg);
			} else if(cap.hasQuantum) {
				qCapT.put(sc.ctx.qtUnit);
				qCapR.put(null);
			}
		}

		auto v = new Value();
		v._creg = sc.ccg.funcPack(fi.indirectName, cCapR[]);
		v.funcInfo = fi;
		v.funcCapR = cCapR[];

		auto qtype = sc.ccg.qtTuple(qCapT[]);
		if(qtype is sc.ctx.qtUnit) {
			foreach(val; captures) {
				if(val.hasQuantum) sc.qcg.deallocUnit(val.qreg);
			}
			return v;
		}

		v._creg = sc.ccg.qfuncPack(v._creg, qtype);
		v.qfuncQcg = sc.qcg;
		v.qfuncCapT = qCapT[];
		v.qfuncCapR = qCapR[];
		return v;
	}

	void setName(ast_exp.Identifier name) {
		if(_creg && !_creg.name) _creg.name = mangleName(name);
		if(_qreg && !_qreg.name) _qreg.name = mangleName(name);
	}
}

private bool valueIsZero(Expression exp) {
	if (auto m = exp.asIntegerConstant(true)) {
		return m.get() == 0;
	}
	return false;
}

private bool typeHasClassical(Expression ty) {
	assert(ty);
	if(ast_ty.isEmpty(ty)) return true;
	if(!ast_ty.hasClassicalComponent(ty)) return false;
	if(auto tupTy = cast(ast_ty.TupleTy) ty) {
		return tupTy.types.any!(typeHasClassical);
	}
	if(auto vecTy = cast(ast_ty.VectorTy) ty) {
		return !valueIsZero(vecTy.num) && typeHasClassical(vecTy.next);
	}
	if(auto intTy = ast_ty.isFixedIntTy(ty)) {
		return intTy.isClassical;
	}
	return true;
}

private bool typeHasQuantum(Expression ty) {
	assert(ty);
	if(!ast_ty.hasQuantumComponent(ty)) return false;
	if(auto tupTy = cast(ast_ty.TupleTy) ty) {
		return tupTy.types.any!(typeHasQuantum);
	}
	if(auto vecTy = cast(ast_ty.VectorTy) ty) {
		return !valueIsZero(vecTy.num) && typeHasQuantum(vecTy.next);
	}
	if(auto arrTy = cast(ast_ty.ArrayTy) ty) {
		return typeHasQuantum(arrTy.next);
	}
	if(auto intTy = ast_ty.isFixedIntTy(ty)) {
		if(intTy.isClassical) return false;
		return !valueIsZero(intTy.bits);
	}
	return true;
}

private bool typeHasQDep(Expression ty) {
	assert(ty);
	if(!ast_ty.hasClassicalComponent(ty)) return false;
	if(!ast_ty.hasQuantumComponent(ty)) return false;
	if(auto tupTy = cast(ast_ty.TupleTy) ty) {
		return tupTy.types.any!(subty => typeHasQDep(subty));
	}
	if(auto vecTy = cast(ast_ty.VectorTy) ty) {
		return !valueIsZero(vecTy.num) && typeHasQDep(vecTy.next);
	}
	if(auto arrTy = cast(ast_ty.ArrayTy) ty) {
		return typeHasQuantum(arrTy.next);
	}
	if(ast_ty.isFixedIntTy(ty)) {
		return false;
	}
	return true;
}

private bool productTyIsMoved(ast_ty.ProductTy ty) {
	final switch(ty.captureAnnotation) {
		case ast_ty.CaptureAnnotation.none:
		case ast_ty.CaptureAnnotation.const_:
			return false;
		case ast_ty.CaptureAnnotation.moved:
			return true;
		case ast_ty.CaptureAnnotation.once:
		case ast_ty.CaptureAnnotation.spent:
			assert(0, "TODO mixed const/moved captures");
	}
}

private void putRet(FunctionInfo fi, ref CReg[] cRet, ref QReg[] qRet, Value v) {
	if(!fi || fi.retHasClassical) {
		cRet = [v.creg];
	} else {
		assert(!v.creg);
	}
	if(!fi || fi.retHasQuantum) {
		qRet = [v.qreg];
	} else {
		assert(!v.qreg, format("callee returns no quantum component but caller wants it"));
	}
}

private enum ConvertFlags {
	noop = 0,
	check = 1,
	classical = 2,
	quantum = 4,
}

private ConvertFlags qpromoteFlags(Expression ty) {
	if(!typeHasQuantum(ty)) {
		return ConvertFlags.noop;
	}
	if(auto tupTy = cast(ast_ty.TupleTy) ty) {
		return tupTy.types.fold!((v, sub) => v | qpromoteFlags(sub))(ConvertFlags.noop);
	}
	if(auto vecTy = cast(ast_ty.VectorTy) ty) {
		if(valueIsZero(vecTy.num)) return ConvertFlags.noop;
		return qpromoteFlags(vecTy.next);
	}
	if(auto arrTy = cast(ast_ty.ArrayTy) ty) {
		return qpromoteFlags(arrTy.next);
	}
	if(auto prodTy = cast(ast_ty.ProductTy) ty) {
		return ConvertFlags.classical;
	}
	return ConvertFlags.classical | ConvertFlags.quantum;
}

private ConvertFlags conversionFlags(ast_conv.Conversion conv) {
	assert(conv);
	if(cast(ast_conv.NoOpConversion) conv || cast(ast_conv.AnnotationPun) conv || cast(ast_conv.TypeConversion) conv || cast(ast_conv.ExplosionConversion) conv) {
		return ConvertFlags.noop;
	}
	if(cast(ast_conv_UintToNConversion) conv || cast(ast_conv_IntToZConversion) conv) {
		return ConvertFlags.noop;
	}
	if(cast(ast_conv.NumericConversion) conv) {
		auto r = ConvertFlags.classical;
		if(conv.from == ast_ty_Nt() && conv.to == ast_ty_Zt()) r = ConvertFlags.noop;
		if(conv.from == ast_ty_Qt() && conv.to == ast_ty_R()) r = ConvertFlags.noop;
		return r;
	}
	if(auto nConv = cast(ast_conv.NumericCoercion) conv) {
		auto r = ConvertFlags.classical;
		if(conv.from == ast_ty_Zt() && conv.to == ast_ty_Nt()) r = ConvertFlags.noop;
		if(conv.from == ast_ty_R() && conv.to == ast_ty_Qt()) r = ConvertFlags.noop;
		if(nConv.needsCheck) r |= ConvertFlags.check;
		return r;
	}
	if(cast(ast_conv.QuantumPromotion) conv) {
		assert(!typeHasQuantum(conv.from));
		return qpromoteFlags(conv.to);
	}
	if(auto tConv = cast(ast_conv.TransitiveConversion) conv) {
		return conversionFlags(tConv.a) | conversionFlags(tConv.b);
	}
	if(auto tupConv = cast(ast_conv.TupleConversion) conv) {
		return tupConv.elements.fold!((v, sub) => v | conversionFlags(sub))(ConvertFlags.noop);
	}
	if(auto vecConv = cast(ast_conv.VectorConversion) conv) {
		auto r = conversionFlags(vecConv.next);
		if(vecConv.checkLength) r |= ConvertFlags.check;
		return r;
	}
	if(auto arrConv = cast(ast_conv.ArrayConversion) conv) {
		return conversionFlags(arrConv.next);
	}
	if(auto arrConv = cast(ast_conv.ArrayToVectorConversion) conv) {
		auto r = ConvertFlags.classical;
		if(arrConv.checkLength) r |= ConvertFlags.check;
		return r;
	}
	if(auto arrConv = cast(ast_conv.VectorToArrayConversion) conv) {
		return ConvertFlags.classical;
	}
	if(auto funcConv = cast(ast_conv.FunctionConversion) conv) {
		// annotation conversions are no-op
		auto r = conversionFlags(funcConv.dom) | conversionFlags(funcConv.cod);
		return r != ConvertFlags.noop ? ConvertFlags.classical : ConvertFlags.noop;
	}
	if(auto fConv = cast(ast_conv.FixedToVectorConversion) conv) {
		auto t = ast_ty.isFixedIntTy(conv.from);
		assert(t);
		auto r = t.isClassical ? ConvertFlags.classical : ConvertFlags.noop;
		if(fConv.checkLength) r |= ConvertFlags.check;
		return r;
	}
	if(auto fConv = cast(ast_conv.VectorToFixedConversion) conv) {
		auto t = ast_ty.isFixedIntTy(conv.to);
		assert(t);
		auto r = t.isClassical ? ConvertFlags.classical : ConvertFlags.noop;
		if(fConv.checkLength) r |= ConvertFlags.check;
		return r;
	}
	auto r = ConvertFlags.noop;
	if(typeHasClassical(conv.to)) r |= ConvertFlags.classical;
	if(typeHasQuantum(conv.to)) r |= ConvertFlags.quantum;
	return r;
}

struct PureOpKey {
	string op;
	CReg[] args;
}

class ExprInfo {
	immutable size_t id;
	Expression expr;

	this(size_t id, Expression expr) {
		this.id = id;
		this.expr = expr;
	}
}

struct CondC {
	CReg reg;
	bool value = true;

	CondC invert(){ return CondC(reg, !value); }

	bool opCast(T:bool)(){ return !!reg; }
}

struct CondQ {
	QReg reg;
	bool value = true;

	CondQ invert(){ return CondQ(reg, !value); }

	bool opCast(T:bool)(){ return !!reg; }
}

struct CondAny {
	union {
		CReg _creg;
		QReg _qreg;
	};
	bool value;
	bool isQuantum;

	this(CReg r, bool value = true) scope @safe nothrow {
		assert(r);
		this._creg = r;
		this.value = value;
		this.isQuantum = false;
	}

	this(QReg r, bool value = true) scope @safe nothrow {
		assert(r);
		this._qreg = r;
		this.value = value;
		this.isQuantum = true;
	}

	this(CondC c) scope @safe nothrow {
		assert(c.reg);
		this(c.reg, c.value);
	}

	this(CondQ c) scope @safe nothrow {
		assert(c.reg);
		this(c.reg, c.value);
	}

	bool opCast(T:bool)(){ return this !is CondAny.init; }

	@property
	bool isClassical() const pure @safe nothrow {
		return !isQuantum;
	}

	@property
	CReg creg() pure @trusted nothrow {
		assert(!isQuantum);
		return _creg;
	}

	@property
	QReg qreg() pure @trusted nothrow {
		assert(isQuantum);
		return _qreg;
	}

	@property
	CondQ qcond() pure @safe nothrow {
		return CondQ(qreg, value);
	}

	@property
	CondC ccond() pure @safe nothrow {
		return CondC(creg, value);
	}

	CondAny invert() @safe nothrow {
		return isQuantum ? CondAny(qreg, !value) : CondAny(creg, !value);
	}

	string toString(){ return text("CondAny(",isClassical?text(ccond):text(qcond),")"); }
}

class RTTI {
	ScopeWriter sc;
	ExprInfo ei;

	CReg _packed;

	CReg _qtypeF;
	CReg _promoteF;
	CReg _measureF;

	this(ScopeWriter sc, ExprInfo ei) {
		this.sc = sc;
		this.ei = ei;
	}

	static RTTI builtin(Writer ctx, CReg qtypeF, CReg promoteF, CReg measureF) {
		auto r = new RTTI(null, null);
		r._qtypeF = qtypeF;
		r._promoteF = promoteF;
		r._measureF = measureF;
		r._packed = ctx.literalBox(ctypeRTTI, [qtypeF, promoteF, measureF]);
		return r;
	}

	@property
	CReg qtypeF() {
		if(_qtypeF) return _qtypeF;
		auto f = _packed ? sc.ccg.boxIndex(ctypeRTTI, 3, _packed, 0) : sc.genQTypeFunc(ei.expr);
		_qtypeF = f;
		return f;
	}

	@property
	CReg promoteF() {
		if(_promoteF) return _promoteF;
		auto f = _packed ? sc.ccg.boxIndex(ctypeRTTI, 3, _packed, 1) : sc.genPromoteFunc(ei.expr);
		_promoteF = f;
		return f;
	}

	@property
	CReg measureF() {
		if(_measureF) return _measureF;
		auto f = _packed ? sc.ccg.boxIndex(ctypeRTTI, 3, _packed, 2) : sc.genMeasureFunc(ei.expr);
		_measureF = f;
		return f;
	}

	@property
	CReg packed() {
		if(_packed) return _packed;
		auto p = sc.ccg.boxPack(ctypeRTTI, [this.qtypeF, this.promoteF, this.measureF]);
		_packed = p;
		return p;
	}
}

struct CondRetValue {
	CReg condC;
	QReg condQ;

	bool hasClassical(){ return !!condC; }
	bool hasQuantum(){ return !!condQ; }

	this(CReg condC) {
		this.condC = condC;
	}
	this(QReg condQ) {
		this.condQ = condQ;
	}
	this(CReg condC, QReg condQ) {
		this.condC = condC;
		this.condQ = condQ;
	}

	static CondRetValue makeConst(bool val, ScopeWriter w) {
		return CondRetValue(val ? w.ctx.boolTrue : w.ctx.boolFalse);
	}

	CondRetValue toQuantum(ScopeWriter w) {
		assert(hasClassical ^ hasQuantum);
		if(hasQuantum) {
			return this;
		}
		return CondRetValue(w.qcg.allocQubit(condC));
	}

	static CondRetValue merge(CondAny cond, CondRetValue v0, CondRetValue v1, ScopeWriter w0, ScopeWriter w1, ScopeWriter w) {
		assert(v0.hasClassical ^ v0.hasQuantum);
		assert(v1.hasClassical ^ v1.hasQuantum);
		bool isQuantum = cond.isQuantum || v0.hasQuantum() || v1.hasQuantum();
		if(isQuantum) {
			v0 = v0.toQuantum(w0);
			v1 = v1.toQuantum(w1);
		}
		assert(v0.hasClassical ^ v0.hasQuantum);
		assert(v0.hasClassical == v1.hasClassical);
		assert(v0.hasQuantum == v1.hasQuantum);

		auto v = w.valMerge(cond, Value.newReg(v0.condC, v0.condQ), Value.newReg(v1.condC, v1.condQ));
		assert(v.hasClassical == !isQuantum);
		assert(v.hasQuantum == isQuantum);
		return CondRetValue(v.creg, v.qreg);
	}

	CondRet asCondRet() {
		assert(!!condC ^ !!condQ);
		return CondRet(condQ ? CondAny(condQ) : CondAny(condC));
	}
}

struct CondRet {
	CondC condC;
	CondQ condQ;
	bool isAnd = false;

	@property
	//deprecated
	CondAny cond(){ // TODO: remove
		assert(!!condC ^ !!condQ);
		if(condC) return CondAny(condC);
		return CondAny(condQ);
	}

	bool opCast(T:bool)(){ return !!condC||!!condQ; }

	this(CondAny cond) {
		if(cond.isQuantum) condQ=cond.qcond;
		else condC=cond.ccond;
	}
	this(CondC condC) {
		this.condC = condC;
	}
	this(CondQ condQ) {
		this.condQ = condQ;
	}
	this(CondC condC, CondQ condQ, bool isAnd = false) {
		this.condC = condC;
		this.condQ = condQ;
		this.isAnd = isAnd;
	}

	void forget(ScopeWriter sc) {
		if(!condQ) return;
		sc.qcg.forget(condQ.reg);
	}

	CondRet invert() {
		return CondRet(condC.invert(), condQ.invert, !isAnd);
	}

	RetValue valMerge(RetValue v0, RetValue v1, ScopeWriter w) {
		if((!!v0.classicalRet ^ !!v0.quantumRet) && (!!v1.classicalRet ^ !!v1.quantumRet)) {
			if(!!v0.classicalRet == !!v1.classicalRet) {
				if(!!v0.classicalRet) {
					assert(!!condC ^ !!condQ);
					return RetValue(w.valMerge(condQ ? CondAny(condQ) : CondAny(condC), v0.classicalRet, v1.classicalRet));
				}
			}
		}
		assert(0,text("TODO ",v0," ",v1));
	}

	ScopeWriter addToScope(ast_scope.NestedScope nscope, ScopeWriter w) {
		assert(isAnd);
		if(condC) w = w.withCond(nscope, CondAny(condC));
		if(condQ) w = w.withCond(nscope, CondAny(condQ));
		return w;
	}

	CondRetValue asCondRetValue(ScopeWriter w) {
		assert(!!condC ^ !!condQ);
		auto valT = condQ ? w.withCond(w.nscope, CondAny(condQ)).valAllocQubit(1) : w.valNewC(w.ctx.boolTrue);
		auto valF = condQ ? w.withCond(w.nscope, CondAny(condQ.invert())).valAllocQubit(0) : w.valNewC(w.ctx.boolFalse);
		auto val = w.valMerge(condQ ? CondAny(condQ) : CondAny(condC), valF, valT); // TODO: this is overkill for cond.value = true or cond.isClassical
		assert(!!val.hasClassical ^ !!val.hasQuantum);
		return CondRetValue(val.creg, val.qreg);
	}

	bool isQuantum() { // TODO: remove
		return cond.isQuantum;
	}

	RetValue updateRetCond(RetValue retv, CondRet previous, ScopeWriter w) {
		auto ret = retv.classicalRet;
		assert(ret && !retv.quantumRet,"TODO");
		auto wRet = w;
		if(previous) {
			wRet = wRet.withCond(wRet.nscope, previous.cond);
		}
		Value retUnreachable, retReachable;
		wRet.valSplit(cond, retUnreachable, retReachable, ret);
		wRet.withCond(wRet.nscope, cond.invert()).valDeallocError(retUnreachable);
		if(previous) {
			auto wRet2 = w.withCond(w.nscope, cond);
			retUnreachable = Value.newReg(null, previous.isQuantum ? wRet2.withCond(wRet.nscope, previous.cond.invert()).qcg.allocError() : null);
			ret = wRet2.valMerge(previous.cond, retUnreachable, retReachable);
		} else {
			ret = retReachable;
		}
		return RetValue(ret);
	}

	RetValue mergeRet(CondAny cond, RetValue r0, RetValue r1, ScopeWriter w) {
		return RetValue.valMerge(cond, r0, r1, w.withCond(w.nscope, this.cond));
	}

	ScopeWriter genMerge(CondAny cond, ScopeWriter w0, ScopeWriter w1, ScopeWriter w){
		w = w.withCond(w.nscope, this.cond);
		w.genMerge(cond, w0, w1);
		return w;
	}

	RetValue allocUnreachableRet(RetValue reachable, ScopeWriter w) {
		RetValue r;
		if(reachable.classicalRet) r.classicalRet = Value.newReg(null, reachable.classicalRet.hasQuantum ? w.withCond(w.nscope, cond).qcg.allocError() : null);
		if(reachable.quantumRet) r.quantumRet = Value.newReg(null, reachable.classicalRet.hasQuantum ? w.withCond(w.nscope, cond).qcg.allocError() : null);
		return r;
	}

	ScopeWriter removeCondRet(ScopeWriter w) {
		foreach(name, ref var; w.vars) {
			if(!var.value) continue;
			auto valUnreachable = Value.newReg(null, cond.isQuantum ? w.withCond(w.nscope, cond).qcg.allocError() : null);
			var.value = w.valMerge(cond, var.value, valUnreachable);
		}
		return w;
	}

	ScopeWriter replaceCondRet(CondRet previous, ScopeWriter w){
		auto w0 = w.withCond(w.nscope, cond);
		auto w1 = w.withCond(w.nscope, cond.invert());
		auto wg = w, w0g = w0;
		if(previous) {
			wg = wg.withCond(wg.nscope, previous.cond.invert());
			w0g = w0g.withCond(w0g.nscope, previous.cond.invert());
		}
		foreach(name, ref var; w.vars) {
			if(!var.value) continue;
			Value v0, v1;
			wg.valSplit(cond, v1, v0, var.value);
			w0g.valDeallocError(v0);
			w1.defineVar(var.decl, v1);
			var.value = null;
		}
		if(previous) {
			w1 = previous.removeCondRet(w1);
		}
		return w1;
	}
}

struct RetValue {
	Value classicalRet;
	Value quantumRet;

	this(Value value) {
		classicalRet = value;
	}

	bool opCast(T:bool)(){
		return classicalRet || quantumRet;
	}

	static RetValue valMerge(CondAny cond, RetValue r0, RetValue r1, ScopeWriter w) {
		assert(r0.classicalRet && !r0.quantumRet, "TODO");
		assert(r1.classicalRet && !r1.quantumRet, "TODO");
		return RetValue(w.valMerge(cond, r0.classicalRet, r1.classicalRet));
	}
}


struct Result {
	RetValue retValue;
	bool isReturn() scope @safe nothrow {
		return retValue && !retCond;
	}
	CondRet retCond;
	bool isConditionalReturn() scope @safe nothrow {
		return retValue && retCond;
	}
	CReg abortWitness;
	bool isAbort() scope @safe nothrow {
		return !!abortWitness;
	}

	@property
	bool isPass() scope @safe nothrow {
		return !retValue && !isAbort;
	}

	@property
	bool mayPass() scope @safe nothrow {
		return !(isReturn || isAbort);
	}

	private this() scope @safe nothrow @disable;

	private this(RetValue retValue, CondRet retCond, CReg abortWitness) scope @safe nothrow {
		assert((!retValue && !retCond) || !abortWitness);
		this.retValue = retValue;
		this.retCond = retCond;
		this.abortWitness = abortWitness;
	}

	static Result passes() scope @safe nothrow {
		return Result(RetValue.init, CondRet.init, null);
	}

	static Result returns(RetValue value) scope @safe nothrow {
		return Result(value, CondRet.init, null);
	}

	static Result conditionallyReturns(RetValue value,CondRet cond) scope @safe nothrow {
		return Result(value, cond, null);
	}

	static Result aborts(CReg witness) scope @safe nothrow {
		assert(witness);
		return Result(RetValue.init, CondRet.init, witness);
	}

	RetValue asValue(ScopeWriter sc, Expression type) {
		if(isAbort) return RetValue(sc.valError(abortWitness, type));
		assert(isReturn);
		return retValue;
	}

	void forgetCond(ScopeWriter sc) {
		assert(isConditionalReturn);
		retCond.forget(sc);
	}
}

abstract class IteResult {
	CondAny cond;

	void forgetCond(ScopeWriter sc) {
		if(!cond.isQuantum) return;
		sc.qcg.forget(cond.qreg);
	}
}

final class IteReturn: IteResult {
	RetValue value;

	this(CondAny cond, RetValue value) scope @safe nothrow {
		this.cond = cond;
		this.value = value;
	}
}

final class ItePass: IteResult {
	this(CondAny cond) scope @safe nothrow {
		this.cond = cond;
	}
}

final class IteAbort: IteResult {
	CReg witness;

	this(CondAny cond, CReg witness) scope @safe nothrow {
		this.cond = cond;
		this.witness = witness;
	}
}

final class ItePartialReturn: IteResult {
	RetValue value;
	CondRet retCond_;
	ScopeWriter scCont;

	this(CondAny cond, RetValue value, ScopeWriter scCont) scope @safe nothrow {
		this.cond = cond;
		this.value = value;
		this.scCont = scCont;
	}

	this(CondRet retCond, RetValue value, ScopeWriter scCont) scope @safe nothrow {
		this.retCond_ = retCond;
		this.value = value;
		this.scCont = scCont;
	}

	CondRet retCond() {
		assert(!cond || !retCond_);
		if(retCond_) {
			return retCond_;
		}
		return CondRet(cond);
	}

	override void forgetCond(ScopeWriter sc) {
		if(retCond_) {
			assert(!cond);
			retCond_.forget(sc);
		}else super.forgetCond(sc);
	}
}

final class ItePartialAbort: IteResult {
	CReg witness;
	ScopeWriter scCont;

	this(CondAny cond, CReg witness, ScopeWriter scCont) scope @safe nothrow {
		this.cond = cond;
		this.witness = witness;
		this.scCont = scCont;
	}

	override void forgetCond(ScopeWriter sc) {
		if(!cond.isQuantum) return;
		auto op = cond.value ? opDeallocQubit0 : opDeallocQubit1;
		sc.qcg.writeQOp(op, [], [], [], [cond.qreg]);
	}
}

class CCGen {
	this(CCGen parent, CodeWriter code, CondC[] condC) {
		this.parent = parent;
		this.code = code;
		this.condC = condC;
	}

	@property
	Writer ctx() {
		return code.ctx;
	}

	CCGen forSubfunc(CodeWriter subcode) {
		return new CCGen(this, subcode, []);
	}

	CCGen withCond(CReg reg, bool want) {
		// We'd also need to const-fold in split/merge.
		// if(reg is ctx.boolTrue && want) return this;
		// if(reg is ctx.boolFalse && !want) return this;

		return new CCGen(this, code, condC ~ [CondC(reg, want)]);
	}

	void writeCOp(string op, CReg[] cRet, CReg[] cArgs) {
		return code.writeOp(condC, null, op, cRet, [], cArgs, [], []);
	}

	CReg emitPureOp(string op, CReg[] args, scope void delegate(CCGen, CReg) onNew = null) {
		auto key = PureOpKey(op, args);
		for(auto cg = this; cg; cg = cg.parent) {
			if(auto p = key in cg.cachedPureOps) return *p;
		}
		auto r = new CReg();
		writeCOp(op, [r], args);
		cachedPureOps[key] = r;
		if(onNew) onNew(this, r);
		return r;
	}

	CReg boxCat(string tag, CReg n1, CReg r1, CReg n2, CReg r2) {
		if(n1 is ctx.intZero) return r2;
		if(n2 is ctx.intZero) return r1;
		if(!r1 && !r2) return null;
		return emitPureOp(format("box_cat[%s]", tag), [n1, r1, n2, r2]);
	}

	CReg boxPack(string tag, CReg[] items) {
		if(items.all!(r => !r)) return null;
		return emitPureOp(format("box[%s]", tag), items, (cg, r) {
			cg.cachedBoxItems[r] = items;
		});
	}

	CReg boxRepeat(string tag, CReg n, CReg val) {
		if(n is ctx.intZero) return boxPack(tag, []);
		if(!val) return null;
		if(auto p = ctx.asUnroll(n)) {
			return boxPack(tag, val.repeat(p.get()).array);
		}
		return emitPureOp(format("box_repeat[%s]", tag), [n, val], (cg, r) {
			cg.cachedBoxItems[r] = [val];
		});
	}

	CReg boxIndex(string boxTag, CReg len, CReg box, CReg ix) {
		if(!box) return null;
		for(auto cg = this; cg; cg = cg.parent) {
			if(auto p = box in cg.cachedBoxItems) {
				auto v = *p;
				if(v.length == 0) return null;
				if(v.length == 1) return v[0];
				if(auto ixBig = ix in ctx.intValue) {
					auto ixInt = ixBig.to!size_t();
					if(ixInt >= v.length) break;
					return v[ixInt];
				} else {
					break;
				}
			}
		}
		return emitPureOp(format("box_index[%s]", boxTag), [len, box, ix]);
	}

	CReg boxReplace(string boxTag, CReg len, CReg box, CReg ix, CReg val) {
		if(!box && !val) return null;
		return emitPureOp(format("box_replace[%s]", boxTag), [len, box, ix, val]);
	}

	CReg boxIndex(string boxTag, CReg len, CReg box, size_t ix) {
		return boxIndex(boxTag, len, box, ctx.literalInt(ix));
	}

	CReg boxIndex(string boxTag, size_t len, CReg box, size_t ix) {
		return boxIndex(boxTag, ctx.literalInt(len), box, ctx.literalInt(ix));
	}

	CReg[] boxUnpack(string boxTag, size_t n, CReg box) {
		auto r = new CReg[n];
		auto len = ctx.literalInt(n);
		foreach(i; iota(n)) {
			r[i] = boxIndex(boxTag, len, box, i);
		}
		return r;
	}

	CReg boxSlice(string boxTag, CReg len, CReg box, CReg ixL, CReg ixR) {
		if(!box || ixL == ixR) return null;
		return emitPureOp(format("box_slice[%s]", boxTag), [len, box, ixL, ixR]);
	}

	CReg funcPack(string name, CReg[] args) {
		if(args.all!(arg => ctx.isLiteral(arg))) {
			return ctx.literalFunc(name, args);
		}
		return emitPureOp(format("func[%s]", name), args);
	}

	CReg funcApply(string func, CReg[] args) {
		return emitPureOp(format("classical_call[%s]", func), args);
	}

	CReg funcApply(CReg func, CReg[] args) {
		return emitPureOp("classical_call", [func] ~ args);
	}

	CReg qtVector(CReg elt, CReg n) {
		assert(n);
		assert(elt);
		if(n is ctx.intZero || elt is ctx.qtUnit) {
			return ctx.qtUnit;
		}
		return emitPureOp("qt_vector", [n, elt]);
	}

	CReg qtTuple(CReg[] items) {
		size_t n = items.length;
		if(n == 0) {
			return ctx.qtUnit;
		}
		if(items.all!(t => t is items[0])) {
			return qtVector(items[0], ctx.literalInt(n));
		}
		return emitPureOp("qt_tuple", items);
	}

	CReg qtArray(CReg n, CReg elts) {
		assert(n);
		if(n is ctx.intZero) {
			return ctx.qtUnit;
		}
		return emitPureOp("qt_array", [n, elts]);
	}

	CReg qtSlice(CReg n, CReg elts, CReg i1, CReg i2) {
		assert(n);
		if(n is ctx.intZero || i1 is i2) {
			return ctx.qtUnit;
		}
		return qtArray(intSub(i2, i1), boxSlice(ctypeQtArray, n, elts, i1, i2));
	}

	CReg cond(CReg cond, CReg c0, CReg c1) {
		if(c0 is c1) return c0;
		if(cond is ctx.boolFalse) return c0;
		if(cond is ctx.boolTrue) return c1;
		return emitPureOp(opCond, [cond, c0, c1]);
	}

	CReg boolNot(CReg a) {
		if(a is ctx.boolTrue) return ctx.boolFalse;
		if(a is ctx.boolFalse) return ctx.boolTrue;
		return emitPureOp("bool_xor", [a, ctx.boolTrue]);
	}

	CReg boolEq(CReg a, CReg b) {
		if(a is ctx.boolTrue) return b;
		if(a is ctx.boolFalse) return boolNot(b);
		if(b is ctx.boolTrue) return a;
		if(b is ctx.boolFalse) return boolNot(a);
		return emitPureOp("bool_xor", [a, b, ctx.boolTrue]);
	}

	CReg boolNe(CReg a, CReg b) {
		if(a is ctx.boolTrue) return boolNot(b);
		if(a is ctx.boolFalse) return b;
		if(b is ctx.boolTrue) return boolNot(a);
		if(b is ctx.boolFalse) return a;
		return emitPureOp("bool_xor", [a, b]);
	}

	CReg intFromBool(CReg r) {
		return cond(r, ctx.intZero, ctx.intOne);
	}

	CReg intNeg(CReg r1) {
		if(auto p1 = r1 in ctx.intValue) {
			return ctx.literalInt(-*p1);
		}
		return emitPureOp("int_linear[0,-1]", [r1]);
	}

	CReg intAdd(CReg r1, CReg r2) {
		if(r1 is ctx.intZero) return r2;
		if(r2 is ctx.intZero) return r1;
		if(auto p1 = r1 in ctx.intValue) {
			if(auto p2 = r2 in ctx.intValue) {
				return ctx.literalInt(*p1 + *p2);
			}
			return emitPureOp(format("int_linear[%s,1]", (*p1).toDecimalString()), [r2]);
		} else if(auto p2 = r2 in ctx.intValue) {
			return emitPureOp(format("int_linear[%s,1]", (*p2).toDecimalString()), [r1]);
		}
		return emitPureOp("int_linear[0,1,1]", [r1, r2]);
	}

	CReg intSub(CReg r1, CReg r2) {
		if(r1 is ctx.intZero) return intNeg(r2);
		if(r2 is ctx.intZero) return r1;
		if(r1 is r2) return ctx.intZero;
		if(auto p1 = r1 in ctx.intValue) {
			if(auto p2 = r2 in ctx.intValue) {
				return ctx.literalInt(*p1 - *p2);
			}
			return emitPureOp(format("int_linear[%s,-1]", (*p1).toDecimalString()), [r2]);
		} else if(auto p2 = r2 in ctx.intValue) {
			return emitPureOp(format("int_linear[%s,1]", (-*p2).toDecimalString()), [r1]);
		}
		return emitPureOp("int_linear[0,1,-1]", [r1, r2]);
	}

	CReg intMod(CReg r1, CReg r2) {
		if(r1 is r2) return ctx.intZero;
		return emitPureOp("int_mod", [r1, r2]);
	}

	CReg intPow(CReg r1, CReg r2) {
		return emitPureOp("int_pow", [r1, r2]);
	}

	CReg intPow2(CReg r2) {
		return emitPureOp("int_pow", [ctx.intTwo, r2]);
	}

	CReg intBitAnd(CReg r1, CReg r2) {
		return emitPureOp("int_bit_and[-1]", [r1, r2]);
	}

	CReg intBitXor(CReg r1, CReg r2) {
		if(r1 is r2) return ctx.intZero;
		return emitPureOp("int_bit_xor[0]", [r1, r2]);
	}

	CReg intCmpEq(CReg r1, CReg r2) {
		if (r1 == r2) return ctx.boolTrue;
		if (ctx.isLiteral(r1) && ctx.isLiteral(r2)) return ctx.boolFalse;
		return emitPureOp("int_cmp_eq", [r1, r2]);
	}

	CReg intCmpNe(CReg r1, CReg r2) {
		return boolNot(intCmpEq(r1, r2));
	}

	CReg intCmpNe0(CReg r1) {
		return intCmpNe(r1, ctx.intZero);
	}

	CReg intCmpLt(CReg r1, CReg r2) {
		if (r1 == r2) return ctx.boolFalse;
		return emitPureOp("int_cmp_lt", [r1, r2]);
	}

	CReg intCmpLe(CReg r1, CReg r2) {
		return boolNot(intCmpLt(r2, r1));
	}

	CReg intMakeSigned(CReg bits, CReg val) {
		auto half = intPow2(intSub(bits, ctx.intOne));
		return intSub(intBitXor(half, val), half);
	}

	CReg floatFromBool(CReg r) {
		if(r is ctx.boolFalse) return ctx.floatZero;
		if(r is ctx.boolTrue) return ctx.floatOne;
		return emitPureOp("cond", [r, ctx.floatZero, ctx.floatOne]);
	}

	CReg floatFromInt(CReg r1) {
		return emitPureOp("float_from_int", [r1]);
	}

	CReg floatCmpEq(CReg r1, CReg r2) {
		if(r1 is r2) return ctx.boolTrue;
		return emitPureOp("float_cmp_eq", [r1, r2]);
	}

	CReg floatCmpEq0(CReg r1) {
		return floatCmpEq(r1, ctx.floatZero);
	}

	CReg floatCmpNe(CReg r1, CReg r2) {
		return boolNot(floatCmpEq(r1, r2));
	}

	CReg floatCmpNe0(CReg r1) {
		return floatCmpNe(r1, ctx.floatZero);
	}

	CReg floatCmpLt(CReg r1, CReg r2) {
		if(r1 is r2) return ctx.boolFalse;
		return emitPureOp("float_cmp_lt", [r1, r2]);
	}

	CReg intWrap(bool isSigned, CReg bits, CReg val) {
		val = intMod(val, intPow2(bits));
		if(isSigned) val = intMakeSigned(bits, val);
		return val;
	}

	CReg complexFromBool(CReg r) {
		return complexFromFloat(floatFromBool(r));
	}

	CReg complexFromInt(CReg r) {
		return complexFromFloat(floatFromInt(r));
	}

	CReg complexFromFloat(CReg r) {
		auto tup = boxPack(ctypeSilqTuple, [r, ctx.floatZero]);
		return emitPureOp("classical_call[primitive.complex.cfromri]", [tup]);
	}

	CReg qfuncPack(CReg func, CReg qtype) {
		return boxPack(ctypeSilqQFunc, [func, qtype]);
	}

	CReg qfuncInner(CReg r) {
		assert(r);
		return boxIndex(ctypeSilqQFunc, 2, r, 0);
	}

	CReg qfuncQType(CReg r) {
		assert(r);
		return boxIndex(ctypeSilqQFunc, 2, r, 1);
	}

	CReg getArrayLength(CReg r) {
		assert(r);
		return boxIndex(ctypeSilqArray, 2, r, 0);
	}

	CReg getArrayItems(CReg r) {
		return boxIndex(ctypeSilqArray, 2, r, 1);
	}

	void checkBool(bool isAssert, CReg val) {
		if(!isAssert) return;
		// at node.loc.line
		withCond(val, false).writeCOp(opAbort, [new CReg()], []);
	}

	void checkUnsigned(bool isAssert, CReg val) {
		if(auto p = val in ctx.intValue) {
			if(*p >= 0) return;
		}
		checkBool(isAssert, intCmpLe(ctx.intZero, val));
	}

	CReg checkEqInt(bool isAssert, CReg val1, CReg val2) {
		if(val1 is val2) return val1;
		checkBool(isAssert, intCmpEq(val1, val2));
		if(val1 in ctx.intValue) return val1;
		return val2;
	}

	void checkEqInt(bool isAssert, CReg val1, size_t val2) {
		checkEqInt(isAssert, val1, ctx.literalInt(val2));
	}

	void checkLeInt(bool isAssert, CReg val1, CReg val2) {
		checkBool(isAssert, intCmpLe(val1, val2));
	}

	void checkLtInt(bool isAssert, CReg val1, CReg val2) {
		checkBool(isAssert, intCmpLt(val1, val2));
	}

	CReg assumeEqual(CReg val1, CReg val2) {
		if (val1 is val2) return val1;
		// TODO emit assertion?
		if (val2 in ctx.literalValue) return val2;
		return val1;
	}


private:
	CCGen parent;
	CodeWriter code;
	CondC[] condC;
	CReg[PureOpKey] cachedPureOps;
	CReg[][CReg] cachedBoxItems;
}

class QCGen {
	CCGen ccg;
	CondQ[] condQ;
	bool inType;

	this(CCGen ccg, CondQ[] condQ) {
		this.ccg = ccg;
		this.condQ = condQ;
		this.inType = false;
	}

	@property
	Writer ctx() {
		return ccg.ctx;
	}

	QCGen withCond(CondAny cond) {
		CondQ[] condQ = this.condQ;
		CCGen ccg = this.ccg;
		if(cond.isQuantum) {
			if(inType) return this;
			condQ = condQ ~ [cond.qcond()];
		} else {
			ccg = ccg.withCond(cond.creg, cond.value);
		}
		auto r = new QCGen(ccg, condQ);
		r.inType = inType;
		return r;
	}

	QReg[] fixQcNull(QReg[] regs) {
		if(regs.all!(r => !!r)) return regs;
		regs = regs.array;
		foreach(ref r; regs) {
			if(!r) r = ccg.code.qregU;
		}
		return regs;
	}

	QReg[] fixQiNull(QReg[] regs) {
		if(regs.all!(r => !!r)) return regs;
		regs = regs.array;
		foreach(ref r; regs) {
			if(r) continue;
			r = new QReg();
			allocUnit(r);
		}
		return regs;
	}

	QReg[] fixQrNull(QReg[] regs, out QReg[] toDealloc) {
		size_t n = regs.count!(r => !r);
		if(n == 0) return regs;
		toDealloc = new QReg[n];
		regs = regs.array;
		size_t i = 0;
		foreach(ref r; regs) {
			if(!r) r = toDealloc[i++] = new QReg();
		}
		assert(i == n);
		return regs;
	}

	void writeQOp(string op, QReg[] qRet, CReg[] cArgs, QReg[] qcArgs, QReg[] qiArgs) {
		if(inType) return;
		QReg[] toDealloc;
		qRet = fixQrNull(qRet, toDealloc);
		qcArgs = fixQcNull(qcArgs);
		qiArgs = fixQiNull(qiArgs);
		ccg.code.writeOp(ccg.condC, condQ, op, [], qRet, cArgs, qcArgs, qiArgs);
		foreach(r; toDealloc) deallocUnit(r);
	}

	void writeMOp(string op, CReg[] cRet, QReg[] qRet, CReg[] cArgs, QReg[] qcArgs, QReg[] qiArgs) {
		assert(!inType, "measurement in quantum-disabled mode");
		assert(condQ.length == 0, "mixed classical/quantum operation in quantum-conditional context");
		QReg[] toDealloc;
		qRet = fixQrNull(qRet, toDealloc);
		qcArgs = fixQcNull(qcArgs);
		qiArgs = fixQiNull(qiArgs);
		ccg.code.writeOp(ccg.condC, null, op, cRet, qRet, cArgs, qcArgs, qiArgs);
		foreach(r; toDealloc) deallocUnit(r);
	}

	void allocUnit(QReg r) {
		if(!r) return;
		if(inType) return;
		ccg.code.writeOp(ccg.condC, condQ, opAllocUnit, [], [r], [], [], []);
	}

	void deallocUnit(QReg r) {
		if(!r) return;
		if(inType) return;
		ccg.code.writeOp(ccg.condC, condQ, opDeallocUnit, [], [], [], [], [r]);
	}

	QReg dup(QReg r) {
		auto r2 = new QReg();
		writeQOp(opDup, [r2], [], [r], []);
		return r2;
	}

	void allocError(QReg r) {
		writeQOp(opAllocError, [r], [], [], []);
	}

	void deallocError(QReg r) {
		writeQOp(opDeallocError, [], [], [], [r]);
	}

	QReg allocUnit() {
		auto r = new QReg();
		allocUnit(r);
		return r;
	}

	QReg allocQubit(bool v) {
		auto r = new QReg();
		writeQOp(v ? opAllocQubit1 : opAllocQubit0, [r], [], [], []);
		return r;
	}

	void deallocQubit(QReg r, bool v) {
		assert(r);
		writeQOp(v ? opDeallocQubit1 : opDeallocQubit0, [], [], [], [r]);
	}

	QReg allocQubit(CReg v) {
		assert(v);
		if(v is ctx.boolFalse) return allocQubit(false);
		if(v is ctx.boolTrue) return allocQubit(true);
		auto r0 = new QReg();
		auto r1 = new QReg();
		auto r = new QReg();
		ccg.code.writeOp(ccg.condC ~ [CondC(v, false)], condQ, opAllocQubit0, [], [r0], [], [], []);
		ccg.code.writeOp(ccg.condC ~ [CondC(v, true)], condQ, opAllocQubit1, [], [r1], [], [], []);
		writeQOp(opCMerge, [r], [v], [], [r0, r1]);
		return r;
	}

	void deallocQubit(QReg r, CReg v) {
		assert(r);
		assert(v);
		if(v is ctx.boolFalse) return deallocQubit(r, false);
		if(v is ctx.boolTrue) return deallocQubit(r, true);
		auto r0 = new QReg();
		auto r1 = new QReg();
		writeQOp(opCSplit, [r0, r1], [v], [], [r]);
		ccg.code.writeOp(ccg.condC ~ [CondC(v, false)], condQ, opDeallocQubit0, [], [r0], [], [], []);
		ccg.code.writeOp(ccg.condC ~ [CondC(v, true)], condQ, opDeallocQubit1, [], [r1], [], [], []);
	}

	QReg allocError() {
		auto r = new QReg();
		allocError(r);
		return r;
	}

	QReg allocDummy(CReg qt) {
		if(qt is ctx.qtUnit) return null;
		auto qr = new QReg();
		auto cv = ccg.emitPureOp("qt_dummy", [qt]);
		writeQOp(opAllocBitvec, [qr], [qt, cv], [], []);
		return qr;
	}

	void deallocDummy(CReg qt, QReg qr) {
		if(qt is ctx.qtUnit) return deallocUnit(qr);
		auto cv = ccg.emitPureOp("qt_dummy", [qt]);
		writeQOp(opDeallocBitvec, [], [qt, cv], [], [qr]);
	}

	void forget(QReg r) {
		if(!r) return;
		writeQOp(opForget, [], [], [], [r]);
	}

	void forget(QReg[] rs) {
		foreach(r; rs) {
			if(r) writeQOp(opForget, [], [], [], [r]);
		}
	}

	QReg concat(CReg n1, CReg t1, QReg q1, CReg n2, CReg t2, QReg q2) {
		assert(t1);
		assert(t2);
		if(q1 && t1 == ctx.qtUnit) {
			deallocUnit(q1);
			q1 = null;
		}
		if(q2 && t2 == ctx.qtUnit) {
			deallocUnit(q2);
			q2 = null;
		}
		if(!q1 && !q2) return null;
		if(!q1) return q2;
		if(!q2) return q1;
		auto r = new QReg();
		writeQOp(opCat, [r], [n1, t1, n2, t2], [], [q1, q2]);
		return r;
	}

	QReg pack(CReg[] qtypes, QReg[] qregs) {
		size_t n = qtypes.length;
		assert(qregs.length == n);
		if(qtypes.all!(t => t is ctx.qtUnit)) {
			foreach(r; qregs) {
				if(r) deallocUnit(r);
			}
			return null;
		}
		auto r = new QReg();
		writeQOp(opPack(n), [r], qtypes, [], qregs);
		return r;
	}

	QReg cat(CReg len, CReg qtypes, CReg[] slices, QReg[] qrs) {
		assert(qrs.length == slices.length);

		size_t i = slices.length - 1;
		auto qr = qrs[i];
		CReg rightLen = slices[i];
		while (i--) {
			auto subLen = slices[i];
			if (subLen is ctx.intZero) {
				deallocUnit(qrs[i]);
				continue;
			}
			auto leftLen = ccg.intAdd(subLen, rightLen);
			auto leftOff = ccg.intSub(len, leftLen);
			auto rightOff = ccg.intSub(len, rightLen);
			auto qt0 = ccg.qtSlice(len, qtypes, leftOff, rightOff);
			auto qt1 = ccg.qtSlice(len, qtypes, rightOff, len);
			auto qrc = new QReg();
			writeQOp(opCat, [qrc], [subLen, qt0, rightLen, qt1], [], [qrs[i], qr]);
			qr = qrc;
			rightLen = leftLen;
		}

		return qr;
	}

	QReg[] uncat(CReg len, CReg qtypes, CReg[] slices, QReg qr) {
		auto qrs = appender!(QReg[]);

		CReg leftOff = ctx.intZero;
		for (size_t i = 0; i < slices.length - 1; i++) {
			auto subLen = slices[i];
			if (subLen is ctx.intZero) {
				qrs.put(allocUnit());
				continue;
			}
			auto rightOff = ccg.intAdd(leftOff, subLen);
			auto rightLen = ccg.intSub(len, rightOff);
			auto qt0 = ccg.qtSlice(len, qtypes, leftOff, rightOff);
			auto qt1 = ccg.qtSlice(len, qtypes, rightOff, len);
			auto qr0 = new QReg();
			auto qr1 = new QReg();
			writeQOp(opUncat, [qr0, qr1], [subLen, qt0, rightLen, qt1], [], [qr]);
			qrs.put(qr0);
			qr = qr1;
			leftOff = rightOff;
		}
		qrs.put(qr);

		return qrs[];
	}

	void pack(QReg tup, CReg[] qtypes, QReg[] qregs) {
		size_t n = qtypes.length;
		assert(qregs.length == n);
		if(!tup || qtypes.all!(t => t is ctx.qtUnit)) {
			foreach(r; qregs) {
				if(r) deallocUnit(r);
			}
			if(tup) allocUnit(tup);
			return;
		}
		writeQOp(opPack(n), [tup], qtypes, [], qregs);
	}
}

struct ArgInfo {
	Expression ty;
	Expression expr;
	Value val;
	bool isConst;
}

struct CallInfo {
	Value target;
	FunctionInfo targetF;
	bool isTuple, hasQuantum, captureMoved;
	Expression retType;
	bool makeClassical;
	ast_exp.Annotation effect;
	ArgInfo[] args;
}

struct Variable {
	ast_decl.Declaration decl;
	Value value;
}

struct Dummy {
	Expression type;
	CReg creg;
	CReg qtype;
}

struct DummyTypes {
	Expression type;
	DummyTypes[] next;
}

struct Borrow {
	ast_decl.VarDecl var;
	CReg[] indices;
	Dummy dummy;
	DummyTypes[] dummyTypes;
}

class BorrowScope {
	bool isItrans;
	Borrow[Id] borrows;
}

struct IndexChain {
	ast_exp.Identifier base;
	ast_exp.IndexExp[] ie;

	this(ast_exp.IndexExp at) {
		auto indicesE = appender!(ast_exp.IndexExp[]);
		while(true) {
			indicesE.put(at);
			auto next = cast(ast_exp.IndexExp) at.e;
			if(!next) break;
			at = next;
		}
		base = cast(ast_exp.Identifier) at.e;
		assert(base, format("IndexExp(byRef=true) base not Identifier: %s %s", typeid(at.e).name, at.e));
		ie = indicesE[];
		reverse(ie);
	}
}

class ScopeWriter {
	this(ast_decl.FunctionDef fd, Writer ctx) {
		this.nscope = fd.fscope_;
		this.bscope = null;
		this.parent = null;
		this.qcg = new QCGen(new CCGen(null, new CodeWriter(ctx), []), []);
		this.detPassthrough = true;
	}

	this(ast_scope.NestedScope nscope, ScopeWriter parent) {
		this.nscope = nscope;
		this.bscope = null;
		this.parent = parent;
		this.qcg = parent.qcg;
		this.detPassthrough = true;
	}

	ScopeWriter withBlock(ast_scope.NestedScope nscope) {
		auto sc = new ScopeWriter(nscope, this);
		sc.bscope = bscope;
		return sc;
	}

	ScopeWriter withCond(ast_scope.NestedScope nscope, CondAny cond) {
		auto sc = withBlock(nscope);
		sc.qcg = qcg.withCond(cond);
		if(cond.isClassical) sc.detPassthrough = false;
		return sc;
	}

	ScopeWriter typeScope() {
		auto subsc = new ScopeWriter(null, this);
		subsc.qcg = new QCGen(ccg, null);
		subsc.qcg.inType = true;
		return subsc;
	}

	ScopeWriter subfuncScope(bool detPassthrough) {
		auto subcode = new CodeWriter(ctx, ccg.code);
		auto subsc = new ScopeWriter(nscope, this);
		subsc.qcg = new QCGen(ccg.forSubfunc(subcode), []);
		subsc.detPassthrough = detPassthrough;
		return subsc;
	}

	ScopeWriter evalScope(ExprInfo ei) {
		if(!parent) return this;
		auto expr = ei.expr;
		bool total = expr.isTotal();
		if(!total && !detPassthrough) return this;

		IdSet ids;
		foreach(var; expr.freeVars) {
			ids[var.id] = unit;
		}
		auto sc = this;
		while(true) {
			if(ids.byKey().any!(id => id in sc.vars)) break;
			auto par = sc.parent;
			if(!par) break;
			if(!total && !sc.detPassthrough) break;
			sc = par;
		}
		return sc;
	}

	@property
	CCGen ccg() {
		return qcg.ccg;
	}

	@property
	Writer ctx() {
		return qcg.ctx;
	}

	Value valNewC(CReg creg) {
		return Value.newReg(creg, null);
	}

	Value valNewQ(CReg creg, QReg qreg) {
		return Value.newReg(creg, qreg);
	}

	Value valNewQ(CReg creg, Expression ty) {
		if(!typeHasClassical(ty)) creg = null;
		QReg qreg = null;
		if(typeHasQuantum(ty)) qreg = new QReg();
		return valNewQ(creg, qreg);
	}

	Value valNewQ(Expression ty) {
		CReg creg = null;
		if(typeHasClassical(ty)) creg = new CReg();
		QReg qreg = null;
		if(typeHasQuantum(ty)) qreg = new QReg();
		return valNewQ(creg, qreg);
	}

	Value valNewQt(CReg creg, CReg qtype) {
		assert(qtype);
		QReg qreg;
		if(qtype != ctx.qtUnit) qreg = new QReg();
		return Value.newReg(creg, qreg);
	}

	Value valAllocQubit(bool v) {
		return valNewQ(null, qcg.allocQubit(v));
	}

	Value valAllocQubit(CReg r) {
		return valNewQ(null, qcg.allocQubit(r));
	}

	Value valDup(Value v) {
		if(!v.hasQuantum) return v;
		return valNewQ(v.creg, qcg.dup(v.qreg));
	}

	void valUndup(Value v, Value v2) {
		if(v.hasClassical || v2.hasClassical) {
			ccg.assumeEqual(v2.creg, v.creg);
		}
		if(!v.hasQuantum) return;
		if(!v2.hasQuantum) {
			qcg.deallocUnit(v.qreg);
			return;
		}
		qcg.writeQOp(opUndup, [], [], [v2.qreg], [v.qreg]);
	}

	void valForget(Value v) {
		if(!v.hasQuantum) return;
		qcg.forget(v.qreg);
	}

	void valForget(Value[] vs) {
		foreach(v; vs) {
			if(v) valForget(v);
		}
	}

	void valDeallocError(Value v) {
		if(!v.hasQuantum) return;
		qcg.deallocError(v.qreg);
	}

	void valSplit(CondAny cond, ref Value v0, ref Value v1, Value v) {
		if(!v.hasQuantum) {
			v0 = v;
			v1 = v;
			return;
		}
		QReg r0 = null, r1 = null;
		if(v.hasQuantum) {
			r0 = new QReg();
			r1 = new QReg();
			if(cond.isClassical) {
				qcg.writeQOp(opCSplit, [r0, r1], [cond.creg], [], [v.qreg]);
			} else {
				qcg.writeQOp(opQSplit, [r0, r1], [], [cond.qreg], [v.qreg]);
			}
			if(!cond.value) {
				swap(r0, r1);
			}
		}
		v0 = valNewQ(v.creg, r0);
		v1 = valNewQ(v.creg, r1);
	}

	Value valMerge(CondAny cond, Value v0, Value v1) {
		assert(cond.isQuantum?!!cond.qreg:!!cond.creg);
		CReg creg = null;
		if(v0.creg || v1.creg) {
			assert(cond.isClassical);
			CReg c0 = v0.creg;
			CReg c1 = v1.creg;
			if(!cond.value) swap(c0, c1);
			creg = ccg.cond(cond.creg, c0, c1);
		}
		QReg qreg;
		if(!v0.hasQuantum && !v1.hasQuantum || cond.isQuantum && (!v0.hasQuantum || !v1.hasQuantum)) {
			qreg = null;
			if(v0.hasQuantum) qcg.withCond(cond.invert()).deallocUnit(v0.qreg);
			if(v1.hasQuantum) qcg.withCond(cond).deallocUnit(v1.qreg);
		} else {
			qreg = new QReg();
			QReg if0 = v0.qreg;
			QReg if1 = v1.qreg;
			if(cond.isClassical) {
				if(!if0) if0 = qcg.withCond(cond.invert()).allocUnit();
				if(!if1) if1 = qcg.withCond(cond).allocUnit();
				if(!cond.value) swap(if0, if1);
				qcg.writeQOp(opCMerge, [qreg], [cond.creg], [], [if0, if1]);
			} else {
				assert(if0);
				assert(if1);
				if(!cond.value) swap(if0, if1);
				qcg.writeQOp(opQMerge, [qreg], [], [cond.qreg], [if0, if1]);
			}
		}
		return valNewQ(creg, qreg);
	}

	Value valArrayCat(Expression itemTy, Value lhs, Value rhs) {
		CReg lhsLen = ccg.getArrayLength(lhs.creg);
		CReg rhsLen = ccg.getArrayLength(rhs.creg);

		CReg lhsItems, rhsItems, rItems;
		if(typeHasClassical(itemTy)) {
			lhsItems = ccg.getArrayItems(lhs.creg);
			rhsItems = ccg.getArrayItems(rhs.creg);
			rItems = ccg.boxCat(ctypeSilqTuple, lhsLen, lhsItems, rhsLen, rhsItems);
		}

		CReg rLen = ccg.intAdd(lhsLen, rhsLen);
		CReg rArray = ccg.boxPack(ctypeSilqArray, [rLen, rItems]);

		QReg qr;
		auto lhsQt = getVectorQType(itemTy, lhsLen, lhsItems);
		auto rhsQt = getVectorQType(itemTy, rhsLen, rhsItems);
		if(lhsQt != ctx.qtUnit || rhsQt != ctx.qtUnit) {
			assert(typeHasQuantum(itemTy));
			qr = qcg.concat(lhsLen, lhsQt, lhs.qreg, rhsLen, rhsQt, rhs.qreg);
		} else {
			qr = null;
		}
		return valNewQ(rArray, qr);
	}

	void valVectorUncat(out Value lhs, out Value rhs, Expression itemTy, CReg lhsLen, CReg rhsLen, CReg totLen, Value val) {
		CReg lhsC = null, rhsC = null;
		if(typeHasClassical(itemTy)) {
			lhsC = ccg.boxSlice(ctypeSilqTuple, totLen, val.creg, ctx.intZero, lhsLen);
			rhsC = ccg.boxSlice(ctypeSilqTuple, totLen, val.creg, lhsLen, totLen);
		}

		CReg lhsQt, rhsQt;
		if(typeHasQuantum(itemTy) && val.hasQuantum) {
			lhsQt = getVectorQType(itemTy, lhsLen, lhsC);
			rhsQt = getVectorQType(itemTy, rhsLen, rhsC);
		} else {
			lhsQt = ctx.qtUnit;
			rhsQt = ctx.qtUnit;
		}
		lhs = valNewQt(lhsC, lhsQt);
		rhs = valNewQt(rhsC, rhsQt);
		if(typeHasQuantum(itemTy) && val.hasQuantum) {
			qcg.writeQOp(opUncat, [lhs.qreg, rhs.qreg], [lhsLen, lhsQt, rhsLen, rhsQt], [], [val.qreg]);
		}
	}

	Value valPack(Expression[] types, Value[] rhs) {
		assert(types.length == rhs.length);
		auto qtypes = iota(types.length).map!(i => getQType(types[i], rhs[i])).array;
		CReg clhs = ccg.boxPack(ctypeSilqTuple, rhs.map!(r => r.creg).array);
		QReg qr = null;
		if(qtypes.all!(qt => qt is ctx.qtUnit)) {
			foreach(v; rhs) {
				if(v.hasQuantum) qcg.deallocUnit(v.qreg);
			}
		} else {
			qr = qcg.pack(qtypes, rhs.map!(r => r.qreg).array);
		}
		return valNewQ(clhs, qr);
	}

	Value[] valUnpack(Expression[] types, Value rhs) {
		size_t n = types.length;
		// `rhs.type` could be a vector
		auto res = new Value[n];

		for(size_t i = 0; i < n; i++) {
			CReg cres = null;
			if(typeHasClassical(types[i])) {
				cres = ccg.boxIndex(ctypeSilqTuple, n, rhs.creg, i);
			}
			res[i] = valNewQ(cres, types[i]);
		}

		if(res.any!(e => e.hasQuantum)) {
			auto qres = res.map!(e => e.qreg).array;
			auto qtypes = iota(n).map!(i => getQType(types[i], res[i])).array;
			qcg.writeQOp(opUnpack(res.length), qres, qtypes, [], [rhs.qreg]);
		} else if(rhs.hasQuantum) {
			qcg.deallocUnit(rhs.qreg);
			// assert(0, format("unpacking quantum value produced no quantum results; types: %s", types));
		}
		return cast(Value[]) res;
	}

	Value valVectorToArray(CReg n, Value v) {
		// Convert `a: T^n` into `T[]`
		return valNewQ(ccg.boxPack(ctypeSilqArray, [n, v.creg]), v.qreg);
	}

	Value valArrayToVector(ast_ty.Expression innerTy, ref CReg len, Value v) {
		len = ccg.getArrayLength(v.creg);
		auto creg = typeHasClassical(innerTy) ? ccg.getArrayItems(v.creg) : null;
		return valNewQ(creg, v.qreg);
	}

	void debugVar(ast_decl.Declaration d, Value v) {
		ast_decl.FunctionDef varFunc = d.scope_.getFunction();
		int capLevel = 0;
		for(ast_decl.FunctionDef curFunc = nscope.getFunction(); curFunc !is varFunc; curFunc = curFunc.scope_.getFunction()) {
			capLevel += 1;
		}

		int param = -1;
		if(cast(ast_decl.Parameter) d) {
			auto fsc = cast(ast_scope.FunctionScope) d.scope_;
			assert(fsc);
			assert(fsc.fd is varFunc);
			foreach(i, p; varFunc.params) {
				if(p is d) param = cast(int) i;
			}
			assert(param >= 0);
		}
		ccg.code.vars.put(IrVariable(d, v, ctx.curLoc.loc, capLevel, param));
	}

	void defineVar(ast_decl.Declaration d, Value v) {
		v.setName(d.name);
		auto name = d.getId;
		assert(d.scope_ is nscope, format("Scope violation for %s", name.str));
		auto p = name in vars;
		assert(!p || p.value is null, format("Duplicate definition: %s", name.str));
		vars[name] = Variable(d, v);
		debugVar(d, v);
	}

	Value defineParam(ast_decl.Parameter d) {
		auto v = valNewQ(typeForDecl(d));
		defineVar(d, v);
		return v;
	}

	Value defineCapture(ast_decl.Declaration d) {
		auto v = valNewQ(typeForDecl(d));
		v.setName(d.name);
		auto name = d.getId;
		auto p = name in vars;
		assert(!p || p.value is null, format("Duplicate definition: %s", name.str));
		vars[name] = Variable(d, v);
		debugVar(d, v);
		return v;
	}

	Value getVar(ast_decl.Declaration decl, bool isDup, bool strictDecl = true) {
		assert(decl);
		auto name = decl.getId;
		Value v;
		auto p = name in vars;
		if(!isDup) {
			if(!p) {
				for(auto sc = parent; sc; sc = sc.parent) {
					assert(name !in sc.vars, format("Variable %s not split from parent scope", name.str));
				}
				assert(0, format("Variable %s not available at moved use", name.str));
			}
		} else {
			auto cur = this;
			while(!p) {
				assert(cur.parent, format("Variable %s not available at const use", name.str));
				cur = cur.parent;
				p = name in cur.vars;
			}
			assert(cur.ccg.code is this.ccg.code || !typeHasQuantum(typeForDecl(decl)), format("Variable %s used in subfunction has quantum component", name.str));
		}
		assert(p.value, format("Variable %s used after being consumed", name.str));
		v = p.value;
		if(isDup) {
			v = valDup(v);
		} else {
			p.value = null;
		}
		if (p.decl !is decl) {
			assert(!strictDecl || (isDup && p.decl.isSplitFrom(decl)), format("Variable %s declaration mismatch at %s use; found %s, expected %s\n", name.str, isDup ? "const" : "moved", p.decl.loc, decl.loc));
			assert(typeForDecl(p.decl) == typeForDecl(decl), "Split const decl changed type");
		}
		return v;
	}

	Borrow *defineBorrow(ast_decl.Identifier id, CReg[] indices) {
		auto vd = cast(ast_decl.VarDecl) id.meaning;
		assert(vd);
		assert(bscope);
		assert(!bscope.isItrans);

		assert(id.id !in bscope.borrows);
		bscope.borrows[id.id] = Borrow(vd, indices);
		auto b = id.id in bscope.borrows;
		assert(b);
		return b;
	}

	Value getBorrow(ast_exp.Identifier id, ref Borrow b) {
		auto vd = cast(ast_decl.VarDecl) id.meaning;
		assert(vd);
		Value v = getVar(vd, false);

		assert(bscope);
		assert(bscope.isItrans);
		auto p = id.id in bscope.borrows;
		assert(p);
		b = *p;
		bscope.borrows.remove(id.id);
		return v;
	}

	Value getRawVar(Id name) {
		auto cur = this;
		auto p = name in vars;
		while(!p) {
			cur = cur.parent;
			assert(cur, format("Variable %s not available at const use", name.str));
			p = name in cur.vars;
		}
		Value v = p.value;
		assert(v, format("Variable %s used after being consumed", name.str));
		return valDup(v);
	}

	Value getFunc(ast_decl.FunctionDef fd, bool isDup, ast_exp.Identifier[] recaptures) {
		auto fi = ctx.getFunctionInfo(fd);
		auto caps = new Value[fi.captures.length];
		foreach(i, cap; fi.captures) {
			bool keep = isDup || cap.innerDecl is cap.outerDecl;
			bool strict = true;
			ast_decl.Declaration outer = cap.outerDecl;
			if (recaptures) {
				strict = false;
			}
			Value v = getVar(cap.outerDecl, keep, strict);
			v = genSubtype(v, typeForDecl(cap.innerDecl), typeForDecl(cap.innerDecl));
			caps[i] = v;
		}
		return Value.newFunction(this, fi, caps);
	}

	void checkEmpty(bool isAbort) {
		foreach(name, ref var; vars) {
			if(!var.value) continue;
			if(!var.value.hasQuantum) continue;
			assert(isAbort, format("variable %s not consumed", name.str));
			qcg.deallocError(var.value.qreg);
			var.value = null;
		}
	}

	Value valError(CReg cr, Expression ty) {
		QReg qr;
		if(typeHasQuantum(ty)) qr = qcg.allocError();
		if(!typeHasClassical(ty)) cr = null;
		return valNewQ(cr, qr);
	}

	Value valAbort(Expression ty) {
		auto r = new CReg();
		ccg.writeCOp(opAbort, [r], []);
		return valError(r, ty);
	}

	CondAny genCond(Expression e) {
		CondAny cond;
		auto c = genExpr(e);
		if(e.type is ast_ty.Bool(true)) {
			assert(c.creg);
			return CondAny(c.creg);
		} else if(e.type is ast_ty.Bool(false)) {
			assert(!c.creg);
			return CondAny(c.qreg);
		} else {
			assert(0, format("bad boolean type: %s", e.type));
		}
	}

	void genSplit(CondAny cond, ref ScopeWriter if0, ast_scope.NestedScope sc0, ref ScopeWriter if1, ast_scope.NestedScope sc1) {
		if(!sc0 && !sc1) {
			if0 = withCond(null, cond.invert());
			if1 = withCond(null, cond);
			return;
		}

		assert(sc0);
		assert(!nscope || sc0.parent is nscope);
		assert(sc1);
		assert(!nscope || sc1.parent is nscope);

		if0 = withCond(sc0, cond.invert());
		if1 = withCond(sc1, cond);

		struct Triple {
			ast_decl.Declaration outer, d0, d1;
		}
		IdMap!Triple splitVars;
		foreach(decl; sc1.splitVars) {
			assert(decl.scope_ is sc1);
			auto outer = decl.splitFrom;
			assert(outer.scope_ is nscope);
			splitVars[outer.getId] = Triple(outer, null, decl);
		}
		foreach(decl; sc0.splitVars) {
			assert(decl.scope_ is sc0);
			auto id = decl.splitFrom.getId;
			Triple* t = id in splitVars;
			assert(t, format("Split variable %s missing in if-true", id.str));
			assert(decl.splitFrom is t.outer, format("Split variable %s splitFrom scope mismatch", id));
			t.d0 = decl;
		}

		foreach(id, t; splitVars) {
			assert(t.d0, format("Split variable %s missing in if-false", id));
			auto d1 = t.d1;
			auto d0 = t.d0;
			auto vtype = typeForDecl(t.outer);
			assert(typeForDecl(d1) == vtype, format("Split variable %s changed type in if-true", id));
			assert(typeForDecl(d0) == vtype, format("Split variable %s changed type in if-false", id));
			auto v = getVar(t.outer, false);
			Value v0, v1;
			valSplit(cond, v0, v1, v);
			if1.defineVar(d1, v1);
			if0.defineVar(d0, v0);
		}

		// Make sure the merged types are evaluated in the outer scope.
		foreach(decl; sc1.mergedVars ~ sc0.mergedVars) {
			auto ty = typeForDecl(decl.mergedInto);
			pinType(ty);
		}
	}

	void genMerge(CondAny cond, ScopeWriter if0, ScopeWriter if1) {
		auto sc0 = if0.nscope;
		auto sc1 = if1.nscope;

		struct Triple {
			ast_decl.Declaration outer, d0, d1;
		}
		IdMap!Triple mergedVars;
		foreach(decl; sc1.mergedVars) {
			mergedVars[decl.mergedInto.getId] = Triple(decl.mergedInto, null, decl);
		}
		foreach(decl; sc0.mergedVars) {
			auto id = decl.mergedInto.getId;
			auto t = id in mergedVars;
			assert(t, format("Merged variable %s missing in if-true", id));
			assert(decl.mergedInto is t.outer, format("Merged variable %s splitFrom mismatch", id));
			t.d0 = decl;
		}

		foreach(id, t; mergedVars) {
			assert(t.d0, format("Merged variable %s missing in if-false", id));
			auto outer = t.outer;
			// TODO types as part of merge result?
			auto ty = typeForDecl(outer);
			auto r1 = if1.genSubtype(if1.getVar(t.d1, false), typeForDecl(t.d1), ty);
			auto r0 = if0.genSubtype(if0.getVar(t.d0, false), typeForDecl(t.d0), ty);
			auto val = valMerge(cond, r0, r1);
			defineVar(outer, val);
		}
	}

	Value genCompoundValue(ast_exp.CompoundExp e, ast_exp.Expression fin, Expression ty) {
		assert(e.blscope_ is null || e.blscope_ is nscope);
		assert(e.s.length > 0);

		if(e.blscope_) {
			foreach(decl; e.blscope_.forgottenVarsOnEntry) {
				valForget(getVar(decl, false));
			}
		}

		Expression[] stmts = e.s;
		if (!fin) {
			fin = stmts[$-1];
			stmts = stmts[0..$-1];
		}

		foreach(stmt; stmts) {
			Result r = genStmt(stmt);
			if(r.isAbort) return valError(r.abortWitness, e.type);
			assert(!r.isReturn && !r.isConditionalReturn, "early return in compound expression");
		}
		auto r = genExprAs(fin, ty);
		if(e.blscope_) {
			scope loc = PushLocation(ctx, locEnd(e.loc));
			foreach(decl; e.blscope_.forgottenVars) {
				valForget(getVar(decl, false));
			}
		}
		return r;
	}

	Value genExprAs(Expression e, Expression ty) {
		assert(ty, "genExprAs(_, null)");
		auto v = genExpr(e);
		try {
			return genSubtype(v, e.type, ty);
		} catch(AssertError exc) {
			exc.msg = format("%s\nin conversion: %s -> %s", exc.msg, e.type, ty);
			throw exc;
		}
	}

	Value genExpr(Expression e) {
		assert(e, "genExpr(null)");
		Value r;
		try {
			r = genValue(e);
		} catch(AssertError exc) {
			exc.msg = format("%s\nat %s, expression: %s", exc.msg, e.loc, e);
			throw exc;
		}
		if (ast_ty.isEmpty(e.type)) {
			assert(!r.hasQuantum, "quantum component in diverging expression");
			assert(r.hasClassical, "missing classical component in diverging expression");
		} else {
			assert(!r.hasClassical || typeHasClassical(e.type), format("got a classical component in value of type %s: %s", e.type, e));
			assert(!r.hasQuantum || typeHasQuantum(e.type), format("got a quantum component in value of type %s: %s", e.type, e));
		}
		return r;
	}

	Value genValue(Expression e) {
		assert(e, "genValue(null)");
		scope loc = PushLocation(ctx, e.loc);
		return ast_exp.dispatchExp!((auto ref e){
			Value r = this.implExpr(e);
			assert(r);
			return r;
		})(e);
	}

	Value implExpr(ast_exp.Identifier e) {
		final switch(ast_sem.isBuiltIn(e)) {
			case ast_sem.BuiltIn.none:
				break;
			case ast_sem.BuiltIn.pi:
				return valNewC(ctx.floatPi);
			case ast_sem.BuiltIn.show:
			case ast_sem.BuiltIn.query:
				assert(0, "Built-in %s cannot be used as first-class value");
		}

		if(auto init=e.getInitializer()) {
			return genExprAs(init, e.type);
		}
		if(e.classical) {
			auto r = getSimpleRTTI(e);
			assert(r);
			return valNewC(r.packed);
		}

		auto decl = e.meaning;
		if(!decl) {
			assert(e.constLookup || e.implicitDup);
			return getRawVar(e.id);
		}

		auto dty = typeForDecl(decl);
		assert(e.type == dty, format("Different types: %s != %s", e.type, dty));

		bool isDup = e.constLookup || e.implicitDup;

		if(auto dd = cast(ast_decl.DatDecl) decl) {
			auto fd = dd.toFunctionDef();
			decl = fd;
		}

		if(auto fd = cast(ast_decl.FunctionDef) decl) {
			if(!fd.scope_.getFunction()) {
				// global function
				return getFunc(fd, true, null);
			}
			if(nscope.isNestedIn(fd.fscope_)) {
				// recursive closure
				assert(decl.getId !in vars, format("Recursive closure %s also visible as variable", decl));
				return getFunc(fd, isDup, e.recaptures);
			}
		}

		return getVar(decl, isDup);
	}

	Value implExpr(ast_exp.LambdaExp e) {
		return getFunc(e.fd, e.constLookup, null);
	}

	Value implExpr(ast_exp.IndexExp e) {
		assert(!e.byRef, "IndexExp(byRef=true) not in simple DefineExp");
		assert(e.e.constLookup, "Indexed value must be const");
		assert(e.a.constLookup, "Index must be const");

		if (ast_ty.isEmpty(e.type)) {
			// Index out of bounds?
			return valAbort(e.type);
		}

		auto v = genExpr(e.e);
		auto ty = e.e.type;
		if(auto tupTy = cast(ast_ty.TupleTy) ty) {
			if(e.a.isConstant()) {
				auto vs = valUnpack(tupTy.types, v);
				auto r = recIndexTuple(vs, e.a);
				valForget(vs);
				return r;
			}
		}

		CReg i = genIndex(e.a);
		Value r = implIndexDup(v, e.type, ty, i);
		valForget(v);
		return r;
	}

	Value recIndexTuple(Value[] vs, Expression ie) {
		if(auto tup = cast(ast_exp.TupleExp) ie) {
			Value[] rs = iota(tup.e.length).map!(i => this.recIndexTuple(vs, tup.e[i])).array;
			Expression[] types = tup.e.map!(e => e.type).array;
			return valPack(types, rs);
		}
		if(auto lit = ie.asIntegerConstant(true)) {
			return valDup(vs[lit.get().to!size_t()]);
		}
		assert(false, "TODO non-literal tuple indexing; vector? coerce?");
	}

	CReg genIndex(Expression i) {
		assert(ast_ty.isClassical(i.type), "TODO quantum indexing");
		assert(ast_ty.isSubtype(i.type, ast_ty_Zt()), "TODO non-integer indexing");
		CReg r;
		bool check;
		if(ast_ty.isSubtype(i.type, ast_ty_Nt())) {
			r = genExprAs(i, ast_ty_Nt()).creg;
			check = true;
		} else {
			r = genExprAs(i, ast_ty_Zt()).creg;
			check = false;
		}
		if(r !in ctx.intValue) {
			if(auto lit = i.asIntegerConstant(true)) {
				r = ctx.literalInt(lit.get());
			}
		}
		ccg.checkLeInt(check, ctx.intZero, r);
		return r;
	}

	Value implIndexDup(Value v, Expression rTy, Expression ty, CReg i) {
		if(auto tupTy = cast(ast_ty.TupleTy) ty) {
			if(auto ii = ctx.asIndex(i, tupTy.types.length)) {
				size_t ix = ii.get();
				auto vs = valUnpack(tupTy.types, valDup(v));
				auto r = vs[ix];
				vs[ix] = null;
				valForget(vs);
				return genSubtype(r, tupTy.types[ix], rTy);
			}

			auto ty2 = ast_ty.vectorTy(rTy, tupTy.length);
			auto v2 = genSubtype(valDup(v), ty, ty2);
			auto r = implIndexDupVector(v2, rTy, ctx.literalInt(tupTy.length), i);
			valForget(v2);
			return r;
		}
		if(auto vecTy = cast(ast_ty.VectorTy) ty) {
			CReg len = getVectorLength(vecTy);
			ccg.checkLtInt(true, i, len);
			return genSubtype(
				implIndexDupVector(v, vecTy.next, len, i),
				vecTy.next,
				rTy,
			);
		}
		if(auto arrTy = cast(ast_ty.ArrayTy) ty) {
			CReg len;
			auto v2o = valArrayToVector(arrTy.next, len, v), v2 = v2o;
			ccg.checkLtInt(true, i, len);
			Value r = implIndexDupVector(v2, arrTy.next, len, i);
			return genSubtype(r, arrTy.next, rTy);
		}
		if(auto intTy = ast_ty.isFixedIntTy(ty)) {
			auto bits = getNumericBits(intTy);
			ccg.checkLtInt(true, i, bits);
			if(intTy.isClassical) {
				assert(rTy == ast_ty.Bool(true));
				return implIndexDupCInt(v, bits, i);
			}
			assert(rTy == ast_ty.Bool(false), format("indexing %s results in %s", ty, rTy));
			return implIndexDupVector(v, rTy, bits, i);
		}
		assert(false, format("Cannot index %s", ty));
	}

	Value implIndexDupVector(Value v, Expression itemTy, CReg len, CReg i) {
		CReg rc = null;
		QReg rq = null;
		if(v.hasClassical && typeHasClassical(itemTy)) {
			rc = ccg.boxIndex(ctypeSilqTuple, len, v.creg, i);
		}
		if(v.hasQuantum && typeHasQuantum(itemTy)) {
			rq = new QReg();
			if(typeHasQDep(itemTy)) {
				auto qts = getVectorQTypes(itemTy, len, v.creg);
				qcg.writeQOp(opIndexDupD, [rq], [len, qts, i], [v.qreg], []);
			} else {
				auto qt = getQTypeRaw(itemTy, null);
				qcg.writeQOp(opIndexDupI, [rq], [len, qt, i], [v.qreg], []);
			}
		}
		return valNewQ(rc, rq);
	}

	Value implIndexDupCInt(Value v, CReg bits, CReg i) {
		auto mask = ccg.intPow2(i);
		return valNewC(ccg.intCmpEq(ccg.intBitAnd(v.creg, mask), mask));
	}

	Value implIndexSwapOut(ref Value v, Expression outerTy, Expression wantTy, CReg i, ref Dummy dummy) {
		Expression gotTy = null;
		auto r = implIndexSwap(v, outerTy, outerTy, i, (ref Expression ty, CReg rc) {
			gotTy = ty;
			auto qt = getQTypeRaw(ty, rc);
			dummy.type = ty;
			dummy.creg = rc;
			dummy.qtype = qt;
			return valNewQ(rc, qcg.allocDummy(qt));
		});
		assert(gotTy);
		return genSubtype(r, gotTy, wantTy);
	}

	void implIndexSwapIn(ref Value v, Expression outerTy1, Expression outerTy2, Expression valueTy, CReg i, Dummy orig, Value p) {
		Expression dummyTy = null;
		auto r = implIndexSwap(v, outerTy1, outerTy2, i, (ref Expression ty, CReg rc) {
			dummyTy = ty;
			ty = valueTy;
			return p;
		});
		assert(!!dummyTy);
		auto tmp = valNewQ(orig.creg, qcg.allocDummy(orig.qtype));
		tmp = genSubtype(tmp, orig.type, dummyTy);
		valUndup(r, tmp);
		valForget(tmp);
	}

	Value implIndexSwap(ref Value v, Expression outerTy1, Expression outerTy2, CReg i, Value delegate(ref Expression, CReg) repl) {
		if(auto tupTy1 = cast(ast_ty.TupleTy) outerTy1) {
			return implIndexSwapTuple(v, tupTy1.types, outerTy2, i, repl);
		}
		if(auto vecTy1 = cast(ast_ty.VectorTy) outerTy1) {
			if(auto vecTy2 = cast(ast_ty.VectorTy) outerTy2) {
				CReg len = getVectorLength(vecTy1);
				ccg.checkLtInt(true, i, len);
				return implIndexSwapVector(v, vecTy1.next, vecTy2.next, len, i, repl);
			}
			auto tupTy2 = outerTy2.isTupleTy();
			assert(tupTy2);
			auto types = vecTy1.next.repeat(tupTy2.length).array;
			return implIndexSwapTuple(v, types, outerTy2, i, repl);
		}
		if(auto arrTy1 = cast(ast_ty.ArrayTy) outerTy1) {
			auto arrTy2 = cast(ast_ty.ArrayTy) outerTy2;
			assert(arrTy2);
			CReg len;
			auto vec0 = valArrayToVector(arrTy1.next, len, v), vec = vec0;
			ccg.checkLtInt(true, i, len);
			auto r = implIndexSwapVector(vec, arrTy1.next, arrTy2.next, len, i, repl);
			if(vec.creg !is vec0.creg) {
				v = valVectorToArray(len, vec);
			} else {
				v = valNewQ(v.creg, vec.qreg);
			}
			return r;
		}
		if(auto intTy1 = ast_ty.isFixedIntTy(outerTy1)) {
			auto intTy2 = ast_ty.isFixedIntTy(outerTy2);
			assert(intTy2);
			assert(intTy1.bits == intTy2.bits);
			assert(intTy1.isSigned == intTy2.isSigned);
			auto bits = getNumericBits(intTy1);
			ccg.checkLtInt(true, i, bits);
			if(!intTy2.isClassical) {
				if(intTy1.isClassical) {
					v = genSubtype(v, outerTy1, outerTy2);
				}
				return implIndexSwapVector(v, ast_ty.Bool(false), ast_ty.Bool(false), bits, i, repl);
			}
			auto r = implIndexDupCInt(v, bits, i);

			Expression innerTy = ast_ty.Bool(true);
			auto p = repl(innerTy, r.creg);
			assert(innerTy is ast_ty.Bool(true));
			assert(!p.qreg);
			if(p.creg !is r.creg) {
				auto mask = ccg.intPow2(i);
				if(intTy1.isSigned) {
					// negate mask if isSigned && i == bits - 1
					auto isLast = ccg.intCmpEq(i, ccg.intSub(bits, ctx.intOne));
					mask = ccg.cond(isLast, mask, ccg.intNeg(mask));
				}
				auto v0 = v.creg;
				auto v1 = ccg.intBitXor(v0, mask);
				auto isDiff = ccg.boolNe(r.creg, p.creg);
				v = valNewC(ccg.cond(isDiff, v0, v1));
			}
			return r;
		}
		assert(false, format("Cannot index %s", outerTy1));
	}

	Value implIndexSwapTuple(ref Value v, Expression[] types, Expression outerTy2, CReg ix, Value delegate(ref Expression, CReg) repl) {
		if(auto ii = ctx.asIndex(ix, types.length)) {
			if(0<=ii.get() && ii.get() < types.length) {
				auto vs = valUnpack(types, v);
				auto types2 = types.dup;
				auto r = vs[ii.get()];
				auto p = repl(types2[ii.get()], r.creg);
				vs[ii.get()] = p;
				auto v2 = valPack(types2, vs);
				v = valNewQ(
					p.creg is r.creg ? v.creg : v2.creg,
					v2.qreg,
				);
				v = genSubtype(v, ast_ty.tupleTy(types2), outerTy2);
				return r;
			} else {
				Expression ty = ast_ty.bottom;
				auto r = valAbort(ty);
				auto p = repl(ty, r.creg);
				valDeallocError(p);
				return r;
			}
		} else {
			Expression cty = ast_ty.bottom;
			foreach(ty; types) {
				cty = ast_ty.joinTypes(cty, ty);
				assert(!!cty);
			}
			auto vecTy1 = ast_ty.vectorTy(cty, types.length);
			v = genSubtype(v, ast_ty.tupleTy(types), vecTy1);
			auto len = ctx.literalInt(types.length);
			ccg.checkLtInt(true, ix, len);
			if(auto vecTy2 = cast(ast_ty.VectorTy) outerTy2) {
				return implIndexSwapVector(v, vecTy1.next, vecTy2.next, len, ix, repl);
			}
			if(auto arrTy2 = cast(ast_ty.ArrayTy) outerTy2) {
				auto r = implIndexSwapVector(v, vecTy1.next, arrTy2.next, len, ix, repl);
				v = genSubtype(v, ast_ty.vectorTy(arrTy2.next, types.length), arrTy2);
				return r;
			}
			assert(0, "dynamic-index tuple swap must result in vector or array");
		}
	}

	Value implIndexSwapVector(ref Value v, Expression itemTy1, Expression itemTy2, CReg len, CReg i, Value delegate(ref Expression, CReg) repl) {
		if(itemTy1 !is itemTy2) {
			auto conv = ast_conv.typeExplicitConversion!true(itemTy1, itemTy2, ast_exp.TypeAnnotationType.annotation);
			assert(conv, format("not a subtype: %s -> %s", itemTy1, itemTy2));
			itemTy1 = itemTy2;
			v = implConvertVector(conv, len, v);
		}
		assert(typeHasClassical(itemTy2) || !v.hasClassical);
		assert(typeHasQuantum(itemTy2) || !v.hasQuantum);

		auto vc = v.creg;
		CReg rc = ccg.boxIndex(ctypeSilqTuple, len, vc, i);
		auto p = repl(itemTy1, rc);
		p = genSubtype(p, itemTy1, itemTy2);
		if(p.creg !is rc) {
			vc = ccg.boxReplace(ctypeSilqTuple, len, vc, i, p.creg);
		}

		auto vq = v.qreg;
		auto oldQt = getQTypeRaw(itemTy2, rc);
		auto newQt = getQType(itemTy2, p);

		QReg rq = null;
		if(oldQt !is ctx.qtUnit || newQt !is ctx.qtUnit) {
			vq = new QReg();
			rq = new QReg();
			bool qd = typeHasQDep(itemTy2);
			if(newQt is oldQt && !qd) {
				qcg.writeQOp(opIndexSwapI, [vq, rq], [len, oldQt, i], [], [v.qreg, p.qreg]);
			} else {
				auto qts = qd ? getVectorQTypes(itemTy2, len, v.creg) : ccg.boxRepeat(ctypeQtArray, len, oldQt);
				auto qts2 = newQt is oldQt ? qts : ccg.boxReplace(ctypeQtArray, len, qts, i, newQt);
				qcg.writeQOp(opIndexSwapD, [vq, rq], [len, qts, qts2, i], [], [v.qreg, p.qreg]);
			}
		} else {
			if(p.hasQuantum) qcg.deallocUnit(p.qreg);
			vq = v.qreg;
		}

		v = valNewQ(vc, vq);
		return valNewQ(rc, rq);
	}

	Value implExpr(ast_exp.SliceExp e) {
		Expression arg = e.e;
		assert(arg.constLookup, "TODO non-lifted slicing");
		assert(e.l.constLookup, "slice left index must be const");
		assert(e.r.constLookup, "slice right index must be const");

		auto v = genExpr(arg);

		CReg li = genIndex(e.l);
		CReg ri = genIndex(e.r);

		Expression itemTy;
		CReg len;

		if(auto tupTy = cast(ast_ty.TupleTy) arg.type) {
			auto lLit = ctx.asIndex(li, tupTy.types.length);
			auto rLit = ctx.asIndex(ri, tupTy.types.length);
			if(lLit && rLit) {
				auto l = lLit.get();
				auto r = rLit.get();
				if(l > r || r > tupTy.types.length) {
					return valAbort(e.type);
				}
				if(l == r) {
					valForget(v);
					return genSubtype(valNewC(null), ast_ty.unit, e.type);
				}
				assert(l < r);
				Value[] vs = valUnpack(tupTy.types, v);
				valForget(vs[0..l]);
				valForget(vs[r..$]);

				return genSubtype(
					valPack(tupTy.types[l..r], vs[l..r]),
					ast_ty.tupleTy(tupTy.types[l..r]),
					e.type,
				);
			}
			itemTy = ast_ty.elementType(e.type);
			len = ctx.literalInt(tupTy.types.length);
			assert(itemTy, format("not a vector/array: %s", e.type));
			auto vecTy = ast_ty.vectorTy(itemTy, tupTy.types.length);
			v = genSubtype(v, arg.type, vecTy);
		} else if(auto vecTy = cast(ast_exp.VectorTy) arg.type) {
			itemTy = vecTy.next;
			len = getVectorLength(vecTy);
		} else if(auto arrTy = cast(ast_exp.ArrayTy) arg.type) {
			itemTy = arrTy.next;
			v = valArrayToVector(itemTy, len, v);
		} else {
			assert(false, format("slicing %s", arg.type));
		}

		ccg.checkLeInt(true, li, len);

		if(li is ri) {
			return genSubtype(valNewC(null), ast_ty.unit, e.type);
		}
		ccg.checkLeInt(true, ri, len);
		ccg.checkLeInt(true, li, ri);

		CReg rLen;
		bool rArray;
		if(auto vecTy = cast(ast_exp.VectorTy) e.type) {
			assert(vecTy.next == itemTy);
			rLen = getVectorLength(vecTy);
			rArray = false;
		} else if(auto arrTy = cast(ast_exp.ArrayTy) e.type) {
			assert(arrTy.next == itemTy);
			rLen = ccg.intSub(ri, li);
			rArray = true;
		} else {
			assert(false, format("slicing result %s", e.type));
		}

		CReg rc = null;
		if(typeHasClassical(itemTy)) {
			rc = ccg.boxSlice(ctypeSilqTuple, len, v.creg, li, ri);
		}
		Value r;
		if(!typeHasQDep(itemTy)) {
			auto itemQType = getQTypeRaw(itemTy, null);
			r = valNewQt(rc, ccg.qtVector(itemQType, rLen));
			if(r.hasQuantum) {
				qcg.writeQOp(opSliceI, [r.qreg], [len, itemQType, li, ri], [v.qreg], []);
			}
		} else {
			auto qts = getVectorQTypes(itemTy, len, v.creg);
			r = valNewQ(rc, new QReg());
			qcg.writeQOp(opSliceD, [r.qreg], [len, qts, li, ri], [v.qreg], []);
		}
		valForget(v);
		if(rArray) {
			r = valVectorToArray(rLen, r);
		}
		return r;
	}

	Value implExpr(ast_exp.ForgetExp e) {
		assert(!e.var.constLookup);
		if(e.val) {
			Value v = genExpr(e.var);
			Value vf = genExprAs(e.val, e.var.type);
			valUndup(v, vf);
			valForget(vf);
		} else {
			genForget(e.var);
		}
		return valNewC(null);
	}

	void genForget(Expression e) {
		if(auto id = cast(ast_exp.Identifier) e) {
			auto v = genExpr(id);
			valForget(v);
			return;
		}
		if(auto tup = cast(ast_exp.TupleExp) e) {
			foreach(sube; tup.e) {
				genForget(sube);
			}
			return;
		}
		assert(false, format("Cannot forget %s %s", typeid(e).name, e));
	}

	Value implExpr(ast_exp.LiteralExp e) {
		auto ty = e.type;
		switch(ast_ty.isNumericTy(ty)) {
			case ast_ty.NumericType.none:
				break;
			case ast_ty.NumericType.Bool:
				string s = e.lit.str;
				bool val;
				if(s == "0") {
					val = false;
				} else if(s == "1") {
					val = true;
				} else {
					assert(false, format("Unknown literal %s", s));
				}
				if(typeHasClassical(ty)) {
					return valNewC(ctx.literalBool(val));
				}
				return valAllocQubit(val);
			case ast_ty_NumericType_Nt:
				assert(!typeHasQuantum(ty));
				return valNewC(ctx.literalInt(e.asIntegerConstant().get()));
			case ast_ty_NumericType_Zt:
				assert(!typeHasQuantum(ty));
				return valNewC(ctx.literalInt(e.asIntegerConstant().get()));
			case ast_ty_NumericType_Qt:
			case ast_ty_NumericType_R:
				assert(!typeHasQuantum(ty));
				return valNewC(ctx.literalFloat(to!double(e.lit.str)));
			case ast_ty_NumericType_C:
				assert(!typeHasQuantum(ty));
				if(!e.lit.str.endsWith("i")) {
					goto default;
				}
				auto val = ctx.literalFloat(to!double(e.lit.str[0..$-1]));
				auto tup = ccg.boxPack(ctypeSilqTuple, [ctx.floatZero, val]);
				auto z = ccg.emitPureOp("classical_call[primitive.complex.cfromri]", [tup]);
				return valNewC(z);
			default:
				assert(0, format("unknown numeric literal type: %s", ty));
		}
		if(auto intTy = ast_ty.isFixedIntTy(ty)) {
			auto bits = getNumericBits(intTy);
			auto val = ctx.literalInt(e.asIntegerConstant().get());
			if(intTy.isClassical) {
				return valNewC(ccg.intWrap(intTy.isSigned, bits, val));
			}
			auto r = valNewQt(null, ccg.qtVector(ctx.qtQubit, bits));
			if(r.hasQuantum) {
				qcg.writeQOp(opAllocUint, [r.qreg], [bits, val], [], []);
			}
			return r;
		}

		assert(false, format("Literal %s", e.type));
	}

	Value implType(ast_exp.Expression e) {
		if(ast_ty.isQNumeric(e)) return valNewC(null);
		return valNewC(getRTTI(e).packed);
	}

	Value implExpr(ast_exp.ClassicalTy e) {
		if(!qcg.inType) {
			genExpr(e.inner);
		}
		return implType(e);
	}

	Value implExpr(ast_exp.ArrayTy e) {
		if(!qcg.inType) {
			genExpr(e.next);
		}
		return implType(e);
	}

	Value implExpr(ast_exp.VectorTy e) {
		if(!qcg.inType) {
			genExpr(e.next);
			genExpr(e.num);
		}
		return implType(e);
	}

	Value implExpr(ast_exp.TupleTy e) {
		if(!qcg.inType) {
			foreach(sube; e.types) {
				genExpr(sube);
			}
		}
		return implType(e);
	}

	Value implExpr(ast_exp.ProductTy e) {
		if(!qcg.inType) {
			foreach(p; e.params) {
				genExpr(p.dtype);
			}
		}
		return implType(e);
	}

	Value implExpr(ast_exp.VariadicTy e) {
		if(!qcg.inType) {
			genExpr(e.next);
		}
		return implType(e);
	}

	Value implExpr(ast_exp.TypeTy e) {
		return implType(e);
	}

	Value implExpr(ast_exp.QNumericTy e) {
		return implType(e);
	}

	Value implExpr(ast_exp.BottomTy e) {
		return implType(e);
	}

	Value implExpr(ast_exp.NumericTy e) {
		return implType(e);
	}

	Value implExpr(ast_exp.StringTy e) {
		return implType(e);
	}

	Value implExpr(ast_exp.TypeAnnotationExp e) {
		// assert(e.e.constLookup == e.constLookup);
		auto conv = ast_conv.typeExplicitConversion!true(e.e.type, e.type, e.annotationType);
		assert(conv, format("bad conversion %s -> %s", e.e.type, e.type));
		if(!qcg.inType) {
			genExpr(e.t);
		}
		return genConvert(conv, genExpr(e.e));
	}

	Value implExpr(ast_exp.FieldExp e) {
		assert(e.f.name == "length", format("Unsupported field: %s", e.f.name));
		assert(e.type == ast_ty_Nt());
		assert(e.e.constLookup);
		auto v = genExpr(e.e);
		CReg r;
		if(auto tupTy = cast(ast_ty.TupleTy) e.e.type) {
			r = ctx.literalInt(tupTy.types.length);
		} else if(auto vecTy = cast(ast_ty.VectorTy) e.e.type) {
			r = getVectorLength(vecTy);
		} else if(auto arrTy = cast(ast_ty.ArrayTy) e.e.type) {
			r = ccg.getArrayLength(v.creg);
		} else {
			assert(false, format("Length of type %s", e.e.type));
		}
		valForget(v);
		return valNewC(r);
	}

	Value implExpr(ast_exp.IteExp e) {
		// Pin evaluation of lengths etc. outside the if statement
		pinType(e.type);

		auto cond = genCond(e.cond);
		ScopeWriter ifTrue, ifFalse;
		genSplit(cond, ifFalse, e.othw.blscope_, ifTrue, e.then.blscope_);

		auto rTrue = ifTrue.genCompoundValue(e.then, null, e.type);
		auto rFalse = ifFalse.genCompoundValue(e.othw, null, e.type);
		auto r = valMerge(cond, rFalse, rTrue);

		assert(!ifTrue.nscope || ifTrue.nscope.mergedVars.length == 0);
		ifTrue.checkEmpty(false);

		assert(!ifFalse.nscope || ifFalse.nscope.mergedVars.length == 0);
		ifFalse.checkEmpty(false);

		if(cond.isQuantum) qcg.forget(cond.qreg);
		return r;
	}

	Value implExpr(ast_exp.LetExp e) {
		return genCompoundValue(e.s, e.e, e.type);
	}

	Value implExpr(ast_exp.TupleExp e) {
		foreach(i, sube; e.e) {
			assert(sube.constLookup == e.constLookup || !typeHasQuantum(sube.type), format("tuple constLookup mismatch at %s; inner %s outer %s: %s item %s", sube.loc, sube.constLookup, e.constLookup, e, i));
		}
		auto types = e.e.map!(ei => ei.type).array;
		auto sub = e.e.map!(ei => genExpr(ei)).array;
		return valPack(types, sub);
	}

	Value implExpr(ast_exp.VectorExp e) {
		auto vecType = cast(ast_ty.VectorTy)e.type;
		assert(vecType);
		// TODO: make second disjunct unnecessary
		assert(e.e.all!(ei => ei.constLookup == e.constLookup || ast_ty.isClassical(ei.type)));
		auto sub = e.e.map!(ei => genExprAs(ei, vecType.next)).array;
		size_t n = e.e.length;
		auto vec = valPack(vecType.next.repeat(n).array, sub);
		return vec;
	}

	Value implExpr(ast_exp.CallExp e) {
		if(e.isClassical_) {
			auto r = getSimpleRTTI(e);
			assert(r);
			return valNewC(r.packed);
		}

		if(e.isSquare) {
			switch(ast_sem.isPreludeCall(e)) {
				case "int":
				case "uint":
					if(!qcg.inType) {
						genExpr(e.arg);
					}
					return valNewC(getRTTI(e).packed);
				default:
					break;
			}
		} else {
			// fast-path `dup`, `measure` to avoid RTTI
			// maybe consider `vector` as well?
			if(auto sube = cast(ast_exp.CallExp) e.e) {
				switch(ast_sem.isPreludeCall(sube)) {
					case "dup":
						assert(sube.isSquare, "non-[] call to dup");
						return genExprAs(e.arg, e.type);
					case "measure":
						assert(sube.isSquare, "non-[] call to measure");
						auto ty = sube.arg.eval();
						assert(e.type == ty.getClassical(), format("typeof(measure[t](e)) != classical(t) : %s != classical(%s)", e.type, ty));
						return valNewC(genMeasure(ty, genExprAs(e.arg, ty)));
					default:
						break;
				}
			}
		}

		final switch(ast_sem.isBuiltInCall(e)) {
			case ast_sem.BuiltIn.none:
				break;
			case ast_sem.BuiltIn.show:
			case ast_sem.BuiltIn.query:
				return valNewC(null);
			case ast_sem.BuiltIn.pi:
				assert(false, format("cannot call %s", e));
		}

		CallInfo ci = prepCall(e.e, e.arg, e.type, false);

		if(ci.makeClassical) {
			assert(!ci.hasQuantum, "quantum captures in make-classical call");

			auto subsc = subfuncScope(true);
			foreach(ref arg; ci.args) {
				arg.val = subsc.genPromote(arg.ty, arg.val.creg);
			}
			auto v = subsc.implCall(ci);
			auto r = subsc.genMeasure(ci.retType, v);
			auto f = subfuncPack("silq_cfunc", subsc, [r], []);

			ccg.writeCOp(opCallAsClassicalIndirect, [r], [f]);
			return valNewC(r);
		}

		return implCall(ci);
	}

	Value implCall(CallInfo ci) {
		string nameArg = null;
		CReg[] cArgs;
		QReg[] qcArgs, qiArgs;

		if(ci.targetF) {
			nameArg = ci.targetF.directName;
			auto cAp = appender!(CReg[]);
			auto qcAp = appender!(QReg[]);
			auto qiAp = appender!(QReg[]);
			cAp.put(ci.target.funcCapR);
			if (ci.captureMoved) {
				qiAp.put(ci.target.qfuncCapR);
			} else {
				qcAp.put(ci.target.qfuncCapR);
			}

			assert(ci.args.length == ci.targetF.params.length);
			assert(ci.args.length == ci.targetF.fd.params.length);
			foreach(i, param; ci.targetF.params) {
				auto arg = ci.args[i].val;
				if(param.hasClassical) cAp.put(arg.creg);
				if(param.hasQuantum) {
					if(param.isConst) qcAp.put(arg.qreg);
					else qiAp.put(arg.qreg);
				} else if(arg.hasQuantum) {
					// We've constant-folded the function but the frontend
					// hasn't constant-folded its argument type.
					if(!param.isConst) qcg.deallocUnit(arg.qreg);
				}
			}

			cArgs = cAp[];
			qcArgs = qcAp[];
			qiArgs = qiAp[];
		} else {
			packIndirect(ci, cArgs, qcArgs, qiArgs, false);
		}

		CReg[] cRet;
		QReg[] qRet;
		auto ret = valNewQ(ci.retType);
		putRet(ci.targetF, cRet, qRet, ret);

		if(ci.effect <= ast_ty.Annotation.none) {
			qcg.writeMOp(opCallMeasure(nameArg), cRet, qRet, cArgs, qcArgs, qiArgs);
		} else {
			ccg.writeCOp(opCallClassical(nameArg), cRet, cArgs);
			string op = ci.effect >= ast_ty.Annotation.qfree ? opCallQfree(nameArg) : opCallMfree(nameArg);
			qcg.writeQOp(op, qRet, cArgs, qcArgs, qiArgs);
		}
		qcg.forget(qcArgs);
		return ret;
	}

	ast_sem.ExpSemContext semContext(bool isConst) {
		auto cur = this;
		auto lookupScope = cur.nscope;
		while(!lookupScope) {
			cur = cur.parent;
			lookupScope = cur.nscope;
		}
		return ast_sem.ExpSemContext(
			lookupScope,
			isConst ? ast_sem.ConstResult.yes : ast_sem.ConstResult.no,
			qcg.inType ? ast_sem.InType.yes : ast_sem.InType.no,
		);
	}

	Value implExpr(ast_exp.CatExp e) {
		Value v1 = genExpr(e.e1);
		Value v2 = genExpr(e.e2);
		return genConcat(e.type, v1, e.e1.type, v2, e.e2.type);
	}

	Value genConcat(Expression ty, Value lhsV, Expression lhsTy, Value rhsV, Expression rhsTy) {
		if(ast_ty.isEmpty(ty)) {
			if(ast_ty.isEmpty(lhsTy)) return lhsV;
			if(ast_ty.isEmpty(rhsTy)) return rhsV;
			assert(false, "non-bottom concatentation is bottom");
		}
		if(auto tupTy = cast(ast_ty.TupleTy) ty) {
			return implCatTuple(tupTy, lhsV, lhsTy, rhsV, rhsTy);
		}
		if(auto vecTy = cast(ast_ty.VectorTy) ty) {
			return implCatVector(vecTy, lhsV, lhsTy, rhsV, rhsTy);
		}
		if(auto arrTy = cast(ast_ty.ArrayTy) ty) {
			return implCatArray(arrTy, lhsV, lhsTy, rhsV, rhsTy);
		}
		assert(false, format("concatenation result %s", ty));
	}

	Value implCatTuple(ast_ty.TupleTy ty, Value lhsV, Expression lhsRawTy, Value rhsV, Expression rhsRawTy) {
		auto lhsTy = lhsRawTy.isTupleTy();
		if (!lhsTy) lhsTy = lhsRawTy.eval().isTupleTy();
		assert(!!lhsTy, format("not a tuple type: %s", lhsRawTy));
		auto rhsTy = rhsRawTy.isTupleTy();
		if (!rhsTy) lhsTy = lhsRawTy.eval().isTupleTy();
		assert(!!rhsTy, format("not a tuple type: %s", rhsRawTy));

		auto lhsTypes = iota(lhsTy.length).map!(i => lhsTy[i]).array;
		auto rhsTypes = iota(rhsTy.length).map!(i => rhsTy[i]).array;
		assert(ty.types == lhsTypes ~ rhsTypes, format("tuple concat: %s ~ %s != %s", lhsTypes, rhsTypes, ty.types));

		Value[] lhsVs = valUnpack(lhsTypes, lhsV);
		Value[] rhsVs = valUnpack(rhsTypes, rhsV);
		return valPack(ty.types, lhsVs ~ rhsVs);
	}

	Value implCatVector(ast_ty.VectorTy ty, Value lhsV, Expression lhsTy, Value rhsV, Expression rhsTy) {
		auto aTy = ast_ty.arrayTy(ty.next);
		auto r = implCatArray(aTy, lhsV, lhsTy, rhsV, rhsTy);
		CReg len;
		return valArrayToVector(ty.next, len, r);
	}

	Value implCatArray(ast_ty.ArrayTy ty, Value lhsV, Expression lhsTy, Value rhsV, Expression rhsTy) {
		lhsV = genSubtype(lhsV, lhsTy, ty);
		rhsV = genSubtype(rhsV, rhsTy, ty);
		return valArrayCat(ty.next, lhsV, rhsV);
	}

	Value implExpr(TokenType op)(UnaryExp!op e){
		auto lowered = ast_low.getLowering(e, semContext(e.constLookup));
		assert(lowered, format("Failed to lower expression: %s", e));
		return genExprAs(lowered, e.type);
	}

	Value implExpr(TokenType op)(BinaryExp!op e) if(op != Tok!opConcat && op != Tok!opDefine && op != Tok!opComma && !is(BinaryExp!op: ast_exp.AAssignExp)) {
		if(ast_ty.isEmpty(e.type) && ast_ty.isEmpty(e.e1.type)) {
			auto v1 = genExpr(e.e1);
			auto v2 = genExpr(e.e2);
			valDeallocError(v2);
			return v1;
		}
		auto lowered = ast_low.getLowering(e, semContext(e.constLookup));
		assert(lowered, format("Failed to lower expression: %s", e));
		return genExprAs(lowered, e.type);
	}

	Value implExpr(ast_exp.AssertExp e) {
		if(ast_ty.isEmpty(e.type)) {
			return valAbort(e.type);
		}
		assert(e.e.constLookup);
		assert(e.type == ast_ty.unit(), "abort(non-false) must return unit");
		auto v = genExprAs(e.e, ast_ty.Bool(true));
		ccg.checkBool(true, v.creg);
		return valNewC(null);
	}

	void genLhs(Expression lhs, Value rhs, Expression rhsType) {
		while(auto lhsE = cast(ast_exp.TypeAnnotationExp) lhs) lhs = lhsE.e;
		// TODO: Is coerce the right thing here?
		rhs = genCoerce(rhs, rhsType, lhs.type);
		return ast_exp.dispatchExp!((auto ref lhs) => this.implLhs(lhs, rhs))(lhs);
	}

	void implLhs(ast_exp.Identifier e, Value v) {
		auto var = e.meaning;
		assert(cast(ast_decl.VarDecl) var, "LHS of assignment not VarDecl");
		defineVar(var, v);
	}

	void implLhs(ast_exp.TupleExp e, Value v) {
		auto tupTy = e.type.isTupleTy();
		assert(tupTy);
		size_t n = tupTy.length;
		assert(n == e.length);
		Value[] res = valUnpack(iota(n).map!(i => tupTy[i]).array, v);
		for(size_t i = 0; i < n; i++) {
			genLhs(e.e[i], res[i], tupTy[i]);
		}
	}

	void implLhs(ast_exp.VectorExp e, Value v) {
		auto vecTy = cast(ast_exp.VectorTy)e.type;
		assert(vecTy);
		auto itemTy = vecTy.next;
		size_t n = e.e.length;
		Value[] res = valUnpack(itemTy.repeat(n).array, v);
		for(size_t i = 0; i < n; i++) {
			genLhs(e.e[i], res[i], itemTy);
		}
	}

	void implLhs(ast_exp.CallExp e, Value ret) {
		assert(!e.isSquare);
		assert(!e.isClassical_);
		assert(ret);

		// fast-path `dup` to avoid RTTI
		if(auto sube = cast(ast_exp.CallExp) e.e) {
			switch(ast_sem.isPreludeCall(sube)) {
				case "dup":
					assert(sube.isSquare, "non-[] call to dup");
					assert(sube.arg.eval() == e.type, "typeof(dup[t](e)) != t");
					Value tmp = genExprAs(e.arg, e.type);
					valUndup(ret, tmp);
					valForget(tmp);
					return;
				default:
					break;
			}
		}

		CallInfo ci = prepCall(e.e, e.arg, e.type, true);
		assert(!ci.makeClassical, "TODO reversed make-classical");

		string nameArg = null;
		CReg[] cArgs;
		QReg[] qcArgs, qiArgs;
		void delegate() unpackCb;
		if(ci.targetF) {
			nameArg = ci.targetF.directName;
			auto cAp = appender!(CReg[]);
			auto qcAp = appender!(QReg[]);
			auto qiAp = appender!(QReg[]);
			cAp.put(ci.target.funcCapR);
			assert(!ci.target.hasQuantum);

			assert(ci.args.length == ci.targetF.params.length);
			assert(ci.args.length == ci.targetF.fd.params.length);
			foreach(i, param; ci.targetF.params) {
				auto arg = ci.args[i].val;
				if(param.hasClassical) cAp.put(arg.creg);
				if(param.hasQuantum) {
					if(param.isConst) qcAp.put(arg.qreg);
					else qiAp.put(arg.qreg);
				} else if(arg.hasQuantum) {
					// We've constant-folded the function but the frontend
					// hasn't constant-folded its argument type.
					if(!param.isConst) qcg.allocUnit(arg.qreg);
				}
			}

			cArgs = cAp[];
			qcArgs = qcAp[];
			qiArgs = qiAp[];
		} else {
			unpackCb = packIndirect(ci, cArgs, qcArgs, qiArgs, true);
		}

		CReg[] cRet, cRet2;
		QReg[] qRet;
		putRet(ci.targetF, cRet, qRet, ret);

		assert(ci.effect > ast_ty.Annotation.none, "reverse call not mfree");

		if (cRet) {
			cRet2 = [new CReg()];
		}
		ccg.writeCOp(opCallClassical(nameArg), cRet2, cArgs);
		if (cRet) {
			ccg.assumeEqual(cRet[0], cRet2[0]);
		}
		if(ci.effect < ast_ty.Annotation.qfree || qRet.any!(r => !!r) || qiArgs[].any!(r => !!r)) {
			string op = ci.effect >= ast_ty.Annotation.qfree ? opCallQfreeRev(nameArg) : opCallMfreeRev(nameArg);
			qcg.writeQOp(op, qiArgs, cArgs, qcArgs, qRet);
		}
		qcg.forget(qcArgs);
		if(unpackCb) unpackCb();

		foreach(i, arg; ci.args) {
			if(!arg.isConst) {
				genLhs(arg.expr, arg.val, arg.ty);
			}
		}
	}

	void implLhs(ast_exp.CatExp e, Value ret) {
		auto ty = e.type;
		if(auto tupTy = cast(ast_ty.TupleTy) ty) {
			return implUncatTuple(tupTy, e.e1, e.e2, ret);
		}
		if(auto vecTy = cast(ast_ty.VectorTy) ty) {
			return implUncatVector(vecTy, e.e1, e.e2, ret);
		}
		if(auto arrTy = cast(ast_ty.ArrayTy) ty) {
			return implUncatArray(arrTy, e.e1, e.e2, ret);
		}
		assert(false, format("can't unconcatenate %s", ty));
	}

	void implUncatTuple(ast_ty.TupleTy ty, Expression lhs, Expression rhs, Value ret) {
		auto lhsN = knownLength(lhs, false).asIntegerConstant(true).get().to!size_t();
		auto rhsN = knownLength(rhs, false).asIntegerConstant(true).get().to!size_t();
		assert(lhsN + rhsN == ty.types.length);

		auto items = valUnpack(ty.types, ret);
		auto lhsTy = ty.types[0..lhsN];
		auto rhsTy = ty.types[lhsN..$];
		auto lhsVal = valPack(lhsTy, items[0..lhsN]);
		auto rhsVal = valPack(rhsTy, items[lhsN..$]);
		genLhs(lhs, lhsVal, ast_ty.tupleTy(lhsTy));
		genLhs(rhs, rhsVal, ast_ty.tupleTy(rhsTy));
	}

	void implUncatVector(ast_ty.VectorTy ty, Expression lhs, Expression rhs, Value ret) {
		auto lhsLen = knownLength(lhs, false);
		assert(lhsLen, format("no length for LHS: %s", lhs));
		auto lhsTy = ast_ty.vectorTy(ty.next, lhsLen.eval());
		CReg lhsN = getVectorLength(lhsTy);

		auto rhsLen = knownLength(rhs, false);
		assert(rhsLen, format("no length for RHS: %s", rhs));
		auto rhsTy = ast_ty.vectorTy(ty.next, rhsLen.eval());
		CReg rhsN = getVectorLength(rhsTy);

		CReg totN = getVectorLength(ty);

		Value lhsVal, rhsVal;
		valVectorUncat(lhsVal, rhsVal, ty.next, lhsN, rhsN, totN, ret);
		genLhs(lhs, lhsVal, lhsTy);
		genLhs(rhs, rhsVal, rhsTy);
	}

	void implUncatArray(ast_ty.ArrayTy ty, Expression lhs, Expression rhs, Value ret) {
		void trySetLen(out Expression ty, out CReg len, Expression itemTy, Expression val) {
			auto le = knownLength(val, false);
			if(!le) return;
			auto t = ast_ty.vectorTy(itemTy, le.eval());
			ty = t;
			len = getVectorLength(t);
		}

		Expression lhsTy = null, rhsTy = null;
		CReg lhsN = null, rhsN = null;
		trySetLen(lhsTy, lhsN, ty.next, lhs);
		trySetLen(rhsTy, rhsN, ty.next, rhs);
		assert(lhsN || rhsN);

		CReg totN;
		ret = valArrayToVector(ty.next, totN, ret);
		if(lhsN && rhsN) {
			ccg.checkEqInt(true, totN, ccg.intAdd(lhsN, rhsN));
		}
		if(!lhsN) {
			lhsN = ccg.intSub(totN, rhsN);
			ccg.checkLeInt(true, ctx.intZero, lhsN);
		}
		if(!rhsN) {
			rhsN = ccg.intSub(totN, lhsN);
			ccg.checkLeInt(true, ctx.intZero, rhsN);
		}

		Value lhsVal, rhsVal;
		valVectorUncat(lhsVal, rhsVal, ty.next, lhsN, rhsN, totN, ret);
		if(!lhsTy) {
			lhsVal = valVectorToArray(lhsN, lhsVal);
			lhsTy = ty;
		}
		genLhs(lhs, lhsVal, lhsTy);
		if(!rhsTy) {
			rhsVal = valVectorToArray(rhsN, rhsVal);
			rhsTy = ty;
		}
		genLhs(rhs, rhsVal, rhsTy);
	}

	void implLhs(ast_exp.IndexExp e, Value v) {
		assert(false, format("TODO LHS %s: %s; type=%s, etype=%s", typeid(e).name, e, e.type, e.e.type));
	}

	void implLhs(Expression e, Value v) {
		assert(false, format("unknown LHS %s: %s; type=%s", typeid(e).name, e, e.type));
	}

	Result genCompoundStmt(ast_exp.CompoundExp e) {
		assert(nscope);
		assert(nscope == e.blscope_);
		foreach(decl; nscope.forgottenVarsOnEntry) {
			valForget(getVar(decl, false));
		}
		auto r = genStmts(e.s);
		scope loc = PushLocation(ctx, e.loc);
		foreach(decl; nscope.forgottenVars) {
			assert(!r.isReturn, format("CompoundExp returns but blscope_ has forgotten var %s", decl));
			Value v = getVar(decl, false);
			if(!v.hasQuantum) continue;
			if(r.isAbort) qcg.deallocError(v.qreg);
			else valForget(v);
		}
		return r;
	}

	Result genStmts(Expression[] stmts, Result result = Result.passes()) {
		assert(nscope);
		Result combineResults(Result ra, Result rb, ScopeWriter scB) {
			if(ra.isReturn || ra.isAbort || rb.isPass) {
				return ra;
			}
			if(ra.isPass) {
				if(rb.isReturn || rb.isAbort) {
					scB.checkEmpty(rb.isAbort);
				}
				return rb;
			}
			assert(ra.isConditionalReturn);
			if(rb.isReturn || rb.isAbort) {
				auto vb = rb.asValue(scB, nscope.getFunction().ret);
				scB.checkEmpty(rb.isAbort);
				auto vc = ra.retCond.invert().valMerge(ra.retValue, vb, this);
				ra.forgetCond(this);
				checkEmpty(false);
				return Result.returns(vc);
			}
			assert(rb.isConditionalReturn);
			assert(0, "TODO multiple subsequent nested conditional returns");
		}
		foreach(i, sube; stmts) {
			if(auto iteExp = cast(ast_exp.IteExp) sube) {
				auto ite = genIte(iteExp);
				if(auto rv = cast(ItePass) ite) {
					rv.forgetCond(this);
					continue;
				}
				if(auto rv = cast(IteAbort) ite) {
					rv.forgetCond(this);
					return Result.aborts(rv.witness);
				}
				if(auto rv = cast(IteReturn) ite) {
					rv.forgetCond(this);
					return Result.returns(rv.value);
				}
				if(auto rv = cast(ItePartialReturn) ite) {
					auto scCont = rv.scCont;
					ScopeWriter scTail;
					if(scCont.nscope !is nscope) {
						assert(scCont.nscope.parent is nscope);
						scTail = new ScopeWriter(nscope, scCont);

						// move classical variables so that they can be consumed
						foreach(name, ref var; this.vars) {
							if(!var.value) continue;
							assert(!var.value.hasQuantum, format("returning if statement did not split variable %s", name));
							scTail.vars[name] = var;
						}
						checkEmpty(false);

						foreach(decl; scCont.nscope.mergedVars) {
							auto outer = decl.mergedInto;
							assert(outer.scope_ is nscope);
							auto ty = typeForDecl(outer);
							assert(ty == typeForDecl(decl));
							assert(outer.mergedFrom == [decl]);
							scTail.defineVar(outer, scCont.getVar(decl, false));
						}
						scCont.checkEmpty(false);
					}else{
						scTail = scCont;
					}

					auto contRet = scTail.genStmts(stmts[i+1..$], result);
					if(contRet.isReturn || contRet.isAbort) {
						scTail.checkEmpty(contRet.isAbort);

						auto r = rv.retCond.valMerge(contRet.asValue(scTail, nscope.getFunction().ret), rv.value, this);
						rv.forgetCond(this);
						return Result.returns(r);
					} else {
						result = combineResults(result, Result.conditionallyReturns(rv.value, rv.retCond), this);
						result = combineResults(result, contRet, scTail);
						assert(result.isConditionalReturn);
						vars = scTail.vars;
						return result;
					}
				}
				if(auto rv = cast(ItePartialAbort) ite) {
					auto scCont = rv.scCont;
					auto scFail = withCond(null, rv.cond);
					foreach(decl; scCont.nscope.mergedVars) {
						auto outer = decl.mergedInto;
						auto ty = typeForDecl(outer);
						assert(ty == typeForDecl(decl));
						assert(outer.mergedFrom == [decl]);
						auto v0 = scCont.getVar(decl, false);
						auto v1 = scFail.valError(rv.witness, ty);
						defineVar(outer, valMerge(rv.cond, v0, v1));
					}
					scCont.checkEmpty(false);
					rv.forgetCond(this);
					continue;
				}
				assert(false, "Bad if-then-else result");
			}

			if(result.isConditionalReturn) {
				auto scCondRet = result.retCond.invert().addToScope(nscope, this);
				scCondRet.vars = vars;
				result = combineResults(result, scCondRet.genStmt(sube), scCondRet);
				vars = scCondRet.vars;
			} else {
				result = combineResults(result, genStmt(sube), this);
			}
			if(result.isReturn || result.isAbort) {
				return result;
			}
		}
		return result;
	}

	IteResult genIte(ast_exp.IteExp e) {
		auto cond = genCond(e.cond);

		ScopeWriter ifTrue, ifFalse;
		genSplit(cond, ifFalse, e.othw.blscope_, ifTrue, e.then.blscope_);

		Result rTrue = ifTrue.genCompoundStmt(e.then);
		Result rFalse = ifFalse.genCompoundStmt(e.othw);

		if(rTrue.isAbort && rFalse.isAbort) {
			CReg cr;
			if(cond.isClassical) cr = ccg.cond(cond.creg, rFalse.abortWitness, rTrue.abortWitness);
			else cr = rTrue.abortWitness;
			return new IteAbort(cond, cr);
		}

		if(rTrue.isConditionalReturn || rFalse.isConditionalReturn) {
			RetValue retTrue = RetValue.init, retFalse = RetValue.init;
			CondRetValue condTrue, condFalse;
			if(rTrue.isConditionalReturn) {
				retTrue = rTrue.retValue;
				condTrue = rTrue.retCond.asCondRetValue(ifTrue);
			}else if(rTrue.isAbort || rTrue.isReturn) {
				retTrue = rTrue.asValue(ifTrue, e.type);
				condTrue = CondRetValue.makeConst(1, ifTrue);
			}else{
				assert(rTrue.isPass);
				condTrue = CondRetValue.makeConst(0, ifTrue);
			}

			if(rFalse.isConditionalReturn) {
				retFalse = rFalse.retValue;
				condFalse = rFalse.retCond.asCondRetValue(ifFalse);
			}else if(rFalse.isAbort || rFalse.isReturn) {
				retFalse = rFalse.asValue(ifFalse, e.type);
				condFalse = CondRetValue.makeConst(1, ifFalse);
			}else{
				assert(rFalse.isPass);
				condFalse = CondRetValue.makeConst(0, ifFalse);
			}

			auto retCond = CondRetValue.merge(cond, condFalse, condTrue, ifFalse, ifTrue, this).asCondRet();

			if(retTrue) {
				retTrue = retCond.updateRetCond(retTrue, rTrue.retCond, ifTrue);
			}

			if(retFalse) {
				retFalse = retCond.updateRetCond(retFalse, rFalse.retCond, ifFalse);
			}

			RetValue ret;
			ScopeWriter retScope;
			if(retFalse && retTrue) {
				ret = retCond.mergeRet(cond, retFalse, retTrue, this);
				retScope = this;
			}else if(retTrue) {
				ret = retTrue;
				retScope = ifTrue;
			}else if(retFalse) {
				ret = retFalse;
				retScope = ifFalse;
			}else assert(0);

			if(retScope !is this) {
				if(retTrue) {
					auto retFalseUnreachable = retCond.allocUnreachableRet(retTrue, ifFalse);
					ret = retCond.mergeRet(cond, retFalseUnreachable, retTrue, this);
				}else if(retFalse) {
					auto retTrueUnreachable = retCond.allocUnreachableRet(retFalse, ifTrue);
					ret = retCond.mergeRet(cond, retFalse, retTrueUnreachable, this);
				}else assert(0);
			}

			auto ifFalseOrig = ifFalse, ifTrueOrig = ifTrue;

			if(rFalse.mayPass) {
				ifFalse = retCond.replaceCondRet(rFalse.retCond, ifFalse);
			}
			if(rTrue.mayPass) {
				ifTrue = retCond.replaceCondRet(rTrue.retCond, ifTrue);
			}

			static ScopeWriter removeCond(CondAny cond, ScopeWriter w) {
				if(cond.isQuantum) w.qcg.condQ=w.qcg.condQ.filter!(qc=>qc != cond.qcond).array;
				else w.ccg.condC=w.ccg.condC.filter!(cc=>cc != cond.ccond).array;
				foreach(name, ref var; w.vars) {
					if(!var.value) continue;
					auto valUnreachable = Value.newReg(null, cond.isQuantum ? w.withCond(w.nscope, cond.invert()).qcg.allocError() : null);
					var.value = w.valMerge(cond, valUnreachable, var.value);
				}
				return w;
			}

			ScopeWriter reachable;
			if(rFalse.mayPass && rTrue.mayPass) {
				reachable = retCond.invert().genMerge(cond, ifFalse, ifTrue, this);
			}else if(rFalse.mayPass) {
				reachable = removeCond(cond.invert(), ifFalse);
			}else if(rTrue.mayPass) {
				reachable = removeCond(cond, ifTrue);
			}else assert(0);

			if(rTrue.isConditionalReturn()) {
				rTrue.forgetCond(ifTrueOrig);
			}
			if(rFalse.isConditionalReturn()) {
				rFalse.forgetCond(ifFalseOrig);
			}

			if(cond.isQuantum) qcg.forget(cond.qreg);
			return new ItePartialReturn(retCond, ret, reachable);
		}

		if(!rTrue.isPass && !rFalse.isPass) {
			RetValue retTrue = rTrue.asValue(ifTrue, e.type);
			RetValue retFalse = rFalse.asValue(ifFalse, e.type);
			RetValue ret = RetValue.valMerge(cond, retFalse, retTrue, this);
			return new IteReturn(cond, ret);
		}
		if(rTrue.isAbort) {
			assert(rFalse.isPass);
			ifTrue.checkEmpty(true);
			return new ItePartialAbort(cond, rTrue.abortWitness, ifFalse);
		}
		if(rTrue.isReturn) {
			assert(rFalse.isPass);
			ifTrue.checkEmpty(false);
			return new ItePartialReturn(cond, rTrue.retValue, ifFalse);
		}
		if(rFalse.isAbort) {
			assert(rTrue.isPass);
			ifFalse.checkEmpty(true);
			return new ItePartialAbort(cond.invert(), rFalse.abortWitness, ifTrue);
		}
		if(rFalse.isReturn) {
			assert(rTrue.isPass);
			ifFalse.checkEmpty(false);
			return new ItePartialReturn(cond.invert(), rFalse.retValue, ifTrue);
		}
		assert(rTrue.isPass && rFalse.isPass);

		scope loc = PushLocation(ctx, locEnd(e.loc));
		genMerge(cond, ifFalse, ifTrue);
		ifTrue.checkEmpty(false);
		ifFalse.checkEmpty(false);
		return new ItePass(cond);
	}

	Result genStmt(Expression e) {
		assert(e, "genStmt(null)");
		scope loc = PushLocation(ctx, e.loc);
		try {
			static foreach(t; AliasSeq!(
				ast_exp.DefineExp,
				ast_exp.AssignExp,
				ast_exp.OrAssignExp,
				ast_exp.AndAssignExp,
				ast_exp.AddAssignExp,
				ast_exp.SubAssignExp,
				ast_exp.NSubAssignExp,
				ast_exp.MulAssignExp,
				ast_exp.DivAssignExp,
				ast_exp.IDivAssignExp,
				ast_exp.ModAssignExp,
				ast_exp.PowAssignExp,
				ast_exp.CatAssignExp,
				ast_exp.BitOrAssignExp,
				ast_exp.BitXorAssignExp,
				ast_exp.BitAndAssignExp,
			)) {
				if(auto et = cast(t) e) return implStmt(et);
			}
			return ast_exp.dispatchStm!((auto ref e)=>this.implStmt(e))(e);
		} catch(AssertError exc) {
			exc.msg = format("%s\nat %s, statement: %s", exc.msg, e.loc, e);
			throw exc;
		}
	}

	Result implStmt(ast_exp.CompoundExp e) {
		if(!e.blscope_) return genStmts(e.s);

		auto sub = withBlock(e.blscope_);
		foreach(decl; sub.nscope.splitVars) {
			assert(decl.scope_ is sub.nscope);
			auto outer = decl.splitFrom;
			assert(outer.scope_ is nscope);
			assert(outer.splitInto == [decl]);
			sub.defineVar(decl, getVar(outer, false));
		}
		auto r = sub.genCompoundStmt(e);
		if(r.mayPass) {
			foreach(decl; sub.nscope.mergedVars) {
				assert(decl.scope_ is sub.nscope);
				auto outer = decl.mergedInto;
				assert(outer.scope_ is nscope);
				assert(outer.mergedFrom == [decl]);
				defineVar(outer, sub.getVar(decl, false));
			}
		}
		sub.checkEmpty(!!r.isAbort);
		return r;
	}

	Result implStmt(ast_exp.FunctionDef e) {
		defineVar(e, getFunc(e, false, null));
		return Result.passes();
	}

	Result implStmt(ast_exp.CommaExp e) {
		auto r = genStmt(e.e1);
		assert(!r.isReturn && !r.isConditionalReturn, "return in lhs of CommaExp");
		if(r.isAbort) return r;
		return genStmt(e.e2);
	}

	Result implStmt(ast_exp.ReturnExp e) {
		assert(!e.e.constLookup || !ast_ty.hasQuantumComponent(e.e.type));
		auto r = genExprAs(e.e, nscope.getFunction().ret);
		foreach(decl; e.forgottenVars) {
			valForget(getVar(decl, false));
		}
		checkEmpty(false);
		return Result.returns(RetValue(r));
	}

	Result implStmt(ast_exp.IteExp e) {
		auto ite = genIte(e);
		ite.forgetCond(this);
		if(cast(ItePass) ite) return Result.passes();
		if(auto rv = cast(IteAbort) ite) return Result.aborts(rv.witness);
		if(auto rv = cast(IteReturn) ite) return Result.returns(rv.value);
		assert(0, "TODO if-then-else with conditional return");
	}

	Result implStmt(ast_exp.DefineExp e) {
		if(e.isSwap) {
			return implSwap(e);
		}
		auto lhs = e.e1;
		auto rhs = e.e2;
		if(auto ie = cast(ast_exp.IndexExp) rhs) {
			if(ie.byRef) {
				return genIndexRead(ie, lhs);
			}
		}
		if(auto ie = cast(ast_exp.IndexExp) lhs) {
			if(ie.byRef) {
				return genIndexWrite(ie, rhs, e);
			}
		}

		auto pairs = appender!(Expression[2][]);
		flattenDefine(lhs, rhs, pairs);
		auto values = pairs[].map!(p => genExpr(p[1])).array;

		foreach(i, p; pairs[]) {
			if (ast_ty.isEmpty(p[1].type)) {
				foreach(v; values) {
					valDeallocError(v);
				}
				return Result.aborts(values[i].creg);
			}
		}

		foreach(i, p; pairs[]) {
			genLhs(p[0], values[i], p[1].type);
		}
		return Result.passes();
	}

	void flattenDefine(Expression lhs, Expression rhs, ref Appender!(Expression[2][]) ap) {
		if(auto lhsTup = cast(ast_exp.TupleExp)lhs) {
			if(auto rhsTup = cast(ast_exp.TupleExp)rhs) {
				assert(lhsTup.e.length == rhsTup.e.length);
				foreach(i, subl; lhsTup.e) {
					flattenDefine(subl, rhsTup.e[i], ap);
				}
				return;
			}
		}
		Expression[2] p = [lhs, rhs];
		ap.put(p);
	}

	Result genIndexRead(ast_exp.IndexExp ie, Expression lhse) {
		auto lhs = cast(ast_exp.Identifier) lhse;
		assert(lhs, "IndexExp(byRef=true) read not into Identifier");
		assert(lhs.type == ie.type);

		auto chain = IndexChain(ie);
		auto var = chain.base.meaning.getId in vars;
		assert(var && var.value);
		assert(var.decl is chain.base.meaning);

		auto indices = chain.ie.map!(at => genIndex(at.a)).array;
		auto b = defineBorrow(lhs, indices[]);

		Value moveOut(ref Value v, Expression baseTy, CReg[] indices, out Dummy dummy, out DummyTypes[] dummyTypes, ScopeWriter w) {
			if(!indices.length) {
				auto creg = v.creg;
				auto qtype = w.getQTypeRaw(baseTy, creg);
				dummy = Dummy(null, creg, qtype);
				auto r = w.valNewQ(creg, w.qcg.allocDummy(qtype));
				swap(v, r);
				r = w.genSubtype(r, baseTy, ie.type);
				dummyTypes ~= DummyTypes(baseTy);
				return r;
			}
			auto ix = indices[0];
			if(auto tupTy = cast(ast_ty.TupleTy) baseTy) {
				auto types = tupTy.types;
				Value moveOutTuple(ref Value v, size_t i, out Dummy dummy, out DummyTypes dummyTypes, ScopeWriter w) {
					auto vs = w.valUnpack(types, v);
					auto prc = vs[i].creg;
					auto r = moveOut(vs[i], types[i], indices[1..$], dummy, dummyTypes.next , w);
					auto v2 = w.valPack(types, vs);
					v = w.valNewQ(
						prc is r.creg ? v.creg : v2.creg,
						v2.qreg,
					);
					return r;
				}
				if(auto ii = ctx.asIndex(ix, types.length)) {
					dummyTypes ~= DummyTypes(null, []);
					return moveOutTuple(v, ii.get(), dummy, dummyTypes[0], w);
				}
				dummyTypes = new DummyTypes[](types.length);
				Value rec(size_t l, size_t r, ref Value v, out Dummy dummy, ScopeWriter w) {
					if(l + 1 < r) {
						size_t m = l + (r - l) / 2;
						auto cond = CondAny(w.ccg.intCmpLt(ix, w.ctx.literalInt(m)));
						ScopeWriter w0, w1;
						w.genSplit(cond, w0, null, w1, null);
						Value v0, v1;
						w.valSplit(cond, v0, v1, v);
						Dummy dummy0, dummy1;
						auto r0 = rec(m, r, v0, dummy0, w0);
						auto r1 = rec(l, m, v1, dummy1, w1);
						assert(!dummy0.type && !dummy1.type);
						auto creg = w.ccg.cond(cond.creg, dummy0.creg, dummy1.creg);
						auto qtype = w.ccg.cond(cond.creg, dummy0.qtype, dummy1.qtype);
						dummy = Dummy(null, creg, qtype);
						v = w.valMerge(cond, v0, v1);
						auto r_ = w.valMerge(cond, r0, r1);
						w0.checkEmpty(false);
						w1.checkEmpty(false);
						return r_;
					} else {
						auto r_ = moveOutTuple(v, l, dummy, dummyTypes[l], w);
						dummy.type = null;
						return r_;
					}
				}
				return rec(0, types.length, v, dummy, w);
			}
			dummyTypes = [DummyTypes(null, [])];
			Expression itemTy = null;
			if(auto vecTy = cast(ast_ty.VectorTy) baseTy) {
				itemTy = vecTy.next;
			}
			if(auto arrTy = cast(ast_ty.ArrayTy) baseTy) {
				itemTy = arrTy.next;
			}
			if(auto intTy = ast_ty.isFixedIntTy(baseTy)) {
				itemTy = ast_ty.Bool(intTy.isClassical);
			}
			assert(!!itemTy, format("Cannot index %s", baseTy));
			Dummy tmpDummy;
			Value r = w.implIndexSwapOut(v, baseTy, itemTy, ix, tmpDummy);
			Value rr = moveOut(r, itemTy, indices[1..$], dummy, dummyTypes[0].next, w);
			w.implIndexSwapIn(v, baseTy, baseTy, itemTy, ix, tmpDummy, r);
			return rr;
		}
		DummyTypes[] dummyTypes;
		Value r = moveOut(var.value, chain.base.type, indices, b.dummy, dummyTypes, this);
		if(!b.dummy.type) {
			assert(dummyTypes.length);
			b.dummyTypes = dummyTypes;
		}
		assert(b.dummy.type || b.dummyTypes.length);
		defineVar(lhs.meaning, r);
		return Result.passes();
	}

	Result genIndexWrite(ast_exp.IndexExp ie, Expression rhse, ast_exp.DefineExp de) {
		auto rhs = cast(ast_exp.Identifier) rhse;
		assert(rhs, "IndexExp(byRef=true) write not from Identifier");

		Borrow b;
		auto rhsv = getBorrow(rhs, b);
		auto indices = b.indices;

		auto chain = IndexChain(ie);
		auto var = chain.base.meaning.getId() in vars;
		assert(var && var.value);

		auto baseTy1 = typeForDecl(var.decl);
		auto baseTy2 = chain.base.type;

		void moveIn(ref Value v, Value rhsv, Expression baseTy1, Expression baseTy2, CReg[] indices, DummyTypes[] dummyTypes, ScopeWriter w) {
			if(!indices.length) {
				auto tmp = w.valNewQ(b.dummy.creg, w.qcg.allocDummy(b.dummy.qtype));
				assert(b.dummy.type || dummyTypes.length==1 && dummyTypes[0].type);
				auto dummyType = b.dummy.type ? b.dummy.type : dummyTypes[0].type;
				tmp = w.genSubtype(tmp, dummyType, baseTy1);
				w.valUndup(v, tmp);
				w.valForget(tmp);
				v = w.genSubtype(rhsv, rhs.type, baseTy2);
				return;
			}
			auto ix = indices[0];
			Expression arrayTy2 = null;
			bool makeArray = false;
			if(dummyTypes.length > 1) {
				if(auto at1 = cast(ast_ty.ArrayTy) baseTy1) {
					auto nbaseTy1 = ast_ty.vectorTy(at1.next, dummyTypes.length);
					// TODO: the length check is redundant
					auto conv = ast_conv.typeExplicitConversion!true(baseTy1, nbaseTy1, ast_exp.TypeAnnotationType.coercion);
					baseTy1 = nbaseTy1;
					v = w.genConvert(conv, v);
					makeArray = true;
				}
				if(auto at2 = cast(ast_ty.ArrayTy) baseTy2){
					baseTy2 = ast_ty.vectorTy(at2.next, dummyTypes.length);
					makeArray = true;
					arrayTy2 = at2;
				} else {
					assert(!makeArray);
				}
			}
			if(auto tt2 = baseTy2.isTupleTy()) { // TODO: not always needed for vectors
				if(ast_ty.isSubtype(baseTy1, baseTy2)) {
					v = w.genSubtype(v, baseTy1, baseTy2);
					baseTy1 = baseTy2;
				}
				auto tt1 = baseTy1.isTupleTy();
				assert(!!tt1);
				Expression[] types1, types2;
				if(auto tupTy1 = cast(ast_ty.TupleTy) baseTy1) {
					types1 = tupTy1.types;
				} else {
					types1 = iota(tt1.length).map!(i => tt1[i]).array;
				}
				if(auto tupTy2 = cast(ast_ty.TupleTy) baseTy2) {
					types2 = tupTy2.types;
				} else {
					types2 = iota(tt2.length).map!(i => tt2[i]).array;
				}
				assert(types1.length == types2.length);
				void moveInTuple(ref Value v, Value rhsv, size_t i, DummyTypes dummyTypes, ScopeWriter w) {
					auto vs = w.valUnpack(types1, v);
					auto prc = vs[i].creg;
					moveIn(vs[i], rhsv, types1[i], types2[i], indices[1..$], dummyTypes.next, w);
					Expression[] types3;
					if(types1[i] == types2[i]) {
						types3 = types1;
					} else {
						types3 = iota(types1.length).map!(k => i!=k ? types1[k] : types2[k]).array;
					}
					auto v2 = w.valPack(types3, vs);
					v = w.valNewQ(
						prc is rhsv.creg ? v.creg : v2.creg,
						v2.qreg,
					);
					v = genSubtype(v, ast_ty.tupleTy(types3), baseTy2);
				}
				if(auto ii = ctx.asIndex(ix, types2.length)) {
					assert(dummyTypes.length == 1);
					moveInTuple(v, rhsv, ii.get(), dummyTypes[0], w);
					return;
				}
				if(dummyTypes.length == 1 && types2.length != 1) {
					dummyTypes = repeat(dummyTypes[0], types2.length).array;
				}
				assert(dummyTypes.length == types2.length);
				void rec(size_t l, size_t r, ref Value v, Value rhsv, ScopeWriter w) {
					if(l + 1 < r) {
						size_t m = l + (r - l) / 2;
						auto cond = CondAny(w.ccg.intCmpLt(ix, w.ctx.literalInt(m)));
						ScopeWriter w0, w1;
						w.genSplit(cond, w0, null, w1, null);
						Value v0, v1;
						w.valSplit(cond, v0, v1, v);
						Value rhsv0, rhsv1;
						w.valSplit(cond, rhsv0, rhsv1, rhsv);
						rec(m, r, v0, rhsv0, w0);
						rec(l, m, v1, rhsv1, w1);
						v = w.valMerge(cond, v0, v1);
						w0.checkEmpty(false);
						w1.checkEmpty(false);
					} else {
						moveInTuple(v, rhsv, l, dummyTypes[l], w);
					}
				}
				rec(0, types2.length, v, rhsv, w);
				if(makeArray) {
					assert(!!arrayTy2);
					v = w.genSubtype(v, baseTy2, arrayTy2);
				}
				return;
			}
			assert(dummyTypes.length == (b.dummy.type ? 0 : 1));
			Expression itemTy1 = null;
			if(auto vecTy1 = cast(ast_ty.VectorTy) baseTy1) {
				itemTy1 = vecTy1.next;
			}
			if(auto arrTy1 = cast(ast_ty.ArrayTy) baseTy1) {
				itemTy1 = arrTy1.next;
			}
			if(auto intTy1 = ast_ty.isFixedIntTy(baseTy1)) {
				itemTy1 = ast_ty.Bool(intTy1.isClassical);
			}
			assert(!!itemTy1, format("Cannot index %s", baseTy1));
			Expression itemTy2 = null;
			if(auto vecTy2 = cast(ast_ty.VectorTy) baseTy2) {
				itemTy2 = vecTy2.next;
			}
			if(auto arrTy2 = cast(ast_ty.ArrayTy) baseTy2) {
				itemTy2 = arrTy2.next;
			}
			if(auto intTy2 = ast_ty.isFixedIntTy(baseTy2)) {
				itemTy2 = ast_ty.Bool(intTy2.isClassical);
			}
			assert(!!itemTy2, format("Cannot index %s", baseTy2));
			Value r;
			Dummy dummy;
			if(indices.length == 1) {
				r = w.genSubtype(rhsv, rhs.type, itemTy2);
				dummy = b.dummy;
				if(!dummy.type) {
					assert(dummyTypes.length == 1 && dummyTypes[0].next.length == 1);
					dummy.type = dummyTypes[0].next[0].type;
					assert(!!dummy.type);
				}
			} else {
				r = w.implIndexSwapOut(v, baseTy1, itemTy1, ix, dummy);
				DummyTypes[] ndummyTypes;
				if(dummyTypes.length) {
					assert(dummyTypes.length == 1);
					ndummyTypes = dummyTypes[0].next;
				}
				moveIn(r, rhsv, itemTy1, itemTy2, indices[1..$], ndummyTypes, w);
			}
			w.implIndexSwapIn(v, baseTy1, baseTy2, itemTy2, ix, dummy, r);
		}

		moveIn(var.value, rhsv, baseTy1, baseTy2, indices, b.dummyTypes, this);

		if(chain.base.type == typeForDecl(chain.base.meaning)) {
			var.decl = chain.base.meaning;
		} else {
			// Create temporary decl
			auto vd = new ast_decl.VarDecl(null);
			vd.loc = ie.loc;
			vd.vtype = chain.base.type;
			var.decl = vd;
		}
		return Result.passes();
	}

	Result implStmt(ast_exp.AssignExp e) {
		ast_decl.Declaration[void*] declMap;

		foreach(repl; e.replacements) {
			declMap[cast(void*)repl.previous] = repl.new_;
		}

		auto v = genExpr(e.e2);

		// TODO
		valForget(genExpr(e.e1));

		// HACK?
		auto lhs2 = e.e1.copy(ast_exp.Expression.CopyArgs(true, true));
		assert(lhs2);
		foreach(id; lhs2.freeVars) {
			if (auto d = cast(void*)id.meaning in declMap) {
				id.meaning = *d;
			}
		}
		lhs2 = lhs2.copy(ast_exp.Expression.CopyArgs(false, true));
		ast_sem.expressionSemantic(lhs2, semContext(false));
		genLhs(lhs2, v, e.e2.type);

		return Result.passes();
	}

	Result implStmt(ast_exp.CatAssignExp e) {
		auto lhs = cast(ast_exp.Identifier) e.e1;
		assert(lhs, "TODO AssignExp with non-Identifier LHS");

		auto rhs = e.e2;
		assert(!rhs.constLookup, "CatAssignExp RHS const");

		auto var1 = cast(ast_decl.VarDecl) lhs.meaning;
		assert(var1, "LHS of assignment not VarDecl");
		assert(e.replacements.length == 1);
		assert(e.replacements[0].previous is var1);
		auto var2 = cast(ast_decl.VarDecl) e.replacements[0].new_;
		assert(var2, "LHS of assignment not VarDecl");

		Value rhsV = genExpr(rhs);
		Value lhsV = genExpr(lhs);
		auto v = genConcat(var2.vtype, lhsV, lhs.type, rhsV, rhs.type);
		defineVar(var2, v);
		return Result.passes();
	}

	Result implStmt(TokenType op)(BinaryExp!op e) if(op != Tok!opAssign && op != Tok!opConcatAssign && is(BinaryExp!op: ast_exp.AAssignExp)) {
		auto lowered = ast_low.getLowering!op(e, nscope);
		assert(lowered, format("Failed to lower expression: %s", e));
		return genStmt(lowered);
	}

	Result implStmt(ast_exp.WithExp e) {
		BorrowScope oldBscope;
		auto bsc = new BorrowScope();

		oldBscope = bscope;
		bscope = bsc;
		Result r1 = implStmt(e.trans);
		bscope = oldBscope;
		assert(!r1.isReturn && !r1.isConditionalReturn, "TODO return in with statement");
		if(r1.isAbort) return r1;

		Result r2 = implStmt(e.bdy);
		assert(!r2.isReturn && !r2.isConditionalReturn, "TODO return in with statement");
		if(r2.isAbort) return r2;

		oldBscope = bscope;
		bscope = bsc;
		bsc.isItrans = true;
		Result r3 = implStmt(e.itrans);
		bscope = oldBscope;
		assert(!r3.isReturn && !r3.isConditionalReturn, "TODO return in with statement");
		if(r3.isAbort) return r3;

		return Result.passes();
	}

	Result implSwap(ast_exp.DefineExp orig) {
		auto origVars = cast(ast_exp.TupleExp)orig.e2;
		assert(origVars && origVars.e.length == 2);

		auto ie1 = cast(ast_exp.IndexExp)origVars.e[0];
		assert(!!ie1);
		auto ie2 = cast(ast_exp.IndexExp)origVars.e[1];
		assert(!!ie2);
		if(cast(ast_exp.IndexExp)ie1.e || cast(ast_exp.IndexExp)ie2.e) {
			auto lowering = ast_low.getSwapLowering(orig, nscope);
			assert(!!lowering, format("Failed to lower swap: %s", orig));
			return genStmt(lowering);
		}
		auto arrIn = cast(ast_exp.Identifier)ie1.e;
		assert(arrIn && ie2.e == arrIn);
		auto index1 = ie1.a;
		auto index2 = ie2.a;

		auto origVars2 = cast(ast_exp.TupleExp)orig.e1;
		assert(origVars2);
		assert(origVars2.e.length == 2);
		auto ie3 = cast(ast_exp.IndexExp)origVars2.e[0];
		assert(ie3);
		auto arrOut = cast(ast_exp.Identifier)ie3.e;
		assert(ie3.a == index2);
		auto ie4 = cast(ast_exp.IndexExp)origVars2.e[1];
		assert(ie4);
		assert(ie4.e == arrOut);
		assert(ie4.a == index1);

		assert(arrIn.meaning !is arrOut.meaning);

		auto outTy = typeForDecl(arrOut.meaning);

		assert(arrIn.type == typeForDecl(arrIn.meaning));
		assert(arrOut.type == outTy);

		Value v = getVar(arrIn.meaning, false);

		if (auto tupTyOut = cast(ast_ty.TupleTy)outTy) {
			auto i1Lit = index1.asIntegerConstant(true);
			auto i2Lit = index2.asIntegerConstant(true);
			assert(i1Lit, format("not a constant: %s", index1));
			assert(i2Lit, format("not a constant: %s", index2));
			auto i1 = i1Lit.get().to!size_t();
			auto i2 = i2Lit.get().to!size_t();
			auto tupTyIn = cast(ast_exp.TupleTy)arrIn.type;
			assert(tupTyIn);
			auto ty1 = tupTyIn.types[i1];
			auto ty2 = tupTyIn.types[i2];
			assert(tupTyOut.types[i2] == ty1 && tupTyOut.types[i1] == ty2, format("item type didn't change on swap(%s, %s): %s -> %s", i1, i2, arrIn.type, outTy));

			Value[] vals = valUnpack(tupTyIn.types, v);
			swap(vals[i1], vals[i2]);
			defineVar(arrOut.meaning, valPack(tupTyOut.types, vals));
			return Result.passes();
		}

		CReg i1 = genIndex(index1);
		CReg i2 = genIndex(index2);

		v = genSubtype(v, arrIn.type, outTy);

		Expression itemTy;
		CReg len;
		bool packArray;
		if (auto vecTy = cast(ast_ty.VectorTy)outTy) {
			itemTy = vecTy.next;
			len = getVectorLength(vecTy);
			packArray = false;
		} else if (auto arrTy = cast(ast_ty.ArrayTy)outTy) {
			itemTy = arrTy.next;
			v = valArrayToVector(itemTy, len, v);
			packArray = true;
		} else if (auto intTy = ast_ty.isFixedIntTy(outTy)) {
			if (intTy.isClassical) {
				auto bits = getNumericBits(intTy);
				ccg.checkLtInt(true, i1, bits);
				ccg.checkLtInt(true, i2, bits);
				CReg m1 = ccg.intPow2(i1);
				CReg m2 = ccg.intPow2(i2);
				CReg m = ccg.intAdd(m1, m2);
				CReg c1 = ccg.intCmpEq(ccg.intBitAnd(v.creg, m1), m1);
				CReg c2 = ccg.intCmpEq(ccg.intBitAnd(v.creg, m2), m2);
				CReg r = ccg.emitPureOp("cond", [ccg.boolNe(c1, c2), v.creg, ccg.intBitXor(v.creg, m)]);
				if(intTy.isSigned) r = ccg.intMakeSigned(bits, r);
				defineVar(arrOut.meaning, valNewC(r));
				return Result.passes();
			}
			itemTy = ast_ty.Bool(false);
			len = getNumericBits(intTy);
			packArray = false;
		} else {
			assert(0, format("item swap on %s", outTy));
		}

		CReg cr = null;
		if (v.hasClassical) {
			cr = v.creg;
			cr = ccg.boxReplace(ctypeSilqTuple, len, cr, i1, ccg.boxIndex(ctypeSilqTuple, len, v.creg, i2));
			cr = ccg.boxReplace(ctypeSilqTuple, len, cr, i2, ccg.boxIndex(ctypeSilqTuple, len, v.creg, i1));
		}

		QReg qr = null;
		if (v.hasQuantum) {
			CReg qtypes = getVectorQTypes(itemTy, len, v.creg);
			CReg qtypes2;
			if (cr && typeHasQDep(itemTy)) {
				qtypes2 = getVectorQTypes(itemTy, len, cr);
			} else {
				qtypes2 = qtypes;
			}

			CReg isEq = ccg.intCmpEq(i1, i2);
			CReg isLt = ccg.intCmpLt(i1, i2);

			QCGen cgNe = qcg.withCond(CondAny(isEq, false));
			QCGen cgLt = cgNe.withCond(CondAny(isLt, true));
			QCGen cgGt = cgNe.withCond(CondAny(isLt, false));

			// First split into lt/gt
			auto qrNe = new QReg();
			auto qrEq = new QReg();
			auto qrLt = new QReg();
			auto qrGt = new QReg();
			qcg.writeQOp(opCSplit, [qrNe, qrEq], [isEq], [], [v.qreg]);
			cgNe.writeQOp(opCSplit, [qrGt, qrLt], [isLt], [], [qrNe]);

			qrLt = implSwapQuantum(cgLt, qrLt, len, qtypes, qtypes2, i1, i2);
			qrGt = implSwapQuantum(cgGt, qrGt, len, qtypes, qtypes2, i2, i1);

			qrNe = new QReg();
			cgNe.writeQOp(opCMerge, [qrNe], [isLt], [], [qrGt, qrLt]);
			qr = new QReg();
			qcg.writeQOp(opCMerge, [qr], [isEq], [], [qrNe, qrEq]);
		}

		v = valNewQ(cr, qr);
		if (packArray) {
			v = valVectorToArray(len, v);
		}
		defineVar(arrOut.meaning, v);

		return Result.passes();
	}

	static QReg implSwapQuantum(QCGen qcg, QReg qr, CReg len, CReg qtypes, CReg qtypes2, CReg i1, CReg i2) {
		// Swap qr[i1] and qr[i2], where i1 < i2
		auto ccg = qcg.ccg;
		auto ctx = ccg.ctx;

		auto left = new QReg();
		auto v1t = new QReg();
		auto mid = new QReg();
		auto v2t = new QReg();
		auto right = new QReg();

		auto midLen = ccg.intSub(ccg.intSub(i2, i1), ctx.intOne);
		auto rightLen = ccg.intSub(ccg.intSub(len, i2), ctx.intOne);
		auto slices = [i1, ctx.intOne, midLen, ctx.intOne, rightLen];

		auto parts = qcg.uncat(len, qtypes, slices, qr);
		swap(parts[1], parts[3]);
		return qcg.cat(len, qtypes2, slices, parts);
	}

	void genNoopLoop(ast_exp.CompoundExp s) {
		auto sc = s.blscope_;
		assert(sc);

		// stderr.writef("outer scope %s\n", cast(void*)nscope);
		// stderr.writef("inner scope %s\n", cast(void*)sc);
		foreach(inner1; sc.splitVars) {
			auto id = inner1.getId;
			// stderr.writef("var %s\n", id);
			// stderr.writef("  inner1 %s scope %s\n", cast(void*)inner1, cast(void*)inner1.scope_);
			assert(inner1.scope_ is sc);

			assert(!inner1.mergedFrom);
			assert(!inner1.mergedInto);

			auto outer1 = inner1.splitFrom;
			// stderr.writef("  outer1 %s scope %s\n", cast(void*)outer1, cast(void*)outer1.scope_);
			assert(outer1.getId == id);
			assert(outer1.splitInto.length == 2);
			assert(outer1.splitInto[1] is inner1);
			assert(!outer1.mergedInto);
			assert(outer1.scope_ is nscope);

			auto mid = outer1.splitInto[0];
			// stderr.writef("  mid %s scope %s\n", cast(void*)mid, cast(void*)mid.scope_);
			assert(mid.getId == id);
			assert(mid.splitFrom is outer1);

			assert(!mid.splitInto);
			assert(!mid.mergedFrom);

			auto outer2 = mid.mergedInto;
			// stderr.writef("  outer2 %s scope %s\n", cast(void*)outer2, cast(void*)outer2.scope_);
			assert(outer2.scope_ is nscope);
			assert(outer2.getId == id);
			assert(!outer2.splitFrom);
			assert(outer2.mergedFrom.length == 2);
			assert(outer2.mergedFrom[1] is mid);

			auto inner2 = outer2.mergedFrom[0];
			// stderr.writef("  inner2 %s scope %s\n", cast(void*)inner2, cast(void*)inner2.scope_);
			assert(inner2.scope_ is sc);
			assert(inner2.mergedInto is outer2);
			assert(!inner2.splitFrom);
			assert(!inner2.splitInto);

			auto val = getVar(outer1, false);
			val = genSubtype(val, typeForDecl(outer1), typeForDecl(outer2));
			defineVar(outer2, val);
		}
	}

	Result implStmt(ast_exp.ForExp e) {
		assert(ctx.options.compileLoopsAsNoOps, "TODO ForExp");
		assert(e.fescope_ == e.bdy.blscope_);
		genExpr(e.left);
		genExpr(e.right);
		if(e.step) genExpr(e.step);
		genNoopLoop(e.bdy);
		return Result.passes();
	}

	Result implStmt(ast_exp.WhileExp e) {
		assert(ctx.options.compileLoopsAsNoOps, "TODO WhileExp");
		auto v = genExprAs(e.cond, ast_ty.Bool(true));
		if(v.creg is ctx.boolTrue) {
			auto r = new CReg();
			// at e.loc.line
			ccg.writeCOp(opAbort, [r], []);
			return Result.aborts(r);
		}
		genNoopLoop(e.bdy);
		return Result.passes();
	}

	Result implStmt(ast_exp.RepeatExp e) {
		assert(ctx.options.compileLoopsAsNoOps, "TODO RepeatExp");
		genExpr(e.num);
		genNoopLoop(e.bdy);
		return Result.passes();
	}

	Result implStmt(Expression e) {
		assert(e.constLookup);
		Value v = genExpr(e);
		if (ast_ty.isEmpty(e.type)) {
			return Result.aborts(v.creg);
		}
		valForget(v);
		return Result.passes();
	}

	CReg getVectorLength(ast_ty.VectorTy ty) {
		try {
			return getExprNat(ty.num);
		} catch(AssertError exc) {
			exc.msg = format("%s\nat %s, vector length: %s", exc.msg, ty.loc, ty);
			throw exc;
		}
	}

	CReg getNumericBits(ast_ty.FixedIntTy intTy) {
		auto e = intTy.bits;
		assert(e);
		try {
			return getExprNat(e);
		} catch(AssertError exc) {
			exc.msg = format("%s\nat %s, numeric bits: %s", exc.msg, e.loc, e);
			throw exc;
		}
	}

	CReg getExprNat(Expression expr) {
		ExprInfo ei = ctx.exprEval(expr);
		for(auto par = this; par; par = par.parent) {
			if(auto p = ei in par.cachedNat) return *p;
		}

		auto sc = evalScope(ei);
		auto subsc = sc.typeScope();
		auto r = subsc.implExprNat(ei.expr);
		subsc.checkEmpty(false);

		sc.cachedNat[ei] = r;
		return r;
	}

	CReg implExprNat(Expression expr) {
		return genExprAs(expr, ast_ty_Nt()).creg;
	}

	void pinType(Expression ty) {
		assert(ast_ty.isType(ty), format("not a type: %s of type %s", ty, ty.type));
		// Make sure the type is evaluated in this scope to remove rendundancy
		// in the sub-scopes.
		getRTTI(ty);
	}

	RTTI getRTTI(Expression ty) {
		assert(ast_ty.isType(ty), format("not a type: %s of type %s", ty, ty.type));
		try {
			if(auto r = getSimpleRTTI(ty)) {
				return r;
			}
			ExprInfo ei = ctx.exprEval(ty);
			ty = ei.expr;
			if(auto r = getSimpleRTTI(ty)) {
				return r;
			}
			for(auto par = this; par; par = par.parent) {
				if(auto p = ei in par.cachedRTTI) return *p;
			}
			auto sc = evalScope(ei);
			assert(ei !in sc.cachedRTTI);

			auto r = new RTTI(sc, ei);
			sc.cachedRTTI[ei] = r;
			if(!cast(ast_ty.Type) ty && !ast_ty.isFixedIntTy(ty)) {
				auto subsc = sc.typeScope();
				r._packed = subsc.genValue(ty).creg;
				subsc.checkEmpty(false);
			}
			return r;
		} catch(AssertError exc) {
			exc.msg = format("%s\nat %s, type: %s", exc.msg, ty.loc, ty);
			throw exc;
		}
	}

	RTTI getSimpleRTTI(Expression ty) {
		ty = ty.eval();
		if(!typeHasQuantum(ty)) {
			if(!typeHasClassical(ty)) {
				return ctx.unitRTTI;
			}
			return ctx.classicalRTTI;
		}
		if(ty == ast_ty.Bool(false)) {
			return ctx.qubitRTTI;
		}
		if(auto prodTy = cast(ast_ty.ProductTy) ty) {
			return ctx.qfuncRTTI;
		}
		return null;
	}

	CReg getVectorQTypes(Expression itemTy, CReg len, CReg cc) {
		if(len is ctx.intZero) {
			return ccg.boxPack(ctypeQtArray, []);
		}
		if(!cc || !typeHasQDep(itemTy)) {
			auto qti = getQTypeRaw(itemTy, null);
			return ccg.boxRepeat(ctypeQtArray, len, qti);
		}
		auto qtf = ccg.funcPack("silq_builtin.qtype_vec_d", [len, getRTTI(itemTy).qtypeF, cc]);
		return ccg.funcApply("silq_builtin.iter_qtypes", [qtf, len]);
	}

	CReg getVectorQType(Expression itemTy, CReg len, CReg cc) {
		if(len is ctx.intZero) {
			return ctx.qtUnit;
		}
		if(!cc || !typeHasQDep(itemTy)) {
			auto items = getQTypeRaw(itemTy, null);
			return ccg.qtVector(items, len);
		}
		if(auto p = ctx.asUnroll(len)) {
			auto n = p.get();
			auto items = iota(n).map!(i => getQTypeRaw(itemTy, ccg.boxIndex(ctypeSilqTuple, n, cc, i))).array;
			return ccg.qtTuple(items);
		}
		return ccg.qtArray(len, getVectorQTypes(itemTy, len, cc));
	}

	CReg getQTypeRaw(Expression ty, CReg cc, bool mayUseRTTI = true) {
		assert(ty);
		assert(ty.isSemEvaluated());
		if(!typeHasQuantum(ty)) {
			return ctx.qtUnit;
		}
		if(ty == ast_ty.Bool(false)) {
			return ctx.qtQubit;
		}
		if(cast(ast_ty.ProductTy) ty) {
			assert(cc);
			return ccg.qfuncQType(cc);
		}
		if(cc && !typeHasQDep(ty)) {
			cc = null;
		}
		ScopeWriter sc;
		if(cc) {
			assert(typeHasClassical(ty));
			sc = this;
		} else {
			auto ei = ctx.exprEval(ty);
			if(mayUseRTTI) {
				for(sc = this; sc; sc = sc.parent) {
					if(ei in sc.cachedRTTI) break;
				}
			}
			if(!sc) sc = evalScope(ei);
		}
		return sc.getQTypeImpl(ty, cc, mayUseRTTI);
	}

	CReg getQTypeImpl(Expression ty, CReg cc, bool mayUseRTTI) {
		if(auto tupTy = cast(ast_ty.TupleTy) ty) {
			size_t n = tupTy.types.length;
			auto items = iota(n).map!(i => getQTypeRaw(tupTy.types[i], ccg.boxIndex(ctypeSilqTuple, n, cc, i))).array;
			return ccg.qtTuple(items);
		}
		if(auto intTy = ast_ty.isFixedIntTy(ty)) {
			assert(!intTy.isClassical);
			assert(!cc);
			auto bits = getNumericBits(intTy);
			return ccg.qtVector(ctx.qtQubit, bits);
		}
		if(auto vecTy = cast(ast_ty.VectorTy) ty) {
			auto len = getVectorLength(vecTy);
			return getVectorQType(vecTy.next, len, cc);
		}
		if(auto arrTy = cast(ast_ty.ArrayTy) ty) {
			CReg len = ccg.getArrayLength(cc);
			if(typeHasQDep(arrTy.next)) {
				cc = ccg.getArrayItems(cc);
			} else {
				cc = null;
			}
			return getVectorQType(arrTy.next, len, cc);
		}
		if(auto varTy = cast(ast_ty.VariadicTy) ty) {
			assert(0, "TODO variadics");
		}
		assert(!cast(ast_ty.Type) ty, format("can't get qtype for %s", ty));
		assert(mayUseRTTI);
		return ccg.funcApply(getRTTI(ty).qtypeF, [cc]);
	}

	CReg getQType(Expression ty, Value val) {
		assert(val);
		if(!val.hasQuantum) return ctx.qtUnit;
		return getQTypeRaw(ty, val.creg);
	}

	Value genVectorPromote(Expression itemTy, CReg len, CReg arg) {
		if(auto p = ctx.asUnroll(len)) {
			auto n = p.get();
			auto items = iota(n).map!(i => genPromote(itemTy, ccg.boxIndex(ctypeSilqTuple, n, arg, i))).array;
			return valPack(itemTy.repeat(n).array, items);
		}
		auto promoteF = getRTTI(itemTy).promoteF;

		auto flags = qpromoteFlags(itemTy);
		assert(!(flags & ConvertFlags.check), "check in promotion");

		CReg cr;
		if(typeHasClassical(itemTy)) {
			if(flags & ConvertFlags.classical) {
				auto bound = ccg.funcPack("silq_builtin.convert_vec_c", [promoteF, len, arg]);
				cr = ccg.funcApply("silq_builtin.iter_tuple", [bound, len]);
			} else {
				cr = arg;
			}
		}
		if(!(flags & ConvertFlags.quantum)) {
			return valNewC(cr);
		}

		string func;
		CReg qt;
		if(!typeHasQDep(itemTy)) {
			func = "silq_builtin.promote_vec_i";
			qt = getQTypeRaw(itemTy, null);
		} else {
			func = "silq_builtin.promote_vec_d";
			qt = getVectorQTypes(itemTy, len, cr);
		}
		auto r = valNewQ(cr, itemTy);
		qcg.writeQOp(format("qfree_call[%s]", func), [r.qreg], [promoteF, len, qt, arg, len], [], []);
		return r;
	}

	Value genPromote(Expression ty, CReg arg, bool mayUseRTTI = true) {
		if(qpromoteFlags(ty) == ConvertFlags.noop) {
			return valNewC(arg);
		}
		if(ty == ast_ty.Bool(false)) {
			return valAllocQubit(arg);
		}
		if(auto prodTy = cast(ast_ty.ProductTy) ty) {
			return valNewC(ccg.qfuncPack(arg, ctx.qtUnit));
		}
		if(auto tupTy = cast(ast_ty.TupleTy) ty) {
			size_t n = tupTy.types.length;
			auto items = iota(n).map!(i => genPromote(tupTy.types[i], ccg.boxIndex(ctypeSilqTuple, n, arg, i))).array;
			return valPack(tupTy.types, items);
		}
		if(auto intTy = ast_ty.isFixedIntTy(ty)) {
			auto bits = getNumericBits(intTy);
			auto r = valNewQt(null, ccg.qtVector(ctx.qtQubit, bits));
			if(r.hasQuantum) {
				qcg.writeQOp(opAllocUint, [r.qreg], [bits, arg], [], []);
			}
			return r;
		}
		if(auto vecTy = cast(ast_ty.VectorTy) ty) {
			auto len = getVectorLength(vecTy);
			return genVectorPromote(vecTy.next, len, arg);
		}
		if(auto arrTy = cast(ast_ty.ArrayTy) ty) {
			auto len = ccg.getArrayLength(arg);
			arg = ccg.getArrayItems(arg);
			auto r = genVectorPromote(arrTy.next, len, arg);
			return valVectorToArray(len, r);
		}
		assert(mayUseRTTI);
		auto promoteF = getRTTI(ty).promoteF;
		auto cr = ccg.funcApply(promoteF, [arg]);
		auto r = valNewQ(cr, ty);
		qcg.writeQOp(opCallQfree(null), [r.qreg], [promoteF, arg], [], []);
		return r;
	}

	CReg genVectorMeasure(Expression itemTy, CReg len, Value arg) {
		if(auto p = ctx.asUnroll(len)) {
			auto n = p.get();
			auto elements = valUnpack(itemTy.repeat(n).array, arg);
			auto items = iota(n).map!(i => genMeasure(itemTy, elements[i])).array;
			return ccg.boxPack(ctypeSilqTuple, items);
		}
		auto measureF = getRTTI(itemTy).measureF;
		CReg r = new CReg();
		if(!typeHasQDep(itemTy)) {
			qcg.writeMOp("call[silq_builtin.measure_vec_i]", [r], [], [measureF, len, getQTypeRaw(itemTy, null), arg.creg, len], [], [arg.qreg]);
		} else {
			CReg qtypes = getVectorQTypes(itemTy, len, arg.creg);
			qcg.writeMOp("call[silq_builtin.measure_vec_d]", [r], [], [measureF, len, qtypes, arg.creg, len], [], [arg.qreg]);
		}
		return r;
	}

	CReg genMeasure(Expression ty, Value arg, bool mayUseRTTI = true) {
		if(!typeHasQuantum(ty)) {
			qcg.deallocUnit(arg.qreg);
			return arg.creg;
		}
		if(ty == ast_ty.Bool(false)) {
			auto r = new CReg();
			qcg.writeMOp(opMeasureQubit, [r], [], [], [], [arg.qreg]);
			return r;
		}
		if(auto prodTy = cast(ast_ty.ProductTy) ty) {
			auto cfunc = ccg.qfuncInner(arg.creg);
			if(!arg.hasQuantum) return cfunc;
			auto qtype = ccg.qfuncQType(arg.creg);
			if(qtype is ctx.qtUnit) return cfunc;
			auto bv = new CReg();
			qcg.writeMOp(opMeasureBitvec, [bv], [], [qtype], [], [arg.qreg]);
			string op = productTyIsMoved(prodTy) ? "silq_builtin.qfunc_moved_bitvec" : "silq_builtin.qfunc_const_bitvec";
			return ccg.funcPack(op, [cfunc, qtype, bv]);
		}
		if(auto tupTy = cast(ast_ty.TupleTy) ty) {
			size_t n = tupTy.types.length;
			auto elements = valUnpack(tupTy.types, arg);
			auto items = iota(n).map!(i => genMeasure(tupTy.types[i], elements[i])).array;
			return ccg.boxPack(ctypeSilqTuple, items);
		}
		if(auto intTy = ast_ty.isFixedIntTy(ty)) {
			auto bits = getNumericBits(intTy);
			auto r = new CReg();
			qcg.writeMOp(opMeasureUint, [r], [], [bits], [], [arg.qreg]);
			if(intTy.isSigned) r = ccg.intMakeSigned(bits, r);
			return r;
		}
		if(auto vecTy = cast(ast_ty.VectorTy) ty) {
			auto len = getVectorLength(vecTy);
			return genVectorMeasure(vecTy.next, len, arg);
		}
		if(auto arrTy = cast(ast_ty.ArrayTy) ty) {
			CReg len;
			arg = valArrayToVector(arrTy.next, len, arg);
			auto r = genVectorMeasure(arrTy.next, len, arg);
			return ccg.boxPack(ctypeSilqArray, [len, r]);
		}
		assert(mayUseRTTI);
		auto r = new CReg();
		qcg.writeMOp(opCallMeasureIndirect, [r], [], [getRTTI(ty).measureF, arg.creg], [], [arg.qreg]);
		return r;
	}

	CallInfo prepCall(Expression targetExpr, Expression argExpr, Expression retType, bool isReversed) {
		auto callTy = cast(ast_ty.ProductTy) targetExpr.type;
		assert(!!callTy, format("call to non-ProductTy %s", targetExpr));

		bool makeClassical = false;
		{
			Expression retExpr = callTy.tryApply(argExpr, callTy.isSquare);
			auto retClassical = retExpr.getClassical();
			if(retType != retExpr && retType != retExpr) {
				assert(!isReversed, "TODO make-classical reversed call");
				assert(retType == retClassical, format("function result type mismatch: got %s, want %s or %s", retType, retExpr, retClassical));
				assert(!ast_ty.hasQuantumComponent(argExpr.type), format("make-classical call with quantum argument, type: %s", argExpr.type));
				assert(callTy.annotation >= ast_ty.Annotation.qfree, "make-classical call not qfree");
				makeClassical = true;
				retType = retExpr;
			}
		}

		auto target = genExpr(targetExpr);
		auto targetF = target.funcInfo;
		bool isTuple = false;
		Expression[] params;
		Expression[] args;
		if(callTy.isTuple || (targetF && targetF.fd.isTuple)) {
			if(auto argTuple = cast(ast_exp.TupleExp) argExpr) {
				if(auto tdom = callTy.dom.isTupleTy()) {
					isTuple = true;
					args = argTuple.e;
					params = iota(tdom.length).map!(i => tdom.opIndex(i)).array;
				}
			}
		}
		if(!isTuple) {
			if(targetF && targetF.fd.isTuple) {
				// Function was defined as isTuple, but we can't call it that way.
				// Do indirect call.
				targetF = null;
			}
			if(callTy.isTuple) {
				callTy = callTy.setTuple(false);
				assert(callTy);
			}
			params = [callTy.dom];
			args = [argExpr];
		} else if(targetF && !targetF.fd.isTuple) {
			// Function was defined as !isTuple, but we might need `isTuple`
			// for the call. Do indirect call instead.
			targetF = null;
		}
		assert(!targetF || isTuple == targetF.fd.isTuple);

		size_t n = params.length;
		assert(args.length == n);
		auto isConst = callTy.isConstForReverse();
		auto ai = new ArgInfo[n];
		foreach(i, paramTy; params) {
			bool paramConst = isConst[callTy.isTuple ? i : 0];
			assert(!targetF || paramConst == targetF.params[i].isConst || !ast_ty.hasQuantumComponent(paramTy), format("constness mismatch for call to %s, param #%s/%s of type %s", targetF.prettyName, i, params.length, paramTy));
			assert(paramConst == args[i].constLookup || !ast_ty.hasQuantumComponent(paramTy), format("constness mismatch for call to %s, param #%s/%s of type %s", targetExpr, i, params.length, paramTy));
			ai[i].ty = paramTy;
			ai[i].expr = args[i];
			ai[i].isConst = paramConst;
			if(isReversed && !paramConst) {
				// Will be handled by `genLhs` later.
				assert(!makeClassical);
				ai[i].val = valNewQ(null, paramTy);
				continue;
			}
			ai[i].val = genExprAs(args[i], makeClassical ? paramTy.getClassical() : paramTy);
		}

		CallInfo ci;
		ci.target = target;
		ci.targetF = targetF;
		ci.isTuple = isTuple;
		ci.retType = retType;
		ci.makeClassical = makeClassical;
		ci.hasQuantum = typeHasQuantum(callTy);
		ci.captureMoved = productTyIsMoved(callTy);
		ci.effect = callTy.annotation;
		ci.args = ai;
		if (targetF) {
			assert(targetF.captures.all!(cap => !cap.hasQuantum || cap.isMoved == ci.captureMoved));
		}
		return ci;
	}

	Value[] unpackIndirect(ref CReg cPacked, ref QReg qcPacked, ref QReg qiPacked, Expression[] types, bool[] isConst, bool isTuple) {
		size_t n = types.length;
		assert(isConst.length == n);
		auto args = types.map!(ty => valNewQ(ty)).array;

		if(!isTuple) {
			assert(n == 1);
			cPacked = args[0].creg;
			if(isConst[0]) {
				qcPacked = new QReg();
				qiPacked = null;
				qcg.writeQOp(opDup, [args[0].qreg], [], [qcPacked], []);
			} else {
				qcPacked = null;
				qiPacked = args[0].qreg;
			}
			return args;
		}

		cPacked = new CReg();
		auto nr = ctx.literalInt(n);
		foreach(i, arg; args) {
			if(!arg.creg) continue;
			ccg.writeCOp(format("box_index[%s]", ctypeSilqTuple), [arg.creg], [nr, cPacked, ctx.literalInt(i)]);
		}

		auto qcTypes = new CReg[n];
		auto qcArgs = new QReg[n];
		auto qiTypes = new CReg[n];
		auto qiArgs = new QReg[n];

		foreach(i, ty; types) {
			auto v = args[i];
			auto qtype = getQType(ty, v);
			if(isConst[i]) {
				qcTypes[i] = qtype;
				qcArgs[i] = v.qreg;
				qiTypes[i] = ctx.qtUnit;
				qiArgs[i] = null;
			} else {
				qcTypes[i] = ctx.qtUnit;
				qcArgs[i] = null;
				qiTypes[i] = qtype;
				qiArgs[i] = v.qreg;
			}
		}
		if(qcArgs.any!(r => !!r)) {
			qcPacked = new QReg();
			QReg tmp = qcg.dup(qcPacked);
			qcg.writeQOp(opUnpack(n), qcArgs, qcTypes, [], [tmp]);
		}
		if(qiArgs.any!(r => !!r)) {
			qiPacked = new QReg();
			qcg.writeQOp(opUnpack(n), qiArgs, qiTypes, [], [qiPacked]);
		}

		return args;
	}

	void delegate() packIndirect(CallInfo ci, ref CReg[] cCall, ref QReg[] qcCall, ref QReg[] qiCall, bool isReversed) {
		auto targetC = ci.target.creg;
		auto targetQ = ci.target.qreg;
		assert(targetC, "failed to evaluate call target");
		QReg qcCap = null, qiCap = null;
		if(ci.hasQuantum) {
			targetC = ccg.qfuncInner(targetC);
			if(ci.captureMoved) {
				assert(!isReversed);
				qiCap = targetQ;
			} else {
				qcCap = targetQ;
			}
		} else {
			assert(!targetQ);
		}

		size_t n = ci.args.length;
		auto cArgs = new CReg[n];
		auto qcArgs = new QReg[n];
		auto qiArgs = new QReg[n];
		auto qcTypes = new CReg[n];
		auto qiTypes = new CReg[n];
		foreach(i, arg; ci.args) {
			auto v = arg.val;
			cArgs[i] = v.creg;
			auto qtype = getQType(arg.ty, v);
			if(arg.isConst) {
				qcTypes[i] = qtype;
				qcArgs[i] = v.qreg;
				qiTypes[i] = ctx.qtUnit;
				qiArgs[i] = null;
			} else {
				qcTypes[i] = ctx.qtUnit;
				qcArgs[i] = null;
				qiTypes[i] = qtype;
				qiArgs[i] = v.qreg;
			}
		}
		if(!ci.isTuple) {
			assert(n == 1);
			cCall = [targetC, cArgs[0]];
			qcCall = [qcCap, qcArgs[0]];
			qiCall = [qiCap, qiArgs[0]];
			return null;
		}

		cCall = [targetC, ccg.boxPack(ctypeSilqTuple, cArgs)];
		qcCall = [qcCap, qcg.pack(qcTypes, qcArgs)];

		if (!isReversed) {
			qiCall = [qiCap, qcg.pack(qiTypes, qiArgs)];
			return null;
		}
		if (qiArgs.all!(arg => !arg)) {
			qiCall = [qiCap, null];
			return null;
		}

		auto qiPacked = new QReg();
		qiCall = [qiCap, qiPacked];
		return () {
			qcg.writeQOp(opUnpack(n), qiArgs, qiTypes, [], [qiPacked]);
		};
	}

	Value genNoopConvert(Value v, Expression fromTy, Expression toTy) {
		if(v.hasQuantum && !typeHasQuantum(toTy)) {
			if(fromTy && ast_ty.isEmpty(fromTy)) {
				qcg.deallocError(v.qreg);
			} else {
				qcg.deallocUnit(v.qreg);
			}
			v = valNewC(v.creg);
		}
		if(v.hasClassical && !typeHasClassical(toTy)) {
			v = valNewQ(null, v.qreg);
		}
		return v;
	}

	Value genSubtype(Value v, Expression fromTy, Expression toTy) {
		assert(fromTy.isSemEvaluated());
		assert(toTy.isSemEvaluated());
		if(fromTy == toTy) return genNoopConvert(v, fromTy, toTy);
		auto conv = ast_conv.typeExplicitConversion!true(fromTy, toTy, ast_exp.TypeAnnotationType.annotation);
		assert(conv, format("not a subtype: %s -> %s", fromTy, toTy));
		return genConvert(conv, v);
	}

	Value genCoerce(Value v, Expression fromTy, Expression toTy) {
		assert(fromTy.isSemEvaluated());
		assert(toTy.isSemEvaluated());
		if(fromTy == toTy) return genNoopConvert(v, fromTy, toTy);
		auto conv = ast_conv.typeExplicitConversion!true(fromTy, toTy, ast_exp.TypeAnnotationType.coercion);
		assert(conv, format("not a valid coercion: %s -> %s", fromTy, toTy));
		return genConvert(conv, v);
	}

	Value genConvert(ast_conv.Conversion conv, Value v) {
		// `v` was generated with a type that is equal to `conv.from`, but it
		// equal types may differ in `typeHasClassical` / `typeHasQuantum`, for
		// example when `Expression.eval()` on a vector length makes it zero.
		v = genNoopConvert(v, null, conv.from);

		auto flags = conversionFlags(conv);
		if(flags == ConvertFlags.noop) return genNoopConvert(v, conv.from, conv.to);

		auto v2 = genConvert2(conv, v);
		if(!typeHasQuantum(conv.to) && v2.hasQuantum) {
			assert(typeHasQuantum(conv.from), format("%s %s -> %s produced a quantum component", typeid(conv).name, conv.from, conv.to));
			qcg.deallocUnit(v2.qreg);
			v2 = valNewC(v2.creg);
		}
		if(!typeHasClassical(conv.to)) {
			if(v2.hasClassical) v2 = valNewQ(null, v2.qreg);
		} else if(!(flags & ConvertFlags.classical)) {
			if(v2.creg !is v.creg) v2 = valNewQ(v.creg, v2.qreg);
		}
		return v2;
	}

	Value genConvert2(ast_conv.Conversion conv, Value v) {
		foreach(t; AliasSeq!(
			ast_conv.TransitiveConversion,
			ast_conv.QuantumPromotion,
			ast_conv.NumericConversion,
			ast_conv.NumericCoercion,
			ast_conv.TupleConversion,
			ast_conv.UnmultiplexConversion,
			ast_conv.VectorConversion,
			ast_conv.VectorToArrayConversion,
			ast_conv.ArrayToVectorConversion,
			ast_conv.ArrayConversion,
			ast_conv.FunctionConversion,
			ast_conv_ZtoFixedConversion,
			ast_conv.FixedToVectorConversion,
			ast_conv.VectorToFixedConversion,
		)) {
			if(auto c = cast(t) conv) {
				return implConvert(c, v);
			}
		}
		assert(0, format("TODO conversion: %s", conv));
	}

	Value implConvert(ast_conv.TransitiveConversion conv, Value v) {
		return genConvert(conv.b, genConvert(conv.a, v));
	}

	Value implConvert(ast_conv.QuantumPromotion conv, Value v) {
		assert(!typeHasQuantum(conv.from));
		assert(!v.hasQuantum);
		return genPromote(conv.to, v.creg);
	}

	Value implConvert(ast_conv.NumericConversion conv, Value v) {
		assert(!typeHasQuantum(conv.from) && !typeHasQuantum(conv.to), format("quantum numeric conversion %s -> %s", conv.from, conv.to));
		auto wf = ast_ty.isNumericTy(conv.from);
		auto wt = ast_ty.isNumericTy(conv.to);
		switch(wf) {
			case ast_ty.NumericType.Bool:
				switch(wt) {
					case ast_ty_NumericType_Nt:
					case ast_ty_NumericType_Zt:
						return valNewC(ccg.intFromBool(v.creg));
					case ast_ty_NumericType_Qt:
					case ast_ty_NumericType_R:
						return valNewC(ccg.floatFromBool(v.creg));
					case ast_ty_NumericType_C:
						return valNewC(ccg.complexFromBool(v.creg));
					default:
						assert(0, format("Unsupported numeric conversion: bool -> %s", conv.to));
				}
			case ast_ty_NumericType_Nt:
			case ast_ty_NumericType_Zt:
				switch(wt) {
					case ast_ty_NumericType_Zt:
						// N -> Z
						return v;
					case ast_ty_NumericType_Qt:
					case ast_ty_NumericType_R:
						return valNewC(ccg.floatFromInt(v.creg));
					case ast_ty_NumericType_C:
						return valNewC(ccg.complexFromInt(v.creg));
					default:
						assert(0, format("Unsupported numeric conversion: int -> %s", conv.to));
				}
			case ast_ty_NumericType_Qt:
				switch(wt) {
					case ast_ty_NumericType_R:
						return v;
					case ast_ty_NumericType_C:
						return valNewC(ccg.complexFromFloat(v.creg));
					default:
						assert(0, format("Unsupported numeric conversion: float -> %s", conv.to));
				}
			case ast_ty_NumericType_R:
				switch(wt) {
					case ast_ty_NumericType_C:
						return valNewC(ccg.complexFromFloat(v.creg));
					default:
						assert(0, format("Unsupported numeric conversion: float -> %s", conv.to));
				}
			default:
				assert(0, format("Unsupported numeric conversion: %s -> %s", conv.from, conv.to));
		}
	}

	Value implConvert(ast_conv.NumericCoercion conv, Value v) {
		assert(!typeHasQuantum(conv.from));
		assert(!typeHasQuantum(conv.to));
		auto wf = ast_ty.isNumericTy(conv.from);
		auto wt = ast_ty.isNumericTy(conv.to);
		switch(wf) {
			case ast_ty_NumericType_Nt:
			case ast_ty_NumericType_Zt:
				switch(wt) {
					case ast_ty.NumericType.Bool:
						return valNewC(ccg.intCmpNe0(v.creg));
					case ast_ty_NumericType_Nt:
						// Z -> N
						ccg.checkUnsigned(conv.needsCheck, v.creg);
						return v;
					default:
						assert(0, format("Unsupported numeric coercion int -> %s", conv.to));
				}
			case ast_ty_NumericType_Qt:
			case ast_ty_NumericType_R:
				switch(wt) {
					case ast_ty.NumericType.Bool:
						return valNewC(ccg.floatCmpNe0(v.creg));
					case ast_ty_NumericType_Nt:
						auto r = ccg.emitPureOp("float_floor_int", [v.creg]);
						ccg.checkUnsigned(conv.needsCheck, r);
						return valNewC(r);
					case ast_ty_NumericType_Zt:
						auto r = ccg.emitPureOp("float_floor_int", [v.creg]);
						return valNewC(r);
					case ast_ty_NumericType_Qt:
						// !R -> !Q
						return v;
					default:
						assert(0, format("Unsupported numeric coercion float -> %s", conv.to));
				}
			case ast_ty_NumericType_C:
				auto ri = ccg.boxUnpack(ctypeSilqTuple, 2, ccg.emitPureOp("classical_call[primitive.complex.ctori]", [v.creg]));
				ccg.checkBool(conv.needsCheck, ccg.floatCmpEq0(ri[1]));
				auto nconv = ast_conv.numericToNumeric!true(ast_ty_R, conv.to, ast_exp.TypeAnnotationType.coercion);
				assert(!!nconv);
				return genConvert(nconv, valNewC(ri[0]));
			default:
				assert(0, format("Unsupported numeric coercion %s -> %s", conv.from, conv.to));
		}
	}

	Value implConvert(ast_conv.TupleConversion conv, Value v) {
		Expression[] fromTypes = conv.elements.map!(c => c.from).array;
		Expression[] toTypes = conv.elements.map!(c => c.to).array;
		auto items = valUnpack(fromTypes, v);
		bool changed = false;
		foreach(i, c; conv.elements) {
			auto item = items[i];
			auto item2 = genConvert(c, item);
			items[i] = item2;
			if(item2.creg !is item.creg) {
				changed = true;
			}
		}
		auto r = valPack(toTypes, items);
		if(!changed && r.creg !is v.creg) {
			r = valNewQ(v.creg, r.qreg);
		}
		return r;
	}

	Value implConvert(ast_conv.UnmultiplexConversion conv, Value v) {
		auto i = genExpr(conv.index);
		assert(i.hasClassical && !i.hasQuantum);
		Value rec(size_t l, size_t r, Value v, ScopeWriter writer) {
			if(l + 1 < r) {
				size_t m = l + (r - l) / 2;
				auto cond = CondAny(writer.ccg.intCmpLt(i.creg, writer.ctx.literalInt(m)));
				ScopeWriter w0, w1;
				writer.genSplit(cond, w0, null, w1, null);
				Value v0, v1;
				writer.valSplit(cond, v0, v1, v);
				auto res1 = rec(l, m, v1, w1);
				auto res0 = rec(m, r, v0, w0);
				auto res = writer.valMerge(cond, res0, res1);
				w0.checkEmpty(false);
				w1.checkEmpty(false);
				return res;
			}
			return writer.genConvert(conv.conversions[l], v);
		}
		return rec(0, conv.conversions.length, v, this);
	}

	Value implConvert(ast_conv.VectorConversion conv, Value v) {
		auto fromTy = cast(ast_ty.VectorTy) conv.from;
		assert(fromTy);
		auto toTy = cast(ast_ty.VectorTy) conv.to;
		assert(toTy);
		auto len = ccg.checkEqInt(conv.checkLength, getVectorLength(fromTy), getVectorLength(toTy));
		return implConvertVector(conv.next, len, v);
	}

	Value implConvert(ast_conv.ArrayConversion conv, Value v) {
		auto fromTy = cast(ast_ty.ArrayTy) conv.from;
		CReg len;
		v = valArrayToVector(fromTy.next, len, v);
		auto r = implConvertVector(conv.next, len, v);
		return valVectorToArray(len, r);
	}

	CReg subfuncPack(string prefix, ScopeWriter subsc, CReg[] cRet, QReg[] qRet, CReg[] cArgs, QReg[] qcArgs, QReg[] qiArgs) {
		string f = ctx.allocName(prefix);
		CReg[] cap;
		ctx.output.write(subsc.ccg.code.finish(f, null, cap, cRet, qRet, cArgs, qcArgs, qiArgs, null));
		return ccg.funcPack(f, cap);
	}

	CReg subfuncPack(string prefix, ScopeWriter subsc, CReg[] cRet, CReg[] cArgs) {
		return subfuncPack(prefix, subsc, cRet, [], cArgs, [], []);
	}

	CReg genQTypeFunc(Expression ty) {
		auto subsc = subfuncScope(true);
		auto cc = new CReg();
		auto r = subsc.getQTypeRaw(ty, cc, false);
		return subfuncPack("silq_qtype", subsc, [r], [cc]);
	}

	CReg genPromoteFunc(Expression ty) {
		auto subsc = subfuncScope(true);
		auto arg = new CReg();
		auto r = subsc.genPromote(ty, arg, false);
		return subfuncPack("silq_promote", subsc, [r.creg], [r.qreg], [arg], [], []);
	}

	CReg genMeasureFunc(Expression ty) {
		auto subsc = subfuncScope(true);
		auto arg = subsc.valNewQ(ty);
		auto r = subsc.genMeasure(ty, arg, false);
		return subfuncPack("silq_measure", subsc, [r], [], [arg.creg], [], [arg.qreg]);
	}

	CReg genSubconverter(ast_conv.Conversion inner) {
		auto subsc = subfuncScope(true);

		auto subv = subsc.valNewQ(inner.from);
		auto subr = subsc.genConvert(inner, subv);

		return subfuncPack("silq_converter", subsc, [subr.creg], [subr.qreg], [subv.creg], [], [subv.qreg]);
	}

	Value implConvertVector(ast_conv.Conversion inner, CReg len, Value v) {
		auto flags = conversionFlags(inner);
		if(flags == ConvertFlags.noop) return v; // length-only conversion

		if(auto p = ctx.asUnroll(len)) {
			auto n = p.get();
			auto items = valUnpack(inner.from.repeat(n).array, v);
			items = items.map!(vi => genConvert(inner, vi)).array;
			return valPack(inner.to.repeat(n).array, items);
		}

		auto sub = genSubconverter(inner);
		CReg cr = null;
		if(typeHasClassical(inner.to)) {
			if(!v.creg || !typeHasClassical(inner.from)) {
				auto item = ccg.funcApply(sub, [null]);
				cr = ccg.boxRepeat(ctypeSilqTuple, len, item);
			} else {
				if(flags & (ConvertFlags.classical | ConvertFlags.check)) {
					auto bound = ccg.funcPack("silq_builtin.convert_vec_c", [sub, len, v.creg]);
					cr = ccg.funcApply("silq_builtin.iter_tuple", [bound, len]);
				}
				if(!(flags & ConvertFlags.classical)) {
					cr = v.creg;
				}
			}
		}
		if(!typeHasQuantum(inner.to)) {
			if(v.hasQuantum) qcg.deallocUnit(v.qreg);
			return valNewC(cr);
		}
		if(!(flags & ConvertFlags.quantum)) {
			return valNewQ(cr, v.qreg);
		}

		QReg qr = new QReg();
		if(cr && typeHasQDep(inner.to)) {
			CReg fromQTypes = getVectorQTypes(inner.from, len, v.creg);
			CReg toQTypes = getVectorQTypes(inner.to, len, cr);
			qcg.writeQOp("qfree_call[silq_builtin.convert_vec_qd]", [qr], [sub, len, fromQTypes, toQTypes, v.creg, len], [], [v.qreg]);
		} else {
			assert(!v.creg || !typeHasQDep(inner.to));
			auto fromQType = getQTypeRaw(inner.from, null);
			auto toQType = getQTypeRaw(inner.to, null);
			qcg.writeQOp("qfree_call[silq_builtin.convert_vec_qi]", [qr], [sub, len, fromQType, toQType, v.creg, len], [], [v.qreg]);
		}
		return valNewQ(cr, qr);
	}

	Value implConvert(ast_conv.VectorToArrayConversion conv, Value v) {
		auto vecTy = cast(ast_ty.VectorTy) conv.from;
		assert(vecTy);
		auto arrTy = cast(ast_ty.ArrayTy) conv.to;
		assert(arrTy);
		auto itemTy = arrTy.next;
		assert(vecTy.next == itemTy);
		auto len = getVectorLength(vecTy);
		return valVectorToArray(len, v);
	}

	Value implConvert(ast_conv.ArrayToVectorConversion conv, Value v) {
		auto arrTy = cast(ast_ty.ArrayTy) conv.from;
		assert(arrTy);
		auto vecTy = cast(ast_ty.VectorTy) conv.to;
		assert(vecTy);
		auto itemTy = vecTy.next;
		assert(arrTy.next == itemTy);
		CReg len;
		auto r = valArrayToVector(itemTy, len, v);
		len = ccg.checkEqInt(conv.checkLength, len, getVectorLength(vecTy));
		return r;
	}

	Value implConvert(ast_conv.FunctionConversion conv, Value v) {
		auto fromTy = cast(ast_ty.ProductTy) conv.from;
		auto toTy = cast(ast_ty.ProductTy) conv.to;

		Id[] names = conv.names;
		assert(fromTy && toTy && fromTy.names == names && names == conv.names);
		bool isTuple = fromTy.isTuple;
		assert(toTy.isTuple == isTuple);

		bool[] isConst = toTy.isConst;
		assert(isConst.length == names.length);

		CReg targetC, targetQType;
		QReg targetQ;
		if(typeHasQuantum(conv.from)) {
			targetC = ccg.qfuncInner(v.creg);
			targetQType = ccg.qfuncQType(v.creg);
			targetQ = v.qreg;
		} else {
			assert(v.creg);
			assert(!v.qreg);
			targetC = v.creg;
			targetQType = ctx.qtUnit;
			targetQ = null;
		}

		auto subsc = subfuncScope(false);

		auto typesIn = iota(isConst.length).map!(i => toTy.argTy(i)).array;
		auto typesOut = iota(isConst.length).map!(i => fromTy.argTy(i)).array;
		CReg cPackedIn;
		QReg qcPackedIn, qiPackedIn;

		auto args = subsc.unpackIndirect(cPackedIn, qcPackedIn, qiPackedIn, typesIn, isConst, isTuple);

		IdSet freeVars;
		foreach(var; conv.cod.from.freeVars) {
			freeVars[var.id] = unit;
		}
		foreach(var; conv.cod.to.freeVars) {
			freeVars[var.id] = unit;
		}
		foreach(i, arg; args) {
			auto name = names[i];
			if(name !in freeVars) continue;
			assert(!typeHasQuantum(typesIn[i]), format("quantum argument used in codomain type: %s", name));
			subsc.vars[name] = Variable(null, arg);
		}

		Value argIn;
		if (isTuple) {
			argIn = subsc.valPack(typesIn, args);
		} else {
			assert(args.length == 1);
			assert(typesIn.length == 1);
			assert(typesIn[0] == conv.dom.from);
			argIn = args[0];
		}
		Value argOut = subsc.genConvert(conv.dom, argIn);
		if (isTuple) {
			args = subsc.valUnpack(typesOut, argOut);
		} else {
			assert(args.length == 1);
			assert(typesOut.length == 1);
			assert(typesOut[0] == conv.dom.to);
			args[0] = argOut;
		}

		CReg[] cCall;
		QReg[] qcCall, qiCall;

		CallInfo ci;
		ci.target = valNewC(targetC);
		ci.isTuple = isTuple;
		ci.hasQuantum = false; // arguments forwarded below
		ci.args = iota(args.length).map!(i => ArgInfo(typesOut[i], null, args[i], isConst[i])).array;
		subsc.packIndirect(ci, cCall, qcCall, qiCall, false);

		assert(qcCall.length == 2);
		assert(!qcCall[0]);
		auto qcCap = new QReg();
		qcCall[0] = qcCap;

		assert(qiCall.length == 2);
		assert(!qiCall[0]);
		auto qiCap = new QReg();
		qiCall[0] = qiCap;

		auto r = subsc.valNewQ(conv.cod.from);
		subsc.qcg.writeMOp(opCallMeasureIndirect, [r.creg], [r.qreg], cCall, qcCall, qiCall);
		subsc.qcg.forget(qcCall[1]);
		r = subsc.genConvert(conv.cod, r);

		CReg newC = subfuncPack("silq_funcsubtype", subsc, [r.creg], [r.qreg], [cPackedIn], [qcCap, qcPackedIn], [qiCap, qiPackedIn]);

		if(!typeHasQuantum(conv.to)) {
			assert(!targetQ);
			return valNewC(newC);
		}
		return valNewQ(ccg.qfuncPack(newC, targetQType), targetQ);
	}

	Value implConvert(ast_conv_ZtoFixedConversion conv, Value v) {
		assert(!typeHasQuantum(conv.to));
		auto toInt = ast_ty.isFixedIntTy(conv.to);
		assert(toInt);
		assert(toInt.isClassical);
		auto bits = getNumericBits(toInt);
		return valNewC(ccg.intWrap(toInt.isSigned, bits, v.creg));
	}

	Value implConvert(ast_conv.FixedToVectorConversion conv, Value v) {
		auto fromInt = ast_ty.isFixedIntTy(conv.from);
		assert(fromInt);
		auto len = getNumericBits(fromInt);
		auto vecTy = cast(ast_ty.VectorTy) conv.to;
		assert(vecTy);
		len = ccg.checkEqInt(conv.checkLength, len, getVectorLength(vecTy));
		if(typeHasQuantum(vecTy)) {
			assert(!fromInt.isClassical);
			assert(!v.creg);
			return valNewQ(null, v.qreg);
		}
		assert(fromInt.isClassical);
		assert(!v.hasQuantum);
		return valNewC(ccg.emitPureOp("classical_call[silq_builtin.int_to_bits]", [len, v.creg]));
	}

	Value implConvert(ast_conv.VectorToFixedConversion conv, Value v) {
		auto vecTy = cast(ast_ty.VectorTy) conv.from;
		assert(vecTy);
		auto toInt = ast_ty.isFixedIntTy(conv.to);
		assert(toInt);
		auto len = getNumericBits(toInt);
		len = ccg.checkEqInt(conv.checkLength, len, getVectorLength(vecTy));
		if(typeHasQuantum(vecTy)) {
			assert(!toInt.isClassical);
			assert(!v.creg);
			return valNewQ(null, v.qreg);
		}
		assert(toInt.isClassical);
		assert(!v.hasQuantum);
		auto cval = ccg.emitPureOp("classical_call[silq_builtin.bits_to_int]", [len, v.creg]);
		if(toInt.isSigned) cval = ccg.intMakeSigned(len, cval);
		return valNewC(cval);
	}

private:
	ast_scope.NestedScope nscope;
	BorrowScope bscope;
	ScopeWriter parent;
	QCGen qcg;
	IdMap!Variable vars;
	bool detPassthrough;

	CReg[ExprInfo] cachedNat;
	RTTI[ExprInfo] cachedRTTI;
}

struct IrStatement {
	CondC[] condC;
	CondQ[] condQ;
	string op;
	CReg[] cRet;
	QReg[] qRet;
	CReg[] cArgs;
	QReg[] qcArgs;
	QReg[] qiArgs;
	ast_lex.Location loc;

	void putTo(Appender!string o) {
		o.put("\t");

		if(condC.length > 0 || condQ.length > 0) {
			o.put("if[");
			bool first = true;
			foreach(c; condC) {
				if(!first) o.put(", ");
				first = false;
				o.put(c.reg.toString());
				o.put("=");
				o.put(c.value ? "1" : "0");
			}
			foreach(c; condQ) {
				if(!first) o.put(", ");
				first = false;
				o.put(c.reg.toString());
				o.put("=");
				o.put(c.value ? "1" : "0");
			}
			o.put("] ");
		}

		bool first = true;
		foreach(r; cRet) {
			if(!first) o.put(", ");
			first = false;
			if(!r) {
				r = new CReg();
			}
			o.put(r.toString());
		}
		foreach(r; qRet) {
			if(!first) o.put(", ");
			first = false;
			o.put(r.toString());
		}
		if(!first) o.put(" := ");
		o.put(op);

		o.put("(");
		first = true;
		foreach(r; cArgs) {
			if(!first) o.put(", ");
			first = false;
			o.put(r.toString());
		}
		foreach(r; qcArgs) {
			if(!first) o.put(", ");
			first = false;
			o.put(r.toString());
		}
		o.put(")");

		if(qiArgs.length) {
			o.put(" <- ");
			first = true;
			foreach(r; qiArgs) {
				if(!first) o.put(", ");
				first = false;
				o.put(r.toString());
			}
		}

		o.put(" !loc ");
		escapeStr(&o, loc.source.name);
		o.put(", ");
		o.put(loc.line.text());
		o.put("\n");
	}
}

struct IrVariable {
	ast_decl.Declaration var;
	Value val;
	ast_lex.Location loc;
	int capLevel;
	int param;

	void putTo(Appender!string o) {
		if(!val._creg && !val._qreg) return;
		o.put("\t!var ");
		escapeStr(&o, var.name.name);
		o.put(" := ");
		if(val._creg) o.put(val._creg.toString());
		if(val._creg && val._qreg) o.put(",");
		if(val._qreg) o.put(val._qreg.toString());

		if(capLevel > 0) {
			o.put(" !capture ");
			o.put(capLevel.text());
		}
		if(param >= 0) {
			o.put(" !param ");
			o.put(param.text());
		}

		o.put(" !loc ");
		escapeStr(&o, loc.source.name);
		o.put(", ");
		o.put(loc.line.text());
		o.put("\n");
	}
}

class CodeWriter {
	Writer ctx;
	Appender!(IrStatement[]) code;
	Appender!(IrVariable[]) vars;

	this(Writer ctx, CodeWriter parent = null) {
		this.ctx = ctx;
		this.parent = parent;
	}

	CReg[] fixCNull(CReg[] regs, int mode) {
		if(regs.all!(r => !!r)) return regs;
		regs = regs.array;
		foreach(ref r; regs) {
			if(r) continue;
			if(mode >= 0) {
				r = ctx.nullReg;
				continue;
			}
			r = new CReg();
		}
		return regs;
	}

	void writeOp(CondC[] condC, CondQ[] condQ, string op, CReg[] cRet, QReg[] qRet, CReg[] cArgs, QReg[] qcArgs, QReg[] qiArgs) {
		cArgs = fixCNull(cArgs, 0);
		cRet = fixCNull(cRet, -1);
		code.put(IrStatement(condC, condQ, op, cRet, qRet, cArgs, qcArgs, qiArgs, ctx.curLoc.loc));
	}

	string finish(string defName, string prettyName, ref CReg[] captures, CReg[] cRet, QReg[] qRet, CReg[] cArgs, QReg[] qcArgs, QReg[] qiArgs, Expression[Id] attrs) {
		Appender!(IrStatement[]) literals;

		if(_qregU) {
			writeOp([], [], opDeallocUnit, [], [], [], [], [_qregU]);
		}

		{
			Appender!(CReg[]) cap;
			Appender!(CReg[]) lit;
			Unit[CReg] seenCRegs;
			foreach(r; cArgs) {
				seenCRegs[r] = unit;
			}
			foreach(stmt; code) {
				foreach(r; stmt.cRet) {
					seenCRegs[r] = unit;
				}
			}
			foreach(stmt; code) {
				foreach(r; stmt.cArgs) {
					if(r in seenCRegs) continue;
					seenCRegs[r] = unit;
					if(r in ctx.literalValue) {
						lit.put(r);
					} else {
						cap.put(r);
					}
				}
				foreach(cond; stmt.condC) {
					auto r = cond.reg;
					assert(r);
					if(r in seenCRegs) continue;
					seenCRegs[r] = unit;
					if(r in ctx.literalValue) {
						lit.put(r);
					} else {
						cap.put(r);
					}
				}
			}
			foreach(r; cRet) {
				if(!r) r = ctx.nullReg;
				if(r in seenCRegs) continue;
				seenCRegs[r] = unit;
				if(r in ctx.literalValue) {
					lit.put(r);
				} else {
					cap.put(r);
				}
			}

			foreach(r; lit[]) {
				literals.put(IrStatement([], [], format("literal[%s]", ctx.literalValue[r]), [r], [], [], [], [], ctx.curLoc.loc));
			}

			if(cap[].length > 0) {
				captures = cap[];
				cArgs = cap[] ~ cArgs;
			}
		}

		Appender!string o;
		o.put("def ");
		o.put(defName);
		{
			auto sep = "(";
			foreach(r; cArgs) {
				if(!r) r = new CReg();
				o.put(sep);
				o.put(r.toString());
				sep = ", ";
			}
			foreach(r; qcArgs) {
				if(!r) r = new QReg();
				o.put(sep);
				o.put(r.toString());
				sep = ", ";
			}
			if(sep != "(") o.put(")");
		}
		{
			auto sep = " <- ";
			foreach(r; qiArgs) {
				if(!r) {
					r = new QReg();
					literals.put(IrStatement([], [], opDeallocUnit, [], [], [], [], [r], ctx.curLoc.loc));
				}
				o.put(sep);
				o.put(r.toString());
				sep = ", ";
			}
		}
		foreach(name, val; attrs) {
			o.put(" [");
			o.put(name.str);
			o.put("]");
		}
		o.put("\n");

		if(prettyName) {
			o.put("!func_name ");
			escapeStr(&o, prettyName);
			o.put("\n");
		}

		foreach(s; literals) {
			s.putTo(o);
		}

		qRet = qRet.array;
		foreach(i, r; qRet) {
			if(r) continue;
			qRet[i] = r = new QReg();
			// TODO use end, not start
			code.put(IrStatement([], [], opAllocUnit, [], [r], [], [], [], ctx.curLoc.loc));
		}

		foreach(s; code) {
			s.putTo(o);
		}

		foreach(v; vars) {
			v.putTo(o);
		}

		{
			o.put("\treturn");
			auto sep = " ";
			foreach(r; cRet) {
				o.put(sep);
				if(!r) r = ctx.nullReg;
				o.put(r.toString());
				sep = ", ";
			}
			foreach(r; qRet) {
				o.put(sep);
				assert(r);
				o.put(r.toString());
				sep = ", ";
			}
		}
		o.put("\n\n");

		return o[];
	}

	string finish(string defName, string prettyName, CReg[] cRet, QReg[] qRet, CReg[] cArgs, QReg[] qcArgs, QReg[] qiArgs, Expression[Id] attrs) {
		assert(!parent);
		CReg[] cap;
		auto r = finish(defName, prettyName, cap, cRet, qRet, cArgs, qcArgs, qiArgs, attrs);
		assert(!cap, format("global captures in function %s: %s\n%s", defName, cap[], r));
		return r;
	}

	@property
	QReg qregU() {
		if(_qregU) return _qregU;
		auto r = new QReg();
		writeOp([], [], opAllocUnit, [], [r], [], [], []);
		_qregU = r;
		return r;
	}

private:
	CodeWriter parent = null;
	QReg _qregU = null;
}

struct CapInfo {
	bool hasClassical, hasQuantum, isMoved;
	ast_decl.Declaration innerDecl, outerDecl;
}
struct ParamInfo {
	bool hasClassical, hasQuantum;
	bool isConst;
}

class FunctionInfo {
	ast_decl.FunctionDef fd;
	string prettyName;
	string directName;
	string indirectName;
	CapInfo[] captures;
	ParamInfo[] params;
	bool retHasClassical, retHasQuantum;
	bool isExtern;
}

enum FunctionMode {
	name,
	direct,
	indirect
}

struct Options {
	bool compileLoopsAsNoOps;
}

struct PushLocation {
	Writer ctx;
	PushLocation* prev;
	ast_lex.Location loc;

	this(Writer ctx, ast_lex.Location loc) {
		this.ctx = ctx;
		this.prev = ctx.curLoc;
		this.loc = loc;
		if(!this.loc.rep.ptr) this.loc = this.prev.loc;
		ctx.curLoc = &this;
	}

	~this() {
		assert(this.ctx.curLoc is &this);
		this.ctx.curLoc = prev;
		this.ctx = null;
		this.prev = null;
	}
}

class Writer {
	this(File output, Options opt) {
		this.options = opt;
		this.output = output;
		this.byDirectName["silq_function"] = null;

		nullReg = literalRaw("null");
		qtUnit = literalRaw("qt_unit");
		qtQubit = literalRaw("qt_qubit");
		boolFalse = literalRaw("false");
		boolTrue = literalRaw("true");
		intZero = literalInt(0);
		intOne = literalInt(1);
		intTwo = literalInt(2);
		floatZero = literalFloat(0, 0);
		floatOne = literalFloat(1, 0);
		floatPi = literalFloat(3622009729038561421, -60);

		unitRTTI = RTTI.builtin(
			this,
			literalFunc("silq_builtin.qtype_const", [qtUnit]),
			literalFunc("silq_builtin.promote_unit", []),
			literalFunc("silq_builtin.measure_unit", []),
		);
		classicalRTTI = RTTI.builtin(
			this,
			literalFunc("silq_builtin.qtype_const", [qtUnit]),
			literalFunc("silq_builtin.promote_classical", []),
			literalFunc("silq_builtin.measure_classical", []),
		);
		qubitRTTI = RTTI.builtin(
			this,
			literalFunc("silq_builtin.qtype_const", [qtQubit]),
			literalFunc("silq_builtin.promote_qubit", []),
			literalFunc("silq_builtin.measure_qubit", []),
		);
		qfuncRTTI = RTTI.builtin(
			this,
			literalFunc("silq_builtin.qtype_qfunc", []),
			literalFunc("silq_builtin.promote_qfunc", []),
			literalFunc("silq_builtin.measure_qfunc", []),
		);
	}

	FunctionInfo getFunctionInfo(ast_decl.FunctionDef fd) {
		auto fi = functions.require(fd, new FunctionInfo());
		if(fi.fd) return fi;
		fi.fd = fd;
		pending.put(fi);
		ast_exp.Identifier name = fd.rename ? fd.rename : fd.name ? fd.name : null;
		if(ast_decl.FunctionDef parent = fd.fscope_.parent.getFunction()) {
			auto pi = getFunctionInfo(parent);
			fi.prettyName = pi.prettyName;
			if(name) {
				fi.prettyName ~= "." ~ name.id.str;
			} else if(!isReturnLambda(parent, fd)) {
				fi.prettyName ~= ".<lambda>";
			};
			fi.directName = pi.directName;
		} else {
			fi.prettyName = name ? name.id.str : "<unnamed>";
			fi.directName = "silq_function";
		}
		if (name) {
			fi.directName ~= "." ~ mangleName(name);
		}
		if (fi.directName in byDirectName) {
			size_t i = 0;
			while (true) {
				string cand = format("%s.%d", fi.directName, i);
				if (cand !in byDirectName) {
					fi.directName = cand;
					break;
				}
				i++;
			}
		}
		byDirectName[fi.directName] = fi;

		if(fd.isSquare) {
			fi.prettyName ~= "[";
		} else {
			fi.prettyName ~= "(";
		}
		if(fd.isTuple) {
			foreach(p; fd.params) {
				fi.prettyName ~= p.name.toString();
				fi.prettyName ~= ",";
			}
		} else {
			fi.prettyName ~= fd.params[0].name.toString();
		}
		if(fd.isSquare) {
			fi.prettyName ~= "]";
		} else {
			fi.prettyName ~= ")";
		}

		fi.indirectName = "silq_indirect." ~ fi.directName[14..$];
		fi.retHasClassical = typeHasClassical(fd.ret);
		fi.retHasQuantum = typeHasQuantum(fd.ret);
		fi.params = fd.params.map!((param) {
			ParamInfo p;
			auto ty = typeForDecl(param);
			p.hasClassical = typeHasClassical(ty);
			p.hasQuantum = typeHasQuantum(ty);
			p.isConst = param.isConst;
			return p;
		}).array;
		if(string externName = fd.stringAttribute(Id.s!"extern")) {
			fi.directName = externName;
			auto at = fd;
			ast_decl.Parameter[] outerParams;
			while(!at.name) {
				auto parent = at.fscope_.parent.getFunction();
				assert(parent, "Internal error: Anonyomous global function?");
				assert(parent.body_, "Internal error: Function parent has empty body?");
				assert(parent.body_.s.length == 1, "Extern functions must have a name");
				auto parentRet = cast(ast_exp.ReturnExp) parent.body_.s[0];
				assert(parentRet, "Extern functions must have a name");
				auto parentRef = cast(ast_exp.LambdaExp) parentRet.e;
				assert(parentRef, "Extern functions must have a name");
				assert(parentRef.fd is at, "Extern functions must have a name");
				outerParams = parent.params ~ outerParams;
				at = parent;
			}
			fi.captures = outerParams.map!((cap) {
				auto ty = typeForDecl(cap);
				assert(cap.isConst, format("Extern function %s: Outer parameters must be const", fi.prettyName));
				assert(!ast_ty.hasQuantumComponent(ty), format("Extern function %s: Outer parameters must be classical", fi.prettyName));
				assert(ast_ty.hasClassicalComponent(ty), format("Extern function %s: Outer parameters must be classical", fi.prettyName));
				CapInfo c;
				c.hasClassical = true;
				c.hasQuantum = false;
				return c;
			}).array;

			size_t[ast_decl.Declaration] paramI;
			foreach(i, param; outerParams) {
				paramI[param] = i;
			}
			foreach(cap; fd.capturedDecls) {
				auto p = cap in paramI;
				if (!p) continue;
				auto i = *p;
				fi.captures[i].innerDecl = cap;
				fi.captures[i].outerDecl = cap;
			}
		} else {
			fi.captures = fd.capturedDecls.map!((cap) {
				assert(!cap.scope_.isNestedIn(fd.fscope_));
				auto ty = typeForDecl(cap);
				CapInfo c;
				c.outerDecl = cap;
				if (fd.isConsumedCapture(cap)) {
					assert(cap.splitInto.length == 1);
					c.innerDecl = cap.splitInto[0];
					assert(c.innerDecl.scope_.isNestedIn(fd.fscope_));
					assert(c.innerDecl.splitFrom is cap);
					assert(typeForDecl(c.innerDecl) == typeForDecl(c.outerDecl));
				} else {
					c.innerDecl = cap;
				}
				c.hasClassical = typeHasClassical(ty);
				c.hasQuantum = typeHasQuantum(ty);
				c.isMoved = fd.isConsumedCapture(cap);
				return c;
			}).array;
		}
		return fi;
	}

	string allocName(string prefix) {
		return format("%s.%s", prefix, lambdaCtr++);
	}

	string[] dump(ast_decl.FunctionDef[] rootF) {
		auto r = appender!(string[]);

		output.write(import("builtins.hqir"));

		foreach(fd; rootF) {
			r.put(getFunctionInfo(fd).directName);
		}

		for(size_t i = 0; i < pending[].length; i++) {
			auto fi = pending[][i];
			if(!fi.fd.body_) {
				// assert(fi.isExtern, format("Non-extern function `%s` has no body", fi.prettyName));
				continue;
			}
			try {
				output.write(dumpDirect(fi));
			} catch(AssertError exc) {
				exc.msg = format("%s\nin function: %s", exc.msg, fi.fd);
				throw exc;
			}
			if (fi.directName == "silq_function.main") {
				output.write(dumpPrint(fi));
			}
		}

		foreach(fi; functions) {
			if(!fi.indirectName) continue;
			output.write(dumpIndirect(fi));
		}
		return r[];
	}

	string dumpDirect(FunctionInfo fi) {
		auto fd = fi.fd;
		auto sc = new ScopeWriter(fd, this);
		scope loc = PushLocation(this, fd.loc);

		auto cArgs = appender!(CReg[]);
		auto qcArgs = appender!(QReg[]);
		auto qiArgs = appender!(QReg[]);

		foreach(cap; fi.captures) {
			if(!cap.innerDecl) {
				assert(fi.isExtern, "only extern functions have fake captures");
				assert(!cap.hasQuantum, "fake capture with quantum component");
				if(cap.hasClassical) cArgs.put(null);
				continue;
			}
			auto v = sc.defineCapture(cap.innerDecl);
			if(cap.hasClassical) cArgs.put(v.creg);
			else assert(!v.hasClassical);
			if(cap.hasQuantum) {
				if(cap.isMoved) qiArgs.put(v.qreg);
				else qcArgs.put(v.qreg);
			} else assert(!v.hasQuantum);
		}
		foreach(i, param; fi.params) {
			auto d = fd.params[i];
			sc.genExpr(d.vtype);
			auto v = sc.defineParam(d);
			if(param.hasClassical) cArgs.put(v.creg);
			if(param.hasQuantum) {
				if(param.isConst) qcArgs.put(v.qreg);
				else qiArgs.put(v.qreg);
			} else {
				assert(!v.hasQuantum);
			}
		}

		sc.genExpr(fd.rret ? fd.rret : fd.ret);

		auto res = sc.genStmt(fd.body_);
		assert(!res.mayPass, format("function %s did not return", fd.name));

		// clear const parameters
		foreach(i, param; fd.params) {
			if(param.isConst) sc.getVar(param, false);
		}
		// clear const captures
		foreach(i, cap; fi.captures) {
			if(!cap.isMoved && cap.innerDecl) sc.getVar(cap.innerDecl, false);
		}
		sc.checkEmpty(!!res.isAbort);

		auto rv = res.asValue(sc, fd.ret);
		assert(rv.classicalRet && !rv.quantumRet);
		auto v = rv.classicalRet;

		CReg[] cRet = null;
		if(typeHasClassical(fd.ret)) cRet = [v.creg];
		QReg[] qRet = null;
		if(typeHasQuantum(fd.ret)) qRet = [v.qreg];

		return sc.ccg.code.finish(fi.directName, fi.prettyName, cRet, qRet, cArgs[], qcArgs[], qiArgs[], fd.attributes);
	}

	string dumpIndirect(FunctionInfo fi) {
		auto fd = fi.fd;
		auto sc = new ScopeWriter(fd, this);
		scope loc = PushLocation(this, fd.loc);

		auto cCap = appender!(CReg[]);
		auto qcCapT = appender!(CReg[]);
		auto qcCapR = appender!(QReg[]);
		auto qiCapT = appender!(CReg[]);
		auto qiCapR = appender!(QReg[]);

		foreach(cap; fi.captures) {
			if(!cap.innerDecl) {
				assert(!cap.hasQuantum, "fake capture with quantum component");
				assert(cap.hasClassical, "fake capture without classical component");
				cCap.put(new CReg());
				continue;
			}
			auto val = sc.defineCapture(cap.innerDecl);
			if(cap.hasClassical) {
				assert(val.creg);
				cCap.put(val.creg);
			} else if(val.creg) {
				assert(0, "Capture has no classical component but argument does");
			}
			if(cap.hasQuantum) {
				assert(val.qreg);
				auto qt = sc.getQType(typeForDecl(cap.innerDecl), val);
				if(cap.isMoved) {
					qiCapT.put(qt);
					qiCapR.put(val.qreg);
				} else {
					qcCapT.put(qt);
					qcCapR.put(val.qreg);
				}
			} else if(val.hasQuantum) {
				assert(0, "Capture has no quantum component but argument does");
			}
		}

		QReg qcCap = new QReg();
		QReg qiCap = new QReg();
		if(qiCapR[].length == 0) {
			sc.qcg.deallocUnit(qiCap);
		} else {
			sc.qcg.writeQOp(opUnpack(qiCapR[].length), qiCapR[], qiCapT[], [], [qiCap]);
		}
		if(qcCapR[].length != 0) {
			auto qr2 = sc.qcg.dup(qcCap);
			sc.qcg.writeQOp(opUnpack(qcCapR[].length), qcCapR[], qcCapT[], [], [qr2]);
		}

		CReg cTuple = null;
		QReg qcTuple = null, qiTuple = null;
		auto args = sc.unpackIndirect(
			cTuple, qcTuple, qiTuple,
			fd.params.map!(decl => typeForDecl(decl)).array,
			fd.params.map!(decl => decl.isConst).array,
			fd.isTuple,
		);

		auto realCArgs = appender!(CReg[]);
		auto realQcArgs = appender!(QReg[]);
		auto realQiArgs = appender!(QReg[]);
		foreach(i, param; fi.params) {
			auto v = args[i];
			sc.defineVar(fd.params[i], v);
			if(param.hasClassical) realCArgs.put(v.creg);
			else assert(!v.hasClassical);
			if(param.hasQuantum) {
				if(param.isConst) realQcArgs.put(v.qreg);
				else realQiArgs.put(v.qreg);
			} else {
				assert(!v.hasQuantum);
			}
		}

		CReg[] cRet;
		QReg[] qRet;
		auto v = sc.valNewQ(fd.ret);
		putRet(fi, cRet, qRet, v);

		string nameArg = fi.directName;
		if(fd.annotation <= ast_ty.Annotation.none) {
			sc.qcg.writeMOp(opCallMeasure(nameArg), cRet, qRet, cCap[] ~ realCArgs[], qcCapR[] ~ realQcArgs[], qiCapR[] ~ realQiArgs[]);
		} else {
			sc.ccg.writeCOp(opCallClassical(nameArg), cRet, cCap[] ~ realCArgs[]);
			string op = fd.annotation >= ast_ty.Annotation.qfree ? opCallQfree(nameArg) : opCallMfree(nameArg);
			sc.qcg.writeQOp(op, qRet, cCap[] ~ realCArgs[], qcCapR[] ~ realQcArgs[], qiCapR[] ~ realQiArgs[]);
		}
		sc.qcg.forget(qcCapR[]);
		sc.qcg.forget(realQcArgs[]);

		if(cRet.length == 0) {
			cRet = [null];
		}
		if(qRet.length == 0) {
			qRet = [null];
		}

		Expression[Id] attrs;
		attrs[Id.s!"artificial"] = ast_exp.LiteralExp.makeBoolean(true);
		return sc.ccg.code.finish(fi.indirectName, null, cRet, qRet, cCap[] ~ [cTuple], [qcCap, qcTuple], [qiCap, qiTuple], attrs);
	}

	string dumpPrint(FunctionInfo fi) {
		auto fd = fi.fd;
		auto sc = new ScopeWriter(fd, this);
		scope loc = PushLocation(this, fd.loc);
		// sc.nscope = null; // semScope() needs a scope

		auto cIn = fi.retHasClassical ? new CReg() : null;
		auto cArgs = fi.retHasClassical ? [cIn] : [];

		auto qIn = fi.retHasQuantum ? new QReg() : null;
		auto qArgs = fi.retHasQuantum ? [qIn] : [];

		assert(fd.ret);
		CReg r = fi.retHasQuantum ? sc.genMeasure(fd.ret, sc.valNewQ(cIn, qIn)) : cIn;

		Expression[Id] attrs;
		return sc.ccg.code.finish("silq_main_print", null, [r], [], cArgs, [], qArgs, attrs);
	}

	bool isLiteral(CReg r) {
		return !!(r in literalValue);
	}

	CReg literalRaw(string val) {
		if(auto p = val in literals) return *p;
		auto r = new CReg();
		literalValue[r] = val;
		literals[val] = r;
		return r;
	}

	CReg literalBool(bool val) {
		return val ? boolTrue : boolFalse;
	}

	CReg literalInt(BigInt val) {
		auto r = literalRaw(val.toDecimalString());
		intValue[r] = val;
		return r;
	}

	CReg literalInt(size_t val) {
		return literalInt(BigInt(val));
	}

	CReg literalFloat(long m, int e) {
		if(m == 0) {
			e = 0;
		} else {
			while(!(m & 1)) {
				m >>= 1;
				e++;
			}
		}
		return literalRaw(format("float(%d,%d)", m, e));
	}

	CReg literalFloat(double val) {
		assert(isFinite(val), "literal float not finite");
		int exp;
		val = frexp(val, exp);
		return literalFloat(cast(long)(val * (cast(long)1 << 53)), exp - 53);
	}

	CReg literalFunc(string name, CReg[] args) {
		return literalRaw("func[" ~ name ~ "](" ~ args.map!(arg => literalValue[arg]).join(",") ~ ")");
	}

	CReg literalBox(string tag, CReg[] args) {
		return literalRaw("box[" ~ tag ~ "](" ~ args.map!(arg => literalValue[arg]).join(",") ~ ")");
	}

	Maybe!size_t asIndex(CReg r, size_t bound) {
		auto p = r in intValue;
		if(!p) return none!size_t;
		if(*p < 0 || *p >= bound) return none!size_t;
		return just(p.to!size_t);
	}

	Maybe!size_t asUnroll(CReg r) {
		return asIndex(r, MAX_UNROLL_LENGTH + 1);
	}

	ExprInfo exprInfoImpl(Expression expr) {
		foreach(e; exprInfoList[]) {
			if(e.expr == expr) return e;
		}
		auto e = new ExprInfo(exprInfoList[].length, expr);
		exprInfoList.put(e);
		return e;
	}

	ExprInfo exprEval(Expression expr) {
		expr = expr.eval();
		assert(expr.isDeterministic(), format("non-deterministic expression under static evaluation: %s", expr));
		return exprInfoMap.require(cast(void*) expr, exprInfoImpl(expr));
	}

	CReg nullReg;
	CReg qtUnit, qtQubit;
	CReg boolFalse, boolTrue;
	CReg intZero, intOne, intTwo;
	CReg floatZero, floatOne, floatPi;
	RTTI unitRTTI, classicalRTTI, qubitRTTI, qfuncRTTI;

private:
	CReg[string] literals;
	string[CReg] literalValue;
	BigInt[CReg] intValue;

	Appender!(ExprInfo[]) exprInfoList;
	ExprInfo[void*] exprInfoMap;

	PushLocation* curLoc;

private:
	FunctionInfo[ast_decl.FunctionDef] functions;
	FunctionInfo[string] byDirectName;
	Appender!(FunctionInfo[]) pending;
	File output;
	Options options;
}
