// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

// Language Server Protocol front-end for silq (`silq --lsp`).
//
// One server, two clients: it speaks JSON-RPC over stdin/stdout, so the VSCode
// extension can spawn it directly, and the browser build exports it one
// message per call (silq_lsp_message, silq_lsp_idle; see the end of this
// file), which the WASM IDE's worker drives.
//
// Scope for now: document synchronisation and diagnostics. Diagnostics reuse
// the type checker directly (`importModule`) rather than shelling out, so a
// keystroke costs one in-process check instead of a process spawn.
module lsp;

// The bare-wasm target (build-wasm-ldc.sh, -version=WASM) substitutes stub
// stdio: its std.stdio offers only `writeln` and its core.stdc.stdio only
// `snprintf`. There is no stream to speak LSP over there, so compile the module
// down to a stub rather than breaking that build. (The Emscripten target sets
// version=Emscripten, not WASM, and keeps real stdio - that is the build the
// IDE drives.)
version(WASM) {
	int runLanguageServer() { return 1; }
} else:

import std.json, std.conv, std.string, std.array, std.algorithm;
import std.stdio: stdin, stdout;
import core.stdc.stdio: _IONBF;
import ast.error, ast.lexer, ast.expression, ast.scope_, ast.modules;
import ast.type: clearTypeCaches;
import ast.semantic_: resetFreshNameCount;
import astopt;
import util.path: dirName;
import std.path: isAbsolute;
import std.uri: decodeComponent;

// A diagnostic from one type-check. Positions are kept as byte offsets into the
// owning Source: they are exact, and unlike silq's display-width columns they
// need no assumptions about tab stops or character widths.
private struct Diag {
	ErrorType severity;
	string message;
	bool located;        // false when the error carried no usable location
	Source src;
	string file;         // src's file, absolute: resolved while the check ran
	int startByte, endByte;
	Diag[] related;
}

// Collects diagnostics in memory instead of printing them.
//
// This handler is created once and lives as long as the server, because scopes
// capture their handler permanently: getPreludeScope caches the prelude
// TopScope with whatever handler first built it, and the operator scope is
// cached the same way. A per-request handler would therefore be captured by the
// prelude on the first check and every later error routed through a prelude- or
// import-owned scope would be appended to an object nobody reads. Instead the
// handler is stable and `diags` is cleared per check.
private final class ServerErrorHandler: ErrorHandler {
	Diag[] diags;
	override void report(ErrorType ty, lazy string msg, Location loc) {
		super.report(ty, msg, loc);
		// The front end raises and discards errors during trial analyses
		// (ast.semantic_ bumps `suppress` around them); every other handler
		// honours this, and without it those speculative errors would surface
		// as real squiggles on code that compiles cleanly.
		if(suppress) return;
		// Location.info asserts if it cannot find the Source backing `rep`, so
		// an error without a usable location is recorded as unlocated rather
		// than being anchored at the start of the file.
		if(loc.line == 0 || loc.rep.ptr is null || !loc.rep.length) {
			diags ~= Diag(ty, msg, false);
			return;
		}
		auto li = loc.info(getTabsize());
		auto d = Diag(ty, msg, true, li.source, absoluteFile(li.source.name), li.startByte, li.endByte);
		if(ty == ErrorType.note && diags.length) diags[$-1].related ~= d;
		else diags ~= d;
	}
}

private __gshared ServerErrorHandler handler;

// Every file has one name, and every comparison uses it: a document the client
// opened, an import the check read, and a diagnostic's file must agree on the
// spelling or "is this file open?" gets the wrong answer.
//
// A document's name comes from its URI (uriToName). A name from import
// resolution is relative to the working directory when the file was found
// there (getActualPath), so it is joined with the directory of the check in
// progress *as the client spells it*: getcwd would report the same directory
// with symlinks resolved, a name the client never uses. Nothing here asks the
// disk, because a file can be open in the editor and missing on disk.
//
// A document's own name is kept as it is (untitled:Untitled-1 is not a path),
// and so are the built-in scopes, named like `.prelude`.
private string checkDir; // the directory of the check in progress, or null

// A directory that is guaranteed to contain nothing, created on first use and
// removed when the native server exits (runLanguageServer). The browser build's
// instances are thrown away whole, file system included.
private string emptyDir;

private string emptyDirectory() {
	import std.file: tempDir;
	import std.path: buildPath;
	if(!emptyDir.length) {
		version(Posix) {
			// mkdtemp picks a fresh name and creates the directory in one step.
			// (It also exists in the Emscripten build, which has no
			// std.process.thisProcessID.)
			import core.sys.posix.stdlib: mkdtemp;
			import std.string: fromStringz;
			auto t = (buildPath(tempDir, "silq-lsp-empty-XXXXXX") ~ "\0").dup;
			if(mkdtemp(t.ptr) is null) throw new Exception("cannot create an empty directory");
			emptyDir = fromStringz(t.ptr).idup;
		} else {
			import std.file: mkdirRecurse;
			import std.process: thisProcessID;
			auto d = buildPath(tempDir, "silq-lsp-empty-" ~ to!string(thisProcessID));
			mkdirRecurse(d);
			emptyDir = d;
		}
	}
	return emptyDir;
}

private string absoluteFile(string name) {
	import std.path: absolutePath, buildNormalizedPath;
	if(name in uriForName) return name;
	if(isAbsolute(name)) return canonicalPath(buildNormalizedPath(name));
	if(name.startsWith(".") && !name.canFind('/') && !name.canFind('\\')) return name;
	return canonicalPath(checkDir.length ? buildNormalizedPath(checkDir, name) : absolutePath(name));
}

// One spelling per path on Windows, where the client writes c:/x and the file
// system C:\x. Elsewhere a path is already canonical.
version(Windows) private enum windowsPaths = true; else private enum windowsPaths = false;

private string canonicalPath(string p, bool windows = windowsPaths) {
	if(!windows) return p;
	auto q = p.replace("\\", "/");
	if(q.length >= 2 && q[1] == ':') q = q[0 .. 1].toLower() ~ q[1 .. $];
	return q;
}

// The URI each checked document arrived as, keyed by the Source name derived
// from it. Diagnostics must be published under the URI the client actually
// sent: reconstructing one from a path cannot round-trip a non-file scheme
// (untitled:, vscode-vfs:) and need not agree on escaping for a file one.
private __gshared string[string] uriForName;

// ---------------------------------------------------------------- positions

// Converts byte offsets in one source into LSP positions (0-based line, 0-based
// UTF-16 code unit). Built once per source per check.
private struct PositionMap {
	string text;
	size_t[] lineStart;

	this(string text) {
		this.text = text;
		lineStart = [cast(size_t)0];
		foreach(i, char c; text) if(c == '\n') lineStart ~= i + 1;
	}

	JSONValue at(int byteOffset) const {
		size_t off = byteOffset < 0 ? 0 : byteOffset;
		if(off > text.length) off = text.length;
		size_t lo = 0, hi = lineStart.length - 1;
		while(lo < hi) {
			auto mid = (lo + hi + 1) / 2;
			if(lineStart[mid] <= off) lo = mid; else hi = mid - 1;
		}
		int u16 = 0;
		// A byte offset always lands on a character boundary here (locations are
		// token slices), but decoding defensively keeps a malformed buffer from
		// throwing out of the check.
		try {
			foreach(dchar ch; text[lineStart[lo] .. off]) u16 += ch <= 0xFFFF ? 1 : 2;
		} catch(Exception) {
			u16 = cast(int)(off - lineStart[lo]);
		}
		return JSONValue(["line": JSONValue(cast(int)lo), "character": JSONValue(u16)]);
	}

	// The offset one whole character past `byteOffset`. Advancing by one byte
	// would split a multi-byte character and leave a range ending inside it.
	int nextCharBoundary(int byteOffset) const {
		size_t i = (byteOffset < 0 ? 0 : cast(size_t)byteOffset) + 1;
		while(i < text.length && (text[i] & 0xC0) == 0x80) i++;
		return cast(int)i;
	}

	// The start of the character just before `byteOffset`.
	int prevCharBoundary(int byteOffset) const {
		size_t i = byteOffset <= 0 ? 0 : cast(size_t)byteOffset - 1;
		while(i > 0 && (text[i] & 0xC0) == 0x80) i--;
		return cast(int)i;
	}
}

// LSP severities: 1 Error, 2 Warning, 3 Information, 4 Hint.
private int lspSeverity(ErrorType ty) {
	final switch(ty) {
		case ErrorType.error, ErrorType.run_error: return 1;
		case ErrorType.warning: return 2;
		case ErrorType.note, ErrorType.message: return 3;
	}
}

// The one range policy, shared with the WASM IDE and the VS Code extension:
// never invert, and never emit a zero-width range, because an editor draws
// nothing useful for one.
//
// Clamp first, then widen. The end-of-file token sits in the NUL padding past
// the text (ast/lexer.d), so "expected ';'" on an unfinished last line arrives
// with both ends beyond the text and clamps to one point. With nothing left to
// widen into there, the range falls back onto the last visible character. Only
// a document with no visible character at all still gets a zero-width range.
private JSONValue toLspRange(const ref PositionMap map, int startByte, int endByte) {
	int len = cast(int)map.text.length;
	int clamp(int b) { return b < 0 ? 0 : b > len ? len : b; }
	int s = clamp(startByte), e = clamp(endByte);
	if(e <= s) {
		e = map.nextCharBoundary(s);
		if(e > len) {
			e = s = len;
			for(int i = len; i > 0;) {
				auto p = map.prevCharBoundary(i);
				auto c = map.text[p];
				if(c != ' ' && c != '\t' && c != '\r' && c != '\n') { s = p; e = i; break; }
				i = p;
			}
		}
	}
	return JSONValue(["start": map.at(s), "end": map.at(e)]);
}

// ---------------------------------------------------------------- checking

// Type-check one in-memory buffer, returning the diagnostics it produced.
//
// Anything thrown is contained here, the front end's assertions included: silq
// is assert-heavy and neither build script disables asserts, so a half-typed
// expression that trips one would otherwise unwind out of the message loop and
// take the whole editor session with it. Recovering from a Throwable is a
// compromise - the alternative is losing every open document over one transient
// keystroke. Everything a check does is inside, not only the type checking:
// loading the prelude and moving between directories can fail too.
private Diag[] checkDocument(string name, string text) {
	handler.diags = null;
	try {
		runCheck(name, text);
	} catch(Throwable e) {
		// Keep what was already collected: the errors found before the failure
		// are real and located, and dropping them for one synthetic message
		// makes a partly-broken file look like it has a single mystery error.
		return handler.diags ~ Diag(ErrorType.error, "internal error while checking this file: " ~ e.msg, false);
	}
	return handler.diags;
}

private void runCheck(string name, string text) {
	// Imported modules are cached for the life of the process, which suits a
	// one-shot compile. Here it would mean every check sees an imported file as
	// it was first read, so a saved change to it, broken or not, never shows.
	clearModuleCache();
	// The type constructors' caches likewise outlive a check, and every check
	// adds to them (a 𝔹^n for each new n), keeping each check's syntax tree
	// alive: memory grows with every keystroke until the server is restarted.
	clearTypeCaches();
	// The prelude and operator scopes are rebuilt too, and the counter that
	// names temporaries starts again from zero, so each check is a fresh
	// compile in everything but the process: its diagnostics, temporaries'
	// names included, are the ones F5 would give. (A fresh compile parses the
	// file, then loads the prelude, then analyses the file, all drawing names
	// from that one counter, so no kept prelude could be numbered around.)
	clearBuiltinScopes();
	resetFreshNameCount(0);
	// Imports resolve against the working directory first (getActualPath), and
	// an editor starts the server in the workspace root. Searching the
	// document's directory after that is not enough: a same-named file in the
	// root would win. Check from the document's directory instead, which is
	// exactly what F5 does (the runner spawns silq there). A non-file
	// document's dirName is "." and is left alone. Saving the directory to
	// return to is best-effort: it may have been deleted since the server
	// started, and that must not stop documents elsewhere being checked.
	import std.file: getcwd, chdir;
	import std.exception: collectException;
	auto dir = dirName(name);
	string savedCwd;
	collectException(savedCwd = getcwd());
	scope(exit) if(savedCwd.length) collectException(chdir(savedCwd));
	scope(exit) checkDir = null;
	if(dir.length && isAbsolute(dir)) {
		// Names stay right even if the directory is gone (deleted or renamed
		// while its files are open): they come from checkDir, not the disk.
		checkDir = dir;
		// But imports would then resolve against wherever the server happens
		// to be, and a same-named file there would be read in place of the
		// missing one. Check from an empty directory instead, so that only an
		// open buffer can stand in for a file that is no longer on disk.
		if(collectException(chdir(dir)) !is null) collectException(chdir(emptyDirectory()));
	}

	auto src = new Source(name, text ~ "\0\0\0\0"); // four NUL bytes required
	// The Source registry is a global array with a linear-scan lookup, so an
	// undisposed Source per keystroke both leaks and slows every later lookup.
	scope(exit) src.dispose();
	Expression[] exprs;
	TopScope sc;
	importModule(src, handler, exprs, sc, Location.init);
}

// ---------------------------------------------------------------- transport

// Where outgoing messages go. Natively they are framed onto stdout
// (runLanguageServer); the browser build collects them for its caller instead
// (the exports at the end of this file).
private void delegate(string) emit;

private void sendMessage(JSONValue msg) {
	emit(msg.toString());
}

private void sendNotification(string method, JSONValue params) {
	sendMessage(JSONValue(["jsonrpc": JSONValue("2.0"), "method": JSONValue(method), "params": params]));
}

private void sendResult(JSONValue id, JSONValue result) {
	sendMessage(JSONValue(["jsonrpc": JSONValue("2.0"), "id": id, "result": result]));
}

private void sendError(JSONValue id, int code, string message) {
	sendMessage(JSONValue([
		"jsonrpc": JSONValue("2.0"), "id": id,
		"error": JSONValue(["code": JSONValue(code), "message": JSONValue(message)]),
	]));
}

// Reading a field that may be absent must not throw: an exception escaping the
// dispatch loop ends the editor session, and catching it is not something to
// rely on (the Emscripten build does not unwind through this loop reliably).
private string strField(JSONValue v, string key) {
	if(v.type != JSONType.object) return null;
	if(auto p = key in v) if(p.type == JSONType.string) return p.str;
	return null;
}

private enum Read { message, eof, skip }

// Read one Content-Length framed message. A malformed frame is skipped rather
// than treated as end-of-input: dropping the connection over one bad header
// would end the editor session.
//
// A header block with a missing or unparseable length leaves the size of its
// body unknown. Skipping that frame means scanning ahead for the next
// "Content-Length:", wherever on a line it starts: a body ends without a
// newline, so the next frame's first header shares a line with it.
private Read readMessage(out string result) {
	enum contentLength = "content-length:";
	size_t length = 0;
	bool haveLength = false, resync = false;
	for(;;) {
		auto line = stdin.readln();
		if(line.length == 0) return Read.eof;
		auto header = line.strip();
		if(resync) {
			// The last one: the skipped body may itself contain the text.
			auto i = header.lastIndexOf(contentLength, CaseSensitive.no);
			if(i < 0) continue;
			header = header[i .. $];
			resync = false;
		}
		if(header.length == 0) {
			if(haveLength) break; // blank line ends the headers
			resync = true;
			continue;
		}
		if(header.toLower().startsWith(contentLength)) {
			try {
				length = header[contentLength.length .. $].strip().to!size_t;
				haveLength = true;
			} catch(Exception) {
				haveLength = false;
				resync = true;
			}
		}
	}
	if(length == 0) return Read.skip;
	// Trust nothing about the size: an absurd but parseable length would abort
	// the process with OutOfMemoryError, which no catch here can contain.
	enum maxMessage = 64 * 1024 * 1024;
	if(length > maxMessage) {
		// Consume the body anyway so the next frame still starts at a header.
		auto sink = new char[4096];
		for(size_t left = length; left;) {
			auto want = left < sink.length ? left : sink.length;
			auto got_ = stdin.rawRead(sink[0 .. want]);
			if(got_.length == 0) return Read.eof;
			left -= got_.length;
		}
		return Read.skip;
	}
	auto buf = new char[length];
	size_t got = 0;
	while(got < length) {
		auto chunk = stdin.rawRead(buf[got .. $]);
		if(chunk.length == 0) return Read.eof; // truncated body: the peer is gone
		got += chunk.length;
	}
	result = buf.idup;
	return Read.message;
}

// Whether another message is already waiting, so work can be put off until the
// client pauses. stdin is unbuffered, so nothing can sit read but unseen in a
// stdio buffer while poll reports the pipe empty. Elsewhere the answer is no,
// which means checking at once, as without this.
private bool inputPending() {
	version(Emscripten) return false;
	else version(Posix) {
		import core.sys.posix.poll: poll, pollfd, POLLIN;
		import core.sys.posix.sys.stat: fstat, stat_t, S_IFMT, S_IFREG;
		import core.stdc.stdio: fileno;
		auto fd = fileno(stdin.getFP());
		// A regular file always polls readable, so input redirected from one
		// (a recorded session) would put every check off until the end.
		stat_t st;
		if(fstat(fd, &st) == 0 && (st.st_mode & S_IFMT) == S_IFREG) return false;
		auto p = pollfd(fd, POLLIN, 0);
		return poll(&p, 1, 0) > 0 && (p.revents & POLLIN) != 0;
	}
	else return false;
}

// \uD800-\uDFFF escapes that are not part of a high-low pair, rewritten as
// \uFFFD. Only escapes are looked at; an escaped backslash (\\u...) is text.
private string replaceLoneSurrogateEscapes(string json) {
	// Nearly every message has none: leave those as they are, uncopied.
	if(!json.canFind("\\ud", "\\uD")) return json;
	static int hexAt(string s, size_t i) {
		if(i + 6 > s.length || s[i] != '\\' || s[i+1] != 'u') return -1;
		int v = 0;
		foreach(c; s[i+2 .. i+6]) {
			int d = c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1;
			if(d < 0) return -1;
			v = v * 16 + d;
		}
		return v;
	}
	auto app = appender!string;
	for(size_t i = 0; i < json.length;) {
		if(json[i] != '\\' || i + 1 >= json.length) { app.put(json[i]); i++; continue; }
		auto u = hexAt(json, i);
		if(u >= 0xD800 && u <= 0xDBFF) {
			auto lo = hexAt(json, i + 6);
			if(lo >= 0xDC00 && lo <= 0xDFFF) { app.put(json[i .. i + 12]); i += 12; continue; }
			app.put("\\uFFFD"); i += 6; continue;
		}
		if(u >= 0xDC00 && u <= 0xDFFF) { app.put("\\uFFFD"); i += 6; continue; }
		app.put(json[i .. i + 2]); i += 2; // any other escape, kept whole
	}
	return app.data;
}

// ---------------------------------------------------------------- server

// A file:// URI carries percent escapes, and on Windows an extra leading slash
// before the drive letter. Both must go, or the name never matches a real path
// (which import resolution and the diagnostic source name both depend on).
private string uriToName(string uri, bool windows = windowsPaths) {
	enum scheme = "file://";
	if(!uri.startsWith(scheme)) return uri; // untitled:, vscode-vfs:, ... - keep verbatim
	auto p = uri[scheme.length .. $];
	// What precedes the path is a host. Empty or localhost means this machine;
	// any other is a network share, file://server/share/x for //server/share/x,
	// and dropping it would leave a relative name.
	auto slash = p.indexOf('/');
	auto host = slash < 0 ? p : p[0 .. slash];
	p = slash < 0 ? "" : p[slash .. $];
	if(host.length && host != "localhost") p = "//" ~ host ~ p;
	// Decode per segment: a literal %2F is part of a name, not a separator.
	try {
		string[] segs;
		foreach(seg; p.split("/")) segs ~= decodeComponent(seg);
		p = segs.join("/");
	} catch(Exception) {
		// A malformed escape (URIException), or one that decodes to invalid
		// UTF-8 such as a lone surrogate (UTFException): use it as-is.
	}
	// `file:///C:/x` decodes to `/C:/x`; on Windows the drive letter must lead.
	// Elsewhere /a:b is an ordinary path.
	if(windows && p.length >= 3 && p[0] == '/' && p[2] == ':') p = p[1 .. $];
	return canonicalPath(p, windows);
}

private string nameToUri(string name) {
	// A document we were given: answer with exactly what the client sent.
	if(auto known = name in uriForName) return *known;
	// Otherwise this is a file we reached ourselves, an import that is not
	// open. Escape it the way VS Code does, so the same file does not get a
	// second spelling: every byte but A-Z a-z 0-9 - . _ ~ and the separator,
	// including the drive letter's colon. (std.uri.encodeComponent leaves
	// !*'() alone.)
	auto app = appender!string;
	// A drive (c:/x) needs the slash an absolute path has; a network share
	// (//server/share/x) already carries the host's two.
	app.put(name.length >= 2 && name[1] == ':' ? "file:///" : name.startsWith("//") ? "file:" : "file://");
	foreach(char c; name) {
		if((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')
		   || c == '-' || c == '.' || c == '_' || c == '~' || c == '/') app.put(c);
		else app.put(format("%%%02X", cast(ubyte)c));
	}
	return app.data;
}

// The C runtime's _setmode, used by runLanguageServer. It has to be declared at
// module scope: inside a function, extern(C) still gets a nested D mangling
// (_D3lsp17runLanguageServerFZ8_setmodeUiiZi), and the Windows build fails to link.
version(Windows) private extern(C) int _setmode(int, int);

// The server: its state, and what it does with one message, apart from how
// messages arrive. Natively they come framed on stdin (runLanguageServer); in
// the browser, one call per message (the exports at the end of this file).
private final class Server {
	string[string] documents;          // uri -> text
	bool[string][string] publishedFor; // document uri -> uris it last published to
	bool[string][string] importsOf;    // document uri -> files its last check loaded
	bool[string] stale;                // documents waiting to be re-checked
	bool[string] loaded;               // files the check in progress has loaded
	bool shuttingDown = false;

	this() {
		handler = new ServerErrorHandler();
		moduleSourceOverride = &readOpenBuffer;
	}


	// A file that is not open can get its diagnostics from several documents
	// that import it, and each publish replaces the last. When one of them stops
	// reporting there (it closed, or no longer imports the file), clearing the
	// file would wipe what the others still report. Re-check the others instead:
	// each either reports the file's errors again or, if there are none now,
	// clears them itself.
	void clearUnlessShared(string file, string except) {
		bool shared_ = false;
		foreach(doc, files; publishedFor)
			if(doc != except && file in files && doc in documents) { stale[doc] = true; shared_ = true; }
		if(!shared_) sendNotification("textDocument/publishDiagnostics",
			JSONValue(["uri": JSONValue(file), "diagnostics": JSONValue(cast(JSONValue[])[])]));
	}

	// Errors can come from files other than the one being edited (imports, and
	// the prelude). Attributing those to the current document would point at a
	// line that may not even exist, so each diagnostic is published against the
	// file it actually belongs to, with positions computed from that file's own
	// text.
	void publishDiagnostics(string uri) {
		auto name = uriToName(uri);
		uriForName[name] = uri;
		loaded = null;
		auto diags = checkDocument(name, documents.get(uri, ""));
		importsOf[uri] = loaded;

		JSONValue[][string] byUri;
		byUri[uri] = [];               // always publish, to clear stale squiggles
		PositionMap[string] maps;
		ref PositionMap mapFor(Source s) {
			auto key = s is null ? "" : s.name;
			if(key !in maps) maps[key] = PositionMap(s is null ? "" : s.code);
			return maps[key];
		}
		// A location is only worth a link if it is a real file or a document the
		// client gave us. The prelude and operator scopes are built in, and
		// `.prelude` would become the URI file://.prelude, which opens nothing.
		bool linkable(const ref Diag x) {
			return x.located && (isAbsolute(x.file) || x.file in uriForName);
		}
		foreach(d; diags) {
			// Unlocated errors have nowhere better to go than the top of the
			// document being edited, flagged the way the CLI flags them. So do
			// errors inside a built-in scope, flagged with where they were.
			auto targetName = linkable(d) ? d.file : name;
			// An import that is open in the editor is checked on its own too,
			// and that check owns its squiggles. Publishing them from here as
			// well would have two checks overwriting each other's results.
			// Compared by name: VS Code and nameToUri may escape one path
			// differently, and VS Code treats both URIs as the same file.
			if(targetName != name && targetName in uriForName) continue;
			auto targetUri = nameToUri(targetName);
			auto range = linkable(d)
				? toLspRange(mapFor(d.src), d.startByte, d.endByte)
				: JSONValue(["start": JSONValue(["line": JSONValue(0), "character": JSONValue(0)]),
				             "end": JSONValue(["line": JSONValue(0), "character": JSONValue(0)])]);
			JSONValue j = JSONValue([
				"range": range,
				"severity": JSONValue(lspSeverity(d.severity)),
				"source": JSONValue("silq"),
				"message": JSONValue(linkable(d) ? d.message
					: d.located ? "(in " ~ d.file ~ "): " ~ d.message
					: "(location missing): " ~ d.message),
			]);
			if(d.related.length) {
				JSONValue[] rel;
				foreach(r; d.related) {
					if(!linkable(r)) continue;
					rel ~= JSONValue([
						"location": JSONValue([
							"uri": JSONValue(nameToUri(r.file)),
							"range": toLspRange(mapFor(r.src), r.startByte, r.endByte),
						]),
						"message": JSONValue(r.message),
					]);
				}
				if(rel.length) j["relatedInformation"] = JSONValue(rel);
			}
			if(targetUri !in byUri) byUri[targetUri] = [];
			byUri[targetUri] ~= j;
		}
		// Clear files this document put diagnostics in last time but not now.
		// Tracked per document: a global set would make checking one file clear
		// the diagnostics of every other open file.
		// An open document is skipped for the same reason as above: clearing it
		// would wipe the squiggles its own check put there. So is a file other
		// open documents still report into (clearUnlessShared).
		auto previously = publishedFor.get(uri, null);
		bool[string] nowPublished;
		foreach(u, ds; byUri) {
			if(ds.length) nowPublished[u] = true;
			sendNotification("textDocument/publishDiagnostics",
				JSONValue(["uri": JSONValue(u), "diagnostics": JSONValue(ds)]));
		}
		publishedFor[uri] = nowPublished;
		foreach(old, _; previously)
			if(old !in byUri && uriToName(old) !in uriForName) clearUnlessShared(old, uri);
	}

	// Documents waiting to be re-checked. A change marks the document and every
	// open document whose last check loaded it, directly or through another
	// import. Nothing else would re-check an importer until it was edited itself.
	void markStale(string uri) {
		if(uri in documents) stale[uri] = true;
		auto name = uriToName(uri);
		foreach(other, files; importsOf) if(other != uri && name in files) stale[other] = true;
	}
	// The checks run once the client pauses: typing sends a change per keystroke,
	// and checking each one would answer them all, late, one at a time. A client
	// that never pauses still gets them every `maxDeferred` messages.
	enum maxDeferred = 50;
	int deferred = 0;
	void flushStale() {
		auto uris = stale.keys;
		stale = null;
		deferred = 0;
		foreach(u; uris) if(u in documents) {
			// Each document on its own: this runs outside any one message's
			// handling, so anything thrown here, an Error included, would
			// otherwise end the server, and one document that cannot be
			// published must not keep the others from being checked.
			try publishDiagnostics(u);
			catch(Throwable e) {
				try sendNotification("textDocument/publishDiagnostics", JSONValue([
					"uri": JSONValue(u),
					"diagnostics": JSONValue([JSONValue([
						"range": JSONValue(["start": JSONValue(["line": JSONValue(0), "character": JSONValue(0)]),
						                    "end": JSONValue(["line": JSONValue(0), "character": JSONValue(0)])]),
						"severity": JSONValue(1),
						"source": JSONValue("silq"),
						"message": JSONValue("internal error while publishing diagnostics: " ~ e.msg),
					])]),
				]));
				catch(Exception) {}
			}
		}
	}

	// Once a document is open its content belongs to the client, and the server
	// must not read it from disk (LSP spec, didOpen). That holds when another
	// document imports it too: the importer sees the unsaved buffer.
	//
	// Every import a check reads comes through here, open or not, which is also
	// how the server learns what each document depends on.
	bool readOpenBuffer(string path, out string code) {
		auto file = absoluteFile(path);
		loaded[file] = true;
		if(auto uri = file in uriForName) if(auto text = *uri in documents) {
			code = *text;
			return true;
		}
		return false;
	}

	// Handle one message. Returns the exit code once the client sends `exit`,
	// -1 otherwise.
	int handle(string raw) {
		JSONValue msg;
		// JSON.stringify writes a lone surrogate in a buffer as an escape
		// (\ud800 alone), and std.json either rejects the whole message (the
		// native build: the didOpen or didChange is dropped) or decodes it to
		// invalid UTF-8 (the browser build's, which the check then cannot
		// read). Each is replaced by U+FFFD first, one UTF-16 unit like the
		// surrogate, so no position moves.
		try msg = parseJSON(replaceLoneSurrogateEscapes(raw));
		catch(Exception) return -1; // malformed frame: ignore rather than die
		// `in` requires an object; a body of [], 5 or null would throw here,
		// outside the try below, and take the server down.
		if(msg.type != JSONType.object) return -1;
		if("method" !in msg) return -1; // a response to something we sent; nothing to do yet

		// Every field access below can throw on a message that does not match
		// the shape we expect; a bad message must not end the session.
		try {
			auto method = strField(msg, "method");
			if(method is null) return -1;
			auto idp = "id" in msg;
			auto params = "params" in msg ? msg["params"] : JSONValue.emptyObject;

			switch(method) {
				case "initialize":
					if(idp) sendResult(*idp, JSONValue([
						"capabilities": JSONValue([
							// 1 = full document sync: silq re-checks whole buffers anyway.
							"textDocumentSync": JSONValue(1),
						]),
						"serverInfo": JSONValue(["name": JSONValue("silq"), "version": JSONValue("0.1")]),
					]));
					break;
				case "initialized":
					break;
				case "shutdown":
					shuttingDown = true;
					if(idp) sendResult(*idp, JSONValue(null));
					break;
				case "exit":
					return shuttingDown ? 0 : 1;
				case "textDocument/didOpen":
					if(auto td = "textDocument" in params) {
						auto uri = strField(*td, "uri");
						auto text = strField(*td, "text");
						if(uri !is null) {
							documents[uri] = text is null ? "" : text;
							// Open from now on, for every check: one that runs before this
							// document's own must already read its buffer and leave its
							// squiggles alone.
							uriForName[uriToName(uri)] = uri;
							// Importers now read this buffer rather than the file,
							// and it may differ from what they last saw on disk.
							markStale(uri);
						}
					}
					break;
				case "textDocument/didChange":
					if(auto td = "textDocument" in params) {
						auto uri = strField(*td, "uri");
						if(uri !is null) {
							// Full sync: the last change carries the whole document.
							if(auto changes = "contentChanges" in params) {
								if(changes.type == JSONType.array) {
									auto arr = changes.array;
									if(arr.length) {
										auto text = strField(arr[$-1], "text");
										if(text !is null) documents[uri] = text;
									}
								}
							}
							markStale(uri);
						}
					}
					break;
				case "textDocument/didClose":
					if(auto td = "textDocument" in params) {
						auto uri = strField(*td, "uri");
						if(uri is null) break;
						documents.remove(uri);
						uriForName.remove(uriToName(uri));
						// Clear everywhere this document put diagnostics, not
						// just its own file: errors it reported in an imported
						// file would otherwise stay there for the whole session
						// with nothing left able to clear them. Open documents
						// own their squiggles and are left alone.
						auto previously = publishedFor.get(uri, null);
						publishedFor.remove(uri);
						foreach(other, _; previously)
							if(uriToName(other) !in uriForName) clearUnlessShared(other, uri);
						sendNotification("textDocument/publishDiagnostics",
							JSONValue(["uri": JSONValue(uri), "diagnostics": JSONValue(cast(JSONValue[])[])]));
						// An importer saw this document's buffer while it was
						// open, and now sees the file on disk again, which an
						// unsaved close can leave different. It also reports
						// errors in it again, which it was kept from while open.
						markStale(uri);
						importsOf.remove(uri);
					}
					break;
				default:
					// The spec requires an answer to every request, so report
					// MethodNotFound rather than leaving the client hanging.
					if(idp) sendError(*idp, -32601, "unhandled method: " ~ method);
					break;
			}
		} catch(Exception e) {
			if(auto idp = "id" in msg) sendError(*idp, -32603, "internal error: " ~ e.msg);
		}
		return -1;
	}
}

int runLanguageServer() {
	// Unbuffered stdin is required, not an optimisation. A buffered read tries
	// to fill BUFSIZ before returning, but an LSP client keeps the pipe open
	// and sends one message at a time, so the fill blocks forever and a
	// complete request sits unread - the server looks hung. (It appears to work
	// when stdin is a file, because EOF ends the fill.)
	stdin.setvbuf(0, _IONBF);
	version(Windows) {
		// Text mode rewrites every \n as \r\n, so the "\r\n\r\n" header
		// terminator goes out as "\r\r\n\r\r\n" and no client can find it -
		// the server just looks hung. The framing is bytes; say so.
		import core.stdc.stdio: _fileno = fileno;
		enum _O_BINARY = 0x8000;
		_setmode(_fileno(stdout.getFP()), _O_BINARY);
		_setmode(_fileno(stdin.getFP()), _O_BINARY);
	}
	emit = (string body_) {
		stdout.write("Content-Length: ", body_.length, "\r\n\r\n", body_);
		stdout.flush();
	};
	auto server = new Server();
	scope(exit) if(emptyDir.length) {
		import std.file: rmdir;
		import std.exception: collectException;
		collectException(rmdir(emptyDir));
	}

	for(;;) {
		// Nothing is checked once the client has asked for shutdown: it is about
		// to send `exit`, and nobody would see the result.
		if(server.stale.length && !server.shuttingDown && (!inputPending() || ++server.deferred >= Server.maxDeferred))
			server.flushStale();
		string raw;
		final switch(readMessage(raw)) {
			case Read.eof: return server.shuttingDown ? 0 : 1; // EOF without shutdown is an error per spec
			case Read.skip: continue;
			case Read.message: break;
		}
		auto code = server.handle(raw);
		if(code >= 0) return code;
	}
}

// The browser build has no stream to read: the IDE's worker hands over one
// message per call, and calls silq_lsp_idle once it has nothing queued, which
// is when deferred checks run (inputPending is always false there). Both
// return what the server sent in response, as a JSON array. The returned text
// stays valid until the next call; the caller copies it.
version(Emscripten) {
	private __gshared Server embedded;
	private __gshared string embeddedReply;
	private __gshared string[] outbox;

	private void startEmbedded() {
		if(embedded) return;
		// Nothing has run main, which is what normally starts the D runtime
		// (and with it the module constructors that set the library path).
		import core.runtime: Runtime;
		import core.memory: GC;
		if(!Runtime.initialize()) throw new Error("the D runtime did not start");
		// The IDE runs one check per instance and then drops it, memory and
		// all. A collection could only run after the call returns (the
		// runtime cannot see the wasm stack, so it queues one), on an instance
		// about to be discarded: measured at about 2.5 ms of a 16 ms check.
		GC.disable();
		emit = (string body_) { outbox ~= body_; };
		embedded = new Server();
	}

	private const(char)* takeReply() {
		embeddedReply = "[" ~ outbox.join(",") ~ "]\0";
		outbox = null;
		return embeddedReply.ptr;
	}

	// Nothing may escape into JavaScript, building the reply included. A
	// failure answers with an empty list; the IDE treats a check that
	// publishes nothing for its document as failed, not as clean.
	private const(char)* answer(scope void delegate() work) {
		static immutable empty = "[]\0";
		try {
			startEmbedded();
			work();
			return takeReply();
		} catch(Throwable) {
			outbox = null;
			return empty.ptr;
		}
	}

	extern(C) const(char)* silq_lsp_message(const(char)* json) {
		return answer(() { embedded.handle(fromStringz(json).idup); });
	}

	extern(C) const(char)* silq_lsp_idle() {
		return answer(() {
			if(embedded.stale.length && !embedded.shuttingDown) embedded.flushStale();
		});
	}
}
