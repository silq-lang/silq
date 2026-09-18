// Written in the D programming language
// License: http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0

// Language Server Protocol front-end for silq (`silq --lsp`).
//
// One server, two clients: it speaks JSON-RPC over stdin/stdout, so the VSCode
// extension can spawn it directly, and the WASM IDE can drive the same build
// through a stream shim in a worker.
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
import astopt;
import util.path: dirName;
import std.path: isAbsolute;
import std.uri: decodeComponent, encodeComponent, URIException;

// A diagnostic from one type-check. Positions are kept as byte offsets into the
// owning Source: they are exact, and unlike silq's display-width columns they
// need no assumptions about tab stops or character widths.
private struct Diag {
	ErrorType severity;
	string message;
	bool located;        // false when the error carried no usable location
	Source src;
	int startByte, endByte;
	Diag[] related;
}

// Collects diagnostics in memory instead of printing them.
//
// This handler is created once and lives as long as the server, because scopes
// capture their handler permanently: getPreludeScope caches the prelude
// TopScope with whatever handler first built it, and imported modules are
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
		auto d = Diag(ty, msg, true, li.source, li.startByte, li.endByte);
		if(ty == ErrorType.note && diags.length) diags[$-1].related ~= d;
		else diags ~= d;
	}
}

private __gshared ServerErrorHandler handler;

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
// Both halves are guards, not workarounds for something silq is known to do:
// LocationInfo sets endByte = startByte + rep.length (ast/lexer.d), so the end
// can never precede the start and equals it only for a zero-length slice -
// which report() above already turns into an unlocated diagnostic. The `-1` end
// column is a separate artifact of `displayWidth(...) - 1` on an empty prefix,
// and has no byte-space equivalent.
private JSONValue toLspRange(const ref PositionMap map, int startByte, int endByte) {
	if(endByte <= startByte) endByte = map.nextCharBoundary(startByte);
	return JSONValue(["start": map.at(startByte), "end": map.at(endByte)]);
}

// ---------------------------------------------------------------- checking

// Type-check one in-memory buffer, returning the diagnostics it produced.
//
// Anything thrown by the front end is contained here: silq is assert-heavy and
// neither build script disables asserts, so a half-typed expression that trips
// an assertion would otherwise unwind out of the message loop and take the
// whole editor session with it. Recovering from a Throwable is a compromise -
// the alternative is losing every open document over one transient keystroke.
private Diag[] checkDocument(string name, string text) {
	handler.diags = null;
	// Imports resolve relative to the process CWD first (getActualPath), which
	// for a server spawned by an editor is arbitrary. Make the document's own
	// directory searchable for the duration of the check.
	auto savedPath = astopt.importPath;
	scope(exit) astopt.importPath = savedPath;
	// Only absolute entries: getShortPath feeds these to relativePath(), which
	// throws on a relative base, and a non-file document's dirName is ".".
	auto dir = dirName(name);
	if(dir.length && isAbsolute(dir)) astopt.importPath ~= dir;

	auto src = new Source(name, text ~ "\0\0\0\0"); // four NUL bytes required
	// The Source registry is a global array with a linear-scan lookup, so an
	// undisposed Source per keystroke both leaks and slows every later lookup.
	scope(exit) src.dispose();
	try {
		Expression[] exprs;
		TopScope sc;
		importModule(src, handler, exprs, sc, Location.init);
	} catch(Throwable e) {
		// Keep what was already collected: the errors found before the failure
		// are real and located, and dropping them for one synthetic message
		// makes a partly-broken file look like it has a single mystery error.
		return handler.diags ~ Diag(ErrorType.error, "internal error while checking this file: " ~ e.msg, false);
	}
	return handler.diags;
}

// ---------------------------------------------------------------- transport

private void sendMessage(JSONValue msg) {
	auto body_ = msg.toString();
	stdout.write("Content-Length: ", body_.length, "\r\n\r\n", body_);
	stdout.flush();
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
private Read readMessage(out string result) {
	size_t length = 0;
	bool haveLength = false;
	for(;;) {
		auto line = stdin.readln();
		if(line.length == 0) return Read.eof;
		auto header = line.strip();
		if(header.length == 0) break; // blank line ends the headers
		enum contentLength = "content-length:";
		if(header.toLower().startsWith(contentLength)) {
			try {
				length = header[contentLength.length .. $].strip().to!size_t;
				haveLength = true;
			} catch(Exception) {
				return Read.skip; // unparseable length; resynchronise on the next header block
			}
		}
	}
	// A header block with no length cannot be resynchronised: the body has no
	// terminator, so anything we read next is guesswork. Stop instead of
	// silently misreading every later message as headers.
	if(!haveLength) return Read.eof;
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

// ---------------------------------------------------------------- server

// A file:// URI carries percent escapes, and on Windows an extra leading slash
// before the drive letter. Both must go, or the name never matches a real path
// (which import resolution and the diagnostic source name both depend on).
private string uriToName(string uri) {
	enum scheme = "file://";
	if(!uri.startsWith(scheme)) return uri; // untitled:, vscode-vfs:, ... - keep verbatim
	auto p = uri[scheme.length .. $];
	// Decode per segment: a literal %2F is part of a name, not a separator.
	try {
		string[] segs;
		foreach(seg; p.split("/")) segs ~= decodeComponent(seg);
		p = segs.join("/");
	} catch(URIException) { /* malformed escape: use it as-is */ }
	// `file:///C:/x` decodes to `/C:/x`; the drive letter must lead.
	if(p.length >= 3 && p[0] == '/' && p[2] == ':') p = p[1 .. $];
	return p;
}

private string nameToUri(string name) {
	// A document we were given: answer with exactly what the client sent.
	if(auto known = name in uriForName) return *known;
	// Otherwise this is a file we reached ourselves (an import, or the
	// prelude), so build a file: URI and escape each segment.
	string encodePath(string p) {
		string[] segs;
		foreach(seg; p.split("/")) segs ~= encodeComponent(seg);
		return segs.join("/");
	}
	if(name.startsWith("/")) return "file://" ~ encodePath(name);
	if(name.length >= 2 && name[1] == ':') return "file:///" ~ encodePath(name); // Windows drive
	return "file://" ~ encodePath(name);
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
		extern(C) int _setmode(int, int);
		enum _O_BINARY = 0x8000;
		_setmode(_fileno(stdout.getFP()), _O_BINARY);
		_setmode(_fileno(stdin.getFP()), _O_BINARY);
	}
	handler = new ServerErrorHandler();

	string[string] documents;          // uri -> text
	bool[string][string] publishedFor; // document uri -> uris it last published to
	bool shuttingDown = false;

	// Errors can come from files other than the one being edited (imports, and
	// the prelude). Attributing those to the current document would point at a
	// line that may not even exist, so each diagnostic is published against the
	// file it actually belongs to, with positions computed from that file's own
	// text.
	void publishDiagnostics(string uri) {
		auto name = uriToName(uri);
		uriForName[name] = uri;
		auto diags = checkDocument(name, documents.get(uri, ""));

		JSONValue[][string] byUri;
		byUri[uri] = [];               // always publish, to clear stale squiggles
		PositionMap[string] maps;
		ref PositionMap mapFor(Source s) {
			auto key = s is null ? "" : s.name;
			if(key !in maps) maps[key] = PositionMap(s is null ? "" : s.code);
			return maps[key];
		}
		foreach(d; diags) {
			// Unlocated errors have nowhere better to go than the top of the
			// document being edited, flagged the way the CLI flags them.
			auto targetUri = d.located ? nameToUri(d.src.name) : uri;
			auto range = d.located
				? toLspRange(mapFor(d.src), d.startByte, d.endByte)
				: JSONValue(["start": JSONValue(["line": JSONValue(0), "character": JSONValue(0)]),
				             "end": JSONValue(["line": JSONValue(0), "character": JSONValue(0)])]);
			JSONValue j = JSONValue([
				"range": range,
				"severity": JSONValue(lspSeverity(d.severity)),
				"source": JSONValue("silq"),
				"message": JSONValue(d.located ? d.message : "(location missing): " ~ d.message),
			]);
			if(d.related.length) {
				JSONValue[] rel;
				foreach(r; d.related) {
					if(!r.located) continue;
					rel ~= JSONValue([
						"location": JSONValue([
							"uri": JSONValue(nameToUri(r.src.name)),
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
		foreach(old, _; publishedFor.get(uri, null)) if(old !in byUri) byUri[old] = [];
		bool[string] nowPublished;
		foreach(u, ds; byUri) {
			if(ds.length) nowPublished[u] = true;
			sendNotification("textDocument/publishDiagnostics",
				JSONValue(["uri": JSONValue(u), "diagnostics": JSONValue(ds)]));
		}
		publishedFor[uri] = nowPublished;
	}

	for(;;) {
		string raw;
		final switch(readMessage(raw)) {
			case Read.eof: return shuttingDown ? 0 : 1; // EOF without shutdown is an error per spec
			case Read.skip: continue;
			case Read.message: break;
		}
		JSONValue msg;
		try msg = parseJSON(raw);
		catch(Exception) continue; // malformed frame: ignore rather than die
		// `in` requires an object; a body of [], 5 or null would throw here,
		// outside the try below, and take the server down.
		if(msg.type != JSONType.object) continue;
		if("method" !in msg) continue; // a response to something we sent; nothing to do yet

		// Every field access below can throw on a message that does not match
		// the shape we expect; a bad message must not end the session.
		try {
			auto method = strField(msg, "method");
			if(method is null) continue;
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
							publishDiagnostics(uri);
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
							publishDiagnostics(uri);
						}
					}
					break;
				case "textDocument/didClose":
					if(auto td = "textDocument" in params) {
						auto uri = strField(*td, "uri");
						if(uri is null) break;
						documents.remove(uri);
						// Clear everywhere this document put diagnostics, not
						// just its own file: errors it reported in an imported
						// file would otherwise stay there for the whole session
						// with nothing left able to clear them.
						foreach(other, _; publishedFor.get(uri, null))
							sendNotification("textDocument/publishDiagnostics",
								JSONValue(["uri": JSONValue(other), "diagnostics": JSONValue(cast(JSONValue[])[])]));
						publishedFor.remove(uri);
						uriForName.remove(uriToName(uri));
						sendNotification("textDocument/publishDiagnostics",
							JSONValue(["uri": JSONValue(uri), "diagnostics": JSONValue(cast(JSONValue[])[])]));
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
	}
}
