#!/bin/bash

VERSION=$(cat version-ldc.txt)

if [[ "$OSTYPE" == "linux-gnu" ]]; then
    NAME="ldc2-$VERSION-linux-x86_64"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    NAME="ldc2-$VERSION-osx-x86_64"
fi

if [ -d $NAME ]; then
    LDMD="./$NAME/bin/ldmd2";
else
    LDMD="ldmd2"
fi

std="./$NAME/import/std/uni/package.d ./$NAME/import/std/internal/unicode_tables.d ./$NAME/import/std/utf.d ./$NAME/import/std/format/package.d ./$NAME/import/std/ascii.d ./$NAME/import/std/conv.d ./$NAME/import/std/json.d"

wasm="-version=inline_concat -Iutil/webassembly/arsd-webassembly -Iutil/wasm-stub  util/webassembly/arsd-webassembly/std/*.d -i=util/webassembly/arsd-webassembly/core util/webassembly/arsd-webassembly/core/arsd/memory_allocation.d util/webassembly/arsd-webassembly/core/arsd/aa.d util/webassembly/arsd-webassembly/core/arsd/objectutils.d util/webassembly/arsd-webassembly/core/internal/utf.d util/webassembly/arsd-webassembly/core/arsd/utf_decoding.d util/webassembly/arsd-webassembly/object.d"

$LDMD $wasm $std -version=WASM -mtriple=wasm64-unknown-unknown-wasm -L-mwasm64 -L--error-limit=0 -L--no-entry -J. -Jlibrary *.d ast/*.d util/*.d -noboundscheck -ofsilq $@

#$LDMD -Iwebassembly/arsd-webassembly -Iutil/wasm-stub -version=WASM -mtriple=wasm64-unknown-unknown-wasm -L-mwasm64 -L--no-entry -L--error-limit=0 -J. -Jlibrary *.d ast/*.d util/*.d -ofsilq $@

# $LDMD -Iwebassembly/arsd-webassembly -Iutil/wasm-stub -version=WASM -mtriple=wasm32-unknown-unknown-wasm -L-mwasm32 -L-allow-undefined -L--no-entry -J. -Jlibrary *.d ast/*.d util/*.d -ofsilq $@
