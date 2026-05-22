" Vim syntax file for Abra

if exists("b:current_syntax")
  finish
endif

" --- 1. Keywords & Definitions (Lower Priority) ---

" Constants
syn keyword abraBoolean         true false
syn keyword abraNil             nil

" Attributes (e.g. #host)
syn match   abraAttribute       "#\s*[a-zA-Z_]\w*"

" Control Flow
syn keyword abraConditional     if else match
syn keyword abraRepeat          while for in
syn keyword abraStatement       return break continue

" Storage & Structure
syn keyword abraKeyword         let var interface extend implement impl outputtype use as except
syn keyword abraFunctionKey     fn

" `type` keyword (as match, not keyword, so other matches can coexist)
syn match   abraTypeKw          "\<type\>"

" Operators
syn keyword abraOperatorKey     and or not
" Matches: + - * / % ^ = += == != < > <= >= |
syn match   abraOperator        "\%(+\|-\|/\|*\|%\|\^\|=\|!\|>\|<\||\)\%(= \?\)\?"
syn match   abraOperator        "\.\."
syn match   abraOperator        "->"
syn match   abraOperator        "?"

" Types
syn keyword abraType            void bool int float string
" Match Capitalized words as Types
syn match   abraCustomType      "\<\u\w*\>"
" Generic Parameters (T, U, T1, etc - uppercase letter + digits/underscores only)
syn match   abraGeneric         "\<\u[0-9_]*\>"

" Numbers (allow underscores as digit separators: 1_000, 3.14_15)
syn match   abraNumber          "\<\d[0-9_]*\>"
syn match   abraFloat           "\<\d[0-9_]*\.\d[0-9_]*\>"

" Variants (e.g. .None, .some, .Ok, .err). Excludes method calls (obj.field, arr[i].field).
" The dot must not be preceded by a word char, ')', or ']'.
syn match   abraVariant         "\%([^A-Za-z0-9_)\]]\|^\)\zs\.[a-zA-Z_]\w*"

" Functions
syn match   abraFuncDef         "fn\s\+\w\+" contains=abraFunctionKey
" Function calls: identifier followed by `(`, but NOT preceded by `.`
" (so `.some(x)` stays a variant and `arr.push(x)` isn't styled as a call).
syn match   abraFuncCall        "\.\@<!\<\w\+\s*("he=e-1

" Variants in enum-like `type Name = variant | variant(T) | ...` definitions.
" Matches an identifier on a `type` line preceded (on the same line) by `=` or `|`.
" Variable-width lookbehind; uses `.*` so a `|` after an earlier `(...)` can match.
" Defined AFTER abraFuncCall so it wins via vim's "last-defined at same position"
" priority (otherwise abraFuncCall would claim `some(`, `Break(`, etc.).
syn match   abraVariantDecl     "\%(^\s*type\>.*[=|]\s*\)\@<=\<\h\w*\>"

" --- 2. Regions (Higher Priority - Overrides matchers above) ---

" Shebang
syn match   abraShebang         "\%^#!.*"

" String escape sequences
syn match   abraEscape          contained "\\[ntr\\'\"]"
syn match   abraEscape          contained "\\x\x\{2}"

" Strings: single-line double- and single-quoted. Defined BEFORE abraStringMulti
" so the multi-line region (last-defined) wins at `"""` per vim priority rules.
syn region  abraString          start=+"+  skip=+\\\\\|\\"+  end=+"\|$+ contains=abraEscape,@Spell
syn region  abraString          start=+'+  skip=+\\\\\|\\'+  end=+'\|$+ contains=abraEscape,@Spell
" Strings: triple-quoted multi-line
syn region  abraStringMulti     start=+"""+ end=+"""+ contains=abraEscape,@Spell

" Ensure multi-line strings are recognized when reformatting from anywhere in
" the file (without this, opening near the end of a long multi-line literal
" can mis-classify content as code).
syn sync minlines=50

" TODOs in comments
syn keyword abraTodo            TODO FIXME XXX contained

" Comments
" We define these LAST so they override Operators (/) and Types (Capitalized words)
syn region  abraCommentLine     start="//"  end="$" contains=abraTodo,@Spell
syn region  abraCommentBlock    start="/\*" end="\*/" contains=abraCommentBlockNest,abraTodo,@Spell
syn region  abraCommentBlockNest start="/\*" end="\*/" contains=abraCommentBlockNest,abraTodo,@Spell contained


" --- 3. Highlighting Links ---

hi def link abraShebang         PreProc
hi def link abraTodo            Todo
hi def link abraCommentLine     Comment
hi def link abraCommentBlock    Comment
hi def link abraString          String
hi def link abraStringMulti     String
hi def link abraEscape          SpecialChar
hi def link abraNumber          Number
hi def link abraFloat           Float
hi def link abraBoolean         Boolean
hi def link abraNil             Constant

" Variants -> Type group (distinct from String/Constant)
hi def link abraVariant         Type
hi def link abraVariantDecl     Type
hi def link abraAttribute       PreProc

" Keywords -> Statement (Yellow/Brown)
hi def link abraConditional     Conditional
hi def link abraRepeat          Repeat
hi def link abraStatement       Statement
hi def link abraKeyword         Statement
hi def link abraTypeKw          Statement
hi def link abraFunctionKey     Statement
hi def link abraOperatorKey     Operator
hi def link abraOperator        Operator

" Types -> Type (Green/Blue)
hi def link abraType            Type
hi def link abraCustomType      Type
hi def link abraGeneric         Type

" Functions -> Function (Cyan/Blue)
hi def link abraFuncDef         Function
hi def link abraFuncCall        Function

let b:current_syntax = "abra"
