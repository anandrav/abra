" Vim syntax file for Abra

if exists("b:current_syntax") && b:current_syntax == "abra"
  finish
endif

syn region  abraString        start=+"+  skip=+\\\\\|\\"+  end=+"\|$+
syn match   abraNumber        "\<[0-9]\d*\(_\d\+\)*\>"
syn match   abraDecimalNumber "\<\(\d\+\(_\d\+\)*\)\?\.\d\+\(_\d\+\)*\>"
syn match   abraOperator      display "\%(+\|-\|/\|*\|=\|\^\|&\||\|!\|>\|<\|%\)=\?"
syn keyword abraConditional	  if else match
syn keyword abraRepeat		    while
syn keyword abraBranch		    break continue
syn keyword abraType		      void bool int float string array list
syn keyword abraStatement		  return 
syn keyword abraBoolean		    true false
syn keyword abraIdentifier    var let
syn keyword abraReserved		  fn implement import interface type use
syn match   abraFuncCall      "\w\(\w\)*("he=e-1,me=e-1

hi def link abraString        String
hi def link abraNumber		    Number
hi def link abraDecimalNumber Number
hi def link abraOperator      Operator
hi def link abraConditional		Conditional
hi def link abraRepeat		    Repeat
hi def link abraBranch		    Conditional
hi def link abraType			    Type
hi def link abraStatement		  Statement
hi def link abraFuncCall      Function
hi def link abraError		      Error
hi def link abraBoolean		    Boolean
hi def link abraIdentifier		Identifier
hi def link abraReserved		  Keyword

if !exists("b:current_syntax")
  let b:current_syntax = "abra"
endif
