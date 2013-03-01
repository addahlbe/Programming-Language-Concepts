" Vim syntax file
" Language:     gratr
" Filenames:    *.gr
" Maintainers:  Nao Hirokawa <hirokawa@jaist.ac.jp>
" URL:          http://www.jaist.ac.jp/~hirokawa/

" To use this syntax highlight, put this file in ~/.vim/syntax/
" and add the next line to ~/.vimrc:
"
"   au BufNewFile,BufRead *.gr setf gratr

if version < 600
  syntax clear
elseif exists("b:current_syntax") && b:current_syntax == "gratr"
  finish
endif

syn case match

syn match    gratrComment   "%.*$"
syn match    gratrUid       "\<\u\w*\>"
syn match    gratrScript    "\<\(Syntactic\|Lexical\|Whitespace\|Rules\|Vars\)\>"

" Errors
syn match    gratrBraceErr   "}"
syn match    gratrBrackErr   "\]"
syn match    gratrParenErr   ")"

" Enclosing delimiters
syn region   gratrEncl transparent matchgroup=gratrKeyword start="(" matchgroup=gratrKeyword end=")" contains=ALLBUT,@gratrContained,gratrParenErr
syn region   gratrEncl transparent matchgroup=gratrKeyword start="\[" matchgroup=gratrKeyword end="\]" contains=ALLBUT,@gratrContained,gratrBrackErr
" syn region   gratrString start=+"+  skip=+\\"+  end=+"+  contains=basicSpecial
" syn region   gratrString start=+'+  skip=+\\'+  end=+'+  contains=basicSpecial
syn region   gratrString start=+"+  end=+"+  contains=basicSpecial
syn region   gratrString start=+'+  end=+'+  contains=basicSpecial

syn match    gratrOperator     "\<sos\>"
syn match    gratrOperator     "\<eos\>"
syn match    gratrKeyword      "->"
syn match    gratrKeyword      "=>"
syn match    gratrKeyword      ","
syn match    gratrKeyword      "\."
syn match    gratrUid          ":"

syn match    gratrKeyword     "|"
syn match    gratrKeyword     "?"
syn match    gratrKeyword     "\*"
syn match    gratrKeyword     "+"
syn match    gratrKeyword     "#"

" Synchronization
syn sync minlines=50
syn sync maxlines=500

if version >= 508 || !exists("did_gratr_syntax_inits")
  if version < 508
    let did_gratr_syntax_inits = 1
    command -nargs=+ HiLink hi link <args>
  else
    command -nargs=+ HiLink hi def link <args>
  endif

  HiLink gratrBraceErr	   Error
  HiLink gratrBrackErr	   Error
  HiLink gratrParenErr	   Error

  HiLink gratrCommentErr   Error

  HiLink gratrCountErr	   Error
  HiLink gratrCharErr	   Error
  HiLink gratrErr	   Error

  HiLink gratrScript	   Include
  HiLink gratrComment	   Comment
  HiLink gratrKeyword	   Keyword
  HiLink gratrOperator	   Constant
  HiLink gratrString	   String
  HiLink gratrUid          Identifier
  HiLink gratrEncl	   Keyword

  delcommand HiLink
endif

let b:current_syntax = "gratr"

" vim: ts=8
