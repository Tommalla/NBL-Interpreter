all:
	cp docs/EBNF/NBL.cf .
	bnfc -haskell NBL.cf
	happy -gca ParNBL.y
	alex -g LexNBL.x
	cabal build -v

clean:
	rm -rf *.{cf,x,y}
	rm -rf {Abs,Doc,Lex,Par,Print,Skel,Test}NBL.*
	rm -rf ErrM.hs
