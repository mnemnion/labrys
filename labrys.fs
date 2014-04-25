\ toolkit stuff


include ansi.fs
include stack-util.fs
include forge/card.fth

( Principles: 
	
	Cells are anonymous addresses.

	Atoms are *negative*. Bignums later: fastest is probably
	to use an allocated memory block below the noun addresses. 
	See: cards.

	Car down: 5 4 cons car -> 5

	Cycle: 

		Memoize the "here" memory address.

		Evaluate. This <might?> create many nouns, moving 
		the allotment up. 

		Pull the whole return noun onto the stack.

		Deallocate.

		Cons up the return noun onto the now fresh 'heap'.


)

: cons ( a b -- c) 
	here 2 cells allot dup >r 2! r> ; \ can be better...

: me ; 

: car cell + @ ;

: cdr @ ;

: caar cell + @ cell + @ ;

: cdar cell + @ @ ;

: cadr @ cell + @  ;

: cddr @ @ ;  

: atom? dup 1 < ; \ note that these are Forth native booleans

: cell? dup 1 > ;

: c-pair? dup 2@ 1 < >r 1 < r> + ; \ don't do this to an atom 

: --pair? 2dup 1 < >r 1 < r> +  \ -2 for 2 atoms
	 -2 = if
	 	 -1 
	 else 0 
	 then
	 ; \ a b -- a b c-?

variable cns-ct 0 cns-ct ! \ should come in handy for consing nouns

: ` negate ;               \ makes an atom

: `. dup negate . ;        \ prints an atom

: chop 2@ 2@ swap ; \  ( noun -- subject argument operator )
					\ 
					\         read the above repeatedly
					\     dispatching the operator leaves simply
					\ 
					\         ( subject argument -- )
					\         (    a  'op'   b   -- )

\ create a back-referenced block of address memory because, mirror land. 
here 19 cells allot 19 cells + value axops

: stuff ( verb slot container -- ) \ puts words where they go, no mirror land
  swap cells - ! ;

defer ax

defer chip

: #is  
   cr ." -is "
	nip ;

: #up 
	chip 1- ;

here 8 cells allot 8 cells + value brs 

: brstf brs stuff ;

: br0 cr ." not implemented " 0 -2 cons ax ; \ crash on [2 0]

' br0  0 brstf

'  me  1 brstf

' car  2 brstf

' cdr  3 brstf

' caar 4 brstf

' cdar 5 brstf

' cadr 6 brstf

' cddr 7 brstf 

: #br 
    recursive
	cr ." -br "
	cr ." -adr " `.
    dup -8 > if
    	brs swap
    	cells +  \ load br op
	    perform
	    cr ." -ret: " `.
	else 
		dup 2 mod 0 = if
			4 rshift
		    #br car
		else
			1+ 4 rshift
			#br cdr
		then
	then 
	;

: #ax          \ *[a 3 b c] -> *[*[a b] *[a c]]
	cr ." -ax"
	2@         \ a b c  --
	>r         \ a b    -- c
	over       \ a b a  -- c
	>r         \ a b    -- a c
	chip       \ *[a b] -- a c
	r> r>      \ *[a b] a c --
	chip       \ *[a b] *[a c]
	chip       \ *[*[n1] *[n2]]
	;	

: #equal  \ a b -- <0|-1>
	recursive
	2dup = if 
		2drop 0
	else 
		--pair? if
			2drop -1 
		else  			 \ a b --
			2@ >r 		 \ a carb -- cdrb
			swap         \ carb a -- cdrb
			2@ >r 		 \ carb cara -- cdra cdrb
			#equal       \ a-? -- cdra cdrb
			r> r>        \ a-? cdra cdrb --
			#equal       \ a-? b-? --
			+            \ ab-? --
			0= if 0 
				else -1 
			then
		then
	then 
	;

: #eq  \ a b -- <0|-1>
    cr ." -eq " .s
	chip 2@
	cr ." -is eq: " .s
	#equal ;

: #fz cr ." requires hardware" 5 ax ; \ crash on 5

: #cel         \ a b -- <0|-1>  
	cr ." -cel" 
	.s
	chip	   \ *[a b] --
	1 < if     \ atom?
		cr ." atom"
		-1 
	else       \ noun?
		cr ." cell! "
		0 
	then  
	;

: axstf axops stuff ;

' #is  0  axstf

' #up  1  axstf

' #br  2  axstf

' #ax  3  axstf

' #eq  4  axstf

' #fz  5  axstf

' #cel 6  axstf

: eval 
	cr .bo .r ." Ξ " .!
    axops swap
    ." -op: " `. 
    cr .s
    cells +  \ b a operator --  
    cr ." execute on: " .s
    perform		
    ;


: juggle                \ *[a [b c] d] -> [*[a b c] *[a d]]
		swap			\  a [b c] d     --
		>r 				\  a [b c]       -- d
		over            \  a [b c] a     -- d 
		-rot            \  a a [b c]     -- d
		chip            \  a *[a b c]    -- d
		swap            \  *[n] a        -- d
		r>              \  *[n] a d      --
 	    chip            \  *[n] *[a d]   --
        cons            \  [*[n] *[a d]] --
    ;

:noname \ chip (a b -- noun)
	2@ swap
	dup 1 < if 
		eval
	else
		juggle 
	then ; is chip

:noname \ ax  ( noun -- noun ) 
	2@ chip ; is ax



\ test nouns 


: [ 1 cns-ct +! ;        

: ] cons -1 cns-ct +! ; \ actually does the construction

: is1 [ [ 4 ` 5 ` ] [ 0 ` 23 ` ] ] ;

: up1 [ 42 ` [ 1 ` [ 0 22 ` ] ] ] ;

: br1 [ 22 ` [ 1 ` [ 2 ` 1 ` ] ] ] ;

: bal1 [ [ -1 -2 ] [ -3 -4 ] ] ;

: dst1 [ -23 [ [ -2 -1 ] [ -1 [ -2 -1 ] ] ] ] ;

: ax1 [ -23 [ -3 [ [ 0 -4 ] [ 0 [ 0 -42 ] ] ] ] ] ;

: eq1 [ [ -4 -5 ] [ -4 [ -2 -1 ] ] ] ;

: eq0 [ [ -4 -4 ] [ -4 [ -2 -1 ] ] ] ;

: cel1 [ -23 [ -6 [ -2 -1 ] ] ] ;

: cel0 [ [ -23 -42 ] [ -6 [ -2 -1 ] ] ] ;

: tst is1 ax up1 ax br1 ax dst1 ax 2@ 
	  ax1 ax eq0 ax eq1 ax cel0 ax cel1 ax 
      cr .bo .r ` . ` . ` . ` . ` . ` . ` . ` . ` . ` . .! 
      \  -1 3 4 hd-§-¢--!
      \  2 rshift
      \  cr ocpr 
      ;

: ifbr

	 s" Ξ [a 8 b c] → Ξ [a b] → n → Ξ [a Ξ [c 2 (n + 2)]]" 
	 .\n .bo .w .tall .! cr cr ;

page

.\n s" LABRYS" .c .tall .! cr

cr cr ifbr cr cr

: Ξ ax ;



