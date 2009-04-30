;;
;; Lexical analysis
;;

(defconst verilog-token-comma		?,      "Verilog-lex ','.")
(defconst verilog-token-semi		?;	"Verilog-lex ';'.")
(defconst verilog-token-equal		?=	"Verilog-lex '='.")
(defconst verilog-token-par		?(	"Verilog-lex '('.")
(defconst verilog-token-en		?)	"Verilog-lex ')'.")
(defconst verilog-token-bra		?{	"Verilog-lex '{'.")
(defconst verilog-token-ce		?}	"Verilog-lex '}'.")

;; Lexical tokens specific to verilog-lex-decl
(defconst verilog-token-ASSIGN		300	"Verilog-lex 'KEYWORD'.")
(defconst verilog-token-PARAMETER	306	"Verilog-lex 'KEYWORD'.")
(defconst verilog-token-SIGNED		307	"Verilog-lex 'KEYWORD'.")
(defconst verilog-token-bracketed	311	"Verilog-lex '[...]'; value is what's within brackets.")
(defconst verilog-token-decl-const	301	"Verilog-lex declare constant.")
(defconst verilog-token-decl-wire	302	"Verilog-lex declare wire.")
(defconst verilog-token-direction	303	"Verilog-lex directional.")
(defconst verilog-token-ignore-begin	304	"Verilog-lex block to ignore begin.")
(defconst verilog-token-ignore-end	305	"Verilog-lex block to ignore end.")
(defconst verilog-token-symbol		310	"Verilog-lex symbol.")
(defconst verilog-token-synth-enum	312	"Verilog-lex Synopsys enum token; value is name of enumeration.")
(defconst verilog-token-type		308	"Verilog-lex data type.")
(defconst verilog-token-keyword		313	"Verilog-lex generic keyword.")

(defconst verilog-lex-keywords
  '(
    ("assign"		verilog-token-ASSIGN)
    ("bit"		verilog-token-type)
    ("byte"		verilog-token-type)
    ("class"		verilog-token-ignore-begin)
    ("clocking"		verilog-token-ignore-begin)
    ("covergroup"	verilog-token-ignore-begin)
    ("endclass"		verilog-token-ignore-end)
    ("endclocking"	verilog-token-ignore-end)
    ("endfunction"	verilog-token-ignore-end)
    ("endgroup"		verilog-token-ignore-end)
    ("endproperty"	verilog-token-ignore-end)
    ("endsequence"	verilog-token-ignore-end)
    ("endtask"		verilog-token-ignore-end)
    ("function"		verilog-token-ignore-begin)
    ("genvar"		verilog-token-decl-const)
    ("inout"		verilog-token-direction)
    ("input"		verilog-token-direction)
    ("int"		verilog-token-type)
    ("integer"		verilog-token-type)
    ("localparam"	verilog-token-decl-const)
    ("logic"		verilog-token-type)
    ("longint"		verilog-token-type)
    ("output"		verilog-token-direction)
    ("parameter"	verilog-token-PARAMETER)
    ("property"		verilog-token-ignore-begin)
    ("randsequence"	verilog-token-ignore-begin)
    ("real"		verilog-token-type)
    ("reg"		verilog-token-type)
    ("sequence"		verilog-token-ignore-begin)
    ("shortint"		verilog-token-type)
    ("shortreal"	verilog-token-type)
    ("signed"		verilog-token-signing)
    ("supply"		verilog-token-decl-const)
    ("supply0"		verilog-token-decl-const)
    ("supply1"		verilog-token-decl-const)
    ("task"		verilog-token-ignore-begin)
    ("time"		verilog-token-type)
    ("tri"		verilog-token-decl-wire)
    ("tri0"		verilog-token-decl-wire)
    ("tri1"		verilog-token-decl-wire)
    ("triand"		verilog-token-decl-wire)
    ("trior"		verilog-token-decl-wire)
    ("trireg"		verilog-token-type)
    ("wand"		verilog-token-decl-wire)
    ("wire"		verilog-token-decl-wire)
    ("wor"		verilog-token-decl-wire)
    )
  "Map of keyword and token to return for `verilog-lex'.")

(defun verilog-lex (begin end for-decls)
  "Lexically analyze Verilog text between BEGIN to END into tokens.
With FOR-DECL true, parse only for declarations.  Returns list of
tokens, with each token a list of the text for that token and the
verilog-token-TYPE."
  (let ((functask 0)
	tokens token keywd ignore-next-symbol)
    (save-excursion
      (goto-char begin)
      (while (< (point) end)
	;;(if dbg (setq dbg (cons (format "Pt %s  Vec %s   Kwd'%s'\n" (point) vec keywd) dbg)))
	(cond
	 ;; For performance it's better if frequent cases are first
	 ((looking-at "//")
	  (when (looking-at "[^\n]*synopsys\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
	    (setq tokens (cons (list (match-string 1) verilog-token-synth-enum) tokens)))
	  (search-forward "\n"))
	 ((looking-at "/\\*")
	  (forward-char 2)
	  (when (looking-at "[^*]*synopsys\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
	    (setq tokens (cons (list (match-string 1) verilog-token-synth-enum) tokens)))
	  (or (search-forward "*/")
	      (error "%s: Unmatched /* */, at char %d" (verilog-point-text) (point))))
	 ((looking-at "(\\*")
	  (forward-char 2)
	  (or (looking-at "\\s-*)")   ; It's an "always @ (*)"
	      (search-forward "*)")
	      (error "%s: Unmatched (* *), at char %d" (verilog-point-text) (point))))
	 ((eq ?\" (following-char))
	  (or (re-search-forward "[^\\]\"" nil t)	;; don't forward-char first, since we look for a non backslash first
	      (error "%s: Unmatched quotes, at char %d" (verilog-point-text) (point))))
	 ;; []: Grab all text to ending ].  Probably should match bracket pairs and strip comments, but old version didn't
	 ((looking-at "\\[[^]]+\\]")
	  (goto-char (match-end 0))
	  (setq tokens (cons (list (match-string 0) verilog-token-bracketed) tokens)))
	 ;; Single character tokens we just pass through
	 ((looking-at "[;,=(){}]")
	  (setq tokens (cons (list (following-char) (following-char)) tokens))
	  (forward-char 1))
	 ;; Ifdef, ignore name of define
	 ((looking-at "`ifn?def\\>")
	  (goto-char (match-end 0))
	  (setq ignore-next-symbol t))
	 ;; Normal identifier
	 ((looking-at "[`a-zA-Z0-9_$]+")
	  (goto-char (match-end 0))
	  ;; buffer-substring is faster than match-string, and this is hot code.
	  (setq keywd (buffer-substring-no-properties (match-beginning 0) (match-end 0)))
	  (cond (ignore-next-symbol	;; preproc identifier after `ifdef
		 (setq ignore-next-symbol nil))
		((member keywd verilog-keywords)
		 (setq token (assoc keywd verilog-lex-keywords))
		 ;; Now you'll see why the token list has text first then the token number;
		 ;; we can just return the assoc result directly
		 (cond ((eq token verilog-token-ignore-begin)
			(setq functask (1+ functask)))
		       ((eq token verilog-token-ignore-end)
			(setq functask (1- functask)))
		       (token
			(setq tokens (cons token tokens)))
		       (t
			(setq tokens (cons (list keywd verilog-token-keyword) tokens)))))
		;; Must be typedef or symbol.  For speed, ignore if inside begin/end
		((and (eq functask 0)
		      (verilog-typedef-name-p keywd))
		   (setq tokens (cons (list keywd verilog-token-typedef) tokens)))
		;; Normal user symbol
		((eq functask 0)
		 (setq tokens (cons (list keywd verilog-token-symbol) tokens)))))
	 ;; Escaped identifier -- note we remember the \ if escaped
	 ((looking-at "\\\\[^ \t\n\f]+")
	  (goto-char (match-end 0))
	  (when (eq functask 0)
	    (setq tokens (cons (list (concat (match-string-no-properties 0) " ") ;; Escaped ID needs space at end
				     verilog-token-symbol)
			       tokens))))
	 ;; Default
	 (t
	  (forward-char 1)))
	;; End of parser while
	(skip-syntax-forward " "))
      tokens)))

