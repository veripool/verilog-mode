;;; verilog.el --- major mode for editing verilog source in Emacs

;; Copyright (C) 1996 Free Software Foundation, Inc.

;; Author: Michael McNamara (mac@verilog.com) 
;; Keywords: languages

;; This file is part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;;; Commentary:

;;; This mode borrows heavily from the pascal-mode and the cc-mode of emacs

;;; USAGE
;;; =====

;;; Emacs should enter Verilog mode when you find a Verilog source file.
;;; When you have entered Verilog mode, you may get more info by pressing
;;; C-h m. You may also get online help describing various functions by:
;;; C-h f <Name of function you want described>

;;; to set up auto mode, include stuff like this in your .emacs:
; (autoload 'verilog-mode "verilog-mode" "Verilog mode" t )
; (setq auto-mode-alist (cons  '("\\.v\\'" . verilog-mode) auto-mode-alist))
; (setq auto-mode-alist (cons  '("\\.dv\\'" . verilog-mode) auto-mode-alist))
;;; to get pretty colors:
;(cond ((window-system)
;       (copy-face 'default font-lock-keyword-face)
;       (set-face-foreground font-lock-keyword-face     "tan")
;       (make-face-unbold font-lock-keyword-face)
;       (set-face-foreground font-lock-function-name-face "red") 
;       (set-face-foreground font-lock-type-face        "#efc80c") ; yellow
;       (set-face-foreground font-lock-string-face      "lightskyblue1")
;       (set-face-foreground font-lock-comment-face     "#00e000")
;       (set-face-foreground font-lock-doc-string-face  "gold")
;       (add-hook 'verilog-mode-hook 'font-lock-mode)))


;;; If you want to customize Verilog mode to fit you better, you may add
;;; these lines (the values of the variables presented here are the defaults):
;;;
;;; ;; User customization for Verilog mode
;;; (setq verilog-indent-level       3
;;;       verilog-case-indent        2
;;;       verilog-auto-newline       t
;;;       verilog-tab-always-indent  t
;;;       verilog-auto-endcomments   t
;;;       verilog-auto-lineup        '(all))

;;; KNOWN BUGS / BUGREPORTS
;;; =======================
;;; This is beta code, and likely has bugs. Please report any and all
;;; bugs to me at mac@verilog.com.
;; 
;; $Header$
;; $Log$
;; Revision 1.93  1996/01/03 22:21:24  mac
;; Fix some silly typos; for now on I promise to _at least_ byte-compile
;; and load the file before I send it out...
;;
; Revision 1.92  1996/01/03  21:40:50  mac
; Fix a few bugs:
;  a typo, hints to use autoload, incorrect indentation of module as
;  typed, named blocks where not handled. [ Thanks Drew!]
;
; There was a bug in the auto endcomment for `else and `endif (comment
;  went to the wrong spot)
;
; Changed some features:
; The auto comments used to add comments like:
;  endmodule /* module: foo */
;  endfunction /* function: bar */
;
;  I deleted the "module:" and "function:" parts as they are rather obvious...
;
; The end for named blocks is now marked.
;
; Added some features:
;  Now M-C-t (esc tab) does some reasonable completion;
;  it tries to get appropriate keywords based on scope;
;  it tries to get tasks based on scope;
;  it tires to get modules based on scope.
;
;  eg,
;  module foo;
;    ini<M-TAB> fills with initial
;
;  module barinsky;
;  endmodule
;
;  module foo;
;
;   ba<M-TAB> fills with barinsky
;
; and so on.
;
; However, it still needs more work (vestiges of pascal mode remain)
;
; Revision 1.91  1996/01/03  17:19:02  mac
; Base of publically released version
;
;;; Code:

(defconst verilog-mode-version "$$Revision$$"
  "Version of this verilog mode.")

(defvar verilog-mode-abbrev-table nil
  "Abbrev table in use in Verilog-mode buffers.")

(define-abbrev-table 'verilog-mode-abbrev-table ())

(defvar verilog-mode-map ()
  "Keymap used in Verilog mode.")

(if verilog-mode-map
    ()
  (setq verilog-mode-map (make-sparse-keymap))
  (define-key verilog-mode-map ";"        'electric-verilog-semi)
  (define-key verilog-mode-map ":"        'electric-verilog-colon)
  (define-key verilog-mode-map "="        'electric-verilog-equal)
  (define-key verilog-mode-map "\`"       'electric-verilog-tick)
  (define-key verilog-mode-map "\r"       'electric-verilog-terminate-line)
  (define-key verilog-mode-map "\t"       'electric-verilog-tab)
  (define-key verilog-mode-map "\M-\t"    'verilog-complete-word)
  (define-key verilog-mode-map "\M-?"     'verilog-show-completions)
  (define-key verilog-mode-map "\177"     'backward-delete-char-untabify)
  (define-key verilog-mode-map "\M-\C-h"  'verilog-mark-defun)
  (define-key verilog-mode-map "\C-c\C-b" 'verilog-insert-block)
  (define-key verilog-mode-map "\C-cb"    'verilog-label-be)
  (define-key verilog-mode-map "\M-*"     'verilog-star-comment)
  (define-key verilog-mode-map "\C-c\C-c" 'verilog-comment-area)
  (define-key verilog-mode-map "\C-c\C-u" 'verilog-uncomment-area)
  (define-key verilog-mode-map "\M-\C-a"  'verilog-beg-of-defun)
  (define-key verilog-mode-map "\M-\C-e"  'verilog-end-of-defun)
  (define-key verilog-mode-map "\C-c\C-d" 'verilog-goto-defun)
  (define-key verilog-mode-map "\C-c\C-o" 'verilog-outline)
  )

(defvar verilog-imenu-generic-expression
  '("^[ \t]*\\(module\\|macromodule\\|primitive\\)[ \t\n]+\\([a-zA-Z0-9_.:]+\\)" . (2))
  "Imenu expression for Verilog-mode.  See `imenu-generic-expression'.")
  
;;;
;;; Regular expressions used to calculate indent, etc.
;;;
(defconst verilog-symbol-re      "\\<[a-zA-Z_][a-zA-Z_0-9.]*\\>")
(defconst verilog-case-re        "\\(\\<case[xz]?\\>\\)")
(defconst verilog-beg-block-re   "\\<\\(begin\\|case\\|casex\\|casez\\|fork\\)\\>")
(defconst verilog-beg-block-re-1 "\\<\\(begin\\)\\|\\(case[xz]?\\)\\|\\(fork\\)\\>")
(defconst verilog-end-block-re   "\\<\\(end\\|join\\|endcase\\)\\>")
(defconst verilog-end-block-re-1 "\\(\\<end\\>\\)\\|\\(\\<endcase\\>\\)\\|\\(\\<join\\>\\)")
(defconst verilog-beg-tf-re      "\\<\\(task\\|function\\)\\>")
(defconst verilog-end-tf-re      "\\<\\(endtask\\|endfunction\\)\\>")
(defconst verilog-end-tf-re-1    "\\(\\<endtask\\>\\)\\|\\(\\<endfunction\\>\\)")
(defconst verilog-declaration-re     "\\<\\(in\\(put\\|out\\|teger\\)\\|output\\|event\\|re\\(al\\|g\\|eltime\\)\\|time\\|tri\\(0\\|1\\|and\\|or\\|reg\\)\\|w\\(and\\|or\\|ire\\)\\)\\>")
(defconst verilog-defun-re       "\\<\\(module\\|macromodule\\|primitive\\)\\>")
(defconst verilog-defun-re-1     "\\<\\(module\\|macromodule\\)\\|\\(primitive\\)\\>")
(defconst verilog-behavorial-re  "\\<initial\\|always\\>")
(defconst verilog-end-defun-re   "\\<\\(endmodule\\|endprimitive\\)\\>")
(defconst verilog-sub-block-re   "\\<\\(if\\|else\\|for\\|while\\)\\>")
(defconst verilog-noindent-re    "")
(defconst verilog-nosemi-re      "\\<\\(begin\\|repeat\\|then\\|do\\|else\\)\\>")
(defconst verilog-autoindent-lines-re
  "\\<\\(\\(macro\\)?module\\|primitive\\|end\\(case\\|function\\|task\\|module\\|\\)\\|join\\|begin\\|else\\)\\>")

;;; Strings used to mark beginning and end of excluded text
(defconst verilog-exclude-str-start "/* -----\\/----- EXCLUDED -----\\/-----")
(defconst verilog-exclude-str-end " -----/\\----- EXCLUDED -----/\\----- */")

(defconst verilog-emacs-features
  (let ((major (and (boundp 'emacs-major-version)
		    emacs-major-version))
	(minor (and (boundp 'emacs-minor-version)
		    emacs-minor-version))
	flavor comments)
    ;; figure out version numbers if not already discovered
    (and (or (not major) (not minor))
	 (string-match "\\([0-9]+\\).\\([0-9]+\\)" emacs-version)
	 (setq major (string-to-int (substring emacs-version
					       (match-beginning 1)
					       (match-end 1)))
	       minor (string-to-int (substring emacs-version
					       (match-beginning 2)
					       (match-end 2)))))
    (if (not (and major minor))
	(error "Cannot figure out the major and minor version numbers."))
    ;; calculate the major version
    (cond
     ((= major 18) (setq major 'v18))	;Emacs 18
     ((= major 4)  (setq major 'v18))	;Epoch 4
     ((= major 19) (setq major 'v19	;Emacs 19
			 flavor (if (or (string-match "Lucid" emacs-version)
					(string-match "XEmacs" emacs-version))
				    'XEmacs 'FSF)))
     ;; I don't know
     (t (error "Cannot recognize major version number: %s" major)))
    ;; All XEmacs 19's (formerly Lucid) use 8-bit modify-syntax-entry
    ;; flags, as do all patched (obsolete) Emacs 19, Emacs 18,
    ;; Epoch 4's.  Only vanilla Emacs 19 uses 1-bit flag.  Lets be
    ;; as smart as we can about figuring this out.
    (if (eq major 'v19)
	(let ((table (copy-syntax-table)))
	  (modify-syntax-entry ?a ". 12345678" table)
	  (if (and (vectorp table)
		   (= (logand (lsh (aref table ?a) -16) 255) 255))
	      (setq comments '8-bit)
	    (setq comments '1-bit)))
      (setq comments 'no-dual-comments))
    ;; lets do some minimal sanity checking.
    (if (or
	 ;; Lemacs before 19.6 had bugs
	 (and (eq major 'v19) (eq flavor 'XEmacs) (< minor 6))
	 ;; Emacs 19 before 19.21 has known bugs
	 (and (eq major 'v19) (eq flavor 'FSF) (< minor 21))
	 )
	(with-output-to-temp-buffer "*verilog-mode warnings*"
	  (print (format
"The version of Emacs that you are running, %s,
has known bugs in its syntax parsing routines which will affect the
performance of verilog-mode. You should strongly consider upgrading to the
latest available version.  verilog-mode may continue to work, after a
fashion, but strange indentation errors could be encountered."
		     emacs-version))))
    ;; Emacs 18, with no patch is not too good
    (if (and (eq major 'v18) (eq comments 'no-dual-comments))
	(with-output-to-temp-buffer "*verilog-mode warnings*"
	  (print (format
"The version of Emacs 18 you are running, %s,
has known deficiencies in its ability to handle the dual verilog 
(and C++) comments, (e.g. the // and /* */ comments). This will
not be much of a problem for you if you only use the /* */ comments,
but you really should strongly consider upgrading to one of the latest 
Emacs 19's.  In Emacs 18, you may also experience performance degradations. 
Emacs 19 has some new built-in routines which will speed things up for you.
Because of these inherent problems, verilog-mode is not supported 
on emacs-18."
			    emacs-version))))
    ;; Emacs 18 with the syntax patches are no longer supported
    (if (and (eq major 'v18) (not (eq comments 'no-dual-comments)))
	(with-output-to-temp-buffer "*verilog-mode warnings*"
	  (print (format
"You are running a syntax patched Emacs 18 variant.  While this should
work for you, you may want to consider upgrading to Emacs 19.
The syntax patches are no longer supported either for verilog-mode."))))
    (list major comments))
  "A list of features extant in the Emacs you are using.
There are many flavors of Emacs out there, each with different
features supporting those needed by verilog-mode.  Here's the current
supported list, along with the values for this variable:

 Vanilla Emacs 18/Epoch 4:   (v18 no-dual-comments)
 Emacs 18/Epoch 4 (patch2):  (v18 8-bit)
 XEmacs (formerly Lucid) 19: (v19 8-bit)
 Emacs 19:                   (v19 1-bit).")

(defconst verilog-comment-start-regexp "//\\|/\\*"
  "Dual comment value for `comment-start-regexp'.")

(defun verilog-populate-syntax-table (table)
  ;; Populate the syntax TABLE
  ;; DO NOT TRY TO SET _ (UNDERSCORE) TO WORD CLASS!
  (modify-syntax-entry ?\\ "\\" table)
  (modify-syntax-entry ?+ "." table)
  (modify-syntax-entry ?- "." table)
  (modify-syntax-entry ?= "." table)
  (modify-syntax-entry ?% "." table)
  (modify-syntax-entry ?< "." table)
  (modify-syntax-entry ?> "." table)
  (modify-syntax-entry ?( "." table)
  (modify-syntax-entry ?) "." table)
  (modify-syntax-entry ?[ "." table)
  (modify-syntax-entry ?] "." table)
  (modify-syntax-entry ?& "." table)
  (modify-syntax-entry ?| "." table)
  (modify-syntax-entry ?_ "w" table)
  (modify-syntax-entry ?\' "." table)
)

(defun verilog-setup-dual-comments (table)
  ;; Set up TABLE to handle block and line style comments
  (cond
   ((memq '8-bit verilog-emacs-features)
    ;; XEmacs (formerly Lucid) has the best implementation
    (modify-syntax-entry ?/  ". 1456" table)
    (modify-syntax-entry ?*  ". 23"   table)
    (modify-syntax-entry ?\n "> b"    table)
    ;; Give CR the same syntax as newline, for selective-display
    (modify-syntax-entry ?\^m "> b"    table))
   ((memq '1-bit verilog-emacs-features)
    ;; Emacs 19 does things differently, but we can work with it
    (modify-syntax-entry ?/  ". 124b" table)
    (modify-syntax-entry ?*  ". 23"   table)
    (modify-syntax-entry ?\n "> b"    table)
    ;; Give CR the same syntax as newline, for selective-display
    (modify-syntax-entry ?\^m "> b"   table))
   ))

(defvar verilog-mode-syntax-table nil
  "Syntax table used in verilog-mode buffers.")
(if verilog-mode-syntax-table
    ()
  (setq verilog-mode-syntax-table (make-syntax-table))
  (verilog-populate-syntax-table verilog-mode-syntax-table)
  ;; add extra comment syntax
  (verilog-setup-dual-comments verilog-mode-syntax-table)
  )

(defvar verilog-font-lock-keywords 
  '(
   ("^[ \t]*\\(function\\|task\\|module\\)\\>"  1 font-lock-keyword-face) 
   ("^[ \t]*\\(function\\|task\\|module\\)\\>[ \t]*\\(\\sw+\\)"  2 font-lock-function-name-face nil t)
   "\\$[^ \t([]*"
   ("\\\\[^ \t]*" .  font-lock-function-name-face)
   ("`[ \t]*[A-Za-z][A-Za-z0-9_]*" .  font-lock-type-face)
   ("\\<\\(in\\(teger\\|put\\|out\\)\\|output\\|event\\|tri[01]?\\|wire\\|re\\(al\\|g\\)\\)\\>" . font-lock-type-face)
   "\\<\\(begin\\|case\\(x\\|z\\|\\)\\|end\\(case\\|function\\|task\\|module\\)?\\|always\\|initial\\|\\(pos\\|neg\\)edge\\|else\\|for\\(ever\\|k\\)?\\|join\\|if\\|repeat\\|then\\|while\\)\\>"
   )
  "Additional expressions to highlight in Verilog mode.")

(setq verilog-font-lock-keywords 
  '(
   ("^[ \t]*\\(function\\|task\\|module\\)\\>[ \t]*"  1 font-lock-keyword-face) 
   ("^[ \t]*\\(function\\|task\\|module\\)\\>[ \t]*\\(\\sw+\\)"  2 font-lock-function-name-face nil t)
   "\\$[^ \t([]*"
   ("\\\\[^ \t]*" .  font-lock-function-name-face)
   ("`[ \t]*[A-Za-z][A-Za-z0-9_]*" .  font-lock-type-face)
   ("\\<\\(in\\(teger\\|put\\|out\\)\\|output\\|event\\|tri1\\|tri0\\|\\|wire\\|re\\(al\\|g\\)\\)\\>" . font-lock-type-face)
   "\\<\\(begin\\|case\\(x\\|z\\|\\)\\|end\\(case\\|function\\|task\\|module\\)?\\|always\\|initial\\|\\(pos\\|neg\\)edge\\|else\\|for\\(ever\\|k\\)?\\|join\\|if\\|repeat\\|then\\|while\\)\\>"
   ))


(defvar verilog-indent-level 3
  "*Indentation of Verilog statements with respect to containing block.")

(defvar verilog-case-indent 2
  "*Indentation for case statements.")

(defvar verilog-auto-newline t
  "*Non-nil means automatically newline after semicolons")

(defvar verilog-tab-always-indent t
  "*Non-nil means TAB in Verilog mode should always reindent the current line,
regardless of where in the line point is when the TAB command is used.")

(defvar verilog-auto-endcomments t
  "*Non-nil means a comment /* ... */ is set after the ends which ends cases and
functions. The name of the function or case will be set between the braces.")

(defvar verilog-auto-lineup '(all)
  "*List of contexts where auto lineup of :'s or ='s should be done.
Elements can be of type: 'declaration' or 'case', which will do auto
lineup in parameterlist, declarations or case-statements
respectively. The word 'all' will do all lineups. '(case declaration)
for instance will do lineup in case-statements and parameterlist,
while '(all) will do all lineups." )

;;;
;;;  Macros
;;;

(defsubst verilog-get-beg-of-line (&optional arg)
  (save-excursion
    (beginning-of-line arg)
    (point)))

(defsubst verilog-get-end-of-line (&optional arg)
  (save-excursion
    (end-of-line arg)
    (point)))

(defun verilog-declaration-end ()
  (search-forward ";"))


(defun verilog-declaration-beg ()
  (re-search-backward verilog-declaration-re (bobp) t))
  
(defsubst verilog-within-string ()
  (save-excursion
    (nth 3 (parse-partial-sexp (verilog-get-beg-of-line) (point)))))


;;;###autoload
(defun verilog-mode ()
  "Major mode for editing Verilog code. \\<verilog-mode-map>
TAB indents for Verilog code.  Delete converts tabs to spaces as it moves back.

Other useful functions are:

\\[verilog-mark-defun]\t- Mark function.
\\[verilog-insert-block]\t- insert begin ... end;
\\[verilog-label-be]\t- Label matching begin ... end, fork ... join and case ... endcase statements;
\\[verilog-star-comment]\t- insert /* ... */
\\[verilog-comment-area]\t- Put marked area in a comment, fixing nested comments.
\\[verilog-uncomment-area]\t- Uncomment an area commented with \
\\[verilog-comment-area].
\\[verilog-beg-of-defun]\t- Move to beginning of current function.
\\[verilog-end-of-defun]\t- Move to end of current function.
\\[verilog-goto-defun]\t- Goto function prompted for in the minibuffer.
\\[verilog-outline]\t- Enter verilog-outline-mode (see also verilog-outline).

Variables controlling indentation/edit style:

 verilog-indent-level      (default 3)
    Indentation of Verilog statements with respect to containing block.
 verilog-case-indent       (default 2)
    Indentation for case statements.
 verilog-auto-newline      (default nil)
    Non-nil means automatically newline after simcolons and the punctation mark
    after an end.
 verilog-tab-always-indent (default t)
    Non-nil means TAB in Verilog mode should always reindent the current line,
    regardless of where in the line point is when the TAB command is used.
 verilog-auto-endcomments  (default t)
    Non-nil means a comment /* ... */ is set after the ends which ends cases, tasks, functions and modules.
    The type and name of the object will be set between the braces.
 verilog-auto-lineup       (default t)
    List of contexts where auto lineup of :'s or ='s should be done.

Turning on Verilog mode calls the value of the variable verilog-mode-hook with
no args, if that value is non-nil."
  (interactive)
  (kill-all-local-variables)
  (use-local-map verilog-mode-map)
  (setq major-mode 'verilog-mode)
  (setq mode-name "Verilog")
  (setq local-abbrev-table verilog-mode-abbrev-table)
  (set-syntax-table verilog-mode-syntax-table)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'verilog-indent-line)
  (setq comment-indent-function 'verilog-indent-comment)
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments nil)
  (make-local-variable 'case-fold-search)
  (setq case-fold-search t)
  (make-local-variable 'comment-start)
  (setq comment-start "// "
	comment-end ""
	comment-multi-line nil)
  (setq comment-start "/\\*")
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "/\\*+ *\\|// *")
  (make-local-variable 'comment-end)
  (setq comment-end " \\*/")
  ;; Font lock support
  (make-local-variable 'font-lock-keywords)
  (setq font-lock-keywords verilog-font-lock-keywords)
  ;; Imenu support
  (make-local-variable 'imenu-generic-expression)
  (setq imenu-generic-expression verilog-imenu-generic-expression)
  (run-hooks 'verilog-mode-hook))



;;;
;;;  Electric functions
;;;
(defun electric-verilog-terminate-line ()
  "Terminate line and indent next line."
  (interactive)
  ;; First, check if current line should be indented
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward " \t")
    (if (looking-at verilog-autoindent-lines-re)
	(verilog-indent-line)))
  (delete-horizontal-space) ; Removes trailing whitespaces
  (newline)
  ;; Indent next line
  (verilog-indent-line)
  ;; Maybe we should set some endcomments
  (if verilog-auto-endcomments
      (verilog-set-auto-comments))
  ;; Check if we shall indent inside comment
;  (let ((setstar nil))
;    (save-excursion
;      (forward-line -1)
;      (skip-chars-forward " \t")
;      (cond ((looking-at "\\*[ \t]+)")
;	     ;; Delete region between `*' and `)' if there is only whitespaces.
;	     (forward-char 1)
;	     (delete-horizontal-space))
;	    ((and (looking-at "(\\*\\|\\*[^)]")
;		  (not (save-excursion
;			 (search-forward "*)" (verilog-get-end-of-line) t))))
;	     (setq setstar t))))
;    ;; If last line was a star comment line then this one shall be too.
;    (if (null setstar)	
;	(verilog-indent-line)
;      (insert "*  ")
;      ) )
)

(defun electric-verilog-semi ()
  "Insert `;' character and reindent the line."
  (interactive)
  (insert last-command-char)
  (save-excursion
    (beginning-of-line)
    (verilog-indent-line))
  (if verilog-auto-newline
      (electric-verilog-terminate-line)))

(defun electric-verilog-colon ()
  "Insert `:' and do all indentions except line indent on this line."
  (interactive)
  (insert last-command-char)
  ;; Do nothing if within string.
  (if (verilog-within-string)
      ()
    (save-excursion
      (beginning-of-line)
      (verilog-indent-line))
    (let ((verilog-tab-always-indent nil))
      (verilog-indent-command))))

(defun electric-verilog-equal ()
  "Insert `=', and do indention if within block."
  (interactive)
  (insert last-command-char)
  (if (eq (car (verilog-calculate-indent)) 'block)
      (let ((verilog-tab-always-indent nil))
	(verilog-indent-command))))

(defun electric-verilog-tick ()
  "Insert back-tick, and indent to coulmn 0 if this is a CPP directive."
  (interactive)
  (insert last-command-char)
  (if (save-excursion (beginning-of-line) (looking-at "^[ \t]*\`"))
      (save-excursion (beginning-of-line)
		      (delete-horizontal-space))))

(defun electric-verilog-tab ()
  "Function called when TAB is pressed in Verilog mode."
  (interactive)
  ;; If verilog-tab-always-indent, indent the beginning of the line.
  (if verilog-tab-always-indent
      (progn 
	(save-excursion
	  (beginning-of-line)
	  (skip-chars-forward " \t")
	  (verilog-indent-command))
	(if (looking-at "^[ \t]*$")
	    (end-of-line)))
    (progn (insert "\t")
	   (verilog-indent-command))
    ))




;;;
;;; Interactive functions
;;;
(defun verilog-insert-block ()
  "Insert Verilog begin ... end; block in the code with right indentation."
  (interactive)
  (verilog-indent-line)
  (insert "begin")
  (electric-verilog-terminate-line)
  (save-excursion
    (electric-verilog-terminate-line)
    (insert "end")
    (beginning-of-line)
    (verilog-indent-line)))

(defun verilog-star-comment ()
  "Insert Verilog star comment at point."
  (interactive)
  (verilog-indent-line)
  (insert "/*")
  (electric-verilog-terminate-line)
  (save-excursion
    (electric-verilog-terminate-line)
    (delete-horizontal-space)
    (insert "*/"))
  (insert "  "))

(defun verilog-mark-defun ()
  "Mark the current verilog function (or procedure).
This puts the mark at the end, and point at the beginning."
  (interactive)
  (push-mark (point))
  (verilog-end-of-defun)
  (push-mark (point))
  (verilog-beg-of-defun)
  (if (fboundp 'zmacs-activate-region)
      (zmacs-activate-region)))

(defun verilog-comment-area (start end)
  "Put the region into a Verilog comment.
The comments that are in this area are \"deformed\":
`*)' becomes `!(*' and `}' becomes `!{'.
These deformed comments are returned to normal if you use
\\[verilog-uncomment-area] to undo the commenting.

The commented area starts with `verilog-exclude-str-start', and ends with
`verilog-include-str-end'.  But if you change these variables,
\\[verilog-uncomment-area] won't recognize the comments."
  (interactive "r")
  (save-excursion
    ;; Insert start and endcomments
    (goto-char end)
    (if (and (save-excursion (skip-chars-forward " \t") (eolp))
	     (not (save-excursion (skip-chars-backward " \t") (bolp))))
	(forward-line 1)
      (beginning-of-line))
    (insert verilog-exclude-str-end)
    (setq end (point))
    (newline)
    (goto-char start)
    (beginning-of-line)
    (insert verilog-exclude-str-start)
    (newline)
    ;; Replace end-comments within commented area
    (goto-char end)
    (save-excursion
      (while (re-search-backward "\\*/" start t)
	(replace-match "!/*" t t)))
    )
)

(defun verilog-uncomment-area ()
  "Uncomment a commented area; change deformed comments back to normal.
This command does nothing if the pointer is not in a commented
area.  See also `verilog-comment-area'."
  (interactive)
  (save-excursion
    (let ((start (point))
	  (end (point)))
      ;; Find the boundaries of the comment
      (save-excursion
	(setq start (progn (search-backward verilog-exclude-str-start nil t)
			   (point)))
	(setq end (progn (search-forward verilog-exclude-str-end nil t)
			 (point))))
      ;; Check if we're really inside a comment
      (if (or (equal start (point)) (<= end (point)))
	  (message "Not standing within commented area.")
	(progn
	  ;; Remove endcomment
	  (goto-char end)
	  (beginning-of-line)
	  (let ((pos (point)))
	    (end-of-line)
	    (delete-region pos (1+ (point))))
	  ;; Change comments back to normal
	  (save-excursion
	    (while (re-search-backward "!/\\*" start t)
	      (replace-match "*/" t t)))
	  ;; Remove startcomment
	  (goto-char start)
	  (beginning-of-line)
	  (let ((pos (point)))
	    (end-of-line)
	    (delete-region pos (1+ (point)))))))))

(defun verilog-beg-of-defun ()
  "Move backward to the beginning of the current function or procedure."
  (interactive)
  (catch 'found
    (if (not (looking-at (concat "\\s \\|\\s)\\|" verilog-defun-re)))
	(forward-sexp 1))
    (let ((nest 0) (max -1) (func 0)
	  (reg (concat verilog-beg-block-re "\\|" 
		       verilog-end-block-re "\\|"
		       verilog-defun-re)))
      (while (re-search-backward reg nil 'move)
	(cond ((let ((state (save-excursion
			      (parse-partial-sexp (point-min) (point)))))
		 (or (nth 3 state) (nth 4 state))) ; Inside string or comment
	       ())
	      ((match-end 1)                       ; begin|case|fork
	       (setq nest (1+ nest)
		     max (max nest max)))
	      ((match-end 2)                       ; end|endcase|join
	       (if (and (= nest max) (>= max 0))
		   (setq func (1+ func)))
	       (setq nest (1- nest)))
	      ((match-end 3)                       ; module|primitive
	       (if (= 0 func)
		   (throw 'found t)
		 (setq func (1- func)))))))
    nil))

(defun verilog-end-of-defun ()
  "Move forward to the end of the current function or procedure."
  (interactive)
  (let (reg)
    (if (looking-at "\\s ")
	(forward-sexp 1))
    (if (not (looking-at verilog-defun-re-1))
	(progn
	  (verilog-beg-of-defun)
	  (looking-at verilog-defun-re-1))
      )
    (cond
     ((match-end 1)
      (setq reg "\\<endmodule\\>"))
     ((match-end 2)
      (setq reg "\\<endprimitive\\>"))
     )
    (catch 'found 
      (while (re-search-forward reg nil 'move)
	(cond ((let ((state (save-excursion
			      (parse-partial-sexp (point-min) (point)))))
		 (or (nth 3 state) (nth 4 state))) ; Inside string or comment
	       ())
	      ((match-end 0)
	       (throw 'found t))
	      (t
	       (throw 'found nil)))))
    (forward-line 1)))

(defun verilog-label-be (&optional arg)
"Label matching begin ... end, fork ... join and case ... endcase statements in this module;
With argument, first kill any existing labels."
  (interactive)
  (let ((nest 0)
	(mod-name "Unknown")
	(fmt " /* [#%s:%s] */")
	(oldpos (point))
	(b (progn 
	     (verilog-beg-of-defun) 
	     (point-marker)))
	(e (progn 
	     (verilog-end-of-defun) 
	     (point-marker)))
	(beg 0)
	(fork 0)
	(case 0)
	(func "Unknown")
	(reg (concat verilog-beg-block-re "\\|" 
		     verilog-end-block-re "\\|"
		     verilog-beg-tf-re "\\|"
		     verilog-end-tf-re )))
    (goto-char (marker-position b))
    (save-excursion
      (forward-sexp)
      (let ((b1 (progn (skip-chars-forward " \t")
		      (point)))
	    (e1 (progn (skip-chars-forward "\\\.a-zA-Z0-9_")
		     (point))))
	(setq mod-name (buffer-substring b1 e1))
	(setq func mod-name)))

    (save-excursion
      (while (re-search-forward " /\\* \\[#\[^]\]+] \\*/" (marker-position e) t)
	(replace-match "" nil nil)))
    (while (and
	    (> (marker-position e) (point))
	    (re-search-forward reg nil 'move))
      (cond ((let ((state (save-excursion
			    (parse-partial-sexp (point-min) (point)))))
	       (or (nth 3 state) (nth 4 state))) ; Inside string or comment
	     ())
	    ((match-end 1)		; begin|case|fork
	     (end-of-line)
	     (delete-horizontal-space)
	     (insert-string (format fmt func beg))
	     (setq beg (1+ beg)))
	    
	    ((match-end 2)		; end|join|endcase
	     (end-of-line)
	     (delete-horizontal-space)
	     (setq beg (1- beg))
	     (insert-string (format fmt func (if (< beg 0)
						 "ERROR" beg))))
	    
	    ((match-end 3)		; task|function
	     (save-excursion
	       (let (
		     (tsk (progn
			    (backward-sexp)
			    (if (looking-at "task") "task" "function")))
		     (bg (progn 
			   (forward-sexp)
			   (skip-chars-forward " \t")
			   (point)))
		     (en (progn
			   (skip-chars-forward "a-zA-Z0-9_")
			   (point)
			   )))
		 (setq func (concat tsk " " mod-name "." (buffer-substring bg en)))
		 )))
	    ((match-end 4)		; endtask|endfunction
	     (setq func mod-name))
	    )
      (forward-line 1)
      )
    (goto-char oldpos)
    )
  )


(defun verilog-end-of-statement ()
  "Move forward to end of current statement."
  (interactive)
  (let ((nest 0) pos
	(regexp (concat "\\(" verilog-beg-block-re "\\)\\|\\("
			verilog-end-block-re "\\)")))
    (if (not (looking-at "[ \t\n]")) (forward-sexp -1))
    (or (looking-at verilog-beg-block-re)
	;; Skip to end of statement
	(setq pos (catch 'found
		    (while t
		      (forward-sexp 1)
		      (cond ((looking-at "[ \t]*;")
			     (skip-chars-forward "^;")
			     (forward-char 1)
			     (throw 'found (point)))
			    ((save-excursion
			       (forward-sexp -1)
			       (looking-at verilog-beg-block-re))
			     (goto-char (match-beginning 0))
			     (throw 'found nil))
			    ((eobp)
			     (throw 'found (point))))))))
    (if (not pos)
	;; Skip a whole block
	(catch 'found
	  (while t
	    (re-search-forward regexp nil 'move)
	    (setq nest (if (match-end 1) 
			   (1+ nest)
			 (1- nest)))
	    (cond ((eobp)
		   (throw 'found (point)))
		  ((= 0 nest)
		   (throw 'found (verilog-end-of-statement))))))
      pos)))



;;;
;;; Other functions
;;;
(defun verilog-set-auto-comments ()
  "Insert `/* case */' or `/* NAME */' on this line if appropriate.
Insert `/* case expr */' if this line ends a case block.  
Insert `/* ifdef FOO */' if this line ends code conditional on FOO.
Insert `/* NAME */' if this line ends a module or primitive named NAME."
  (save-excursion
    (forward-line -1)
    (skip-chars-forward " \t")
    (cond 
     (; Comment close preprocessor directives
      (and 
       (looking-at "\\(`endif\\)\\|\\(`else\\)")
       (not (save-excursion
	      (end-of-line)
	      (search-backward "/*" (verilog-get-beg-of-line) t))))
      (let ( (reg "\\(`else\\)\\|\\(`ifdef\\)\\|\\(`endif\\)")
	     (nest 1)
	     b e str
	     (else (if (match-end 2)
		       1
		     0))
	     )
	(end-of-line)
	(delete-horizontal-space)
	(save-excursion
	  (backward-sexp 1)
	  (while (and (/= nest 0)
		      (re-search-backward reg nil 'move))
	    (cond ((let ((state (save-excursion
				  (parse-partial-sexp (point-min) (point)))))
		     (or (nth 3 state) (nth 4 state))) ; Inside string or comment
		   ())
		  ((match-end 1) ; `else
		   (if (= nest 1)
		       (setq else 1)))
		  ((match-end 2) ; `ifdef
		   (setq nest (1- nest)))
		  ((match-end 3) ; `endif
		   (setq nest (1+ nest)))
		  ))
	  (setq b (progn 
		    (skip-chars-forward "^ \t")
		    (skip-chars-forward " \t")
		    (point))
		e (progn
		    (skip-chars-forward "a-zA-Z0-9_")
		    (point)
		    )))
	(insert (concat (if 
			    (= else 0)
			    " /* ifdef " 
			  " /* !ifdef ")
			(buffer-substring b e)
			" */"))))

     (; Comment close case/function/task/module and named block
      (and (looking-at "\\<end")
	   (not (save-excursion
		  (end-of-line)
		  (search-backward "/*" (verilog-get-beg-of-line) t))))
      (let (
	    (type (car (verilog-calculate-indent)))
	    b reg
	    )
	(if (eq type 'declaration)
	    ()
	  (if (and (or
		    (eq type 'block)
		    (eq type 'tf)
		    (eq type 'case)
		    (eq type 'defun))
		   (looking-at "\\<\\(endcase\\)\\|\\(end\\)\\|\\(endfunction\\)\\|\\(endtask\\)\\|\\(endmodule\\)\\>"))
	      (cond
	       ((match-end 1)
		;; This is a case block
		;; search back for the start of this case
		
		(let ((nest 1) 
		      (str "UNMATCHED CASE")
		      (reg (concat verilog-case-re "\\|" 
				   "\\(endcase\\)\\|"
				   verilog-defun-re
				   )))
		  (end-of-line)
		  (delete-horizontal-space)
		  (insert " /*  */")
		  (backward-char 3)
		  (save-excursion
		    (backward-sexp 1)
		    (while (and (/= nest 0)
				(re-search-backward reg nil 'move))
		      (cond ((let ((state (save-excursion
					    (parse-partial-sexp (point-min) (point)))))
			       (or (nth 3 state) (nth 4 state))) ; Inside string or comment
			     ())
			    ((match-end 1) ; case|casex|casez
			     (setq nest (1- nest)))
			    ((match-end 2) ; endcase
			     (setq nest (1+ nest)))
			    ((match-end 3)
			     (error))))
		    (setq b (progn 
			      (skip-chars-forward "^ \t")
			      (skip-chars-forward " \t")
			      (point))
			  e (let ((par 1)) 
			      (if (looking-at "(")
				  (progn
				    (forward-char 1)
				    (while (and (/= par 0) 
						(re-search-forward "\\((\\)\\|\\()\\)" nil 'move))
				      (cond
				       ((match-end 1)
					(setq par (1+ par)))
				       ((match-end 2)
					(setq par (1- par)))))
				    (point))
				(skip-chars-forward "a-zA-Z0-9_"))))
		    (setq str (concat "case " (buffer-substring b e))))
		    (insert str)))
	       ((match-end 2)
		;; This is a begin..end block
		;; search back for the matching begin
		
		(let ((nest 1) 
		      (str " /* UNMATCHED END */")
		      (reg "\\<\\(begin\\)\\|\\(end\\)\\>")
		      (named-block 0)
		      (here (point))
		      )
		  (save-excursion
		    (while (and (/= nest 0)
				(re-search-backward reg nil 'move))
		      (cond ((let ((state (save-excursion
					    (parse-partial-sexp (point-min) (point)))))
			       (or (nth 3 state) (nth 4 state))) ; Inside string or comment
			     ())
			    ((match-end 1) ; begin
			     (setq nest (1- nest)))
			    ((match-end 2) ; end
			     (setq nest (1+ nest)))
			    ((match-end 3) ; module!!
			     (error))))
		    (if (looking-at "begin[ \t]*:")
			(progn
			  (setq b (progn 
				    (forward-sexp)
				    (skip-chars-forward " \t:")
				    (point))
				e (progn
				    (skip-chars-forward "a-zA-Z0-9_")
				    (point)))
			  (setq str (concat " /* block: " (buffer-substring b e) " */"))
			  (goto-char here)
			  (end-of-line)
			  (delete-horizontal-space)
			  (insert str))))))

	       
	       (t 
		(let (state b e com)
		  (end-of-line)
		  (delete-horizontal-space)
		  (cond 
		   ((match-end 3) (setq reg "\\<function\\>"))
		   ((match-end 4) (setq reg "\\<task\\>"))
		   ((match-end 5) (setq reg "\\<module\\>")))
		  (save-excursion
		    (setq b (progn 
			      (while (and
				      (re-search-backward reg nil 'move)
				      (progn 
					(setq state (save-excursion
						      (parse-partial-sexp (point-min) (point))))
					(or (nth 3 state) (nth 4 state))) ; Inside string or comment
				      ))
			      (skip-chars-forward "^ \t")
			      (skip-chars-forward " \t")
			      (point))
			  e (progn 
			      (skip-chars-forward "a-zA-Z0-9_")
			      (point))))
		  (insert (concat " /* " (buffer-substring b e) " */")))
		)
	       )
	    )
	  )
	)
      )
     )
    )
  )



;;;
;;; Indentation
;;;
(setq verilog-indent-alist
  '((block       . (+ ind verilog-indent-level))
    (case        . (+ ind verilog-case-indent))
    (defun       . verilog-indent-level)
    (declaration . verilog-indent-level)
    (tf          . verilog-indent-level)
    (behavorial  . verilog-indent-level)
    (caseblock   . ind) 
    (endblock    . (- ind verilog-indent-level))
    (cpp         . 0)
    (comment     . (verilog-indent-comment t))
    (contexp     . ind)
    (unknown     . 3) 
    (string      . 0)))

(defun verilog-calculate-indent ()
"Calculate the indent of the current Verilog line, through examination
of previous lines.  Once a line is found that is definitive as to the
type of the current line, return that lines' indent level and it's
type. Return a list of two elements: (INDENT-TYPE INDENT-LEVEL)."
  (save-excursion
    (let* ((oldpos (point))
	   (state (save-excursion (parse-partial-sexp (point-min) (point))))
	   (nest 0) 
	   (par 0) 
	   (complete (looking-at "[ \t]*end\\>"))
	   (elsed (looking-at "[ \t]*else\\>"))

	   (type (catch 'nesting
		   ;; Check if inside a string, comment or parenthesis
		   (cond ((nth 3 state) (throw 'nesting 'string))
			 ((nth 4 state) (throw 'nesting 'comment))
			 ((> (car state) 0)
			  (goto-char (scan-lists (point) -1 (car state)))
			  (setq par (1+ (current-column))))
			 )
		   ;; Keep working backwards until we can figure out
		   ;; what type of statement this is.
		   (while t
		     (while
			 (progn
			   (backward-sexp 1)
			   (setq state (parse-partial-sexp (point-min) (point)))
			   (cond ((nth 3 state) 
				  (goto-char (scan-lists (point) -1 1))
				  nil)
				 ((nth 4 state) 't) ;; Get out of the comment
				 ((> (car state) 0)
				  (goto-char (scan-lists (point) -1 (car state)))
				  (setq par (1+ (current-column)))
				  nil)
				 )
			   ))
		     (cond 
		      (;--behaviorial block
		       (looking-at verilog-behavorial-re)
		       ;; Need to figure out if it is closed or open
		       (throw 'nesting 'defun))
		      
		      (;-- tf block
		       (looking-at verilog-beg-tf-re)
		       (throw 'nesting 'tf))

		      (;--Declaration part
		       (looking-at verilog-declaration-re)
		       (if (save-excursion
			     (goto-char oldpos)
			     (looking-at verilog-declaration-re))
			   (throw 'nesting 'declaration)
			 ))
		      
		      (;--Nest block outwards
		       (looking-at verilog-beg-block-re-1)
		       (cond
			((match-end 2)
			 ;; case
			 (throw 'nesting 'case)			 
			 )
			(t
			 (throw 'nesting 'block)
			 )))

		      (;--Nest block inwards
		       ; try to leap back to matching outward block by striding across
		       ; indent level changing tokens then immediately
		       ; previous line governs indentation.
		       (looking-at verilog-end-block-re-1) ;; end|join|endcase
		       (catch 'skip
			 (let ((reg)
			       (nest 1))
			   (cond 
			    ((match-end 1)                       ; end
			     ;; Search back for matching begin
			     (setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" )
			     )
			    ((match-end 2)                       ; endcase
			     ;; Search back for matching case
			     (setq reg "\\(\\<case[xz]?\\>\\)\\|\\(\\<endcase\\>\\)" )
			     )
			    ((match-end 3)                       ; join
			     ;; Search back for matching fork
			     (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" )
			     )
			    )
			   (while (re-search-backward reg nil 'move)
			     (cond ((let ((state (save-excursion
						   (parse-partial-sexp (point-min) (point)))))
				      (or (nth 3 state) (nth 4 state))) ; Inside string or comment
				    ())
				   ((match-end 1)                       ; begin
				    (setq nest (1- nest))
				    (if (= 0 nest)
					(progn
					  (setq complete 1)
					  ;; got it
					  (throw 'skip 1))
				      ))
				   ((match-end 2)                       ; end
				    (setq nest (1+ nest)))))
			   )
			 )
		       )
		       
		      (;-- tf block
		       (looking-at verilog-end-tf-re-1)
		       (let ((reg))
			 (cond 
			  ((match-end 1)                       ; end
			   ;; Search back for matching task - note no nesting
			   (setq reg "\\<task\\>" )
			   )
			  ((match-end 2)                       ; join
			   ;; Search back for matching function - note no nesting
			   (setq reg "\\<function\\>" )
			   )
			  )
			 (catch 'out
			   (while (re-search-backward reg nil 'move)
			     (cond ((let ((state (save-excursion
						   (parse-partial-sexp (point-min) (point)))))
				      (or (nth 3 state) (nth 4 state))) ; Inside string or comment
				    ())
				   ((match-end 0)
				    (throw 'out 1))
				   (t
				    (error "Unbalanced end(task)|(function)")
				    (throw 'nesting 'unknown)))))))

		      (;--Defun (or parameter list)
		       (looking-at verilog-defun-re)
		       (if (= 0 par)
			   (throw 'nesting 'defun)
			 (setq par 0)
			 (throw 'nesting 'declaration)))
		      
		      (;--If, else or while statement
		       (and (not complete)
			    (looking-at verilog-sub-block-re))
		       (throw 'nesting 'block))
		      
		      (;--Escape from case statements
		       (and (looking-at "[A-Za-z0-9]+[ \t]*:[^=]")
			    (not complete)
			    (save-excursion (skip-chars-backward " \t")
					    (bolp))
			    (= (save-excursion
				 (end-of-line) (backward-sexp) (point))
			       (point))
			    (> (save-excursion (goto-char oldpos)
					       (beginning-of-line)
					       (point))
			       (point)))
		       (throw 'nesting 'case))
		      
		      (;--Found complete statement
		       (save-excursion (forward-sexp 1)
				       (= (following-char) ?\;))
		       (setq complete 1))
		      
		      (;--end Defun
		       (looking-at verilog-end-defun-re)
		       (throw 'nesting 'cpp))
		      
		      (;--No known statements
		       (bobp)
		       (throw 'nesting 'cpp))
		      )
		     )
		   )
		 )
	   )

      ;; Return type of block and indent level.
      (if (> par 0)                               ; Unclosed Parenthesis 
	  (list 'contexp par)
	(list type (verilog-indent-level))))))

(defun verilog-indent-command ()
  "Indent for special part of code."
  (if (looking-at "\\(`else\\)\\|\\(`ifdef\\)\\|\\(`endif\\)")
      ;; We could nicely nest `ifdef's, but...
      (progn
	(delete-horizontal-space)
	(indent-to 0))
    (let* ((indent-str (verilog-calculate-indent))
	   (type (car indent-str))
	   (ind (car (cdr indent-str))))
      (cond ((and (eq type 'declaration)
		  (or (memq 'all verilog-auto-lineup)
		      (memq 'declaration  verilog-auto-lineup)))
	     (verilog-indent-declaration type)
	     )
	    ((and (eq type 'case) (not (looking-at "^[ \t]*$"))
		  (or (memq 'all verilog-auto-lineup)
		      (memq 'case verilog-auto-lineup)))
	     (verilog-indent-case)
	     (if (looking-at "endcase\\>")
		 (verilog-do-indent-line indent-str)))
	    (t
	     (verilog-do-indent-line indent-str))
	    )
      (if (looking-at "[ \t]+$")
	  (skip-chars-forward " \t")))))

(defun verilog-do-indent-line (indent-str)
  "Indent current line as a Verilog statement."
  (let* ((type (car indent-str))
	 (ind (car (cdr indent-str))))
    (if (looking-at "^[0-9a-zA-Z]+[ \t]*:[^=]")
	(search-forward ":" nil t))
    (delete-horizontal-space)
    (cond 
     ((or (and (eq type 'block) 
	       (looking-at verilog-end-block-re-1))
	  (and (eq type 'case) 
	       (looking-at "\\<endcase\\>"))
	  (and (eq type 'behavorial)
	       (or (looking-at verilog-behavorial-re)
		   (looking-at verilog-beg-tf-re))))
      (indent-to ind))
     ((and (eq type 'defun)
	   (looking-at (concat verilog-defun-re "\\|" verilog-end-defun-re)))
      (indent-to 0))      
     (t
      (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
	;;	(verilog-comment-depth type val)
	(indent-to val)
	))
     )
    )
  )

(defun verilog-indent-line ()
  "Indent current line as a Verilog statement."
  (let* ((indent-str (verilog-calculate-indent)))
    (verilog-do-indent-line indent-str)))
	 

(defun verilog-indent-level ()
  "Return the indent-level the current statement has.
Do not count labels, case-statements or records."
  (save-excursion
    (beginning-of-line)
    (if (and (not (looking-at "[ \t]*begin[ \t]*:"))
	     (looking-at "[ \t]*[0-9a-zA-Z]+[ \t]*:"))
	(search-forward ":" nil t)
      )
    (skip-chars-forward " \t")
    (current-column)))

(defun verilog-indent-comment (&optional arg)
  "Indent current line as comment.
If optional arg is non-nil, just return the
column number the line should be indented to."
    (let* ((stcol (save-excursion
		    (re-search-backward "(\\*\\|{" nil t)
		    (1+ (current-column)))))
      (if arg stcol
	(delete-horizontal-space)
	(indent-to stcol))))

(defun verilog-indent-case ()
  "Indent within case statements."
  (let ((start (point))
	oldpos
	(foo   (skip-chars-forward ": \t"))
	(end (prog2
		 (end-of-line)
		 (point-marker)
	       (re-search-backward verilog-case-re nil t)))
	(beg (point)) 
	(ind 0))
    ;; Get right indent
    (while (< (point) (marker-position end))
      (if (re-search-forward 
	   "^[ \t]*[^ \t,:]+[ \t]*\\(,[ \t]*[^ \t,:]+[ \t]*\\)*:"
	   (marker-position end) 'move)
	  (forward-char -1))
      (delete-horizontal-space)
      (if (> (current-column) ind)
	  (setq ind (current-column)))
      (verilog-end-of-statement))
    (goto-char beg)
    (setq oldpos (marker-position end))
    ;; Indent all case statements
    (while (< (point) (marker-position end))
      (if (re-search-forward
	   "^[ \t]*[^][ \t,\\.:]+[ \t]*\\(,[ \t]*[^ \t,:]+[ \t]*\\)*:"
	   (marker-position end) 'move)
	  (forward-char -1))
      (indent-to (1+ ind))
      (if (/= (following-char) ?:)
	  ()
	(forward-char 1)
	(delete-horizontal-space)
	(insert " "))
      (setq oldpos (point))
      (verilog-end-of-statement))
    (goto-char oldpos)
;;  (goto-char start)
    )
  )


(defun verilog-indent-declaration (type &optional arg start end)
  "Indent current lines as declaration, lining up the variable names"
  (let ((pos (point-marker))
	state
	(lim (save-excursion (progn (end-of-line) (point-marker))))
	)
    (if (and (not (or arg start)) (not (re-search-forward verilog-declaration-re lim t)))
	()
      (progn
	(beginning-of-line)
	(delete-horizontal-space)
	(indent-to (eval (cdr (assoc type verilog-indent-alist))))
	(let ((pos (point-marker))
	      (reg (concat verilog-declaration-re "[ \t]*\\(\\[[^]]*\\][ \t]*\\)?"))
	      (state)
	      (stpos (if start start
		       (save-excursion
			 (goto-char pos)
			 (catch 'first
			   (while t
			     (backward-sexp)
			     (setq state (save-excursion (parse-partial-sexp (point-min) (point))))
			     (cond ((or (nth 4 state) ; in a comment
					(progn (beginning-of-line )
					       (skip-chars-forward " \t")
					       (looking-at verilog-declaration-re))) ;; looking at decl
				    ())
				   (t 
				    (throw 'first (point-marker)))))))))
	      (edpos (if end 
			 (set-marker (make-marker) end)
		       lim))
	      ind)
	  (goto-char stpos)
	  ;; Indent lines in declaration block
	  (if arg
	      (while (<= (point) (marker-position edpos))
		(beginning-of-line)
		(delete-horizontal-space)
		(if (not (looking-at verilog-declaration-re))
		    (indent-to arg)
		  (indent-to (+ arg verilog-indent-level)))
		(forward-line 1)))
	  
	  ;; Do lineup
	  (setq ind (verilog-get-lineup-indent stpos edpos))
	  (goto-char stpos)
	  (while (<= (point) (marker-position edpos))
	    (if (re-search-forward reg (verilog-get-end-of-line) 'move)
		(forward-char -1))
	    (delete-horizontal-space)
	    (indent-to ind)
	    (forward-line 1))))
      
      ;; If arg - move point
      (if arg (forward-line -1)
	(goto-char (marker-position pos))))))

;  "Return the indent level that will line up several lines within the region
;from b to e nicely. The lineup string is str."
(defun verilog-get-lineup-indent (b e)
  (save-excursion
    (let ((ind 0)
	  (reg (concat verilog-declaration-re "[ \t]*\\(\\[[^]]*\\][ \t]*\\)?"))
	  nest)
      (goto-char b)
      ;; Get rightmost position
      (while (< (point) e)
	(if (re-search-forward reg (min e (verilog-get-end-of-line 2)) 'move)
	    (progn
	      (goto-char (match-end 0))
		  (skip-chars-backward " \t")
		  (if (> (current-column) ind)
		      (setq ind (current-column)))
		  (goto-char (match-end 0)))))
      (if (> ind 0)
	  (1+ ind)
	;; No lineup-string found
	(goto-char b)
	(end-of-line)
	(skip-chars-backward " \t")
	(1+ (current-column))))))

;;    A useful mode debugging aide
(defun verilog-comment-depth (type val)
  ""
  (save-excursion 
    (let 
	((b (prog2
		(beginning-of-line)
		(point-marker)
	      (end-of-line)))
	 (e (point-marker)))	      
      (if (re-search-backward " /\\* \[#-\]# \[a-z\]+ \[0-9\]+ ## \\*/" b t) 
	  (progn 
	    (replace-match " /* -#  ## */") 
	    (end-of-line))
	(progn 
	  (end-of-line)
	  (insert " /* ##  ## */"))))
    (backward-char 6) 
    (insert 
     (format "%s %d" type val))
    )
  )
;;; 
;;;
;;; Completion
;;;
(defvar verilog-str nil)
(defvar verilog-all nil)
(defvar verilog-pred nil)
(defvar verilog-buffer-to-use nil)
(defvar verilog-flag nil)
(defvar verilog-toggle-completions nil
  "*Non-nil means \\<verilog-mode-map>\\[verilog-complete-word] should try all possible completions one by one.
Repeated use of \\[verilog-complete-word] will show you all of them.
Normally, when there is more than one possible completion,
it displays a list of all possible completions.")

(defvar verilog-type-keywords
  '("buf" "bufif0" "bufif1" "cmos" "inout" "input"
    "integer" "nand" "nmos" "nor" "not" "notif0" "notif1" "or" "output"
    "pmos" "pull0" "pull1" "pullup" "rcmos" "real" "realtime" "reg" "rnmos" "rpmos" "rtran"
    "rtranif0" "rtranif1" "time" "tran" "tranif0" "tranif1" "tri" "tri0" "tri1"
    "triand" "trior" "trireg" "wand" "wire" "wor" "xnor" "xor" )
  "*Keywords for types used when completing a word in a declaration or parmlist.
\(eg. integer, real, char.)  The types defined within the Verilog program
will be completed runtime, and should not be added to this list.")

(defvar verilog-defun-keywords
  '("begin" "function" "task" "initial" "always" "assign" "posedge" "negedge" "endmodule")
  "*Keywords to complete when standing at first word of a line in declarative scope.
\(eg. initial, always, begin, assign.)
The procedures and variables defined within the Verilog program
will be completed runtime and should not be added to this list.")

(defvar verilog-block-keywords
  '("begin" "fork" "join" "case" "end" "if" "else" "for" "repeat")
  "*Keywords to complete when standing at first word of a line in behavorial scope.
\(eg. begin, if, then, else, for, fork.)
The procedures and variables defined within the Verilog program
will be completed runtime and should not be added to this list.")

(defvar verilog-tf-keywords
  '("begin" "fork" "join" "case" "end" "endtask" "endfunction" "if" "else" "for" "repeat")
  "*Keywords to complete when standing at first word of a line in behavorial scope.
\(eg. begin, if, then, else, for, fork.)
The procedures and variables defined within the Verilog program
will be completed runtime and should not be added to this list.")

(defvar verilog-case-keywords
  '("begin" "fork" "join" "case" "end" "endcase" "if" "else" "for" "repeat")
  "*Keywords to complete when standing at first word of a line in behavorial scope.
\(eg. begin, if, then, else, for, fork.)
The procedures and variables defined within the Verilog program
will be completed runtime and should not be added to this list.")

(defvar verilog-separator-keywords
  '("else" "then")
  "*Keywords to complete when NOT standing at the first word of a statement.
\(eg. else, then.) 
Variables and function names defined within the
Verilog program are completed runtime and should not be added to this list.")

(defun verilog-string-diff (str1 str2)
  "Return index of first letter where STR1 and STR2 differs."
  (catch 'done
    (let ((diff 0))
      (while t
	(if (or (> (1+ diff) (length str1))
		(> (1+ diff) (length str2)))
	    (throw 'done diff))
	(or (equal (aref str1 diff) (aref str2 diff))
	    (throw 'done diff))
	(setq diff (1+ diff))))))

;; Calculate all possible completions for functions if argument is `function',
;; completions for procedures if argument is `procedure' or both functions and
;; procedures otherwise.

(defun verilog-func-completion (type)
  ;; Build regular expression for function/procedure names
  (if (string= verilog-str "")
      (setq verilog-str "[a-zA-Z_]"))
  (let ((verilog-str (concat (cond
			     ((eq type 'module) "\\<\\(module\\)\\s +")
			     ((eq type 'tf) "\\<\\(task\\|function\\)\\s +")
			     (t "\\<\\(task\\|function\\|module\\)\\s +"))
			    "\\<\\(" verilog-str "[a-zA-Z0-9_.]*\\)\\>"))
	match)
    
    (if (not (looking-at verilog-defun-re))
	(re-search-backward verilog-defun-re nil t))
    (forward-char 1)

    ;; Search through all reachable functions
    (goto-char (point-min))
    (while (re-search-forward verilog-str (point-max) t)
      (progn (setq match (buffer-substring (match-beginning 2)
					   (match-end 2)))
	     (if (or (null verilog-pred)
		     (funcall verilog-pred match))
		 (setq verilog-all (cons match verilog-all)))))
    (goto-char (match-beginning 0))))

(defun verilog-get-completion-decl ()
  ;; Macro for searching through current declaration (var, type or const)
  ;; for matches of `str' and adding the occurence tp `all'
  (let ((end (save-excursion (verilog-declaration-end)
			     (point)))
	match)
    ;; Traverse lines
    (while (< (point) end)
      (if (re-search-forward "[:=]" (verilog-get-end-of-line) t)
	  ;; Traverse current line
	  (while (and (re-search-backward 
		       (concat "\\((\\|\\<\\(var\\|type\\|const\\)\\>\\)\\|" 
			       verilog-symbol-re)
		       (verilog-get-beg-of-line) t)
		      (not (match-end 1)))
	    (setq match (buffer-substring (match-beginning 0) (match-end 0)))
	    (if (string-match (concat "\\<" verilog-str) match)
		(if (or (null verilog-pred)
			(funcall verilog-pred match))
		    (setq verilog-all (cons match verilog-all))))))
      (if (re-search-forward "\\<record\\>" (verilog-get-end-of-line) t)
	  (verilog-declaration-end)
	(forward-line 1)))))

(defun verilog-type-completion ()
  "Calculate all possible completions for types."
  (let ((start (point))
	goon)
    ;; Search for all reachable type declarations
    (while (or (verilog-beg-of-defun)
	       (setq goon (not goon)))
      (save-excursion
	(if (and (< start (prog1 (save-excursion (verilog-end-of-defun)
						 (point))
			    (forward-char 1)))
		 (re-search-forward
		  "\\<type\\>\\|\\<\\(begin\\|function\\|procedure\\)\\>"
		  start t)
		 (not (match-end 1)))
	    ;; Check current type declaration
	    (verilog-get-completion-decl))))))

(defun verilog-var-completion ()
  "Calculate all possible completions for variables (or constants)."
  (let ((start (point))
	goon twice)
    ;; Search for all reachable var declarations
    (while (or (verilog-beg-of-defun)
	       (setq goon (not goon)))
      (save-excursion
	(if (> start (prog1 (save-excursion (verilog-end-of-defun)
					    (point))))
	    () ; Declarations not reacable
	  (if (search-forward "(" (verilog-get-end-of-line) t)
	      ;; Check parameterlist
		(verilog-get-completion-decl))
	  (setq twice 2)
	  (while (>= (setq twice (1- twice)) 0)
	    (cond ((and (re-search-forward
			 (concat "\\<\\(var\\|const\\)\\>\\|"
				 "\\<\\(begin\\|function\\|procedure\\)\\>")
			 start t)
			(not (match-end 2)))
		   ;; Check var/const declarations
		   (verilog-get-completion-decl))
		  ((match-end 2)
		   (setq twice 0)))))))))


(defun verilog-keyword-completion (keyword-list)
  "Give list of all possible completions of keywords in KEYWORD-LIST."
  (mapcar '(lambda (s) 
	     (if (string-match (concat "\\<" verilog-str) s)
		 (if (or (null verilog-pred)
			 (funcall verilog-pred s))
		     (setq verilog-all (cons s verilog-all)))))
	  keyword-list))

;; Function passed to completing-read, try-completion or
;; all-completions to get completion on STR. If predicate is non-nil,
;; it must be a function to be called for every match to check if this
;; should really be a match. If flag is t, the function returns a list
;; of all possible completions. If it is nil it returns a string, the
;; longest possible completion, or t if STR is an exact match. If flag
;; is 'lambda, the function returns t if STR is an exact match, nil
;; otherwise.

(defun verilog-completion (verilog-str verilog-pred verilog-flag)
  (save-excursion
    (let ((verilog-all nil))
      ;; Set buffer to use for searching labels. This should be set
      ;; within functins which use verilog-completions
      (set-buffer verilog-buffer-to-use)

      ;; Determine what should be completed
      (let ((state (car (verilog-calculate-indent))))
	(cond ((eq state 'defun)
	       (save-excursion (verilog-var-completion))
	       (verilog-func-completion 'module)
	       (verilog-keyword-completion verilog-defun-keywords))

	      ((eq state 'block)
	       (save-excursion (verilog-var-completion))
	       (verilog-func-completion 'tf)
	       (verilog-keyword-completion verilog-block-keywords))

	      ((eq state 'case)
	       (save-excursion (verilog-var-completion))
	       (verilog-func-completion 'tf)
	       (verilog-keyword-completion verilog-case-keywords))

	      ((eq state 'tf)
	       (save-excursion (verilog-var-completion))
	       (verilog-func-completion 'tf)
	       (verilog-keyword-completion verilog-tf-keywords))
      
	      (t;--Anywhere else
	       (save-excursion (verilog-var-completion))
	       (verilog-func-completion 'both)
	       (verilog-keyword-completion verilog-separator-keywords))))
      
      ;; Now we have built a list of all matches. Give response to caller
      (verilog-completion-response))))

(defun verilog-completion-response ()
  (cond ((or (equal verilog-flag 'lambda) (null verilog-flag))
	 ;; This was not called by all-completions
	 (if (null verilog-all)
	     ;; Return nil if there was no matching label
	     nil
	   ;; Get longest string common in the labels
	   (let* ((elm (cdr verilog-all))
		  (match (car verilog-all))
		  (min (length match))
		  exact tmp)
	     (if (string= match verilog-str)
		 ;; Return t if first match was an exact match
		 (setq match t)
	       (while (not (null elm))
		 ;; Find longest common string
		 (if (< (setq tmp (verilog-string-diff match (car elm))) min)
		     (progn
		       (setq min tmp)
		       (setq match (substring match 0 min))))
		 ;; Terminate with match=t if this is an exact match
		 (if (string= (car elm) verilog-str)
		     (progn
		       (setq match t)
		       (setq elm nil))
		   (setq elm (cdr elm)))))
	     ;; If this is a test just for exact match, return nil ot t
	     (if (and (equal verilog-flag 'lambda) (not (equal match 't)))
		 nil
	       match))))
	;; If flag is t, this was called by all-completions. Return
	;; list of all possible completions
	(verilog-flag
	 verilog-all)))

(defvar verilog-last-word-numb 0)
(defvar verilog-last-word-shown nil)
(defvar verilog-last-completions nil)

(defun verilog-complete-word ()
  "Complete word at current point.
\(See also `verilog-toggle-completions', `verilog-type-keywords',
`verilog-start-keywords' and `verilog-separator-keywords'.)"
  (interactive)
  (let* ((b (save-excursion (skip-chars-backward "a-zA-Z0-9_") (point)))
	 (e (save-excursion (skip-chars-forward "a-zA-Z0-9_") (point)))
	 (verilog-str (buffer-substring b e))
	 ;; The following variable is used in verilog-completion
	 (verilog-buffer-to-use (current-buffer))
	 (allcomp (if (and verilog-toggle-completions
			   (string= verilog-last-word-shown verilog-str))
		      verilog-last-completions
		    (all-completions verilog-str 'verilog-completion)))
	 (match (if verilog-toggle-completions
		    "" (try-completion
			verilog-str (mapcar '(lambda (elm)
					      (cons elm 0)) allcomp)))))
    ;; Delete old string
    (delete-region b e)

    ;; Toggle-completions inserts whole labels
    (if verilog-toggle-completions
	(progn
	  ;; Update entry number in list
	  (setq verilog-last-completions allcomp
		verilog-last-word-numb 
		(if (>= verilog-last-word-numb (1- (length allcomp)))
		    0
		  (1+ verilog-last-word-numb)))
	  (setq verilog-last-word-shown (elt allcomp verilog-last-word-numb))
	  ;; Display next match or same string if no match was found
	  (if (not (null allcomp))
	      (insert "" verilog-last-word-shown)
	    (insert "" verilog-str)
	    (message "(No match)")))
      ;; The other form of completion does not necessarly do that.

      ;; Insert match if found, or the original string if no match
      (if (or (null match) (equal match 't))
	  (progn (insert "" verilog-str)
		 (message "(No match)"))
	(insert "" match))
      ;; Give message about current status of completion
      (cond ((equal match 't)
	     (if (not (null (cdr allcomp)))
		 (message "(Complete but not unique)")
	       (message "(Sole completion)")))
	    ;; Display buffer if the current completion didn't help 
	    ;; on completing the label.
	    ((and (not (null (cdr allcomp))) (= (length verilog-str)
						(length match)))
	     (with-output-to-temp-buffer "*Completions*"
	       (display-completion-list allcomp))
	     ;; Wait for a keypress. Then delete *Completion*  window
	     (momentary-string-display "" (point))
	     (delete-window (get-buffer-window (get-buffer "*Completions*")))
	     )))))

(defun verilog-show-completions ()
  "Show all possible completions at current point."
  (interactive)
  (let* ((b (save-excursion (skip-chars-backward "a-zA-Z0-9_") (point)))
	 (e (save-excursion (skip-chars-forward "a-zA-Z0-9_") (point)))
	 (verilog-str (buffer-substring b e))
	 ;; The following variable is used in verilog-completion
	 (verilog-buffer-to-use (current-buffer))
	 (allcomp (if (and verilog-toggle-completions
			   (string= verilog-last-word-shown verilog-str))
		      verilog-last-completions
		    (all-completions verilog-str 'verilog-completion))))
    ;; Show possible completions in a temporary buffer.
    (with-output-to-temp-buffer "*Completions*"
      (display-completion-list allcomp))
    ;; Wait for a keypress. Then delete *Completion*  window
    (momentary-string-display "" (point))
    (delete-window (get-buffer-window (get-buffer "*Completions*")))))


(defun verilog-get-default-symbol ()
  "Return symbol around current point as a string."
  (save-excursion
    (buffer-substring (progn
			(skip-chars-backward " \t")
			(skip-chars-backward "a-zA-Z0-9_")
			(point))
		      (progn
			(skip-chars-forward "a-zA-Z0-9_")
			(point)))))

(defun verilog-build-defun-re (str &optional arg)
  "Return function/procedure starting with STR as regular expression.
With optional second arg non-nil, STR is the complete name of the instruction."
  (if arg
      (concat "^\\(function\\|procedure\\)[ \t]+\\(" str "\\)\\>")
    (concat "^\\(function\\|procedure\\)[ \t]+\\(" str "[a-zA-Z0-9_]*\\)\\>")))

;; Function passed to completing-read, try-completion or
;; all-completions to get completion on any function name. If
;; predicate is non-nil, it must be a function to be called for every
;; match to check if this should really be a match. If flag is t, the
;; function returns a list of all possible completions. If it is nil
;; it returns a string, the longest possible completion, or t if STR
;; is an exact match. If flag is 'lambda, the function returns t if
;; STR is an exact match, nil otherwise.

(defun verilog-comp-defun (verilog-str verilog-pred verilog-flag)
  (save-excursion
    (let ((verilog-all nil)
	  match)

      ;; Set buffer to use for searching labels. This should be set
      ;; within functins which use verilog-completions
      (set-buffer verilog-buffer-to-use)

      (let ((verilog-str verilog-str))
	;; Build regular expression for functions
	(if (string= verilog-str "")
	    (setq verilog-str (verilog-build-defun-re "[a-zA-Z_]"))
	  (setq verilog-str (verilog-build-defun-re verilog-str)))
	(goto-char (point-min))
      
	;; Build a list of all possible completions
	(while (re-search-forward verilog-str nil t)
	  (setq match (buffer-substring (match-beginning 2) (match-end 2)))
	  (if (or (null verilog-pred)
		  (funcall verilog-pred match))
	      (setq verilog-all (cons match verilog-all)))))

      ;; Now we have built a list of all matches. Give response to caller
      (verilog-completion-response))))

(defun verilog-goto-defun ()
  "Move to specified Verilog function/procedure.
The default is a name found in the buffer around point."
  (interactive)
  (let* ((default (verilog-get-default-symbol))
	 ;; The following variable is used in verilog-comp-function
	 (verilog-buffer-to-use (current-buffer))
	 (default (if (verilog-comp-defun default nil 'lambda)
		      default ""))
	 (label (if (not (string= default ""))
		    ;; Do completion with default
		    (completing-read (concat "Label: (default " default ") ")
				     'verilog-comp-defun nil t "")
		  ;; There is no default value. Complete without it
		  (completing-read "Label: "
				   'verilog-comp-defun nil t ""))))
    ;; If there was no response on prompt, use default value
    (if (string= label "")
	(setq label default))
    ;; Goto right place in buffer if label is not an empty string
    (or (string= label "")
	(progn
	  (goto-char (point-min))
	  (re-search-forward (verilog-build-defun-re label t))
	  (beginning-of-line)))))

;;; verilog.el ends here
