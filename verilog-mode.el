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

;;; This mode borrows heavily from the pascal-mode and the cc-mode or emacs

;;; USAGE
;;; =====

;;; Emacs should enter Verilog mode when you find a Verilog source file.
;;; When you have entered Verilog mode, you may get more info by pressing
;;; C-h m. You may also get online help describing various functions by:
;;; C-h f <Name of function you want described>

;;; to set up auto mode, include stuff like this in your .emacs:
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
;;; Code:

(defconst verilog-mode-version "1.91 $$Version: $$"
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
  "\\<\\(end\\(case\\|function\\|task\\|module\\|\\)\\|join\\|begin\\|else\\)\\>")

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
    (if (and (or
	      ;; Lemacs before 19.6 had bugs
	      (and (eq major 'v19) (eq flavor 'XEmacs) (< minor 6))
	      ;; Emacs 19 before 19.21 has known bugs
	      (and (eq major 'v19) (eq flavor 'FSF) (< minor 21)))
	     (not c-inhibit-startup-warnings-p))
	(with-output-to-temp-buffer "*verilog-mode warnings*"
	  (print (format
"The version of Emacs that you are running, %s,
has known bugs in its syntax parsing routines which will affect the
performance of verilog-mode. You should strongly consider upgrading to the
latest available version.  verilog-mode may continue to work, after a
fashion, but strange indentation errors could be encountered."
		     emacs-version))))
    ;; Emacs 18, with no patch is not too good
    (if (and (eq major 'v18) (eq comments 'no-dual-comments)
	     (not c-inhibit-startup-warnings-p))
	(with-output-to-temp-buffer "*verilog-mode warnings*"
	  (print (format
"The version of Emacs 18 you are running, %s,
has known deficiencies in its ability to handle dual C++ comments,
i.e. C++ line style comments and C block style comments.  This will
not be much of a problem for you if you are only editing C code, but
if you are doing much C++ editing, you should strongly consider
upgrading to one of the latest Emacs 19's.  In Emacs 18, you may also
experience performance degradations. Emacs 19 has some new built-in
routines which will speed things up for you.

Because of these inherent problems, verilog-mode is no longer being
actively maintained for Emacs 18, however, until you can upgrade to
Emacs 19, you may want to look at verilog-mode-18.el in the verilog-mode
distribution.  THIS FILE IS COMPLETELY UNSUPPORTED!  If you use it,
you are on your own, although patch contributions will be folded into
the main release."
			    emacs-version))))
    ;; Emacs 18 with the syntax patches are no longer supported
    (if (and (eq major 'v18) (not (eq comments 'no-dual-comments))
	     (not c-inhibit-startup-warnings-p))
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
   "\\<\\(begin\\|case\\(x\\|z\\|\\)\\|end\\(case\\|function\\|task\\|module\\)?\\|always\\|initial\\|\\(pos\\|neg\\)edge\\|else\\|for\\(ever\\|\\)\\|if\\|repeat\\|then\\|while\\)\\>"
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
   "\\<\\(begin\\|case\\(x\\|z\\|\\)\\|end\\(case\\|function\\|task\\|module\\)?\\|always\\|initial\\|\\(pos\\|neg\\)edge\\|else\\|for\\(ever\\|\\)\\|if\\|repeat\\|then\\|while\\)\\>"
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
  (forward-line 1))

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
     ((and 
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
		    ))
	  (insert (concat (if 
			      (= else 0)
			      "ifdef " 
			    "!ifdef ")
			  (buffer-substring b e))))))

     ((and (looking-at "\\<end")
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
		   (looking-at "\\<\\(endcase\\)\\|\\(endfunction\\)\\|\\(endtask\\)\\|\\(endmodule\\)\\>"))
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
		 (t 
		  (let (state b e com)
		    (end-of-line)
		    (delete-horizontal-space)
		    (cond 
		     ((match-end 2) (setq reg "\\<function\\>"
					  com " /* function:  */"))
		     ((match-end 3) (setq reg "\\<task\\>"
					  com " /* task:  */"))
		     ((match-end 4) (setq reg "\\<module\\>"
					  com " /* module:  */"))
		     )
		    (save-excursion
		      (setq b (progn (while (and
					     (re-search-backward reg nil 'move)
					     (progn 
					       (setq state (save-excursion
							     (parse-partial-sexp (point-min) (point))))
					       (or (nth 3 state) (nth 4 state))) ; Inside string or comment
					     ))
				     (skip-chars-forward "^ \t")
				     (skip-chars-forward " \t")
				     (point))
			    e (progn (skip-chars-forward "a-zA-Z0-9_")
				     (point))))
		    (insert-string com)
		    (backward-char 3)
		    (insert-buffer-substring (current-buffer) b e))
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
	(skip-chars-forward " \t"))))

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
	   (looking-at verilog-end-defun-re))
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
    (if (looking-at "[ \t]*[0-9a-zA-Z]+[ \t]*:[^=]")
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
;;; verilog.el ends here
