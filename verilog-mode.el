;;; verilog-mode.el --- major mode for editing verilog source in Emacs
;;
;; $Header$

;; Copyright (C) 1996 Free Software Foundation, Inc.

;; Author: Michael McNamara (mac@verilog.com) 
;; President, Silicon Sorcery
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

;;; This mode borrows heavily from the Pascal-mode and the cc-mode of emacs

;;; USAGE
;;; =====

;;; A major mode for editing Verilog HDL source code. When you have
;;; entered Verilog mode, you may get more info by pressing C-h m. You
;;; may also get online help describing various functions by: C-h f
;;; <Name of function you want described>

;;; You can get step by step help in installing this file by going to
;;; <http://www.silicon-sorcery.com/emacs_install.html>

;;; The short list of installation instructions are: To set up
;;; automatic verilog mode, put this file in your load path, and put
;;; the following in code (please un comment it first!) in your
;;; .emacs, or in your site's site-load.el

; (autoload 'verilog-mode "verilog-mode" "Verilog mode" t )
; (setq auto-mode-alist (cons  '("\\.v\\'" . verilog-mode) auto-mode-alist))
; (setq auto-mode-alist (cons  '("\\.dv\\'" . verilog-mode) auto-mode-alist))

;;; If you want to customize Verilog mode to fit your needs better,
;;; you may add these lines (the values of the variables presented
;;; here are the defaults). Note also that if you use an emacs that
;;; supports custom, it's probably better to use the custom menu to
;;; edit these.
;;;
; ;; User customization for Verilog mode
; (setq verilog-indent-level             3
;       verilog-indent-level-module      3
;       verilog-indent-level-declaration 3
;       verilog-indent-level-behavioral  3
;       verilog-case-indent              2
;       verilog-auto-newline             t
;       verilog-auto-indent-on-newline   t
;       verilog-tab-always-indent        t
;       verilog-auto-endcomments         t
;       verilog-minimum-comment-distance 40
;       verilog-indent-begin-after-if    t
;       verilog-auto-lineup              '(all))

;;; KNOWN BUGS / BUG REPORTS
;;; ======================= 
'
;;; This is beta code, and likely has bugs. Please report any and all
;;; bugs to me at verilog-mode-bugs@verilog.com.  Use
;;; verilog-submit-bug-report to submit a report.
;; 
;;; Code:

(provide 'verilog-mode)

;; This variable will always hold the version number of the mode
(defconst verilog-mode-version "$$Revision$$"
  "Version of this verilog mode.")

;;
;; A hack so we can support either custom, or the old defvar
;;
;; Insure we have certain packages, and deal with it if we don't

(if (fboundp 'eval-when-compile)
    (eval-when-compile
      (condition-case nil
          (require 'imenu)
        (error nil))
      (condition-case nil
	  (require 'reporter)
        (error nil))
      (condition-case nil
          (require 'easymenu)
        (error nil))
      (condition-case nil
          (if (fboundp 'store-match-data)
	      nil ;; fab
	    (defmacro store-match-data (&rest args) nil))
        (error nil))
      (condition-case nil
	  (if (boundp 'current-menubar)
	      nil ;; great
	    (defmacro set-buffer-menubar (&rest args) nil)
	    (defmacro add-submenu (&rest args) nil))
	(error nil))
      (condition-case nil
	  (if (fboundp 'zmacs-activate-region)
	      nil ;; great
	    (defmacro zmacs-activate-region (&rest args) nil))
	(error nil))
      (condition-case nil
	  (require 'custom)
	(error nil))
      (if (and (featurep 'custom) (fboundp 'custom-declare-variable))
	  nil ;; We've got what we needed
	;; We have the old custom-library, hack around it!
	(defmacro defgroup (&rest args)  nil)
	(defmacro customize (&rest args)
	  (message "Sorry, Customize is not available with this version of emacs"))
	(defmacro defcustom (var value doc &rest args) 
	  (` (defvar (, var) (, value) (, doc))))
	)
      (if (and (featurep 'custom) (fboundp 'customize-group))
	  nil ;; We've got what we needed
	;; We have an intermediate custom-library, hack around it!
	(defmacro customize-group (var &rest args) 
	  (`(customize (, var) )))
	)
      
      ))

(defun verilog-customize ()
  "Link to customize screen for Verilog"
  (interactive)
  (customize-group 'verilog-mode)
  )

(defun verilog-font-customize ()
  "Link to customize fonts used for Verilog"
  (interactive)
  (customize-apropos "font-lock-*" 'faces)
  )

(defgroup verilog-mode nil
  "Facilitates easy editing of Verilog source text"
  :group 'languages)

(defcustom verilog-compiler "vcs "
  "*Program and arguments to use to compile/run/lint verilog source."
  :type 'string 
  :group 'verilog-mode
  )
      
(defcustom verilog-indent-level 3
  "*Indentation of Verilog statements with respect to containing block."
  :group 'verilog-mode
  :type 'integer 
  )

(defcustom verilog-indent-level-module 3
  "* Indentation of Module level Verilog statements. (eg always, initial)
    Set to 0 to get initial and always statements lined up 
    on the left side of your screen."
  :group 'verilog-mode
  :type 'integer 
  )

(defcustom verilog-indent-level-declaration 3
  "*Indentation of declarations with respect to containing block. 
    Set to 0 to get them list right under containing block."
  :group 'verilog-mode
  :type 'integer 
  )

(defcustom verilog-indent-level-behavioral 3
  "*Absolute indentation of first begin in a task or function block
    Set to 0 to get such code to start at the left side of the screen."
  :group 'verilog-mode
  :type 'integer 
  )

(defcustom verilog-cexp-indent 2
  "*Indentation of Verilog statements split across lines."
  :group 'verilog-mode
  :type 'integer 
  )

(defcustom verilog-case-indent 2
  "*Indentation for case statements."
  :group 'verilog-mode
  :type 'integer 
  )

(defcustom verilog-auto-newline t
  "*Non-nil means automatically newline after semicolons"
  :group 'verilog-mode
  :type 'boolean
  )

(defcustom verilog-auto-indent-on-newline t
  "*Non-nil means automatically indent line after newline"
  :group 'verilog-mode
  :type 'boolean
  )

(defcustom verilog-tab-always-indent t
  "*Non-nil means TAB in Verilog mode should always re-indent the
  current line, regardless of where in the line point is when the TAB
  command is used."
  :group 'verilog-mode
  :type 'boolean 
  )

(defcustom verilog-indent-begin-after-if t
  "*If true, indent begin statements following if, else, while, for
  and repeat.  otherwise, line them up."
  :group 'verilog-mode
  :type 'boolean )


(defcustom verilog-align-ifelse nil
  "*If true, align `else' under matching `if'. Otherwise
  else is lined up with first character on line holding matching if "
  :group 'verilog-mode
  :type 'boolean )

(defcustom verilog-auto-endcomments t
  "*Non-nil means a comment /* ... */ is set after the ends which ends
  cases and functions. The name of the function or case will be set
  between the braces."
  :group 'verilog-mode
  :type 'boolean )

(defcustom verilog-minimum-comment-distance 40
  "*Minimum distance between begin and end required before a comment
  will be inserted.  Setting this variable to zero results in every
  end acquiring a comment; the default avoids too many redundant
  comments in tight quarters"
  :group 'verilog-mode
  :type 'integer 
  )

(defvar verilog-auto-lineup '(all) 
  "*List of contexts where auto lineup of :'s or ='s should be done.
Elements can be of type: 'declaration' or 'case', which will do auto
lineup in declarations or case-statements respectively. The word 'all'
will do all lineups. '(case declaration) for instance will do lineup
in case-statements and parameter list, while '(all) will do all
lineups."
  )

(defvar verilog-mode-abbrev-table nil
  "Abbrev table in use in Verilog-mode buffers.")

(defvar verilog-font-lock-keywords-after-1930
  '(
   ("^\\s-*\\(function\\|task\\|module\\|macromodule\\|primitive\\)\\>\\s-*\\(\\sw+\\)"  
    2 'font-lock-function-name-face nil t)
   ("\\(\\\\\\S-*\\s-\\)\\|\\(`\\s-*[A-Za-z][A-Za-z0-9_]*\\)" 0 'font-lock-function-name-face)
   ("\\(@\\)\\|\\(#\\s-*\\(\\(\[0-9\]+\\('[hdxbo][0-9_xz]*\\)?\\)\\|\\((\[^)\]*)\\|\\sw+\\)\\)\\)" 0 'font-lock-type-face)
; "integer" "input" "inout" "parameter" "defparam" "output" "supply0" "supply1" "supply" "tri0" "tri1" "trireg"
; "triand" trior" "wire" "wor" "wand" "time" "real" "realtime" "reg" "signed" "vectored"
   ("\\<\\(defparam\\|in\\(out\\|put\\|teger\\)\\|output\\|parameter\\|re\\(al\\(\\|time\\)\\|g\\)\\|s\\(igned\\|upply\\(\\|[01]\\)\\)\\|t\\(ime\\|ri\\([01]\\|and\\|or\\|reg\\)\\)\\|vectored\\|w\\(and\\|ire\\|or\\)\\)\\>" 0 'font-lock-type-face)
; "assign" "force" "always" "initial" "begin" "end"  "case" "casex" "casez" "default" "endcase"
; "if" "wait" "else" "fork" "join" "for" "while" "repeat" "forever" "posedge" "negedge"
; "primitive" "endprimitive" "specify" "endspecify" "table" "endtable" 
; "function" "endfunction" "task" "endtask" "module" "macromodule""endmodule"
 ("\\<\\(\\$[a-zA-Z][a-zA-Z0-9_\\$]*\\|\\(a\\(lways\\|ssign\\)\\|begin\\|case\\(\\|[xz]\\)\\|\\(de\\(fault\\|assign\\)\\)\\|e\\(lse\\|nd\\(\\|case\\|function\\|module\\|primitive\\|specify\\|ta\\(ble\\|sk\\)\\)\\)\\|f\\(or\\(\\|ce\\|ever\\|k\\)\\|unction\\)\\|i\\(f\\|nitial\\)\\|join\\|m\\(acromodule\\|odule\\)\\|negedge\\|p\\(osedge\\|rimitive\\)\\|repeat\\|specify\\|ta\\(ble\\|sk\\)\\|w\\(ait\\|hile\\)\\)\\)\\>" 0 'font-lock-keyword-face)

   )
)

(defvar verilog-font-lock-keywords-before-1930
  '(
    ("^\\s-*\\(function\\|task\\|module\\|macromodule\\|primitive\\)\\>\\s-*\\(\\sw+\\)"  
     2 font-lock-function-name-face nil t)
    ("\\(\\\\\\S-*\\s-\\)\\|\\(`\\s-*[A-Za-z][A-Za-z0-9_]*\\)" 0 font-lock-function-name-face)
    ("[@#]" . font-lock-type-face)
; "integer" "input" "inout" "parameter" "defparam" "output" "supply0" "supply1" "supply" "tri0" "tri1" "trireg"
; "triand" trior" "wire" "wor" "wand" "time" "real" "realtime" "reg" "signed" "vectored"
   ("\\<\\(defparam\\|in\\(out\\|put\\|teger\\)\\|output\\|parameter\\|re\\(al\\(\\|time\\)\\|g\\)\\|s\\(igned\\|upply\\(\\|[01]\\)\\)\\|t\\(ime\\|ri\\([01]\\|and\\|or\\|reg\\)\\)\\|vectored\\|w\\(and\\|ire\\|or\\)\\)\\>" 0 font-lock-type-face)
; "assign" "force" "always" "initial" "begin" "end"  "case" "casex" "casez" "default" "endcase"
; "if" "wait" "else" "fork" "join" "for" "while" "repeat" "forever" "posedge" "negedge"
; "primitive" "endprimitive" "specify" "endspecify" "table" "endtable" 
; "function" "endfunction" "task" "endtask" "module" "macromodule""endmodule"
   ("\\<\\(\\$[a-zA-Z][a-zA-Z0-9_\\$]*\\|\\(a\\(lways\\|ssign\\)\\|begin\\|case\\(\\|[xz]\\)\\|\\(de\\(fault\\|assign\\)\\)\\|e\\(lse\\|nd\\(\\|case\\|function\\|module\\|primitive\\|specify\\|ta\\(ble\\|sk\\)\\)\\)\\|f\\(or\\(\\|ce\\|ever\\|k\\)\\|unction\\)\\|i\\(f\\|nitial\\)\\|join\\|m\\(acromodule\\|odule\\)\\|negedge\\|p\\(osedge\\|rimitive\\)\\|repeat\\|specify\\|ta\\(ble\\|sk\\)\\|w\\(ait\\|hile\\)\\)\\)\\>" 0 font-lock-keyword-face)
    )
)

(defvar verilog-imenu-generic-expression
  '((nil "^\\s-*\\(\\(m\\(odule\\|acromodule\\)\\)\\|primitive\\)\\s-+\\([a-zA-Z0-9_.:]+\\)" 3)
    ("*Vars*" "^\\s-*\\(reg\\|wire\\)\\)\\s-+\\(\\|\\[[^\\]+]\\s-+\\)\\([-A-Za-z0-9+]+\\)" 3))
  "Imenu expression for Verilog-mode.  See `imenu-generic-expression'.")

(defvar verilog-mode-abbrev-table nil
  "Abbrev table in use in Verilog-mode buffers.")


(define-abbrev-table 'verilog-mode-abbrev-table ())

(defvar verilog-mode-map ()
  "Keymap used in Verilog mode.")
(if verilog-mode-map
    ()
  (setq verilog-mode-map (make-sparse-keymap))
  (define-key verilog-mode-map ";"        'electric-verilog-semi)
  (define-key verilog-mode-map [(control 59)]    'electric-verilog-semi-with-comment)
  (define-key verilog-mode-map ":"        'electric-verilog-colon)
  (define-key verilog-mode-map "="        'electric-verilog-equal)
  (define-key verilog-mode-map "\`"       'electric-verilog-tick)
  (define-key verilog-mode-map "\t"       'electric-verilog-tab)
  (define-key verilog-mode-map "\r"       'electric-verilog-terminate-line)
  (define-key verilog-mode-map "\M-\C-b"  'electric-verilog-backward-sexp)
  (define-key verilog-mode-map "\M-\C-f"  'electric-verilog-forward-sexp)
  (define-key verilog-mode-map "\M-\r"    (function (lambda ()
		      (interactive) (electric-verilog-terminate-line 1))))
  (define-key verilog-mode-map "\177"     'backward-delete-char-untabify)
  (define-key verilog-mode-map "\M-\t"    'verilog-complete-word)
  (define-key verilog-mode-map "\M-?"     'verilog-show-completions)
  (define-key verilog-mode-map "\M-\C-h"  'verilog-mark-defun)
  (define-key verilog-mode-map "\C-c\C-r" 'verilog-label-be)
  (define-key verilog-mode-map "\C-c\C-i" 'verilog-pretty-declarations)
  (define-key verilog-mode-map "\C-c\C-b" 'verilog-submit-bug-report)
  (define-key verilog-mode-map "\M-*"     'verilog-star-comment)
  (define-key verilog-mode-map "\C-c\C-c" 'verilog-comment-region)
  (define-key verilog-mode-map "\C-c\C-u" 'verilog-uncomment-region)
  (define-key verilog-mode-map "\M-\C-a"  'verilog-beg-of-defun)
  (define-key verilog-mode-map "\M-\C-e"  'verilog-end-of-defun)
  (define-key verilog-mode-map "\C-c\C-d" 'verilog-goto-defun)
  )

;; menus

(if (string-match "XEmacs" emacs-version)
    (defvar verilog-xemacs-menu
      '("Verilog"
	["Line up declarations around point"        verilog-pretty-declarations t]
	["Redo/insert comments on every end" verilog-label-be t]
	"----"
	["Beginning of function"     verilog-beg-of-defun t]
	["End of function"           verilog-end-of-defun t]
	["Mark function"             verilog-mark-defun t]
	"----"
	["Move to beginning of block" electric-verilog-backward-sexp t]
	["Move to end of block"      electric-verilog-forward-sexp t]
	"----" 
	["Comment Region"            verilog-comment-region t]
	["UnComment Region"          verilog-uncomment-region t]
	["Multi-line comment insert" verilog-star-comment t]
	"----" 
	["Insert begin-end block"    verilog-insert-block t]
	["Complete word"             verilog-complete-word t]
	"----"
	["Submit bug report"         verilog-submit-bug-report t]
	["Customize Verilog Mode..." verilog-customize t]
	["Customize Fonts & Colors used by Verilog" verilog-font-customize t]
	"XEmacs menu for VERILOG mode."))
  (progn
    (easy-menu-define verilog-menu verilog-mode-map "Menu for Verilog mode"
		      '("Verilog"
			["Line up declarations around point"        verilog-pretty-declarations t]
			["Redo/insert comments on every end" verilog-label-be t]
			"----"
			["Beginning of function"     verilog-beg-of-defun t]
			["End of function"           verilog-end-of-defun t]
			["Mark function"             verilog-mark-defun t]
			"----" 
			["Move to beginning of block" electric-verilog-backward-sexp t]
			["Move to end of block"      electric-verilog-forward-sexp t]
			"----" 
			["Comment Region"            verilog-comment-region t]
			["UnComment Region"          verilog-uncomment-region t]
			["Multi-line comment insert" verilog-star-comment t]
			"----" 
			["Insert begin-end block"    verilog-insert-block t]
			["Complete word"             verilog-complete-word t]
			"----"
			["Submit bug report"         verilog-submit-bug-report t]
			["Customize Verilog Mode..." verilog-customize t]
			["Customize Fonts & Colors used by Verilog" verilog-font-customize t]
			))))

(defvar verilog-mode-abbrev-table nil
  "Abbrev table in use in Verilog-mode buffers.")

(define-abbrev-table 'verilog-mode-abbrev-table ())

;; compilation program
(defun verilog-compile ()
  "function to compile verilog"
  (or (file-exists-p "makefile") (file-exists-p "Makefile")
      (progn (make-local-variable 'compile-command)
	     (setq compile-command
		   (concat verilog-compiler
			   buffer-file-name)))))

(add-hook 'verilog-mode-hook 'verilog-compile)

;;;
;;; Regular expressions used to calculate indent, etc.
;;;
(defconst verilog-symbol-re      "\\<[a-zA-Z_][a-zA-Z_0-9.]*\\>")
(defconst verilog-case-re        "\\(\\<case[xz]?\\>\\)")
;; Want to match
;; aa :
;; aa,bb :
;; a[34:32] :
;; a,
;;   b :
(defconst 
  verilog-no-indent-begin-re 
  "\\<\\(if\\|else\\|while\\|for\\|repeat\\|always\\)\\>")
(defconst verilog-ends-re
  (concat
   "\\(\\<else\\>\\)\\|"
   "\\(\\<if\\>\\)\\|"
   "\\(\\<end\\>\\)\\|"
   "\\(\\<join\\>\\)\\|" 
   "\\(\\<endcase\\>\\)\\|" 
   "\\(\\<endtable\\>\\)\\|" 
   "\\(\\<endspecify\\>\\)\\|" 
   "\\(\\<endfunction\\>\\)\\|"
   "\\(\\<endtask\\>\\)"))


(defconst verilog-enders-re
  (concat "\\(\\<endcase\\>\\)\\|"
	  "\\(\\<end\\>\\)\\|"
	  "\\(\\<end\\(\\(function\\)\\|\\(task\\)\\|"
	  "\\(module\\)\\|\\(primitive\\)\\)\\>\\)"))
(defconst verilog-endcomment-reason-re 
  (concat 
   "\\(\\<fork\\>\\)\\|"
   "\\(\\<begin\\>\\)\\|"
   "\\(\\<if\\>\\)\\|"
   "\\(\\<else\\>\\)\\|"
   "\\(\\<end\\>.*\\<else\\>\\)\\|"
   "\\(\\<task\\>\\)\\|"
   "\\(\\<function\\>\\)\\|"
   "\\(\\<initial\\>\\)\\|"
   "\\(\\<always\\>\\(\[ \t\]*@\\)?\\)\\|"
   "\\(\\<while\\>\\)\\|"
   "\\(\\<for\\(ever\\)?\\>\\)\\|"
   "\\(\\<repeat\\>\\)\\|\\(\\<wait\\>\\)\\|"
   "#"))

(defconst verilog-named-block-re  "begin[ \t]*:")
(defconst verilog-beg-block-re
  ;; "begin" "case" "casex" "fork" "casez" "table" "specify" "function" "task"
  "\\(\\<\\(begin\\>\\|case\\(\\>\\|x\\>\\|z\\>\\)\\|f\\(ork\\>\\|unction\\>\\)\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)\\)")

(defconst verilog-beg-block-re-1 
  "\\<\\(begin\\)\\|\\(case[xz]?\\)\\|\\(fork\\)\\|\\(table\\)\\|\\(specify\\)\\|\\(function\\)\\|\\(task\\)\\>")
(defconst verilog-end-block-re   
  ;; "end" "join" "endcase" "endtable" "endspecify" "endtask" "endfunction"
  "\\<\\(end\\(\\>\\|case\\>\\|function\\>\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)\\|join\\>\\)")

(defconst verilog-end-block-re-1 "\\(\\<end\\>\\)\\|\\(\\<endcase\\>\\)\\|\\(\\<join\\>\\)\\|\\(\\<endtable\\>\\)\\|\\(\\<endspecify\\>\\)\\|\\(\\<endfunction\\>\\)\\|\\(\\<endtask\\>\\)")
(defconst verilog-declaration-re 
  ;; "input" "inout" "output" "integer" "parameter" "defparam" "event" 
  ;; "real" "reg" "realtime" "time" "tri" "tri0" "tri1" "trireg" "triand" 
  ;; "trior" "supply0" "supply1" "wire" "wor" "wand"
"\\(\\<\\(defparam\\>\\|event\\>\\|in\\(out\\>\\|put\\>\\|teger\\>\\)\\|output\\>\\|parameter\\>\\|re\\(al\\(\\>\\|time\\>\\)\\|g\\>\\)\\|supply\\(0\\>\\|1\\>\\)\\|t\\(ime\\>\\|ri\\(0\\>\\|1\\>\\|\\>\\|and\\>\\|or\\>\\|reg\\>\\)\\)\\|w\\(and\\>\\|ire\\>\\|or\\>\\)\\)\\)")
(defconst verilog-declaration-re-1 (concat "^[ \t]*" verilog-declaration-re "[ \t]*\\(\\[[^]]*\\][ \t]*\\)?"))
(defconst verilog-declaration-re-2 (concat "[ \t]*" verilog-declaration-re "[ \t]*\\(\\[[^]]*\\][ \t]*\\)?"))
(defconst verilog-defun-re 
  ;;"module" "macromodule" "primitive"
  "\\(\\<\\(m\\(acromodule\\>\\|odule\\>\\)\\|primitive\\>\\)\\)")
(defconst verilog-end-defun-re   
  ;; "endmodule" "endprimitive"
"\\(\\<end\\(module\\>\\|primitive\\>\\)\\)")
(defconst verilog-zero-indent-re 
  (concat verilog-defun-re "\\|" verilog-end-defun-re))
(defconst verilog-directive-re
  ;;   "`else" "`ifdef" "`endif" "`define" "`undef" "`include"
  "`\\(define\\>\\|e\\(lse\\>\\|ndif\\>\\)\\|i\\(fdef\\>\\|nclude\\>\\)\\|undef\\>\\|timescale\\)")
(defconst verilog-directive-re-1
  ;;   "`else" "`ifdef" "`endif" "`define" "`undef" "`include"
       (concat "[ \t]*"  verilog-directive-re))
(defconst verilog-autoindent-lines-re
  ;; "macromodule" "module" "primitive" "end" "endcase" "endfunction"
  ;; "endtask" "endmodule" "endprimitive" "endspecify" "endtable" "join" 
  ;; "begin" "else" "`else" "`ifdef" "`endif" "`define" "`undef" "`include"
  "\\(\\(`\\(define\\>\\|e\\(lse\\>\\|ndif\\>\\)\\|i\\(fdef\\>\\|nclude\\>\\)\\|undef\\>\\)\\)\\|\\(\\<begin\\>\\|e\\(lse\\>\\|nd\\(\\>\\|case\\>\\|function\\>\\|module\\>\\|primitive\\>\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)\\)\\|join\\>\\|m\\(acromodule\\>\\|odule\\>\\)\\|primitive\\>\\)\\)")

(defconst verilog-behavioral-block-beg-re
  "\\(\\<initial\\>\\|\\<always\\>\\|\\<function\\>\\|\\<task\\>\\)")
(defconst verilog-indent-reg 
  (concat 
   "\\(\\<begin\\>\\|\\<case[xz]?\\>\\|\\<specify\\>\\|\\<fork\\>\\|\\<table\\>\\)\\|"
   "\\(\\<end\\>\\|\\<join\\>\\|\\<endcase\\>\\|\\<endtable\\>\\|\\<endspecify\\>\\)\\|" 
   "\\(\\<module\\>\\|\\<macromodule\\>\\|\\<primitive\\>\\|\\<initial\\>\\|\\<always\\>\\)\\|"
   "\\(\\<endmodule\\>\\|\\<endprimitive\\>\\)\\|"
   "\\(\\<endtask\\>\\|\\<endfunction\\>\\)\\|"
   "\\(\\<function\\>\\|\\<task\\>\\)"	  
   ;;	  "\\|\\(\\<if\\>\\|\\<else\\>\\)"
   ))
(defconst verilog-indent-re 
  "\\(\\<\\(always\\>\\|begin\\>\\|case\\(\\>\\|x\\>\\|z\\>\\)\\|end\\(\\>\\|case\\>\\|function\\>\\|module\\>\\|primitive\\>\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)\\|f\\(ork\\>\\|unction\\>\\)\\|initial\\>\\|join\\>\\|m\\(acromodule\\>\\|odule\\>\\)\\|primitive\\>\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)\\)")

(defconst verilog-defun-level-re 
  ;; "module" "macromodule" "primitive" "initial" "always" "endtask" "endfunction"
  "\\(\\<\\(always\\>\\|end\\(function\\>\\|task\\>\\)\\|initial\\>\\|m\\(acromodule\\>\\|odule\\>\\)\\|primitive\\>\\)\\)")
(defconst verilog-cpp-level-re 
 ;;"endmodule" "endprimitive"
  "\\(\\<end\\(module\\>\\|primitive\\>\\)\\)")
(defconst verilog-behavioral-level-re
  ;; "function" "task"
  "\\(\\<\\(function\\>\\|task\\>\\)\\)")
(defconst verilog-complete-reg
  ;; "always" "initial" "repeat" "case" "casex" "casez" "while" "if" "for" "forever" "else"
  "\\<\\(always\\|case\\(\\|[xz]\\)\\|else\\|for\\(\\|ever\\)\\|i\\(f\\|nitial\\)\\|repeat\\|while\\)\\>")
(defconst verilog-end-statement-re 
  (concat "\\(" verilog-beg-block-re "\\)\\|\\("
	  verilog-end-block-re "\\)"))
(defconst verilog-endcase-re 
  (concat verilog-case-re "\\|" 
	  "\\(endcase\\)\\|"
	  verilog-defun-re
	  ))
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
     ((= major 4)  (setq major 'v18))	;Epoch 4
     ((= major 18) (setq major 'v18))	;Emacs 18
     ((= major 19) (setq major 'v19	;Emacs 19
			 flavor (if (or (string-match "Lucid" emacs-version)
					(string-match "XEmacs" emacs-version))
				    'XEmacs 'FSF)))
     ((= major 20) (setq major 'v20 
			 flavor (if (or (string-match "Lucid" emacs-version)
					(string-match "XEmacs" emacs-version))
				    'XEmacs 'FSF)))
     ;; I don't know
     (t (error "Cannot recognize major version number: %s" major)))
    ;; XEmacs 19 uses 8-bit modify-syntax-entry flags, as do all
    ;; patched Emacs 19, Emacs 18, Epoch 4's.  Only Emacs 19 uses a
    ;; 1-bit flag.  Let's be as smart as we can about figuring this
    ;; out.
    (if (or (eq major 'v20) (eq major 'v19))
	(let ((table (copy-syntax-table)))
	  (modify-syntax-entry ?a ". 12345678" table)
	  (cond
	   ;; XEmacs pre 20 and Emacs pre 19.30 use vectors for syntax tables.
	   ((vectorp table)
	    (if (= (logand (lsh (aref table ?a) -16) 255) 255)
		(setq comments '8-bit)
	      (setq comments '1-bit)))
	   ;; XEmacs 20 is known to be 8-bit
	   ((eq flavor 'XEmacs) (setq comments '8-bit))
	   ;; Emacs 19.30 and beyond are known to be 1-bit
	   ((eq flavor 'FSF) (setq comments '1-bit))
	   ;; Don't know what this is
	   (t (error "Couldn't figure out syntax table format."))
	   ))
      ;; Emacs 18 has no support for dual comments
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
 XEmacs 20:                  (v20 8-bit)
 Emacs 19,20:                (v19 1-bit).")

(defconst verilog-comment-start-regexp "//\\|/\\*"
  "Dual comment value for `comment-start-regexp'.")

(defun verilog-populate-syntax-table (table)
  ;; Populate the syntax TABLE
  (modify-syntax-entry ?\\ "\\" table)
  (modify-syntax-entry ?+ "." table)
  (modify-syntax-entry ?- "." table)
  (modify-syntax-entry ?= "." table)
  (modify-syntax-entry ?% "." table)
  (modify-syntax-entry ?< "." table)
  (modify-syntax-entry ?> "." table)
  (modify-syntax-entry ?& "." table)
  (modify-syntax-entry ?| "." table)
  (modify-syntax-entry ?` "w" table)
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
    )
   ((memq '1-bit verilog-emacs-features)
    ;; Emacs 19 does things differently, but we can work with it
    (modify-syntax-entry ?/  ". 124b" table)
    (modify-syntax-entry ?*  ". 23"   table)
    (modify-syntax-entry ?\n "> b"    table)
    )
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

(defvar verilog-font-lock-keywords nil
  "keyword highlighting used in verilog-mode buffers.")
(defvar verilog-font-lock-keywords-1 nil
  "keyword highlighting used in verilog-mode buffers.")
(defvar verilog-font-lock-keywords-2 nil
  "keyword highlighting used in verilog-mode buffers.")
(defvar verilog-font-lock-keywords-3 nil
  "keyword highlighting used in verilog-mode buffers.")
(defvar verilog-font-lock-keywords-4 nil
  "keyword highlighting used in verilog-mode buffers.")
(if verilog-font-lock-keywords
    ()
  (cond
   ;; We can assume 8-bit syntax table emacsen aupport new syntax
   ((memq '8-bit verilog-emacs-features)
    (setq verilog-font-lock-keywords verilog-font-lock-keywords-after-1930
	  verilog-font-lock-keywords-1 verilog-font-lock-keywords-after-1930
	  verilog-font-lock-keywords-2 verilog-font-lock-keywords-after-1930
	  verilog-font-lock-keywords-3 verilog-font-lock-keywords-after-1930
	  verilog-font-lock-keywords-4 verilog-font-lock-keywords-after-1930)
    )
   (t
    (setq verilog-font-lock-keywords   verilog-font-lock-keywords-before-1930
	  verilog-font-lock-keywords-1 verilog-font-lock-keywords-before-1930
	  verilog-font-lock-keywords-2 verilog-font-lock-keywords-before-1930
	  verilog-font-lock-keywords-3 verilog-font-lock-keywords-before-1930
	  verilog-font-lock-keywords-4 verilog-font-lock-keywords-before-1930)
    )
   )
  )

;;;
;;;  Macros
;;;

(defsubst verilog-re-search-forward (REGEXP BOUND NOERROR)
  "Like re-search-forward, but skips over matches in comments or strings"
  (store-match-data '(nil nil))    
  (while (and
	  (re-search-forward REGEXP BOUND NOERROR)
	  (and (verilog-skip-forward-comment-or-string)
	       (progn 
		 (store-match-data '(nil nil))
		 (if BOUND
		     (< (point) BOUND)
		   t)
		 )
	       )
	  )
    )
  (match-end 0))

(defsubst verilog-re-search-backward (REGEXP BOUND NOERROR)
  "Like re-search-backward, but skips over matches in comments or strings"
  (store-match-data '(nil nil))
  (while (and
	  (re-search-backward REGEXP BOUND NOERROR)
	  (verilog-skip-backward-comment-or-string)
	  (not (store-match-data '(nil nil))))
    ())
  (match-end 0))

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

(defun electric-verilog-backward-sexp ()
  "Move backward over a sexp"
  (interactive)
  ;; before that see if we are in a comment
  (verilog-backward-sexp)
)
(defun electric-verilog-forward-sexp ()
  "Move backward over a sexp"
  (interactive)
  ;; before that see if we are in a comment
  (verilog-forward-sexp)
)

(defun verilog-backward-sexp ()
  (let ((reg)
	(elsec 1)
	(found nil)
	)
    (if (not (looking-at "\\<"))
	(forward-word -1))
    (cond
     ((verilog-skip-backward-comment-or-string)
      )
     ((looking-at "\\<else\\>")
      (setq reg (concat
		 verilog-end-block-re
		 "\\|\\(\\<else\\>\\)"
		 "\\|\\(\\<if\\>\\)"
		 ))
      (while (and (not found)
		  (verilog-re-search-backward reg nil 'move))
	(cond 
	 ((match-end 1) ; endblock
	; try to leap back to matching outward block by striding across
	; indent level changing tokens then immediately
	; previous line governs indentation.
	  (verilog-leap-to-head)
	  )
	 ((match-end 2) ; else, we're in deep
	  (setq elsec (1+ elsec))				 
	  )
	 ((match-end 3) ; found it
	  (setq elsec (1- elsec))
	  (if (= 0 elsec)
	      ;; Now previous line describes syntax
	      (setq found 't)
	    ))
	 )
	)
      )
     ((looking-at verilog-end-block-re)
      (verilog-leap-to-head)
      )
     ((looking-at "\\(endmodule\\>\\)\\|\\(\\<endprimitive\\>\\)")
      (cond
       ((match-end 1)
	(verilog-re-search-backward "\\<\\(macro\\)?module\\>" nil 'move))
       ((match-end 2)
	(verilog-re-search-backward "\\<primitive\\>" nil 'move))
       (t 
	(backward-sexp 1))))
     (t
      (backward-sexp))
     ) ;; cond
    )
  )
(defun verilog-forward-sexp ()
  (let ((reg)
	(st (point)))
    (if (not (looking-at "\\<"))
	(forward-word -1))
    (cond
     ((verilog-skip-forward-comment-or-string)
      (verilog-forward-syntactic-ws)
      )
     ((looking-at verilog-beg-block-re-1);; begin|fork|case|table|specify
      (cond 
       ((match-end 1) ; end
	;; Search forward for matching begin
	(setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" )
	)
       ((match-end 2) ; endcase
	;; Search forward for matching case
	(setq reg "\\(\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" )
	)
       ((match-end 3) ; join
	;; Search forward for matching fork
	(setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" )
	)
       ((match-end 4) ; endtable
	;; Search forward for matching table
	(setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" )
	)
       ((match-end 5) ; endspecify
	;; Search forward for matching specify
	(setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" )
	)
       ((match-end 6) ; endfunction
	;; Search forward for matching function
	(setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" )
	)
       ((match-end 7) ; endspecify
	;; Search forward for matching task
	(setq reg "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)" )
	)
       )
      (if (forward-word 1)
	  (catch 'skip
	    (let ((nest 1))
	      (while (verilog-re-search-forward reg nil 'move)
		(cond 
		 ((match-end 2) ; end
		  (setq nest (1- nest))
		  (if (= 0 nest)
		      (throw 'skip 1)))
		 ((match-end 1) ; begin
		  (setq nest (1+ nest)))))
	      )
	    )
	)
      )
     ((looking-at "\\(\\<\\(macro\\)?module\\>\\)\\|\\(\\<primitive\\>\\)")
      (cond
       ((match-end 1)
	(verilog-re-search-forward "\\<endmodule\\>" nil 'move))
       ((match-end 2)
	(verilog-re-search-forward "\\<endprimitive\\>" nil 'move))
       (t 
	(goto-char st)
	(if (= (following-char) ?\) )
	    (forward-char 1)
	  (forward-sexp 1)))))
     (t
      (goto-char st)
      (if (= (following-char) ?\) )
	  (forward-char 1)
	(forward-sexp 1)))
     ) ;; cond
    )
  )


(defun verilog-declaration-beg ()
  (verilog-re-search-backward verilog-declaration-re (bobp) t))
  
(defsubst verilog-within-string ()
  (save-excursion
    (nth 3 (parse-partial-sexp (verilog-get-beg-of-line) (point)))))

(put 'verilog-mode 'font-lock-defaults 
     '((verilog-font-lock-keywords-after-1930 )
       nil ;; nil means highlight strings & comments as well as keywords
       nil ;; nil means keywords must match case
       nil ;; syntax table handled elsewhere
       verilog-beg-of-defun ;; function to move to beginning of reasonable region to highlight
       ))

;;;###autoload
(defun verilog-mode ()
"Major mode for editing Verilog code. \\<verilog-mode-map>
NEWLINE, TAB indents for Verilog code.  
Delete converts tabs to spaces as it moves back.
Supports highlighting.

Variables controlling indentation/edit style:

 verilog-indent-level           (default 3)
    Indentation of Verilog statements with respect to containing block.
 verilog-indent-level-module    (default 3)
    Absolute indentation of Module level Verilog statements. 
    Set to 0 to get initial and always statements lined up 
    on the left side of your screen.
 verilog-indent-level-declaration    (default 3)
    Indentation of declarations with respect to containing block. 
    Set to 0 to get them list right under containing block.
 verilog-indent-level-behavioral    (default 3)
    Indentation of first begin in a task or function block
    Set to 0 to get such code to linedup underneath the task or function keyword
 verilog-cexp-indent            (default 1)
    Indentation of Verilog statements broken across lines IE:
    if (a)
     begin
 verilog-case-indent            (default 2)
    Indentation for case statements.
 verilog-auto-newline           (default nil)
    Non-nil means automatically newline after semicolons and the punctation 
    mark after an end.
 verilog-auto-indent-on-newline (default t)
    Non-nil means automatically indent line after newline
 verilog-tab-always-indent      (default t)
    Non-nil means TAB in Verilog mode should always reindent the current line,
    regardless of where in the line point is when the TAB command is used.
 verilog-indent-begin-after-if  (default t)
    Non-nil means to indent begin statements following a preceding
    if, else, while, for and repeat statements, if any. otherwise,
    the begin is lined up with the preceding token. If t, you get:
      if (a)
         begin // amount of indent based on verilog-cexp-indent
    otherwise you get:
      if (a)
      begin
 verilog-auto-endcomments       (default t)
    Non-nil means a comment /* ... */ is set after the ends which ends 
      cases, tasks, functions and modules.
    The type and name of the object will be set between the braces.
 verilog-minimum-comment-distance (default 40)
    Minimum distance between begin and end required before a comment
    will be inserted.  Setting this variable to zero results in every
    end aquiring a comment; the default avoids too many redundanet
    comments in tight quarters. 
 verilog-auto-lineup            (default `(all))
    List of contexts where auto lineup of :'s or ='s should be done.

Turning on Verilog mode calls the value of the variable verilog-mode-hook with
no args, if that value is non-nil.
Other useful functions are:
\\[verilog-complete-word]\t-complete word with appropriate possibilities 
   (functions, verilog keywords...)
\\[verilog-comment-region]\t- Put marked area in a comment, fixing 
   nested comments.
\\[verilog-uncomment-region]\t- Uncomment an area commented with \
\\[verilog-comment-region].
\\[verilog-insert-block]\t- insert begin ... end;
\\[verilog-star-comment]\t- insert /* ... */
\\[verilog-mark-defun]\t- Mark function.
\\[verilog-beg-of-defun]\t- Move to beginning of current function.
\\[verilog-end-of-defun]\t- Move to end of current function.
\\[verilog-label-be]\t- Label matching begin ... end, fork ... join 
  and case ... endcase statements;
"
  (interactive)
  (kill-all-local-variables)
  (use-local-map verilog-mode-map)
  (setq major-mode 'verilog-mode)
  (setq mode-name "Verilog")
  (setq local-abbrev-table verilog-mode-abbrev-table)
  (set-syntax-table verilog-mode-syntax-table)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'verilog-indent-line)
  (setq comment-indent-function 'verilog-comment-indent)
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments nil)
  (make-local-variable 'comment-start)
  (make-local-variable 'comment-end)
  (make-local-variable 'comment-multi-line)
  (make-local-variable 'comment-start-skip)
  (setq comment-start "// "
	comment-end ""
	comment-start-skip "/\\*+ *\\|// *"
	comment-multi-line nil)
  ;; Setting up things for font-lock 
  (if (string-match "XEmacs" emacs-version) 
      (progn 
        (if (and current-menubar 
                 (not (assoc "Verilog" current-menubar))) 
            (progn 
              (set-buffer-menubar (copy-sequence current-menubar)) 
              (add-submenu nil verilog-xemacs-menu))) ))
  ;; Stuff for GNU emacs
  (make-local-variable 'font-lock-defaults) 
  (setq font-lock-defaults  
	'((verilog-font-lock-keywords verilog-font-lock-keywords-1 
				      verilog-font-lock-keywords-2 
				      verilog-font-lock-keywords-3 
				      verilog-font-lock-keywords-4) 
	  nil t)) 

  ;; Tell imenu how to handle verilog. 
  (make-local-variable 'imenu-generic-expression) 
  (setq imenu-generic-expression verilog-imenu-generic-expression) 
  ;; End GNU emacs stuff
  (run-hooks 'verilog-mode-hook))


;;;
;;;  Electric functions
;;;
(defun electric-verilog-terminate-line (&optional arg)
  "Terminate line and indent next line."
  (interactive)
  ;; before that see if we are in a comment
  (let ((state 
	 (save-excursion
	   (parse-partial-sexp (point-min) (point)))))
    (cond
     ((nth 7 state)			; Inside // comment
      (if (eolp)
	  (progn
	    (delete-horizontal-space)
	    (newline))
	(progn 
	  (newline)
	  (insert-string "// ")
	  (beginning-of-line)
	  ))
      (verilog-indent-line)
      )
     ((nth 4 state)			; Inside any comment (hence /**/)
      (newline)
      (verilog-more-comment)
      )
     ((eolp)
       ;; First, check if current line should be indented
       (if (save-excursion 
             (delete-horizontal-space)
	     (beginning-of-line)
	     (skip-chars-forward " \t")
	     (if (looking-at verilog-autoindent-lines-re)
		 (let ((indent-str (verilog-indent-line)))
		   ;; Maybe we should set some endcomments
		   (if verilog-auto-endcomments
		       (verilog-set-auto-endcomments indent-str arg))
		   (end-of-line)
		   (delete-horizontal-space)
		   (if arg
		       ()
		     (newline))
		   nil)
	       (progn
		 (end-of-line)
		 (delete-horizontal-space)
		 't
		 )))
	   (newline)
	 (forward-line 1)
	 )
       ;; Indent next line
       (if verilog-auto-indent-on-newline
	   (verilog-indent-line))
       )
     (t
      (newline)
      )
     )
    )
  )
  
(defun electric-verilog-semi ()
  "Insert `;' character and reindent the line."
  (interactive)
  (insert last-command-char)
  (if (verilog-in-comment-or-string-p)
      () 
    (save-excursion
      (beginning-of-line)
      (verilog-forward-ws&directives)
      (verilog-indent-line))
    (if (and verilog-auto-newline
	     (= 0 (verilog-parenthesis-depth)))
	(electric-verilog-terminate-line))))

(defun electric-verilog-semi-with-comment ()
  "Insert `;' character, reindent the line and indent for comment."
  (interactive)
  (insert "\;")
  (save-excursion
    (beginning-of-line)
    (verilog-indent-line))
  (indent-for-comment))

(defun electric-verilog-colon ()
  "Insert `:' and do all indentions except line indent on this line."
  (interactive)
  (insert last-command-char)
  ;; Do nothing if within string.
  (if (or
       (verilog-within-string)
       (not (verilog-in-case-region-p)))
      ()
    (save-excursion
      (let ((p (point))
	    (lim (progn (verilog-beg-of-statement) (point))))
	(goto-char p)
	(verilog-backward-case-item lim)
	(verilog-indent-line)))
;;    (let ((verilog-tab-always-indent nil))
;;      (verilog-indent-line))
    )
  )

(defun electric-verilog-equal ()
  "Insert `=', and do indention if within block."
  (interactive)
  (insert last-command-char)
;; Could auto line up expressions, but not yet
;;  (if (eq (car (verilog-calculate-indent)) 'block)
;;      (let ((verilog-tab-always-indent nil))
;;	(verilog-indent-command)))
)


(defun electric-verilog-tick ()
  "Insert back-tick, and indent to coulmn 0 if this is a CPP directive."
  (interactive)
  (insert last-command-char)
  (if (save-excursion 
	(beginning-of-line) 
	(looking-at verilog-directive-re-1))
      (save-excursion (beginning-of-line)
		      (delete-horizontal-space))))

(defun electric-verilog-tab ()
  "Function called when TAB is pressed in Verilog mode."
  (interactive)
  ;; If verilog-tab-always-indent, indent the beginning of the line.
  (if verilog-tab-always-indent
      (let* (
	     (boi-point 
	      (save-excursion
		(beginning-of-line)
		(skip-chars-forward " \t")
		(let (type state )
		  (setq type (verilog-indent-line))
		  (setq state (car type))
		  (cond
		   ((eq state 'block)
		    (if (looking-at verilog-behavioral-block-beg-re )
			(error 
			 (concat 
			  "The reserved word \""
			  (buffer-substring (match-beginning 0) (match-end 0))
			  "\" must be at the behavioral level!"))))
		   ))
		(back-to-indentation)
		(point))))
        (if (< (point) boi-point)
            (back-to-indentation)))
    (progn (insert "\t"))
    )
  )



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
  (save-excursion
    (newline)
    (insert " */"))
  (newline)
  (insert " * "))

(defun verilog-mark-defun ()
  "Mark the current verilog function (or procedure).
This puts the mark at the end, and point at the beginning."
  (interactive)
  (push-mark (point))
  (verilog-end-of-defun)
  (push-mark (point))
  (verilog-beg-of-defun)
  (zmacs-activate-region))

(defun verilog-comment-region (start end)
  "Put the region into a Verilog comment.
The comments that are in this area are \"deformed\":
`*)' becomes `!(*' and `}' becomes `!{'.
These deformed comments are returned to normal if you use
\\[verilog-uncomment-region] to undo the commenting.

The commented area starts with `verilog-exclude-str-start', and ends with
`verilog-include-str-end'.  But if you change these variables,
\\[verilog-uncomment-region] won't recognize the comments."
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
	(replace-match "*-/" t t)))
    (save-excursion
      (let ((s+1 (1+ start)))
	(while (re-search-backward "/\\*" s+1 t)
	  (replace-match "/-*" t t))))
    )
)

(defun verilog-uncomment-region ()
  "Uncomment a commented area; change deformed comments back to normal.
This command does nothing if the pointer is not in a commented
area.  See also `verilog-comment-region'."
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
	    (while (re-search-backward "\\*-/" start t)
	      (replace-match "*/" t t)))
	  (save-excursion
	    (while (re-search-backward "/-\\*" start t)
	      (replace-match "/*" t t)))
	  ;; Remove startcomment
	  (goto-char start)
	  (beginning-of-line)
	  (let ((pos (point)))
	    (end-of-line)
	    (delete-region pos (1+ (point)))))))))

(defun verilog-beg-of-defun ()
  "Move backward to the beginning of the current function or procedure."
  (interactive)
  (verilog-re-search-backward verilog-defun-re nil 'move)
  )
(defun verilog-end-of-defun ()
  (interactive)
  (verilog-re-search-forward verilog-end-defun-re nil 'move)
  )

(defun verilog-label-be (&optional arg)
  "Label matching begin ... end, fork ... join and case ... endcase
  statements in this module; With argument, first kill any existing
  labels."
  (interactive)
  (let ((cnt 0)
	(oldpos (point))
	(b (progn 
	     (verilog-beg-of-defun) 
	     (point-marker)))
	(e (progn 
	     (verilog-end-of-defun) 
	     (point-marker)))
	)
    (goto-char (marker-position b))
    (if (> (- e b) 200)
	(message  "Relabeling module..."))
    (while (and
	    (> (marker-position e) (point))
	    (verilog-re-search-forward 
	     (concat 
	      "\\<end\\(\\(function\\)\\|\\(task\\)\\|\\(module\\)\\|"
	      "\\(primitive\\)\\|\\(case\\)\\)?\\>"
	      "\\|\\(`endif\\)\\|\\(`else\\)")
	     nil 'move))
      (goto-char (match-beginning 0))
      (let ((indent-str (verilog-indent-line)))
	(verilog-set-auto-endcomments indent-str 't)
	(end-of-line)
	(delete-horizontal-space)
	)
      (setq cnt (1+ cnt))
      (if (= 9 (% cnt 10))
	  (message "%d..." cnt))
      )
    (goto-char oldpos)
    (if (or
	 (> (- e b) 200)
	 (> cnt 20))
	(message  "%d lines autocommented" cnt))
    )
  )
(defun verilog-beg-of-statement ()
  "Move backward to beginning of statement"
  (interactive)
  (while (save-excursion 
	   (and
	    (not (looking-at verilog-complete-reg))
	    (verilog-backward-syntactic-ws)
	    (not (or (bolp) (= (preceding-char) ?\;)))
	    )
	   )
    (skip-chars-backward " \t")
    (verilog-backward-token))
  (let ((last (point)))
    (while (progn
	     (setq last (point))
	     (and (not (looking-at verilog-complete-reg))
		  (verilog-continued-line))))
    (goto-char last)
    (verilog-forward-syntactic-ws)
    )
  )

(defun verilog-beg-of-statement-1 ()
  "Move backward to beginning of statement"
  (interactive)
  (let ((pt (point)))
    
    (while (and (not (looking-at verilog-complete-reg))
		(setq pt (point))
		(verilog-backward-token)
		(setq pt (point))
		(verilog-backward-syntactic-ws)
		(not (bolp))
		(not (= (preceding-char) ?\;)))
      )
    (goto-char pt)
    (while (progn
	     (setq pt (point))
	     (and (not (looking-at verilog-complete-reg))
		  (not (= (preceding-char) ?\;))
		  (verilog-continued-line))))
    (goto-char pt)
    (verilog-forward-syntactic-ws)
    )
  )
(defun verilog-end-of-statement ()
  "Move forward to end of current statement."
  (interactive)
  (let ((nest 0) pos)
    (or (looking-at verilog-beg-block-re)
	;; Skip to end of statement
	(setq pos (catch 'found
		    (while t
		      (forward-sexp 1)
		      (verilog-skip-forward-comment-or-string)
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
	    (verilog-re-search-forward verilog-end-statement-re nil 'move)
	    (setq nest (if (match-end 1) 
			   (1+ nest)
			 (1- nest)))
	    (cond ((eobp)
		   (throw 'found (point)))
		  ((= 0 nest)
		   (throw 'found (verilog-end-of-statement))))))
      pos)))
(defun verilog-in-case-region-p ()
  "Return TRUE if in a case region: more specifically, point @ in the
  line foo : @ begin"
  (interactive)
  (save-excursion
    (if (and 
	 (progn (verilog-forward-syntactic-ws)	
		(looking-at "\\<begin\\>"))
	 (progn (verilog-backward-syntactic-ws)	
		(= (preceding-char) ?\:)))
	(catch 'found
	  (let ((nest 1))
	    (while t
	      (verilog-re-search-backward 
	       (concat "\\(\\<module\\>\\)\\|\\(\\<case[xz]?\\>[^:]\\)\\|"
		       "\\(\\<endcase\\>\\)\\>")
	       nil 'move)
	      (cond
	       ((match-end 3)
		(setq nest (1+ nest)))
	       ((match-end 2)
		(if (= nest 1)
		(throw 'found 1))
		(setq nest (1- nest))
		)
	       ( t
		 (throw 'found (= nest 0)))
	       )
	      )
	    )
	  )
      nil)
    )
  )
(defun verilog-in-fork-region-p ()
  "Return true if between a fork and join"
  (interactive)
  (let 
      ( (lim (save-excursion (verilog-beg-of-defun)  (point)))
	(nest 1)
	)
    (save-excursion
      (while (and 
	      (/= nest 0)
	      (verilog-re-search-backward "\\<\\(fork\\)\\|\\(join\\)\\>" lim 'move)
	      (cond 
	       ((match-end 1) ; fork
		(setq nest (1- nest)))
	       ((match-end 2) ; join
		(setq nest (1+ nest)))
	       )
	      )
	)
      )
    (= nest 0) )				; return nest
  )
(defun verilog-backward-case-item (lim)
  "Skip backward to nearest enclosing case item"
  (interactive)
  (let (
	(str 'nil)
	(lim1 
	 (progn 
	   (save-excursion 
	     (verilog-re-search-backward verilog-endcomment-reason-re 
					 lim 'move)
	     (point)))))
    ;; Try to find the real :
    (if (save-excursion (search-backward ":" lim1 t))
	(let ((colon 0)
	      b e )
	  (while 
	      (and 
	       (< colon 1)
	       (verilog-re-search-backward "\\(\\[\\)\\|\\(\\]\\)\\|\\(:\\)" 
					   lim1 'move))
	    (cond 
	     ((match-end 1) ;; [
	      (setq colon (1+ colon))
	      (if (>= colon 0)
		  (error "unbalanced [")))
	     ((match-end 2) ;; ]
	      (setq colon (1- colon)))
	     
	     ((match-end 3) ;; :
	      (setq colon (1+ colon)))
	     
	     )
	    )
	  ;; Skip back to begining of case item
	  (skip-chars-backward "\t ")
	  (verilog-skip-backward-comment-or-string)
	  (setq e (point))
	  (setq b 
		(progn
		  (if 
		      (verilog-re-search-backward 
		       "\\<\\(case[zx]?\\)\\>\\|;\\|\\<end\\>" nil 'move)
		      (progn
			(cond 
			 ((match-end 1)
			  (goto-char (match-end 1))
			  (verilog-forward-ws&directives)
			  (if (looking-at "(")
			      (progn
				(forward-sexp)
				(verilog-forward-ws&directives)
				))
			  (point))
			 (t
			  (goto-char (match-end 0))
			  (verilog-forward-ws&directives)
			  (point))
			 ))
		    (error "Malformed case item")
		    )
		  )
		)
	  (setq str (buffer-substring b e))
	  (if 
	      (setq e 
		    (string-match 
		     "[ \t]*\\(\\(\n\\)\\|\\(//\\)\\|\\(/\\*\\)\\)" str))
	      (setq str (concat (substring str 0 e) "...")))
	  str)
      'nil)
    )
  )


;;;
;;; Other functions
;;;

(defun kill-existing-comment ()
  "kill autocomment on this line"
  (save-excursion 
    (let* (
	   (e (progn
		(end-of-line)
		(point)))
	   (b (progn 
		(beginning-of-line)
		(search-forward "//" e t))))
      (if b
	  (delete-region (- b 2) e))
      )
    )
  )

(defun verilog-set-auto-endcomments (indent-str kill-existing-comment)
  "Insert `// case: 7 ' or `// NAME ' on this line if appropriate.
Insert `// case expr ' if this line ends a case block.  
Insert `// ifdef FOO ' if this line ends code conditional on FOO.
Insert `// NAME ' if this line ends a module or primitive named NAME."
  (save-excursion
    (cond 
     (; Comment close preprocessor directives
      (and 
       (looking-at "\\(`endif\\)\\|\\(`else\\)")
       (or  kill-existing-comment	
	    (not (save-excursion
		   (end-of-line)
		   (search-backward "//" (verilog-get-beg-of-line) t)))))
      (let ( (reg "\\(`else\\>\\)\\|\\(`ifdef\\>\\)\\|\\(`endif\\>\\)")
	     (nest 1)
	     b e 
	     (else (if (match-end 2)
		       1
		     0))
	     )
	(end-of-line)
	(if kill-existing-comment
	    (kill-existing-comment))
	(delete-horizontal-space)
	(save-excursion
	  (backward-sexp 1)
	  (while (and (/= nest 0)
		      (verilog-re-search-backward reg nil 'move))
	    (cond 
	     ((match-end 1) ; `else
	      (if (= nest 1)
		  (setq else 1)))
	     ((match-end 2) ; `ifdef
	      (setq nest (1- nest)))
	     ((match-end 3) ; `endif
	      (setq nest (1+ nest)))
	     ))
	  (if (match-end 0)
	      (setq b (progn 
			(skip-chars-forward "^ \t")
			(verilog-forward-syntactic-ws)
			(point))
		    e (progn
			(skip-chars-forward "a-zA-Z0-9_")
			(point)
			))))
	(if b
	    (if (> (- (point) b) verilog-minimum-comment-distance)
		(insert (concat (if 
				    (= else 0)
				    " // ifdef " 
				  " // !ifdef ")
				(buffer-substring b e))))
	  (progn
	    (insert " // unmatched `endif")
	    (ding 't))
	  )))
     
     (; Comment close case/function/task/module and named block
      (and (looking-at "\\<end")
	   (or kill-existing-comment
	       (not (save-excursion
		      (end-of-line)
		      (search-backward "//" (verilog-get-beg-of-line) t)))))
      (let ((type (car indent-str)))
	(if (eq type 'declaration)
	    ()
	  (if 
	      (looking-at verilog-enders-re)
	      (cond
	       (;- This is a case block; search back for the start of this case
		(match-end 1)
		
		(let ((err 't)
		      (str "UNMATCHED!!"))
		  (save-excursion
		    (verilog-leap-to-head)
		    (if (match-end 0)
			(progn
			  (goto-char (match-end 1))
			  (setq str (concat (buffer-substring (match-beginning 1) (match-end 1))
					    (verilog-get-expr)))
			  (setq err nil))))
		  (end-of-line)
		  (if kill-existing-comment
		      (kill-existing-comment))
		  (delete-horizontal-space)
		  (insert (concat " // " str ))
		  (if err (ding 't))
		  ))
	       
	       (;- This is a begin..end block
		(match-end 2)
		(let ((str " // UNMATCHED !!")
		      (err 't)
		      (here (point))
		      there
		      cntx
		      )
		  (save-excursion
		    (verilog-leap-to-head)
		    (setq there (point))
		    (if (not (match-end 0))
			(progn
			  (goto-char here)
			  (end-of-line)
			  (if kill-existing-comment
			      (kill-existing-comment))
			  (delete-horizontal-space)
			  (insert str)
			  (ding 't)			  
			  )
		      (let ( sp 
			    (lim (save-excursion (verilog-beg-of-defun) (point)))
			    (here (point))
			    )
			(cond
			 (;-- handle named block differently
			  (looking-at verilog-named-block-re)
			  (search-forward ":")
			  (setq there (point))
			  (setq str (verilog-get-expr))
			  (setq err nil)
			  (setq str (concat " // block: " str )))
			 
			 ((verilog-in-case-region-p) ;-- handle case item differently
			  (goto-char here)
			  (setq str (verilog-backward-case-item lim))
			  (setq there (point))
			  (setq err nil)
			  (setq str (concat " // case: " str ))
			  )
			 (;- try to find "reason" for this begin
			  (cond 
			   (;
			    (eq here (progn 
				       (verilog-backward-token)
				       (verilog-beg-of-statement) 
				       (point)))
			    (setq err nil)
			    (setq str ""))
			   ((looking-at verilog-endcomment-reason-re)
			    (setq there (match-end 0))
			    (setq cntx (concat 
					(buffer-substring (match-beginning 0) (match-end 0)) " "))
			    (cond
			     (;
			      (match-end 2)
			      (setq err nil)
			      (save-excursion
				(goto-char sp)
				(if (and (verilog-continued-line)
					 (looking-at "\\<repeat\\>\\|\\<wait\\>\\|\\<always\\>"))
				    (progn
				      (goto-char (match-end 0))
				      (setq there (point))
				      (setq str 
					    (concat " // "
						    (buffer-substring (match-beginning 0) (match-end 0)) " "
						    (verilog-get-expr))))
				  (setq str "")		  
				  )
				)
			      )
			     (;- else 
			      (match-end 4)
			      (let ((nest 0)
				    ( reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<if\\>\\)")
				    )
				(catch 'skip
				  (while (verilog-re-search-backward reg nil 'move)
				    (cond 
				     ((match-end 1) ; begin
				      (setq nest (1- nest)))
				     ((match-end 2)                       ; end
				      (setq nest (1+ nest)))
				     ((match-end 3)
				      (if (= 0 nest)
					  (progn
					    (goto-char (match-end 0))
					    (setq there (point))
					    (setq err nil)
					    (setq str (verilog-get-expr))
					    (setq str (concat " // else: !if" str ))
					    (throw 'skip 1))
					)))
				    )
				  )
				)
			      )
			     (;- end else 
			      (match-end 5)
			      (goto-char there)
			      (let ((nest 0)
				    ( reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<if\\>\\)")
				    )
				(catch 'skip
				  (while (verilog-re-search-backward reg nil 'move)
				    (cond 
				     ((match-end 1) ; begin
				      (setq nest (1- nest)))
				     ((match-end 2)                       ; end
				      (setq nest (1+ nest)))
				     ((match-end 3)
				      (if (= 0 nest)
					  (progn
					    (goto-char (match-end 0))
					    (setq there (point))
					    (setq err nil)
					    (setq str (verilog-get-expr))
					    (setq str (concat " // else: !if" str ))
					    (throw 'skip 1))
					)))
				    )
				  )
				)
			      )

			     (;- task/function/initial et cetera
			      t
			      (match-end 0)
			      (goto-char (match-end 0))
			      (setq there (point))
			      (setq err nil)
			      (setq str (verilog-get-expr))
			      (setq str (concat " // " cntx str )))
			     
			     (;-- otherwise...
			      (setq str " // auto-endcomment confused ")
			      )
			     )
			    )
			   ((and
			     (verilog-in-case-region-p) ;-- handle case item differently
			     (progn
			       (setq there (point))			       
			       (goto-char here)
			       (setq str (verilog-backward-case-item lim))))
			    (setq err nil)
			    (setq str (concat " // case: " str ))
			    )
			   ((verilog-in-fork-region-p)
			    (setq err nil)
			    (setq str " // fork branch" )) 
			   )
			  )
			 )
			)
		      (goto-char here)
		      (end-of-line)
		      (if kill-existing-comment
			  (kill-existing-comment))
		      (delete-horizontal-space)
		      (if (or err
			      (> (- here there) verilog-minimum-comment-distance))
			  (insert str))
		      (if err (ding 't))
		      )
		    )
		  )
		)


	       (;- this is end{function,task,module}
		t 
		(let (string reg (width nil))
		  (end-of-line)
		  (if kill-existing-comment
		      (kill-existing-comment))
		  (delete-horizontal-space)
		  (backward-sexp)
		  (cond 
		   ((match-end 5) 
		    (setq reg "\\(\\<function\\>\\)\\|\\(\\<\\(endfunction\\|task\\|\\(macro\\)?module\\|primitive\\)\\>\\)")
		    (setq width "\\([ \t]*\\[[^]]*\\]\\)?")
		    )
		   ((match-end 6) 
		    (setq reg "\\(\\<task\\>\\)\\|\\(\\<\\(endtask\\|function\\|\\(macro\\)?module\\|primitive\\)\\>\\)"))
		   ((match-end 7) 
		    (setq reg "\\(\\<\\(macro\\)?module\\>\\)\\|\\<endmodule\\>"))
		   ((match-end 8) 
		    (setq reg "\\(\\<primitive\\>\\)\\|\\(\\<\\(endprimitive\\|function\\|task\\|\\(macro\\)?module\\)\\>\\)"))
		   )
		  (let (b e)
		    (save-excursion
		      (verilog-re-search-backward reg nil 'move)
		      (cond 
		       ((match-end 1)
			(setq b (progn 
				  (skip-chars-forward "^ \t")
				  (verilog-forward-ws&directives)
				  (if (and width (looking-at width))
				      (progn
					(goto-char (match-end 0))
					(verilog-forward-ws&directives)
					))
				  (point))
			      e (progn 
				  (skip-chars-forward "a-zA-Z0-9_")
				  (point)))
			(setq string (buffer-substring b e)))
		       (t
			(ding 't)
			(setq string "unmactched end(function|task|module|primitive)")))))
		  (end-of-line)
		  (insert (concat " // " string )))
		)
	       )
	    )
	  )
	)
      )
     )
    )
  )

(defun verilog-get-expr()
  "Grab expression at point, e.g, case ( a | b & (c ^d))"
  (let* ((b (progn 
	      (verilog-forward-syntactic-ws)
	      (skip-chars-forward " \t")
	      (point)))
	 (e (let ((par 1)) 
	      (cond
	       ((looking-at "(")
		(forward-char 1)
		(while (and (/= par 0) 
			    (verilog-re-search-forward "\\((\\)\\|\\()\\)" nil 'move))
		  (cond
		   ((match-end 1)
		    (setq par (1+ par)))
		   ((match-end 2)
		    (setq par (1- par)))))
		(point))
	       ((looking-at "\\[")
		(forward-char 1)
		(while (and (/= par 0) 
			    (verilog-re-search-forward "\\(\\[\\)\\|\\(\\]\\)" nil 'move))
		  (cond
		   ((match-end 1)
		    (setq par (1+ par)))
		   ((match-end 2)
		    (setq par (1- par)))))
		(verilog-forward-syntactic-ws)
		(skip-chars-forward "^ \t\n")		
		(point))
	       ((looking-at "/[/\\*]")
		b)
	       ('t
		(skip-chars-forward "^: \t\n")
		(point)
		))))
	 (str (buffer-substring b e)))
    (if (setq e (string-match "[ \t]*\\(\\(\n\\)\\|\\(//\\)\\|\\(/\\*\\)\\)" str))
	(setq str (concat (substring str 0 e) "...")))
    str)
  )


;;;
;;; Indentation
;;;
(defconst verilog-indent-alist
  '((block       . (+ ind verilog-indent-level))
    (case        . (+ ind verilog-case-indent))
    (cparenexp   . (+ ind verilog-indent-level))
    (cexp        . (+ ind verilog-cexp-indent))
    (defun       . verilog-indent-level-module)
    (declaration . verilog-indent-level-declaration)
    (tf          . verilog-indent-level)
    (behavioral  . (+ verilog-indent-level-behavioral verilog-indent-level-module))
    (statement   . ind)
    (cpp         . 0)
    (comment     . (verilog-comment-indent))
    (unknown     . 3) 
    (string      . 0)))

(defun verilog-calculate-indent ()
  "Calculate the indent of the current Verilog line, through examination
of previous lines.  Once a line is found that is definitive as to the
type of the current line, return that lines' indent level and it's
type. Return a list of two elements: (INDENT-TYPE INDENT-LEVEL)."
  (save-excursion
    (let* ((starting_position (point))
	   (par 0) 
	   (begin (looking-at "[ \t]*begin\\>"))
	   (type (catch 'nesting
		   ;; Keep working backwards until we can figure out
		   ;; what type of statement this is.
		   ;; Basically we need to figure out 
		   ;; 1) if this is a continuation of the previous line;
		   ;; 2) are we in a block scope (begin..end)
		   
		   ;; if we are in a comment, done.
		   (if (verilog-in-star-comment-p)   (throw 'nesting 'comment))

		   ;; if we are in a parenthesized list, done.
		   (if (verilog-in-paren) (progn (setq par 1) (throw 'nesting 'block)))

		   ;; See if we are continuing a previous line
		   (while t
		     ;; trap out if we crawl off the top of the buffer
		     (if (bobp) (throw 'nesting 'cpp))

		     (if (verilog-continued-line-1)
			 (let ((sp (point)))
			   (if (and
				(not (looking-at verilog-complete-reg))
				(verilog-continued-line-1))
			       (progn (goto-char sp)
				      (throw 'nesting 'cexp))
			     (goto-char sp))
			   
			   (if (and begin
				    (not verilog-indent-begin-after-if)
				    (looking-at verilog-no-indent-begin-re))
			       (throw 'nesting 'statement)
			     (progn
			       (throw 'nesting 'cexp)
			       )
			     ))

		       ;; not a continued line
		       (goto-char starting_position))

		     (if (looking-at "\\<else\\>")
			 ;; search back for governing if, striding across begin..end pairs
			 ;; appropriately
			 (let ((elsec 1))
			   (while (verilog-re-search-backward verilog-ends-re nil 'move)
			     (cond 
			      ((match-end 1) ; else, we're in deep
			       (setq elsec (1+ elsec))				 
			       )
			      ((match-end 2) ; found it
			       (setq elsec (1- elsec))
			       (if (= 0 elsec)
				   (if verilog-align-ifelse
				       (throw 'nesting 'statement)
				     (progn ;; back up to first word on this line
				       (beginning-of-line)
				       (verilog-forward-syntactic-ws)
				       (throw 'nesting 'statement))
				     )))
			      (t ; endblock
				; try to leap back to matching outward block by striding across
				; indent level changing tokens then immediately
				; previous line governs indentation.
			       (let ((reg)(nest 1))
;;				 (looking-at verilog-end-block-re-1);; end|join|endcase|endtable|endspecify
				 (cond 
				  ((match-end 3) ; end
				   ;; Search back for matching begin
				   (setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" )
				   )
				  ((match-end 4) ; endcase
				   ;; Search back for matching case
				   (setq reg "\\(\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" )
				   )
				  ((match-end 5) ; join
				   ;; Search back for matching fork
				   (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" )
				   )
				  ((match-end 6) ; endtable
				   ;; Search back for matching table
				   (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" )
				   )
				  ((match-end 7) ; endspecify
				   ;; Search back for matching specify
				   (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" )
				   )
				  ((match-end 8) ; endfunction
				   ;; Search back for matching function
				   (setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" )
				   )
				  ((match-end 9) ; endtask
				   ;; Search back for matching task
				   (setq reg "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)" )
				   )
				  )
				 (catch 'skip
				   (while (verilog-re-search-backward reg nil 'move)
				     (cond 
				      ((match-end 1) ; begin
				       (setq nest (1- nest))
				       (if (= 0 nest)
					   (throw 'skip 1)))
				      ((match-end 2) ; end
				       (setq nest (1+ nest)))))
				   )
				 )
			       )
			      )
			     )
			   )
		       )
		     (throw 'nesting (verilog-calc-1))
		     )
		   )
		 )
	   )
      ;; Return type of block and indent level.
      (if (not type)
	  (setq type 'cpp))
      (if (> par 0)			; Unclosed Parenthesis 
	  (list 'cparenexp par)
	(cond
	  ((eq type 'case)
	   (list type (verilog-case-indent-level)))
	  ((eq type 'statement)
	   (list type (current-column)))
	  ((eq type 'defun)
	   (list type 0))
	  (t
	   (list type (verilog-indent-level)))))
      )
    )
  )
(defun verilog-calc-1 ()
  ""
  (catch 'nesting
    (while (verilog-re-search-backward verilog-indent-re nil 'move)
      (cond 
       ((looking-at verilog-behavioral-level-re)
	(throw 'nesting 'behavioral))
			
       ((looking-at verilog-beg-block-re-1)
	(cond
	 ((match-end 2)  (throw 'nesting 'case))
	 (t              (throw 'nesting 'block))))

       ((looking-at verilog-end-block-re)
	(verilog-leap-to-head)
	(if (verilog-in-case-region-p)
	    (progn
	      (verilog-leap-to-case-head)
	      (if (looking-at verilog-case-re)
		  (throw 'nesting 'case))
	      )))
			
       ((looking-at verilog-defun-level-re)
	(throw 'nesting 'defun)) 

       ((looking-at verilog-cpp-level-re)
	(throw 'nesting 'cpp))

       ((bobp) 
	(throw 'nesting 'cpp))
       )
      )
    )
  )

(defun verilog-leap-to-case-head () ""
  (let ((nest 1))
    (while (/= 0 nest)
      (verilog-re-search-backward "\\(\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" nil 'move)
      (cond 
       ((match-end 1)
	(setq nest (1- nest)))
       ((match-end 2)
	(setq nest (1+ nest)))
       ((bobp)
	(ding 't)
	(setq nest 0))
       )
      )
    )
  )

(defun verilog-leap-to-head () 
  "Move point to the head of this block; jump from end to matching begin,
   from endcase to matching case, and so on."
  (let (reg 
	snest
	(nest 1))
    (cond 
     ((looking-at "\\<end\\>")
      ;; Search back for matching begin
      (setq reg (concat "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|" 
			"\\(\\<endcase\\>\\)\\|\\(\\<join\\>\\)" )))
     
     ((looking-at "\\<endcase\\>")
      ;; Search back for matching case
      (setq reg "\\(\\<case[xz]?\\>\\)\\|\\(\\<endcase\\>\\)" )
      )
     ((looking-at "\\<join\\>")
      ;; Search back for matching fork
      (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" )
      )
     ((looking-at "\\<endtable\\>")
      ;; Search back for matching table
      (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" )
      )
     ((looking-at "\\<endspecify\\>")
      ;; Search back for matching specify
      (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" )
      )
     ((looking-at "\\<endfunction\\>")
      ;; Search back for matching function
      (setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" )
      )
     ((looking-at "\\<endtask\\>")
      ;; Search back for matching task
      (setq reg "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)" )
      )
     )
    (catch 'skip
      (let (sreg)
	(while (verilog-re-search-backward reg nil 'move)
	  (cond 
	   ((match-end 1) ; begin
	    (setq nest (1- nest))
	    (if (= 0 nest)
		;; Now previous line describes syntax
		(throw 'skip 1))
	    (if (and snest
		     (= snest nest))
		(setq reg sreg))
	    )
	   ((match-end 2) ; end
	    (setq nest (1+ nest))
	    )
	   ((match-end 3)
	    ;; endcase, jump to case
	    (setq snest nest)
	    (setq nest (1+ nest))
	    (setq sreg reg)
	    (setq reg "\\(\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" )
	    )
	   ((match-end 4)
	    ;; join, jump to fork
	    (setq snest nest)
	    (setq nest (1+ nest))
	    (setq sreg reg)
	    (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" )
	    )
	   )
	  )
	)
      )
    )
  )

(defun verilog-continued-line-1 ()
  "Return true if this is a continued line.
   Set point to where line starts"
  (let ((continued 't))
    (if (eq 0 (forward-line -1))
	(progn
	  (end-of-line)
	  (verilog-backward-ws&directives)
	  (if (bobp)
	      (setq continued nil)
	    (setq continued (verilog-backward-token))
	    )
	  )
      (setq continued nil)
      )
    continued)
  )

(defun verilog-continued-line ()
  "Return true if this is a continued line.
   Set point to where line starts"
  (let ((continued 't))
    (if (eq 0 (forward-line -1))
	(progn
	  (end-of-line)
	  (verilog-backward-ws&directives)
	  (if (bobp)
	      (setq continued nil)
	    (while (and continued
			(save-excursion
			  (skip-chars-backward " \t") 
			  (not (bolp))))
	    (setq continued (verilog-backward-token))
	      ) ;; while
	    )
	  )
      (setq continued nil)
      )
    continued)
  )

(defun verilog-backward-token ()
  "step backward token, returning true if we are now at an end of line token"
  (verilog-backward-syntactic-ws)
  (cond 
   ((bolp)
    nil)
   (;-- Anything ending in a ; is complete
    (= (preceding-char) ?\;)
    nil)
   (;-- Could be 'case (foo)' or 'always @(bar)' which is complete
    (= (preceding-char) ?\))
    (progn
      (backward-char)
      (backward-up-list 1)
      (verilog-backward-syntactic-ws)
      (forward-word -1)
      (not (looking-at "\\<case[xz]?\\>[^:]"))))
   (;-- any of begin|initial|while are complete statements; 'begin : foo' is also complete
    t
    (forward-word -1)
    (cond 
     ( 
      (looking-at "\\(else\\)\\|\\(initial\\>\\)\\|\\(always\\>\\)")  
      t)
     ( 
      (looking-at verilog-indent-reg) 
      nil)
     (t
      (let 
	  ((back (point)))
	(verilog-backward-syntactic-ws)
	(cond
	 ((= (preceding-char) ?\:)
	  (backward-char)
	  (verilog-backward-syntactic-ws)
	  (backward-sexp)
	  (if (looking-at "begin")
	      nil
	    t)
	  )
	 ((= (preceding-char) ?\#)
	  (backward-char)
	  t)
	 ((= (preceding-char) ?\`)
	  (backward-char)
	  t)
	 
	 (t
	  (goto-char back)
	  t)
	 )
	)
      )
     )
    )
   )
)

(defun verilog-backward-syntactic-ws (&optional lim)
  ;; Backward skip over syntactic whitespace for Emacs 19.
  (save-restriction
    (let* ((lim (or lim (point-min)))
	   (here lim)
	   bol
	   )
      (if (< lim (point))
	  (progn
	    (narrow-to-region lim (point))
	    (while (/= here (point))
	      (setq here (point))
	      (forward-comment (-(buffer-size)))
	      (save-excursion
		(setq bol (progn (beginning-of-line) (point))))
	      (search-backward "//" bol t)
	      )))
      ))
  t)

(defun verilog-forward-syntactic-ws (&optional lim)
  ;; forward skip over syntactic whitespace for Emacs 19.
  (save-restriction
    (let* ((lim (or lim (point-max)))
	   (here lim)
	   )
      (if (> lim (point))
	  (progn
	    (narrow-to-region (point) lim)
	    (while (/= here (point))
	      (setq here (point))
	      (forward-comment (buffer-size))
	      )))
      )))

(defun verilog-backward-ws&directives (&optional lim)
  ;; Backward skip over syntactic whitespace and compiler directives for Emacs 19.
  (save-restriction
    (let* ((lim (or lim (point-min)))
	   (here lim)
	   jump
	   )
      (if (< lim (point))
	  (progn
	    (let ((state 
		   (save-excursion
		     (parse-partial-sexp (point-min) (point)))))
	      (cond
	       ((nth 4 state) ;; in /* */ comment
		(verilog-re-search-backward "/\*" nil 'move)
		)
	       ((nth 7 state) ;; in // comment
		(verilog-re-search-backward "//" nil 'move)
		)))
	    (narrow-to-region lim (point))
	    (while (/= here (point))
	      (setq here (point))
	      (forward-comment (-(buffer-size)))
	      (save-excursion
		(beginning-of-line)
		(if (looking-at verilog-directive-re-1)
		    (setq jump t)
		  (setq jump nil)))
	      (if jump
		  (beginning-of-line))
	      )))
      )))

(defun verilog-forward-ws&directives (&optional lim)
  ;; forward skip over syntactic whitespace and compiler directives for Emacs 19.
  (save-restriction
    (let* ((lim (or lim (point-max)))
	   (here lim)
	   jump
	   )
      (if (> lim (point))
	  (progn
	    (let ((state 
		   (save-excursion
		     (parse-partial-sexp (point-min) (point)))))
	      (cond
	       ((nth 4 state) ;; in /* */ comment
		(verilog-re-search-forward "/\*" nil 'move)
		)
	       ((nth 7 state) ;; in // comment
		(verilog-re-search-forward "//" nil 'move)
		)))
	    (narrow-to-region (point) lim)
	    (while (/= here (point))
	      (setq here (point))
	      (forward-comment (buffer-size))
	      (save-excursion
		(beginning-of-line)
		(if (looking-at verilog-directive-re-1)
		    (setq jump t)))
	      (if jump
		  (beginning-of-line 2))
	      )))
      )))
(defun verilog-parenthesis-depth ()
 "Return non zero if in parenthetical-expression"
 (save-excursion
   (car (parse-partial-sexp (point-min) (point)))))

(defun verilog-in-comment-or-string-p ()
 "Return true if in a string or comment"
 (let ((state 
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (or (nth 3 state) (nth 4 state) (nth 7 state))) ; Inside string or comment
 )

(defun verilog-in-star-comment-p ()
 "Return true if in a star comment"
 (let ((state 
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (nth 4 state))
 )

(defun verilog-in-paren ()
 "Return true if in a parenthetical expression"
 (let ((state 
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (/= 0 (nth 0 state)))
 )

(defun verilog-skip-forward-comment-or-string ()
 "Return true if in a string or comment"
 (let ((state 
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (cond
    ((nth 3 state)			;Inside string
     (goto-char (nth 3 state))
     t)
    ((nth 7 state)			;Inside // comment
     (forward-line 1)
     t)
    ((nth 4 state)			;Inside any comment (hence /**/)
     (search-forward "*/"))
    (t
     nil)
    )
   )
 )

(defun verilog-skip-backward-comment-or-string ()
 "Return true if in a string or comment"
 (let ((state 
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (cond
    ((nth 3 state)			;Inside string
     (search-backward "\"")
     t)
    ((nth 7 state)			;Inside // comment
     (search-backward "//")
     t)
    ((nth 4 state)			;Inside /* */ comment
     (search-backward "/*")
     t)
    (t
     nil)
    )
   )
 )

(defun verilog-skip-forward-comment-p ()
  "If in comment, move to end and return true"
  (let (state)
    (progn 
      (setq state
	    (save-excursion
	      (parse-partial-sexp (point-min) (point))))
      (cond 
       ((nth 3 state)
	t)
       ((nth 7 state)			;Inside // comment
	(end-of-line)
	(forward-char 1)
	t)
       ((nth 4 state)			;Inside any comment
	t)
       (t
	nil)
       )
      )
    )
  )

(defun verilog-indent-line-relative ()
  "Cheap version of indent line that only looks at
  a few lines to determine indent level"
  (interactive)
  (let ((indent-str))
    (save-excursion
      (beginning-of-line)
      (if (looking-at "^[ \t]*$")
	  (cond  ;- A blank line; No need to be too smart.
	   ((bobp)
	    (setq indent-str (list 'cpp 0)))
	   ((verilog-continued-line)
	    (let ((sp (point)))
	      (if (verilog-continued-line)
		  (progn (goto-char sp)
			 (setq indent-str (list 'statement (verilog-indent-level))))
		(goto-char sp)
		(setq indent-str (list 'block (verilog-indent-level))))))
	   (t
	    (setq indent-str (verilog-calculate-indent))))
	(setq indent-str (verilog-calculate-indent))
	)
      )
    (verilog-do-indent indent-str)
    )
  )
(defun verilog-indent-line ()
  "Indent for special part of code."
  (if (looking-at verilog-directive-re)
      ;; We could nicely nest `ifdef's, but...
      (progn
	(delete-horizontal-space)
	(indent-to 0)
	(list 'cpp 0))			; Return verilog-calculate-indent data
    (verilog-do-indent (verilog-calculate-indent)))
  )

(defun verilog-do-indent (indent-str)
  ""
  (let ((type (car indent-str))
	(ind (car (cdr indent-str))))
    (cond 
     (; handle continued exp
      (eq type 'cexp)
      (let ((here (point)))
	(verilog-backward-syntactic-ws)
	(cond
	 ((= (preceding-char) ?\,)
	  (let* ( fst
		  (val
		   (save-excursion
		     (backward-char 1)
		     (verilog-beg-of-statement-1)
		     (setq fst (point))
		     (if (looking-at verilog-declaration-re)
			 (progn ;; we have multiple words
			   (goto-char (match-end 0))
			   (skip-chars-forward " \t")
			   (if (= (following-char) ?\[)
			       (progn
				 (forward-char 1)
				 (backward-up-list -1)
				 (skip-chars-forward " \t")
				 )
			     )
			   (current-column)
			   )
		       (progn
			 (goto-char fst)
			 (+ (current-column) verilog-cexp-indent)
			 )
		       )
		     )
		   )
		  )
	    (goto-char here)
	    (if (/= (current-column) val)
		(progn
		  (delete-horizontal-space)
		  (indent-to val)))
	    )
	  )
	 ((= (preceding-char) ?\) )
	  (goto-char here)
	  (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
	    (if (/= (current-column) val)
		(progn
		  (delete-horizontal-space)
		  (indent-to val)))
	    )
	  )
	 (t
	  (goto-char here)
	  (let ((val))
	    (verilog-beg-of-statement)
	    (if (verilog-re-search-forward "=[ \\t]*" here 'move)
		(setq val (current-column))
	      (setq val (eval (cdr (assoc type verilog-indent-alist)))))
	    (goto-char here)
	    (if (/= (current-column) val)
		(progn
		  (delete-horizontal-space)
		  (indent-to val)))
	    )
	  )
	 )
	)
      )
     (; handle inside parenthetical expressions
      (eq type 'cparenexp)
      (let ((val (save-excursion
		      (backward-up-list 1)
		      (forward-char 1)
		      (skip-chars-forward " \t")
		      (current-column))))
	(if (/= (current-column) val)
	    (progn
	      (delete-horizontal-space)
	      (indent-to val)))
	))
     
     (;-- Handle the ends
      (looking-at verilog-end-block-re )
      (let ((val (if (eq type 'statement)
		     (- ind verilog-indent-level)
		   ind)))
	(if (/= (current-column) val)
	    (progn
	      (delete-horizontal-space)
	      (indent-to val)))
	))

	
     (;-- Case -- maybe line 'em up
      (and (eq type 'case) (not (looking-at "^[ \t]*$")))
      (progn
	(cond
	 ((looking-at "\\<endcase\\>")
	  (if (/= (current-column) ind)
	      (progn
		(delete-horizontal-space)
		(indent-to ind))))
	 (t
	  (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
	    (if (/= (current-column) val)
		(progn
		  (delete-horizontal-space)
		  (indent-to val)))
	    )
	  )
	 )
	)
      )

     (;-- defun
      (and (eq type 'defun)
 	   (looking-at verilog-zero-indent-re))
      (if (/= (current-column) 0)
	  (delete-horizontal-space)))

     (;-- declaration
      (and (or 
	    (eq type 'defun)
	    (eq type 'block))
	   (looking-at verilog-declaration-re))
      (verilog-indent-declaration ind))

     (;-- Everything else
      t
      (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
	(if (/= (current-column) val)
	    (progn
	      (delete-horizontal-space)
	      (indent-to val)))
	))
     )
    (if (looking-at "[ \t]+$")
	(skip-chars-forward " \t"))
    indent-str				; Return indent data
    )
)
  
(defun verilog-indent-level ()
  "Return the indent-level the current statement has."
  (save-excursion
    (beginning-of-line)
    (skip-chars-forward " \t")
    (current-column)))


(defun verilog-case-indent-level ()
  "Return the indent-level the current statement has.
Do not count named blocks or case-statements."
  (save-excursion
    (skip-chars-forward " \t")
    (cond
     ((looking-at verilog-named-block-re)
      (current-column))
     ((and (not (looking-at verilog-case-re))
	   (looking-at "^[^:;]+[ \t]*:"))
      (search-forward ":" nil t)
      (skip-chars-forward " \t")
      (current-column))
     (t
      (current-column)))))

(defun verilog-indent-comment ()
  "Indent current line as comment."
  (let* ((stcol 
	  (cond 
	   ((verilog-in-star-comment-p)
	    (save-excursion
	      (re-search-backward "/\\*" nil t)
	      (1+(current-column))))
	   (comment-column
	     comment-column )
	   (t
	    (save-excursion
	      (re-search-backward "//" nil t)
	      (current-column)))
	   )
	  ))
    (delete-horizontal-space)
    (indent-to stcol)
    stcol)
  )
(defun verilog-more-comment (&optional arg)
  "Make more comment lines like the previous "
  (let* ((star 0)
	 (stcol 
	  (cond 
	   ((verilog-in-star-comment-p)
	    (save-excursion
	      (setq star 1)
	      (re-search-backward "/\\*" nil t)
	      (1+(current-column))))
	   (comment-column
	    comment-column )
	   (t
	    (save-excursion
	      (re-search-backward "//" nil t)
	      (current-column)))
	   )
	  ))
    (progn
      (indent-to stcol)
      (if (and star 
	       (save-excursion
		 (forward-line -1)
		 (skip-chars-forward " \t")
		 (looking-at "\*")
		 )
	       )
	  (insert "* "))
      )
    )
  )
(defun verilog-comment-indent (&optional arg)
  "return the column number the line should be indented to."
  (cond 
   ((verilog-in-star-comment-p)
    (save-excursion
      (re-search-backward "/\\*" nil t)
      (1+(current-column))))
   ( comment-column
     comment-column )
   (t
    (save-excursion
      (re-search-backward "//" nil t)
      (current-column)))
   )
  )

;;;

(defun verilog-pretty-declarations ()
  "Line up declarations arround point"
  (interactive)
  (save-excursion
    (if (progn
	  (verilog-beg-of-statement-1)
	  (looking-at verilog-declaration-re))
	(let* ((m1 (make-marker))
	       (e) (r)
	       (here (point))
	       (start
		(progn
		  (verilog-beg-of-statement-1)
		  (while (looking-at verilog-declaration-re)
		    (beginning-of-line)
		    (setq e (point))
		    (verilog-backward-syntactic-ws)
		    (backward-char)
		    (verilog-beg-of-statement-1)) ;Ack, need to grok `define
		  e))
	       (end
		(progn
		  (goto-char here)
		  (verilog-end-of-statement)
		  (setq e (point))	;Might be on last line
		  (verilog-forward-syntactic-ws)
		  (while (looking-at verilog-declaration-re)
		    (beginning-of-line)
		    (verilog-end-of-statement)
		    (setq e (point))
		    (verilog-forward-syntactic-ws)
		    )
		  e))
	       (edpos (set-marker (make-marker) end))
	       (ind) 
	       (base-ind 
		(progn
		  (goto-char start)
		  (verilog-do-indent (verilog-calculate-indent))
		  (verilog-forward-ws&directives)
		  (current-column)
		  ))
	       )
	  (goto-char end)
	  (goto-char start)
	  (if (> (- end start) 100)
	      (message "Lining up declarations..(please stand by)"))
	  ;; Get the begining of line indent first
	  (while (progn (setq e (marker-position edpos))
			(< (point) e))
	    (delete-horizontal-space)
	    (indent-to base-ind)
	    (forward-line))
	  ;; Now find biggest prefix
	  (setq ind (verilog-get-lineup-indent start edpos))
	  ;; Now indent each line.
	  (goto-char start)
	  (while (progn (setq e (marker-position edpos))
			(setq r (- e (point)))
			(> r 0))
	    (setq e (point))
	    (message "%d" r)
	    (cond
	     ((looking-at verilog-declaration-re-1)
	      (let ((p (match-end 0)))
		(set-marker m1 p)
		(if (verilog-re-search-forward "\\[" p 'move)
		    (progn
		      (forward-char -1)
		      (just-one-space)
		      (goto-char (marker-position m1))
		      (just-one-space)
		      (indent-to ind)
		      )
		  (progn
		    (just-one-space)
		    (indent-to ind))
		  )
		))
	     ((verilog-continued-line-1)
	      (goto-char e)
	      (delete-horizontal-space)
	      (indent-to ind))
	     (t 	; Must be comment or white space
	      (goto-char e)
	      (verilog-forward-ws&directives)
	      (forward-line -1)
	      )	
	     )
	    (forward-line 1)
	    )
	  (message "")
	  )
      )
    )
  )
(defun verilog-indent-declaration (baseind)
  "Indent current lines as declaration, lining up the variable names
   based on previous declaration's indentation."
  (interactive)
  (let ((pos (point-marker))
	(lim (save-excursion 
	       (verilog-re-search-backward "\\(\\<begin\\>\\)\\|\\(\\<module\\>\\)" nil 'move)  
	       (point)))
	(ind)
	(val)
	(m1 (make-marker))
	)
    ;; Use previous declaration (in this module) as template.
    (if (verilog-re-search-backward verilog-declaration-re-1 lim t)
	(progn
	  (goto-char (match-end 0))
	  (setq ind (current-column))
	  (goto-char pos)
	  (setq val (+ baseind (eval (cdr (assoc 'declaration verilog-indent-alist)))))
	  (if (/= (current-column) val)
	      (progn
		(delete-horizontal-space)
		(indent-to val)))
	  (if (looking-at verilog-declaration-re-2)
	      (let ((p (match-end 0)))
		(set-marker m1 p)
		(if (verilog-re-search-forward "\\[" p 'move)
		    (progn
		      (forward-char -1)
		      (just-one-space)
		      (goto-char (marker-position m1))
		      (just-one-space)
		      (indent-to ind)
		      )
		  (if (/= p ind)
		      (progn
			(just-one-space)
			(indent-to ind))
		    )
		  )
		)
	    )
	  )
      (let ((val (+ baseind (eval (cdr (assoc 'declaration verilog-indent-alist))))))
	(if (/= val (current-column))
	    (progn
	      (delete-horizontal-space)
	      (indent-to val))))
      )
    (goto-char pos)
    )
  )

;  "Return the indent level that will line up several lines within the region
;from b to e nicely. The lineup string is str."
(defun verilog-get-lineup-indent (b edpos)
  (save-excursion
    (let ((ind 0) e)
      (goto-char b)
      ;; Get rightmost position
      (while (progn (setq e (marker-position edpos))
		    (< (point) e))
	(if (verilog-re-search-forward verilog-declaration-re-1 e 'move)
	    (progn
	      (goto-char (match-end 0))
	      (verilog-backward-syntactic-ws)
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
  '("buf" "bufif0" "bufif1" "cmos" "defparam" "inout" "input"
    "integer" "nand" "nmos" "nor" "not" "notif0" "notif1" "or" "output" "parameter"
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
  '("begin" "fork" "join" "case" "end" "if" "else" "for" "while" "repeat")
  "*Keywords to complete when standing at first word of a line in behavioral scope.
\(eg. begin, if, then, else, for, fork.)
The procedures and variables defined within the Verilog program
will be completed runtime and should not be added to this list.")

(defvar verilog-tf-keywords
  '("begin" "fork" "join" "case" "end" "endtask" "endfunction" "if" "else" "for" "while" "repeat")
  "*Keywords to complete when standing at first word of a line in a task or function scope.
\(eg. begin, if, then, else, for, fork.)
The procedures and variables defined within the Verilog program
will be completed runtime and should not be added to this list.")

(defvar verilog-case-keywords
  '("begin" "fork" "join" "case" "end" "endcase" "if" "else" "for" "repeat")
  "*Keywords to complete when standing at first word of a line in behavioral scope.
\(eg. begin, if, then, else, for, fork.)
The procedures and variables defined within the Verilog program
will be completed runtime and should not be added to this list.")

(defvar verilog-separator-keywords
  '("else" "then" "begin")
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
  ;; Build regular expression for module/task/function names
  (if (string= verilog-str "")
      (setq verilog-str "[a-zA-Z_]"))
  (let ((verilog-str (concat (cond
			     ((eq type 'module) "\\<\\(module\\)\\s +")
			     ((eq type 'tf) "\\<\\(task\\|function\\)\\s +")
			     (t "\\<\\(task\\|function\\|module\\)\\s +"))
			    "\\<\\(" verilog-str "[a-zA-Z0-9_.]*\\)\\>"))
	match)
    
    (if (not (looking-at verilog-defun-re))
	(verilog-re-search-backward verilog-defun-re nil t))
    (forward-char 1)

    ;; Search through all reachable functions
    (goto-char (point-min))
    (while (verilog-re-search-forward verilog-str (point-max) t)
      (progn (setq match (buffer-substring (match-beginning 2)
					   (match-end 2)))
	     (if (or (null verilog-pred)
		     (funcall verilog-pred match))
		 (setq verilog-all (cons match verilog-all)))))
    (if (match-beginning 0)
	(goto-char (match-beginning 0)))))

(defun verilog-get-completion-decl ()
  ;; Macro for searching through current declaration (var, type or const)
  ;; for matches of `str' and adding the occurence tp `all'
  (let ((end (save-excursion (verilog-declaration-end)
			     (point)))
	match)
    ;; Traverse lines
    (while (< (point) end)
      (if (verilog-re-search-forward verilog-declaration-re-1 (verilog-get-end-of-line) t)
	  ;; Traverse current line
	  (while (and (verilog-re-search-forward 
		       (concat "\\((\\|\\<\\(var\\|type\\|const\\)\\>\\)\\|" 
			       verilog-symbol-re)
		       (verilog-get-beg-of-line) t)
		      (not (match-end 1)))
	    (setq match (buffer-substring (match-beginning 0) (match-end 0)))
	    (if (string-match (concat "\\<" verilog-str) match)
		(if (or (null verilog-pred)
			(funcall verilog-pred match))
		    (setq verilog-all (cons match verilog-all))))))
      (if (verilog-re-search-forward "\\<record\\>" (verilog-get-end-of-line) t)
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
		 (verilog-re-search-forward
		  "\\<type\\>\\|\\<\\(begin\\|function\\|procedure\\)\\>"
		  start t)
		 (not (match-end 1)))
	    ;; Check current type declaration
	    (verilog-get-completion-decl))))))

(defun verilog-var-completion ()
  "Calculate all possible completions for variables (or constants)."
  nil)
;  Not done yet; in 1.99 perhaps
;  (let ((start (point))
;	goon twice)
;    ;; Search for all reachable var declarations
;    (while (or (verilog-beg-of-defun)
;	       (setq goon (not goon)))
;      (save-excursion
;	(if (> start (prog1 (save-excursion (verilog-end-of-defun)
;					    (point))))
;	    () ; Declarations not reacable
;	  (cond ((and (verilog-re-search-forward  verilog-declaration-re start t)
;		      ;; Check var/const declarations
;		      (verilog-get-completion-decl)))))))))


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
		  tmp)
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
  "Return function/task/module starting with STR as regular expression.
With optional second arg non-nil, STR is the complete name of the instruction."
  (if arg
      (concat "^\\(function\\|task\\|module\\)[ \t]+\\(" str "\\)\\>")
    (concat "^\\(function\\|task\\|module\\)[ \t]+\\(" str "[a-zA-Z0-9_]*\\)\\>")))

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
	(while (verilog-re-search-forward verilog-str nil t)
	  (setq match (buffer-substring (match-beginning 2) (match-end 2)))
	  (if (or (null verilog-pred)
		  (funcall verilog-pred match))
	      (setq verilog-all (cons match verilog-all)))))

      ;; Now we have built a list of all matches. Give response to caller
      (verilog-completion-response))))

(defun verilog-goto-defun ()
  "Move to specified Verilog module/task/function.
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
(defun verilog-showscopes ()
  "list all scopes in this module"
  (interactive)
  (let (
    	(buffer (current-buffer))
	(linenum 1)
	(nlines 0)
	(first 1)
	(prevpos (point-min))
        (final-context-start (make-marker))
	(regexp "\\(module\\s-+\\w+\\s-*(\\)\\|\\(\\w+\\s-+\\w+\\s-*(\\)")
	)
    (with-output-to-temp-buffer "*Occur*"
      (save-excursion
	(message (format "Searching for %s ..." regexp))
	;; Find next match, but give up if prev match was at end of buffer.
	(while (and (not (= prevpos (point-max)))
		    (verilog-re-search-forward regexp nil t))
	  (goto-char (match-beginning 0))
	  (beginning-of-line)
	  (save-match-data
            (setq linenum (+ linenum (count-lines prevpos (point)))))
	  (setq prevpos (point))
	  (goto-char (match-end 0))
	  (let* ((start (save-excursion
			  (goto-char (match-beginning 0))
			  (forward-line (if (< nlines 0) nlines (- nlines)))
			  (point)))
		 (end (save-excursion
			(goto-char (match-end 0))
			(if (> nlines 0)
			    (forward-line (1+ nlines))
			    (forward-line 1))
			(point)))
		 (tag (format "%3d" linenum))
		 (empty (make-string (length tag) ?\ ))
		 tem)
	    (save-excursion
	      (setq tem (make-marker))
	      (set-marker tem (point))
	      (set-buffer standard-output)
	      (setq occur-pos-list (cons tem occur-pos-list))
	      (or first (zerop nlines)
		  (insert "--------\n"))
	      (setq first nil)
	      (insert-buffer-substring buffer start end)
	      (backward-char (- end start))
	      (setq tem (if (< nlines 0) (- nlines) nlines))
	      (while (> tem 0)
		(insert empty ?:)
		(forward-line 1)
		(setq tem (1- tem)))
	      (let ((this-linenum linenum))
		(set-marker final-context-start
			    (+ (point) (- (match-end 0) (match-beginning 0))))
		(while (< (point) final-context-start)
		  (if (null tag)
		      (setq tag (format "%3d" this-linenum)))
		  (insert tag ?:)))))))
      (set-buffer-modified-p nil))))

(defun verilog-submit-bug-report ()
  "Submit via mail a bug report on lazy-lock.el."
  (interactive)
  (let ((reporter-prompt-for-summary-p t))
    (reporter-submit-bug-report 
     "verilog-mode-bugs@verilog.com" 
     (concat "verilog-mode v" (substring verilog-mode-version 12 -3))
     '(verilog-indent-level 
       verilog-indent-level-module 
       verilog-indent-level-declaration
       verilog-indent-level-behavioral 
       verilog-cexp-indent
       verilog-case-indent 
       verilog-auto-newline 
       verilog-auto-indent-on-newline 
       verilog-tab-always-indent 
       verilog-auto-endcomments 
       verilog-minimum-comment-distance 
       verilog-indent-begin-after-if 
       verilog-auto-lineup)
     nil nil
     (concat "Hi Mac,

I want to report a bug.  I've read the `Bugs' section of `Info' on
Emacs, so I know how to make a clear and unambiguous report.  To get
to that Info section, I typed

M-x info RET m " invocation-name " RET m bugs RET
 
Before I go further, I want to say that Verilog mode has changed my life.
I save so much time, my files are colored nicely, my co workers respect 
my coding ability... until now.  I'd really appreciate anything you 
could do to help me out with this minor deficiency in the product.

To reproduce the bug, start a fresh Emacs via " invocation-name "
-no-init-file -no-site-file'.  In a new buffer, in verilog mode, type
the code included below.

Given those lines, I expected [[Fill in here]] to happen; 
but instead, [[Fill in here]] happens!.

== The code: =="))))

;;; verilog.el ends here
