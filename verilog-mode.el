;;; verilog-mode.el --- major mode for editing verilog source in Emacs
;;
;; $Id$

;; Copyright (C) 1996 Free Software Foundation, Inc.

;; Author: Michael McNamara (mac@verilog.com) 
;; President, SureFire Verification, Inc.
;; (company was previously known as Silicon Sorcery)
;;	http://www.surefirev.com
;; AUTO features, signal, modsig; by: Wilson Snyder (wsnyder@wsnyder.org)
;;	http://www.veripool.org
;; Keywords: languages

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
;;; <http://www.surefirev.com/emacs_install.html>

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
;;; Be sure to examine at the help for verilog-auto, and the other
;;; verilog-auto-* functions for some major coding time savers.
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
;;; This is beta code, and likely has bugs. Please report any and all
;;; bugs to me at verilog-mode-bugs@verilog.com.  Use
;;; verilog-submit-bug-report to submit a report.
;; 
;;; Code:

(provide 'verilog-mode)

;; This variable will always hold the version number of the mode
(defconst verilog-mode-version "$$Revision$$"
  "Version of this verilog mode.")
(defun verilog-version ()
  "Inform caller of the version of this file"
  (interactive)
  (message (concat "Using verilog-mode version " (substring verilog-mode-version 12 -3 )) )
  )
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
          (if (fboundp 'when)
	      nil ;; fab
	    (defmacro when (var &rest body)
	      (` (cond ( (, var) (,@ body))))))
        (error nil))
      (condition-case nil
          (if (fboundp 'unless)
	      nil ;; fab
	    (defmacro unless (var &rest body)
	      (` (if (, var) nil (,@ body)))))
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
      ;; Requires to define variables that would be "free" warnings
      (condition-case nil
	  (require 'font-lock)
	(error nil))
      (condition-case nil
	  (require 'compile)
	(error nil))
      (condition-case nil
	  (require 'custom)
	(error nil))
      (condition-case nil
	  (require 'dinotrace)
	(error nil))
      (condition-case nil
	  (if (fboundp 'dinotrace-unannotate-all)
	      nil ;; great
	    (defun dinotrace-unannotate-all (&rest args) nil))
	(error nil))
      (condition-case nil
	  (if (fboundp 'customize-apropos)
	      nil ;; great
	    (defun customize-apropos (&rest args) nil))
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

(defcustom verilog-tab-to-comment nil
  "*Non-nil means TAB in Verilog mode should move to the right hand
  column in preparation for a comment."
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

(defcustom verilog-minimum-comment-distance 10
  "*Minimum distance (in lines) between begin and end required before
a comment will be inserted.  Setting this variable to zero results in
every end acquiring a comment; the default avoids too many redundant
comments in tight quarters"
  :group 'verilog-mode
  :type 'integer 
  )

(defcustom verilog-auto-endcomments t
  "*Non-nil means a comment /* ... */ is set after the ends which ends
  cases and functions. The name of the function or case will be set
  between the braces."
  :group 'verilog-mode
  :type 'boolean )

(defcustom verilog-auto-save-policy nil
  "*Non-nil indicates action to take when saving a Verilog buffer that has
  been changed but not auto-updated.  A value of `force' will always do the
  auto-updates when saving.  A value of `detect' will do the auto-updates
  when it thinks necessary.  A value of `ask' will query the user when it
  thinks updating is needed.

  You should not rely on the 'ask or 'detect policies, they are safeguards
  only.  They do not detect when AUTOINSTs need to be updated because a
  sub-module's port list has changed."
  :group 'verilog-mode
  :type '(choice (const nil) (const ask) (const detect) (const force)))

(defvar verilog-auto-update-tick nil
  "Modification tick at which autos were last performed.")

(setq verilog-error-regexp
  '(
    ("^\\(Error\\|Warning\\):.*\\s \\([^ \t]+\\)\\s *\\([0-9]+\\):" 2 3) ; vcs
    ("^\\(Error\\|Warning\\):.*\n\\([^ \t]+\\)\\s *\\([0-9]+\\):" 2 3) ; vcs, w/newline
    ("^\\(Error\\|Warning\\):[^(]*(\\([^ \t]+\\)\\s line \\([0-9]+\\))" 2 3) ; vcs, w/newline 
    ("^Warning:.*(port.*(\\([^ \t]+\\) line \\([0-9]+\\))" 1 2) ; vcs, w/newline 
    ("^syntax error:.*\n\\([^ \t]+\\)\\s *\\([0-9]+\\):" 1 2) ; vcs, w/newline
    ("^Warning: port size.*(\\([^ \t]+\\)\\s line *\\([0-9]+\\))" 1 2)  ; vcs
    ("^Error: Port name.*(\\([^ \t]+\\)\\s line *\\([0-9]+\\))" 1 2)	; vcs
    ("^([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+\\([0-9]+\\):.*$" 1 2)	     ; vxl
    ("^([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+line[ \t]+\\([0-9]+\\):.*$" 1 2)  ; vxl
    )
;  "*List of regexps for verilog compilers, like verilint. See compilation-error-regexp-alist for the formatting."
)

(defcustom verilog-library-directories '(".")
  "*List of directories when looking for files for /*AUTOINST*/
auto-instantiation.  The directory may be relative to the current
file, or absolute.  Having at least the current directory is a good
idea.
 
You might want these defined in each file; put at the *END* of your file
something like:

// Local Variables:
// verilog-library-directories:(\".\" \"subdir\" \"subdir2\")
// End:

Note these are only read when the file is first visited, you must use
\\[find-alternate-file] RET  to have these take effect after editing them!
"
  :group 'verilog-mode
  :type '(repeat directory)
  )

(defcustom verilog-auto-sense-include-inputs nil
  "*If true, AUTOSENSE should include in the sensitivity list
input signals that are also output signals in the same block."
  :type 'boolean
  :group 'verilog-mode)

(defcustom verilog-mode-hook nil
  "*Hook (List of functions) run after verilog mode is loaded."
  :type 'hook
  :group 'verilog-mode)

(defcustom verilog-before-auto-hook nil
  "*Hook run before verilog-mode updates AUTOs."
  :type 'hook
  :group 'verilog-mode)

(defcustom verilog-auto-hook nil
  "*Hook run after verilog-mode updates AUTOs."
  :type 'hook
  :group 'verilog-mode)

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
    ("^\\s-*function\\>\\s-+\\(\\(\\[[^]]*\\]\\|integer\\|real\\(time\\)?\\|time\\)\\s-+\\)?\\(\\sw+\\)"
     3 'font-lock-function-name-face nil t)
    ("\\(//\\s-*sv\\s-.*\\)" 1 'font-lock-function-name-face t t)
    ("^\\s-*\\(task\\|module\\|macromodule\\|primitive\\)\\>\\s-*\\(\\sw+\\)"  
     2 'font-lock-function-name-face nil t)
    ("\\(\\\\\\S-*\\s-\\)\\|\\(`\\s-*[A-Za-z][A-Za-z0-9_]*\\)" 
     0 'font-lock-function-name-face)
    ("\\(@\\)\\|\\(#\\s-*\\(\\(\[0-9_\]+\\('[hdxbo][0-9_xz]*\\)?\\)\\|\\((\[^)\]*)\\|\\sw+\\)\\)\\)" 
     0 'font-lock-type-face)
;    (princ (regexp-opt (list 
;			"defparam" "event" "inout" "input" "integer" "output" "parameter"
;			"real" "realtime" "reg" "signed" "supply" "supply0" "supply1" "time"
;			"tri" "tri0" "tri1" "triand" "trior" "trireg" "vectored" "wand" "wire"
;			"wor" ) nil)
    ("\\<\\(?:defparam\\|event\\|in\\(?:out\\|put\\|teger\\)\\|output\\|parameter\\|re\\(?:al\\(?:time\\)?\\|g\\)\\|s\\(?:igned\\|upply[01]?\\)\\|t\\(?:ime\\|ri\\(?:and\\|or\\|reg\\|[01]\\)?\\)\\|vectored\\|w\\(?:and\\|ire\\|or\\)\\)\\>"
     0 'font-lock-type-face)

;    (princ (concat "\\<\\(\\$[a-zA-Z][a-zA-Z0-9_\\$]*\\|" 
;	     (regexp-opt (list 
;			  "always" "assign" "begin" "case" "casex" "casez" "default" "deassign"
;			  "disable" "else" "end" "endcase" "endfunction" "endmodule"
;			  "endprimitive" "endspecify" "endtable" "endtask" "for" "force"
;			  "forever" "fork" "function" "if" "initial" "join" "macromodule"
;			  "module" "negedge" "posedge" "primitive" "repeat" "release" "specify"
;			  "table" "task" "wait" "while" ))
;	     "\\)\\>" )
    ("\\<\\(\\$[a-zA-Z][a-zA-Z0-9_\\$]*\\|a\\(?:lways\\|ssign\\)\\|begin\\|case[xz]?\\|d\\(?:e\\(?:assign\\|fault\\)\\|isable\\)\\|e\\(?:lse\\|nd\\(?:case\\|function\\|module\\|primitive\\|specify\\|ta\\(?:ble\\|sk\\)\\)?\\)\\|f\\(?:or\\(?:ce\\|ever\\|k\\)?\\|unction\\)\\|i\\(?:f\\|nitial\\)\\|join\\|m\\(?:acromodule\\|odule\\)\\|negedge\\|p\\(?:osedge\\|rimitive\\)\\|re\\(?:lease\\|peat\\)\\|specify\\|ta\\(?:ble\\|sk\\)\\|w\\(?:ait\\|hile\\)\\)\\>"
     0 'font-lock-keyword-face))
  )


(defvar verilog-font-lock-keywords-before-1930
  '(
    ("^\\s-*function\\>\\s-+\\(\\(\\[[^]]*\\]\\|integer\\|real\\(time\\)?\\|time\\)\\s-+\\)?\\(\\sw+\\)"
     3 font-lock-function-name-face nil t)
    ("\\(//\\s-*sv\\s-.*\\)" 1 font-lock-function-name-face t t)
    ("^\\s-*\\(task\\|module\\|macromodule\\|primitive\\)\\>\\s-*\\(\\sw+\\)"  
     2 font-lock-function-name-face nil t)
    ("\\(\\\\\\S-*\\s-\\)\\|\\(`\\s-*[A-Za-z][A-Za-z0-9_]*\\)" 
     0 font-lock-function-name-face)
    ("\\(@\\)\\|\\(#\\s-*\\(\\(\[0-9_\]+\\('[hdxbo][0-9_xz]*\\)?\\)\\|\\((\[^)\]*)\\|\\sw+\\)\\)\\)" 
     0 font-lock-type-face)
    ("\\<\\(defparam\\|event\\|in\\(out\\|put\\|teger\\)\\|output\\|parameter\\|re\\(al\\(time\\)?\\|g\\)\\|s\\(igned\\|upply[01]?\\)\\|t\\(ime\\|ri\\(and\\|or\\|reg\\|[01]\\)?\\)\\|vectored\\|w\\(and\\|ire\\|or\\)\\)\\>"
     0 font-lock-type-face)
    ("\\<\\(\\$[a-zA-Z][a-zA-Z0-9_\\$]*\\|a\\(lways\\|ssign\\)\\|begin\\|case[xz]?\\|d\\(e\\(assign\\|fault\\)\\|isable\\)\\|e\\(lse\\|nd\\(case\\|function\\|module\\|primitive\\|specify\\|ta\\(ble\\|sk\\)\\)?\\)\\|f\\(or\\(ce\\|ever\\|k\\)?\\|unction\\)\\|i\\(f\\|nitial\\)\\|join\\|m\\(acromodule\\|odule\\)\\|negedge\\|p\\(osedge\\|rimitive\\)\\|re\\(lease\\|peat\\)\\|specify\\|ta\\(ble\\|sk\\)\\|w\\(ait\\|hile\\)\\)\\>"
     0 font-lock-keyword-face)
    )
  )

(defvar verilog-imenu-generic-expression
  '((nil "^\\s-*\\(\\(m\\(odule\\|acromodule\\)\\)\\|primitive\\)\\s-+\\([a-zA-Z0-9_.:]+\\)" 4)
    ("*Vars*" "^\\s-*\\(reg\\|wire\\)\\s-+\\(\\|\\[[^\\]]+\\]\\s-+\\)\\([A-Za-z0-9_]+\\)" 3))
  "Imenu expression for Verilog-mode.  See `imenu-generic-expression'.")

(defvar verilog-mode-abbrev-table nil
  "Abbrev table in use in Verilog-mode buffers.")

;;;
;;; provide a verilog-header function.
;;; Customization variables:
;;;
(defvar verilog-date-scientific-format nil
  "*If non-nil, dates are written in scientific format (e.g. 1997/09/17),
in european format otherwise (e.g. 17.09.1997). The braindead american
format (e.g. 09/17/1997) is not supported.")

(defvar verilog-company nil "Default name of Company for verilog
  header. If set will become buffer local. ")

(defvar verilog-project nil "Default name of Project for verilog
  header. If set will become buffer local.")

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
  (define-key verilog-mode-map "\177"     'backward-delete-char-untabify)
  (define-key verilog-mode-map "\M-\C-b"  'electric-verilog-backward-sexp)
  (define-key verilog-mode-map "\M-\C-f"  'electric-verilog-forward-sexp)
  (define-key verilog-mode-map "\M-\r"    (function (lambda ()
		      (interactive) (electric-verilog-terminate-line 1))))
  (define-key verilog-mode-map "\M-\t"    'verilog-complete-word)
  (define-key verilog-mode-map "\M-?"     'verilog-show-completions)
  (define-key verilog-mode-map "\M-\C-h"  'verilog-mark-defun)
  (define-key verilog-mode-map "\C-c`"    'verilog-verilint-off)
  (define-key verilog-mode-map "\C-c\C-r" 'verilog-label-be)
  (define-key verilog-mode-map "\C-c\C-i" 'verilog-pretty-declarations)
  (define-key verilog-mode-map "\C-c\C-b" 'verilog-submit-bug-report)
  (define-key verilog-mode-map "\M-*"     'verilog-star-comment)
  (define-key verilog-mode-map "\C-c\C-c" 'verilog-comment-region)
  (define-key verilog-mode-map "\C-c\C-u" 'verilog-uncomment-region)
  (define-key verilog-mode-map "\M-\C-a"  'verilog-beg-of-defun)
  (define-key verilog-mode-map "\M-\C-e"  'verilog-end-of-defun)
  (define-key verilog-mode-map "\C-c\C-d" 'verilog-goto-defun)
  (define-key verilog-mode-map "\C-c\C-k" 'verilog-delete-auto)
  (define-key verilog-mode-map "\C-c\C-a" 'verilog-auto)
  (define-key verilog-mode-map "\C-c\C-s" 'verilog-auto-save-compile)
  (define-key verilog-mode-map "\C-c\C-e" 'verilog-expand-vector)
  (define-key verilog-mode-map "\C-c\C-h" 'verilog-header)
  )

;; menus

(defvar verilog-xemacs-menu
  '("Verilog"
    ["Line up declarations around point"	verilog-pretty-declarations t]
    ["Redo/insert comments on every end"	verilog-label-be t]
    "----"
    ["Beginning of function"		verilog-beg-of-defun t]
    ["End of function"			verilog-end-of-defun t]
    ["Mark function"			verilog-mark-defun t]
    ["Goto function"			verilog-goto-defun t]
    "----"				
    ["Move to beginning of block"	electric-verilog-backward-sexp t]
    ["Move to end of block"		electric-verilog-forward-sexp t]
    "----"				
    ["Comment Region"			verilog-comment-region t]
    ["UnComment Region"			verilog-uncomment-region t]
    ["Multi-line comment insert"	verilog-star-comment t]
    ["Verilint error to comment"	verilog-verilint-off t]
    ["Expand [x:y] vector line"		verilog-expand-vector t]
    "----"				
    ["Insert begin-end block"		verilog-insert-block t]
    ["Complete word"			verilog-complete-word t]
    "----"
    ["Recompute AUTOs"			verilog-auto t]
    ["Kill AUTOs"			verilog-delete-auto t]
    ["AUTO, Save, Compile"		verilog-auto-save-compile t]
    ["Compile"				verilog-compile t]
    ["Next Compile Error"		next-error t]
    "----"
    ("Help..."
     ["AUTO General"			(describe-function 'verilog-auto) t]
     ["AUTO Library Path"		(describe-variable 'verilog-library-directories) t]
     ["AUTO `define Reading"		(describe-function 'verilog-read-defines) t]
     ["AUTO `include Reading"		(describe-function 'verilog-read-includes) t]
     ["AUTOARG"				(describe-function 'verilog-auto-arg) t]
     ["AUTOINST"			(describe-function 'verilog-auto-inst) t]
     ["AUTOINOUTMODULE"			(describe-function 'verilog-auto-inout-module) t]
     ["AUTOINPUT"			(describe-function 'verilog-auto-input) t]
     ["AUTOOUTPUT"			(describe-function 'verilog-auto-output) t]
     ["AUTOOUTPUTEVERY"			(describe-function 'verilog-auto-output-every) t]
     ["AUTOWIRE"			(describe-function 'verilog-auto-wire) t]
     ["AUTOREG"				(describe-function 'verilog-auto-reg) t]
     ["AUTOSENSE"			(describe-function 'verilog-auto-sense) t]
     )
    ["Submit bug report"		verilog-submit-bug-report t]
    ["Customize Verilog Mode..."	verilog-customize t]
    ["Customize Verilog Fonts & Colors"	verilog-font-customize t]
    )
  "Emacs menu for VERILOG mode."
  )
(or (string-match "XEmacs" emacs-version)
    (easy-menu-define verilog-menu verilog-mode-map "Menu for Verilog mode"
		      verilog-xemacs-menu))		   

(defvar verilog-mode-abbrev-table nil
  "Abbrev table in use in Verilog-mode buffers.")

(define-abbrev-table 'verilog-mode-abbrev-table ())

;; compilation program
(defun verilog-compile ()
  "function to compile verilog. Can be the path and arguments for your
Verilog simulator: \"vcs -p123 -O\"
or a string like \"(cd /tmp; surecov %s)\".
In the former case, the path to the current buffer is concat'ed to the 
value of verilog-compiler; in the later, the path to the current buffer is substituted for the %s "
  (or (file-exists-p "makefile") (file-exists-p "Makefile")
      (progn (make-local-variable 'compile-command)
	     (setq compile-command
		   (if (string-match "%s" verilog-compiler)
		       (format verilog-compiler (or buffer-file-name ""))
		     (concat verilog-compiler (or buffer-file-name "")))))))

  
(add-hook 'verilog-mode-hook 'verilog-compile)

(defvar verilog-error-regexp-add-didit nil)
(setq verilog-error-regexp-add-didit nil)	;; So reloading file does it again
(defun verilog-error-regexp-add ()
  "Called by compilation-mode-hook to add the Verilint, VCS, etc messages to the
compilation-error-regexp-alist.  This allows \\[next-error] to find the errors."
  (cond (verilog-error-regexp-add-didit)
	(t (setq verilog-error-regexp-add-didit t)
	   ;; Probably buffer local at this point; maybe also in let; change all three
	   (set (make-local-variable 'compilation-error-regexp-alist)
		(append compilation-error-regexp-alist verilog-error-regexp))
	   (setq compilation-error-regexp-alist
		 (append compilation-error-regexp-alist verilog-error-regexp))
	   (setq-default compilation-error-regexp-alist
			 (append (default-value 'compilation-error-regexp-alist) verilog-error-regexp)))))

(add-hook 'compilation-mode-hook 'verilog-error-regexp-add)

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
;	(concat "\\<" 
;		 (regexp-opt (list 
;			      "assign" "defparam" "event" "inout" "input" "integer" "output"
;			      "parameter" "real" "realtime" "reg" "supply" "supply0" "supply1"
;			      "time" "tri" "tri0" "tri1" "triand" "trior" "trireg" "wand" "wire"
;			      "wor") t)
;		 "\\>"))
  "\\<\\(?:assign\\|defparam\\|event\\|in\\(?:out\\|put\\|teger\\)\\|output\\|parameter\\|re\\(?:al\\(?:time\\)?\\|g\\)\\|supply[01]?\\|t\\(?:ime\\|ri\\(?:and\\|or\\|reg\\|[01]\\)?\\)\\|w\\(?:and\\|ire\\|or\\)\\)\\>" )
(defconst verilog-range-re "\\[[^]]*\\]")
(defconst verilog-macroexp-re "`\\sw+")
(defconst verilog-delay-re "#\\s-*\\(\\([0-9_]+\\('[hdxbo][0-9_xz]+\\)?\\)\\|\\(([^)]*)\\)\\|\\(\\sw+\\)\\)")
(defconst verilog-declaration-re-2 
  (concat "\\s-*" verilog-declaration-re 
	  "\\s-*\\(\\(" verilog-range-re "\\)\\|\\(" verilog-delay-re "\\)\\|\\(" verilog-macroexp-re "\\)\\)?"))
(defconst verilog-declaration-re-1 (concat "^" verilog-declaration-re-2))
(defconst verilog-defun-re 
  ;;"module" "macromodule" "primitive"
  "\\(\\<\\(m\\(acromodule\\>\\|odule\\>\\)\\|primitive\\>\\)\\)")
(defconst verilog-end-defun-re   
  ;; "endmodule" "endprimitive"
"\\(\\<end\\(module\\>\\|primitive\\>\\)\\)")
(defconst verilog-zero-indent-re 
  (concat verilog-defun-re "\\|" verilog-end-defun-re))
(defconst verilog-directive-re
  ;;   "`else" "`ifdef" "`endif" "`define" "`undef" "`include" "`timescale" "`protect" "`endprotect 
  "`\\(define\\>\\|e\\(lse\\>\\|nd\\(if\\|protect\\)\\>\\)\\|i\\(fdef\\>\\|nclude\\>\\)\\|protect\\|undef\\>\\|time_?scale\\)")
(defconst verilog-directive-re-1
  ;;   "`else" "`ifdef" "`endif" "`define" "`undef" "`include"
       (concat "[ \t]*"  verilog-directive-re))
(defconst verilog-autoindent-lines-re
  ;; "macromodule" "module" "primitive" "end" "endcase" "endfunction"
  ;; "endtask" "endmodule" "endprimitive" "endspecify" "endtable" "join" 
  ;; "begin" "else" "`else" "`ifdef" "`endif" "`define" "`undef" "`include"
  (concat "\\("
	  verilog-directive-re
	  "\\|\\(\\<begin\\>\\|e\\(lse\\>\\|nd\\(\\>\\|case\\>\\|function\\>\\|module\\>\\|primitive\\>\\|specify\\>\\|ta\\(ble\\>\\|sk\\>\\)\\)\\)\\|join\\>\\|m\\(acromodule\\>\\|odule\\>\\)\\|primitive\\>\\)\\)" )
  )

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
  "\\<\\(always\\|case\\(\\|[xz]\\)\\|begin\\|else\\|for\\(\\|ever\\)\\|i\\(f\\|nitial\\)\\|repeat\\|while\\)\\>")
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

(defconst verilog-keywords
 '("`define" "`else" "`endif" "`ifdef" "`include" "`timescale" "`undef"
   "always" "and" "assign" "begin" "buf" "bufif0" "bufif1" "case" "casex"
   "casez" "cmos" "default" "defparam" "else" "end" "endcase" "endfunction"
   "endmodule" "endprimitive" "endspecify" "endtable" "endtask" "event" "for"
   "force" "forever" "fork" "function" "if" "initial" "inout" "input"
   "integer" "join" "macromodule" "makefile" "module" "nand" "negedge" "nmos"
   "nor" "not" "notif0" "notif1" "or" "output" "parameter" "pmos" "posedge"
   "primitive" "pulldown" "pullup" "rcmos" "real" "realtime" "reg" "repeat"
   "rnmos" "rpmos" "rtran" "rtranif0" "rtranif1" "signed" "specify" "supply"
   "supply0" "supply1" "table" "task" "time" "tran" "tranif0" "tranif1" "tri"
   "tri0" "tri1" "triand" "trior" "trireg" "vectored" "wait" "wand" "while"
   "wire" "wor" "xnor" "xor" )
 "List of Verilog keywords.")

(defconst verilog-keywords-regexp
  (concat "\\<\\(" (mapconcat 'format verilog-keywords "\\|") "\\)\\>")
  "Regexp that matches Verilog keywords.")

(defconst verilog-emacs-features
  (let ((major (and (boundp 'emacs-major-version)
		    emacs-major-version))
	(minor (and (boundp 'emacs-minor-version)
		    emacs-minor-version))
	flavor comments flock-syntax)
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
    ;; determine whether to use old or new font lock syntax
    ;; We can assume 8-bit syntax table emacsen aupport new syntax, otherwise
    ;; look for version > 19.30
    (setq flock-syntax
        (if (or (equal comments '8-bit)
                (equal major 'v20)
                (and (equal major 'v19) (> minor 30)))
            'flock-syntax-after-1930
          'flock-syntax-before-1930))
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
    (list major comments flock-syntax))
  "A list of features extant in the Emacs you are using.
There are many flavors of Emacs out there, each with different
features supporting those needed by verilog-mode.  Here's the current
supported list, along with the values for this variable:

 Vanilla Emacs 18/Epoch 4:   (v18 no-dual-comments flock-syntax-before-1930)
 Emacs 18/Epoch 4 (patch2):  (v18 8-bit flock-syntax-after-1930)
 XEmacs (formerly Lucid) 19: (v19 8-bit flock-syntax-after-1930)
 XEmacs 20:                  (v20 8-bit flock-syntax-after-1930)
 Emacs 19.1-19.30:           (v19 8-bit flock-syntax-before-1930)
 Emacs 19.31-19.xx:          (v19 8-bit flock-syntax-after-1930)
 Emacs20        :            (v20 1-bit flock-syntax-after-1930).")

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
   ((memq 'flock-syntax-after-1930 verilog-emacs-features)
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

(defsubst verilog-string-replace-matches (from-string to-string fixedcase literal string)
  "Replace occurances of from-string with to-string in the string.
The case (verilog-string-replace-matches \"o\" \"oo\" nil nil \"foobar\")
will break, as the o's continuously replace.  xa -> x works ok though."
  ;; Hopefully soon to a emacs built-in
  (let ((start 0))
    (while (string-match from-string string start)
      (setq string (replace-match to-string fixedcase literal string)
	    start (min (length string) (match-end 0))))
    string))

(defsubst verilog-string-remove-spaces (string)
  "Remove spaces surrounding the string"
  (save-match-data
    (setq string (verilog-string-replace-matches "^\\s-+" "" nil nil string))
    (setq string (verilog-string-replace-matches "\\s-+$" "" nil nil string))
    string))

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
	  (and (verilog-skip-backward-comment-or-string)
	       (progn
		 (store-match-data '(nil nil))
		 (if BOUND
		     (> (point) BOUND)
		   t)
		 )
	       )
	  )
    )
  (match-end 0))

(defsubst verilog-re-search-forward-quick (regexp bound noerror)
  "Like verilog-re-search-forward, but trashes match data and
is faster for regexps that don't match much.
This may at some point use text properties to ignore comments,
so there may be a large up front penalty for the first search."
  (let (pt)
    (while (and (not pt)
		(re-search-forward regexp bound noerror))
      (if (not (verilog-inside-comment-p))
	  (setq pt (match-end 0))))
    pt))

(defsubst verilog-re-search-backward-quick (regexp bound noerror)
  "Like verilog-re-search-forward, but trashes match data and
is faster for regexps that don't match much.
This may at some point use text properties to ignore comments,
so there may be a large up front penalty for the first search."
  (let (pt)
    (while (and (not pt)
		(re-search-backward regexp bound noerror))
      (if (not (verilog-inside-comment-p))
	  (setq pt (match-end 0))))
    pt))

(defsubst verilog-get-beg-of-line (&optional arg)
  (save-excursion
    (beginning-of-line arg)
    (point)))

(defsubst verilog-get-end-of-line (&optional arg)
  (save-excursion
    (end-of-line arg)
    (point)))

(defun verilog-inside-comment-p ()
  "Check if point inside a nested comment."
  (save-excursion
    (let ((st-point (point)) hitbeg)
      (or (search-backward "//" (verilog-get-beg-of-line) t)
	  (if (progn
		;; This is for tricky case //*, we keep searching if /* is proceeded by // on same line
		(while (and (setq hitbeg (search-backward "/*" nil t))
			    (progn (forward-char 1) (search-backward "//" (verilog-get-beg-of-line) t))))
		hitbeg)
	      (not (search-forward "*/" st-point t)))))))

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

;;;
;;;  Mode
;;;

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
 verilog-minimum-comment-distance (default 10)
    Minimum distance (in lines) between begin and end required before a comment
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
  (setq verilog-mode-syntax-table (make-syntax-table))
  (verilog-populate-syntax-table verilog-mode-syntax-table)
  ;; add extra comment syntax
  (verilog-setup-dual-comments verilog-mode-syntax-table)
  (set-syntax-table verilog-mode-syntax-table)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'verilog-indent-line-relative)
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
  ;; Stuff for autos
  (add-hook 'write-contents-hooks 'verilog-auto-save-check) ; already local
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
  (if (or (verilog-in-comment-or-string-p)
	  (verilog-in-escaped-name-p))
      () 
    (save-excursion
      (beginning-of-line)
      (verilog-forward-ws&directives)
      (verilog-indent-line))
    (if (and verilog-auto-newline
	     (not (verilog-parenthesis-depth)))
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
  (if (or verilog-tab-always-indent
	  (save-excursion
	    (skip-chars-backward " \t")
	    (bolp)))
      (let* (
	     (oldpnt (point))
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
            (back-to-indentation)
	  (cond ((not verilog-tab-to-comment))
		((not (eolp))
		 (end-of-line))
		(t
		 (indent-for-comment)
		 (when (and (eolp) (= oldpnt (point)))
					; kill existing comment
		   (beginning-of-line)
		   (re-search-forward comment-start-skip oldpnt 'move)
		   (goto-char (match-beginning 0))
		   (skip-chars-backward " \t")
		   (kill-region (point) oldpnt)
		   ))))
	)
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

(defun verilog-get-beg-of-defun (&optional warn)
  (save-excursion
    (cond ((verilog-re-search-forward-quick verilog-defun-re nil t)
	   (point))
	  (warn (error "Can't find module beginning in %s" (or buffer-file-name (buffer-name)))
		(point-max)))))
(defun verilog-get-end-of-defun (&optional warn)
  (save-excursion
    (cond ((verilog-re-search-forward-quick verilog-end-defun-re nil t)
	   (point))
	  (warn (error "Can't find endmodule in %s" (or buffer-file-name (buffer-name)))
		(point-max)))))

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
		(verilog-backward-syntactic-ws)
		(setq pt (point))
		(not (bolp))
		(not (= (preceding-char) ?\;)))
      )
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
	    (if (> (count-lines (point) b) verilog-minimum-comment-distance)
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
			      (> (count-lines here there) verilog-minimum-comment-distance))
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
		    (setq width "\\(\\s-*\\(\\[[^]]*\\]\\)\\|\\(real\\(time\\)?\\)\\|\\(integer\\)\\|\\(time\\)\\)?")
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

(defun verilog-expand-vector ()
  "Take a signal vector on the current line and expand it to multiple lines.
Useful for creating tri's and other expanded fields."
  (interactive)
  (verilog-expand-vector-internal "[" "]"))

(defun verilog-expand-vector-internal (bra ket)
  "Given a start brace and end brace, expand one line into many lines."
  (interactive)
  (save-excursion
    (forward-line 0)
    (let ((signal-string (buffer-substring (point)
					   (progn 
					     (end-of-line) (point)))))
      (if (string-match (concat "\\(.*\\)"
				(regexp-quote bra)
				"\\([0-9]*\\)\\(:[0-9]*\\|\\)\\(::[0-9---]*\\|\\)"
				(regexp-quote ket)
				"\\(.*\\)$") signal-string)
	  (let* ((sig-head (match-string 1 signal-string))
		 (vec-start (string-to-int (match-string 2 signal-string)))
		 (vec-end (if (= (match-beginning 3) (match-end 3))
			      vec-start
			    (string-to-int (substring signal-string (1+ (match-beginning 3)) (match-end 3)))))
		 (vec-range (if (= (match-beginning 4) (match-end 4))
				1
			      (string-to-int (substring signal-string (+ 2 (match-beginning 4)) (match-end 4)))))
		 (sig-tail (match-string 5 signal-string))
		 vec)
	    ;; Decode vectors
	    (setq vec nil)
	    (if (< vec-range 0)
		(let ((tmp vec-start))
		  (setq vec-start vec-end
			vec-end tmp
			vec-range (- vec-range))))
	    (if (< vec-end vec-start)
		(while (<= vec-end vec-start)
		  (setq vec (append vec (list vec-start)))
		  (setq vec-start (- vec-start vec-range)))
	      (while (<= vec-start vec-end)
		(setq vec (append vec (list vec-start)))
		(setq vec-start (+ vec-start vec-range))))
	    ;;
	    ;; Delete current line
	    (delete-region (point) (progn (forward-line 0) (point)))
	    ;;
	    ;; Expand vector
	    (while vec
	      (insert (concat sig-head bra (int-to-string (car vec)) ket sig-tail "\n"))
	      (setq vec (cdr vec)))
	    (delete-char -1)
	    ;;
	    )))))

(defun verilog-strip-comments ()
  "Strip all comments from the verilog code."
  (interactive)
  (goto-char (point-min))
  (while (re-search-forward "//" nil t)
    (let ((bpt (- (point) 2)))
      (end-of-line)
      (delete-region bpt (point))))
  ;;
  (goto-char (point-min))
  (while (re-search-forward "/\\*" nil t)
    (let ((bpt (- (point) 2)))
      (re-search-forward "\\*/")
      (delete-region bpt (point))))
  )

(defun verilog-one-line ()
  "Converts structural verilog instances to occupy one line."
  (interactive)
  (goto-char (point-min))
  (while (re-search-forward "\\([^;]\\)[ \t]*\n[ \t]*" nil t)
	(replace-match "\\1 " nil nil)))

(defun verilog-verilint-off ()
  "Convert a verilint warning line into a disable statement.
	(W240)  pci_bfm_null.v, line  46: Unused input: pci_rst_
   becomes:
	//Verilint 240 off // WARNING: Unused input
"
  (interactive)
  (save-excursion
    (beginning-of-line)
    (when (looking-at "\\(.*\\)([WE]\\([0-9A-Z]+\\)).*,\\s +line\\s +[0-9]+:\\s +\\([^:\n]+\\):?.*$")
      (replace-match (format
		      ;; %3s makes numbers 1-999 line up nicely
		      "\\1//Verilint %3s off // WARNING: \\3"
		      (match-string 2)))
      (verilog-indent-line))))

(defun verilog-auto-save-compile ()
  "Update automatics with \\[verilog-auto],
save the buffer, and compile to check syntax."
  (interactive)
  (verilog-auto)	; Always do it for saftey
  (save-buffer)
  (compile compile-command))


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

(defun verilog-continued-line-1 (lim)
  "Return true if this is a continued line.
   Set point to where line starts"
  (let ((continued 't))
    (if (eq 0 (forward-line -1))
	(progn
	  (end-of-line)
	  (verilog-backward-ws&directives lim)
	  (if (bobp)
	      (setq continued nil)
	    (setq continued (verilog-backward-token))
	    )
	  )
      (setq continued nil)
      )
    continued)
  )

(defun verilog-calculate-indent ()
  "Calculate the indent of the current Verilog line, through examination
of previous lines.  Once a line is found that is definitive as to the
type of the current line, return that lines' indent level and it's
type. Return a list of two elements: (INDENT-TYPE INDENT-LEVEL)."
  (save-excursion
    (let* ((starting_position (point))
	   (par 0) 
	   (begin (looking-at "[ \t]*begin\\>"))
	   (lim (save-excursion (verilog-re-search-backward "\\(\\<begin\\>\\)\\|\\(\\<module\\>\\)" nil t)))
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
;		   (if (/= 0 (verilog-parenthesis-depth)) (progn (setq par 1) (throw 'nesting 'block)))

		   ;; See if we are continuing a previous line
		   (while t
		     ;; trap out if we crawl off the top of the buffer
		     (if (bobp) (throw 'nesting 'cpp))

		     (if (verilog-continued-line-1 lim)
			 (let ((sp (point)))
			   (if (and
				(not (looking-at verilog-complete-reg))
				(verilog-continued-line-1 lim))
			       (progn (goto-char sp)
				      (throw 'nesting 'cexp))
			     (goto-char sp))
			   
			   (if (and begin
				    (not verilog-indent-begin-after-if)
				    (looking-at verilog-no-indent-begin-re))
			       (progn
				 (beginning-of-line)
				 (skip-chars-forward " \t") 
				 (throw 'nesting 'statement))
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
;;				 verilog-ends =>  else|if|end|join|endcase|endtable|endspecify|endfunction|endtask
				 (cond 
				  ((match-end 3) ; end
				   ;; Search back for matching begin
				   (setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" )
				   )
				  ((match-end 5) ; endcase
				   ;; Search back for matching case
				   (setq reg "\\(\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" )
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
				  ((match-end 4) ; join
				   ;; Search back for matching fork
				   (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" )
				   )
				  ((match-end 6) ; endtable
				   ;; Search back for matching table
				   (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" )
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
    (let* ((lim (or lim (point-min))) (here lim) )
      (if (< lim (point))
	  (progn
	    (narrow-to-region lim (point))
	    (while (/= here (point))
	      (setq here (point))
	      (forward-comment (-(buffer-size)))
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

(defun verilog-in-comment-p ()
 "Return true if in a star or // comment"
 (let ((state 
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (or (nth 4 state) (nth 7 state)))
 )
(defun verilog-in-star-comment-p ()
 "Return true if in a star comment"
 (let ((state 
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (nth 4 state))
 )

(defun verilog-in-comment-or-string-p ()
 "Return true if in a string or comment"
 (let ((state 
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (or (nth 3 state) (nth 4 state) (nth 7 state))) ; Inside string or comment
 )

(defun verilog-in-escaped-name-p ()
 "Return true if in an escaped name"
 (save-excursion
   (backward-char)
   (skip-chars-backward "^ \t\n")
   (if (= (char-after (point) ) ?\\ )
       t
     nil)
   )
 )

(defun verilog-in-paren ()
 "Return true if in a parenthetical expression"
 (let ((state 
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (/= 0 (nth 0 state)))
 )
(defun verilog-parenthesis-depth ()
 "Return non zero if in parenthetical-expression"
 (save-excursion
   (nth 1 (parse-partial-sexp (point-min) (point)))))

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
  (let ((indent-str)
	(sp (point)))
    (if (looking-at "^[ \t]*$")
	(cond  ;- A blank line; No need to be too smart.
	 ((bobp)
	  (setq indent-str (list 'cpp 0)))
	 ((verilog-continued-line)
	  (let ((sp1 (point)))
	    (if (verilog-continued-line)
		(progn (goto-char sp)
		       (setq indent-str (list 'statement (verilog-indent-level))))
	      (goto-char sp1)
	      (setq indent-str (list 'block (verilog-indent-level))))
	    )
	  (goto-char sp)
	  )
	 ((goto-char sp)
	  (setq indent-str (verilog-calculate-indent))))
      (progn (skip-chars-forward " \t")
	     (setq indent-str (verilog-calculate-indent)))
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
	 ((or
	   (= (preceding-char) ?\,)
	   (= (preceding-char) ?\])
	   (save-excursion
	     (verilog-beg-of-statement-1)
	     (looking-at verilog-declaration-re)))
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
	    (verilog-beg-of-statement-1)
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
    (let (par-pos)
      (beginning-of-line)
      (setq par-pos (verilog-parenthesis-depth))
      (while par-pos
	(goto-char par-pos)
	(beginning-of-line)	    
	(setq par-pos (verilog-parenthesis-depth)))
      (skip-chars-forward " \t")
      (current-column))))


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
      (verilog-re-search-forward ":" nil t)
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
		(if (verilog-re-search-forward "[[#`]" p 'move)
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
	     ((verilog-continued-line-1 start)
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
	  (skip-chars-forward " \t")
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
		(if (verilog-re-search-forward "[[#`]" p 'move)
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
      (if (re-search-backward " /\\* \[#-\]# \[a-zA-Z\]+ \[0-9\]+ ## \\*/" b t) 
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
The default is a name found in the buffer around point.
If search fails, other files are checked based on verilog-library-directories."
  (interactive)
  (let* ((default (verilog-get-default-symbol))
	 ;; The following variable is used in verilog-comp-function
	 (verilog-buffer-to-use (current-buffer))
	 (label (if (not (string= default ""))
		    ;; Do completion with default
		    (completing-read (concat "Label: (default " default ") ")
				     'verilog-comp-defun nil nil "")
		  ;; There is no default value. Complete without it
		  (completing-read "Label: "
				   'verilog-comp-defun nil nil "")))
	 pt)
    ;; If there was no response on prompt, use default value
    (if (string= label "")
	(setq label default))
    ;; Goto right place in buffer if label is not an empty string
    (or (string= label "")
	(progn
	  (save-excursion
	    (goto-char (point-min))
	    (setq pt (re-search-forward (verilog-build-defun-re label t) nil t)))
	  (when pt
	    (goto-char pt)
	    (beginning-of-line))
	  pt)
	(verilog-goto-defun-file label)
	)))

;; Eliminate compile warning
(eval-when-compile
  (if (not (boundp 'occur-pos-list))
      (defvar occur-pos-list nil "Backward compatibility occur positions.")))
  
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

;;;; Added by Subbu Meiyappan for Header

(defun verilog-header ()
  "Insert a standard Verilog file header."
  (interactive)
  (let ((start (point)))
  (insert "\
//-----------------------------------------------------------------------------
// Title         : <title>
// Project       : <project>
//-----------------------------------------------------------------------------
// File          : <filename>
// Author        : <author>
// Created       : <credate>
// Last modified : <moddate>
//-----------------------------------------------------------------------------
// Description :
// <description>
//-----------------------------------------------------------------------------
// Copyright (c) 1998 by <company> This model is the confidential and
// proprietary property of <company> and the possession or use of this
// file requires a written license from <company>.
//------------------------------------------------------------------------------
// Modification history :
// <modhist>
//-----------------------------------------------------------------------------

")
    (goto-char start)
    (search-forward "<filename>")
    (replace-match (buffer-name) t t)
    (search-forward "<author>") (replace-match "" t t)
    (insert (user-full-name))     
    (insert "  <" (user-login-name) "@" (system-name) ">")
    (search-forward "<credate>") (replace-match "" t t)
    (insert-date)
    (search-forward "<moddate>") (replace-match "" t t)
    (insert-date)
    (search-forward "<modhist>") (replace-match "" t t)
    (insert-date)
    (insert " : created")
    (goto-char start)
    (let (string)
      (setq string (read-string "title: "))
      (search-forward "<title>")
      (replace-match string t t)
      (setq string (read-string "project: " verilog-project))
      (make-variable-buffer-local 'verilog-project)
      (setq verilog-project string)
      (search-forward "<project>")
      (replace-match string t t)
      (setq string (read-string "Company: " verilog-company))
      (make-variable-buffer-local 'verilog-company)
      (setq verilog-company string)
      (search-forward "<company>")
      (replace-match string t t)
      (search-forward "<company>")
      (replace-match string t t)
      (search-forward "<company>")
      (replace-match string t t)
      (search-backward "<description>")
      (replace-match "" t t)
  )))

;; verilog-header Uses the insert-date function 

(defun insert-date ()
  "Insert date from the system."
  (interactive)
  (let ((timpos))
    (setq timpos (point))
    (if verilog-date-scientific-format
	(shell-command  "date \"+@%Y/%m/%d\"" t)
      (shell-command  "date \"+@%d.%m.%Y\"" t))
    (search-forward "@")
    (delete-region timpos (point))
    (end-of-line))
    (delete-char 1)
  )


;;;
;;; Signal list parsing
;;;

(defun verilog-signals-not-in (in-list not-list)
  "Return list of signals in IN-LIST that aren't also in NOT-LIST.
Signals must be in standard (base vector) form."
  (let (out-list)
    (while in-list
      (if (not (assoc (car (car in-list)) not-list))
	  (setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    (nreverse out-list)))
;;;(verilog-signals-not-in '(("A" "") ("B" "") ("DEL" "[2:3]")) '(("DEL" "") ("EXT" "")))

(defun verilog-signals-memory (in-list)
  "Return list of signals in IN-LIST that are memoried (multidimensional)."
  (let (out-list)
    (while in-list
      (if (nth 3 (car in-list))
	  (setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    out-list))
;;;(verilog-signals-memory '(("A" nil nil "[3:0]")) '(("B" nil nil nil)))

(defun verilog-signals-combine-bus (in-list)
  "Return a list of signals in IN-LIST, with all duplicates removed, and with
busses combined.  For example A[2] and A[1] become A[2:1]."
  (let ((combo "")
	out-list signal highbit lowbit svhighbit svlowbit comment svbusstring bus)
      ;; Shove signals so duplicated signals will be adjacent
      (setq in-list (sort in-list (function (lambda (a b) (string< (car a) (car b))))))
      (while in-list
	(setq signal (nth 0 (car in-list))
	      bus (nth 1 (car in-list))
	      comment (nth 2 (car in-list)))
	(cond ((and bus 
		    (or (and (string-match "\\[\\([0-9]+\\):\\([0-9]+\\)\\]" bus)
			     (setq highbit (string-to-int (match-string 1 bus))
				   lowbit  (string-to-int (match-string 2 bus))))
			(and (string-match "\\[\\([0-9]+\\)\\]" bus)
			     (setq highbit (string-to-int (match-string 1 bus))
				   lowbit  highbit))))
	       ;; Combine bits in bus
	       (if svhighbit
		   (setq svhighbit (max highbit svhighbit)
			 svlowbit  (min lowbit  svlowbit))
		 (setq svhighbit highbit
		       svlowbit  lowbit))
	       )
	      (bus
	       ;; String, probably something like `preproc:0
	       (setq svbusstring bus)))
	;; Next
	(setq in-list (cdr in-list))
	(cond ((and in-list (equal (nth 0 (car in-list)) signal))
	       ;; Combine with this signal
	       (if (and svbusstring (not (equal svbusstring (nth 1 (car in-list)))))
		   (message (concat "Warning, can't merge into single bus " signal bus
				    ", the AUTOs may be wrong")))
	       (setq combo ", ...")
	       )
	      (t ;; Doesn't match next signal, add to que, zero in prep for next
	       (setq out-list (cons (list signal
					  (or svbusstring 
					      (if svhighbit (concat "[" svhighbit ":" svlowbit "]")))
					  (concat comment combo))
				    out-list)
		     svhighbit nil svbusstring nil combo ""))))
      ;;
      out-list))

;;;
;;; Port/Wire/Etc Reading
;;;

(defun verilog-read-inst-module ()
  "Return module_name when point is inside instantiation"
  (save-excursion
    (search-backward "(")
    ;; Skip over instantiation name
    (verilog-re-search-backward-quick "\\b[a-zA-Z0-9`_\$]" nil nil)
    (skip-chars-backward "a-zA-Z0-9`_$")
    (verilog-re-search-backward-quick "\\b[a-zA-Z0-9`_)\$]" nil nil)
    ;; Check for parameterized instantiations
    (when (looking-at ")")
      (search-backward "(")
      (verilog-re-search-backward-quick "\\b[a-zA-Z0-9`_\$]" nil nil))
    (skip-chars-backward "a-zA-Z0-9'_$")
    (looking-at "[a-zA-Z0-9`_\$]+")
    ;; Important: don't use match string, this must work with emacs 19 font-lock on
    (buffer-substring-no-properties (match-beginning 0) (match-end 0))))

(defun verilog-read-inst-name ()
  "Return instance_name when point is inside instantiation.
Or, return module name when after its ( or ;"
  (save-excursion
    (re-search-backward "[(;]")
    (verilog-re-search-backward-quick "\\b[a-zA-Z0-9`_\$]" nil nil)
    (skip-chars-backward "a-zA-Z0-9`_$")
    (looking-at "[a-zA-Z0-9`_\$]+")
    ;; Important: don't use match string, this must work with emacs 19 font-lock on
    (buffer-substring-no-properties (match-beginning 0) (match-end 0))))

(defun verilog-read-auto-param ()
  "Return parameter inside auto"
  (save-excursion
    ;; /*AUTOPUNT("parameter")*/
    (search-backward "(")
    (if (looking-at "(\\s *\"\\([^\"]*\\)\"")
	(match-string 1)
      nil)))

(defun verilog-read-decls ()
  "Return a array of [outputs inouts inputs wire reg assign const] used in the current
module that the point is over."
  (let ((end-mod-point (or (verilog-get-end-of-defun t) (point-max)))
	(functask 0) (paren 0)
	sigs-in sigs-out sigs-inout sigs-wire sigs-reg sigs-assign sigs-const
	vec expect-signal keywd newsig rvalue)
    (save-excursion
      (verilog-beg-of-defun)
      (setq sigs-const (verilog-read-auto-constants (point) end-mod-point))
      (while (< (point) end-mod-point)
	;;(if dbg (setq dbg (cons (format "Pt %s  Vec %s   Kwd'%s'\n" (point) vec keywd) dbg)))
	(cond
	 ((looking-at "//")
	  (search-forward "\n"))
	 ((looking-at "/\\*")
	  (or (search-forward "*/")
	      (error "Unmatched /* */, at char %d in %s" (point) (buffer-name))))
	 ((eq ?\" (following-char))
	  (or (re-search-forward "[^\\]\"" nil t)	;; don't forward-char first, since we look for a non backslash first
	      (error "Unmatched quotes, at char %d in %s" (point) (buffer-name))))
	 ((eq ?\; (following-char))
	  (setq vec nil expect-signal nil newsig nil paren 0 rvalue nil)
	  (forward-char 1))
	 ((eq ?= (following-char))
	  (setq rvalue t newsig nil)
	  (forward-char 1))
	 ((and rvalue
	       (cond ((and (eq ?, (following-char))
			   (eq paren 0))
		      (setq rvalue nil)
		      (forward-char 1)
		      t)
		     ;; ,'s can occur inside {} & funcs
		     ((looking-at "[{(]")
		      (setq paren (1+ paren))
		      (forward-char 1)
		      t)
		     ((looking-at "[})]")
		      (setq paren (1- paren))
		      (forward-char 1)
		      t)
		     )))
	 ((looking-at "\\s-*\\(\\[[^]]+\\]\\)")
	  (goto-char (match-end 0))
	  (cond (newsig	; Memory, not just width.  Patch last signal added's memory (nth 3)
		 (setcar (cdr (cdr (cdr newsig))) (match-string 1)))
		(t ;; Bit width
		 (setq vec (verilog-string-replace-matches 
			    "\\s-+" "" nil nil (match-string 1))))))
	 ((looking-at "\\s-*\\([a-zA-Z0-9`_$]+\\)")
	  (goto-char (match-end 0))
	  (setq keywd (match-string 1))
	  (cond ((equal keywd "input")
		 (setq vec nil expect-signal 'sigs-in))
		((equal keywd "output")
		 (setq vec nil expect-signal 'sigs-out))
		((equal keywd "inout")
		 (setq vec nil expect-signal 'sigs-inout))
		((equal keywd "wire")
		 (setq vec nil expect-signal 'sigs-wire))
		((equal keywd "reg")
		 (setq vec nil expect-signal 'sigs-reg))
		((equal keywd "assign")
		 (setq vec nil expect-signal 'sigs-assign))
		((or (equal keywd "supply0")
		     (equal keywd "supply1")
		     (equal keywd "supply")
		     (equal keywd "parameter"))
		 (setq vec nil expect-signal 'sigs-const))
		((or (equal keywd "function")
		     (equal keywd "task"))
		 (setq functask (1+ functask)))
		((or (equal keywd "endfunction")
		     (equal keywd "endtask"))
		 (setq functask (1- functask)))
		((and expect-signal
		      (eq functask 0)
		      (not rvalue))
		 ;; Add new signal to expect-signal's variable 
		 (setq newsig (list keywd vec nil nil))
		 (set expect-signal (cons newsig
					  (symbol-value expect-signal))))))
	 (t
	  (forward-char 1)))
	(skip-syntax-forward " "))
      ;; Return arguments
      (vector (nreverse sigs-out)
	      (nreverse sigs-inout)
	      (nreverse sigs-in)
	      (nreverse sigs-wire)
	      (nreverse sigs-reg)
	      (nreverse sigs-assign)
	      (nreverse sigs-const)
	      ))))

(defun verilog-read-sub-decls-line (comment)
  ;; For read-sub-decl, read lines of port defs until none match anymore
  (let (sigs)
    (while (or
	    (if (looking-at "\\s-*\\.[^(]*(\\s-*\\([^[({)]*\\)\\s-*)")
		(let ((sig (verilog-string-remove-spaces (match-string 1)))
		      vec)
		  (or (equal sig "")
		      (setq sigs (cons (list sig vec comment)
				       sigs)))))
	    (if (looking-at "\\s-*\\.[^(]*(\\s-*\\([^[({)]*\\)\\s-*\\(\\[[^]]+\\]\\)\\s-*)")
		(let ((sig (verilog-string-remove-spaces (match-string 1)))
		      (vec (match-string 2)))
		  (or (equal sig "")
		      (setq sigs (cons (list sig vec comment)
				       sigs)))))
	    (looking-at "\\s-*\\.[^(]*("))
      (forward-line 1))
    sigs))

(defun verilog-read-sub-decls ()
  "Return a array of [ outputs inouts inputs ] signals for modules that are
instantiated in this module.  For example if declare A A (.B(SIG)) and SIG
is a output, then it will be included in the list.

This only works on instantiations created with /*AUTOINST*/ converted by
\\[verilog-auto-instant].  Otherwise, it would have to read in the whole
component library to determine connectivity of the design."
  (save-excursion
    (let ((end-mod-point (verilog-get-end-of-defun t))
	  sigs-out sigs-inout sigs-in comment)
      (verilog-beg-of-defun)
      (while (search-forward "/*AUTOINST*/" end-mod-point t)
	(forward-line 1)
	(save-excursion
	  ;; Attempt to snarf a comment
	  (setq comment (concat (verilog-read-inst-name)
				" of " (verilog-read-inst-module) ".v")))
	;; This could have used a list created by verilog-auto-instant
	;; However I want it to be runable even if that function wasn't called before.
	(when (looking-at "\\s *// Outputs")
	  (forward-line 1)
	  (setq sigs-out (append (verilog-read-sub-decls-line
				  (concat "From " comment)) sigs-out)))
	(when (looking-at "\\s *// Inouts")
	  (forward-line 1)
	  (setq sigs-inout (append (verilog-read-sub-decls-line
				    (concat "To/From " comment)) sigs-inout)))
	(when (looking-at "\\s *// Inputs")
	  (forward-line 1)
	  (setq sigs-in (append (verilog-read-sub-decls-line
				 (concat "To " comment)) sigs-in)))
	)
      ;; Combine duplicate bits
      (vector (verilog-signals-combine-bus sigs-out)
	      (verilog-signals-combine-bus sigs-inout)
	      (verilog-signals-combine-bus sigs-in)))))

(defun verilog-read-auto-constants (beg end-mod-point)
  "Return a list of (constants) used in the region"
  ;; Insert new
  (save-excursion
    (let (sig-list tpl-end-pt)
      (goto-char beg)
      (while (re-search-forward "\\<AUTO_CONSTANT" end-mod-point t)
	(search-forward "(" end-mod-point)
	(setq tpl-end-pt (save-excursion
			   (backward-char 1)
			   (forward-sexp 1)   ;; Moves to paren that closes argdecl's
			   (backward-char 1)
			   (point)))
	(while (re-search-forward "\\s-*\\([a-zA-Z0-9`_$]+\\)\\s-*,*" tpl-end-pt t)
	  (setq sig-list (cons (list (match-string 1) nil nil) sig-list))))
      sig-list)))

(eval-when-compile
  ;; These are passed in a let, not global
  (if (not (boundp 'sigs-in))
      (defvar sigs-in nil) (defvar sigs-out nil)
      (defvar got-sig nil) (defvar got-rvalue nil)))
  
(defun verilog-read-always-signals-recurse
  (exit-keywd	;; Expression to stop at, nil if top level
   rvalue	;; right hand side of equal
   ignore-next  ;; Ignore next token, it's fake
   )
  "Recursive routine for parentheses/bracket matching."
  (let* ((semi-rvalue (equal "endcase" exit-keywd)) ;; true if after a ; we are looking for rvalue
	 keywd last-keywd sig-tolk sig-last-tolk gotend)
    ;;(if dbg (setq dbg (concat dbg (format "Recursion %S %S %S\n" exit-keywd rvalue ignore-next))))
    (while (not (or (eobp) gotend))
      (cond
       ((looking-at "//")
	(search-forward "\n"))
       ((looking-at "/\\*")
	(or (search-forward "*/")
	    (error "Unmatched /* */, at char %d in %s" (point) (buffer-name))))
       (t (setq keywd (buffer-substring-no-properties
		       (point) 
		       (save-excursion (when (eq 0 (skip-syntax-forward "w_"))
					 (forward-char 1))
				       (point)))
		sig-last-tolk sig-tolk
		sig-tolk nil)
	  ;;(if dbg (setq dbg (concat dbg (format "\tPt %S %S\t%S %S\n" (point) keywd rvalue ignore-next))))
	  (cond
	   ((equal keywd "\"")
	    (or (re-search-forward "[^\\]\"" nil t)
		(error "Unmatched quotes, at char %d in %s" (point) (buffer-name))))
	   ;; Final statement?
	   ((equal keywd (or exit-keywd ";"))
	    (setq gotend t)
	    (forward-char (length keywd)))
	   ((equal keywd ";")
	    (setq ignore-next nil rvalue semi-rvalue)
	    (forward-char 1))
	   ((equal keywd "'")
	    (setq ignore-next t)
	    (forward-char 1))
	   ((equal keywd ":")	;; Case statement, begin/end label, x?y:z
	    (cond ((equal "endcase" exit-keywd)  ;; case x: y=z; statement next
		   (setq ignore-next nil rvalue nil))
		  ((not rvalue)	;; begin label
		   (setq ignore-next t rvalue nil)))
	    (forward-char 1))
	   ((equal keywd "=")
	    (setq ignore-next nil rvalue t)
	    (forward-char 1))
	   ((equal keywd "?")
	    (forward-char 1)
	    (verilog-read-always-signals-recurse ":" rvalue nil))
	   ((equal keywd "[")
	    (forward-char 1)
	    (verilog-read-always-signals-recurse "]" t nil))
	   ((equal keywd "(")
	    (forward-char 1)
	    (cond (sig-last-tolk	;; Function call; zap last signal
		   (setq got-sig nil)))
	    (cond ((equal last-keywd "for")
		   (verilog-read-always-signals-recurse ";" nil nil)
		   (verilog-read-always-signals-recurse ";" t nil)
		   (verilog-read-always-signals-recurse ")" nil nil))
		  (t (verilog-read-always-signals-recurse ")" t nil))))
	   ((equal keywd "begin")
	    (skip-syntax-forward "w_")
	    (verilog-read-always-signals-recurse "end" nil nil)
	    (setq ignore-next nil rvalue semi-rvalue)
	    (if (not exit-keywd) (setq gotend t)))	;; top level begin/end
	   ((or (equal keywd "case")
		(equal keywd "casex")
		(equal keywd "casez"))
	    (skip-syntax-forward "w_")
	    (verilog-read-always-signals-recurse "endcase" t nil)
	    (setq ignore-next nil rvalue semi-rvalue)
	    (if (not exit-keywd) (setq gotend t)))	;; top level begin/end
	   ((string-match "^[$`a-zA-Z_]" keywd)	;; not exactly word constituant
	    (cond ((or ignore-next
		       (member keywd verilog-keywords)
		       (string-match "^\\$" keywd))	;; PLI task
		   (setq ignore-next nil))
		  (t
		   (when (string-match "^`" keywd)
		     ;; This only will work if the define is a simple signal, not
		     ;; something like a[b].  Sorry, it should be substituted into the parser
		     (setq keywd
			   (verilog-string-replace-matches
			    "\[[^0-9: \t]+\]" "" nil nil
			    (or (verilog-symbol-detick keywd nil) keywd)))
		     (if (or (string-match "^[0-9 \t]+$" keywd)
			     (string-match "^[0-9 \t]+'[hbdox]*[0-9 \t]*$" keywd))
			 (setq keywd nil))
		     )
		   (if got-sig (if got-rvalue
				   (setq sigs-in (cons got-sig sigs-in))
				 (setq sigs-out (cons got-sig sigs-out))))
		   (setq got-rvalue rvalue
			 got-sig (if (or (not keywd)
					 (assoc keywd (if got-rvalue sigs-in sigs-out)))
				     nil (list keywd nil nil))
			 sig-tolk t)))
	    (skip-syntax-forward "w_"))
	   (t
	    (forward-char 1)))
	  ;; End of non-comment tolken
	  (setq last-keywd keywd)
	  ))
      (skip-syntax-forward " "))
    ;;(if dbg (setq dbg (concat dbg (format "ENDRecursion %s\n" exit-keywd))))
    ))

(defun verilog-read-always-signals ()
  "Return a list of (inputs outputs) used in the current
always block that the point is over."
  ;; Insert new
  (save-excursion
    (let* (;;(dbg "")
	   sigs-in sigs-out
	   got-sig got-rvalue)	;; Found signal/rvalue; push if not function
      (search-forward ")")
      (verilog-read-always-signals-recurse nil nil nil)
      ;; Return what was found
      (if got-sig (if got-rvalue
		      (setq sigs-in (cons got-sig sigs-in))
		    (setq sigs-out (cons got-sig sigs-out))))
      ;;(if dbg (message dbg))
      (list sigs-in sigs-out))))

(defun verilog-read-instants ()
  "Return a list of ( ( file instance ) ... ) for the
module that the point is over."
  (verilog-beg-of-defun)
  (let* ((end-mod-point (verilog-get-end-of-defun t))
	 (state nil)
	 (instants-list nil))
    (save-excursion
      (while (< (point) end-mod-point)
	;; Stay at level 0, no comments
	(while (progn
		 (setq state (parse-partial-sexp (point) end-mod-point 0 t nil))
		 (or (> (car state) 0)	; in parens
		     (nth 5 state)		; comment
		     ))
	  (forward-line 1))
	(beginning-of-line)
	(if (looking-at "^\\s-*\\([a-zA-Z0-9`_$]+\\)\\s-+\\([a-zA-Z0-9`_$]+\\)\\s-*(")
	    ;;(if (looking-at "^\\(.+\\)$")
	    (let ((module (match-string 1))
		  (instant (match-string 2)))
	      (if (not (member module verilog-keywords))
		  (setq instants-list (cons (list module instant) instants-list)))))
	(forward-line 1)
	))
    instants-list))


(defun verilog-read-auto-template (module)
  "Looks for a auto_template for the instantiation of the given module.  If
found returns the signal name connections.  Return nil or list of
 ( (signal_name connection_name)... )
"
  (save-excursion
    ;; Find beginning
    (let (tpl-list tpl-end-pt)
      (cond ((or
	       (re-search-backward (concat "^\\s-*/?\\*?\\s-*" module "\\s-+AUTO_TEMPLATE") nil t)
	       (progn 
		 (goto-char (point-min))
		 (re-search-forward (concat "^\\s-*/?\\*?\\s-*" module "\\s-+AUTO_TEMPLATE") nil t)))
	     (search-forward "(")
	     (setq tpl-end-pt (save-excursion
				(backward-char 1)
				(forward-sexp 1)   ;; Moves to paren that closes argdecl's
				(backward-char 1)
				(point)))
	     ;;
	     (while (< (point) tpl-end-pt)
	       (when (looking-at "\\s-*\\.\\([a-zA-Z0-9`_$]+\\)\\s-*(\\(.*\\))\\s-*\\(,\\|)\\s-*;\\)")
		 (setq tpl-list (cons
				 (list
				  (match-string 1)
				  (match-string 2))
				 tpl-list)))
	       (forward-line 1))
	     ;;
	     tpl-list
	     )))))
;;;(progn (find-file "auto-template.v") (verilog-read-auto-template "ptl_entry"))

(defun verilog-read-defines (&optional filename)
  "Read `defines for the current file, or with a optional FILENAME, that
file.  If the filename is provided, verilog-library-directories will be
used to resolve it.

Defines must be simple text substitutions, one on a line, starting
at the beginning of the line.  Any ifdefs or multline comments around the
define are ignored.

Defines are stored inside emacs variables using the name vh-{definename}.

This function is useful for setting vh-* variables. The file variables
feature can be used to set defines that verilog-mode can see; put at the
*END* of your file something like:

// Local Variables:
// vh-macro:\"macro_definition\"
// End:

If macros are defined earlier in the same file and you want their values,
you can read them automatically (provided enable-local-eval is on):

// Local Variables:
// eval:(verilog-read-defines)
// eval:(verilog-read-defines \"group_standard_includes.v\")
// End:

Note these are only read when the file is first visited, you must use
\\[find-alternate-file] RET  to have these take effect after editing them!
"
  (let ((origbuf (current-buffer)))
    (save-excursion
      (when filename
	(let ((fns (verilog-library-filenames filename (buffer-file-name))))
	  (if fns
	      (set-buffer (find-file-noselect (car fns)))
	    (error (concat "Can't find verilog-read-defines file: " filename)))))
      (goto-char (point-min))
      (while (re-search-forward "^\\s-*`define\\s-+\\([a-zA-Z0-9_$]+\\)\\s-+\\(.*\\)$" nil t)
	(let ((mac (intern (concat "vh-" (match-string 1))))
	      (value (match-string 2)))
	  (setq value (verilog-string-replace-matches "\\s-*/[/*].*$" "" nil nil value))
	  (save-excursion
	    (set-buffer origbuf)
	    ;;(message "Define %s %s=%s" origbuf mac value) (sleep-for 1)
	    (set (make-variable-buffer-local mac) value)))))))

(defun verilog-read-includes ()
  "Read `includes for the current file.  This will find all of the `includes
which are at the beginning of lines, ignoring any ifdefs or multiline comments
around them.  verilog-read-defines is then performed on each included file.

It is often useful put at the *END* of your file something like:

// Local Variables:
// eval:(verilog-read-includes)
// End:

Note includes are only read when the file is first visited, you must use
\\[find-alternate-file] RET  to have these take effect after editing them!

It is good to get in the habit of including all needed files in each .v
file that needs it, rather then waiting for compile time.  This will aid
this process, Verilint, and readability.  To prevent defining the same
variable over and over when many modules are compiled together, put a test
around the inside each include file:

foo.v (a include):
	`ifdef _FOO_V	// include if not already included
	`else
	`define _FOO_V
	... contents of file
	`endif // _FOO_V
"
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "^\\s-*`include\\s-+\\([^ \t\n]+\\)" nil t)
      (let ((inc (verilog-string-replace-matches "\"" "" nil nil (match-string 1))))
	(verilog-read-defines inc)))))

(defun verilog-read-signals ()
  "Return a simple list of all possible signals in the file, overly aggressive but
fast.  Some macros and such are also found and included.  For dinotrace.el"
  (let (sigs-all keywd)
    (progn;save-excursion
      (goto-char (point-min))
      (while (re-search-forward "[\"/a-zA-Z_]" nil t)
	(forward-char -1)
	(cond
	 ((looking-at "//")
	  (search-forward "\n"))
	 ((looking-at "/\\*")
	  (search-forward "*/"))
	 ((eq ?\" (following-char))
	  (re-search-forward "[^\\]\""))	;; don't forward-char first, since we look for a non backslash first
	 ((looking-at "\\s-*\\([a-zA-Z0-9`_$]+\\)")
	  (goto-char (match-end 0))
	  (setq keywd (match-string 1))
	  (or (member keywd verilog-keywords)
	      (member keywd sigs-all)
	      (setq sigs-all (cons keywd sigs-all))))
	 (t (forward-char 1)))
	)
      ;; Return list
      sigs-all)))


;;;
;;; Module name lookup
;;;

(defun verilog-module-inside-filename-p (mod filename)
  "Return point if the given file has the module specified, else nil.
Allows version control to check out the file if need be."
  (and (or (file-exists-p filename)
	   (and (fboundp 'vc-backend) (vc-backend filename)))
       (let (pt)
	 (save-excursion
	   (set-buffer (find-file-noselect filename))
	   (goto-char (point-min))
	   (while (and 
		   ;; It may be tempting to look for verilog-defun-re, don't, it slows things down a lot!
		   (verilog-re-search-forward-quick "module" nil t)
		   (verilog-re-search-forward-quick "[(;]" nil t))
	     (if (equal mod (verilog-read-inst-name))
		 (setq pt (point))))
	   pt))))

(defun verilog-symbol-detick (mod wing-it)
  "Return a expanded SYMBOL name without any defines.
If the variable vh-{symbol} is defined, return that value.
If undefined, and WING-IT, return just SYMBOL without the tick, else nil."
  (when (string-match "^`" mod)
    (setq mod (substring mod 1))
    (if (boundp (intern (concat "vh-" mod)))
	(setq mod (eval (intern (concat "vh-" mod))))
      (if (not wing-it) (setq mod nil))))
  mod)
;;(verilog-symbol-detick "mod" nil)

(defun verilog-library-filenames (filename current)
  "Return a search path to find the given filename name.  Uses the
verilog-library-directories variable to build the path"
  (let ((ckdir verilog-library-directories)
	fn outlist)
    (while ckdir
      (setq fn (expand-file-name
		filename
		(expand-file-name (car ckdir) (file-name-directory current))))
      (if (file-exists-p fn)
	  (setq outlist (cons fn outlist)))
      (setq ckdir (cdr ckdir)))
    (nreverse outlist)))

(defun verilog-module-filenames (mod current)
  "Return a search path to find the given module name.  Uses the
verilog-library-directories variable to build the path"
  ;; Return search locations for it
  (append (list current)	; first, current buffer
	  (verilog-library-filenames (concat mod ".v") current)))

;;;
;;; Module Information
;;;
;;; Many of these functions work on "modi" a module information structure
;;; A modi is:  [module-name-string file-name begin-point]

(defvar verilog-cache-enabled t
  "If true, enable caching of signals, etc.  Set to nil for debugging to make things SLOW!")

(defvar verilog-modi-cache-list nil
  "Cache of ((Module Function) Buf-Tick Buf-Modtime Func-Returns)...
For speeding up verilog-modi-get-* commands.
Buffer-local.")

(defvar verilog-modi-cache-preserve-tick nil
  "Modification tick after which the cache is still considered valid.
Use verilog-preserve-cache's to set")
(defvar verilog-modi-cache-preserve-buffer nil
  "Modification tick after which the cache is still considered valid.
Use verilog-preserve-cache's to set")

(defun verilog-modi-current ()
  "Return the modi structure for the module currently at point"
  (let* (name pt)
    ;; read current module's name
    (save-excursion
      (verilog-re-search-backward-quick verilog-defun-re nil nil)
      (verilog-re-search-forward-quick "(" nil nil)
      (setq name (verilog-read-inst-name))
      (setq pt (point)))
    ;; return
    (vector name (or (buffer-file-name) (current-buffer)) pt)))

(defvar verilog-modi-lookup-last-mod nil "Cache of last module looked up")
(defvar verilog-modi-lookup-last-current nil "Cache of last current looked up")
(defvar verilog-modi-lookup-last-modi nil "Cache of last modi returned")

(defun verilog-modi-lookup (mod allow-cache)
  "Find the file and point at which a given module is defined.
Return modi if successful, else print message."
  (let* ((current (or (buffer-file-name) (current-buffer))))
    (cond ((and (equal verilog-modi-lookup-last-mod mod)
		(equal verilog-modi-lookup-last-current current)
		verilog-modi-lookup-last-modi
		verilog-cache-enabled
		allow-cache)
	   ;; ok as is
	   )
	  (t (let* ((realmod (verilog-symbol-detick mod t))
		    (orig-filenames (verilog-module-filenames realmod current))
		    (filenames orig-filenames)
		    pt)
	       (while (and filenames (not pt))
		 (if (not (setq pt (verilog-module-inside-filename-p realmod (car filenames))))
		     (setq filenames (cdr filenames))))
	       (cond (pt (setq verilog-modi-lookup-last-modi
			       (vector realmod (car filenames) pt)))
		     (t (setq verilog-modi-lookup-last-modi nil)
			(error (concat "Can't locate " mod " module definition"
				       (if (not (equal mod realmod))
					   (concat " (Expanded macro to " realmod ")")
					 "")
				       "\n    Check the verilog-library-directories variable."
				       "\n    I looked in:\n\t" (mapconcat 'concat orig-filenames "\n\t"))))
		     )
	       (setq verilog-modi-lookup-last-mod mod
		     verilog-modi-lookup-last-current current))))
    verilog-modi-lookup-last-modi
    ))

(defsubst verilog-modi-name (modi)
  (aref modi 0))

(defun verilog-modi-goto (modi)
  "Move point/buffer to specified modi"
  (or modi (error "Passed unfound modi to goto, check earlier"))
  (set-buffer (if (bufferp (aref modi 1))
		  (aref modi 1)
		(find-file-noselect (aref modi 1))))
  (or (equal major-mode `verilog-mode)	;; Put into verilog mode to get syntax
      (verilog-mode))
  (goto-char (aref modi 2)))

(defun verilog-goto-defun-file (mod)
  "Move point to the file at which a given module is defined."
  (interactive "sGoto File for Module: ")
  (let* ((modi (verilog-modi-lookup mod nil)))
    (when modi
      (verilog-modi-goto modi)
      (switch-to-buffer (current-buffer)))))

(defun verilog-modi-cache-results (modi function)
  "Run FUNCTION for given MODI.  Locate the module in a file.
Cache the output of function so next call may have faster access."
  (let (func-returns fass)
    (save-excursion
      (verilog-modi-goto modi)
      (if (and (setq fass (assoc (list (verilog-modi-name modi) function)
				 verilog-modi-cache-list))
	       ;; Destroy caching when incorrect; Modified or file changed
	       (not (and verilog-cache-enabled
			 (or (equal (buffer-modified-tick) (nth 1 fass))
			     (and verilog-modi-cache-preserve-tick
				  (<= verilog-modi-cache-preserve-tick  (nth 1 fass))
				  (equal  verilog-modi-cache-preserve-buffer (current-buffer))))
			 (equal (visited-file-modtime) (nth 2 fass)))))
	  (setq verilog-modi-cache-list nil
		fass nil))
      (cond (fass
	     ;; Found
	     (setq func-returns (nth 3 fass)))
	    (t
	     ;; Read from file
	     ;; Clear then restore any hilighting to make emacs19 happy
	     (let ((fontlocked (when (and (memq 'v19 verilog-emacs-features)
					  (boundp 'font-lock-mode)
					  font-lock-mode)
				 (font-lock-mode nil)
				 t)))
	       (setq func-returns (funcall function))
	       (when fontlocked (font-lock-mode t)))
	     ;; Cache for next time
	     (make-variable-buffer-local 'verilog-modi-cache-list)
	     (setq verilog-modi-cache-list
		   (cons (list (list (verilog-modi-name modi) function)
			       (buffer-modified-tick)
			       (visited-file-modtime)
			       func-returns)
			 verilog-modi-cache-list)))
	    ))
      ;;
      func-returns))

(defun verilog-modi-cache-add (modi function idx sig-list)
  "Update the modi's cache for given function so that the elt'th
return element of that function now contains the additional SIG-list
parameters."
  (let (fass)
    (save-excursion
      (verilog-modi-goto modi)
      (if (setq fass (assoc (list (verilog-modi-name modi) function)
			    verilog-modi-cache-list))
	  (let ((func-returns (nth 3 fass)))
	    (aset func-returns idx
		  (append sig-list (aref func-returns idx))))))))

(defmacro verilog-preserve-cache (&rest body)
  "Execute the BODY forms, allowing cache preservation cache within calls
inside the body.  This means that changes to the buffer will not result in
the cache being flushed.  If the changes affect the modsig state, they must
call the modsig-cache-add-* function, else the results of later calls may
be incorrect.  Without this, changes are assumed to be adding/removing
signals and invalidating the cache."
  `(let ((verilog-modi-cache-preserve-tick (buffer-modified-tick))
	 (verilog-modi-cache-preserve-buffer (current-buffer)))
     (progn ,@body)))

(defsubst verilog-modi-get-decls (modi)
  (verilog-modi-cache-results modi 'verilog-read-decls))

(defsubst verilog-modi-get-sub-decls (modi)
  (verilog-modi-cache-results modi 'verilog-read-sub-decls))

;;; Signal reading for given module
;;; Note these all take modi's - as returned from the modi-lookupFIX function
(defsubst verilog-modi-get-outputs (modi)
  (aref (verilog-modi-get-decls modi) 0))
(defsubst verilog-modi-get-inouts (modi)
  (aref (verilog-modi-get-decls modi) 1))
(defsubst verilog-modi-get-inputs (modi)
  (aref (verilog-modi-get-decls modi) 2))
(defsubst verilog-modi-get-wires (modi)
  (aref (verilog-modi-get-decls modi) 3))
(defsubst verilog-modi-get-regs (modi)
  (aref (verilog-modi-get-decls modi) 4))
(defsubst verilog-modi-get-assigns (modi)
  (aref (verilog-modi-get-decls modi) 5))
(defsubst verilog-modi-get-consts (modi)
  (aref (verilog-modi-get-decls modi) 6))
(defsubst verilog-modi-get-sub-outputs (modi)
  (aref (verilog-modi-get-sub-decls modi) 0))
(defsubst verilog-modi-get-sub-inouts (modi)
  (aref (verilog-modi-get-sub-decls modi) 1))
(defsubst verilog-modi-get-sub-inputs (modi)
  (aref (verilog-modi-get-sub-decls modi) 2))

;;; Combined
(defun verilog-modi-get-signals (modi)
  (append 
   (verilog-modi-get-outputs modi)
   (verilog-modi-get-inouts modi)
   (verilog-modi-get-inputs modi)
   (verilog-modi-get-wires modi)
   (verilog-modi-get-regs modi)
   (verilog-modi-get-assigns modi)
   (verilog-modi-get-consts modi)))

(defun verilog-modi-get-ports (modi)
  (append 
   (verilog-modi-get-outputs modi)
   (verilog-modi-get-inouts modi)
   (verilog-modi-get-inputs modi)))

(defsubst verilog-modi-cache-add-outputs (modi sig-list)
  (verilog-modi-cache-add modi 'verilog-read-decls 0 sig-list))
(defsubst verilog-modi-cache-add-inouts (modi sig-list)
  (verilog-modi-cache-add modi 'verilog-read-decls 1 sig-list))
(defsubst verilog-modi-cache-add-inputs (modi sig-list)
  (verilog-modi-cache-add modi 'verilog-read-decls 2 sig-list))
(defsubst verilog-modi-cache-add-wires (modi sig-list)
  (verilog-modi-cache-add modi 'verilog-read-decls 3 sig-list))
(defsubst verilog-modi-cache-add-regs (modi sig-list)
  (verilog-modi-cache-add modi 'verilog-read-decls 4 sig-list))

;;;
;;; Auto creation utilities
;;;

(defun verilog-auto-search-do (search-for func)
  "Search for the given auto text, and perform function where it occurs."
  (goto-char (point-min))
  (while (search-forward search-for nil t)
    (if (not (save-excursion
	       (goto-char (match-beginning 0))
	       (verilog-inside-comment-p)))
	(funcall func))))
  
(defun verilog-auto-re-search-do (search-for func)
  "Search for the given auto text, and perform function where it occurs."
  (goto-char (point-min))
  (while (re-search-forward search-for nil t)
    (if (not (save-excursion
	       (goto-char (match-beginning 0))
	       (verilog-inside-comment-p)))
	(funcall func))))
  
(defun verilog-insert-definition (sigs type indent-pt &optional dont-sort)
  "Print out a definition for a list of SIGNALS of the given TYPE,
with appropriate INPUT.  TYPE is normally wire/reg/output."
  (or dont-sort
      (setq sigs (sort (copy-alist sigs) (function (lambda (a b) (string< (car a) (car b)))))))
  (while sigs
    (let ((sig (car sigs)))
      (indent-to indent-pt)
      (insert type)
      (when (nth 1 sig)
	(insert " " (nth 1 sig)))
      (indent-to (max 24 (+ indent-pt 16)))
      (insert (concat (car sig) ";"))
      (if (not (nth 2 sig))
	  (insert "\n")
	(indent-to (max 48 (+ indent-pt 40)))
	(insert (concat "// " (nth 2 sig) "\n")))
      (setq sigs (cdr sigs)))))


;;;
;;; Auto deletion
;;;

(defun verilog-delete-autos-lined ()
  (let ((pt (point)))
    (forward-line 1)
    (when (and
	   (looking-at "\\s-*// Beginning")
	   (search-forward "// End of automatic" nil t))
      ;; End exists
      (end-of-line)
      (delete-region pt (point))
      (forward-line 1))
  ))

(defun verilog-delete-to-paren ()
  "Delete the automatic inst/sense/arg created by verilog-mode.
Deletion stops at the matching end parenthesis."
  (delete-region (point)
		 (save-excursion
		   (verilog-re-search-backward-quick "(" nil nil)
		   (forward-sexp 1)   ;; Moves to paren that closes argdecl's
		   (backward-char 1)
		   (point))))

(defun verilog-delete-auto ()
  "Delete the automatic outputs, regs, and wires created by verilog-mode.
Use \\[verilog-auto] to re-insert the updated AUTOs."
  (interactive)
  (save-excursion
    (if (buffer-file-name)
	(find-file-noselect (buffer-file-name)))	;; To check we have latest version
    ;; Remove those that have multi-line insertions
    (verilog-auto-re-search-do "/\\*AUTO\\(OUTPUTEVERY\\|WIRE\\|REG\\|INPUT\\|OUTPUT\\)\\*/"
			       'verilog-delete-autos-lined)
    ;; Remove those that have multi-line insertions with parameters
    (verilog-auto-re-search-do "/\\*AUTO\\(INOUTMODULE\\)([^)]*)\\*/"
			       'verilog-delete-autos-lined)
    ;; Remove those that are in parenthesis
    (verilog-auto-re-search-do "/\\*AUTO\\(ARG\\|INST\\|SENSE\\)\\*/"
			       'verilog-delete-to-paren)

    ;; Remove template comments ... anywhere in case was pasted after AUTOINST removed
    (goto-char (point-min))
    (while (re-search-forward "\\s-*// Templated$" nil t)
      (replace-match ""))))


;;;
;;; Auto save
;;;

(defun verilog-auto-save-check ()
  "On saving see if we need auto update"
  (cond ((not verilog-auto-save-policy)) ; disabled
	((not (save-excursion
		(save-match-data
		  (let ((case-fold-search nil))
		    (goto-char (point-min))
		    (re-search-forward "AUTO" nil t))))))
	((eq verilog-auto-save-policy 'force)
	 (verilog-auto))
	((not (buffer-modified-p)))
	((eq verilog-auto-update-tick (buffer-modified-tick))) ; up-to-date
	((eq verilog-auto-save-policy 'detect)
	 (verilog-auto))
	(t
	 (when (yes-or-no-p "AUTO statements not recomputed, do it now? ")
	   (verilog-auto))
	 ;; Don't ask again if didn't update
	 (set (make-local-variable 'verilog-auto-update-tick) (buffer-modified-tick))
	 ))
  nil)	;; Always return nil -- we don't write the file ourselves

;;;
;;; Auto creation
;;;

(defun verilog-auto-arg-ports (sigs message indent-pt)
  "Print a argument list"
  (when sigs
    (insert "\n")
    (indent-to indent-pt)
    (insert message)
    (insert "\n")
    (indent-to indent-pt)
    (while sigs
      (cond ((> (+ 2 (current-column) (length (nth 0 (car sigs)))) fill-column)
	     (insert "\n")
	     (indent-to indent-pt)))
      (insert (nth 0 (car sigs)) ", ")
      (setq sigs (cdr sigs)))))
  
(defun verilog-auto-arg ()
  "Replace the argument declarations at the beginning of the
module with ones automatically derived from input and output
statements.  This can be dangerous if the module is instantiated
using position-based connections, so use only name-based when
instantiating the resulting module.  Long lines are split based
on the fill-column, see \\[set-fill-column].

Limitations:
   Concatencation and outputting partial busses is not supported.

For example:

	module ex_arg (/*AUTOARG*/);
	  input i;
	  output o;
	endmodule
	
Typing \\[verilog-auto] will make this into:

	module ex_arg (/*AUTOARG*/
	  // Outputs
	  o,
	  // Inputs
	  i
	);
	  input i;
	  output o;
	endmodule
"
  (save-excursion
    (let ((modi (verilog-modi-current))
	  (pt (point)))
      (verilog-auto-arg-ports (verilog-modi-get-outputs modi)
			      "// Outputs"
			      verilog-indent-level-declaration)
      (verilog-auto-arg-ports (verilog-modi-get-inouts modi)
			      "// Inouts"
			      verilog-indent-level-declaration)
      (verilog-auto-arg-ports (verilog-modi-get-inputs modi)
			      "// Inputs"
			      verilog-indent-level-declaration)
      (save-excursion
	(if (re-search-backward "," pt t)
	    (delete-char 2)))
      (insert "\n")
      (indent-to verilog-indent-level-declaration)
      )))

(defun verilog-auto-inst-port-map (port-st)
  nil)

(defun verilog-auto-inst-port (port-st indent-pt tpl-list tpl-num)
  "Print out a instantiation connection for this port.  @ are instantiation numbers.
@\"(expression @)\" are evaluated, with @ as a variable."
  (let* ((port (car port-st))
	 (tpl-ass (or (assoc port tpl-list)
		      (verilog-auto-inst-port-map port-st)))
	 (tpl-net (concat port (nth 1 port-st))))
    (cond (tpl-ass
	   (setq tpl-net (nth 1 tpl-ass))
	   (cond ((string-match "@\".*[^\\]\"" tpl-net)
		  (while (string-match "@\"\\(\\([^\\\"]*\\(\\\\.\\)*\\)*\\)\"" tpl-net)
		    (setq tpl-net
			  (concat
			   (substring tpl-net 0 (match-beginning 0))
			   (save-match-data
			     (let ((expr (match-string 1 tpl-net)))
			       (setq expr (verilog-string-replace-matches "\\\\\"" "\"" nil nil expr))
			       (setq expr (verilog-string-replace-matches "@" tpl-num nil nil expr))
			       (prin1 (eval (car (read-from-string expr)))
				      (lambda (ch) ()))))
			   (substring tpl-net (match-end 0))))))
		 (t
		  (setq tpl-net (verilog-string-replace-matches "@" tpl-num nil nil tpl-net))
		  ))))
    (indent-to indent-pt)
    (insert "." port)
    (indent-to 40)
    (insert "(" tpl-net "),")
    (when tpl-ass
      (indent-to 64)
      (insert " // Templated"))
    (insert "\n")))
;;;(verilog-auto-inst-port (list "foo" "[5:0]") 10 (list (list "foo" "a@\"(% (+ @ 1) 4)\"a")) "3")
;;;(x "incom[@\"(+ (* 8 @) 7)\":@\"(* 8 @)\"]")
;;;(x ".out (outgo[@\"(concat (+ (* 8 @) 7) \\\":\\\" ( * 8 @))\"]));")

(defun verilog-auto-inst ()
  "Replace the argument calls inside an instantiation with ones
automatically derived from the module header of the instantiated netlist.

Limitations:
  This presumes a one-to-one port name to signal name mapping.

  Module names must be resolvable to filenames, either by being in the same
  directory, or by changing the variable verilog-library-directories.
  Macros `modname are translated through the vh-{name} emacs variable,
  if that is not found, it just ignores the `.

A simple example:

module ex_inst (o,i)
   output o;
   input i;
   inst inst (/*AUTOINST*/);
endmodule

Where somewhere the instantiated module is declared:

	module inst (o,i)
	   output [31:0] o;
	   input i;
	   wire [31:0] o = {32{i}};
	endmodule

Typing \\[verilog-auto] will make this into:

	module ex_inst (o,i)
	   output o;
	   input i;
	   inst inst (/*AUTOINST*/
		      // Outputs
		      .ov			(ov[31:0]),
		      // Inputs
		      .i			(i));
	endmodule

Where the list of inputs and outputs came from the inst module.

For multiple instantiations based upon a single template,

Create a commented out template:
	/*
	psm_mas AUTO_TEMPLATE (
		.PTL_MAPVALIDX		(PTL_MAPVALID[@]),
		.PTL_MAPVALIDP1X	(PTL_MAPVALID[@\"(% (+ 1 @) 4)\"]),
		);
	*/

where the @ character should be replaced by the instantiation number.  The
module name must be the same as the name of the module in the instantiation
name, and the code \"AUTO_TEMPLATE\" must be in these exact words and
capitalized.  Only signals that must be different for each instantiation
need to be listed.

If the syntax @\"( ... )\" is found, the expression in quotes will be
evaluated as a lisp expression, with @ replaced by the instantation number.
The example above would put @+1 modulo 4 into the brackets.  Quote all
double-quotes inside the expression with a leading backslash (\").

The above template will convert:

	psm_mas ms2m (/*AUTOINST*/);

Typing \\[verilog-auto] will make this into:

	psm_mas ms2m (/*AUTOINST*/
	    // Outputs
	    .PO_PSM_PFRAME_L		(PO_PSM_PFRAME_L),
	    .INSTDATAOUT		(INSTDATAOUT2),
	    .PTL_MAPVALIDX		(PTL_MAPVALID[2]),
	    .PTL_MAPVALIDP1X		(PTL_MAPVALID[3]),
	    ....
	    // Inputs
	    ....
	    .INSTDATA			(INSTDATA[2]),
	    .PI_PPAR64_L		(PI_PPAR64_L));

Note the @ character was replaced with the 2 from \"ms2m\".  Also, if a
signal wasn't in the template, it is assumed to be a direct connection.
"
  (save-excursion
    ;; Find beginning
    (let ((pt (point))
	  (indent-pt (save-excursion
		       (or (and (search-backward "(" nil t)  (1+ (current-column)))
			   (current-indentation))))
	  submod submodi inst tpl-list tpl-num)
      ;; Find module name that is instantiated
      (setq submod  (verilog-read-inst-module)
	    inst (verilog-read-inst-name))

      ;; Lookup position, etc of submodule
      ;; Note this may raise an error
      (when (setq submodi (verilog-modi-lookup submod t))
	;; If there's a number in the instantiation, it may be a argument to the
	;; automatic variable instantiation program.
	(setq tpl-num (if (string-match "[0-9]+" inst)
			  (substring inst (match-beginning 0) (match-end 0))
			"")
	      tpl-list (verilog-read-auto-template submod))
	;; Find submodule's signals and dump
	(insert "\n")
	(let ((sig-list (verilog-modi-get-outputs submodi)))
	  (when sig-list
	    (indent-to indent-pt)
	    (insert "// Outputs\n")	;; Note these are searched for in verilog-read-sub-decl
	    (mapcar (function (lambda (port) 
				(verilog-auto-inst-port port indent-pt tpl-list tpl-num)))
		    sig-list)))
	(let ((sig-list (verilog-modi-get-inouts submodi)))
	  (when sig-list
	    (indent-to indent-pt)
	    (insert "// Inouts\n")
	    (mapcar (function (lambda (port) 
				(verilog-auto-inst-port port indent-pt tpl-list tpl-num)))
		    sig-list)))
	(let ((sig-list (verilog-modi-get-inputs submodi)))
	  (when sig-list
	    (indent-to indent-pt)
	    (insert "// Inputs\n")
	    (mapcar (function (lambda (port) 
				(verilog-auto-inst-port port indent-pt tpl-list tpl-num)))
		    sig-list)))
	;; Kill extra semi
	(save-excursion
	  (cond ((re-search-backward "," pt t)
		 (delete-char 1)
		 (insert ");")
		 (search-forward "\n")	;; Added by inst-port
		 (delete-backward-char 1)
		 (if (search-forward ")" nil t) ;; From user, moved up a line
		     (delete-backward-char 1))
		 (if (search-forward ";" nil t) ;; Don't error if user had syntax error and forgot it
		     (delete-backward-char 1))
		 )
		(t
		 (delete-backward-char 1)	;; Newline Inserted above
		 )))
	))))

(defun verilog-auto-reg ()
  "Make register statements for any output that isn't already declared,
and isn't a wire output from a block.

Limitiations:
  This ONLY detects outputs of AUTOINSTants (see verilog-read-sub-decl).
  This does NOT work on memories, declare those yourself.  

A simple example:

	module ex_reg (o,i)
	   output o;
	   input i;
	   /*AUTOREG*/
	   always o <= i;
	endmodule

Typing \\[verilog-auto] will make this into:

	module a ()
	   output a;
	   input i;
	   /*AUTOREG*/
	   // Beginning of automatic regs (for this module's undeclared outputs)
	   reg			a;
	   // End of automatics
	   always a <= i;
	endmodule
"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (sig-list (verilog-signals-not-in
		      (verilog-modi-get-outputs modi)
		      (append (verilog-modi-get-wires modi)
			      (verilog-modi-get-regs modi)
			      (verilog-modi-get-assigns modi)
			      (verilog-modi-get-consts modi)
			      (verilog-modi-get-sub-outputs modi)
			      (verilog-modi-get-sub-inouts modi)
			      ))))
      (forward-line 1)
      (indent-to indent-pt)
      (insert "// Beginning of automatic regs (for this module's undeclared outputs)\n")
      (verilog-insert-definition sig-list "reg" indent-pt)
      (verilog-modi-cache-add-regs modi sig-list)
      (indent-to indent-pt)
      (insert "// End of automatics\n")
      )))

(defun verilog-auto-wire ()
  "Make wire statements for outputs of instantiations that aren't already
declared.  

Limitiations:
  This ONLY detects outputs of AUTOINSTants (see verilog-read-sub-decl).
  This does NOT work on memories, declare those yourself.  

A simple example (see verilog-auto-inst for what else is going on here):

	module ex_wire (o,i)
	   output o;
	   input i;
	   /*AUTOWIRE*/
           inst inst (/*AUTOINST*/);
	endmodule

Typing \\[verilog-auto] will make this into:

	module ex_wire (o,i)
	   output o;
	   input i;
	   /*AUTOWIRE*/
	   // Beginning of automatic wires (for undeclared instantiated-module outputs)
	   wire [31:0]		ov;			// From inst of inst.v
	   // End of automatics
	   inst inst (/*AUTOINST*/
		      // Outputs
		      .ov			(ov[31:0]),
		      // Inputs
		      .i			(i));
	   wire o = | ov;
	endmodule
"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (sig-list (verilog-signals-combine-bus 
		      (verilog-signals-not-in
		       (append (verilog-modi-get-sub-outputs modi)
			       (verilog-modi-get-sub-inouts modi))
		       (verilog-modi-get-signals modi)
		       ))))
      (forward-line 1)
      (indent-to indent-pt)
      (insert "// Beginning of automatic wires (for undeclared instantiated-module outputs)\n")
      (verilog-insert-definition sig-list "wire" indent-pt)
      (verilog-modi-cache-add-wires modi sig-list)
      (indent-to indent-pt)
      (insert "// End of automatics\n")
      )))

(defun verilog-auto-output ()
  "Make output statements for any output signal from an /*AUTOINST*/ that
isn't used elsewhere inside the module.  This is useful for modules which
only instantiate other modules.

Limitiations:
  This ONLY detects outputs of AUTOINSTants (see verilog-read-sub-decl).

  If any concatenation, or bitsubscripts are missing in the AUTOINSTant's
  instantiation, all bets are off.  (For example due to a AUTO_TEMPLATE).

A simple example (see verilog-auto-inst for what else is going on here):

	module ex_output (ov,i)
	   input i;
	   /*AUTOWIRE*/
	   inst inst (/*AUTOINST*/);
	endmodule

Typing \\[verilog-auto] will make this into:

	module ex_output (ov,i)
	   input i;
	   /*AUTOOUTPUT*/
	   // Beginning of automatic outputs (from unused autoinst outputs)
	   output [31:0]	ov;			// From inst of inst.v
	   // End of automatics
	   inst inst (/*AUTOINST*/
		      // Outputs
		      .ov			(ov[31:0]),
		      // Inputs
		      .i			(i));
	endmodule
"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (sig-list (verilog-signals-not-in
		      (verilog-modi-get-sub-outputs modi)
		      (append (verilog-modi-get-outputs modi)
			      (verilog-modi-get-inouts modi)
			      (verilog-modi-get-sub-inputs modi)
			      (verilog-modi-get-sub-inouts modi)
			      ))))
      (forward-line 1)
      (indent-to indent-pt)
      (insert "// Beginning of automatic outputs (from unused autoinst outputs)\n")
      (verilog-insert-definition sig-list "output" indent-pt)
      (verilog-modi-cache-add-outputs modi sig-list)
      (indent-to indent-pt)
      (insert "// End of automatics\n")
      )))

(defun verilog-auto-output-every ()
  "Make output statements for any signals that aren't primary inputs or
outputs already.  This makes every signal in the design a output.  This is
useful to get Synopsys to preserve every signal in the design, since it
won't optimize away the outputs.

A simple example:

	module ex_output_every (o,i,tempa,tempb)
	   output o;
	   input i;
	   /*AUTOOUTPUTEVERY*/
	   wire tempa = i;
	   wire tempb = tempa;
	   wire o = tempb;
	endmodule

Typing \\[verilog-auto] will make this into:

	module ex_output_every (o,i,tempa,tempb)
	   output o;
	   input i;
	   /*AUTOOUTPUTEVERY*/
	   // Beginning of automatic outputs (every signal)
	   output		tempb;
	   output		tempa;
	   // End of automatics
	   wire tempa = i;
	   wire tempb = tempa;
	   wire o = tempb;
	endmodule
"
  (save-excursion
    ;;Point must be at insertion point
    (let* ((indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (sig-list (verilog-signals-not-in
		      (verilog-modi-get-signals modi)
		      (verilog-modi-get-ports modi)
		      )))
      (forward-line 1)
      (indent-to indent-pt)
      (insert "// Beginning of automatic outputs (every signal)\n")
      (verilog-insert-definition sig-list "output" indent-pt)
      (verilog-modi-cache-add-outputs modi sig-list)
      (indent-to indent-pt)
      (insert "// End of automatics\n")
      )))

(defun verilog-auto-input ()
  "Make input statements for any input signal into an /*AUTOINST*/ that
isn't declared elsewhere inside the module.  This is useful for modules which
only instantiate other modules.

Limitiations:
  This ONLY detects outputs of AUTOINSTants (see verilog-read-sub-decl).

  If any concatenation, or bitsubscripts are missing in the AUTOINSTant's
  instantiation, all bets are off.  (For example due to a AUTO_TEMPLATE).

A simple example (see verilog-auto-inst for what else is going on here):

	module ex_input (ov,i)
	   output [31:0] ov;
	   /*AUTOINPUT*/
	   inst inst (/*AUTOINST*/);
	endmodule

Typing \\[verilog-auto] will make this into:

	module ex_input (ov,i)
	   output [31:0] ov;
	   /*AUTOINPUT*/
	   // Beginning of automatic inputs (from unused autoinst inputs)
	   input		i;			// From inst of inst.v
	   // End of automatics
	   inst inst (/*AUTOINST*/
		      // Outputs
		      .ov			(ov[31:0]),
		      // Inputs
		      .i			(i));
	endmodule
"
  (save-excursion
    (let* ((indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (sig-list (verilog-signals-not-in
		      (verilog-modi-get-sub-inputs modi)
		      (append (verilog-modi-get-inputs modi)
			      (verilog-modi-get-inouts modi)
			      (verilog-modi-get-wires modi)
			      (verilog-modi-get-regs modi)
			      (verilog-modi-get-consts modi)
			      (verilog-modi-get-sub-outputs modi)
			      (verilog-modi-get-sub-inouts modi)
			      ))))
      (forward-line 1)
      (indent-to indent-pt)
      (insert "// Beginning of automatic inputs (from unused autoinst inputs)\n")
      (verilog-insert-definition sig-list "input" indent-pt)
      (verilog-modi-cache-add-inputs modi sig-list)
      (indent-to indent-pt)
      (insert "// End of automatics\n")
      )))

(defun verilog-auto-inout-module ()
  "Take input/output/inout statements from the specified module and insert into
the current module.  This is useful for making null templates and shell modules
which need to have identical I/O with another module.  Any I/O which are already
defined in this module will not be redefined.

Limitiations:
  Concatencation and outputting partial busses is not supported.
  Module names must be resolvable to filenames.  See \\[verilog-auto-inst] for help.
  Signals are not inserted in the same order as in the original module, though they
  will appear to be in the same order to a AUTOINST instantiating either module.

A simple example:

	module ex_shell (/*AUTOARG*/)
	   /*AUTOINOUTMODULE(\"ex_main\")*/
	endmodule

	module ex_main (i,o,io)
          input i;
          output o;
          inout io;
        endmodule

Typing \\[verilog-auto] will make this into:

	module ex_shell (/*AUTOARG*/i,o,io)
	   /*AUTOINOUTMODULE(\"ex_main\")*/
           // Beginning of automatic in/out/inouts (from specific module)
           input i;
           output o;
           inout io;
	   // End of automatics
	endmodule
"
  (save-excursion
    (let* ((submod  (verilog-read-auto-param)) submodi)
      ;; Lookup position, etc of co-module
      ;; Note this may raise an error
      (when (setq submodi (verilog-modi-lookup submod t))
	(let* ((indent-pt (current-indentation))
	       (modi (verilog-modi-current))
	       (sig-list-i  (verilog-signals-not-in
			     (verilog-modi-get-inputs submodi)
			     (append (verilog-modi-get-inputs modi))))
	       (sig-list-o  (verilog-signals-not-in
			     (verilog-modi-get-outputs submodi)
			     (append (verilog-modi-get-outputs modi))))
	       (sig-list-io (verilog-signals-not-in
			     (verilog-modi-get-inouts submodi)
			     (append (verilog-modi-get-inouts modi)))))
	  (forward-line 1)
	  (indent-to indent-pt)
	  (insert "// Beginning of automatic in/out/inouts (from specific module)\n")
	  ;; Don't sort them so a upper AUTOINST will match the main module
	  (verilog-insert-definition sig-list-o  "output" indent-pt t)
	  (verilog-insert-definition sig-list-io "inout" indent-pt t)
	  (verilog-insert-definition sig-list-i  "input" indent-pt t)
	  (verilog-modi-cache-add-inputs modi sig-list-i)
	  (verilog-modi-cache-add-outputs modi sig-list-o)
	  (verilog-modi-cache-add-inouts modi sig-list-io)
	  (indent-to indent-pt)
	  (insert "// End of automatics\n")
	  )))))

(defun verilog-auto-sense ()
  "Replace the always (/*AUTOSENSE*/) sensitivity list with one
automatically derived from all inputs declared in the always statement.
Signals that are generated within the same always block are NOT placed into
the sensitivity list (see verilog-auto-sense-include-inputs).
Long lines are split based on the fill-column, see \\[set-fill-column].

Limitiations:
  The end of a always is considered to be a ; unless a begin/end is used.
  This is wrong for \"always if foo else bar\", so use begin/end pairs
  after always!

  Verilog does not allow memories (multidimensional arrays) in sensitivity
  lists.  AUTOSENSE will thus exclude them, and add a /*memory or*/ comment.

Constant signals:
  AUTOSENSE cannot always determine if a `define is a constant or a signal
  (it could be in a include file for example).  If a `define or other signal
  is put into the AUTOSENSE list and is not desired, use the AUTO_CONSTANT
  declaration anywhere in the module (parenthesis are required):

	/* AUTO_CONSTANT ( `this_is_really_constant_dont_autosense_it ) */

  Better yet, use a parameter, which will be understood to be constant
  automatically.

OOps!  
  If AUTOSENSE makes a mistake, please report it.  As a workaround, if
  a signal that shouldn't be in the sensitivity list was, use the
  AUTO_CONSTANT above.  If a signal should be in the sensitivity list
  wasn't, placing it before the /*AUTOSENSE*/ comment will prevent it from
  being deleted when the autos are updated.

A simple example:

	   always @ (/*AUTOSENSE*/) begin
	      /* AUTO_CONSTANT (`constant) */
	      outin <= ina | inb | `constant;
	      out <= outin;
	   end

Typing \\[verilog-auto] will make this into:

	   always @ (/*AUTOSENSE*/ina or inb) begin
	      /* AUTO_CONSTANT (`constant) */
	      outin <= ina | inb | `constant;
	      out <= outin;
	   end
"
  (save-excursion
    ;; Find beginning
    (let* ((indent-pt (save-excursion
		       (or (and (search-backward "(" nil t)  (1+ (current-column)))
			   (current-indentation))))
	   (modi (verilog-modi-current))
	   (sig-memories (verilog-signals-memory (verilog-modi-get-regs modi)))
	   sigss sig-list not-first)
      ;; Read signals in always, eliminate outputs from sense list
      (setq sigss (verilog-read-always-signals))
      (setq sig-list (verilog-signals-not-in (nth 0 sigss)
					     (append (and (not verilog-auto-sense-include-inputs) (nth 1 sigss))
						     (verilog-modi-get-consts modi))
					     ))
      (when sig-memories
	(let ((tlen (length sig-list)))
	  (setq sig-list (verilog-signals-not-in sig-list sig-memories))
	  (if (not (eq tlen (length sig-list))) (insert " /*memory or*/ "))))
      (setq sig-list (sort sig-list (function (lambda (a b) (string< (car a) (car b))))))
      (while sig-list 
	(cond ((> (+ 4 (current-column) (length (nth 0 (car sig-list)))) fill-column) ;+4 for width of or
	       (insert "\n")
	       (indent-to indent-pt)
	       (if not-first (insert "or ")))
	      (not-first (insert " or ")))
	(insert (nth 0 (car sig-list)))
	(setq sig-list (cdr sig-list)
	      not-first t))
      )))


;;;
;;; Auto top level
;;;

(defun verilog-auto ()
  "Look for any /*AUTO...*/ commands in the code, as used in
instantiations or argument headers.  Update the list of signals
following the /*AUTO...*/ command.

Use \\[verilog-delete-auto] to remove the AUTOs.

The hooks verilog-before-auto-hook and verilog-auto-hook are
called before and after this function, respectively.

For example:
	module (/*AUTOARG*/)
	/*AUTOINPUT*/
	/*AUTOOUTPUT*/
	/*AUTOWIRE*/
	/*AUTOREG*/
	somesub sub (/*AUTOINST*/);

Using \\[describe-function], see also:
   verilog-auto-arg    for AUTOARG module instantiations
   verilog-auto-inst   for AUTOINST argument declarations
   verilog-auto-input  for AUTOINPUT making hiearchy inputs
   verilog-auto-output for AUTOOUTPUT making hiearchy outputs
   verilog-auto-output-every for AUTOOUTPUTEVERY making all outputs
   verilog-auto-wire   for AUTOWIRE instantiation wires
   verilog-auto-reg    for AUTOREG registers
   verilog-auto-sense  for AUTOSENSE always sensitivity lists

   verilog-read-defines  for reading `define values
   verilog-read-includes for reading `includes

If you have bugs with these autos, try contacting
Wilson Snyder (wsnyder@wsnyder.org)
"
  (interactive)
  (message "Updating AUTOs...")
  (if (featurep 'dinotrace)
      (dinotrace-unannotate-all))
  (let ((oldbuf (if (not (buffer-modified-p))
		    (buffer-string)))
	;; Before version 20, match-string with font-lock returns a 
	;; vector that is not equal to the string.  IE if on "input"
	;; nil==(equal "input" (progn (looking-at "input") (match-string 0)))
	(fontlocked (when (and (memq 'v19 verilog-emacs-features)
			       (boundp 'font-lock-mode)
			       font-lock-mode)
		      (font-lock-mode nil)
		      t)))
    (save-excursion
      (run-hooks 'verilog-before-auto-hook)
      ;; This particular ordering is important 
      ;; INST: Lower modules correct, no internal dependencies, FIRST
      (verilog-preserve-cache
       ;; Clear existing autos else we'll be screwed by existing ones
       (verilog-delete-auto)
       ;;
       (verilog-auto-search-do "/*AUTOINST*/" 'verilog-auto-inst)
       ;; Doesn't matter when done, but combine it with a common changer
       (verilog-auto-search-do "/*AUTOSENSE*/" 'verilog-auto-sense))
      ;;
      ;; Inputs/outputs are mutually independant
      (verilog-preserve-cache
       ;; first in/outs from other files
       (verilog-auto-re-search-do "/\\*AUTOINOUTMODULE([^)]*)\\*/" 'verilog-auto-inout-module)
       ;; next in/outs which need previous sucked inputs first
       (verilog-auto-search-do "/*AUTOOUTPUT*/" 'verilog-auto-output)
       (verilog-auto-search-do "/*AUTOINPUT*/" 'verilog-auto-input)
       ;; outputevery needs autooutputs done first
       (verilog-auto-search-do "/*AUTOOUTPUTEVERY*/" 'verilog-auto-output-every)
       ;; Wires/regs must be after inputs/outputs
       (verilog-auto-search-do "/*AUTOWIRE*/" 'verilog-auto-wire)
       (verilog-auto-search-do "/*AUTOREG*/" 'verilog-auto-reg)
       ;; Must be after all inputs outputs are generated
       (verilog-auto-search-do "/*AUTOARG*/" 'verilog-auto-arg)
       )
      ;;
      (run-hooks 'verilog-auto-hook)
      ;;
      (set (make-local-variable 'verilog-auto-update-tick) (buffer-modified-tick))
      ;;
      ;; If end result is same as when started, clear modified flag
      (cond ((and oldbuf (equal oldbuf (buffer-string)))
	     (set-buffer-modified-p nil)
	     (message "Updating AUTOs...done (no changes)"))
	    (t (message "Updating AUTOs...done")))
      ;; Restore font-lock
      (when fontlocked (font-lock-mode t))
      )))

;;;
;;; Bug reporting
;;;

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
