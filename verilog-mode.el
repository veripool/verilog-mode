;;; verilog-mode.el --- major mode for editing verilog source in Emacs  -*- lexical-binding: t; -*-

;; Copyright (C) 1996-2025 Free Software Foundation, Inc.

;; Author: Michael McNamara <mac@verilog.com>
;;    Wilson Snyder <wsnyder@wsnyder.org>
;; URL: https://www.veripool.org
;; Created: 3 Jan 1996
;; Keywords: languages
;; The "Version" is the date followed by the decimal rendition of the Git
;;     commit hex.
;; Version: __VMVERSIONDOT__.__VMREVISIONDOT__

;; Yoni Rabkin <yoni@rabkins.net> contacted the maintainer of this
;; file on 19/3/2008, and the maintainer agreed that when a bug is
;; filed in the Emacs bug reporting system against this file, a copy
;; of the bug report be sent to the maintainer's email address.

;;    This code supports Emacs 21.1 and later
;;    And XEmacs 21.1 and later
;;    Please do not make changes that break Emacs 21.  Thanks!
;;
;;

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:

;; USAGE
;; =====

;; A major mode for editing Verilog and SystemVerilog HDL source code (IEEE
;; 1364-2005 and IEEE 1800-2012 standards).  When you have entered Verilog
;; mode, you may get more info by pressing C-h m. You may also get online
;; help describing various functions by: C-h f <Name of function you want
;; described>

;; KNOWN BUGS / BUG REPORTS
;; =======================

;; SystemVerilog is a rapidly evolving language, and hence this mode is
;; under continuous development.  Please report any issues to the issue
;; tracker at
;;
;;    https://www.veripool.org/verilog-mode
;;
;; Please use verilog-submit-bug-report to submit a report; type C-c
;; C-b to invoke this and as a result we will have a much easier time
;; of reproducing the bug you find, and hence fixing it.

;; INSTALLING THE MODE
;; ===================

;; An older version of this mode may be already installed as a part of
;; your environment, and one method of updating would be to update
;; your Emacs environment.  Sometimes this is difficult for local
;; political/control reasons, and hence you can always install a
;; private copy (or even a shared copy) which overrides the system
;; default.

;; You can get step by step help in installing this file by going to
;; <https://www.veripool.org/verilog-mode>

;; The short list of installation instructions are: To set up
;; automatic Verilog mode, put this file in your load path, and put
;; the following in code (please un comment it first!) in your
;; .emacs, or in your site's site-load.el

;;   (autoload 'verilog-mode "verilog-mode" "Verilog mode" t )
;;   (add-to-list 'auto-mode-alist '("\\.[ds]?va?h?\\'" . verilog-mode))

;; Be sure to examine at the help for verilog-auto, and the other
;; verilog-auto-* functions for some major coding time savers.
;;
;; If you want to customize Verilog mode to fit your needs better,
;; you may add the below lines (the values of the variables presented
;; here are the defaults).  Note also that if you use an Emacs that
;; supports custom, it's probably better to use the custom menu to
;; edit these.  If working as a member of a large team these settings
;; should be common across all users (in a site-start file), or set
;; in Local Variables in every file.  Otherwise, different people's
;; AUTO expansion may result different whitespace changes.
;;
;;   ;; Enable syntax highlighting of **all** languages
;;   (global-font-lock-mode t)
;;
;;   ;; User customization for Verilog mode
;;   (setq verilog-indent-level             3
;;         verilog-indent-level-module      3
;;         verilog-indent-level-declaration 3
;;         verilog-indent-level-behavioral  3
;;         verilog-indent-level-directive   1
;;         verilog-case-indent              2
;;         verilog-auto-newline             t
;;         verilog-auto-indent-on-newline   t
;;         verilog-tab-always-indent        t
;;         verilog-auto-endcomments         t
;;         verilog-minimum-comment-distance 40
;;         verilog-indent-begin-after-if    t
;;         verilog-auto-lineup              'declarations
;;         verilog-linter                   "my_lint_shell_command"
;;         )


;;; History:
;;
;; See commit history at https://www.veripool.org/verilog-mode
;; (This section is required to appease checkdoc.)

;;; Code:
;;

;; This variable will always hold the version number of the mode
(defconst verilog-mode-version "__VMVERSION__-__VMREVISION__-__VMPACKAGER__"
  "Version of this Verilog mode.")
(defconst verilog-mode-release-emacs nil
  "If non-nil, this version of Verilog mode was released with Emacs itself.")

(defun verilog-version ()
  "Inform caller of the version of this file."
  (interactive)
  (message "Using verilog-mode version %s" verilog-mode-version))

(defmacro verilog--suppressed-warnings (warnings &rest body)
  (declare (indent 1) (debug t))
  (cond
   ((fboundp 'with-suppressed-warnings)
    `(with-suppressed-warnings ,warnings ,@body))
   ((fboundp 'with-no-warnings)
    `(with-no-warnings ,@body))
   (t
    `(progn ,@body))))

;; Insure we have certain packages, and deal with it if we don't
;; Be sure to note which Emacs flavor and version added each feature.
(eval-when-compile
  ;; Provide stuff if we are XEmacs
  (when (featurep 'xemacs)
    (condition-case nil
        (require 'easymenu)
      (error nil))
    (condition-case nil
        (require 'regexp-opt)
      (error nil))
    ;; Bug in 19.28 through 19.30 skeleton.el, not provided.
    (condition-case nil
        (load "skeleton")
      (error nil))
    (condition-case nil
        (if (fboundp 'when)
            nil  ; fab
          (defmacro when (cond &rest body)
            (list 'if cond (cons 'progn body))))
      (error nil))
    (condition-case nil
        (if (fboundp 'unless)
            nil  ; fab
          (defmacro unless (cond &rest body)
            (cons 'if (cons cond (cons nil body)))))
      (error nil))
    (condition-case nil
        (if (fboundp 'store-match-data)
            nil  ; fab
          (defmacro store-match-data (&rest _args) nil))
      (error nil))
    (condition-case nil
        (if (fboundp 'char-before)
            nil  ; great
          (defmacro char-before (&rest _body)
            (char-after (1- (point)))))
      (error nil))
    (condition-case nil
        (if (fboundp 'when)
            nil  ; fab
          (defsubst point-at-bol (&optional N)
            (save-excursion (beginning-of-line N) (point))))
      (error nil))
    (condition-case nil
        (if (fboundp 'when)
            nil  ; fab
          (defsubst point-at-eol (&optional N)
            (save-excursion (end-of-line N) (point))))
      (error nil))
    (condition-case nil
        (require 'custom)
      (error nil))
    (condition-case nil
        (if (fboundp 'match-string-no-properties)
            nil  ; great
          (defsubst match-string-no-properties (num &optional string)
            "Return string of text matched by last search, without text properties.
NUM specifies which parenthesized expression in the last regexp.
 Value is nil if NUMth pair didn't match, or there were less than NUM pairs.
Zero means the entire text matched by the whole regexp or whole string.
STRING should be given if the last search was by `string-match' on STRING."
            (if (match-beginning num)
                (if string
                    (let ((result
                           (substring string
				      (match-beginning num) (match-end num))))
                      (set-text-properties 0 (length result) nil result)
                      result)
                  (buffer-substring-no-properties (match-beginning num)
                                                  (match-end num)
                                                  (current-buffer)))))
	  )
      (error nil))
    (if (and (featurep 'custom) (fboundp 'custom-declare-variable))
        nil  ; We've got what we needed
      ;; We have the old custom-library, hack around it!
      (defmacro defgroup (&rest _args)  nil)
      (defmacro customize (&rest _args)
        (message
	 "Sorry, Customize is not available with this version of Emacs"))
      (defmacro defcustom (var value doc &rest _args)
        `(defvar ,var ,value ,doc))
      )
    (if (fboundp 'defface)
        nil				; great!
      (defmacro defface (var _values _doc &rest _args)
        `(make-face ,var))
      )

    (if (and (featurep 'custom) (fboundp 'customize-group))
        nil  ; We've got what we needed
      ;; We have an intermediate custom-library, hack around it!
      (defmacro customize-group (var &rest _args)
        `(customize ,var))
      )

    (defvar inhibit-modification-hooks)
    (defvar inhibit-point-motion-hooks)
    (defvar deactivate-mark)
    )
  ;;
  ;; OK, do this stuff if we are NOT XEmacs:
  (unless (featurep 'xemacs)
    (unless (fboundp 'region-active-p)
      (defmacro region-active-p ()
	'(and transient-mark-mode mark-active))))
  )

;; Provide a regular expression optimization routine, using regexp-opt
;; if provided by the user's elisp libraries
(eval-and-compile
  ;; The below were disabled when GNU Emacs 22 was released;
  ;; perhaps some still need to be there to support Emacs 21.
  (if (featurep 'xemacs)
      (if (fboundp 'regexp-opt)
          ;; regexp-opt is defined, does it take 3 or 2 arguments?
          (if (fboundp 'function-max-args)
              (let ((args (function-max-args 'regexp-opt)))
                (cond
                 ((eq args 3)  ; It takes 3
                  (condition-case nil	; Hide this defun from emacses
                                        ; with just a two input regexp
                      (defun verilog-regexp-opt (a b)
                        "Deal with differing number of required arguments for  `regexp-opt'.
         Call `regexp-opt' on A and B."
                        (regexp-opt a b t))
                    (error nil))
                  )
                 ((eq args 2)  ; It takes 2
                  (defun verilog-regexp-opt (a b)
                    "Call `regexp-opt' on A and B."
                    (regexp-opt a b))
                  )
                 (t nil)))
            ;; We can't tell; assume it takes 2
            (defun verilog-regexp-opt (a b)
              "Call `regexp-opt' on A and B."
              (regexp-opt a b))
            )
        ;; There is no regexp-opt, provide our own
        (defun verilog-regexp-opt (strings &optional paren _shy)
          (let ((open (if paren "\\(" "")) (close (if paren "\\)" "")))
            (concat open (mapconcat 'regexp-quote strings "\\|") close)))
        )
    ;; Emacs.
    (defalias 'verilog-regexp-opt #'regexp-opt)))

;; emacs >=22 has looking-back, but older emacs and xemacs don't.
;; This function is lifted directly from emacs's subr.el
;; so that it can be used by xemacs.
;; The idea for this was borrowed from org-mode via this link:
;; https://lists.gnu.org/r/emacs-orgmode/2009-12/msg00032.html
(eval-and-compile
  (cond
   ((fboundp 'looking-back)
    (defalias 'verilog-looking-back #'looking-back))
   (t
    (defun verilog-looking-back (regexp limit &optional greedy)
      "Return non-nil if text before point matches regular expression REGEXP.
Like `looking-at' except matches before point, and is slower.
LIMIT if non-nil speeds up the search by specifying a minimum
starting position, to avoid checking matches that would start
before LIMIT.

If GREEDY is non-nil, extend the match backwards as far as
possible, stopping when a single additional previous character
cannot be part of a match for REGEXP.  When the match is
extended, its starting position is allowed to occur before
LIMIT.

As a general recommendation, try to avoid using `looking-back'
wherever possible, since it is slow."
      (let ((start (point))
            (pos
             (save-excursion
               (and (re-search-backward (concat "\\(?:" regexp "\\)\\=") limit t)
                    (point)))))
        (if (and greedy pos)
            (save-restriction
              (narrow-to-region (point-min) start)
              (while (and (> pos (point-min))
                          (save-excursion
                            (goto-char pos)
                            (backward-char 1)
                            (looking-at (concat "\\(?:"  regexp "\\)\\'"))))
                (setq pos (1- pos)))
              (save-excursion
                (goto-char pos)
                (looking-at (concat "\\(?:"  regexp "\\)\\'")))))
        (not (null pos)))))))

(eval-and-compile
  (cond
   ((fboundp 'restore-buffer-modified-p)
    ;; Faster, as does not update mode line when nothing changes
    (defalias 'verilog-restore-buffer-modified-p #'restore-buffer-modified-p))
   (t
    (defalias 'verilog-restore-buffer-modified-p #'set-buffer-modified-p))))

(eval-and-compile
  (cond
   ((fboundp 'quit-window)
    (defalias 'verilog-quit-window #'quit-window))
   (t
    (defun verilog-quit-window (_kill-ignored window)
      "Quit WINDOW and bury its buffer. KILL-IGNORED is ignored."
      (delete-window window)))))

(eval-and-compile
  ;; Both xemacs and emacs
  (condition-case nil
      ;; `diff-command' and `diff-switches',
      ;; although XEmacs lacks the former.
      (require 'diff)
    (error nil))
  (condition-case nil
      (require 'compile)  ; compilation-error-regexp-alist-alist
    (error nil))
  (condition-case nil
      (unless (fboundp 'buffer-chars-modified-tick)  ; Emacs 22 added
	(defmacro buffer-chars-modified-tick () (buffer-modified-tick)))
    (error nil))
  ;; Added in Emacs 23.1
  (condition-case nil
      (unless (fboundp 'ignore-errors)
        (defmacro ignore-errors (&rest body)
          (declare (debug t) (indent 0))
          `(condition-case nil (progn ,@body) (error nil))))
    (error nil))
  ;; Added in Emacs 24.1
  (condition-case nil
      (unless (fboundp 'prog-mode)
	(define-derived-mode prog-mode fundamental-mode "Prog"))
    (error nil))
  ;; Added in Emacs 25.1
  (condition-case nil
      (unless (fboundp 'forward-word-strictly)
        (defalias 'forward-word-strictly #'forward-word))
    (error nil)))

(eval-when-compile
  (defun verilog-regexp-words (a)
    "Call `regexp-opt' with word delimiters for the words A."
    (concat "\\<" (verilog-regexp-opt a t) "\\>")))
(defun verilog-regexp-words (a)
  "Call `regexp-opt' with word delimiters for the words A."
  ;; The FAQ references this function, so user LISP sometimes calls it
  (concat "\\<" (verilog-regexp-opt a t) "\\>"))

(defun verilog-easy-menu-filter (menu)
  "Filter `easy-menu-define' MENU to support new features."
  (cond ((not (featurep 'xemacs))
         menu)  ; GNU Emacs - passthru
	;; XEmacs doesn't support :help.  Strip it.
	;; Recursively filter the a submenu
	((listp menu)
	 (mapcar 'verilog-easy-menu-filter menu))
	;; Look for [:help "blah"] and remove
	((vectorp menu)
	 (let ((i 0) (out []))
	   (while (< i (length menu))
	     (if (equal :help (aref menu i))
		 (setq i (+ 2 i))
	       (setq out (vconcat out (vector (aref menu i)))
		     i (1+ i))))
	   out))
        (t menu)))  ; Default - ok
;;(verilog-easy-menu-filter
;;  `("Verilog" ("MA" ["SAA" nil :help "Help SAA"] ["SAB" nil :help "Help SAA"])
;;     "----" ["MB" nil :help "Help MB"]))

(defun verilog-define-abbrev-table (tablename definitions &optional docstring &rest props)
  "Filter `define-abbrev-table' TABLENAME DEFINITIONS.
Provides DOCSTRING PROPS in newer Emacs (23.1)."
  (condition-case nil
      (apply #'define-abbrev-table tablename definitions docstring props)
    (error
     (define-abbrev-table tablename definitions))))

(defun verilog-define-abbrev (table name expansion &optional hook)
  "Filter `define-abbrev' TABLE NAME EXPANSION and call HOOK.
Provides SYSTEM-FLAG in newer Emacs."
  (condition-case nil
      (define-abbrev table name expansion hook 0 t)
    (error
     (define-abbrev table name expansion hook))))

(defun verilog-customize ()
  "Customize variables and other settings used by Verilog-Mode."
  (interactive)
  (customize-group 'verilog-mode))

(defun verilog-font-customize ()
  "Customize fonts used by Verilog-Mode."
  (interactive)
  (if (fboundp 'customize-apropos)
      (customize-apropos "font-lock-*" 'faces)))

(defun verilog-booleanp (value)
  "Return t if VALUE is boolean.
This implements GNU Emacs 22.1's `booleanp' function in earlier Emacs.
This function may be removed when Emacs 21 is no longer supported."
  (or (equal value t) (equal value nil)))

(defun verilog-insert-last-command-event ()
  "Insert the `last-command-event'."
  (insert (if (featurep 'xemacs)
	      ;; XEmacs 21.5 doesn't like last-command-event
	      last-command-char
	    ;; And GNU Emacs 22 has obsoleted last-command-char
	    last-command-event)))

(defvar verilog-no-change-functions nil
  "Non-nil if `after-change-functions' is disabled.
Use of `syntax-ppss' may break, as ppss's cache may get corrupted.")

(defvar verilog-in-hooks nil
  "Non-nil when within a `verilog-run-hooks' block.")

(defmacro verilog-run-hooks (&rest hooks)
  "Run each hook in HOOKS using `run-hooks'.
Set `verilog-in-hooks' during this time, to assist AUTO caches."
  `(let ((verilog-in-hooks t))
     (run-hooks ,@hooks)))

(defun verilog-syntax-ppss (&optional pos)
  (when verilog-no-change-functions
    (if verilog-in-hooks
	(verilog-scan-cache-flush)
      ;; else don't let the AUTO code itself get away with flushing the cache,
      ;; as that'll make things very slow
      (backtrace)
      (error "%s: Internal problem; use of syntax-ppss when cache may be corrupt"
	     (verilog-point-text))))
  (if (fboundp 'syntax-ppss)
      (syntax-ppss pos)
    (parse-partial-sexp (point-min) (or pos (point)))))

(defgroup verilog-mode nil
  "Major mode for Verilog source code."
  :version "22.2"
  :group 'languages)

;; (defgroup verilog-mode-fonts nil
;;   "Facilitates easy customization fonts used in Verilog source text"
;;   :link '(customize-apropos "font-lock-*" 'faces)
;;   :group 'verilog-mode)

(defgroup verilog-mode-indent nil
  "Customize indentation and highlighting of Verilog source text."
  :group 'verilog-mode)

(defgroup verilog-mode-actions nil
  "Customize actions on Verilog source text."
  :group 'verilog-mode)

(defgroup verilog-mode-auto nil
  "Customize AUTO actions when expanding Verilog source text."
  :group 'verilog-mode)

(defvar verilog-debug nil
  "Non-nil means enable debug messages for `verilog-mode' internals.")

(defcustom verilog-warn-fatal nil
  "Non-nil means `verilog-warn-error' warnings are fatal `error's."
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-warn-fatal 'safe-local-variable #'verilog-booleanp)

;; Internal use similar to `verilog-warn-fatal'
(defvar verilog-warn-fatal-internal t)

(defcustom verilog-linter
  "echo 'No verilog-linter set, see \"M-x describe-variable verilog-linter\"'"
  "Unix program and arguments to call to run a lint checker on Verilog source.
Depending on the `verilog-set-compile-command', this may be invoked when
you type \\[compile].  When the compile completes, \\[next-error] will take
you to the next lint error."
  :type 'string
  :group 'verilog-mode-actions)
;; We don't mark it safe, as it's used as a shell command

(defcustom verilog-coverage
  "echo 'No verilog-coverage set, see \"M-x describe-variable verilog-coverage\"'"
  "Program and arguments to use to annotate for coverage Verilog source.
Depending on the `verilog-set-compile-command', this may be invoked when
you type \\[compile].  When the compile completes, \\[next-error] will take
you to the next lint error."
  :type 'string
  :group 'verilog-mode-actions)
;; We don't mark it safe, as it's used as a shell command

(defcustom verilog-simulator
  "echo 'No verilog-simulator set, see \"M-x describe-variable verilog-simulator\"'"
  "Program and arguments to use to interpret Verilog source.
Depending on the `verilog-set-compile-command', this may be invoked when
you type \\[compile].  When the compile completes, \\[next-error] will take
you to the next lint error."
  :type 'string
  :group 'verilog-mode-actions)
;; We don't mark it safe, as it's used as a shell command

(defcustom verilog-compiler
  "echo 'No verilog-compiler set, see \"M-x describe-variable verilog-compiler\"'"
  "Program and arguments to use to compile Verilog source.
Depending on the `verilog-set-compile-command', this may be invoked when
you type \\[compile].  When the compile completes, \\[next-error] will take
you to the next lint error."
  :type 'string
  :group 'verilog-mode-actions)
;; We don't mark it safe, as it's used as a shell command

(defcustom verilog-preprocessor
  "verilator -E __FLAGS__ __FILE__"
  "Program and arguments to use to preprocess Verilog source.
This is invoked with `verilog-preprocess', and depending on the
`verilog-set-compile-command', may also be invoked when you type
\\[compile].  When the compile completes, \\[next-error] will
take you to the next lint error."
  :type 'string
  :group 'verilog-mode-actions)
;; We don't mark it safe, as it's used as a shell command

(defvar verilog-preprocess-history nil
  "History for `verilog-preprocess'.")

(defvar verilog-tool 'verilog-linter
  "Which tool to use for building compiler-command.
Either nil, `verilog-linter', `verilog-compiler',
`verilog-coverage', `verilog-preprocessor', or `verilog-simulator'.
Alternatively use the \"Choose Compilation Action\" menu.  See
`verilog-set-compile-command' for more information.")

(defcustom verilog-highlight-translate-off nil
  "Non-nil means background-highlight code excluded from translation.
That is, all code between \"// synopsys translate_off\" and
\"// synopsys translate_on\" is highlighted using a different background color
\(face `verilog-font-lock-translate-off-face').

Note: This will slow down on-the-fly fontification (and thus editing).

Note: Activate the new setting in a Verilog buffer by re-fontifying it (menu
entry \"Fontify Buffer\").  XEmacs: turn off and on font locking."
  :type 'boolean
  :group 'verilog-mode-indent)
;; Note we don't use :safe, as that would break on Emacsen before 22.0.
(put 'verilog-highlight-translate-off 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-lineup 'declarations
  "Type of statements to lineup across multiple lines.
If `all' is selected, then all line ups described below are done.

If `declarations', then just declarations are lined up with any
preceding declarations, taking into account widths and the like,
so or example the code:
        reg [31:0] a;
        reg b;
would become
        reg [31:0] a;
        reg        b;

If `assignment', then assignments are lined up with any preceding
assignments, so for example the code
        a_long_variable <= b + c;
        d = e + f;
would become
        a_long_variable <= b + c;
        d                = e + f;

In order to speed up editing, large blocks of statements are lined up
only when a \\[verilog-pretty-expr] is typed; and large blocks of declarations
are lineup only when \\[verilog-pretty-declarations] is typed."

  :type '(radio (const :tag "Line up Assignments and Declarations" all)
		(const :tag "Line up Assignment statements" assignments )
		(const :tag "Line up Declarations" declarations)
		(function :tag "Other"))
  :group 'verilog-mode-indent )
(put 'verilog-auto-lineup 'safe-local-variable
     (lambda (x) (memq x '(nil all assignments declarations))))

(defcustom verilog-indent-level 3
  "Indentation of Verilog statements with respect to containing block."
  :group 'verilog-mode-indent
  :type 'integer)
(put 'verilog-indent-level 'safe-local-variable #'integerp)

(defcustom verilog-indent-level-module 3
  "Indentation of Module level Verilog statements (eg always, initial).
Set to 0 to get initial and always statements lined up on the left side of
your screen."
  :group 'verilog-mode-indent
  :type 'integer)
(put 'verilog-indent-level-module 'safe-local-variable #'integerp)

(defcustom verilog-indent-level-declaration 3
  "Indentation of declarations with respect to containing block.
Set to 0 to get them list right under containing block."
  :group 'verilog-mode-indent
  :type 'integer)
(put 'verilog-indent-level-declaration 'safe-local-variable #'integerp)

(defcustom verilog-indent-declaration-macros nil
  "How to treat macro expansions in a declaration.
If nil, indent as:
        input [31:0] a;
        input        \\=`CP;
        output       c;
If non-nil, treat as:
        input [31:0] a;
        input \\=`CP    ;
        output       c;"
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-indent-declaration-macros 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-indent-lists t
  "How to treat indenting items in a list.
If t (the default), indent as:
        always @( posedge a or
                  reset ) begin

If nil, treat as:
        always @( posedge a or
           reset ) begin"
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-indent-lists 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-indent-level-behavioral 3
  "Absolute indentation of first begin in a task or function block.
Set to 0 to get such code to start at the left side of the screen."
  :group 'verilog-mode-indent
  :type 'integer)
(put 'verilog-indent-level-behavioral 'safe-local-variable #'integerp)

(defcustom verilog-indent-level-directive 1
  "Indentation to add to each level of \\=`ifdef declarations.
Set to 0 to have all directives start at the left side of the screen."
  :group 'verilog-mode-indent
  :type 'integer)
(put 'verilog-indent-level-directive 'safe-local-variable #'integerp)

(defcustom verilog-indent-ignore-multiline-defines t
  "Non-nil means ignore indentation on lines that are part of a multiline define."
  :group 'verilog-mode-indent
  :version "30.1"
  :type 'boolean)
(put 'verilog-indent-ignore-multiline-defines 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-indent-ignore-regexp nil
  "Regexp that matches lines that should be ignored for indentation."
  :group 'verilog-mode-indent
  :version "30.1"
  :type 'boolean)
(put 'verilog-indent-ignore-regexp 'safe-local-variable #'stringp)

(defcustom verilog-cexp-indent 2
  "Indentation of Verilog statements split across lines."
  :group 'verilog-mode-indent
  :type 'integer)
(put 'verilog-cexp-indent 'safe-local-variable #'integerp)

(defcustom verilog-case-indent 2
  "Indentation for case statements."
  :group 'verilog-mode-indent
  :type 'integer)
(put 'verilog-case-indent 'safe-local-variable #'integerp)

(defcustom verilog-auto-newline t
  "Non-nil means automatically newline after semicolons."
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-auto-newline 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-indent-on-newline t
  "Non-nil means automatically indent line after newline."
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-auto-indent-on-newline 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-tab-always-indent t
  "Non-nil means TAB should always re-indent the current line.
A nil value means TAB will only reindent when at the beginning of the line."
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-tab-always-indent 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-tab-to-comment nil
  "Non-nil means TAB moves to the right hand column in preparation for a comment."
  :group 'verilog-mode-actions
  :type 'boolean)
(put 'verilog-tab-to-comment 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-indent-begin-after-if t
  "Non-nil means indent begin statements following if, else, while, etc.
Otherwise, line them up."
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-indent-begin-after-if 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-indent-class-inside-pkg t
  "Non-nil means indent classes inside packages.
Otherwise, classes have zero indentation."
  :group 'verilog-mode-indent
  :version "30.1"
  :type 'boolean)
(put 'verilog-indent-class-inside-pkg 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-align-ifelse nil
  "Non-nil means align `else' under matching `if'.
Otherwise else is lined up with first character on line holding matching if."
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-align-ifelse 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-align-decl-expr-comments t
  "Non-nil means align declaration and expressions comments."
  :group 'verilog-mode-indent
  :version "30.1"
  :type 'boolean)
(put 'verilog-align-decl-expr-comments 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-align-comment-distance 1
  "Distance (in spaces) between longest declaration/expression and comments.
Only works if `verilog-align-decl-expr-comments' is non-nil."
  :group 'verilog-mode-indent
  :version "30.1"
  :type 'integer)
(put 'verilog-align-comment-distance 'safe-local-variable #'integerp)

(defcustom verilog-align-assign-expr nil
  "Non-nil means align expressions of continuous assignments."
  :group 'verilog-mode-indent
  :version "30.1"
  :type 'boolean)
(put 'verilog-align-assign-expr 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-align-typedef-regexp nil
  "Regexp that matches user typedefs for declaration alignment."
  :group 'verilog-mode-indent
  :version "30.1"
  :type '(choice (regexp :tag "Regexp")
                 (const :tag "None" nil)))
(put 'verilog-align-typedef-regexp 'safe-local-variable #'stringp)

(defcustom verilog-align-typedef-words nil
  "List of words that match user typedefs for declaration alignment."
  :group 'verilog-mode-indent
  :version "30.1"
  :type '(repeat string))
(put 'verilog-align-typedef-words 'safe-local-variable #'listp)

(defcustom verilog-minimum-comment-distance 10
  "Minimum distance (in lines) between begin and end required before a comment.
Setting this variable to zero results in every end acquiring a comment; the
default avoids too many redundant comments in tight quarters."
  :group 'verilog-mode-indent
  :type 'integer)
(put 'verilog-minimum-comment-distance 'safe-local-variable #'integerp)

(defcustom verilog-highlight-p1800-keywords nil
  "Obsolete.
Was non-nil means highlight SystemVerilog IEEE-1800 differently.
All code is now highlighted as if SystemVerilog IEEE-1800."
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-highlight-p1800-keywords 'safe-local-variable #'verilog-booleanp)
(make-obsolete-variable 'verilog-highlight-p1800-keywords nil "27.1")

(defcustom verilog-highlight-grouping-keywords nil
  "Non-nil means highlight grouping keywords more dramatically.
If false, these words are in the `font-lock-type-face'; if True
then they are in `verilog-font-lock-grouping-keywords-face'.
Some find that special highlighting on these grouping constructs
allow the structure of the code to be understood at a glance."
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-highlight-grouping-keywords 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-highlight-modules nil
  "Non-nil means highlight module statements for `verilog-load-file-at-point'.
When true, mousing over module names will allow jumping to the
module definition.  If false, this is not supported.  Setting
this is experimental, and may lead to bad performance."
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-highlight-modules 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-highlight-includes t
  "Non-nil means highlight module statements for `verilog-load-file-at-point'.
When true, mousing over include file names will allow jumping to the
file referenced.  If false, this is not supported."
  :group 'verilog-mode-indent
  :type 'boolean)
(put 'verilog-highlight-includes 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-highlight-max-lookahead 10000
  "Maximum size of declaration statement that undergoes highlighting.
Highlighting is performed only on the first `verilog-highlight-max-lookahead'
characters in a declaration statement.
Setting this variable to zero would remove this limit.  Note that removing
the limit can greatly slow down highlighting for very large files."
  :group 'verilog-mode-indent
  :type 'integer)
(put 'verilog-highlight-max-lookahead 'safe-local-variable #'integerp)

(defcustom verilog-auto-declare-nettype nil
  "Non-nil specifies the data type to use with `verilog-auto-input' etc.
Set this to \"wire\" if the Verilog code uses \"\\=`default_nettype
none\".  Note using \\=`default_nettype none isn't recommended practice; this
mode is experimental."
  :version "24.1"  ; rev670
  :group 'verilog-mode-actions
  :type 'boolean)
(put 'verilog-auto-declare-nettype 'safe-local-variable #'stringp)

(defcustom verilog-auto-wire-comment t
  "Non-nil indicates to insert to/from comments with `verilog-auto-wire' etc."
  :version "25.1"
  :group 'verilog-mode-actions
  :type 'boolean)
(put 'verilog-auto-wire-comment 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-wire-type nil
  "Non-nil specifies the data type to use with `verilog-auto-wire' etc.
Set this to \"logic\" for SystemVerilog code, or use `verilog-auto-logic'.
Set this to \"wire\" to force use of wire when logic is otherwise appropriate;
this is generally only appropriate when making a non-SystemVerilog wrapper
containing SystemVerilog cells."
  :version "24.1"  ; rev673
  :group 'verilog-mode-actions
  :type '(choice (const nil) string))
(put 'verilog-auto-wire-type 'safe-local-variable #'stringp)

(defcustom verilog-auto-endcomments t
  "Non-nil means insert a comment /* ... */ after `end's.
The name of the function or case will be set between the braces."
  :group 'verilog-mode-actions
  :type 'boolean)
(put 'verilog-auto-endcomments 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-delete-trailing-whitespace nil
  "Non-nil means to `delete-trailing-whitespace' in `verilog-auto'."
  :version "24.1"  ; rev703
  :group 'verilog-mode-actions
  :type 'boolean)
(put 'verilog-auto-delete-trailing-whitespace 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-ignore-concat nil
  "Non-nil means ignore signals in {...} concatenations for AUTOWIRE etc.
This will exclude signals referenced as pin connections in {...}
or (...) from AUTOWIRE, AUTOOUTPUT and friends.  See also AUTONOHOOKUP."
  :group 'verilog-mode-actions
  :type 'boolean)
(put 'verilog-auto-ignore-concat 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-read-includes nil
  "Non-nil means to automatically read includes before AUTOs.
This will do a `verilog-read-defines' and `verilog-read-includes' before
each AUTO expansion.  This makes it easier to embed defines and includes,
but can result in very slow reading times if there are many or large
include files."
  :group 'verilog-mode-actions
  :type 'boolean)
(put 'verilog-auto-read-includes 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-save-policy nil
  "Non-nil indicates action to take when saving a Verilog buffer with AUTOs.
A value of `force' will always do a \\[verilog-auto] automatically if
needed on every save.  A value of `detect' will do \\[verilog-auto]
automatically when it thinks necessary.  A value of `ask' will query the
user when it thinks updating is needed.

You should not rely on the `ask' or `detect' policies, they are safeguards
only.  They do not detect when AUTOINSTs need to be updated because a
sub-module's port list has changed."
  :group 'verilog-mode-actions
  :type '(choice (const nil) (const ask) (const detect) (const force)))

(defcustom verilog-auto-star-expand t
  "Non-nil means to expand SystemVerilog .* instance ports.
They will be expanded in the same way as if there was an AUTOINST in the
instantiation.  See also `verilog-auto-star' and `verilog-auto-star-save'."
  :group 'verilog-mode-actions
  :type 'boolean)
(put 'verilog-auto-star-expand 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-star-save nil
  "Non-nil means save to disk SystemVerilog .* instance expansions.
A nil value indicates direct connections will be removed before saving.
Only meaningful to those created due to `verilog-auto-star-expand' being set.

Instead of setting this, you may want to use /*AUTOINST*/, which will
always be saved."
  :group 'verilog-mode-actions
  :type 'boolean)
(put 'verilog-auto-star-save 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-fontify-variables t
  "Non-nil means fontify declaration variables."
  :group 'verilog-mode-actions
  :version "30.1"
  :type 'boolean)
(put 'verilog-fontify-variables 'safe-local-variable #'verilog-booleanp)

(defvar verilog-auto-update-tick nil
  "Modification tick at which autos were last performed.")

(defvar verilog-auto-last-file-locals nil
  "Text from file-local-variables during last evaluation.")

(defvar verilog-diff-function #'verilog-diff-report
  "Function to run when `verilog-diff-auto' detects differences.
Function takes three arguments, the original buffer, the
difference buffer, and the point in original buffer with the
first difference.")

(defvar verilog-diff-ignore-regexp nil
  "Non-nil specifies regexp which `verilog-diff-auto' will ignore.
This is typically nil.")

;;; Compile support:
;;

(require 'compile)

(defvar verilog-error-regexp-added nil)

(defvar verilog-error-regexp-emacs-alist
  '(
    (verilog-xl-1
     "\\(Error\\|Warning\\)!.*\n?.*\"\\([^\"]+\\)\", \\([0-9]+\\)" 2 3)
    (verilog-xl-2
     "([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+\\(line[ \t]+\\)?\\([0-9]+\\):.*$" 1 3)
    (verilog-IES
     ".*\\*[WE],[0-9A-Z]+\\(\\[[0-9A-Z_,]+\\]\\)? (\\([^ \t,]+\\),\\([0-9]+\\)" 2 3)
    (verilog-surefire-1
     "[^\n]*\\[\\([^:]+\\):\\([0-9]+\\)\\]" 1 2)
    (verilog-surefire-2
     "\\(WARNING\\|ERROR\\|INFO\\)[^:]*: \\([^,]+\\),\\s-+\\(line \\)?\\([0-9]+\\):" 2 4 )
    (verilog-verbose
     "\
\\([a-zA-Z]?:?[^:( \t\n]+\\)[:(][ \t]*\\([0-9]+\\)\\([) \t]\\|\
:\\([^0-9\n]\\|\\([0-9]+:\\)\\)\\)" 1 2 5)
    (verilog-xsim
     "\\(Error\\|Warning\\).*in file (\\([^ \t]+\\) at line *\\([0-9]+\\))" 2 3)
    (verilog-vcs-1
     "\\(Error\\|Warning\\):[^(]*(\\([^ \t]+\\) line *\\([0-9]+\\))" 2 3)
    (verilog-vcs-2
     "Warning:.*(port.*(\\([^ \t]+\\) line \\([0-9]+\\))" 1 2)
    (verilog-vcs-3
     "\\(Error\\|Warning\\):[\n.]*\\([^ \t]+\\) *\\([0-9]+\\):" 2 3)
    (verilog-vcs-4
     "syntax error:.*\n\\([^ \t]+\\) *\\([0-9]+\\):" 1 2)
    (verilog-verilator
     "%?\\(Error\\|Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):" 3 4)
    (verilog-leda
     "^In file \\([^ \t]+\\)[ \t]+line[ \t]+\\([0-9]+\\):\n[^\n]*\n[^\n]*\n\\(Warning\\|Error\\|Failure\\)[^\n]*" 1 2)
    )
  "List of regexps for Verilog compilers.
See `compilation-error-regexp-alist' for the formatting.  For Emacs 22+.")

(defvar verilog-error-regexp-xemacs-alist
  ;; Emacs form is '((v-tool "re" 1 2) ...)
  ;; XEmacs form is '(verilog ("re" 1 2) ...)
  ;; So we can just map from Emacs to XEmacs
  (cons 'verilog (mapcar #'cdr verilog-error-regexp-emacs-alist))
  "List of regexps for Verilog compilers.
See `compilation-error-regexp-alist-alist' for the formatting.  For XEmacs.")

(defvar verilog-error-font-lock-keywords
  '(
    ;; verilog-xl-1
    ("\\(Error\\|Warning\\)!.*\n?.*\"\\([^\"]+\\)\", \\([0-9]+\\)" 2 bold t)
    ("\\(Error\\|Warning\\)!.*\n?.*\"\\([^\"]+\\)\", \\([0-9]+\\)" 2 bold t)
    ;; verilog-xl-2
    ("([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+\\(line[ \t]+\\)?\\([0-9]+\\):.*$" 1 bold t)
    ("([WE][0-9A-Z]+)[ \t]+\\([^ \t\n,]+\\)[, \t]+\\(line[ \t]+\\)?\\([0-9]+\\):.*$" 3 bold t)
    ;; verilog-IES (nc-verilog)
    (".*\\*[WE],[0-9A-Z]+\\(\\[[0-9A-Z_,]+\\]\\)? (\\([^ \t,]+\\),\\([0-9]+\\)|" 2 bold t)
    (".*\\*[WE],[0-9A-Z]+\\(\\[[0-9A-Z_,]+\\]\\)? (\\([^ \t,]+\\),\\([0-9]+\\)|" 3 bold t)
    ;; verilog-surefire-1
    ("[^\n]*\\[\\([^:]+\\):\\([0-9]+\\)\\]" 1 bold t)
    ("[^\n]*\\[\\([^:]+\\):\\([0-9]+\\)\\]" 2 bold t)
    ;; verilog-surefire-2
    ("\\(WARNING\\|ERROR\\|INFO\\): \\([^,]+\\), line \\([0-9]+\\):" 2 bold t)
    ("\\(WARNING\\|ERROR\\|INFO\\): \\([^,]+\\), line \\([0-9]+\\):" 3 bold t)
    ;; verilog-verbose
    ("\
\\([a-zA-Z]?:?[^:( \t\n]+\\)[:(][ \t]*\\([0-9]+\\)\\([) \t]\\|\
:\\([^0-9\n]\\|\\([0-9]+:\\)\\)\\)" 1 bold t)
    ("\
\\([a-zA-Z]?:?[^:( \t\n]+\\)[:(][ \t]*\\([0-9]+\\)\\([) \t]\\|\
:\\([^0-9\n]\\|\\([0-9]+:\\)\\)\\)" 1 bold t)
    ;; verilog-vcs-1
    ("\\(Error\\|Warning\\):[^(]*(\\([^ \t]+\\) line *\\([0-9]+\\))" 2 bold t)
    ("\\(Error\\|Warning\\):[^(]*(\\([^ \t]+\\) line *\\([0-9]+\\))" 3 bold t)
    ;; verilog-vcs-2
    ("Warning:.*(port.*(\\([^ \t]+\\) line \\([0-9]+\\))" 1 bold t)
    ("Warning:.*(port.*(\\([^ \t]+\\) line \\([0-9]+\\))" 1 bold t)
    ;; verilog-vcs-3
    ("\\(Error\\|Warning\\):[\n.]*\\([^ \t]+\\) *\\([0-9]+\\):" 2 bold t)
    ("\\(Error\\|Warning\\):[\n.]*\\([^ \t]+\\) *\\([0-9]+\\):" 3 bold t)
    ;; verilog-vcs-4
    ("syntax error:.*\n\\([^ \t]+\\) *\\([0-9]+\\):" 1 bold t)
    ("syntax error:.*\n\\([^ \t]+\\) *\\([0-9]+\\):" 2 bold t)
    ;; verilog-verilator
    (".*\\(Error\\|Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):" 3 bold t)
    (".*\\(Error\\|Warning\\)\\(-[^:]+\\|\\):[\n ]*\\([^ \t:]+\\):\\([0-9]+\\):" 4 bold t)
    ;; verilog-leda
    ("^In file \\([^ \t]+\\)[ \t]+line[ \t]+\\([0-9]+\\):\n[^\n]*\n[^\n]*\n\\(Warning\\|Error\\|Failure\\)[^\n]*" 1 bold t)
    ("^In file \\([^ \t]+\\)[ \t]+line[ \t]+\\([0-9]+\\):\n[^\n]*\n[^\n]*\n\\(Warning\\|Error\\|Failure\\)[^\n]*" 2 bold t)
    )
  "Keywords to also highlight in Verilog *compilation* buffers.
Only used in XEmacs; GNU Emacs uses `verilog-error-regexp-emacs-alist'.")

(defcustom verilog-library-flags '("")
  "List of standard Verilog arguments to use for /*AUTOINST*/.
These arguments are used to find files for `verilog-auto', and match
the flags accepted by a standard Verilog-XL simulator.

    -f filename     Reads absolute `verilog-library-flags' from the filename.
    -F filename     Reads relative `verilog-library-flags' from the filename.
    +incdir+dir     Adds the directory to `verilog-library-directories'.
    -Idir           Adds the directory to `verilog-library-directories'.
    -y dir          Adds the directory to `verilog-library-directories'.
    +libext+.v      Adds the extensions to `verilog-library-extensions'.
    -v filename     Adds the filename to `verilog-library-files'.

    filename        Adds the filename to `verilog-library-files'.
                    This is not recommended, -v is a better choice.

You might want these defined in each file; put at the *END* of your file
something like:

    // Local Variables:
    // verilog-library-flags:(\"-y dir -y otherdir\")
    // End:

Verilog-mode attempts to detect changes to this local variable, but they
are only insured to be correct when the file is first visited.  Thus if you
have problems, use \\[find-alternate-file] RET to have these take effect.

See also the variables mentioned above."
  :group 'verilog-mode-auto
  :type '(repeat string))
(put 'verilog-library-flags 'safe-local-variable #'listp)

(defcustom verilog-library-directories '(".")
  "List of directories when looking for files for /*AUTOINST*/.
The directory may be relative to the current file, or absolute.
Environment variables are also expanded in the directory names.
Having at least the current directory is a good idea.

You might want these defined in each file; put at the *END* of your file
something like:

    // Local Variables:
    // verilog-library-directories:(\".\" \"subdir\" \"subdir2\")
    // End:

Verilog-mode attempts to detect changes to this local variable, but they
are only insured to be correct when the file is first visited.  Thus if you
have problems, use \\[find-alternate-file] RET to have these take effect.

See also `verilog-library-flags', `verilog-library-files'
and `verilog-library-extensions'."
  :group 'verilog-mode-auto
  :type '(repeat file))
(put 'verilog-library-directories 'safe-local-variable #'listp)

(defcustom verilog-library-files '()
  "List of files to search for modules.
AUTOINST will use this when it needs to resolve a module name.
This is a complete path, usually to a technology file with many standard
cells defined in it.

You might want these defined in each file; put at the *END* of your file
something like:

    // Local Variables:
    // verilog-library-files:(\"/path/technology.v\" \"/path2/tech2.v\")
    // End:

Verilog-mode attempts to detect changes to this local variable, but they
are only insured to be correct when the file is first visited.  Thus if you
have problems, use \\[find-alternate-file] RET to have these take effect.

See also `verilog-library-flags', `verilog-library-directories'."
  :group 'verilog-mode-auto
  :type '(repeat directory))
(put 'verilog-library-files 'safe-local-variable #'listp)

(defcustom verilog-library-extensions '(".v" ".va" ".sv")
  "List of extensions to use when looking for files for /*AUTOINST*/.
See also `verilog-library-flags', `verilog-library-directories'."
  :type '(repeat string)
  :group 'verilog-mode-auto)
(put 'verilog-library-extensions 'safe-local-variable #'listp)

(defcustom verilog-active-low-regexp nil
  "If true, treat signals matching this regexp as active low.
This is used for AUTORESET and AUTOTIEOFF.  For proper behavior,
you will probably also need `verilog-auto-reset-widths' set."
  :group 'verilog-mode-auto
  :type '(choice (const nil) regexp))
(put 'verilog-active-low-regexp 'safe-local-variable #'stringp)

(defcustom verilog-auto-sense-include-inputs nil
  "Non-nil means AUTOSENSE should include all inputs.
If nil, only inputs that are NOT output signals in the same block are
included."
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-sense-include-inputs 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-sense-defines-constant nil
  "Non-nil means AUTOSENSE should assume all defines represent constants.
When true, the defines will not be included in sensitivity lists.  To
maintain compatibility with other sites, this should be set at the bottom
of each Verilog file that requires it, rather than being set globally."
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-sense-defines-constant 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-simplify-expressions t
  "Non-nil means AUTOs will simplify expressions when calculating bit ranges.
When nil, do not simply ranges, which may simplify the output,
but may cause problems when there are multiple instantiations
outputting to the same wire.  To maintain compatibility with
other sites, this should be set at the bottom of each Verilog
file that requires it, rather than being set globally."
  :version "27.1"
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-simplify-expressions 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-reset-blocking-in-non t
  "Non-nil means AUTORESET will reset blocking statements.
When true, AUTORESET will reset in blocking statements those
signals which were assigned with blocking assignments (=) even in
a block with non-blocking assignments (<=).

If nil, all blocking assigned signals are ignored when any
non-blocking assignment is in the AUTORESET block.  This allows
blocking assignments to be used for temporary values and not have
those temporaries reset.  See example in `verilog-auto-reset'."
  :version "24.1"  ; rev718
  :type 'boolean
  :group 'verilog-mode-auto)
(put 'verilog-auto-reset-blocking-in-non 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-reset-widths t
  "Non-nil means AUTORESET should determine the width of signals.
This is then used to set the width of the zero (32'h0 for example).  This
is required by some lint tools that aren't smart enough to ignore widths of
the constant zero.  This may result in ugly code when parameters determine
the MSB or LSB of a signal inside an AUTORESET.

If nil, AUTORESET uses \"0\" as the constant.

If `unbased', AUTORESET used the unbased unsized literal \"\\='0\"
as the constant. This setting is strongly recommended for
SystemVerilog designs."
  :type 'boolean
  :group 'verilog-mode-auto)
(put 'verilog-auto-reset-widths 'safe-local-variable
     (lambda (x) (memq x '(nil t unbased))))

(defcustom verilog-assignment-delay ""
  "Text used for delays in delayed assignments.  Add a trailing space if set."
  :group 'verilog-mode-auto
  :type 'string)
(put 'verilog-assignment-delay 'safe-local-variable #'stringp)

(defcustom verilog-auto-arg-format 'packed
  "Formatting to use for AUTOARG signal names.
If `packed', then as many inputs and outputs that fit within
`fill-column' will be put onto one line.

If `single', then a single input or output will be put onto each
line."
  :version "25.1"
  :type '(radio (const :tag "Line up Assignments and Declarations" packed)
		(const :tag "Line up Assignment statements" single))
  :group 'verilog-mode-auto)
(put 'verilog-auto-arg-format 'safe-local-variable
     (lambda (x) (memq x '(packed single))))

(defcustom verilog-auto-arg-sort nil
  "Non-nil means AUTOARG signal names will be sorted, not in declaration order.
Declaration order is advantageous with order based instantiations
and is the default for backward compatibility.  Sorted order
reduces changes when declarations are moved around in a file, and
it's bad practice to rely on order based instantiations anyhow.

See also `verilog-auto-inst-sort'."
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-arg-sort 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-inst-dot-name nil
  "Non-nil means when creating ports with AUTOINST, use .name syntax.
This will use \".port\" instead of \".port(port)\" when possible.
This is only legal in SystemVerilog files, and will confuse older
simulators.  Setting `verilog-auto-inst-vector' to nil may also
be desirable to increase how often .name will be used."
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-inst-dot-name 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-inst-param-value nil
  "Non-nil means AUTOINST will replace parameters with the parameter value.
If nil, leave parameters as symbolic names.

Parameters must be in Verilog 2001 format #(...), and if a parameter is not
listed as such there (as when the default value is acceptable), it will not
be replaced, and will remain symbolic.

For example, imagine a submodule uses parameters to declare the size of its
inputs.  This is then used by an upper module:

        module InstModule (o,i);
           parameter WIDTH;
           input [WIDTH-1:0] i;
           parameter type OUT_t;
           output OUT_t o;
        endmodule

        module ExampParamVal1;
           /*AUTOOUTPUT*/
           // Beginning of automatic outputs
           output OUT_t o;
           // End of automatics

           InstModule
             #(.WIDTH(10),
               ,.OUT_t(upper_t))
            instName
             (/*AUTOINST*/
              .o        (o),
              .i        (i[WIDTH-1:0]));
        endmodule

       // Local Variables:
       // verilog-typedef-regexp: \"_t$\"
       // End:

Note even though WIDTH=10, the AUTOINST has left the parameter as
a symbolic name.  Likewise the OUT_t is preserved as the name
from the instantiated module.

If `verilog-auto-inst-param-value' is set, this will
instead expand to:

        module ExampParamVal1;
           /*AUTOOUTPUT*/
           // Beginning of automatic outputs
           output upper_t o;
           // End of automatics

           InstModule
             #(.WIDTH(10),
               ,.OUT_t(upper_t))
            instName
             (/*AUTOINST*/
              .o        (o),
              .i        (i[9:0]));

Note that the instantiation now has \"i[9:0]\" as the WIDTH
was expanded.  Likewise the data type of \"o\" in the AUTOOUTPUT
is now upper_t, from the OUT_t parameter override.
This second expansion of parameter types can be overridden with
`verilog-auto-inst-param-value-type'."
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-inst-param-value 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-inst-param-value-type t
  "Non-nil means expand parameter type in instantiations.
If nil, leave parameter types as symbolic names.

See `verilog-auto-inst-param-value'."
  :version "25.1"
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-inst-param-value-type 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-inst-sort nil
  "Non-nil means AUTOINST signals will be sorted, not in declaration order.
Also affects AUTOINSTPARAM.  Declaration order is the default for
backward compatibility, and as some teams prefer signals that are
declared together to remain together.  Sorted order reduces
changes when declarations are moved around in a file.  Sorting is
within input/output/inout groupings, there is intentionally no
option to intermix between input/output/inouts.

See also `verilog-auto-arg-sort'."
  :version "24.1"  ; rev688
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-inst-sort 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-inst-vector t
  "Non-nil means when creating default ports with AUTOINST, use bus subscripts.
If nil, skip the subscript when it matches the entire bus as declared in
the module (AUTOWIRE signals always are subscripted, you must manually
declare the wire to have the subscripts removed.)  Setting this to nil may
speed up some simulators, but is less general and harder to read, so avoid.
If `unsigned', use vectors for unsigned types (like using true,
otherwise no vectors if sizes match (like using nil)."
  :group 'verilog-mode-auto
  :type '(choice (const nil) (const t) (const unsigned)))
(put 'verilog-auto-inst-vector 'safe-local-variable
     (lambda (x) (memq x '(nil t unsigned))))

(defcustom verilog-auto-inst-template-numbers nil
  "If true, when creating templated ports with AUTOINST, add a comment.

If t, the comment will add the line number of the template that
was used for that port declaration.  This setting is suggested
only for debugging use, as regular use may cause a large numbers
of merge conflicts.

If `lhs', the comment will show the left hand side of the
AUTO_TEMPLATE rule that is matched.  This is less precise than
numbering (t) when multiple rules have the same pin name, but
won't merge conflict."
  :group 'verilog-mode-auto
  :type '(choice (const nil) (const t) (const lhs)))
(put 'verilog-auto-inst-template-numbers 'safe-local-variable
     (lambda (x) (memq x '(nil t lhs))))

(defcustom verilog-auto-inst-template-required nil
  "If non-nil, when creating a port with AUTOINST, require a template.
Any port which does not have a template will be omitted from the
instantiation.

If nil, if a port is not templated it will be inserted to connect
to a net with the same name as the port."
  :version "28.0"
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-inst-template-required 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-inst-column 40
  "Indent-to column number for net name part of AUTOINST created pin."
  :group 'verilog-mode-indent
  :type 'integer)
(put 'verilog-auto-inst-column 'safe-local-variable #'integerp)

(defcustom verilog-auto-inst-interfaced-ports nil
  "Non-nil means include interfaced ports in AUTOINST expansions."
  :version "24.3"  ; rev773, default change rev815
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-inst-interfaced-ports 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-input-ignore-regexp nil
  "If non-nil, when creating AUTOINPUT, ignore signals matching this regexp.
See the \\[verilog-faq] for examples on using this."
  :group 'verilog-mode-auto
  :type '(choice (const nil) regexp))
(put 'verilog-auto-input-ignore-regexp 'safe-local-variable #'stringp)

(defcustom verilog-auto-reg-input-assigned-ignore-regexp nil
  "If non-nil, when creating AUTOINPUTREG, ignore signals matching this regexp."
  :version "27.1"
  :group 'verilog-mode-auto
  :type '(choice (const nil) regexp))
(put 'verilog-auto-reg-input-assigned-ignore-regexp 'safe-local-variable #'stringp)

(defcustom verilog-auto-inout-ignore-regexp nil
  "If non-nil, when creating AUTOINOUT, ignore signals matching this regexp.
See the \\[verilog-faq] for examples on using this."
  :group 'verilog-mode-auto
  :type '(choice (const nil) regexp))
(put 'verilog-auto-inout-ignore-regexp 'safe-local-variable #'stringp)

(defcustom verilog-auto-output-ignore-regexp nil
  "If non-nil, when creating AUTOOUTPUT, ignore signals matching this regexp.
See the \\[verilog-faq] for examples on using this."
  :group 'verilog-mode-auto
  :type '(choice (const nil) regexp))
(put 'verilog-auto-output-ignore-regexp 'safe-local-variable #'stringp)

(defcustom verilog-auto-template-warn-unused nil
  "Non-nil means report warning if an AUTO_TEMPLATE line is not used.
This feature is not supported before Emacs 21.1 or XEmacs 21.4."
  :version "24.3"  ; rev787
  :group 'verilog-mode-auto
  :type 'boolean)
(put 'verilog-auto-template-warn-unused 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-auto-tieoff-declaration "wire"
  "Data type used for the declaration for AUTOTIEOFF.
If \"wire\" then create a wire, if \"assign\" create an
assignment, else the data type for variable creation."
  :version "24.1"  ; rev713
  :group 'verilog-mode-auto
  :type 'string)
(put 'verilog-auto-tieoff-declaration 'safe-local-variable #'stringp)

(defcustom verilog-auto-tieoff-ignore-regexp nil
  "If non-nil, when creating AUTOTIEOFF, ignore signals matching this regexp.
See the \\[verilog-faq] for examples on using this."
  :group 'verilog-mode-auto
  :type '(choice (const nil) regexp))
(put 'verilog-auto-tieoff-ignore-regexp 'safe-local-variable #'stringp)

(defcustom verilog-auto-unused-ignore-regexp nil
  "If non-nil, when creating AUTOUNUSED, ignore signals matching this regexp.
See the \\[verilog-faq] for examples on using this."
  :group 'verilog-mode-auto
  :type '(choice (const nil) regexp))
(put 'verilog-auto-unused-ignore-regexp 'safe-local-variable #'stringp)

(defcustom verilog-case-fold t
  "Non-nil means `verilog-mode' regexps should ignore case.
This variable is t for backward compatibility; nil is suggested."
  :version "24.4"
  :group 'verilog-mode
  :type 'boolean)
(put 'verilog-case-fold 'safe-local-variable #'verilog-booleanp)

(defcustom verilog-typedef-regexp nil
  "If non-nil, regular expression that matches Verilog-2001 typedef names.
For example, \"_t$\" matches typedefs named with _t, as in the C language.
See also `verilog-case-fold'."
  :group 'verilog-mode-auto
  :type '(choice (const nil) regexp))
(put 'verilog-typedef-regexp 'safe-local-variable #'stringp)

(defcustom verilog-mode-hook (list #'verilog-set-compile-command)
  "Hook run after Verilog mode is loaded."
  :type 'hook
  :group 'verilog-mode)

(defcustom verilog-auto-hook nil
  "Hook run after `verilog-mode' updates AUTOs."
  :group 'verilog-mode-auto
  :type 'hook)

(defcustom verilog-before-auto-hook nil
  "Hook run before `verilog-mode' updates AUTOs."
  :group 'verilog-mode-auto
  :type 'hook)

(defcustom verilog-delete-auto-hook nil
  "Hook run after `verilog-mode' deletes AUTOs."
  :group 'verilog-mode-auto
  :type 'hook)

(defcustom verilog-before-delete-auto-hook nil
  "Hook run before `verilog-mode' deletes AUTOs."
  :group 'verilog-mode-auto
  :type 'hook)

(defcustom verilog-getopt-flags-hook nil
  "Hook run after `verilog-getopt-flags' determines the Verilog option lists."
  :group 'verilog-mode-auto
  :type 'hook)

(defcustom verilog-before-getopt-flags-hook nil
  "Hook run before `verilog-getopt-flags' determines the Verilog option lists."
  :group 'verilog-mode-auto
  :type 'hook)

(defcustom verilog-before-save-font-hook nil
  "Hook run before `verilog-save-font-no-change-functions' removes highlighting."
  :version "24.3"  ; rev735
  :group 'verilog-mode-auto
  :type 'hook)

(defcustom verilog-after-save-font-hook nil
  "Hook run after `verilog-save-font-no-change-functions' restores highlighting."
  :version "24.3"  ; rev735
  :group 'verilog-mode-auto
  :type 'hook)

(defvar verilog-imenu-generic-expression
  '((nil            "^\\s-*\\(?:connectmodule\\|m\\(?:odule\\|acromodule\\)\\|p\\(?:rimitive\\|rogram\\|ackage\\)\\)\\s-+\\([a-zA-Z0-9_.:]+\\)" 1)
    ("*Variables*"  "^\\s-*\\(reg\\|wire\\|logic\\)\\s-+\\(\\|\\[[^]]+\\]\\s-+\\)\\([A-Za-z0-9_]+\\)" 3)
    ("*Classes*"    "^\\s-*\\(?:\\(?:virtual\\|interface\\)\\s-+\\)?class\\s-+\\([A-Za-z_][A-Za-z0-9_]+\\)" 1)
    ("*Tasks*"      "^\\s-*\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*task\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\([A-Za-z_][A-Za-z0-9_:]+\\)" 1)
    ("*Functions*"  "^\\s-*\\(?:\\(?:static\\|pure\\|virtual\\|local\\|protected\\)\\s-+\\)*function\\s-+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\(?:\\w+\\s-+\\)?\\(?:\\(?:un\\)signed\\s-+\\)?\\([A-Za-z_][A-Za-z0-9_:]+\\)" 1)
    ("*Interfaces*" "^\\s-*interface\\s-+\\([a-zA-Z_0-9]+\\)" 1)
    ("*Types*"      "^\\s-*typedef\\s-+.*\\s-+\\([a-zA-Z_0-9]+\\)\\s-*;" 1))
  "Imenu expression for Verilog mode.  See `imenu-generic-expression'.")

;;
;; provide a verilog-header function.
;; Customization variables:
;;
(defvar verilog-date-scientific-format nil
  "If non-nil, dates are written in scientific format (e.g.  1997/09/17).
If nil, in European format (e.g.  17.09.1997).  The brain-dead American
format (e.g.  09/17/1997) is not supported.")

(defvar verilog-company nil
  "Default name of Company for Verilog header.
If set will become buffer local.")
(make-variable-buffer-local 'verilog-company)

(defvar verilog-project nil
  "Default name of Project for Verilog header.
If set will become buffer local.")
(make-variable-buffer-local 'verilog-project)

;;; Keymap and Menu:
;;

(defvar verilog-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map ";"        #'electric-verilog-semi)
    (define-key map [(control 59)]    #'electric-verilog-semi-with-comment)
    (define-key map ":"        #'electric-verilog-colon)
    ;;(define-key map "="        'electric-verilog-equal)
    (define-key map "`"        #'electric-verilog-tick)
    (define-key map "\t"       #'electric-verilog-tab)
    (define-key map "\r"       #'electric-verilog-terminate-line)
    ;; backspace/delete key bindings
    (define-key map [backspace]    #'backward-delete-char-untabify)
    (unless (boundp 'delete-key-deletes-forward) ; XEmacs variable
      (define-key map [delete]       #'delete-char)
      (define-key map [(meta delete)] #'kill-word))
    (define-key map "\M-\C-b"  #'electric-verilog-backward-sexp)
    (define-key map "\M-\C-f"  #'electric-verilog-forward-sexp)
    (define-key map "\M-\r"    #'electric-verilog-terminate-and-indent)
    (define-key map "\M-\t"    (if (fboundp 'completion-at-point)
                                   #'completion-at-point #'verilog-complete-word))
    (define-key map "\M-?"     (if (fboundp 'completion-help-at-point)
                                   #'completion-help-at-point #'verilog-show-completions))
    ;; Note \C-c and letter are reserved for users
    (define-key map "\C-c`"    #'verilog-lint-off)
    (define-key map "\C-c*"    #'verilog-delete-auto-star-implicit)
    (define-key map "\C-c?"    #'verilog-diff-auto)
    (define-key map "\C-c\C-r" #'verilog-label-be)
    (define-key map "\C-c\C-i" #'verilog-pretty-declarations)
    (define-key map "\C-c="    #'verilog-pretty-expr)
    (define-key map "\C-c/"    #'verilog-star-comment)
    (define-key map "\C-c\C-c" #'verilog-comment-region)
    (define-key map "\C-c\C-u" #'verilog-uncomment-region)
    (define-key map "\M-\C-h"  #'verilog-mark-defun)
    (define-key map "\M-\C-a"  #'verilog-beg-of-defun)
    (define-key map "\M-\C-e"  #'verilog-end-of-defun)
    (define-key map "\C-c\C-d" #'verilog-goto-defun)
    (define-key map "\C-c\C-k" #'verilog-delete-auto)
    (define-key map "\C-c\C-a" #'verilog-auto)
    (define-key map "\C-c\C-s" #'verilog-auto-save-compile)
    (define-key map "\C-c\C-p" #'verilog-preprocess)
    (define-key map "\C-c\C-z" #'verilog-inject-auto)
    (define-key map "\C-c\C-e" #'verilog-expand-vector)
    (define-key map "\C-c\C-h" #'verilog-header)
    map)
  "Keymap used in Verilog mode.")

;; menus
(easy-menu-define verilog-menu verilog-mode-map
  "Menu for Verilog mode."
  (verilog-easy-menu-filter
   `("Verilog"
     ("Choose Compilation Action"
      ["None"
       (progn
	 (setq verilog-tool nil)
	 (verilog-set-compile-command))
       :style radio
       :selected (equal verilog-tool nil)
       :help "When invoking compilation, use compile-command"]
      ["Lint"
       (progn
	 (setq verilog-tool 'verilog-linter)
	 (verilog-set-compile-command))
       :style radio
       :selected (equal verilog-tool 'verilog-linter)
       :help "When invoking compilation, use lint checker"]
      ["Coverage"
       (progn
	 (setq verilog-tool 'verilog-coverage)
	 (verilog-set-compile-command))
       :style radio
       :selected (equal verilog-tool 'verilog-coverage)
       :help "When invoking compilation, annotate for coverage"]
      ["Simulator"
       (progn
	 (setq verilog-tool 'verilog-simulator)
	 (verilog-set-compile-command))
       :style radio
       :selected (equal verilog-tool 'verilog-simulator)
       :help "When invoking compilation, interpret Verilog source"]
      ["Compiler"
       (progn
	 (setq verilog-tool 'verilog-compiler)
	 (verilog-set-compile-command))
       :style radio
       :selected (equal verilog-tool 'verilog-compiler)
       :help "When invoking compilation, compile Verilog source"]
      ["Preprocessor"
       (progn
	 (setq verilog-tool 'verilog-preprocessor)
	 (verilog-set-compile-command))
       :style radio
       :selected (equal verilog-tool 'verilog-preprocessor)
       :help "When invoking compilation, preprocess Verilog source, see also `verilog-preprocess'"]
      )
     ("Move"
      ["Beginning of function"		verilog-beg-of-defun
       :keys "C-M-a"
       :help		"Move backward to the beginning of the current function or procedure"]
      ["End of function"		verilog-end-of-defun
       :keys "C-M-e"
       :help		"Move forward to the end of the current function or procedure"]
      ["Mark function"			verilog-mark-defun
       :keys "C-M-h"
       :help		"Mark the current Verilog function or procedure"]
      ["Goto function/module"		verilog-goto-defun
       :help		"Move to specified Verilog module/task/function"]
      ["Move to beginning of block"	electric-verilog-backward-sexp
       :help		"Move backward over one balanced expression"]
      ["Move to end of block"		electric-verilog-forward-sexp
       :help		"Move forward over one balanced expression"]
      )
     ("Comments"
      ["Comment Region"			verilog-comment-region
       :help		"Put marked area into a comment"]
      ["UnComment Region"		verilog-uncomment-region
       :help		"Uncomment an area commented with Comment Region"]
      ["Multi-line comment insert"	verilog-star-comment
       :help		"Insert Verilog /* */ comment at point"]
      ["Lint error to comment"		verilog-lint-off
       :help		"Convert a Verilog linter warning line into a disable statement"]
      )
     "----"
     ["Compile"				compile
      :help		"Perform compilation-action (above) on the current buffer"]
     ["AUTO, Save, Compile"		verilog-auto-save-compile
      :help		"Recompute AUTOs, save buffer, and compile"]
     ["Next Compile Error"		next-error
      :help		"Visit next compilation error message and corresponding source code"]
     ["Ignore Lint Warning at point"	verilog-lint-off
      :help		"Convert a Verilog linter warning line into a disable statement"]
     "----"
     ["Line up declarations around point"	verilog-pretty-declarations
      :help		"Line up declarations around point"]
     ["Line up equations around point"		verilog-pretty-expr
      :help		"Line up expressions around point"]
     ["Redo/insert comments on every end"	verilog-label-be
      :help		"Label matching begin ... end statements"]
     ["Expand [x:y] vector line"	verilog-expand-vector
      :help		"Take a signal vector on the current line and expand it to multiple lines"]
     ["Insert begin-end block"		verilog-insert-block
      :help		"Insert begin ... end"]
     ["Complete word" ,(if (fboundp 'completion-at-point)
                           'completion-at-point 'verilog-complete-word)
      :help		"Complete word at point"]
     "----"
     ["Recompute AUTOs"			verilog-auto
      :help		"Expand AUTO meta-comment statements"]
     ["Kill AUTOs"			verilog-delete-auto
      :help		"Remove AUTO expansions"]
     ["Diff AUTOs"			verilog-diff-auto
      :help		"Show differences in AUTO expansions"]
     ["Inject AUTOs"			verilog-inject-auto
      :help		"Inject AUTOs into legacy non-AUTO buffer"]
     ("AUTO Help..."
      ["AUTO General"			(describe-function 'verilog-auto)
       :help		"Help introduction on AUTOs"]
      ["AUTO Library Flags"		(describe-variable 'verilog-library-flags)
       :help		"Help on verilog-library-flags"]
      ["AUTO Library Path"		(describe-variable 'verilog-library-directories)
       :help		"Help on verilog-library-directories"]
      ["AUTO Library Files"		(describe-variable 'verilog-library-files)
       :help		"Help on verilog-library-files"]
      ["AUTO Library Extensions"	(describe-variable 'verilog-library-extensions)
       :help		"Help on verilog-library-extensions"]
      ["AUTO `define Reading"		(describe-function 'verilog-read-defines)
       :help		"Help on reading `defines"]
      ["AUTO `include Reading"		(describe-function 'verilog-read-includes)
       :help		"Help on parsing `includes"]
      ["AUTOARG"			(describe-function 'verilog-auto-arg)
       :help		"Help on AUTOARG - declaring module port list"]
      ["AUTOASCIIENUM"			(describe-function 'verilog-auto-ascii-enum)
       :help		"Help on AUTOASCIIENUM - creating ASCII for enumerations"]
      ["AUTOASSIGNMODPORT"		(describe-function 'verilog-auto-assign-modport)
       :help		"Help on AUTOASSIGNMODPORT - creating assignments to/from modports"]
      ["AUTOINOUT"			(describe-function 'verilog-auto-inout)
       :help		"Help on AUTOINOUT - adding inouts from cells"]
      ["AUTOINOUTCOMP"			(describe-function 'verilog-auto-inout-comp)
       :help		"Help on AUTOINOUTCOMP - copying complemented i/o from another file"]
      ["AUTOINOUTIN"			(describe-function 'verilog-auto-inout-in)
       :help		"Help on AUTOINOUTIN - copying i/o from another file as all inputs"]
      ["AUTOINOUTMODPORT"		(describe-function 'verilog-auto-inout-modport)
       :help		"Help on AUTOINOUTMODPORT - copying i/o from an interface modport"]
      ["AUTOINOUTMODULE"		(describe-function 'verilog-auto-inout-module)
       :help		"Help on AUTOINOUTMODULE - copying i/o from another file"]
      ["AUTOINOUTPARAM"			(describe-function 'verilog-auto-inout-param)
       :help		"Help on AUTOINOUTPARAM - copying parameters from another file"]
      ["AUTOINPUT"			(describe-function 'verilog-auto-input)
       :help		"Help on AUTOINPUT - adding inputs from cells"]
      ["AUTOINSERTLISP"			(describe-function 'verilog-auto-insert-lisp)
       :help		"Help on AUTOINSERTLISP - insert text from a lisp function"]
      ["AUTOINSERTLAST"			(describe-function 'verilog-auto-insert-last)
       :help		"Help on AUTOINSERTLISPLAST - insert text from a lisp function"]
      ["AUTOINST"			(describe-function 'verilog-auto-inst)
       :help		"Help on AUTOINST - adding pins for cells"]
      ["AUTOINST (.*)"			(describe-function 'verilog-auto-star)
       :help		"Help on expanding Verilog-2001 .* pins"]
      ["AUTOINSTPARAM"			(describe-function 'verilog-auto-inst-param)
       :help		"Help on AUTOINSTPARAM - adding parameter pins to cells"]
      ["AUTOLOGIC"			(describe-function 'verilog-auto-logic)
       :help		"Help on AUTOLOGIC - declaring logic signals"]
      ["AUTOOUTPUT"			(describe-function 'verilog-auto-output)
       :help		"Help on AUTOOUTPUT - adding outputs from cells"]
      ["AUTOOUTPUTEVERY"		(describe-function 'verilog-auto-output-every)
       :help		"Help on AUTOOUTPUTEVERY - adding outputs of all signals"]
      ["AUTOREG"			(describe-function 'verilog-auto-reg)
       :help		"Help on AUTOREG - declaring registers for non-wires"]
      ["AUTOREGINPUT"			(describe-function 'verilog-auto-reg-input)
       :help		"Help on AUTOREGINPUT - declaring inputs for non-wires"]
      ["AUTORESET"			(describe-function 'verilog-auto-reset)
       :help		"Help on AUTORESET - resetting always blocks"]
      ["AUTOSENSE or AS"		(describe-function 'verilog-auto-sense)
       :help		"Help on AUTOSENSE - sensitivity lists for always blocks"]
      ["AUTOTIEOFF"			(describe-function 'verilog-auto-tieoff)
       :help		"Help on AUTOTIEOFF - tying off unused outputs"]
      ["AUTOUNDEF"			(describe-function 'verilog-auto-undef)
       :help		"Help on AUTOUNDEF - undefine all local defines"]
      ["AUTOUNUSED"			(describe-function 'verilog-auto-unused)
       :help		"Help on AUTOUNUSED - terminating unused inputs"]
      ["AUTOWIRE"			(describe-function 'verilog-auto-wire)
       :help		"Help on AUTOWIRE - declaring wires for cells"]
      )
     "----"
     ["Submit bug report"		verilog-submit-bug-report
      :help		"Submit via mail a bug report on verilog-mode.el"]
     ["Version and FAQ"			verilog-faq
      :help		"Show the current version, and where to get the FAQ etc"]
     ["Customize Verilog Mode..."	verilog-customize
      :help		"Customize variables and other settings used by Verilog-Mode"]
     ["Customize Verilog Fonts & Colors"	verilog-font-customize
      :help		"Customize fonts used by Verilog-Mode."])))

(easy-menu-define
  verilog-stmt-menu verilog-mode-map "Menu for statement templates in Verilog."
  (verilog-easy-menu-filter
   '("Statements"
     ["Header"		verilog-sk-header
      :help		"Insert a header block at the top of file"]
     ["Comment"		verilog-sk-comment
      :help		"Insert a comment block"]
     "----"
     ["Module"		verilog-sk-module
      :help		"Insert a module .. (/*AUTOARG*/);.. endmodule block"]
     ["OVM Class"	verilog-sk-ovm-class
      :help		"Insert an OVM class block"]
     ["UVM Object"	verilog-sk-uvm-object
      :help		"Insert an UVM object block"]
     ["UVM Component"	verilog-sk-uvm-component
      :help		"Insert an UVM component block"]
     ["Primitive"	verilog-sk-primitive
      :help		"Insert a primitive .. (.. );.. endprimitive block"]
     "----"
     ["Input"		verilog-sk-input
      :help		"Insert an input declaration"]
     ["Output"		verilog-sk-output
      :help		"Insert an output declaration"]
     ["Inout"		verilog-sk-inout
      :help		"Insert an inout declaration"]
     ["Wire"		verilog-sk-wire
      :help		"Insert a wire declaration"]
     ["Reg"		verilog-sk-reg
      :help		"Insert a register declaration"]
     ["Define thing under point as a register" verilog-sk-define-signal
      :help		"Define signal under point as a register at the top of the module"]
     "----"
     ["Initial"		verilog-sk-initial
      :help		"Insert an initial begin .. end block"]
     ["Always"		verilog-sk-always
      :help		"Insert an always @(AS) begin .. end block"]
     ["Function"	verilog-sk-function
      :help		"Insert a function .. begin .. end endfunction block"]
     ["Task"		verilog-sk-task
      :help		"Insert a task .. begin .. end endtask block"]
     ["Specify"		verilog-sk-specify
      :help		"Insert a specify .. endspecify block"]
     ["Generate"	verilog-sk-generate
      :help		"Insert a generate .. endgenerate block"]
     "----"
     ["Begin"		verilog-sk-begin
      :help		"Insert a begin .. end block"]
     ["If"		verilog-sk-if
      :help		"Insert an if (..) begin .. end block"]
     ["(if) else"	verilog-sk-else-if
      :help		"Insert an else if (..) begin .. end block"]
     ["For"		verilog-sk-for
      :help		"Insert a for (...) begin .. end block"]
     ["While"		verilog-sk-while
      :help		"Insert a while (...) begin .. end block"]
     ["Fork"		verilog-sk-fork
      :help		"Insert a fork begin .. end .. join block"]
     ["Repeat"		verilog-sk-repeat
      :help		"Insert a repeat (..) begin .. end block"]
     ["Case"		verilog-sk-case
      :help		"Insert a case block, prompting for details"]
     ["Casex"		verilog-sk-casex
      :help		"Insert a casex (...) item: begin.. end endcase block"]
     ["Casez"		verilog-sk-casez
      :help		"Insert a casez (...) item: begin.. end endcase block"])))

(defvar verilog-mode-abbrev-table nil
  "Abbrev table in use in Verilog-mode buffers.")

;;(makunbound 'verilog-mode-abbrev-table) ; For testing, clear out old defvar
(verilog-define-abbrev-table
 'verilog-mode-abbrev-table ()
 "Abbrev table for Verilog mode skeletons."
 :case-fixed t
 ;; Only expand in code.
 :enable-function (lambda () (not (verilog-in-comment-or-string-p))))
(verilog-define-abbrev verilog-mode-abbrev-table "class" "" 'verilog-sk-ovm-class)
(verilog-define-abbrev verilog-mode-abbrev-table "always" "" 'verilog-sk-always)
(verilog-define-abbrev verilog-mode-abbrev-table "begin" nil 'verilog-sk-begin)
(verilog-define-abbrev verilog-mode-abbrev-table "case" "" 'verilog-sk-case)
(verilog-define-abbrev verilog-mode-abbrev-table "for" "" 'verilog-sk-for)
(verilog-define-abbrev verilog-mode-abbrev-table "generate" "" 'verilog-sk-generate)
(verilog-define-abbrev verilog-mode-abbrev-table "initial" "" 'verilog-sk-initial)
(verilog-define-abbrev verilog-mode-abbrev-table "fork" "" 'verilog-sk-fork)
(verilog-define-abbrev verilog-mode-abbrev-table "module" "" 'verilog-sk-module)
(verilog-define-abbrev verilog-mode-abbrev-table "primitive" "" 'verilog-sk-primitive)
(verilog-define-abbrev verilog-mode-abbrev-table "repeat" "" 'verilog-sk-repeat)
(verilog-define-abbrev verilog-mode-abbrev-table "specify" "" 'verilog-sk-specify)
(verilog-define-abbrev verilog-mode-abbrev-table "task" "" 'verilog-sk-task)
(verilog-define-abbrev verilog-mode-abbrev-table "while" "" 'verilog-sk-while)
(verilog-define-abbrev verilog-mode-abbrev-table "casex" "" 'verilog-sk-casex)
(verilog-define-abbrev verilog-mode-abbrev-table "casez" "" 'verilog-sk-casez)
(verilog-define-abbrev verilog-mode-abbrev-table "if" "" 'verilog-sk-if)
(verilog-define-abbrev verilog-mode-abbrev-table "else if" "" 'verilog-sk-else-if)
(verilog-define-abbrev verilog-mode-abbrev-table "assign" "" 'verilog-sk-assign)
(verilog-define-abbrev verilog-mode-abbrev-table "function" "" 'verilog-sk-function)
(verilog-define-abbrev verilog-mode-abbrev-table "input" "" 'verilog-sk-input)
(verilog-define-abbrev verilog-mode-abbrev-table "output" "" 'verilog-sk-output)
(verilog-define-abbrev verilog-mode-abbrev-table "inout" "" 'verilog-sk-inout)
(verilog-define-abbrev verilog-mode-abbrev-table "wire" "" 'verilog-sk-wire)
(verilog-define-abbrev verilog-mode-abbrev-table "reg" "" 'verilog-sk-reg)

;;
;;  Macros
;;

(defsubst verilog-within-string ()
  (nth 3 (parse-partial-sexp (line-beginning-position) (point))))

(defsubst verilog-string-match-fold (regexp string &optional start)
  "Like `string-match', but use `verilog-case-fold'.
Return index of start of first match for REGEXP in STRING, or nil.
Matching ignores case if `verilog-case-fold' is non-nil.
If third arg START is non-nil, start search at that index in STRING."
  (let ((case-fold-search verilog-case-fold))
    (string-match regexp string start)))

(defsubst verilog-string-replace-matches (from-string to-string fixedcase literal string)
  "Replace occurrences of FROM-STRING with TO-STRING.
FIXEDCASE and LITERAL as in `replace-match'.  STRING is what to replace.
The case (verilog-string-replace-matches \"o\" \"oo\" nil nil \"foobar\")
will break, as the o's continuously replace.  xa -> x works ok though."
  ;; Hopefully soon to an Emacs built-in
  ;; Also note \ in the replacement prevent multiple replacements; IE
  ;;   (verilog-string-replace-matches "@" "\\\\([0-9]+\\\\)" nil nil "wire@_@")
  ;;   Gives "wire\([0-9]+\)_@" not "wire\([0-9]+\)_\([0-9]+\)"
  (let ((start 0))
    (while (string-match from-string string start)
      (setq string (replace-match to-string fixedcase literal string)
	    start (min (length string) (+ (match-beginning 0) (length to-string)))))
    string))

(defsubst verilog-string-remove-spaces (string)
  "Remove spaces surrounding STRING."
  (save-match-data
    (setq string (verilog-string-replace-matches "^\\s-+" "" nil nil string))
    (setq string (verilog-string-replace-matches "\\s-+$" "" nil nil string))
    string))

(defsubst verilog-re-search-forward (REGEXP BOUND NOERROR)
  ;; checkdoc-params: (REGEXP BOUND NOERROR)
  "Like `re-search-forward', but skips over match in comments or strings."
  (let ((mdata '(nil nil)))  ; So match-end will return nil if no matches found
    (while (and
	    (re-search-forward REGEXP BOUND NOERROR)
	    (setq mdata (match-data))
	    (and (verilog-skip-forward-comment-or-string)
		 (progn
		   (setq mdata '(nil nil))
		   (if BOUND
		       (< (point) BOUND)
		     t)))))
    (store-match-data mdata)
    (match-end 0)))

(defsubst verilog-re-search-backward (REGEXP BOUND NOERROR)
  ;; checkdoc-params: (REGEXP BOUND NOERROR)
  "Like `re-search-backward', but skips over match in comments or strings."
  (let ((mdata '(nil nil)))  ; So match-end will return nil if no matches found
    (while (and
	    (re-search-backward REGEXP BOUND NOERROR)
	    (setq mdata (match-data))
	    (and (verilog-skip-backward-comment-or-string)
		 (progn
		   (setq mdata '(nil nil))
		   (if BOUND
		       (> (point) BOUND)
		     t)))))
    (store-match-data mdata)
    (match-end 0)))

(defsubst verilog-re-search-forward-quick (regexp bound noerror)
  "Like `verilog-re-search-forward', including use of REGEXP BOUND and NOERROR,
but trashes match data and is faster for REGEXP that doesn't match often.
This uses `verilog-scan' and text properties to ignore comments,
so there may be a large up front penalty for the first search."
  (let (pt)
    (while (and (not pt)
		(re-search-forward regexp bound noerror))
      (if (verilog-inside-comment-or-string-p (match-beginning 0))
          (re-search-forward "[/\"\n]" nil t)  ; Only way a comment or quote can end
	(setq pt (match-end 0))))
    pt))

(defsubst verilog-re-search-backward-quick (regexp bound noerror)
  ;; checkdoc-params: (REGEXP BOUND NOERROR)
  "Like `verilog-re-search-backward', including use of REGEXP BOUND and NOERROR,
but trashes match data and is faster for REGEXP that doesn't match often.
This uses `verilog-scan' and text properties to ignore comments,
so there may be a large up front penalty for the first search."
  (let (pt)
    (while (and (not pt)
		(re-search-backward regexp bound noerror))
      (if (verilog-inside-comment-or-string-p (match-beginning 0))
          (re-search-backward "[/\"]" nil t)  ; Only way a comment or quote can begin
	(setq pt (match-beginning 0))))
    pt))

(defsubst verilog-re-search-forward-substr (substr regexp bound noerror)
  "Like `re-search-forward', but first search for SUBSTR constant.
Then searched for the normal REGEXP (which contains SUBSTR), with given
BOUND and NOERROR.  The REGEXP must fit within a single line.
This speeds up complicated regexp matches."
  ;; Problem with overlap: search-forward BAR then FOOBARBAZ won't match.
  ;; thus require matches to be on one line, and use beginning-of-line.
  (let (done)
    (while (and (not done)
		(search-forward substr bound noerror))
      (save-excursion
	(beginning-of-line)
        (setq done (re-search-forward regexp (line-end-position) noerror)))
      (unless (and (<= (match-beginning 0) (point))
		   (>= (match-end 0) (point)))
	(setq done nil)))
    (when done (goto-char done))
    done))
;;(verilog-re-search-forward-substr "-end" "get-end-of" nil t)  ; -end (test bait)

(defsubst verilog-re-search-backward-substr (substr regexp bound noerror)
  "Like `re-search-backward', but first search for SUBSTR constant.
Then searched for the normal REGEXP (which contains SUBSTR), with given
BOUND and NOERROR.  The REGEXP must fit within a single line.
This speeds up complicated regexp matches."
  ;; Problem with overlap: search-backward BAR then FOOBARBAZ won't match.
  ;; thus require matches to be on one line, and use beginning-of-line.
  (let (done)
    (while (and (not done)
		(search-backward substr bound noerror))
      (save-excursion
	(end-of-line)
        (setq done (re-search-backward regexp (line-beginning-position) noerror)))
      (unless (and (<= (match-beginning 0) (point))
		   (>= (match-end 0) (point)))
	(setq done nil)))
    (when done (goto-char done))
    done))
;;(verilog-re-search-backward-substr "-end" "get-end-of" nil t)  ; -end (test bait)

(defun verilog-delete-trailing-whitespace ()
  "Delete trailing spaces or tabs, but not newlines nor linefeeds.
Also add missing final newline.

To call this from the command line, see \\[verilog-batch-diff-auto].

To call on \\[verilog-auto], set `verilog-auto-delete-trailing-whitespace'."
  ;; Similar to `delete-trailing-whitespace' but that's not present in XEmacs
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "[ \t]+$" nil t)  ; Not syntactic WS as no formfeed
      (replace-match "" nil nil))
    (goto-char (point-max))
    (unless (bolp) (insert "\n"))))

(defvar compile-command)
;; These are known to be from other packages and may not be defined
(defvar diff-command)
;; There are known to be from newer versions of Emacs
(defvar create-lockfiles)  ; Emacs 24
(defvar which-func-modes)

;; compilation program
(defun verilog-set-compile-command ()
  "Function to compute shell command to compile Verilog.

This reads `verilog-tool' and sets `compile-command'.  This specifies the
program that executes when you type \\[compile] or
\\[verilog-auto-save-compile].

By default `verilog-tool' uses a Makefile if one exists in the
current directory.  If not, it is set to the `verilog-linter',
`verilog-compiler', `verilog-coverage', `verilog-preprocessor',
or `verilog-simulator' variables, as selected with the Verilog ->
\"Choose Compilation Action\" menu.

You should set `verilog-tool' or the other variables to the path and
arguments for your Verilog simulator.  For example:
    \"vcs -p123 -O\"
or a string like:
    \"(cd /tmp; surecov %s)\".

In the former case, the path to the current buffer is concat'ed to the
value of `verilog-tool'; in the later, the path to the current buffer is
substituted for the %s.

Where __FLAGS__ appears in the string `verilog-current-flags'
will be substituted.

Where __FILE__ appears in the string, the variable
`buffer-file-name' of the current buffer, without the directory
portion, will be substituted."
  (interactive)
  (cond
   ((or (file-exists-p "makefile")	;If there is a makefile, use it
	(file-exists-p "Makefile"))
    (set (make-local-variable 'compile-command) "make "))
   (t
    (set (make-local-variable 'compile-command)
	 (if verilog-tool
            (let ((cmd (symbol-value verilog-tool)))
              (if (string-match "%s" cmd)
                  (format cmd (or buffer-file-name ""))
                (concat cmd " " (or buffer-file-name ""))))
	   ""))))
  (verilog-modify-compile-command))

(defun verilog-expand-command (command)
  "Replace meta-information in COMMAND and return it.
Where __FLAGS__ appears in the string `verilog-current-flags'
will be substituted.  Where __FILE__ appears in the string, the
current buffer's file-name, without the directory portion, will
be substituted."
  (setq command (verilog-string-replace-matches
		 ;; Note \\b only works if under verilog syntax table
		 "\\b__FLAGS__\\b" (verilog-current-flags)
		 t t command))
  (setq command (verilog-string-replace-matches
		 "\\b__FILE__\\b" (file-name-nondirectory
                                 (or (buffer-file-name) ""))
		 t t command))
  command)

;; Eliminate compile warning
(defvar verilog-compile-command-pre-mod)
(defvar verilog-compile-command-post-mod)

(defun verilog-modify-compile-command ()
  "Update `compile-command' using `verilog-expand-command'."
  ;; Entry into verilog-mode a call to this before Local Variables exist
  ;; Likewise user may have hook or something that changes the flags.
  ;; So, remember we're responsible for the expansion and on re-entry
  ;; recompute __FLAGS__ on each reentry.
  (when (stringp compile-command)
    (when (and
           (boundp 'verilog-compile-command-post-mod)
           (equal compile-command verilog-compile-command-post-mod))
      (setq compile-command verilog-compile-command-pre-mod))
    (when (and
           (string-match "\\b\\(__FLAGS__\\|__FILE__\\)\\b" compile-command))
      (set (make-local-variable 'verilog-compile-command-pre-mod)
           compile-command)
      (set (make-local-variable 'compile-command)
           (verilog-expand-command compile-command))
      (set (make-local-variable 'verilog-compile-command-post-mod)
           compile-command))))

(when (featurep 'xemacs)
  (defvar compilation-error-regexp-systems-alist)
  (if (not (and (= emacs-major-version 21) (<= emacs-minor-version 4)))
      ;; XEmacs 21.5 and newer match GNU, see bug1700
      (defun verilog-error-regexp-add-xemacs ()
        (interactive)
        (verilog-error-regexp-add-xemacs))
    ;; XEmacs 21.4 and older
    ;; Following code only gets called from compilation-mode-hook on XEmacs to add error handling.
    (defun verilog-error-regexp-add-xemacs ()
      "Teach XEmacs about Verilog errors.
Called by `compilation-mode-hook'.  This allows \\[next-error] to
find the errors."
      (interactive)
      (if (boundp 'compilation-error-regexp-systems-alist)
	  (if (and
	       (not (equal compilation-error-regexp-systems-list 'all))
	       (not (member 'verilog compilation-error-regexp-systems-list)))
	      (push 'verilog compilation-error-regexp-systems-list)))
      (if (boundp 'compilation-error-regexp-alist-alist)
	  (if (not (assoc 'verilog compilation-error-regexp-alist-alist))
	      (setcdr compilation-error-regexp-alist-alist
		      (cons verilog-error-regexp-xemacs-alist
			    (cdr compilation-error-regexp-alist-alist)))))
      (if (boundp 'compilation-font-lock-keywords)
	  (progn
	    (set (make-local-variable 'compilation-font-lock-keywords)
		 verilog-error-font-lock-keywords)
	    (font-lock-set-defaults)))
      ;; Need to re-run compilation-error-regexp builder
      (if (fboundp 'compilation-build-compilation-error-regexp-alist)
	  (compilation-build-compilation-error-regexp-alist))
      )))

;; Following code only gets called from compilation-mode-hook on Emacs to add error handling.
(defun verilog-error-regexp-add-emacs ()
  "Tell Emacs compile that we are Verilog.
Called by `compilation-mode-hook'.  This allows \\[next-error] to
find the errors."
  (interactive)
  (when (boundp 'compilation-error-regexp-alist-alist)
    (when (not (assoc 'verilog-xl-1 compilation-error-regexp-alist-alist))
      (mapc
       (lambda (item)
         (push (car item) compilation-error-regexp-alist)
         (push item compilation-error-regexp-alist-alist))
       verilog-error-regexp-emacs-alist))))

(add-hook 'compilation-mode-hook
          (if (featurep 'xemacs)
              #'verilog-error-regexp-add-xemacs
            #'verilog-error-regexp-add-emacs))

(defconst verilog-compiler-directives
  (eval-when-compile
    '(
      ;; compiler directives, from IEEE 1800-2012 section 22.1
      "`__FILE__" "`__LINE" "`begin_keywords" "`celldefine" "`default_nettype"
      "`define" "`else" "`elsif" "`end_keywords" "`endcelldefine" "`endif"
      "`ifdef" "`ifndef" "`include" "`line" "`nounconnected_drive" "`pragma"
      "`resetall" "`timescale" "`unconnected_drive" "`undef" "`undefineall"
      ;; compiler directives not covered by IEEE 1800
      "`case" "`default" "`endfor" "`endprotect" "`endswitch" "`endwhile" "`for"
      "`format" "`if" "`let" "`protect" "`switch" "`time_scale" "`uselib"
      "`while"
      ))
  "List of Verilog compiler directives.")

(defconst verilog-directive-re
  (verilog-regexp-words verilog-compiler-directives))

(defconst verilog-directive-re-1
  (concat "[ \t]*"  verilog-directive-re))

(defconst verilog-directive-begin
  "\\<`\\(for\\|i\\(f\\|fdef\\|fndef\\)\\|switch\\|while\\)\\>")

(defconst verilog-directive-middle
  "\\<`\\(else\\|elsif\\|default\\|case\\)\\>")

(defconst verilog-directive-end
  "`\\(endfor\\|endif\\|endswitch\\|endwhile\\)\\>")

(defconst verilog-ovm-begin-re
  (eval-when-compile
    (verilog-regexp-opt
     '(
       "`ovm_component_utils_begin"
       "`ovm_component_param_utils_begin"
       "`ovm_field_utils_begin"
       "`ovm_object_utils_begin"
       "`ovm_object_param_utils_begin"
       "`ovm_sequence_utils_begin"
       "`ovm_sequencer_utils_begin"
       ) nil )))

(defconst verilog-ovm-end-re
  (eval-when-compile
    (verilog-regexp-opt
     '(
       "`ovm_component_utils_end"
       "`ovm_field_utils_end"
       "`ovm_object_utils_end"
       "`ovm_sequence_utils_end"
       "`ovm_sequencer_utils_end"
       ) nil )))

(defconst verilog-uvm-begin-re
  (eval-when-compile
    (verilog-regexp-opt
     '(
       "`uvm_component_utils_begin"
       "`uvm_component_param_utils_begin"
       "`uvm_field_utils_begin"
       "`uvm_object_utils_begin"
       "`uvm_object_param_utils_begin"
       "`uvm_sequence_utils_begin"
       "`uvm_sequencer_utils_begin"
       ) nil )))

(defconst verilog-uvm-end-re
  (eval-when-compile
    (verilog-regexp-opt
     '(
       "`uvm_component_utils_end"
       "`uvm_field_utils_end"
       "`uvm_object_utils_end"
       "`uvm_sequence_utils_end"
       "`uvm_sequencer_utils_end"
       ) nil )))

(defconst verilog-vmm-begin-re
  (eval-when-compile
    (verilog-regexp-opt
     '(
       "`vmm_data_member_begin"
       "`vmm_env_member_begin"
       "`vmm_scenario_member_begin"
       "`vmm_subenv_member_begin"
       "`vmm_xactor_member_begin"
       ) nil ) ) )

(defconst verilog-vmm-end-re
  (eval-when-compile
    (verilog-regexp-opt
     '(
       "`vmm_data_member_end"
       "`vmm_env_member_end"
       "`vmm_scenario_member_end"
       "`vmm_subenv_member_end"
       "`vmm_xactor_member_end"
       ) nil ) ) )

(defconst verilog-vmm-statement-re
  "`vmm_\\(data\\|env\\|scenario\\|subenv\\|xactor\\)_member_\\(scalar\\|string\\|enum\\|vmm_data\\|channel\\|xactor\\|subenv\\|user_defined\\)\\(_array\\)?")

(defconst verilog-ovm-statement-re
  (eval-when-compile
    (verilog-regexp-opt
     '(
       ;; Statements
       "`DUT_ERROR"
       "`MESSAGE"
       "`dut_error"
       "`message"
       "`ovm_analysis_imp_decl"
       "`ovm_blocking_get_imp_decl"
       "`ovm_blocking_get_peek_imp_decl"
       "`ovm_blocking_master_imp_decl"
       "`ovm_blocking_peek_imp_decl"
       "`ovm_blocking_put_imp_decl"
       "`ovm_blocking_slave_imp_decl"
       "`ovm_blocking_transport_imp_decl"
       "`ovm_component_registry"
       "`ovm_component_registry_param"
       "`ovm_component_utils"
       "`ovm_create"
       "`ovm_create_seq"
       "`ovm_declare_sequence_lib"
       "`ovm_do"
       "`ovm_do_seq"
       "`ovm_do_seq_with"
       "`ovm_do_with"
       "`ovm_error"
       "`ovm_fatal"
       "`ovm_field_aa_int_byte"
       "`ovm_field_aa_int_byte_unsigned"
       "`ovm_field_aa_int_int"
       "`ovm_field_aa_int_int_unsigned"
       "`ovm_field_aa_int_integer"
       "`ovm_field_aa_int_integer_unsigned"
       "`ovm_field_aa_int_key"
       "`ovm_field_aa_int_longint"
       "`ovm_field_aa_int_longint_unsigned"
       "`ovm_field_aa_int_shortint"
       "`ovm_field_aa_int_shortint_unsigned"
       "`ovm_field_aa_int_string"
       "`ovm_field_aa_object_int"
       "`ovm_field_aa_object_string"
       "`ovm_field_aa_string_int"
       "`ovm_field_aa_string_string"
       "`ovm_field_array_int"
       "`ovm_field_array_object"
       "`ovm_field_array_string"
       "`ovm_field_enum"
       "`ovm_field_event"
       "`ovm_field_int"
       "`ovm_field_object"
       "`ovm_field_queue_int"
       "`ovm_field_queue_object"
       "`ovm_field_queue_string"
       "`ovm_field_sarray_int"
       "`ovm_field_string"
       "`ovm_field_utils"
       "`ovm_file"
       "`ovm_get_imp_decl"
       "`ovm_get_peek_imp_decl"
       "`ovm_info"
       "`ovm_info1"
       "`ovm_info2"
       "`ovm_info3"
       "`ovm_info4"
       "`ovm_line"
       "`ovm_master_imp_decl"
       "`ovm_msg_detail"
       "`ovm_non_blocking_transport_imp_decl"
       "`ovm_nonblocking_get_imp_decl"
       "`ovm_nonblocking_get_peek_imp_decl"
       "`ovm_nonblocking_master_imp_decl"
       "`ovm_nonblocking_peek_imp_decl"
       "`ovm_nonblocking_put_imp_decl"
       "`ovm_nonblocking_slave_imp_decl"
       "`ovm_object_registry"
       "`ovm_object_registry_param"
       "`ovm_object_utils"
       "`ovm_peek_imp_decl"
       "`ovm_phase_func_decl"
       "`ovm_phase_task_decl"
       "`ovm_print_aa_int_object"
       "`ovm_print_aa_string_int"
       "`ovm_print_aa_string_object"
       "`ovm_print_aa_string_string"
       "`ovm_print_array_int"
       "`ovm_print_array_object"
       "`ovm_print_array_string"
       "`ovm_print_object_queue"
       "`ovm_print_queue_int"
       "`ovm_print_string_queue"
       "`ovm_put_imp_decl"
       "`ovm_rand_send"
       "`ovm_rand_send_with"
       "`ovm_send"
       "`ovm_sequence_utils"
       "`ovm_slave_imp_decl"
       "`ovm_transport_imp_decl"
       "`ovm_update_sequence_lib"
       "`ovm_update_sequence_lib_and_item"
       "`ovm_warning"
       "`static_dut_error"
       "`static_message")
     nil )))

(defconst verilog-uvm-statement-re
  (eval-when-compile
    (verilog-regexp-opt
     '(
       ;; Statements
       "`uvm_analysis_imp_decl"
       "`uvm_blocking_get_imp_decl"
       "`uvm_blocking_get_peek_imp_decl"
       "`uvm_blocking_master_imp_decl"
       "`uvm_blocking_peek_imp_decl"
       "`uvm_blocking_put_imp_decl"
       "`uvm_blocking_slave_imp_decl"
       "`uvm_blocking_transport_imp_decl"
       "`uvm_component_param_utils"
       "`uvm_component_registry"
       "`uvm_component_registry_param"
       "`uvm_component_utils"
       "`uvm_create"
       "`uvm_create_on"
       "`uvm_create_seq"                ; Undocumented in 1.1
       "`uvm_declare_p_sequencer"
       "`uvm_declare_sequence_lib"      ; Deprecated in 1.1
       "`uvm_do"
       "`uvm_do_callbacks"
       "`uvm_do_callbacks_exit_on"
       "`uvm_do_obj_callbacks"
       "`uvm_do_obj_callbacks_exit_on"
       "`uvm_do_on"
       "`uvm_do_on_pri"
       "`uvm_do_on_pri_with"
       "`uvm_do_on_with"
       "`uvm_do_pri"
       "`uvm_do_pri_with"
       "`uvm_do_seq"                    ; Undocumented in 1.1
       "`uvm_do_seq_with"               ; Undocumented in 1.1
       "`uvm_do_with"
       "`uvm_error"
       "`uvm_error_context"
       "`uvm_fatal"
       "`uvm_fatal_context"
       "`uvm_field_aa_int_byte"
       "`uvm_field_aa_int_byte_unsigned"
       "`uvm_field_aa_int_enum"
       "`uvm_field_aa_int_int"
       "`uvm_field_aa_int_int_unsigned"
       "`uvm_field_aa_int_integer"
       "`uvm_field_aa_int_integer_unsigned"
       "`uvm_field_aa_int_key"
       "`uvm_field_aa_int_longint"
       "`uvm_field_aa_int_longint_unsigned"
       "`uvm_field_aa_int_shortint"
       "`uvm_field_aa_int_shortint_unsigned"
       "`uvm_field_aa_int_string"
       "`uvm_field_aa_object_int"
       "`uvm_field_aa_object_string"
       "`uvm_field_aa_string_int"
       "`uvm_field_aa_string_string"
       "`uvm_field_array_enum"
       "`uvm_field_array_int"
       "`uvm_field_array_object"
       "`uvm_field_array_string"
       "`uvm_field_enum"
       "`uvm_field_event"
       "`uvm_field_int"
       "`uvm_field_object"
       "`uvm_field_queue_enum"
       "`uvm_field_queue_int"
       "`uvm_field_queue_object"
       "`uvm_field_queue_string"
       "`uvm_field_real"
       "`uvm_field_sarray_enum"
       "`uvm_field_sarray_int"
       "`uvm_field_sarray_object"
       "`uvm_field_sarray_string"
       "`uvm_field_string"
       "`uvm_field_utils"
       "`uvm_file"              ; Undocumented in 1.1, use `__FILE__
       "`uvm_get_imp_decl"
       "`uvm_get_peek_imp_decl"
       "`uvm_info"
       "`uvm_info_context"
       "`uvm_line"              ; Undocumented in 1.1, use `__LINE__
       "`uvm_master_imp_decl"
       "`uvm_non_blocking_transport_imp_decl"   ; Deprecated in 1.1
       "`uvm_nonblocking_get_imp_decl"
       "`uvm_nonblocking_get_peek_imp_decl"
       "`uvm_nonblocking_master_imp_decl"
       "`uvm_nonblocking_peek_imp_decl"
       "`uvm_nonblocking_put_imp_decl"
       "`uvm_nonblocking_slave_imp_decl"
       "`uvm_nonblocking_transport_imp_decl"
       "`uvm_object_param_utils"
       "`uvm_object_registry"
       "`uvm_object_registry_param"     ; Undocumented in 1.1
       "`uvm_object_utils"
       "`uvm_pack_array"
       "`uvm_pack_arrayN"
       "`uvm_pack_enum"
       "`uvm_pack_enumN"
       "`uvm_pack_int"
       "`uvm_pack_intN"
       "`uvm_pack_queue"
       "`uvm_pack_queueN"
       "`uvm_pack_real"
       "`uvm_pack_sarray"
       "`uvm_pack_sarrayN"
       "`uvm_pack_string"
       "`uvm_peek_imp_decl"
       "`uvm_put_imp_decl"
       "`uvm_rand_send"
       "`uvm_rand_send_pri"
       "`uvm_rand_send_pri_with"
       "`uvm_rand_send_with"
       "`uvm_record_attribute"
       "`uvm_record_field"
       "`uvm_register_cb"
       "`uvm_send"
       "`uvm_send_pri"
       "`uvm_sequence_utils"            ; Deprecated in 1.1
       "`uvm_set_super_type"
       "`uvm_slave_imp_decl"
       "`uvm_transport_imp_decl"
       "`uvm_unpack_array"
       "`uvm_unpack_arrayN"
       "`uvm_unpack_enum"
       "`uvm_unpack_enumN"
       "`uvm_unpack_int"
       "`uvm_unpack_intN"
       "`uvm_unpack_queue"
       "`uvm_unpack_queueN"
       "`uvm_unpack_real"
       "`uvm_unpack_sarray"
       "`uvm_unpack_sarrayN"
       "`uvm_unpack_string"
       "`uvm_update_sequence_lib"               ; Deprecated in 1.1
       "`uvm_update_sequence_lib_and_item"      ; Deprecated in 1.1
       "`uvm_warning"
       "`uvm_warning_context")
     nil )))


;;
;; Regular expressions used to calculate indent, etc.
;;
(defconst verilog-identifier-re "[a-zA-Z_][a-zA-Z_0-9]*")
(defconst verilog-identifier-sym-re (concat "\\<" verilog-identifier-re "\\>"))
(defconst verilog-assignment-operator-re
  (eval-when-compile
    (verilog-regexp-opt
     '(
       ;; blocking assignment_operator
       "=" "+=" "-=" "*=" "/=" "%=" "&=" "|=" "^=" "<<=" ">>=" "<<<=" ">>>="
       ;; comparison (also nonblocking assignment "<=")
       "==" "!=" "===" "!==" "<=" ">=" "==?" "!=?" "<->"
       ;; event_trigger
       "->" "->>"
       ;; property_expr
       "|->" "|=>" "#-#" "#=#"
       ;; distribution weighting
       ":=" ":/"
       ) 't
         )))
(defconst verilog-assignment-operation-re
  (concat "\\(^.*?\\)" verilog-assignment-operator-re))
(defconst verilog-assignment-operation-re-2
  (concat "\\(.*?\\)" verilog-assignment-operator-re))

;; Loosely related to IEEE 1800's concurrent_assertion_statement
(defconst verilog-concurrent-assertion-statement-re
  "\\(\\<\\(assert\\|assume\\|cover\\|restrict\\)\\>\\s-+\\<\\(property\\|sequence\\)\\>\\)\\|\\(\\<assert\\>\\)")

(defconst verilog-label-re (concat verilog-identifier-sym-re "\\s-*:\\s-*"))
(defconst verilog-property-re
  (concat "\\(" verilog-label-re "\\)?" verilog-concurrent-assertion-statement-re))

(defconst verilog-no-indent-begin-re
  (eval-when-compile
    (verilog-regexp-words
     '("always" "always_comb" "always_ff" "always_latch" "analog" "initial" "final"  ; procedural blocks
       "if" "else"                                                          ; conditional statements
       "while" "for" "foreach" "repeat" "do" "forever" ))))                 ; loop statements

(defconst verilog-ends-re
  ;; Parenthesis indicate type of keyword found
  (concat
   "\\(\\<else\\>\\)\\|"		; 1
   "\\(\\<if\\>\\)\\|"			; 2
   "\\(\\<assert\\>\\)\\|"              ; 3
   "\\(\\<end\\>\\)\\|"			; 3.1
   "\\(\\<endcase\\>\\)\\|"		; 4
   "\\(\\<endfunction\\>\\)\\|"		; 5
   "\\(\\<endtask\\>\\)\\|"		; 6
   "\\(\\<endspecify\\>\\)\\|"		; 7
   "\\(\\<endtable\\>\\)\\|"		; 8
   "\\(\\<endgenerate\\>\\)\\|"         ; 9
   "\\(\\<join\\(_any\\|_none\\)?\\>\\)\\|" ; 10
   "\\(\\<endclass\\>\\)\\|"            ; 11
   "\\(\\<endgroup\\>\\)\\|"            ; 12
   ;; VMM
   "\\(\\<`vmm_data_member_end\\>\\)\\|"
   "\\(\\<`vmm_env_member_end\\>\\)\\|"
   "\\(\\<`vmm_scenario_member_end\\>\\)\\|"
   "\\(\\<`vmm_subenv_member_end\\>\\)\\|"
   "\\(\\<`vmm_xactor_member_end\\>\\)\\|"
   ;; OVM
   "\\(\\<`ovm_component_utils_end\\>\\)\\|"
   "\\(\\<`ovm_field_utils_end\\>\\)\\|"
   "\\(\\<`ovm_object_utils_end\\>\\)\\|"
   "\\(\\<`ovm_sequence_utils_end\\>\\)\\|"
   "\\(\\<`ovm_sequencer_utils_end\\>\\)"
   ;; UVM
   "\\(\\<`uvm_component_utils_end\\>\\)\\|"
   "\\(\\<`uvm_field_utils_end\\>\\)\\|"
   "\\(\\<`uvm_object_utils_end\\>\\)\\|"
   "\\(\\<`uvm_sequence_utils_end\\>\\)\\|"
   "\\(\\<`uvm_sequencer_utils_end\\>\\)"
   ))

(defconst verilog-auto-end-comment-lines-re
  ;; Matches to names in this list cause auto-end-commenting
  (concat "\\("
	  verilog-directive-re "\\)\\|\\("
	  (eval-when-compile
	    (verilog-regexp-words
	     '( "begin"
               "connectmodule"
		"else"
		"end"
		"endcase"
		"endclass"
		"endclocking"
               "endconnectmodule"
		"endgroup"
		"endfunction"
		"endmodule"
		"endprogram"
		"endprimitive"
		"endinterface"
		"endpackage"
		"endsequence"
		"endproperty"
		"endspecify"
		"endtable"
		"endtask"
		"join"
		"join_any"
		"join_none"
		"module"
		"macromodule"
		"primitive"
		"interface"
		"package")))
	  "\\)"))

;; NOTE: verilog-leap-to-head expects that verilog-end-block-re and
;; verilog-end-block-ordered-re matches exactly the same strings.
(defconst verilog-end-block-ordered-re
  ;; Parenthesis indicate type of keyword found
  (concat "\\(\\<endcase\\>\\)\\|" ; 1
	  "\\(\\<end\\>\\)\\|"     ; 2
	  "\\(\\<end"              ; 3, but not used
	  "\\("                    ; 4, but not used
	  "\\(function\\)\\|"      ; 5
	  "\\(task\\)\\|"          ; 6
	  "\\(module\\)\\|"        ; 7
	  "\\(primitive\\)\\|"     ; 8
	  "\\(interface\\)\\|"     ; 9
	  "\\(package\\)\\|"       ; 10
	  "\\(class\\)\\|"         ; 11
          "\\(group\\)\\|"         ; 12
          "\\(program\\)\\|"	   ; 13
          "\\(sequence\\)\\|"	   ; 14
	  "\\(clocking\\)\\|"      ; 15
	  "\\(property\\)\\|"      ; 16
         "\\(connectmodule\\)\\|" ; 17
	  "\\)\\>\\)"))

(defconst verilog-end-block-re
  (eval-when-compile
    (verilog-regexp-words
     '("end"      ; closes begin
       "endcase"  ; closes any of case, casex casez or randcase
       "join" "join_any" "join_none"  ; closes fork
       "endclass"
       "endtable"
       "endspecify"
       "endfunction"
       "endgenerate"
       "endtask"
       "endgroup"
       "endproperty"
       "endinterface"
       "endpackage"
       "endprogram"
       "endsequence"
       "endclocking"
       ;; OVM
       "`ovm_component_utils_end"
       "`ovm_field_utils_end"
       "`ovm_object_utils_end"
       "`ovm_sequence_utils_end"
       "`ovm_sequencer_utils_end"
       ;; UVM
       "`uvm_component_utils_end"
       "`uvm_field_utils_end"
       "`uvm_object_utils_end"
       "`uvm_sequence_utils_end"
       "`uvm_sequencer_utils_end"
       ;; VMM
       "`vmm_data_member_end"
       "`vmm_env_member_end"
       "`vmm_scenario_member_end"
       "`vmm_subenv_member_end"
       "`vmm_xactor_member_end"
       ))))

(defconst verilog-endcomment-reason-re
  ;; Parenthesis indicate type of keyword found
  (concat
   "\\(\\<begin\\>\\)\\|"		         ; 1
   "\\(\\<else\\>\\)\\|"		         ; 2
   "\\(\\<end\\>\\s-+\\<else\\>\\)\\|"	         ; 3
   "\\(\\<always\\(?:_ff\\)?\\>\\(?:[ \t]*@\\)\\)\\|"    ; 4 (matches always or always_ff w/ @...)
   "\\(\\<always\\(?:_comb\\|_latch\\)?\\>\\)\\|"  ; 5 (matches always, always_comb, always_latch w/o @...)
   "\\(\\<analog\\>\\)\\|"		         ; 6
   "\\(\\<fork\\>\\)\\|"			 ; 7
   "\\(\\<if\\>\\)\\|"
   verilog-property-re "\\|"
   "\\(\\<clocking\\>\\)\\|"
   "\\(\\<task\\>\\)\\|"
   "\\(\\<function\\>\\)\\|"
   "\\(\\<initial\\>\\)\\|"
   "\\(\\<interface\\>\\)\\|"
   "\\(\\<package\\>\\)\\|"
   "\\(\\<final\\>\\)\\|"
   "\\(@\\)\\|"
   "\\(\\<while\\>\\)\\|\\(\\<do\\>\\)\\|"
   "\\(\\<for\\(ever\\|each\\)?\\>\\)\\|"
   "\\(\\<repeat\\>\\)\\|\\(\\<wait\\>\\)\\|"
   "#"))

(defconst verilog-named-block-re  "begin[ \t]*:")

;; These words begin a block which can occur inside a module which should be indented,
;; and closed with the respective word from the end-block list

(defconst verilog-beg-block-re
  (eval-when-compile
    (verilog-regexp-words
     '("begin"
       "case" "casex" "casez" "randcase"
       "clocking"
       "generate"
       "fork"
       "function"
       "property"
       "specify"
       "table"
       "task"
       ;; OVM
       "`ovm_component_utils_begin"
       "`ovm_component_param_utils_begin"
       "`ovm_field_utils_begin"
       "`ovm_object_utils_begin"
       "`ovm_object_param_utils_begin"
       "`ovm_sequence_utils_begin"
       "`ovm_sequencer_utils_begin"
       ;; UVM
       "`uvm_component_utils_begin"
       "`uvm_component_param_utils_begin"
       "`uvm_field_utils_begin"
       "`uvm_object_utils_begin"
       "`uvm_object_param_utils_begin"
       "`uvm_sequence_utils_begin"
       "`uvm_sequencer_utils_begin"
       ;; VMM
       "`vmm_data_member_begin"
       "`vmm_env_member_begin"
       "`vmm_scenario_member_begin"
       "`vmm_subenv_member_begin"
       "`vmm_xactor_member_begin"
       ))))
;; These are the same words, in a specific order in the regular
;; expression so that matching will work nicely for
;; verilog-forward-sexp and verilog-calc-indent
(defconst verilog-beg-block-re-ordered
  ( concat "\\(\\<begin\\>\\)"		;1
	   "\\|\\(\\<randcase\\>\\|\\(\\<unique0?\\s-+\\|priority\\s-+\\)?case[xz]?\\>\\)" ; 2,3
	   "\\|\\(\\(\\<disable\\>\\s-+\\|\\<wait\\>\\s-+\\)?fork\\>\\)" ;4,5
	   "\\|\\(\\<class\\>\\)"		;6
	   "\\|\\(\\<table\\>\\)"		;7
	   "\\|\\(\\<specify\\>\\)"		;8
	   "\\|\\(\\<function\\>\\)"		;9
           "\\|\\(\\(?:\\<\\(?:virtual\\|protected\\|static\\)\\>\\s-+\\)*\\<function\\>\\)"  ;10
           "\\|\\(\\<task\\>\\)"                ;11
           "\\|\\(\\(?:\\<\\(?:virtual\\|protected\\|static\\)\\>\\s-+\\)*\\<task\\>\\)"      ;12
           "\\|\\(\\<generate\\>\\)"            ;13
           "\\|\\(\\<covergroup\\>\\)"          ;14
           "\\|\\(\\(?:\\(?:\\<cover\\>\\s-+\\)\\|\\(?:\\<assert\\>\\s-+\\)\\)*\\<property\\>\\)" ;15
           "\\|\\(\\<\\(?:rand\\)?sequence\\>\\)" ;16
           "\\|\\(\\<clocking\\>\\)"              ;17
           "\\|\\(\\<`[ou]vm_[a-z_]+_begin\\>\\)" ;18
           "\\|\\(\\<`vmm_[a-z_]+_member_begin\\>\\)"
           "\\|\\(\\<`ifn?def\\>\\)"              ;20, matched end can be: `else `elsif `endif
           "\\|\\(\\<`else\\>\\)"                 ;21, matched end can be: `endif
           "\\|\\(\\<`elsif\\>\\)"                ;22, matched end can be: `else `endif
	   ;;
	   ))

(defconst verilog-end-block-ordered-rry
  [ "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<endcase\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)"
    "\\(\\<randcase\\>\\|\\<case[xz]?\\>\\)\\|\\(\\<endcase\\>\\)"
    "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)"
    "\\(\\<class\\>\\)\\|\\(\\<endclass\\>\\)"
    "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)"
    "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)"
    "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)"
    "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)"
    "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)"
    "\\(\\<covergroup\\>\\)\\|\\(\\<endgroup\\>\\)"
    "\\(\\<property\\>\\)\\|\\(\\<endproperty\\>\\)"
    "\\(\\<\\(rand\\)?sequence\\>\\)\\|\\(\\<endsequence\\>\\)"
    "\\(\\<clocking\\>\\)\\|\\(\\<endclocking\\>\\)"
    ] )

(defconst verilog-nameable-item-re
  (eval-when-compile
    (verilog-regexp-words
     '("begin"
       "fork"
       "join" "join_any" "join_none"
       "end"
       "endcase"
       "endchecker"
       "endclass"
       "endclocking"
       "endconfig"
       "endconnectmodule"
       "endfunction"
       "endgenerate"
       "endgroup"
       "endmodule"
       "endprimitive"
       "endinterface"
       "endpackage"
       "endprogram"
       "endproperty"
       "endsequence"
       "endspecify"
       "endtable"
       "endtask" )
     )))

(defconst verilog-declaration-opener
  (eval-when-compile
    (verilog-regexp-words
     '("connectmodule" "module" "begin" "task" "function"))))

(defconst verilog-declaration-prefix-re
  (eval-when-compile
    (verilog-regexp-words
     '(
       ;; port direction
       "inout" "input" "output" "ref"
       ;; changeableness
       "const" "static" "protected" "local"
       ;; parameters
       "localparam" "parameter" "var"
       ;; type creation
       "typedef"
       ;; randomness
       "rand"
       ))))
(defconst verilog-declaration-core-re
  (eval-when-compile
    (verilog-regexp-words
     '(
       ;; port direction (by themselves)
       "inout" "input" "output"
       ;; integer_atom_type
       "byte" "shortint" "int" "longint" "integer" "time"
       ;; integer_vector_type
       "bit" "logic" "reg"
       ;; non_integer_type
       "shortreal" "real" "realtime"
       ;; net_type
       "supply0" "supply1" "tri" "triand" "trior" "trireg" "tri0" "tri1" "uwire" "wire" "wand" "wor"
       ;; parameters
       "localparam" "parameter" "var"
       ;; misc
       "string" "event" "chandle" "virtual" "enum" "genvar"
       "struct" "union" "type"
       ;; builtin classes
       "mailbox" "semaphore"
       ))))
(defconst verilog-range-re "\\(\\[[^]]*\\]\\s-*\\)+")
(defconst verilog-optional-signed-re "\\s-*\\(\\(un\\)?signed\\)?")
(defconst verilog-optional-signed-range-re
  (concat "\\s-*\\(\\<\\(reg\\|wire\\)\\>\\s-*\\)?\\(\\<\\(un\\)?signed\\>\\s-*\\)?\\(" verilog-range-re "\\)?"))
(defconst verilog-macroexp-re "`\\sw+")
(defconst verilog-delay-re "#\\s-*\\(\\([0-9_]+\\('s?[hdxbo][0-9a-fA-F_xz]+\\)?\\)\\|\\(([^()]*)\\)\\|\\(\\sw+\\)\\)")
(defconst verilog-interface-modport-re "\\(\\s-*\\([a-zA-Z0-9`_$]+\\.[a-zA-Z0-9`_$]+\\)[ \t\f]+\\)")
(defconst verilog-comment-start-regexp "//\\|/\\*" "Dual comment value for `comment-start-regexp'.")
(defconst verilog-typedef-enum-re
  (concat "^\\s-*\\(typedef\\s-+\\)?enum\\(\\s-+" verilog-declaration-core-re verilog-optional-signed-range-re "\\)?"))

(defconst verilog-declaration-simple-re
  (concat "\\(" verilog-declaration-prefix-re "\\s-*\\)?" verilog-declaration-core-re))
(defconst verilog-declaration-re
  (concat "\\s-*" verilog-declaration-simple-re
          "\\s-*\\(\\(" verilog-optional-signed-range-re "\\)\\|\\(" verilog-delay-re "\\)\\)"))
(defconst verilog-declaration-re-macro
  (concat "\\s-*" verilog-declaration-simple-re
          "\\s-*\\(\\(" verilog-optional-signed-range-re "\\)\\|\\(" verilog-delay-re "\\)\\|\\(" verilog-macroexp-re "\\)\\)"))
(defconst verilog-declaration-or-iface-mp-re
  (concat "\\(" verilog-declaration-re "\\)\\|\\(" verilog-interface-modport-re "\\)"))
(defconst verilog-declaration-embedded-comments-re
  (concat "\\( " verilog-declaration-re "\\) ""\\s-*" "\\(" verilog-comment-start-regexp "\\)")
  "Match expressions such as: input logic [7:0] /* auto enum sm_psm */ sm_psm;.")

(defconst verilog-defun-re
  (eval-when-compile (verilog-regexp-words '("macromodule" "connectmodule" "module" "class" "program" "interface" "package" "primitive" "config"))))
(defconst verilog-end-defun-re
  (eval-when-compile (verilog-regexp-words '("endconnectmodule" "endmodule" "endclass" "endprogram" "endinterface" "endpackage" "endprimitive" "endconfig"))))
(defconst verilog-defun-tf-re-beg
  (eval-when-compile (verilog-regexp-words '("macromodule" "connectmodule" "module" "class" "program" "interface" "package" "primitive" "config" "function" "task"))))
(defconst verilog-defun-tf-re-end
  (eval-when-compile (verilog-regexp-words '("endconnectmodule" "endmodule" "endclass" "endprogram" "endinterface" "endpackage" "endprimitive" "endconfig" "endfunction" "endtask"))))
(defconst verilog-defun-tf-re-all
  (eval-when-compile (verilog-regexp-words '("macromodule" "connectmodule" "module" "class" "program" "interface" "package" "primitive" "config" "function" "task"
                                             "endconnectmodule" "endmodule" "endclass" "endprogram" "endinterface" "endpackage" "endprimitive" "endconfig" "endfunction" "endtask"))))
(defconst verilog-defun-no-class-re
  (eval-when-compile (verilog-regexp-words '("macromodule" "connectmodule" "module" "program" "interface" "package" "primitive" "config"))))
(defconst verilog-end-defun-no-class-re
  (eval-when-compile (verilog-regexp-words '("endconnectmodule" "endmodule" "endprogram" "endinterface" "endpackage" "endprimitive" "endconfig"))))
(defconst verilog-zero-indent-re
  (concat verilog-defun-re "\\|" verilog-end-defun-re))
(defconst verilog-zero-indent-no-class-re
  (concat verilog-defun-no-class-re "\\|" verilog-end-defun-no-class-re))
(defconst verilog-inst-comment-re
  (eval-when-compile (verilog-regexp-words '("Outputs" "Inouts" "Inputs" "Interfaces" "Interfaced"))))

(defconst verilog-behavioral-block-beg-re
  (eval-when-compile (verilog-regexp-words '("initial" "final" "always" "always_comb" "always_latch" "always_ff" "analog"
                                             "function" "task"))))
(defconst verilog-coverpoint-re "\\w+\\s-*:\\s-*\\(coverpoint\\|cross\\|constraint\\)")
(defconst verilog-in-constraint-re  ; keywords legal in constraint blocks starting a statement/block
  (eval-when-compile (verilog-regexp-words '("if" "else" "solve" "foreach"))))

(defconst verilog-indent-re
  (eval-when-compile
    (verilog-regexp-words
     '(
       "{"
       "always" "always_latch" "always_ff" "always_comb" "analog"
       "begin" "end"
       ;; "unique" "priority"
       "case" "casex" "casez" "randcase" "endcase"
       "class" "endclass"
       "clocking" "endclocking"
       "config" "endconfig"
       "covergroup" "endgroup"
       "fork" "join" "join_any" "join_none"
       "function" "endfunction"
       "final"
       "generate" "endgenerate"
       "initial"
       "interface" "endinterface"
       "connectmodule" "module" "macromodule" "endconnectmodule" "endmodule"
       "package" "endpackage"
       "primitive" "endprimitive"
       "program" "endprogram"
       "property" "endproperty"
       "sequence" "randsequence" "endsequence"
       "specify" "endspecify"
       "table" "endtable"
       "task" "endtask"
       "virtual"
       "`case"
       "`default"
       "`define" "`undef"
       "`if" "`ifdef" "`ifndef" "`else" "`elsif" "`endif"
       "`while" "`endwhile"
       "`for" "`endfor"
       "`format"
       "`include"
       "`let"
       "`protect" "`endprotect"
       "`switch" "`endswitch"
       "`timescale"
       "`time_scale"
       ;; OVM Begin tokens
       "`ovm_component_utils_begin"
       "`ovm_component_param_utils_begin"
       "`ovm_field_utils_begin"
       "`ovm_object_utils_begin"
       "`ovm_object_param_utils_begin"
       "`ovm_sequence_utils_begin"
       "`ovm_sequencer_utils_begin"
       ;; OVM End tokens
       "`ovm_component_utils_end"
       "`ovm_field_utils_end"
       "`ovm_object_utils_end"
       "`ovm_sequence_utils_end"
       "`ovm_sequencer_utils_end"
       ;; UVM Begin tokens
       "`uvm_component_utils_begin"
       "`uvm_component_param_utils_begin"
       "`uvm_field_utils_begin"
       "`uvm_object_utils_begin"
       "`uvm_object_param_utils_begin"
       "`uvm_sequence_utils_begin"
       "`uvm_sequencer_utils_begin"
       ;; UVM End tokens
       "`uvm_component_utils_end"       ; Typo in spec, it's not uvm_component_end
       "`uvm_field_utils_end"
       "`uvm_object_utils_end"
       "`uvm_sequence_utils_end"
       "`uvm_sequencer_utils_end"
       ;; VMM Begin tokens
       "`vmm_data_member_begin"
       "`vmm_env_member_begin"
       "`vmm_scenario_member_begin"
       "`vmm_subenv_member_begin"
       "`vmm_xactor_member_begin"
       ;; VMM End tokens
       "`vmm_data_member_end"
       "`vmm_env_member_end"
       "`vmm_scenario_member_end"
       "`vmm_subenv_member_end"
       "`vmm_xactor_member_end"
       ))))

(defconst verilog-defun-level-not-generate-re
  (eval-when-compile
    (verilog-regexp-words
     '( "connectmodule" "module" "macromodule" "primitive" "class" "program"
        "interface" "package" "config"))))

(defconst verilog-defun-level-re
  (eval-when-compile
    (verilog-regexp-words
     (append
      '( "connectmodule" "module" "macromodule" "primitive" "class" "program"
         "interface" "package" "config")
      '( "initial" "final" "always" "always_comb" "always_ff"
         "always_latch" "analog" "endtask" "endfunction" )))))

(defconst verilog-defun-level-generate-only-re
  (eval-when-compile
    (verilog-regexp-words
     '( "initial" "final" "always" "always_comb" "always_ff"
        "always_latch" "analog" "endtask" "endfunction" ))))

(defconst verilog-cpp-level-re
  (eval-when-compile
    (verilog-regexp-words
     '(
       "endconnectmodule" "endmodule" "endprimitive" "endinterface" "endpackage" "endprogram" "endclass"
       ))))

(defconst verilog-dpi-import-export-re
  (eval-when-compile
    "\\(\\<\\(import\\|export\\)\\>\\s-+\"DPI\\(-C\\)?\"\\s-+\\(\\<\\(context\\|pure\\)\\>\\s-+\\)?\\([A-Za-z_][A-Za-z0-9_]*\\s-*=\\s-*\\)?\\<\\(function\\|task\\)\\>\\)"
    ))

(defconst verilog-default-clocking-re "\\<default\\s-+clocking\\s-+[A-Za-z_][A-Za-z0-9_]*\\s-*;")
(defconst verilog-disable-fork-re "\\(disable\\|wait\\)\\s-+fork\\>")
(defconst verilog-extended-case-re "\\(\\(unique0?\\s-+\\|priority\\s-+\\)?case[xz]?\\|randcase\\)")
(defconst verilog-extended-complete-re
  ;; verilog-beg-of-statement also looks backward one token to extend this match
  (concat "\\(\\(\\<extern\\s-+\\|\\<\\(\\<\\(pure\\|context\\)\\>\\s-+\\)?virtual\\s-+\\|\\<local\\s-+\\|\\<protected\\s-+\\|\\<static\\s-+\\)*\\(\\<function\\>\\|\\<task\\>\\)\\)"
	  "\\|\\(\\(\\<typedef\\>\\s-+\\)*\\(\\<struct\\>\\|\\<union\\>\\|\\<class\\>\\)\\)"
	  "\\|\\(\\(\\<\\(import\\|export\\)\\>\\s-+\\)?\\(\"DPI\\(-C\\)?\"\\s-+\\)?\\(\\<\\(pure\\|context\\)\\>\\s-+\\)?\\([A-Za-z_][A-Za-z0-9_]*\\s-*=\\s-*\\)?\\(function\\>\\|task\\>\\)\\)"
	  "\\|" verilog-extended-case-re ))

(eval-and-compile
  (defconst verilog-basic-complete-words
    '("always" "assign" "always_latch" "always_ff" "always_comb" "analog" "connectmodule" "constraint"
      "import" "initial" "final" "module" "macromodule" "repeat" "randcase" "while"
      "if" "for" "forever" "foreach" "else" "parameter" "do" "localparam" "assert" "default" "generate"))
  (defconst verilog-basic-complete-words-expr
    (let ((words verilog-basic-complete-words))
      (dolist (word '("default" "parameter" "localparam"))
        (setq words (remove word words)))
      words))
  (defconst verilog-basic-complete-words-expr-no-assign
    (remove "assign" verilog-basic-complete-words-expr)))

(defconst verilog-basic-complete-re
  (eval-when-compile
    (verilog-regexp-words verilog-basic-complete-words)))

(defconst verilog-basic-complete-expr-re
  (eval-when-compile
    (verilog-regexp-words verilog-basic-complete-words-expr)))

(defconst verilog-basic-complete-expr-no-assign-re
  (eval-when-compile
    (verilog-regexp-words verilog-basic-complete-words-expr-no-assign)))


(defconst verilog-complete-re
  (concat
   verilog-extended-complete-re "\\|\\(" verilog-basic-complete-re "\\)"))

(defconst verilog-end-statement-re
  (concat "\\(" verilog-beg-block-re "\\)\\|\\("
	  verilog-end-block-re "\\)"))

(defconst verilog-endcase-re
  (concat verilog-extended-case-re "\\|"
	  "\\(endcase\\)\\|"
	  verilog-defun-re
	  ))

(defconst verilog-exclude-str-start "/* -----\\/----- EXCLUDED -----\\/-----"
  "String used to mark beginning of excluded text.")
(defconst verilog-exclude-str-end " -----/\\----- EXCLUDED -----/\\----- */"
  "String used to mark end of excluded text.")
(defconst verilog-preprocessor-re
  (eval-when-compile
    (concat
     ;; single words
     "\\(?:"
     (verilog-regexp-words
      '("`__FILE__"
	"`__LINE__"
	"`celldefine"
	"`else"
	"`end_keywords"
	"`endcelldefine"
	"`endif"
	"`nounconnected_drive"
	"`resetall"
	"`unconnected_drive"
	"`undefineall"))
     "\\)\\|\\(?:"
     ;; two words: i.e. `ifdef DEFINE
     "\\<\\(`elsif\\|`ifn?def\\|`undef\\|`default_nettype\\|`begin_keywords\\)\\>\\s-"
     "\\)\\|\\(?:"
     ;; `line number "filename" level
     "\\<\\(`line\\)\\>\\s-+[0-9]+\\s-+\"[^\"]+\"\\s-+[012]"
     "\\)\\|\\(?:"
     ;;`include "file" or `include <file>
     "\\<\\(`include\\)\\>\\s-+\\(?:\"[^\"]+\"\\|<[^>]+>\\)"
     "\\)\\|\\(?:"
     ;; `pragma <stuff> (no mention in IEEE 1800-2012 that pragma can span multiple lines
     "\\<\\(`pragma\\)\\>\\s-+.+$"
     "\\)\\|\\(?:"
     ;; `timescale time_unit / time_precision
     "\\<\\(`timescale\\)\\>\\s-+10\\{0,2\\}\\s-*[munpf]?s\\s-*/\\s-*10\\{0,2\\}\\s-*[munpf]?s"
     "\\)\\|\\(?:"
     ;; `define and `if can span multiple lines if line ends in '\'.
     ;; NOTE: `if is not IEEE 1800-2012.
     ;; from https://www.emacswiki.org/emacs/MultilineRegexp
     (concat "\\<\\(`define\\|`if\\)\\>"  ; directive
             "\\s-+"  ; separator
             "\\(?:.*?\\(?:\n.*\\)*?\\)"  ; definition: to end of line, then maybe more lines (excludes any trailing \n)
             "\\(?:\n\\s-*\n\\|\\'\\)")  ; blank line or EOF
     "\\)\\|\\(?:"
     ;; `<macro>() : i.e. `uvm_info(a,b,c) or any other pre-defined macro
     ;; Since parameters inside the macro can have parentheses, and
     ;; the macro can span multiple lines, just look for the opening
     ;; parentheses and then continue to the end of the first
     ;; non-escaped EOL
     (concat "\\<`\\w+\\>\\s-*("
             "\\(?:.*?\\(?:\n.*\\)*?\\)"  ; definition: to end of line, then maybe more lines (excludes any trailing \n)
             "\\(?:\n\\s-*\n\\|\\'\\)")   ; blank line or EOF
     "\\)"
     )))

(defconst verilog-keywords
  (append verilog-compiler-directives
          '(
            "after" "alias" "always" "always_comb" "always_ff" "always_latch" "analog" "and"
            "assert" "assign" "assume" "automatic" "before" "begin" "bind"
            "bins" "binsof" "bit" "break" "buf" "bufif0" "bufif1" "byte"
            "case" "casex" "casez" "cell" "chandle" "class" "clocking" "cmos"
            "config" "const" "constraint" "context" "continue" "cover"
            "covergroup" "coverpoint" "cross" "deassign" "default" "defparam"
            "design" "disable" "dist" "do" "edge" "else" "end" "endcase"
            "endclass" "endclocking" "endconfig" "endfunction" "endgenerate"
            "endgroup" "endinterface" "endmodule" "endpackage" "endprimitive"
            "endprogram" "endproperty" "endspecify" "endsequence" "endtable"
            "endtask" "enum" "event" "expect" "export" "extends" "extern"
            "final" "first_match" "for" "force" "foreach" "forever" "fork"
            "forkjoin" "function" "generate" "genvar" "highz0" "highz1" "if"
            "iff" "ifnone" "ignore_bins" "illegal_bins" "import" "incdir"
            "include" "initial" "inout" "input" "inside" "instance" "int"
            "integer" "interface" "intersect" "join" "join_any" "join_none"
            "large" "liblist" "library" "local" "localparam" "logic"
            "longint" "macromodule" "mailbox" "matches" "medium" "modport" "module"
            "nand" "negedge" "new" "nmos" "nor" "noshowcancelled" "not"
            "notif0" "notif1" "null" "or" "output" "package" "packed"
            "parameter" "pmos" "posedge" "primitive" "priority" "program"
            "property" "protected" "pull0" "pull1" "pulldown" "pullup"
            "pulsestyle_onevent" "pulsestyle_ondetect" "pure" "rand" "randc"
            "randcase" "randsequence" "rcmos" "real" "realtime" "ref" "reg"
            "release" "repeat" "return" "rnmos" "rpmos" "rtran" "rtranif0"
            "rtranif1" "scalared" "semaphore" "sequence" "shortint" "shortreal"
            "showcancelled" "signed" "small" "solve" "specify" "specparam"
            "static" "string" "strong0" "strong1" "struct" "super" "supply0"
            "supply1" "table" "tagged" "task" "this" "throughout" "time"
            "timeprecision" "timeunit" "tran" "tranif0" "tranif1" "tri"
            "tri0" "tri1" "triand" "trior" "trireg" "type" "typedef" "union"
            "unique" "unsigned" "use" "uwire" "var" "vectored" "virtual" "void"
            "wait" "wait_order" "wand" "weak0" "weak1" "while" "wildcard"
            "wire" "with" "within" "wor" "xnor" "xor"
            ;; 1800-2009
            "accept_on" "checker" "endchecker" "eventually" "global" "implies"
            "let" "nexttime" "reject_on" "restrict" "s_always" "s_eventually"
            "s_nexttime" "s_until" "s_until_with" "strong" "sync_accept_on"
            "sync_reject_on" "unique0" "until" "until_with" "untyped" "weak"
            ;; 1800-2012
            "implements" "interconnect" "nettype" "soft"
            ;; AMS
            "connectmodule" "endconnectmodule"
            ))
  "List of Verilog keywords.")

(defvar verilog-mode-syntax-table
  (let ((table (make-syntax-table)))
    ;; Populate the syntax TABLE.
    (modify-syntax-entry ?\\ "\\" table)
    (modify-syntax-entry ?+ "." table)
    (modify-syntax-entry ?- "." table)
    (modify-syntax-entry ?= "." table)
    (modify-syntax-entry ?% "." table)
    (modify-syntax-entry ?< "." table)
    (modify-syntax-entry ?> "." table)
    (modify-syntax-entry ?& "." table)
    (modify-syntax-entry ?| "." table)
    (modify-syntax-entry ?` "w" table)  ; ` is part of definition symbols in Verilog
    (modify-syntax-entry ?_ "w" table)
    (modify-syntax-entry ?\' "." table)

    ;; Set up TABLE to handle block and line style comments.
    (if (featurep 'xemacs)
	(progn
	  ;; XEmacs (formerly Lucid) has the best implementation
	  (modify-syntax-entry ?/  ". 1456" table)
	  (modify-syntax-entry ?*  ". 23"   table)
	  (modify-syntax-entry ?\n "> b"    table))
      ;; Emacs does things differently, but we can work with it
      (modify-syntax-entry ?/  ". 124b" table)
      (modify-syntax-entry ?*  ". 23"   table)
      (modify-syntax-entry ?\n "> b"    table))
    table)
  "Syntax table used in Verilog mode buffers.")

(defvar verilog-font-lock-keywords nil
  "Default highlighting for Verilog mode.")

(defvar verilog-font-lock-keywords-1 nil
  "Subdued level highlighting for Verilog mode.")

(defvar verilog-font-lock-keywords-2 nil
  "Medium level highlighting for Verilog mode.
See also `verilog-font-lock-extra-types'.")

(defvar verilog-font-lock-keywords-3 nil
  "Gaudy level highlighting for Verilog mode.
See also `verilog-font-lock-extra-types'.")

(defvar verilog-font-lock-translate-off-face
  'verilog-font-lock-translate-off-face
  "Font to use for translated off regions.")
(defface verilog-font-lock-translate-off-face
  '((((class color)
      (background light))
     (:background "gray90" :slant italic ))
    (((class color)
      (background dark))
     (:background "gray10" :slant italic ))
    (((class grayscale) (background light))
     (:foreground "DimGray" :slant italic))
    (((class grayscale) (background dark))
     (:foreground "LightGray" :slant italic))
    (t (:slant italic)))
  "Font lock mode face used to background highlight translate-off regions."
  :group 'font-lock-highlighting-faces)

(defvar verilog-font-lock-p1800-face
  'verilog-font-lock-p1800-face
  "Obsolete font to use for p1800 keywords.")
(defface verilog-font-lock-p1800-face
  '((((class color)
      (background light))
     (:foreground "DarkOrange3" :weight bold ))
    (((class color)
      (background dark))
     (:foreground "orange1" :weight bold ))
    (t (:slant italic)))
  "Font lock mode face used to highlight P1800 keywords."
  :group 'font-lock-highlighting-faces)
(make-obsolete-variable 'verilog-font-lock-p1800-face nil "27.1")

(defvar verilog-font-lock-ams-face
  'verilog-font-lock-ams-face
  "Font to use for Analog/Mixed Signal keywords.")
(defface verilog-font-lock-ams-face
  '((((class color)
      (background light))
     (:foreground "Purple" :weight bold ))
    (((class color)
      (background dark))
     (:foreground "orange1" :weight bold ))
    (t (:slant italic)))
  "Font lock mode face used to highlight AMS keywords."
  :group 'font-lock-highlighting-faces)

(defvar verilog-font-lock-grouping-keywords-face
  'verilog-font-lock-grouping-keywords-face
  "Font to use for Verilog Grouping Keywords (such as begin..end).")
(defface verilog-font-lock-grouping-keywords-face
  '((((class color)
      (background light))
     (:foreground "Purple" :weight bold ))
    (((class color)
      (background dark))
     (:foreground "orange1" :weight bold ))
    (t (:slant italic)))
  "Font lock mode face used to highlight verilog grouping keywords."
  :group 'font-lock-highlighting-faces)

(let* ((verilog-type-font-keywords
        (eval-when-compile
          (verilog-regexp-opt
           '("and" "buf" "bufif0" "bufif1" "cmos" "defparam" "event"
             "genvar" "highz0" "highz1" "inout" "input" "integer"
             "localparam" "mailbox" "nand" "nmos" "nor" "not" "notif0"
             "notif1" "or" "output" "parameter" "pmos" "pull0" "pull1"
             "pulldown" "pullup" "rcmos" "real" "realtime" "reg" "rnmos"
             "rpmos" "rtran" "rtranif0" "rtranif1" "semaphore" "signed"
             "specparam" "strong0" "strong1" "supply" "supply0" "supply1"
             "time" "tran" "tranif0" "tranif1" "tri" "tri0" "tri1" "triand"
             "trior" "trireg" "unsigned" "uwire" "vectored" "wand" "weak0"
             "weak1" "wire" "wor" "xnor" "xor"
             ;; 1800-2005
             "bit" "byte" "chandle" "const" "enum" "int" "logic" "longint"
             "packed" "ref" "shortint" "shortreal" "static" "string"
             "struct" "type" "typedef" "union" "var"
             ;; 1800-2009
             ;; 1800-2012
             "interconnect" "nettype" ) nil)))

       (verilog-pragma-keywords
        (eval-when-compile
          (verilog-regexp-opt
           '("surefire" "0in" "auto" "leda" "rtl_synthesis" "synopsys"
             "verilint" ) nil)))

       (verilog-ams-keywords
        (eval-when-compile
          (verilog-regexp-opt
           '("above" "abs" "absdelay" "abstol" "ac_stim" "access" "acos"
             "acosh" "aliasparam" "analog" "analysis" "asin" "asinh" "atan"
             "atan2" "atanh" "branch" "ceil" "connect" "connectmodule"
             "connectrules" "continuous" "cos" "cosh" "ddt" "ddt_nature"
             "ddx" "discipline" "discrete" "domain" "driver_update"
             "endconnectmodule" "endconnectrules" "enddiscipline" "endnature" "endparamset"
             "exclude" "exp" "final_step" "flicker_noise" "floor" "flow"
             "from" "ground" "hypot" "idt" "idt_nature" "idtmod" "inf"
             "initial_step" "laplace_nd" "laplace_np" "laplace_zd"
             "laplace_zp" "last_crossing" "limexp" "ln" "log" "max"
             "merged" "min" "nature" "net_resolution" "noise_table"
             "paramset" "potential" "pow" "resolveto" "sin" "sinh" "slew"
             "split" "sqrt" "tan" "tanh" "timer" "transition" "units"
             "white_noise" "wreal" "zi_nd" "zi_np" "zi_zd" "zi_zp"
             ;; Excluded AMS keywords: "assert" "cross" "string"
             ) nil)))

       (verilog-font-general-keywords
        (eval-when-compile
          (verilog-regexp-opt
           '("always" "assign" "automatic" "case" "casex" "casez" "cell"
             "config" "deassign" "default" "design" "disable" "edge" "else"
             "endcase" "endconfig" "endfunction" "endgenerate" "endmodule"
             "endprimitive" "endspecify" "endtable" "endtask" "for" "force"
             "forever" "fork" "function" "generate" "if" "ifnone" "incdir"
             "include" "initial" "instance" "join" "large" "liblist"
             "library" "macromodule" "medium" "module" "negedge"
             "noshowcancelled" "posedge" "primitive" "pulsestyle_ondetect"
             "pulsestyle_onevent" "release" "repeat" "scalared"
             "showcancelled" "small" "specify" "strength" "table" "task"
             "use" "wait" "while"
             ;; 1800-2005
             "alias" "always_comb" "always_ff" "always_latch" "assert"
             "assume" "analog" "before" "bind" "bins" "binsof" "break" "class"
             "clocking" "constraint" "context" "continue" "cover"
             "covergroup" "coverpoint" "cross" "dist" "do" "endclass"
             "endclocking" "endgroup" "endinterface" "endpackage"
             "endprogram" "endproperty" "endsequence" "expect" "export"
             "extends" "extern" "final" "first_match" "foreach" "forkjoin"
             "iff" "ignore_bins" "illegal_bins" "import" "inside"
             "interface" "intersect" "join_any" "join_none" "local"
             "matches" "modport" "new" "null" "package" "priority"
             "program" "property" "protected" "pure" "rand" "randc"
             "randcase" "randsequence" "return" "sequence" "solve" "super"
             "tagged" "this" "throughout" "timeprecision" "timeunit"
             "unique" "virtual" "void" "wait_order" "wildcard" "with"
             "within"
             ;; 1800-2009
             "accept_on" "checker" "endchecker" "eventually" "global"
             "implies" "let" "nexttime" "reject_on" "restrict" "s_always"
             "s_eventually" "s_nexttime" "s_until" "s_until_with" "strong"
             "sync_accept_on" "sync_reject_on" "unique0" "until"
             "until_with" "untyped" "weak"
             ;; 1800-2012
             "implements" "soft" ) nil)))

       (verilog-font-grouping-keywords
        (eval-when-compile
          (verilog-regexp-opt
           '( "begin" "end" ) nil))))

  (setq verilog-font-lock-keywords
	(list
	 ;; Fontify all builtin keywords
         (concat "\\<\\(" verilog-font-general-keywords "\\|"
                 ;; And user/system tasks and functions
                 "\\$[a-zA-Z][a-zA-Z0-9_\\$]*"
                 "\\)\\>")
	 ;; Fontify all types
         (cons (concat "\\<\\(" verilog-font-grouping-keywords "\\)\\>")
               (if verilog-highlight-grouping-keywords
                   'verilog-font-lock-grouping-keywords-face
		 'font-lock-type-face))
	 (cons (concat "\\<\\(" verilog-type-font-keywords "\\)\\>")
               'font-lock-type-face)
	 ;; Fontify Verilog-AMS keywords
	 (cons (concat "\\<\\(" verilog-ams-keywords "\\)\\>")
	       'verilog-font-lock-ams-face)))

  (setq verilog-font-lock-keywords-1
	(append verilog-font-lock-keywords
		(list
		 ;; Fontify module definitions
		 (list
                 "\\<\\(\\(macro\\|connect\\)?module\\|primitive\\|class\\|program\\|interface\\|package\\|task\\)\\>\\s-*\\(\\sw+\\)"
		  '(1 font-lock-keyword-face)
		  '(3 font-lock-function-name-face))
		 ;; Fontify function definitions
		 (list
		  (concat "\\<function\\>\\s-+\\(integer\\|real\\(time\\)?\\|time\\)\\s-+\\(\\sw+\\)" )
                  '(1 font-lock-keyword-face)
                  '(3 font-lock-constant-face))
		 '("\\<function\\>\\s-+\\(\\[[^]]+\\]\\)\\s-+\\(\\sw+\\)"
		   (1 font-lock-keyword-face)
		   (2 font-lock-constant-face append))
		 '("\\<function\\>\\s-+\\(\\sw+\\)"
		   1 'font-lock-constant-face append)
                 ;; Fontify variable names in declarations
                 (list
                  verilog-declaration-re
                  (list
                   ;; Anchored matcher (lookup Search-Based Fontification)
                   'verilog-declaration-varname-matcher
                   ;; Pre-form for this anchored matcher:
                   ;; First, avoid declaration keywords written in comments,
                   ;; which can also trigger this anchor.
                   '(if (and (not (verilog-in-comment-p))
                             (not (member (thing-at-point 'symbol) verilog-keywords)))
                        (verilog-single-declaration-end verilog-highlight-max-lookahead)
                      (point)) ;; => current declaration statement is of 0 length
                   nil ;; Post-form: nothing to be done
                   '(0 font-lock-variable-name-face))))))


  (setq verilog-font-lock-keywords-2
	(append verilog-font-lock-keywords-1
		(list
		 ;; Fontify pragmas
		 (concat "\\(//\\s-*\\(" verilog-pragma-keywords "\\)\\s-.*\\)")
		 ;; Fontify escaped names
		 '("\\(\\\\\\S-*\\s-\\)"  0 font-lock-function-name-face)
		 ;; Fontify macro definitions/ uses
		 '("`\\s-*[A-Za-z][A-Za-z0-9_]*" 0 (if (boundp 'font-lock-preprocessor-face)
                                                      'font-lock-preprocessor-face
                                                    'font-lock-type-face))
		 ;; Fontify delays/numbers
		 '("\\(@\\)\\|\\([ \t\n\f\r]#\\s-*\\(\\([0-9_.]+\\('s?[hdxbo][0-9a-fA-F_xz]*\\)?\\)\\|\\(([^()]+)\\|\\sw+\\)\\)\\)"
		   0 font-lock-type-face append)
     ;; Fontify property/sequence cycle delays - these start with '##'
     '("\\(##\\(\\sw+\\|\\[[^]]+\\]\\)\\)"
       0 font-lock-type-face append)
		 ;; Fontify instantiation names
		 '("\\([A-Za-z][A-Za-z0-9_]*\\)\\s-*(" 1 font-lock-function-name-face)
		 )))

  (setq verilog-font-lock-keywords-3
	(append verilog-font-lock-keywords-2
		(when verilog-highlight-translate-off
		  (list
		   ;; Fontify things in translate off regions
		   '(verilog-match-translate-off
		     (0 'verilog-font-lock-translate-off-face prepend))
		   )))))

;;
;; Buffer state preservation

(defmacro verilog-save-buffer-state (&rest body)
  "Execute BODY forms, saving state around insignificant change.
Changes in text properties like `face' or `syntax-table' are
considered insignificant.  This macro allows text properties to
be changed, even in a read-only buffer.

A change is considered significant if it affects the buffer text
in any way that isn't completely restored again.  Any
user-visible changes to the buffer must not be within a
`verilog-save-buffer-state'."
  `(let (,@(unless (>= emacs-major-version 25)
             '((inhibit-point-motion-hooks t)))
         (verilog-no-change-functions t))
     ,(if (fboundp 'with-silent-modifications)
          `(with-silent-modifications ,@body)
        ;; Backward compatible version of with-silent-modifications
        `(let* ((modified (buffer-modified-p))
                (buffer-undo-list t)
                (inhibit-read-only t)
                (inhibit-modification-hooks t)
                ;; XEmacs ignores inhibit-modification-hooks.
                before-change-functions after-change-functions
                deactivate-mark
                buffer-file-name        ; Prevent primitives checking
                buffer-file-truename)	; for file modification
           (unwind-protect
               (progn ,@body)
             (and (not modified)
                  (buffer-modified-p)
                  (verilog-restore-buffer-modified-p nil)))))))


(defvar verilog-save-font-mod-hooked nil
  "Local variable when inside a `verilog-save-font-no-change-functions' block.")
(make-variable-buffer-local 'verilog-save-font-mod-hooked)

(defmacro verilog-save-font-no-change-functions (&rest body)
 "Execute BODY forms, disabling all change hooks in BODY.
Includes temporary disabling of `font-lock' to restore the buffer
to full text form for parsing.  Additional actions may be specified with
`verilog-before-save-font-hook' and `verilog-after-save-font-hook'.
For insignificant changes, see instead `verilog-save-buffer-state'."
 `(if verilog-save-font-mod-hooked ; Short-circuit a recursive call
      (progn ,@body)
    ;; Before version 20, match-string with font-lock returns a
    ;; vector that is not equal to the string.  IE if on "input"
    ;; nil==(equal "input" (progn (looking-at "input") (match-string 0)))
    ;; Therefore we must remove and restore font-lock mode
    (verilog-run-hooks 'verilog-before-save-font-hook)
    (let* ((verilog-save-font-mod-hooked (- (point-max) (point-min)))
           ;; Significant speed savings with no font-lock properties
           (fontlocked (when font-lock-mode
                         (font-lock-mode 0)
                         t)))
      (run-hook-with-args 'before-change-functions (point-min) (point-max))
      (unwind-protect
          ;; Must inhibit and restore hooks before restoring font-lock
          (let* (,@(unless (>= emacs-major-version 25)
                     '((inhibit-point-motion-hooks t) ;Obsolete since 25.1
                       ;; XEmacs and pre-Emacs 21 ignore
                       ;; `inhibit-modification-hooks'.
                       before-change-functions after-change-functions))
                 (inhibit-modification-hooks t)
                 (verilog-no-change-functions t))
            (progn ,@body))
        ;; Unwind forms
        (run-hook-with-args 'after-change-functions (point-min) (point-max)
                            verilog-save-font-mod-hooked) ; old length
        (when fontlocked (font-lock-mode t))
        (verilog-run-hooks 'verilog-after-save-font-hook)))))

;;
;; Comment detection and caching

(defvar verilog-scan-cache-preserving nil
  "If true, the specified buffer's comment properties are static.
Buffer changes will be ignored.  See `verilog-inside-comment-or-string-p'
and `verilog-scan'.")

(defvar verilog-scan-cache-tick nil
  "Modification tick at which `verilog-scan' was last completed.")
(make-variable-buffer-local 'verilog-scan-cache-tick)

(defun verilog-scan-cache-flush ()
  "Flush the `verilog-scan' cache."
  (setq verilog-scan-cache-tick nil))

(defun verilog-scan-cache-ok-p ()
  "Return t if the scan cache is up to date."
  (or (and verilog-scan-cache-preserving
	   (eq verilog-scan-cache-preserving (current-buffer))
	   verilog-scan-cache-tick)
      (equal verilog-scan-cache-tick (buffer-chars-modified-tick))))

(defmacro verilog-save-scan-cache (&rest body)
  "Execute the BODY forms, allowing scan cache preservation within BODY.
This requires that insertions must use `verilog-insert'."
  ;; If the buffer is out of date, trash it, as we'll not check later the tick
  ;; Note this must work properly if there's multiple layers of calls
  ;; to verilog-save-scan-cache even with differing ticks.
  `(progn
     (unless (verilog-scan-cache-ok-p)   ; Must be before let
       (setq verilog-scan-cache-tick nil))
     (let* ((verilog-scan-cache-preserving (current-buffer)))
       (progn ,@body))))

(defun verilog-scan-region (beg end)
  "Parse between BEG and END for `verilog-inside-comment-or-string-p'.
This creates v-cmts properties where comments are in force."
  ;; Why properties and not overlays?  Overlays have much slower non O(1)
  ;; lookup times.
  ;; This function is warm - called on every verilog-insert
  (save-excursion
    (save-match-data
      (verilog-save-buffer-state
       (let (pt)
	 (goto-char beg)
	 (while (< (point) end)
	   (cond ((looking-at "//")
		  (setq pt (point))
		  (or (search-forward "\n" end t)
		      (goto-char end))
		  ;; "1+": The leading // or /* itself isn't considered as
		  ;; being "inside" the comment, so that a (search-backward)
		  ;; that lands at the start of the // won't mis-indicate
		  ;; it's inside a comment.  Also otherwise it would be
		  ;; hard to find a commented out /*AS*/ vs one that isn't
		  (put-text-property (1+ pt) (point) 'v-cmts t))
		 ((looking-at "/\\*")
		  (setq pt (point))
		  (or (search-forward "*/" end t)
		      ;; No error - let later code indicate it so we can
		      ;; use inside functions on-the-fly
		      ;;(error "%s: Unmatched /* */, at char %d"
		      ;;       (verilog-point-text) (point))
		      (goto-char end))
		  (put-text-property (1+ pt) (point) 'v-cmts t))
		 ((looking-at "\"")
		  (setq pt (point))
                  (or (re-search-forward "[^\\]\"" end t)  ; don't forward-char first, since we look for a non backslash first
		      ;; No error - let later code indicate it so we can
		      (goto-char end))
		  (put-text-property (1+ pt) (point) 'v-cmts t))
		 (t
		  (forward-char 1)
		  (if (re-search-forward "[/\"]" end t)
		      (backward-char 1)
		    (goto-char end))))))))))

(defun verilog-scan ()
  "Parse the buffer, marking all comments with properties.
Also assumes any text inserted since `verilog-scan-cache-tick'
either is ok to parse as a non-comment, or `verilog-insert' was used."
  ;; See also `verilog-scan-debug' and `verilog-scan-and-debug'
  (unless (verilog-scan-cache-ok-p)
    (save-excursion
      (verilog-save-buffer-state
       (when verilog-debug
         (message "Scanning %s cache=%s cachetick=%S tick=%S" (current-buffer)
                  verilog-scan-cache-preserving verilog-scan-cache-tick
                  (buffer-chars-modified-tick)))
       (remove-text-properties (point-min) (point-max) '(v-cmts nil))
       (verilog-scan-region (point-min) (point-max))
       (setq verilog-scan-cache-tick (buffer-chars-modified-tick))
       (when verilog-debug (message "Scanning... done"))))))

(defun verilog-scan-debug ()
  "For debugging, show with display face results of `verilog-scan'."
  (font-lock-mode 0)
  ;;(if dbg (setq dbg (concat dbg "verilog-scan-debug\n")))
  (save-excursion
    (goto-char (point-min))
    (remove-text-properties (point-min) (point-max) '(face nil))
    (while (not (eobp))
      (cond ((get-text-property (point) 'v-cmts)
	     (put-text-property (point) (1+ (point)) 'face 'underline)
	     ;;(if dbg (setq dbg (concat dbg (format "  v-cmts at %S\n" (point)))))
	     (forward-char 1))
	    (t
	     (goto-char (or (next-property-change (point)) (point-max))))))))

(defun verilog-scan-and-debug ()
  "For debugging, run `verilog-scan' and `verilog-scan-debug'."
  (let (verilog-scan-cache-preserving
	verilog-scan-cache-tick)
    (goto-char (point-min))
    (verilog-scan)
    (verilog-scan-debug)))

(defun verilog-inside-comment-or-string-p (&optional pos)
  "Check if optional point POS is inside a comment.
This may require a slow pre-parse of the buffer with `verilog-scan'
to establish comment properties on all text."
  ;; This function is very hot
  (verilog-scan)
  (if pos
      (and (>= pos (point-min))
	   (get-text-property pos 'v-cmts))
    (get-text-property (point) 'v-cmts)))

(defun verilog-insert (&rest stuff)
  "Insert STUFF arguments, tracking for `verilog-inside-comment-or-string-p'.
Any insert that includes a comment must have the entire comment
inserted using a single call to `verilog-insert'."
  (let ((pt (point)))
    (while stuff
      (insert (car stuff))
      (setq stuff (cdr stuff)))
    (verilog-scan-region pt (point))))

;; More searching

(defun verilog-declaration-end ()
  (search-forward ";" nil t))

(defun verilog-single-declaration-end (limit)
  "Return pos where current (single) declaration statement ends.
Also, this function moves POINT forward to the start of a variable name
\(skipping the range-part and whitespace).
Function expected to be called with POINT just after a declaration keyword.
LIMIT sets the max POINT for searching and moving to.  No such limit if LIMIT
is 0.

Meaning of *single* declaration:
   E.g. In a module's port-list -
           module test(input clk, rst, x, output [1:0] y);
   Here `input clk, rst, x' is 1 *single* declaration statement,
and `output [1:0] y' is the other single declaration.  In the 1st single
declaration, POINT is moved to start of `clk'.  And in the 2nd declaration,
POINT is moved to `y'."
  (let (maxpoint old-point)
    ;; maxpoint = min(curr-point + limit, buffer-size)
    (setq maxpoint (if (eq limit 0)
                       (point-max) ;; no bounds if search-bound is zero
                     (+ (point) limit)))
    (if (> maxpoint (buffer-size)) (setq maxpoint (buffer-size)))

    ;; Skip comment - range - comment
    (verilog-forward-ws&directives maxpoint)
    (when (eq (char-after) ?\[)
      (re-search-forward verilog-range-re maxpoint t))
    (verilog-forward-ws&directives maxpoint)

    ;; Move forward until a delimiter is reached which marks end of current
    ;; single declaration. Return point at found delimiter
    (save-excursion
      (while (and (< (point) maxpoint)
                  (not (eq old-point (point)))
                  (not (eq (char-after) ?\; ))
                  (not (eq (char-after) ?\) ))
                  (not (looking-at (verilog-get-declaration-re))))
        (setq old-point (point))
        (ignore-errors
          (forward-sexp)
          (verilog-forward-ws&directives maxpoint)
          (when (eq (char-after) ?,)
            (forward-char)
            (verilog-forward-ws&directives maxpoint))))
    (point))))

(defun verilog-declaration-varname-matcher (limit)
  "Match first variable name b/w POINT & LIMIT, move POINT to next variable.
Expected to be called within a declaration statement, with POINT already beyond
the declaration keyword and range ([a:b])
This function moves POINT to the next variable within the same declaration (if
it exists).
LIMIT is expected to be the pos at which current single-declaration ends,
obtained using `verilog-single-declaration-end'."
  (when (and verilog-fontify-variables
             (not (member (thing-at-point 'symbol) verilog-keywords)))
    (let (found-var old-point)
      ;; Remove starting whitespace
      (verilog-forward-ws&directives limit)
      (when (< (point) limit) ;; no matching if this is violated
        ;; Find the variable name (match-data is set here)
        (setq found-var (re-search-forward verilog-identifier-sym-re limit t))
        ;; Walk to this variable's delimiter
        (save-match-data
          (verilog-forward-ws&directives limit)
          (setq old-point nil)
          (while (and (< (point) limit)
                      (not (member (char-after) '(?, ?\) ?\] ?\} ?\;)))
                      (not (eq old-point (point))))
            (setq old-point (point))
            (verilog-forward-ws&directives limit)
            (forward-sexp)
            (verilog-forward-ws&directives limit))
          ;; Only a comma or semicolon expected at this point
          (skip-syntax-forward "."))
        found-var))))

(defun verilog-point-text (&optional pointnum)
  "Return text describing where POINTNUM or current point is (for errors).
Use filename, if current buffer being edited shorten to just buffer name."
  (concat (or (and (equal (window-buffer) (current-buffer))
		   (buffer-name))
	      buffer-file-name
	      (buffer-name))
	  ":" (int-to-string (1+ (count-lines (point-min) (or pointnum (point)))))))

(defun electric-verilog-backward-sexp ()
  "Move backward over one balanced expression."
  (interactive)
  ;; before that see if we are in a comment
  (verilog-backward-sexp))

(defun electric-verilog-forward-sexp ()
  "Move forward over one balanced expression."
  (interactive)
  ;; before that see if we are in a comment
  (verilog-forward-sexp))

(defun verilog-forward-sexp-function (arg)
  "Move forward ARG sexps."
  ;; Used by hs-minor-mode
  (if (< arg 0)
      (verilog-backward-sexp)
    (verilog-forward-sexp)))

(defun verilog-backward-sexp ()
  (let ((reg)
	(elsec 1)
	(found nil)
	(st (point)))
    (unless (looking-at "\\<")
      (forward-word-strictly -1))
    (cond
     ((save-excursion
        (goto-char st)
        (member (preceding-char) '(?\) ?\} ?\])))
      (goto-char st)
      (backward-sexp 1))
     ((verilog-skip-backward-comment-or-string))
     ((looking-at "\\<else\\>")
      (setq reg (concat
		 verilog-end-block-re
		 "\\|\\(\\<else\\>\\)"
		 "\\|\\(\\<if\\>\\)"))
      (while (and (not found)
		  (verilog-re-search-backward reg nil 'move))
	(cond
	 ((match-end 1) ; matched verilog-end-block-re
	  ;; try to leap back to matching outward block by striding across
	  ;; indent level changing tokens then immediately
	  ;; previous line governs indentation.
	  (verilog-leap-to-head))
	 ((match-end 2) ; else, we're in deep
	  (setq elsec (1+ elsec)))
	 ((match-end 3) ; found it
	  (setq elsec (1- elsec))
	  (if (= 0 elsec)
	      ;; Now previous line describes syntax
	      (setq found 't))))))
     ((looking-at verilog-end-block-re)
      (verilog-leap-to-head))
     (;; Fallback, when current word does not match `verilog-end-block-re'
      (looking-at (concat
                   "\\(\\<endmodule\\>\\)\\|"        ; 1
                   "\\(\\<endprimitive\\>\\)\\|"     ; 2
                   "\\(\\<endclass\\>\\)\\|"         ; 3
                   "\\(\\<endprogram\\>\\)\\|"       ; 4
                   "\\(\\<endinterface\\>\\)\\|"     ; 5
                   "\\(\\<endpackage\\>\\)\\|"       ; 6
                   "\\(\\<endconnectmodule\\>\\)\\|" ; 7
                   "\\(\\<endchecker\\>\\)\\|"       ; 8
                   "\\(\\<endconfig\\>\\)"))         ; 9
      (cond
       ((match-end 1)
	(verilog-re-search-backward "\\<\\(macro\\)?module\\>" nil 'move))
       ((match-end 2)
	(verilog-re-search-backward "\\<primitive\\>" nil 'move))
       ((match-end 3)
	(verilog-re-search-backward "\\<class\\>" nil 'move))
       ((match-end 4)
	(verilog-re-search-backward "\\<program\\>" nil 'move))
       ((match-end 5)
	(verilog-re-search-backward "\\<interface\\>" nil 'move))
       ((match-end 6)
	(verilog-re-search-backward "\\<package\\>" nil 'move))
       ((match-end 7)
        (verilog-re-search-backward "\\<connectmodule\\>" nil 'move))
       ((match-end 8)
        (verilog-re-search-backward "\\<checker\\>" nil 'move))
       ((match-end 9)
        (verilog-re-search-backward "\\<config\\>" nil 'move))
       (t
	(goto-char st)
	(backward-sexp 1))))
     (t
      (goto-char st)
      (backward-sexp)))))

(defun verilog-forward-sexp ()
  (let ((reg)
	(md 2)
	(st (point))
	(nest 'yes))
    (unless (looking-at "\\<")
      (forward-word-strictly -1))
    (cond
     ((save-excursion
        (goto-char st)
        (member (following-char) '(?\( ?\{ ?\[)))
      (goto-char st)
      (forward-sexp 1))
     ((verilog-skip-forward-comment-or-string)
      (verilog-forward-syntactic-ws))
     ((looking-at verilog-beg-block-re-ordered)
      (cond
       ((match-end 1);
	;; Search forward for matching end
	(setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" ))
       ((match-end 2)
	;; Search forward for matching endcase
	(setq reg "\\(\\<randcase\\>\\|\\(\\<unique0?\\>\\s-+\\|\\<priority\\>\\s-+\\)?\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" )
        (setq md 3)  ; ender is third item in regexp
	)
       ((match-end 4)
	;; might be "disable fork" or "wait fork"
	(let
	    (here)
	  (if (or
	       (looking-at verilog-disable-fork-re)
	       (and (looking-at "fork")
		    (progn
                      (setq here (point))  ; sometimes a fork is just a fork
		      (forward-word-strictly -1)
		      (looking-at verilog-disable-fork-re))))
              (progn  ; it is a disable fork; ignore it
		(goto-char (match-end 0))
		(forward-word-strictly 1)
		(setq reg nil))
            (progn  ; it is a nice simple fork
              (goto-char here)   ; return from looking for "disable fork"
	      ;; Search forward for matching join
	      (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)" )))))
       ((match-end 6)
	;; Search forward for matching endclass
	(setq reg "\\(\\<class\\>\\)\\|\\(\\<endclass\\>\\)" ))

       ((match-end 7)
	;; Search forward for matching endtable
	(setq reg "\\<endtable\\>" )
	(setq nest 'no))
       ((match-end 8)
        ;; Search forward for matching endspecify
        (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
       ((match-end 9)
        ;; Search forward for matching endfunction
        (setq reg "\\<endfunction\\>" )
        (setq nest 'no))
       ((match-end 10)
        ;; Search forward for matching endfunction
        (setq reg "\\<endfunction\\>" )
        (setq nest 'no))
       ((match-end 11)
        ;; Search forward for matching endtask
        (setq reg "\\<endtask\\>" )
        (setq nest 'no))
       ((match-end 12)
        ;; Search forward for matching endtask
        (setq reg "\\<endtask\\>" )
        (setq nest 'no))
       ((match-end 13)
        ;; Search forward for matching endgenerate
        (setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
       ((match-end 14)
        ;; Search forward for matching endgroup
        (setq reg "\\(\\<covergroup\\>\\)\\|\\(\\<endgroup\\>\\)" ))
       ((match-end 15)
        ;; Search forward for matching endproperty
        (setq reg "\\(\\<property\\>\\)\\|\\(\\<endproperty\\>\\)" ))
       ((match-end 16)
        ;; Search forward for matching endsequence
        (setq reg "\\(\\<\\(rand\\)?sequence\\>\\)\\|\\(\\<endsequence\\>\\)" )
        (setq md 3)) ; 3 to get to endsequence in the reg above
       ((match-end 17)
        ;; Search forward for matching endclocking
        (setq reg "\\(\\<clocking\\>\\)\\|\\(\\<endclocking\\>\\)" ))
       ((match-end 20)
        ;; Search forward for matching `ifn?def, can be `else `elseif or `endif
        (setq reg "\\(\\<`ifn?def\\>\\)\\|\\(\\<`endif\\>\\|\\<`else\\>\\|\\<`elsif\\>\\)" ))
       ((match-end 21)
        ;; Search forward for matching `else, can be `endif
        (setq reg "\\(\\<`else\\>\\|\\<`ifn?def\\>\\)\\|\\(\\<`endif\\>\\)" ))
       ((match-end 22)
        ;; Search forward for matching `elsif, can be `else or `endif, DONT support `elsif
        (setq reg "\\(\\<`elsif\\>\\|\\<`ifn?def\\>\\)\\|\\(\\<`endif\\>\\|\\<`else\\>\\)" )))
      (if (and reg
	       (forward-word-strictly 1))
	  (catch 'skip
	    (if (eq nest 'yes)
		(let ((depth 1)
		      here)
		  (while (verilog-re-search-forward reg nil 'move)
		    (cond
                     ((and (or (match-end md)
                               (and (member (match-string-no-properties 1) '("`else" "`elsif"))
                                    (= 1 depth)))
                           (or (and (member (match-string-no-properties 2) '("`else" "`elsif"))
                                    (= 1 depth))
                               ;; stop at `else/`elsif which matching ifn?def (or `elsif with same depth)
                               ;; a closer in regular expression, so we are climbing out
                               (not (member (match-string-no-properties 2) '("`else" "`elsif")))))
		      (setq depth (1- depth))
		      (if (= 0 depth) ; we are out!
			  (throw 'skip 1)))
                     ((and (match-end 1)  ; an opener in the r-e, so we are in deeper now
                           (not (member (match-string-no-properties 1) '("`else" "`elsif"))))
		      (setq here (point)) ; remember where we started
		      (goto-char (match-beginning 1))
		      (cond
                       ((verilog-looking-back "\\(\\<typedef\\>\\s-+\\)" (point-at-bol))
                        ;; avoid nesting for typedef class defs
                        (forward-word-strictly 1))
                       ((if (or
			     (looking-at verilog-disable-fork-re)
			     (and (looking-at "fork")
				  (progn
				    (forward-word-strictly -1)
				    (looking-at verilog-disable-fork-re))))
                            (progn  ; it is a disable fork; another false alarm
			      (goto-char (match-end 0)))
                          (progn  ; it is a simple fork (or has nothing to do with fork)
			    (goto-char here)
			    (setq depth (1+ depth))))))))))
	      (if (verilog-re-search-forward reg nil 'move)
		  (throw 'skip 1))))))

     ((looking-at (concat
                   "\\(\\<\\(macro\\)?module\\>\\)\\|"                         ; 1,2
                   "\\(\\<primitive\\>\\)\\|"                                  ; 3
                   "\\(\\(\\(interface\\|virtual\\)\\s-+\\)?\\<class\\>\\)\\|" ; 4,5,6
                   "\\(\\<program\\>\\)\\|"                                    ; 7
                   "\\(\\<interface\\>\\)\\|"                                  ; 8
                   "\\(\\<package\\>\\)\\|"                                    ; 9
                   "\\(\\<connectmodule\\>\\)\\|"                              ; 10
                   "\\(\\<generate\\>\\)\\|"                                   ; 11
                   "\\(\\<checker\\>\\)\\|"                                    ; 12
                   "\\(\\<config\\>\\)"))                                      ; 13
      (cond
       ((match-end 1)
	(verilog-re-search-forward "\\<endmodule\\>" nil 'move))
       ((match-end 3)
	(verilog-re-search-forward "\\<endprimitive\\>" nil 'move))
       ((match-end 4)
	(verilog-re-search-forward "\\<endclass\\>" nil 'move))
       ((match-end 7)
	(verilog-re-search-forward "\\<endprogram\\>" nil 'move))
       ((match-end 8)
	(verilog-re-search-forward "\\<endinterface\\>" nil 'move))
       ((match-end 9)
	(verilog-re-search-forward "\\<endpackage\\>" nil 'move))
       ((match-end 10)
        (verilog-re-search-forward "\\<endconnectmodule\\>" nil 'move))
       ((match-end 11)
        (verilog-re-search-forward "\\<endgenerate\\>" nil 'move))
       ((match-end 12)
        (verilog-re-search-forward "\\<endchecker\\>" nil 'move))
       ((match-end 13)
        (verilog-re-search-forward "\\<endconfig\\>" nil 'move))
       (t
	(goto-char st)
	(if (= (following-char) ?\) )
	    (forward-char 1)
	  (forward-sexp 1)))))
     (t
      (goto-char st)
      (if (= (following-char) ?\) )
	  (forward-char 1)
	(forward-sexp 1))))))

(defun verilog-declaration-beg ()
  (verilog-re-search-backward (verilog-get-declaration-re) (bobp) t))

(defun verilog-align-typedef-enabled-p ()
  "Return non-nil if alignment of user typedefs is enabled.
This will be automatically set when either `verilog-align-typedef-regexp'
or `verilog-align-typedef-words' are non-nil."
  (when (or verilog-align-typedef-regexp
            verilog-align-typedef-words)
    t))

(defun verilog-get-declaration-typedef-re ()
  "Return regexp of a user defined typedef.
See `verilog-align-typedef-regexp' and `verilog-align-typedef-words'."
  (let (typedef-re words words-re re)
    (when (verilog-align-typedef-enabled-p)
      (setq typedef-re verilog-align-typedef-regexp)
      (setq words verilog-align-typedef-words)
      (setq words-re (verilog-regexp-words verilog-align-typedef-words))
      (cond ((and typedef-re (not words))
             (setq re typedef-re))
            ((and (not typedef-re) words)
             (setq re words-re))
            ((and typedef-re words)
             (setq re (concat verilog-align-typedef-regexp "\\|" words-re))))
      (concat "\\s-*" "\\(" verilog-declaration-prefix-re "\\s-*\\(" verilog-range-re "\\)?" "\\s-*\\)?"
              (concat "\\(" re "\\)")
              "\\(\\s-*" verilog-range-re "\\)?\\s-+"))))

(defun verilog-get-declaration-re (&optional type)
  "Return declaration regexp depending on customizable variables and TYPE."
  (let ((re (cond ((equal type 'iface-mp)
                   verilog-declaration-or-iface-mp-re)
                  ((equal type 'embedded-comments)
                   verilog-declaration-embedded-comments-re)
                  (verilog-indent-declaration-macros
                   verilog-declaration-re-macro)
                  (t
                   verilog-declaration-re))))
    (when (and (verilog-align-typedef-enabled-p)
               (or (string= re verilog-declaration-or-iface-mp-re)
                   (string= re verilog-declaration-re)))
      (setq re (concat "\\(" (verilog-get-declaration-typedef-re) "\\)\\|\\(" re "\\)")))
    re))

(defun verilog-looking-at-decl-to-align ()
  "Return non-nil if pointing at a Verilog variable declaration that must be aligned."
  (let* ((re (verilog-get-declaration-re))
         (valid-re (looking-at re))
         (id-pos (match-end 0)))
    (and valid-re
         (not (verilog-at-struct-decl-p))
         (not (verilog-at-enum-decl-p))
         (save-excursion
           (goto-char id-pos)
           (verilog-forward-syntactic-ws)
           (and (not (looking-at ";"))
                (not (member (thing-at-point 'symbol) verilog-keywords))
                (progn ; Avoid alignment of instances whose name match user defined types
                  (forward-word)
                  (verilog-forward-syntactic-ws)
                  (not (looking-at "("))))))))

;;; Mode:
;;
(defvar verilog-which-tool 1)
;;;###autoload
(define-derived-mode verilog-mode prog-mode "Verilog"
  "Major mode for editing Verilog code.
\\<verilog-mode-map>
See \\[describe-function] verilog-auto (\\[verilog-auto]) for details on how
AUTOs can improve coding efficiency.

Use \\[verilog-faq] for a pointer to frequently asked questions.

NEWLINE, TAB indents for Verilog code.
Delete converts tabs to spaces as it moves back.

Supports highlighting.

Turning on Verilog mode calls the value of the variable `verilog-mode-hook'
with no args, if that value is non-nil.

Variables controlling indentation/edit style:

 variable `verilog-indent-level'      (default 3)
   Indentation of Verilog statements with respect to containing block.
 `verilog-indent-level-module'        (default 3)
   Absolute indentation of Module level Verilog statements.
   Set to 0 to get initial and always statements lined up
   on the left side of your screen.
 `verilog-indent-level-declaration'   (default 3)
   Indentation of declarations with respect to containing block.
   Set to 0 to get them list right under containing block.
 `verilog-indent-level-behavioral'    (default 3)
   Indentation of first begin in a task or function block
   Set to 0 to get such code to lined up underneath the task or
   function keyword.
 `verilog-indent-level-directive'     (default 1)
   Indentation of \\=`ifdef/\\=`endif blocks.
 `verilog-indent-ignore-multiline-defines' (default t)
   Non-nil means ignore indentation on lines that are part of a multiline
   define.
 `verilog-indent-ignore-regexp'     (default nil
   Regexp that matches lines that should be ignored for indentation.
 `verilog-cexp-indent'              (default 1)
   Indentation of Verilog statements broken across lines i.e.:
      if (a)
        begin
 `verilog-case-indent'              (default 2)
   Indentation for case statements.
 `verilog-auto-newline'             (default nil)
   Non-nil means automatically newline after semicolons and the punctuation
   mark after an end.
 `verilog-auto-indent-on-newline'   (default t)
   Non-nil means automatically indent line after newline.
 `verilog-tab-always-indent'        (default t)
   Non-nil means TAB in Verilog mode should always reindent the current line,
   regardless of where in the line point is when the TAB command is used.
 `verilog-indent-begin-after-if'    (default t)
   Non-nil means to indent begin statements following a preceding
   if, else, while, for and repeat statements, if any.  Otherwise,
   the begin is lined up with the preceding token.  If t, you get:
      if (a)
         begin // amount of indent based on `verilog-cexp-indent'
   otherwise you get:
      if (a)
      begin
 `verilog-indent-class-inside-pkg'  (default t)
   Non-nil means indent classes inside packages.
   Otherwise, classes have zero indentation.
 `verilog-auto-endcomments'         (default t)
   Non-nil means a comment /* ... */ is set after the ends which ends
   cases, tasks, functions and modules.
   The type and name of the object will be set between the braces.
 `verilog-minimum-comment-distance' (default 10)
   Minimum distance (in lines) between begin and end required before a comment
   will be inserted.  Setting this variable to zero results in every
   end acquiring a comment; the default avoids too many redundant
   comments in tight quarters.
 `verilog-align-decl-expr-comments' (default t)
   Non-nil means align declaration and expressions comments.
 `verilog-align-comment-distance'   (default 1)
   Distance (in spaces) between longest declaration and comments.
   Only works if `verilog-align-decl-expr-comments' is non-nil.
 `verilog-align-assign-expr'        (default nil)
   Non-nil means align expressions of continuous assignments.
 `verilog-align-typedef-regexp'     (default nil)
   Regexp that matches user typedefs for declaration alignment.
 `verilog-align-typedef-words'      (default nil)
   List of words that match user typedefs for declaration alignment.
 `verilog-auto-lineup'              (default `declarations')
   List of contexts where auto lineup of code should be done.

Variables controlling other actions:

 `verilog-linter'                   (default `none')
   Unix program to call to run the lint checker.  This is the default
   command for \\[compile-command] and \\[verilog-auto-save-compile].

See \\[customize] for the complete list of variables.

AUTO expansion functions are, in part:

    \\[verilog-auto]  Expand AUTO statements.
    \\[verilog-delete-auto]  Remove the AUTOs.
    \\[verilog-inject-auto]  Insert AUTOs for the first time.

Some other functions are:

    \\[completion-at-point]    Complete word with appropriate possibilities.
    \\[verilog-mark-defun]  Mark function.
    \\[verilog-beg-of-defun]  Move to beginning of current function.
    \\[verilog-end-of-defun]  Move to end of current function.
    \\[verilog-label-be]  Label matching begin ... end, fork ... join, etc
                          statements.

    \\[verilog-comment-region]  Put marked area in a comment.
    \\[verilog-uncomment-region]  Uncomment an area commented with
                                  \\[verilog-comment-region].
    \\[verilog-insert-block]  Insert begin ... end.
    \\[verilog-star-comment]    Insert /* ... */.

    \\[verilog-sk-always]  Insert an always @(AS) begin .. end block.
    \\[verilog-sk-begin]  Insert a begin .. end block.
    \\[verilog-sk-case]  Insert a case block, prompting for details.
    \\[verilog-sk-for]  Insert a for (...) begin .. end block, prompting for
                        details.
    \\[verilog-sk-generate]  Insert a generate .. endgenerate block.
    \\[verilog-sk-header]  Insert a header block at the top of file.
    \\[verilog-sk-initial]  Insert an initial begin .. end block.
    \\[verilog-sk-fork]  Insert a fork begin .. end .. join block.
    \\[verilog-sk-module]  Insert a module .. (/*AUTOARG*/);.. endmodule block.
    \\[verilog-sk-ovm-class]  Insert an OVM Class block.
    \\[verilog-sk-uvm-object]  Insert an UVM Object block.
    \\[verilog-sk-uvm-component]  Insert an UVM Component block.
    \\[verilog-sk-primitive]  Insert a primitive .. (.. );.. endprimitive block.
    \\[verilog-sk-repeat]  Insert a repeat (..) begin .. end block.
    \\[verilog-sk-specify]  Insert a specify .. endspecify block.
    \\[verilog-sk-task]  Insert a task .. begin .. end endtask block.
    \\[verilog-sk-while]  Insert a while (...) begin .. end block,
                       prompting for details.
    \\[verilog-sk-casex]  Insert a casex (...) item: begin.. end endcase block,
                       prompting for details.
    \\[verilog-sk-casez]  Insert a casez (...) item: begin.. end endcase block,
                       prompting for details.
    \\[verilog-sk-if]  Insert an if (..) begin .. end block.
    \\[verilog-sk-else-if]  Insert an else if (..) begin .. end block.
    \\[verilog-sk-comment]  Insert a comment block.
    \\[verilog-sk-assign]  Insert an assign .. = ..; statement.
    \\[verilog-sk-function]  Insert a function .. begin .. end endfunction
                             block.
    \\[verilog-sk-input]  Insert an input declaration, prompting for details.
    \\[verilog-sk-output]  Insert an output declaration, prompting for details.
    \\[verilog-sk-state-machine]  Insert a state machine definition, prompting
                                  for details.
    \\[verilog-sk-inout]  Insert an inout declaration, prompting for details.
    \\[verilog-sk-wire]  Insert a wire declaration, prompting for details.
    \\[verilog-sk-reg]  Insert a register declaration, prompting for details.
    \\[verilog-sk-define-signal]  Define signal under point as a register at
                                  the top of the module.

All key bindings can be seen in a Verilog-buffer with \\[describe-bindings].
Key bindings specific to `verilog-mode-map' are:

\\{verilog-mode-map}"
  :abbrev-table verilog-mode-abbrev-table
  (set (make-local-variable 'beginning-of-defun-function)
       #'verilog-beg-of-defun)
  (set (make-local-variable 'end-of-defun-function)
       #'verilog-end-of-defun)
  (set-syntax-table verilog-mode-syntax-table)
  (set (make-local-variable 'indent-line-function)
       #'verilog-indent-line-relative)
  (set (make-local-variable 'comment-indent-function) #'verilog-comment-indent)
  (set (make-local-variable 'parse-sexp-ignore-comments) nil)
  (set (make-local-variable 'comment-start) "// ")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'comment-start-skip) "/\\*+ *\\|// *")
  (set (make-local-variable 'comment-multi-line) nil)
  ;; Set up for compilation
  (setq verilog-which-tool 1)
  (setq verilog-tool 'verilog-linter)
  (verilog-set-compile-command)
  (when (boundp 'hack-local-variables-hook)  ; Also modify any file-local-variables
    (add-hook 'hack-local-variables-hook #'verilog-modify-compile-command t))

  ;; Setting up menus
  (when (featurep 'xemacs)
    (easy-menu-add verilog-stmt-menu)
    (easy-menu-add verilog-menu)
    (setq mode-popup-menu (cons "Verilog Mode" verilog-stmt-menu)))

  ;; Stuff for GNU Emacs
  (set (make-local-variable 'font-lock-defaults)
       `((verilog-font-lock-keywords
	  verilog-font-lock-keywords-1
	  verilog-font-lock-keywords-2
	  verilog-font-lock-keywords-3)
         nil nil nil
	 ,(if (functionp 'syntax-ppss)
	      ;; verilog-beg-of-defun uses syntax-ppss, and syntax-ppss uses
	      ;; font-lock-beginning-of-syntax-function, so
	      ;; font-lock-beginning-of-syntax-function, can't use
              ;; verilog-beg-of-defun.
	      nil
	    'verilog-beg-of-defun)))

  ;; Stuff for multiline font-lock
  (set (make-local-variable 'font-lock-multiline) t)

  ;;------------------------------------------------------------
  ;; now hook in 'verilog-highlight-include-files (eldo-mode.el&spice-mode.el)
  ;; all buffer local:
  (unless noninteractive  ; Else can't see the result, and change hooks are slow
    (when (featurep 'xemacs)
      (make-local-hook 'font-lock-mode-hook)
      (make-local-hook 'font-lock-after-fontify-buffer-hook); doesn't exist in Emacs
      (make-local-hook 'after-change-functions))
    (add-hook 'font-lock-mode-hook #'verilog-highlight-buffer t t)
    (add-hook 'font-lock-after-fontify-buffer-hook #'verilog-highlight-buffer t t) ; not in Emacs
    (add-hook 'after-change-functions #'verilog-highlight-region t t))

  ;; Tell imenu how to handle Verilog.
  (set (make-local-variable 'imenu-generic-expression)
       verilog-imenu-generic-expression)
  ;; Tell which-func-modes that imenu knows about verilog
  (when (and (boundp 'which-func-modes) (listp which-func-modes))
    (add-to-list 'which-func-modes 'verilog-mode))
  ;; hideshow support
  (when (boundp 'hs-special-modes-alist)
    (unless (assq 'verilog-mode hs-special-modes-alist)
      (setq hs-special-modes-alist
            (cons '(verilog-mode "\\<begin\\>" "\\<end\\>" nil
                                 verilog-forward-sexp-function)
                  hs-special-modes-alist))))

  (add-hook 'completion-at-point-functions
            #'verilog-completion-at-point nil 'local)

  ;; Stuff for autos
  (add-hook (if (boundp 'write-contents-hooks) 'write-contents-hooks
              'write-contents-functions) ; Emacs >= 22.1
            #'verilog-auto-save-check nil 'local)
  ;; verilog-mode-hook call added by define-derived-mode
  )

;;; Integration with the speedbar:
;;

;; Avoid problems with XEmacs byte-compiles.
;; For GNU Emacs, the eval-after-load will handle if it isn't loaded yet.
(when (eval-when-compile (fboundp 'declare-function))
  (declare-function speedbar-add-supported-extension "speedbar" (extension)))

(defun verilog-speedbar-initialize ()
  "Initialize speedbar to understand `verilog-mode'."
  ;; Set Verilog file extensions (extracted from `auto-mode-alist')
  (let ((mode-alist auto-mode-alist))
    (while mode-alist
      (when (eq (cdar mode-alist) 'verilog-mode)
        (speedbar-add-supported-extension (caar mode-alist)))
      (setq mode-alist (cdr mode-alist)))))

;; If the speedbar is loaded, execute initialization instructions right away,
;; otherwise add the initialization instructions to the speedbar loader.
(eval-after-load "speedbar" '(verilog-speedbar-initialize))


;;; Electric functions:
;;

(defun electric-verilog-terminate-line (&optional arg)
  "Terminate line and indent next line.
With optional ARG, remove existing end of line comments."
  (interactive)
  ;; before that see if we are in a comment
  (let ((state (save-excursion (verilog-syntax-ppss))))
    (cond
     ((nth 7 state)			; Inside // comment
      (if (eolp)
	  (progn
	    (delete-horizontal-space)
	    (newline))
	(progn
	  (newline)
	  (insert "// ")
	  (beginning-of-line)))
      (verilog-indent-line))
     ((nth 4 state)			; Inside any comment (hence /**/)
      (newline)
      (verilog-more-comment))
     ((eolp)
      ;; First, check if current line should be indented
      (if (save-excursion
            (delete-horizontal-space)
            (beginning-of-line)
            (skip-chars-forward " \t")
            (if (looking-at verilog-auto-end-comment-lines-re)
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
                't)))
          ;; see if we should line up assignments
          (progn
            (if (or (eq 'all verilog-auto-lineup)
                    (eq 'assignments verilog-auto-lineup))
                (verilog-pretty-expr :quiet))
            (newline))
        (forward-line 1))
      ;; Indent next line
      (if verilog-auto-indent-on-newline
          (verilog-indent-line)))
     (t
      (newline)))))

(defun electric-verilog-terminate-and-indent ()
  "Insert a newline and indent for the next statement."
  (interactive)
  (electric-verilog-terminate-line 1))

(defun electric-verilog-semi ()
  "Insert `;' character and reindent the line."
  (interactive)
  (verilog-insert-last-command-event)

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
  (insert ";")
  (save-excursion
    (beginning-of-line)
    (verilog-indent-line))
  (indent-for-comment))

(defun electric-verilog-colon ()
  "Insert `:' and do all indentations except line indent on this line."
  (interactive)
  (verilog-insert-last-command-event)
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
    ;; (let ((verilog-tab-always-indent nil))
    ;;   (verilog-indent-line))
    ))

;;(defun electric-verilog-equal ()
;;  "Insert `=', and do indentation if within block."
;;  (interactive)
;;  (verilog-insert-last-command-event)
;; Could auto line up expressions, but not yet
;;  (if (eq (car (verilog-calculate-indent)) 'block)
;;      (let ((verilog-tab-always-indent nil))
;;	(verilog-indent-command)))
;;  )

(defun electric-verilog-tick ()
  "Insert back-tick, and indent to column 0 if this is a CPP directive."
  (interactive)
  (verilog-insert-last-command-event)
  (save-excursion
    (if (verilog-in-directive-p)
        (verilog-indent-line))))

(defun electric-verilog-tab ()
  "Function called when TAB is pressed in Verilog mode."
  (interactive)
  ;; If verilog-tab-always-indent, indent the beginning of the line.
  (cond
   ;; The region is active, indent it.
   ((and (region-active-p)
	 (not (eq (region-beginning) (region-end))))
    (indent-region (region-beginning) (region-end) nil))
   ((or verilog-tab-always-indent
	(save-excursion
	  (skip-chars-backward " \t")
	  (bolp)))
    (let* ((oldpnt (point))
	   (boi-point
	    (save-excursion
	      (beginning-of-line)
	      (skip-chars-forward " \t")
	      (verilog-indent-line)
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
                 ;; kill existing comment
		 (beginning-of-line)
		 (re-search-forward comment-start-skip oldpnt 'move)
		 (goto-char (match-beginning 0))
		 (skip-chars-backward " \t")
		 (kill-region (point) oldpnt)))))))
   (t (progn (insert "\t")))))


;;; Interactive functions:
;;

(defun verilog-indent-buffer ()
  "Indent-region the entire buffer as Verilog code.
To call this from the command line, see \\[verilog-batch-indent]."
  (interactive)
  (verilog-mode)
  (verilog-auto-reeval-locals)
  (indent-region (point-min) (point-max) nil))

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

(defun verilog-insert-1 (fmt max)
  "Use format string FMT to insert integers 0 to MAX - 1.
Inserts one integer per line, at the current column.  Stops early
if it reaches the end of the buffer."
  (let ((col (current-column))
        (n 0))
    (save-excursion
      (while (< n max)
        (insert (format fmt n))
        (forward-line 1)
        ;; Note that this function does not bother to check for lines
        ;; shorter than col.
        (if (eobp)
            (setq n max)
          (setq n (1+ n))
          (move-to-column col))))))

(defun verilog-insert-indices (max)
  "Insert a set of indices into a rectangle.
The upper left corner is defined by point.  Indices begin with 0
and extend to the MAX - 1.  If no prefix arg is given, the user
is prompted for a value.  The indices are surrounded by square
brackets [].  For example, the following code with the point
located after the first `a' gives:

    a = b                           a[  0] = b
    a = b                           a[  1] = b
    a = b                           a[  2] = b
    a = b                           a[  3] = b
    a = b   ==> insert-indices ==>  a[  4] = b
    a = b                           a[  5] = b
    a = b                           a[  6] = b
    a = b                           a[  7] = b
    a = b                           a[  8] = b"

  (interactive "NMAX: ")
  (verilog-insert-1 "[%3d]" max))

(defun verilog-generate-numbers (max)
  "Insert a set of generated numbers into a rectangle.
The upper left corner is defined by point.  The numbers are padded to three
digits, starting with 000 and extending to (MAX - 1).  If no prefix argument
is supplied, then the user is prompted for the MAX number.  Consider the
following code fragment:

    buf buf                             buf buf000
    buf buf                             buf buf001
    buf buf                             buf buf002
    buf buf                             buf buf003
    buf buf   ==> generate-numbers ==>  buf buf004
    buf buf                             buf buf005
    buf buf                             buf buf006
    buf buf                             buf buf007
    buf buf                             buf buf008"

  (interactive "NMAX: ")
  (verilog-insert-1 "%3.3d" max))

(defun verilog-mark-defun ()
  "Mark the current Verilog function (or procedure).
This puts the mark at the end, and point at the beginning."
  (interactive)
  (let (found)
    (if (featurep 'xemacs)
        (progn
          (push-mark)
          (verilog-end-of-defun)
          (push-mark)
          (verilog-beg-of-defun)
          (if (fboundp 'zmacs-activate-region)
              (zmacs-activate-region)))
      ;; GNU Emacs
      (when (verilog-beg-of-defun)
        (setq found (point))
        (verilog-end-of-defun)
        (end-of-line)
        (push-mark)
        (goto-char found)
        (beginning-of-line)
        (setq mark-active t)))))

(defun verilog-comment-region (start end)
  ;; checkdoc-params: (start end)
  "Put the region into a Verilog comment.
The comments that are in this area are \"deformed\":
`*)' becomes `!(*' and `}' becomes `!{'.
These deformed comments are returned to normal if you use
\\[verilog-uncomment-region] to undo the commenting.

The commented area starts with `verilog-exclude-str-start', and ends with
`verilog-exclude-str-end'.  But if you change these variables,
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
	  (replace-match "/-*" t t))))))

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
	  ;; Remove start comment
	  (goto-char start)
	  (beginning-of-line)
	  (let ((pos (point)))
	    (end-of-line)
	    (delete-region pos (1+ (point)))))))))

(defun verilog-beg-of-defun ()
  "Move backward to the beginning of the current function or procedure."
  (interactive)
  (let (found)
    (save-excursion
      (when (verilog-looking-back verilog-defun-tf-re-end (point-at-bol))
        (verilog-backward-sexp)
        (setq found (point)))
      (while (and (not found)
                  (verilog-re-search-backward verilog-defun-tf-re-all nil t))
        (cond ((verilog-looking-back "\\(\\<typedef\\>\\s-+\\)" (point-at-bol)) ; corner case, e.g. 'typedef class <id>;'
               (backward-word))
              ((looking-at verilog-defun-tf-re-end)
               (verilog-backward-sexp))
              ((looking-at verilog-defun-tf-re-beg)
               (setq found (point))))))
    (when found
      (goto-char found))))

(defun verilog-beg-of-defun-quick ()
  "Move backward to the beginning of the current function or procedure.
Uses `verilog-scan' cache."
  (interactive)
  (verilog-re-search-backward-quick verilog-defun-re nil 'move))

(defun verilog-end-of-defun ()
  "Move forward to the end of the current function or procedure."
  (interactive)
  (when (or (looking-at verilog-defun-tf-re-beg)
            (verilog-beg-of-defun))
    (verilog-forward-sexp)
    (point)))

(defun verilog-get-end-of-defun ()
  (save-excursion
    (cond ((verilog-re-search-forward-quick verilog-end-defun-re nil t)
	   (point))
	  (t
	   (error "%s: Can't find endmodule" (verilog-point-text))
	   (point-max)))))

(defun verilog-label-be ()
  "Label matching begin ... end, fork ... join and case ... endcase statements."
  (interactive)
  (let ((cnt 0)
	(case-fold-search nil)
	(oldpos (point))
	(b (progn
	     (verilog-re-search-backward verilog-defun-re nil 'move)
	     (point-marker)))
	(e (progn
	     (verilog-re-search-forward verilog-end-defun-re nil 'move)
	     (point-marker))))
    (goto-char (marker-position b))
    (if (> (- e b) 200)
	(message "Relabeling module..."))
    (while (and
	    (> (marker-position e) (point))
	    (verilog-re-search-forward
	     verilog-auto-end-comment-lines-re
	     nil 'move))
      (goto-char (match-beginning 0))
      (let ((indent-str (verilog-indent-line)))
	(verilog-set-auto-endcomments indent-str 't)
	(end-of-line)
	(delete-horizontal-space))
      (setq cnt (1+ cnt))
      (if (= 9 (% cnt 10))
	  (message "%d..." cnt)))
    (goto-char oldpos)
    (if (or
	 (> (- e b) 200)
	 (> cnt 20))
	(message "%d lines auto commented" cnt))))

(defun verilog-beg-of-statement ()
  "Move backward to beginning of statement."
  (interactive)
  ;; Move back token by token until we see the end
  ;; of some earlier line.
  (let (h)
    (while
	;; If the current point does not begin a new
	;; statement, as in the character ahead of us is a ';', or SOF
	;; or the string after us unambiguously starts a statement,
	;; or the token before us unambiguously ends a statement,
	;; then move back a token and test again.
	(not (or
	      ;; stop if beginning of buffer
	      (bobp)
	      ;; stop if looking at a pre-processor directive
	      (looking-at "`\\w+")
	      ;; stop if we find a ;
	      (= (preceding-char) ?\;)
	      ;; stop if we see a named coverpoint
	      (looking-at "\\w+\\W*:\\W*\\(coverpoint\\|cross\\|constraint\\)")
	      ;; keep going if we are in the middle of a word
	      (not (or (looking-at "\\<") (forward-word-strictly -1)))
	      ;; stop if we see an assertion (perhaps labeled)
	      (and
	       (looking-at (concat "\\(\\w+\\W*:\\W*\\)?" verilog-concurrent-assertion-statement-re))
	       (progn
		 (setq h (point))
		 (save-excursion
		   (verilog-backward-token)
		   (if (and (looking-at verilog-label-re)
		            (not (looking-at verilog-end-block-re)))
		       (setq h (point))))
		 (goto-char h)))
	      ;; stop if we see an extended complete reg, perhaps a complete one
	      (and
	       (looking-at verilog-complete-re)
	       (let* ((p (point)))
		 (while (and (looking-at verilog-extended-complete-re)
			     (progn (setq p (point))
				    (verilog-backward-token)
				    (/= p (point)))))
		 (goto-char p)))
	      ;; stop if previous token is an ender
	      (save-excursion
		(verilog-backward-token)
		(or (looking-at verilog-end-block-re)
                    (verilog-in-directive-p)))))
      (verilog-backward-syntactic-ws)
      (verilog-backward-token))
    ;; Now point is where the previous line ended.
    (verilog-forward-syntactic-ws)
    ;; Skip forward over any preprocessor directives, as they have wacky indentation
    (if (looking-at verilog-preprocessor-re)
	(progn (goto-char (match-end 0))
	       (verilog-forward-syntactic-ws)))))

(defun verilog-beg-of-statement-1 ()
  "Move backward to beginning of statement."
  (interactive)
  (if (verilog-in-comment-p)
      (verilog-backward-syntactic-ws))
  (let ((pt (point)))
    (catch 'done
      (while (not (looking-at verilog-complete-re))
        (setq pt (point))
        (verilog-backward-syntactic-ws)
        (if (or (bolp)
                (= (preceding-char) ?\;)
                (and (= (preceding-char) ?\{)
                     (save-excursion
                       (backward-char)
                       (verilog-at-struct-p)))
		(progn
		  (verilog-backward-token)
                  (or (looking-at verilog-ends-re)
                      (looking-at "begin"))))
            (progn
              (goto-char pt)
              (throw 'done t)))))
    (verilog-forward-syntactic-ws)))

(defun verilog-end-of-statement ()
  "Move forward to end of current statement."
  (interactive)
  (let ((nest 0) pos)
    (cond
     ((verilog-in-directive-p)
      (forward-line 1)
      (backward-char 1))

     ((looking-at verilog-beg-block-re)
      (verilog-forward-sexp))

     ((equal (char-after) ?\})
      (forward-char))

     ;; Skip to end of statement
     ((condition-case nil
          (setq pos
                (catch 'found
                  (while t
                    (forward-sexp 1)
                    (verilog-skip-forward-comment-or-string)
                    (if (eolp)
                        (forward-line 1))
                    (cond ((looking-at "[ \t]*;")
                           (skip-chars-forward "^;")
                           (forward-char 1)
                           (throw 'found (point)))
                          ((save-excursion
                             (forward-sexp -1)
                             (looking-at verilog-beg-block-re))
                           (goto-char (match-beginning 0))
                           (throw 'found nil))
                          ((looking-at "[ \t]*)")
                           (throw 'found (point)))
                          ((eobp)
                           (throw 'found (point)))
                          )))

                )
        (error nil))
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
        pos)))))

(defun verilog-in-case-region-p ()
  "Return non-nil if in a case region.
More specifically, point @ in the line foo : @ begin"
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
              (concat "\\(\\<module\\>\\)\\|\\(\\<connectmodule\\>\\)\\|\\(\\<randcase\\>\\|\\<case[xz]?\\>[^:]\\)\\|"
		       "\\(\\<endcase\\>\\)")
	       nil 'move)
	      (cond
              ((match-end 4)
		(setq nest (1+ nest)))
              ((match-end 3)
		(if (= nest 1)
		    (throw 'found 1))
		(setq nest (1- nest)))
	       (t
		(throw 'found (= nest 0)))))))
      nil)))

(defun verilog-backward-up-list (arg)
  "Call `backward-up-list' ARG, ignoring comments and errors."
  (let ((parse-sexp-ignore-comments t))
    (condition-case nil
        (backward-up-list arg)  ;; May throw Unbalanced parenthesis
      (error nil))))

(defun verilog-forward-sexp-cmt (arg)
  "Call `forward-sexp' ARG, inside comments."
  (let ((parse-sexp-ignore-comments nil))
    (forward-sexp arg)))

(defun verilog-forward-sexp-ign-cmt (arg)
  "Call `forward-sexp' ARG, ignoring comments."
  (let ((parse-sexp-ignore-comments t))
    (forward-sexp arg)))

(defun verilog-in-generate-region-p ()
  "Return non-nil if in a generate region.
More specifically, after a generate and before an endgenerate."
  (interactive)
  (let ((nest 1))
    (save-excursion
      (catch 'done
	(while (and
		(/= nest 0)
		(verilog-re-search-backward
                 "\\<\\(?:\\(module\\)\\|\\(connectmodule\\)\\|\\(endmodule\\)\\|\\(generate\\)\\|\\(endgenerate\\)\\|\\(if\\)\\|\\(case\\)\\|\\(for\\)\\)\\>" nil 'move)
		(cond
		 ((match-end 1) ; module - we have crawled out
		  (throw 'done 1))
                 ((match-end 2) ; connectmodule - we have crawled out
                  (throw 'done 1))
                 ((match-end 3) ; endmodule - we were outside of module block
                  (throw 'done -1))
                 ((match-end 4) ; generate
		  (setq nest (1- nest)))
                 ((match-end 5) ; endgenerate
                  (setq nest (1+ nest)))
                 ((match-end 6) ; if
                  (setq nest (1- nest)))
                 ((match-end 7) ; case
                  (setq nest (1- nest)))
                 ((match-end 8) ; for
                  (setq nest (1- nest))))))))
    (= nest 0) )) ; return nest

(defun verilog-in-fork-region-p ()
  "Return non-nil if between a fork and join."
  (interactive)
  (let ((lim (save-excursion (verilog-re-search-backward verilog-defun-re nil 'move)  (point)))
	(nest 1))
    (save-excursion
      (while (and
	      (/= nest 0)
	      (verilog-re-search-backward "\\<\\(?:\\(fork\\)\\|\\(join\\(_any\\|_none\\)?\\)\\)\\>" lim 'move)
	      (cond
	       ((match-end 1) ; fork
		(setq nest (1- nest)))
	       ((match-end 2) ; join
		(setq nest (1+ nest)))))))
    (= nest 0) )) ; return nest

(defun verilog-in-deferred-immediate-final-p ()
  "Return non-nil if inside an `assert/assume/cover final' statement."
  (interactive)
  (and (looking-at "final")
       (verilog-looking-back "\\<\\(?:assert\\|assume\\|cover\\)\\>\\s-+" nil))
  )

(defun verilog-backward-case-item (lim)
  "Skip backward to nearest enclosing case item.
Limit search to point LIM."
  (interactive)
  (let ((str 'nil)
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
             ((match-end 1)  ; [
	      (setq colon (1+ colon))
	      (if (>= colon 0)
                  (error "%s: Unbalanced [" (verilog-point-text))))
             ((match-end 2)  ; ]
	      (setq colon (1- colon)))

             ((match-end 3)  ; :
	      (setq colon (1+ colon)))))
	  ;; Skip back to beginning of case item
	  (skip-chars-backward "\t ")
	  (verilog-skip-backward-comment-or-string)
	  (setq e (point))
	  (setq b
		(progn
		  (if
		      (verilog-re-search-backward
		       "\\<\\(randcase\\|case[zx]?\\)\\>\\|;\\|\\<end\\>" nil 'move)
		      (progn
			(cond
			 ((match-end 1)
			  (goto-char (match-end 1))
			  (verilog-forward-ws&directives)
			  (if (looking-at "(")
			      (progn
				(forward-sexp)
				(verilog-forward-ws&directives)))
			  (point))
			 (t
			  (goto-char (match-end 0))
			  (verilog-forward-ws&directives)
			  (point))))
		    (error "Malformed case item"))))
	  (setq str (buffer-substring b e))
	  (if
	      (setq e
		    (string-match
		     "[ \t]*\\(\\(\n\\)\\|\\(//\\)\\|\\(/\\*\\)\\)" str))
	      (setq str (concat (substring str 0 e) "...")))
	  str)
      'nil)))

;;; Other functions:
;;

(defun verilog-kill-existing-comment ()
  "Kill auto comment on this line."
  (save-excursion
    (let* (
	   (e (progn
		(end-of-line)
		(point)))
	   (b (progn
		(beginning-of-line)
		(search-forward "//" e t))))
      (if b
	  (delete-region (- b 2) e)))))

(defconst verilog-directive-nest-re
  (concat "\\(`else\\>\\)\\|"
	  "\\(`endif\\>\\)\\|"
	  "\\(`if\\>\\)\\|"
	  "\\(`ifdef\\>\\)\\|"
	  "\\(`ifndef\\>\\)\\|"
	  "\\(`elsif\\>\\)"))

(defun verilog-set-auto-endcomments (indent-str kill-existing-comment)
  "Add ending comment with given INDENT-STR.
With KILL-EXISTING-COMMENT, remove what was there before.
Insert `// case: 7 ' or `// NAME ' on this line if appropriate.
Insert `// case expr ' if this line ends a case block.
Insert `// ifdef FOO ' if this line ends code conditional on FOO.
Insert `// NAME ' if this line ends a function, task, module,
primitive or interface named NAME."
  (save-excursion
    (cond
     (; Comment close preprocessor directives
      (and
       (looking-at "\\(`endif\\)\\|\\(`else\\)")
       (or  kill-existing-comment
	    (not (save-excursion
		   (end-of-line)
                   (search-backward "//" (line-beginning-position) t)))))
      (let ((nest 1) b e
	    m
	    (else (if (match-end 2) "!" " ")))
	(end-of-line)
	(if kill-existing-comment
	    (verilog-kill-existing-comment))
	(delete-horizontal-space)
	(save-excursion
	  (backward-sexp 1)
	  (while (and (/= nest 0)
		      (verilog-re-search-backward verilog-directive-nest-re nil 'move))
	    (cond
	     ((match-end 1) ; `else
	      (if (= nest 1)
		  (setq else "!")))
	     ((match-end 2) ; `endif
	      (setq nest (1+ nest)))
	     ((match-end 3) ; `if
	      (setq nest (1- nest)))
	     ((match-end 4) ; `ifdef
	      (setq nest (1- nest)))
	     ((match-end 5) ; `ifndef
	      (setq nest (1- nest)))
	     ((match-end 6) ; `elsif
	      (if (= nest 1)
		  (progn
		    (setq else "!")
		    (setq nest 0))))))
	  (if (match-end 0)
	      (setq
	       m (buffer-substring
		  (match-beginning 0)
		  (match-end 0))
	       b (progn
		   (skip-chars-forward "^ \t")
		   (verilog-forward-syntactic-ws)
		   (point))
	       e (progn
		   (skip-chars-forward "a-zA-Z0-9_")
		   (point)))))
	(if b
	    (if (> (count-lines (point) b) verilog-minimum-comment-distance)
		(insert (concat " // " else m " " (buffer-substring b e))))
	  (progn
	    (insert " // unmatched `else, `elsif or `endif")
	    (ding 't)))))

     (; Comment close case/class/function/task/module and named block
      (and (looking-at "\\<end")
	   (or kill-existing-comment
	       (not (save-excursion
		      (end-of-line)
                      (search-backward "//" (line-beginning-position) t)))))
      (let ((type (car indent-str)))
	(unless (eq type 'declaration)
          (unless (looking-at (concat "\\(" verilog-end-block-ordered-re "\\)[ \t]*:"))  ; ignore named ends
	    (if (looking-at verilog-end-block-ordered-re)
                (cond
                 (;- This is a case block; search back for the start of this case
                  (match-end 1)  ; of verilog-end-block-ordered-re

                  (let ((err 't)
                        (str "UNMATCHED!!"))
                    (save-excursion
                      (verilog-leap-to-head)
                      (cond
                       ((looking-at "\\<randcase\\>")
                        (setq str "randcase")
                        (setq err nil))
                       ((looking-at "\\(\\(unique0?\\s-+\\|priority\\s-+\\)?case[xz]?\\)")
                        (goto-char (match-end 0))
                        (setq str (concat (match-string 0) " " (verilog-get-expr)))
                        (setq err nil))
                       ))
                    (end-of-line)
                    (if kill-existing-comment
                        (verilog-kill-existing-comment))
                    (delete-horizontal-space)
                    (insert (concat " // " str ))
                    (if err (ding 't))))

                 (;- This is a begin..end block
                  (match-end 2)  ; of verilog-end-block-ordered-re
                  (let ((str " // UNMATCHED !!")
                        (err 't)
                        (here (point))
                        there
                        cntx)
                    (save-excursion
                      (verilog-leap-to-head)
                      (setq there (point))
                      (if (not (match-end 0))
                          (progn
                            (goto-char here)
                            (end-of-line)
                            (if kill-existing-comment
                                (verilog-kill-existing-comment))
                            (delete-horizontal-space)
                            (insert str)
                            (ding 't))
                        (let ((lim
                               (save-excursion (verilog-re-search-backward verilog-defun-re nil 'move) (point)))
                              (here (point)))
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
                            (setq str (concat " // case: " str )))

                           (;- try to find "reason" for this begin
                            (cond
                             (;
                              (eq here (progn
                                         ;;   (verilog-backward-token)
                                         (verilog-beg-of-statement)
                                         (point)))
                              (setq err nil)
                              (setq str ""))
                             ((looking-at verilog-endcomment-reason-re)
                              (setq there (match-end 0))
                              (setq cntx (concat (match-string 0) " "))
                              (cond
                               (;- begin
                                (match-end 1)
                                (setq err nil)
                                (save-excursion
                                  (if (and (verilog-continued-line)
                                           (looking-at "\\<repeat\\>\\|\\<wait\\>\\|\\<always\\>"))
                                      (progn
                                        (goto-char (match-end 0))
                                        (setq there (point))
                                        (setq str
                                              (concat " // " (match-string 0) " " (verilog-get-expr))))
                                    (setq str ""))))

                               (;- else
                                (match-end 2)
                                (let ((nest 0)
                                      ( reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<if\\>\\)\\|\\(assert\\)"))
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
                                              (throw 'skip 1))))
                                       ((match-end 4)
                                        (if (= 0 nest)
                                            (progn
                                              (goto-char (match-end 0))
                                              (setq there (point))
                                              (setq err nil)
                                              (setq str (verilog-get-expr))
                                              (setq str (concat " // else: !assert " str ))
                                              (throw 'skip 1)))))))))
                               (;- end else
                                (match-end 3)
                                (goto-char there)
                                (let ((nest 0)
                                      (reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<if\\>\\)\\|\\(\\<assert\\>\\)"))
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
                                              (throw 'skip 1))))
                                       ((match-end 4)
                                        (if (= 0 nest)
                                            (progn
                                              (goto-char (match-end 0))
                                              (setq there (point))
                                              (setq err nil)
                                              (setq str (verilog-get-expr))
                                              (setq str (concat " // else: !assert " str ))
                                              (throw 'skip 1)))))))))

                               (; always, always_comb, always_latch w/o @...
                                (or (match-end 5) (match-end 6))
                                (goto-char (match-end 0))
                                (setq there (point))
                                (setq err nil)
                                (setq str (concat " // " cntx )))

                               (;- task/function/initial et cetera
                                t
                                (goto-char (match-end 0))
                                (setq there (point))
                                (setq err nil)
                                (setq str (concat " // " cntx (verilog-get-expr))))))

                             ((and
                               (verilog-in-case-region-p) ;-- handle case item differently
                               (progn
                                 (setq there (point))
                                 (goto-char here)
                                 (setq str (verilog-backward-case-item lim))))
                              (setq err nil)
                              (setq str (concat " // case: " str )))

                             ((verilog-in-fork-region-p)
                              (setq err nil)
                              (setq str " // fork branch" ))

                             ((looking-at "\\<end\\>")
                              ;; HERE
                              (forward-word-strictly 1)
                              (verilog-forward-syntactic-ws)
                              (setq err nil)
                              (setq str (verilog-get-expr))
                              (setq str (concat " // " cntx str )))

                             ))))
                        (goto-char here)
                        (end-of-line)
                        (if kill-existing-comment
                            (verilog-kill-existing-comment))
                        (delete-horizontal-space)
                        (if (or err
                                (> (count-lines here there) verilog-minimum-comment-distance))
                            (insert str))
                        (if err (ding 't))
                        ))))
                 (;- this is endclass, which can be nested
                  (match-end 11)  ; of verilog-end-block-ordered-re
                  ;;(goto-char there)
                  (let ((nest 0)
                        (reg "\\<\\(\\(class\\)\\|\\(endclass\\)\\|\\(package\\|primitive\\|\\(macro\\)?module\\)\\)\\>")
                        string)
                    (save-excursion
                      (catch 'skip
                        (while (verilog-re-search-backward reg nil 'move)
                          (cond
                           ((match-end 4)       ; endclass
                            (ding 't)
                            (setq string "unmatched endclass")
                            (throw 'skip 1))

                           ((match-end 3)       ; endclass
                            (setq nest (1+ nest)))

                           ((match-end 2) ; class
                            (setq nest (1- nest))
                            (if (< nest 0)
                                (progn
                                  (goto-char (match-end 0))
                                  (let (b e)
                                    (setq b (progn
                                              (skip-chars-forward "^ \t")
                                              (verilog-forward-ws&directives)
                                              (point))
                                          e (progn
                                              (skip-chars-forward "a-zA-Z0-9_")
                                              (point)))
                                    (setq string (buffer-substring b e)))
                                  (throw 'skip 1))))
                           ))))
                    (end-of-line)
                    (if kill-existing-comment
                        (verilog-kill-existing-comment))
                    (delete-horizontal-space)
                    (insert (concat " // " string ))))

                 (;  - this is end{function,generate,task,module,primitive,table,generate}
                  ;; - which can not be nested.
                  t
                  (let (string reg (name-re nil))
                    (end-of-line)
                    (if kill-existing-comment
                        (save-match-data
                          (verilog-kill-existing-comment)))
                    (delete-horizontal-space)
                    (backward-sexp)
                    (cond
                     ((match-end 5)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<function\\>\\)\\|\\(\\<\\(endfunction\\|task\\|\\(macro\\)?module\\|primitive\\)\\>\\)")
                      (setq name-re "\\w+\\(?:\n\\|\\s-\\)*[(;]"))
                     ((match-end 6)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<task\\>\\)\\|\\(\\<\\(endtask\\|function\\|\\(macro\\)?module\\|primitive\\)\\>\\)")
                      (setq name-re "\\w+\\(?:\n\\|\\s-\\)*[(;]"))
                     ((match-end 7)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<\\(macro\\)?module\\>\\)\\|\\<endmodule\\>"))
                     ((match-end 8)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<primitive\\>\\)\\|\\(\\<\\(endprimitive\\|package\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
                     ((match-end 9)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<interface\\>\\)\\|\\(\\<\\(endinterface\\|package\\|primitive\\|\\(macro\\)?module\\)\\>\\)"))
                     ((match-end 10)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<package\\>\\)\\|\\(\\<\\(endpackage\\|primitive\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
                     ((match-end 11)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<class\\>\\)\\|\\(\\<\\(endclass\\|primitive\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
                     ((match-end 12)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<covergroup\\>\\)\\|\\(\\<\\(endcovergroup\\|primitive\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
                     ((match-end 13)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<program\\>\\)\\|\\(\\<\\(endprogram\\|primitive\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
                     ((match-end 14)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<\\(rand\\)?sequence\\>\\)\\|\\(\\<\\(endsequence\\|primitive\\|interface\\|\\(macro\\)?module\\)\\>\\)"))
                     ((match-end 15)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<clocking\\>\\)\\|\\<endclocking\\>"))
                     ((match-end 16)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<property\\>\\)\\|\\<endproperty\\>"))
                     ((match-end 17)  ; of verilog-end-block-ordered-re
                      (setq reg "\\(\\<connectmodule\\>\\)\\|\\<endconnectmodule\\>"))

                     (t (error "Problem in verilog-set-auto-endcomments")))
                    (let (b e)
                      (save-excursion
                        (verilog-re-search-backward reg nil 'move)
                        (cond
                         ((match-end 1)
                          (setq b (progn
                                    (skip-chars-forward "^ \t")
                                    (verilog-forward-ws&directives)
                                    (if (looking-at "static\\|automatic")
                                        (progn
                                          (goto-char (match-end 0))
                                          (verilog-forward-ws&directives)))
                                    (if (and name-re (verilog-re-search-forward name-re nil 'move))
                                        (progn
                                          (goto-char (match-beginning 0))
                                          (verilog-forward-ws&directives)))
                                    (point))
                                e (progn
                                    (skip-chars-forward "a-zA-Z0-9_")
                                    (point)))
                          (setq string (buffer-substring b e)))
                         (t
                          (ding 't)
                          (setq string "unmatched end(function|task|module|connectmodule|primitive|interface|package|class|clocking)")))))
                    (end-of-line)
                    (insert (concat " // " string )))
                  ))))))))))

(defun verilog-get-expr()
  "Grab expression at point, e.g., case ( a | b & (c ^d))."
  (let* ((b (progn
	      (verilog-forward-syntactic-ws)
	      (skip-chars-forward " \t")
	      (point)))
	 (e (let ((par 1))
	      (cond
	       ((looking-at "@")
		(forward-char 1)
		(verilog-forward-syntactic-ws)
		(if (looking-at "(")
		    (progn
		      (forward-char 1)
		      (while (and (/= par 0)
				  (verilog-re-search-forward "\\((\\)\\|\\()\\)" nil 'move))
			(cond
			 ((match-end 1)
			  (setq par (1+ par)))
			 ((match-end 2)
			  (setq par (1- par)))))))
		(point))
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
		(skip-chars-forward "^ \t\n\f")
		(point))
	       ((looking-at "/[/\\*]")
		b)
	       ('t
		(skip-chars-forward "^: \t\n\f")
		(point)))))
	 (str (buffer-substring b e)))
    (if (setq e (string-match "[ \t]*\\(\\(\n\\)\\|\\(//\\)\\|\\(/\\*\\)\\)" str))
	(setq str (concat (substring str 0 e) "...")))
    str))

(defun verilog-expand-vector ()
  "Take a signal vector on the current line and expand it to multiple lines.
Useful for creating tri's and other expanded fields."
  (interactive)
  (verilog-expand-vector-internal "[" "]"))

(defun verilog-expand-vector-internal (bra ket)
  "Given start brace BRA, and end brace KET, expand one line into many lines."
  (save-excursion
    (forward-line 0)
    (let ((signal-string (buffer-substring (point)
					   (progn
					     (end-of-line) (point)))))
      (if (string-match
	   (concat "\\(.*\\)"
		   (regexp-quote bra)
		   "\\([0-9]*\\)\\(:[0-9]*\\|\\)\\(::[0-9---]*\\|\\)"
		   (regexp-quote ket)
		   "\\(.*\\)$") signal-string)
	  (let* ((sig-head (match-string 1 signal-string))
		 (vec-start (string-to-number (match-string 2 signal-string)))
		 (vec-end (if (= (match-beginning 3) (match-end 3))
			      vec-start
			    (string-to-number
			     (substring signal-string (1+ (match-beginning 3))
					(match-end 3)))))
		 (vec-range
		  (if (= (match-beginning 4) (match-end 4))
		      1
		    (string-to-number
		     (substring signal-string (+ 2 (match-beginning 4))
				(match-end 4)))))
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
	      (insert (concat sig-head bra
			      (int-to-string (car vec)) ket sig-tail "\n"))
	      (setq vec (cdr vec)))
	    (delete-char -1)
	    ;;
	    )))))

(defun verilog-strip-comments ()
  "Strip all comments from the Verilog code."
  (interactive)
  (goto-char (point-min))
  (while (re-search-forward "//" nil t)
    (if (verilog-within-string)
	(re-search-forward "\"" nil t)
      (if (verilog-in-star-comment-p)
	  (re-search-forward "\\*/" nil t)
	(let ((bpt (- (point) 2)))
	  (end-of-line)
	  (delete-region bpt (point))))))
  ;;
  (goto-char (point-min))
  (while (re-search-forward "/\\*" nil t)
    (if (verilog-within-string)
	(re-search-forward "\"" nil t)
      (let ((bpt (- (point) 2)))
	(re-search-forward "\\*/")
	(delete-region bpt (point))))))

(defun verilog-one-line ()
  "Convert structural Verilog instances to occupy one line."
  (interactive)
  (goto-char (point-min))
  (while (re-search-forward "\\([^;]\\)[ \t]*\n[ \t]*" nil t)
    (replace-match "\\1 " nil nil)))

(defun verilog-linter-name ()
  "Return name of linter, either surelint or verilint."
  (let ((compile-word1 (verilog-string-replace-matches "\\s .*$" "" nil nil
						       compile-command))
	(lint-word1    (verilog-string-replace-matches "\\s .*$" "" nil nil
						       verilog-linter)))
    (cond ((equal compile-word1 "surelint") 'surelint)
	  ((equal compile-word1 "verilint") 'verilint)
	  ((equal lint-word1 "surelint")    'surelint)
	  ((equal lint-word1 "verilint")    'verilint)
          (t 'surelint))))  ; back compatibility

(defun verilog-lint-off ()
  "Convert a Verilog linter warning line into a disable statement.
For example:
        pci_bfm_null.v, line  46: Unused input: pci_rst_
becomes a comment for the appropriate tool.

The first word of the `compile-command' or `verilog-linter'
variables is used to determine which product is being used.

See \\[verilog-surelint-off] and \\[verilog-verilint-off]."
  (interactive)
  (let ((linter (verilog-linter-name)))
    (cond ((equal linter 'surelint)
	   (verilog-surelint-off))
	  ((equal linter 'verilint)
	   (verilog-verilint-off))
	  (t (error "Linter name not set")))))

(defvar compilation-last-buffer)
(defvar next-error-last-buffer)

(defun verilog-surelint-off ()
  "Convert a SureLint warning line into a disable statement.
Run from Verilog source window; assumes there is a *compile* buffer
with point set appropriately.

For example:
        WARNING [STD-UDDONX]: xx.v, line 8: output out is never assigned.
becomes:
        // surefire lint_line_off UDDONX"
  (interactive)
  (let ((buff (if (boundp 'next-error-last-buffer)  ; Added to Emacs-22.1
                  next-error-last-buffer
                (verilog--suppressed-warnings
                    ((obsolete compilation-last-buffer))
                  compilation-last-buffer))))
    (when (buffer-live-p buff)
      (save-excursion
        (switch-to-buffer buff)
        (beginning-of-line)
        (when
            (looking-at "\\(INFO\\|WARNING\\|ERROR\\) \\[[^-]+-\\([^]]+\\)\\]: \\([^,]+\\), line \\([0-9]+\\): \\(.*\\)$")
          (let* ((code (match-string 2))
                 (file (match-string 3))
                 (line (match-string 4))
                 (buffer (get-file-buffer file)))
            (unless buffer
              (progn
                (setq buffer
                      (and (file-exists-p file)
                           (find-file-noselect file)))
                (or buffer
                    (let* ((pop-up-windows t))
                      (let ((name (expand-file-name
                                   (read-file-name
                                    ;; `format-prompt' is new in Emacs 28.1.
                                    (if (fboundp 'format-prompt)
                                        (format-prompt "Find this error in" file)
                                      (format "Find this error in (default %s): "
                                              file))
                                    nil ;; dir
                                    file t))))
                        (setq buffer
                              (and (file-exists-p name)
                                   (find-file-noselect name))))))))
            (switch-to-buffer buffer)
            (goto-char (point-min))
            (forward-line (- (string-to-number line)))
            (end-of-line)
            (catch 'already
              (cond
               ((verilog-in-slash-comment-p)
                (re-search-backward "//")
                (cond
                 ((looking-at "// surefire lint_off_line ")
                  (goto-char (match-end 0))
                  (let ((lim (line-end-position)))
                    (if (re-search-forward code lim 'move)
                        (throw 'already t)
                      (insert (concat " " code)))))
                 (t
                  )))
               ((verilog-in-star-comment-p)
                (re-search-backward "/\\*")
                (insert (format " // surefire lint_off_line %6s" code )))
               (t
                (insert (format " // surefire lint_off_line %6s" code ))
                )))))))))

(defun verilog-verilint-off ()
  "Convert a Verilint warning line into a disable statement.

For example:
        (W240)  pci_bfm_null.v, line  46: Unused input: pci_rst_
becomes:
        //Verilint 240 off // WARNING: Unused input"
  (interactive)
  (save-excursion
    (beginning-of-line)
    (when (looking-at "\\(.*\\)([WE]\\([0-9A-Z]+\\)).*,\\s +line\\s +[0-9]+:\\s +\\([^:\n]+\\).*$")
      (replace-match (format
		      ;; %3s makes numbers 1-999 line up nicely
		      "\\1//Verilint %3s off // WARNING: \\3"
		      (match-string 2)))
      (beginning-of-line)
      (verilog-indent-line))))

(defun verilog-auto-save-compile ()
  "Update automatics with \\[verilog-auto], save the buffer, and compile."
  (interactive)
  (verilog-auto)	; Always do it for safety
  (save-buffer)
  (compile compile-command))

(defun verilog-preprocess (&optional command filename)
  "Preprocess the buffer, similar to `compile', but put output in Verilog-Mode.
Takes optional COMMAND or defaults to `verilog-preprocessor', and
FILENAME to find directory to run in, or defaults to `buffer-file-name'."
  (interactive
   (list
    (let ((default (verilog-expand-command verilog-preprocessor)))
      (set (make-local-variable 'verilog-preprocessor)
	   (read-from-minibuffer "Run Preprocessor (like this): "
				 default nil nil
				 'verilog-preprocess-history default)))))
  (unless command (setq command (verilog-expand-command verilog-preprocessor)))
  (let* ((fontlocked font-lock-mode)
	 (dir (file-name-directory (or filename buffer-file-name)))
	 (cmd (concat "cd " dir "; " command)))
    (with-output-to-temp-buffer "*Verilog-Preprocessed*"
      (with-current-buffer "*Verilog-Preprocessed*"
	(insert (concat "// " cmd "\n"))
	(call-process shell-file-name nil t nil shell-command-switch cmd)
	(verilog-mode)
	;; Without this force, it takes a few idle seconds
	;; to get the color, which is very jarring
        (unless (fboundp 'font-lock-ensure)
          ;; We should use font-lock-ensure in preference to
          ;; font-lock-fontify-buffer, but IIUC the problem this is supposed to
          ;; solve only appears in Emacsen older than font-lock-ensure anyway.
          (when fontlocked
            (verilog--suppressed-warnings
                ((interactive-only font-lock-fontify-buffer))
              (font-lock-fontify-buffer))))))))

;;; Batch:
;;

(defun verilog-warn (string &rest args)
  "Print a warning with `format' using STRING and optional ARGS."
  (apply #'message (concat "%%Warning: " string) args))

(defun verilog-warn-error (string &rest args)
  "Call `error' using STRING and optional ARGS.
If `verilog-warn-fatal' is non-nil, call `verilog-warn' instead."
  (apply (if (and verilog-warn-fatal verilog-warn-fatal-internal)
             #'error #'verilog-warn)
         string args))

(defmacro verilog-batch-error-wrapper (&rest body)
  "Execute BODY and add error prefix to any errors found.
This lets programs calling batch mode to easily extract error messages."
  `(let ((verilog-warn-fatal-internal nil))
     (condition-case err
	 (progn ,@body)
       (error
	(error "%%Error: %s%s" (error-message-string err)
               (if (featurep 'xemacs) "\n" ""))))))  ; XEmacs forgets to add a newline

;; Eliminate compile warning
(defvar verilog-batch-orig-buffer-string)

(defun verilog-batch-execute-func (funref &optional no-save)
  "Internal processing of a batch command.
Runs FUNREF on all command arguments.
Save the result unless optional NO-SAVE is t."
  (verilog-batch-error-wrapper
   ;; Setting global variables like that is *VERY NASTY* !!!  --Stef
   ;; However, this function is called only when Emacs is being used as
   ;; a standalone language instead of as an editor, so we'll live.
   ;;
   ;; General globals needed
   (setq make-backup-files nil)
   (setq-default make-backup-files nil)
   (setq enable-local-variables t)
   (setq enable-local-eval t)
   (setq create-lockfiles nil)
   ;; Make sure any sub-files we read get proper mode
   (setq-default major-mode 'verilog-mode)
   ;; Ditto files already read in
   ;; Remember buffer list, so don't later pickup any verilog-getopt files
   (let ((orig-buffer-list (buffer-list)))
     (mapc (lambda (buf)
             (when (buffer-file-name buf)
               (with-current-buffer buf
                 (set (make-local-variable 'verilog-batch-orig-buffer-string)
                      (buffer-string))
                 (put 'verilog-batch-orig-buffer-string 'permanent-local t)
                 (verilog-mode)
                 (verilog-auto-reeval-locals)
                 (verilog-getopt-flags))))
           orig-buffer-list)
     ;; Process the files
     (mapc (lambda (buf)
             (when (buffer-file-name buf)
               (if (not (file-exists-p (buffer-file-name buf)))
                   (error
                    "File not found: %s" (buffer-file-name buf)))
               (message "Processing %s" (buffer-file-name buf))
               (with-current-buffer buf
                 (funcall funref)
                 (verilog-star-cleanup)
                 (when (and (not no-save)
                            (buffer-modified-p)
                            (not (equal verilog-batch-orig-buffer-string (buffer-string))))
                   (save-buffer)))))
           orig-buffer-list))))

(defun verilog-batch-auto ()
  "For use with --batch, perform automatic expansions as a stand-alone tool.
This sets up the appropriate Verilog mode environment, updates automatics
with \\[verilog-auto] on all command-line files, and saves the buffers.
For proper results, multiple filenames need to be passed on the command
line in bottom-up order."
  (unless noninteractive
    (error "Use verilog-batch-auto only with --batch"))  ; Otherwise we'd mess up buffer modes
  (verilog-batch-execute-func 'verilog-auto))

(defun verilog-batch-delete-auto ()
  "For use with --batch, perform automatic deletion as a stand-alone tool.
This sets up the appropriate Verilog mode environment, deletes automatics
with \\[verilog-delete-auto] on all command-line files, and saves the buffers."
  (unless noninteractive
    (error "Use verilog-batch-delete-auto only with --batch"))  ; Otherwise we'd mess up buffer modes
  (verilog-batch-execute-func 'verilog-delete-auto))

(defun verilog-batch-delete-trailing-whitespace ()
  "For use with --batch, perform whitespace deletion as a stand-alone tool.
This sets up the appropriate Verilog mode environment, removes
whitespace with \\[verilog-delete-trailing-whitespace] on all
command-line files, and saves the buffers."
  (unless noninteractive
    (error "Use verilog-batch-delete-trailing-whitespace only with --batch"))  ; Otherwise we'd mess up buffer modes
  (verilog-batch-execute-func 'verilog-delete-trailing-whitespace))

(defun verilog-batch-diff-auto ()
  "For use with --batch, perform automatic differences as a stand-alone tool.
This sets up the appropriate Verilog mode environment, expand automatics
with \\[verilog-diff-auto] on all command-line files, and reports an error
if any differences are observed.  This is appropriate for adding to regressions
to insure automatics are always properly maintained."
  (unless noninteractive
    (error "Use verilog-batch-diff-auto only with --batch"))  ; Otherwise we'd mess up buffer modes
  (verilog-batch-execute-func 'verilog-diff-auto t))

(defun verilog-batch-inject-auto ()
  "For use with --batch, perform automatic injection as a stand-alone tool.
This sets up the appropriate Verilog mode environment, injects new automatics
with \\[verilog-inject-auto] on all command-line files, and saves the buffers.
For proper results, multiple filenames need to be passed on the command
line in bottom-up order."
  (unless noninteractive
    (error "Use verilog-batch-inject-auto only with --batch"))  ; Otherwise we'd mess up buffer modes
  (verilog-batch-execute-func 'verilog-inject-auto))

(defun verilog-batch-indent ()
  "For use with --batch, reindent an entire file as a stand-alone tool.
This sets up the appropriate Verilog mode environment, calls
\\[verilog-indent-buffer] on all command-line files, and saves the buffers."
  (unless noninteractive
    (error "Use verilog-batch-indent only with --batch"))  ; Otherwise we'd mess up buffer modes
  (verilog-batch-execute-func 'verilog-indent-buffer))

;;; Indentation:
;;
(defconst verilog-indent-alist
  '((block       . (+ ind verilog-indent-level))
    (case        . (+ ind verilog-case-indent))
    (cparenexp   . (+ ind verilog-indent-level))
    (cexp        . (+ ind verilog-cexp-indent))
    (defun       . verilog-indent-level-module)
    (declaration . verilog-indent-level-declaration)
    (directive   . (verilog-calculate-indent-directive))
    (tf          . verilog-indent-level)
    (behavioral  . (+ verilog-indent-level-behavioral verilog-indent-level-module))
    (statement   . ind)
    (cpp         . 0)
    (comment     . (verilog-comment-indent))
    (unknown     . 3)
    (string      . 0)))

(defun verilog-continued-line-1 (lim)
  "Return non-nil if this is a continued line.
Set point to where line starts.  Limit search to point LIM."
  (let ((continued 't))
    (if (eq 0 (forward-line -1))
	(progn
	  (end-of-line)
	  (verilog-backward-ws&directives lim)
	  (if (bobp)
	      (setq continued nil)
	    (setq continued (verilog-backward-token))))
      (setq continued nil))
    continued))

(defun verilog-calculate-indent ()
  "Calculate the indent of the current Verilog line.
Examine previous lines.  Once a line is found that is definitive as to the
type of the current line, return that lines' indent level and its type.
Return a list of two elements: (INDENT-TYPE INDENT-LEVEL)."
  (save-excursion
    (let* ((starting_position (point))
	   (case-fold-search nil)
	   (par 0)
	   (begin (looking-at "[ \t]*begin\\>"))
          (lim (save-excursion (verilog-re-search-backward "\\(\\<begin\\>\\)\\|\\(\\<\\(connect\\)?module\\>\\)" nil t)))
           (structres nil)
	   (type (catch 'nesting
		   ;; Keep working backwards until we can figure out
		   ;; what type of statement this is.
		   ;; Basically we need to figure out
		   ;; 1) if this is a continuation of the previous line;
		   ;; 2) are we in a block scope (begin..end)

		   ;; if we are in a comment, done.
		   (if (verilog-in-star-comment-p)
		       (throw 'nesting 'comment))

		   ;; if we have a directive, done.
		   (if (save-excursion (beginning-of-line)
				       (and (looking-at verilog-directive-re-1)
					    (not (or (looking-at "[ \t]*`[ou]vm_")
						     (looking-at "[ \t]*`vmm_")))))
		       (throw 'nesting 'directive))
                   ;; indent structs as if there were module level
                   (setq structres (verilog-in-struct-nested-p))
                   (cond ((not structres) nil)
                         ;;((and structres (equal (char-after) ?\})) (throw 'nesting 'struct-close))
                         ((> structres 0) (throw 'nesting 'nested-struct))
                         ((= structres 0) (throw 'nesting 'block))
                         (t nil))

                   ;; if we are in a parenthesized list, and the user likes to indent these, return.
                   ;; unless we are in the newfangled coverpoint or constraint blocks
                   (if (and
                        (verilog-in-paren)
                        (not (verilog-in-coverage-p))
                        )
                       (progn (setq par 1)
                              (throw 'nesting 'block)))

                   ;; See if we are continuing a previous line
                   (while t
                     ;; trap out if we crawl off the top of the buffer
                     (if (bobp) (throw 'nesting 'cpp))

                     (if (and (verilog-continued-line-1 lim)
                              (or (not (verilog-in-coverage-p))
                                  (looking-at verilog-in-constraint-re) ))  ; may still get hosed if concat in constraint
                         (let ((sp (point)))
                           (if (and
                                (not (looking-at verilog-complete-re))
                                (verilog-continued-line-1 lim))
                               (progn (goto-char sp)
                                      (throw 'nesting 'cexp))

                             (goto-char sp))
                           (if (and (verilog-in-coverage-p)
                                    (looking-at verilog-in-constraint-re))
                               (progn
                                 (beginning-of-line)
                                 (skip-chars-forward " \t")
                                 (throw 'nesting 'constraint)))
                           (if (and begin
                                    (not verilog-indent-begin-after-if)
                                    (looking-at verilog-no-indent-begin-re))
                               (progn
                                 (beginning-of-line)
                                 (skip-chars-forward " \t")
                                 (throw 'nesting 'statement))
                             (progn
                               (throw 'nesting 'cexp))))
                       ;; not a continued line
                       (goto-char starting_position))

                     (if (looking-at "\\<else\\>")
                         ;; search back for governing if, striding across begin..end pairs
                         ;; appropriately
                         (let ((elsec 1))
                           (while (verilog-re-search-backward verilog-ends-re nil 'move)
                             (cond
                              ((match-end 1) ; else, we're in deep
                               (setq elsec (1+ elsec)))
                              ((match-end 2) ; if
                               (setq elsec (1- elsec))
                               (if (= 0 elsec)
                                   (if verilog-align-ifelse
                                       (throw 'nesting 'statement)
                                     (progn  ; back up to first word on this line
                                       (beginning-of-line)
                                       (verilog-forward-syntactic-ws)
                                       (throw 'nesting 'statement)))))
                              ((match-end 3) ; assert block
                               (setq elsec (1- elsec))
                               (verilog-beg-of-statement)  ; doesn't get to beginning
                               (if (looking-at verilog-property-re)
                                   (throw 'nesting 'statement)  ; We don't need an endproperty for these
                                 (throw 'nesting 'block)	; We still need an endproperty
                                 ))
                              (t ; endblock
                               ;; try to leap back to matching outward block by striding across
                               ;; indent level changing tokens then immediately
                               ;; previous line governs indentation.
                               (let (( reg) (nest 1))
                                 ;;	 verilog-ends =>  else|if|end|join(_any|_none|)|endcase|endclass|endtable|endspecify|endfunction|endtask|endgenerate|endgroup
                                 (cond
                                  ((match-end 4) ; end
                                   ;; Search back for matching begin
                                   (setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" ))
                                  ((match-end 5) ; endcase
                                   ;; Search back for matching case
                                   (setq reg "\\(\\<randcase\\>\\|\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" ))
                                  ((match-end 6) ; endfunction
                                   ;; Search back for matching function
                                   (setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" ))
                                  ((match-end 7) ; endtask
                                   ;; Search back for matching task
                                   (setq reg "\\(\\<task\\>\\)\\|\\(\\<endtask\\>\\)" ))
                                  ((match-end 8) ; endspecify
                                   ;; Search back for matching specify
                                   (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
                                  ((match-end 9) ; endtable
                                   ;; Search back for matching table
                                   (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" ))
                                  ((match-end 10) ; endgenerate
                                   ;; Search back for matching generate
                                   (setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
                                  ((match-end 11) ; joins
                                   ;; Search back for matching fork
                                   (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|none\\)?\\>\\)" ))
                                  ((match-end 12) ; class
                                   ;; Search back for matching class
                                   (setq reg "\\(\\<class\\>\\)\\|\\(\\<endclass\\>\\)" ))
                                  ((match-end 13) ; covergroup
                                   ;; Search back for matching covergroup
                                   (setq reg "\\(\\<covergroup\\>\\)\\|\\(\\<endgroup\\>\\)" )))
                                 (catch 'skip
                                   (while (verilog-re-search-backward reg nil 'move)
                                     (cond
                                      ((match-end 1) ; begin
                                       (setq nest (1- nest))
                                       (if (= 0 nest)
                                           (throw 'skip 1)))
                                      ((match-end 2) ; end
                                       (setq nest (1+ nest)))))
                                   )))))))
                     (throw 'nesting (verilog-calc-1)))
                   )  ; catch nesting
		 ) ; type
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
         ((eq type 'constraint)
          (list 'block (current-column)))
         ((eq type 'nested-struct)
          (list 'block structres))
         (t
          (list type (verilog-current-indent-level))))))))

(defun verilog-wai ()
  "Show matching nesting block for debugging."
  (interactive)
  (save-excursion
    (let* ((type (verilog-calc-1))
	   depth)
      ;; Return type of block and indent level.
      (if (not type)
	  (setq type 'cpp))
      (if (and
	   verilog-indent-lists
	   (not(or (verilog-in-coverage-p)
                   (verilog-in-struct-p)))
	   (verilog-in-paren))
	  (setq depth 1)
	(cond
         ((eq type 'case)
          (setq depth (verilog-case-indent-level)))
         ((eq type 'statement)
          (setq depth (current-column)))
         ((eq type 'defun)
          (setq depth 0))
         (t
          (setq depth (verilog-current-indent-level)))))
      (message "You are at nesting %s depth %d" type depth))))

(defun verilog-calc-1 ()
  (catch 'nesting
    (let ((re (concat "\\({\\|}\\|" verilog-indent-re "\\)"))
          (inconstraint (verilog-in-coverage-p)))
      (while (verilog-re-search-backward re nil 'move)
        (catch 'continue
          (cond
           ((equal (char-after) ?\{)
            ;; block type returned based on outer constraint { or inner
            (if (verilog-at-constraint-p)
                (cond (inconstraint
                       (beginning-of-line nil)
                       (skip-chars-forward " \t")
                       (throw 'nesting 'constraint))
                      (t
                       (throw 'nesting 'statement)))))
           ((equal (char-after) ?\})
            (let (par-pos
                  (there (verilog-at-close-constraint-p)))
              (if there  ; we are at the } that closes a constraint.  Find the { that opens it
                  (progn
                    (if (> (verilog-in-paren-count) 0)
                        (forward-char 1))
                    (setq par-pos (verilog-parenthesis-depth))
                    (cond (par-pos
                           (goto-char par-pos)
                           (forward-char 1))
                          (t
                           (backward-char 1)))))))

           ((looking-at verilog-beg-block-re-ordered)
            (cond
             ((match-end 2)  ; *sigh* could be "unique case" or "priority casex"
              (let ((here (point)))
                (verilog-beg-of-statement)
                (if (looking-at verilog-extended-case-re)
                    (throw 'nesting 'case)
                  (goto-char here)))
              (throw 'nesting 'case))

             ((match-end 4)  ; *sigh* could be "disable fork"
              (let ((here (point)))
                (verilog-beg-of-statement)
                (if (looking-at verilog-disable-fork-re)
                    t ; this is a normal statement
                  (progn ; or is fork, starts a new block
                    (goto-char here)
                    (throw 'nesting 'block)))))

             ((match-end 17)  ; *sigh* might be a clocking declaration
              (let ((here (point)))
                (cond ((verilog-in-paren)
                       t) ; this is a normal statement
                      ((save-excursion
                        (verilog-beg-of-statement)
                        (looking-at verilog-default-clocking-re))
                       t) ; default clocking, normal statement
                      (t
                       (goto-char here) ; or is clocking, starts a new block
                       (throw 'nesting 'block)))))

             ;; if find `ifn?def `else `elsif
             ((or (match-end 20)
                  (match-end 21)
                  (match-end 22))
              (throw 'continue 'foo))

             ((looking-at "\\<\\(?:class\\|struct\\|function\\|task\\)\\>")
              ;; *sigh* These words have an optional prefix:
              ;; extern {virtual|protected}? function a();
              ;; and we don't want to confuse this with
              ;; function a();
              ;; property
              ;; ...
              ;; endfunction
              (verilog-beg-of-statement)
              (cond
               ((looking-at verilog-dpi-import-export-re)
                (throw 'continue 'foo))
               ((or
                 (looking-at "\\<pure\\>\\s-+\\<virtual\\>\\s-+\\(?:\\<\\(local\\|protected\\|static\\)\\>\\s-+\\)?\\<\\(function\\|task\\)\\>\\s-+")
                 ;; Do not throw 'defun for class typedefs like
                 ;;   typedef class foo;
                 (looking-at "\\<typedef\\>\\s-+\\(?:\\<virtual\\>\\s-+\\)?\\<class\\>\\s-+"))
                (throw 'nesting 'statement))
               ((looking-at verilog-beg-block-re-ordered)
                (throw 'nesting 'block))
               (t
                (throw 'nesting 'defun))))

             ;;
             ((looking-at "\\<\\(property\\|sequence\\)\\>")
              ;; *sigh*
              ;;    - {assert|assume|cover|restrict} property (); are complete
              ;;    - cover sequence (); is complete
              ;; and could also be labeled:
              ;;    - foo: assert property
              ;;    - bar: cover sequence
              ;; but:
              ;;    - property ID () ... needs endproperty
              ;;    - sequence ID () ... needs endsequence
              (verilog-beg-of-statement)
              (if (looking-at verilog-property-re)
                  (throw 'continue 'statement) ; We don't need an endproperty for these
                (throw 'nesting 'block)	;We still need an endproperty
                ))

             (t              (throw 'nesting 'block))))

           ((looking-at verilog-end-block-re)
            (verilog-leap-to-head)
            (if (verilog-in-case-region-p)
                (progn
                  (verilog-leap-to-case-head)
                  (if (looking-at verilog-extended-case-re)
                      (throw 'nesting 'case)))))

           ((looking-at verilog-defun-level-re)
            (if (looking-at verilog-defun-level-generate-only-re)
                (if (or (verilog-in-generate-region-p)
                        (verilog-in-deferred-immediate-final-p))
                    (throw 'continue 'foo)  ; always block in a generate - keep looking
                  (throw 'nesting 'defun))
              (throw 'nesting 'defun)))

           ((looking-at verilog-cpp-level-re)
            (throw 'nesting 'cpp))

           ((bobp)
            (throw 'nesting 'cpp)))))

      (throw 'nesting 'cpp))))

(defun verilog-calculate-indent-directive ()
  "Return indentation level for directive.
For speed, the searcher looks at the last directive, not the indent
of the appropriate enclosing block."
  (let ((base -1)  ; Indent of the line that determines our indentation
        (ind 0))   ; Relative offset caused by other directives (like `endif on same line as `else)
    ;; Start at current location, scan back for another directive

    (save-excursion
      (beginning-of-line)
      (while (and (< base 0)
		  (verilog-re-search-backward verilog-directive-re nil t))
	(cond ((save-excursion (skip-chars-backward " \t") (bolp))
	       (setq base (current-indentation))))
        (cond ((and (looking-at verilog-directive-end) (< base 0))  ; Only matters when not at BOL
	       (setq ind (- ind verilog-indent-level-directive)))
              ((and (looking-at verilog-directive-middle) (>= base 0))  ; Only matters when at BOL
	       (setq ind (+ ind verilog-indent-level-directive)))
	      ((looking-at verilog-directive-begin)
	       (setq ind (+ ind verilog-indent-level-directive)))))
      ;; Adjust indent to starting indent of critical line
      (setq ind (max 0 (+ ind base))))

    (save-excursion
      (beginning-of-line)
      (skip-chars-forward " \t")
      (cond ((or (looking-at verilog-directive-middle)
		 (looking-at verilog-directive-end))
	     (setq ind (max 0 (- ind verilog-indent-level-directive))))))
    ind))

(defun verilog-leap-to-case-head ()
  (let ((nest 1))
    (while (/= 0 nest)
      (verilog-re-search-backward
       (concat
	"\\(\\<randcase\\>\\|\\(\\<unique0?\\s-+\\|priority\\s-+\\)?\\<case[xz]?\\>\\)"
	"\\|\\(\\<endcase\\>\\)" )
       nil 'move)
      (cond
       ((match-end 1)
	(let ((here (point)))
	  (verilog-beg-of-statement)
	  (unless (looking-at verilog-extended-case-re)
	    (goto-char here)))
	(setq nest (1- nest)))
       ((match-end 3)
	(setq nest (1+ nest)))
       ((bobp)
	(ding 't)
	(setq nest 0))))))

(defun verilog-leap-to-class-head ()
  (let ((nest 1)
        (class-re (concat "\\(\\<class\\>\\)\\|\\(\\<endclass\\>\\)")))
    (catch 'skip
      (while (verilog-re-search-backward class-re nil 'move)
        (cond
         ((match-end 1) ; begin
          (when (verilog-looking-back "\\(\\<interface\\>\\s-+\\)\\|\\(\\<virtual\\>\\s-+\\)" (point-at-bol))
            (goto-char (match-beginning 0)))
          (unless (verilog-looking-back "\\<typedef\\>\\s-+" (point-at-bol))
            (setq nest (1- nest))
            (if (= 0 nest)
	        ;; Now previous line describes syntax
	        (throw 'skip 1))))
	 ((match-end 2) ; end
          (setq nest (1+ nest))))))))

(defun verilog-leap-to-head ()
  "Move point to the head of this block.
Jump from end to matching begin, from endcase to matching case, and so on."
  (let ((reg nil)
	snest
	(nesting 'yes)
	(nest 1))
    (cond
     ((looking-at "\\<end\\>")
      ;; 1: Search back for matching begin
      (setq reg (concat "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)\\|"
			"\\(\\<endcase\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)" )))
     ((looking-at "\\<endtask\\>")
      ;; 2: Search back for matching task
      (setq reg "\\(\\<task\\>\\)\\|\\(\\(\\<\\(virtual\\|protected\\|static\\)\\>\\s-+\\)+\\<task\\>\\)")
      (setq nesting 'no))
     ((looking-at "\\<endcase\\>")
      (catch 'nesting
	(verilog-leap-to-case-head) )
      (setq reg nil) ; to force skip
      )

     ((looking-at "\\<join\\(_any\\|_none\\)?\\>")
      ;; 4: Search back for matching fork
      (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)" ))
     ((looking-at "\\<endclass\\>")
      ;; 5: Search back for matching class
      (catch 'nesting
        (verilog-leap-to-class-head)
        (setq reg nil)))
     ((looking-at "\\<endtable\\>")
      ;; 6: Search back for matching table
      (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" ))
     ((looking-at "\\<endspecify\\>")
      ;; 7: Search back for matching specify
      (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" ))
     ((looking-at "\\<endfunction\\>")
      ;; 8: Search back for matching function
      (setq reg "\\(\\<function\\>\\)\\|\\(\\(\\<\\(virtual\\|protected\\|static\\)\\>\\s-+\\)+\\<function\\>\\)")
      (setq nesting 'no))
     ;;(setq reg "\\(\\<function\\>\\)\\|\\(\\<endfunction\\>\\)" ))
     ((looking-at "\\<endgenerate\\>")
      ;; 8: Search back for matching generate
      (setq reg "\\(\\<generate\\>\\)\\|\\(\\<endgenerate\\>\\)" ))
     ((looking-at "\\<endgroup\\>")
      ;; 10: Search back for matching covergroup
      (setq reg "\\(\\<covergroup\\>\\)\\|\\(\\<endgroup\\>\\)" ))
     ((looking-at "\\<endproperty\\>")
      ;; 11: Search back for matching property
      (setq reg "\\(\\<property\\>\\)\\|\\(\\<endproperty\\>\\)" ))
     ((looking-at verilog-uvm-end-re)
      ;; 12: Search back for matching sequence
      (setq reg (concat "\\(" verilog-uvm-begin-re "\\|" verilog-uvm-end-re "\\)")))
     ((looking-at verilog-ovm-end-re)
      ;; 12: Search back for matching sequence
      (setq reg (concat "\\(" verilog-ovm-begin-re "\\|" verilog-ovm-end-re "\\)")))
     ((looking-at verilog-vmm-end-re)
      ;; 12: Search back for matching sequence
      (setq reg (concat "\\(" verilog-vmm-begin-re "\\|" verilog-vmm-end-re "\\)")))
     ((looking-at "\\<endinterface\\>")
      ;; 12: Search back for matching interface
      (setq reg "\\(\\<interface\\>\\)\\|\\(\\<endinterface\\>\\)" ))
     ((looking-at "\\<endsequence\\>")
      ;; 12: Search back for matching sequence
      (setq reg "\\(\\<\\(rand\\)?sequence\\>\\)\\|\\(\\<endsequence\\>\\)" ))
     ((looking-at "\\<endclocking\\>")
      ;; 12: Search back for matching clocking
      (setq reg "\\(\\<clocking\\)\\|\\(\\<endclocking\\>\\)" ))
     ;; Search back for matching package
     ((looking-at "\\<endpackage\\>")
      (setq reg "\\(\\<package\\>\\)" ))
     ;; Search back for matching program
     ((looking-at "\\<endprogram\\>")
      (setq reg "\\(\\<program\\>\\)" ))
     ((looking-at "\\<`endif\\>")
      ;; Search back for matching `endif `else `elsif
      (setq reg "\\(\\<`ifn?def\\>\\)\\|\\(\\<`endif\\>\\)" ))
     ((looking-at "\\<`else\\>")
      ;; Search back for matching `else `else `elsif
      (setq reg "\\(\\<`ifn?def\\>\\|\\<`elsif\\>\\)\\|\\(\\<`else\\>\\)" )))
    (if reg
	(catch 'skip
	  (if (eq nesting 'yes)
	      (let (sreg)
		(while (verilog-re-search-backward reg nil 'move)
		  (cond
		   ((match-end 1) ; begin
		    (if (looking-at "fork")
			(let ((here (point)))
			  (verilog-beg-of-statement)
			  (unless (looking-at verilog-disable-fork-re)
			    (goto-char here)
			    (setq nest (1- nest))))
		      (setq nest (1- nest)))
		    (if (= 0 nest)
			;; Now previous line describes syntax
			(throw 'skip 1))
		    (if (and snest
			     (= snest nest))
			(setq reg sreg)))
		   ((match-end 2) ; end
		    (setq nest (1+ nest)))
		   ((match-end 3)
		    ;; endcase, jump to case
		    (setq snest nest)
		    (setq nest (1+ nest))
		    (setq sreg reg)
		    (setq reg "\\(\\<randcase\\>\\|\\<case[xz]?\\>[^:]\\)\\|\\(\\<endcase\\>\\)" ))
		   ((match-end 4)
		    ;; join, jump to fork
		    (setq snest nest)
		    (setq nest (1+ nest))
		    (setq sreg reg)
		    (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\(_any\\|_none\\)?\\>\\)" ))
		   )))
	    ;; no nesting
	    (if (and
		 (verilog-re-search-backward reg nil 'move)
		 (match-end 1)) ; task -> could be virtual and/or protected
		(progn
		  (verilog-beg-of-statement)
		  (throw 'skip 1))
	      (throw 'skip 1)))))))

(defun verilog-continued-line ()
  "Return non-nil if this is a continued line.
Set point to where line starts."
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
              (setq continued (verilog-backward-token)))))
      (setq continued nil))
    continued))

(defun verilog-backward-token ()
  "Step backward token, returning true if this is a continued line."
  (interactive)
  (verilog-backward-syntactic-ws)
  (cond
   ((bolp)
    nil)
   (;-- Anything ending in a ; is complete
    (= (preceding-char) ?\;)
    nil)
   (;  If a "}" is prefixed by a ";", then this is a complete statement
    ;; i.e.: constraint foo { a = b; }
    (= (preceding-char) ?\})
    (progn
      (backward-char)
      (not(verilog-at-close-constraint-p))))
   (;-- constraint foo { a = b }
    ;;  is a complete statement. *sigh*
    (= (preceding-char) ?\{)
    (progn
      (backward-char)
      (not (verilog-at-constraint-p))))
   (;" string "
    (= (preceding-char) ?\")
    (backward-char)
    (verilog-skip-backward-comment-or-string)
    nil)

   (; [3:4]
    (= (preceding-char) ?\])
    (backward-char)
    (verilog-backward-open-bracket)
    t)

   (;-- Could be 'case (foo)' or 'always @(bar)' which is complete
    ;;  also could be simply '@(foo)'
    ;;  or foo u1 #(a=8)
    ;;           (b, ... which ISN'T complete
    ;; Do we need this???
    (= (preceding-char) ?\))
    (progn
      (backward-char)
      (verilog-backward-up-list 1)
      (verilog-backward-syntactic-ws)
      (let ((back (point)))
	(forward-word-strictly -1)
	(cond
	 ;;XX
	 ((looking-at "\\<\\(always\\(_latch\\|_ff\\|_comb\\)?\\|case\\(\\|[xz]\\)\\|for\\(\\|each\\|ever\\)\\|i\\(f\\|nitial\\)\\|repeat\\|while\\)\\>")
	  (not (looking-at "\\<randcase\\>\\|\\<case[xz]?\\>[^:]")))
	 ((looking-at verilog-uvm-statement-re)
	  nil)
	 ((looking-at verilog-uvm-begin-re)
	  t)
	 ((looking-at verilog-uvm-end-re)
	  t)
	 ((looking-at verilog-ovm-statement-re)
	  nil)
	 ((looking-at verilog-ovm-begin-re)
	  t)
	 ((looking-at verilog-ovm-end-re)
	  t)
         ;; JBA find VMM macros
         ((looking-at verilog-vmm-statement-re)
          nil )
         ((looking-at verilog-vmm-begin-re)
          t)
         ((looking-at verilog-vmm-end-re)
          nil)
         ;; JBA trying to catch macro lines with no ; at end
         ((looking-at "\\<`")
          nil)
	 (t
	  (goto-char back)
	  (cond
	   ((= (preceding-char) ?\@)
	    (backward-char)
	    (save-excursion
	      (verilog-backward-token)
	      (not (looking-at "\\<\\(always\\(_latch\\|_ff\\|_comb\\)?\\|initial\\|while\\)\\>"))))
	   ((= (preceding-char) ?\#)
	    (backward-char))
	   (t t)))))))

   (;-- any of begin|initial|while are complete statements; 'begin : foo' is also complete
    t
    (forward-word-strictly -1)
    (while (or (= (preceding-char) ?\_)
               (= (preceding-char) ?\@)
               (= (preceding-char) ?\.))
      (forward-word-strictly -1))
    (cond
     ((looking-at "\\<else\\>")
      t)
     ((looking-at verilog-behavioral-block-beg-re)
      t)
     ((looking-at verilog-indent-re)
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
	  (if (looking-at verilog-nameable-item-re )
	      nil
	    t))
	 ((= (preceding-char) ?\#)
	  (backward-char)
	  t)
	 ((= (preceding-char) ?\`)
	  (backward-char)
	  t)

	 (t
	  (goto-char back)
	  t))))))))

(defun verilog-backward-syntactic-ws ()
  "Move backwards putting point after first non-whitespace non-comment."
  (verilog-skip-backward-comments)
  (forward-comment (- (buffer-size))))

(defun verilog-backward-syntactic-ws-quick ()
  "As with `verilog-backward-syntactic-ws' but use `verilog-scan' cache."
  (while (cond ((bobp)
                nil) ; Done
               ((< (skip-syntax-backward " ") 0)
                t)
               ((eq (preceding-char) ?\n)  ; \n's terminate // so aren't space syntax
                (forward-char -1)
                t)
               ((or (verilog-inside-comment-or-string-p (1- (point)))
                    (verilog-inside-comment-or-string-p (point)))
                (re-search-backward "[/\"]" nil t)  ; Only way a comment or quote can begin
                t))))

(defun verilog-forward-syntactic-ws ()
  (verilog-skip-forward-comment-p)
  (forward-comment (buffer-size)))

(defun verilog-backward-ws&directives (&optional bound)
  "Backward skip over syntactic whitespace and compiler directives for Emacs 19.
Optional BOUND limits search."
  (save-restriction
    (let* ((bound (or bound (point-min)))
	   (here bound)
	   (p nil) )
      (if (< bound (point))
	  (progn
	    (let ((state (save-excursion (verilog-syntax-ppss))))
	      (cond
               ((nth 7 state)  ; in // comment
		(re-search-backward "//" nil 'move)
                (skip-chars-backward "/"))
               ((nth 4 state)  ; in /* */ comment
		(re-search-backward "/\\*" nil 'move))))
	    (narrow-to-region bound (point))
	    (while (/= here (point))
	      (setq here (point))
	      (verilog-skip-backward-comments)
	      (setq p
		    (save-excursion
		      (beginning-of-line)
		      ;; for as long as we're right after a continued line, keep moving up
		      (while (and (verilog-looking-back "\\\\[\n\r\f]" nil)
                                  (forward-line -1)))
		      (cond
		       ((and verilog-highlight-translate-off
			     (verilog-within-translate-off))
			(verilog-back-to-start-translate-off (point-min)))
		       ((looking-at verilog-directive-re-1)
			(point))
		       (t
			nil))))
	      (if p (goto-char p))))))))

(defun verilog-forward-ws&directives (&optional bound)
  "Forward skip over syntactic whitespace and compiler directives for Emacs 19.
Optional BOUND limits search."
  (save-restriction
    (let* ((bound (or bound (point-max)))
	   (here bound)
	   jump)
      (if (> bound (point))
	  (progn
	    (let ((state (save-excursion (verilog-syntax-ppss))))
	      (cond
               ((nth 7 state)  ; in // comment
		(end-of-line)
		(forward-char 1)
		(skip-chars-forward " \t\n\f")
		)
               ((nth 4 state)  ; in /* */ comment
		(verilog-re-search-forward "\\*/\\s-*" nil 'move))))
	    (narrow-to-region (point) bound)
	    (while (/= here (point))
	      (setq here (point)
		    jump nil)
	      (forward-comment (buffer-size))
              (and (looking-at "\\s-*(\\*.*\\*)\\s-*")  ; Attribute
		   (goto-char (match-end 0)))
	      (save-excursion
		(beginning-of-line)
		(if (looking-at verilog-directive-re-1)
		    (setq jump t)))
	      (if jump
		  (beginning-of-line 2))))))))

(defun verilog-pos-at-beg-of-statement ()
  "Return point position at the beginning of current statement."
  (save-excursion
    (verilog-beg-of-statement)
    (point)))

(defun verilog-col-at-beg-of-statement ()
  "Return current column at the beginning of current statement."
  (save-excursion
    (verilog-beg-of-statement)
    (current-column)))

(defun verilog-pos-at-end-of-statement ()
  "Return point position at the end of current statement."
  (save-excursion
    (verilog-end-of-statement)
    (point)))

(defun verilog-col-at-end-of-statement ()
  "Return current column at the end of current statement."
  (save-excursion
    (verilog-end-of-statement)
    (current-column)))

(defun verilog-pos-at-forward-syntactic-ws ()
  "Return point position at next non whitespace/comment token."
  (save-excursion
    (verilog-forward-syntactic-ws)
    (point)))

(defun verilog-col-at-forward-syntactic-ws ()
  "Return current column at next non whitespace/comment token."
  (save-excursion
    (verilog-forward-syntactic-ws)
    (current-column)))

(defun verilog-pos-at-backward-syntactic-ws ()
  "Return point position at previous non whitespace/comment token."
  (save-excursion
    (verilog-backward-syntactic-ws)
    (point)))

(defun verilog-col-at-backward-syntactic-ws ()
  "Return current column at previous non whitespace/comment token."
  (save-excursion
    (verilog-backward-syntactic-ws)
    (current-column)))

(defun verilog-in-comment-p ()
  "Return non-nil if in a star or // comment."
  (let ((state (save-excursion (verilog-syntax-ppss))))
    (or (nth 4 state) (nth 7 state))))

(defun verilog-in-star-comment-p ()
  "Return non-nil if in a star comment."
  (let ((state (save-excursion (verilog-syntax-ppss))))
    (and
     (nth 4 state)			; t if in a comment of style a // or b /**/
     (not
      (nth 7 state)			; t if in a comment of style b /**/
      ))))

(defun verilog-in-slash-comment-p ()
  "Return non-nil if in a slash comment."
  (let ((state (save-excursion (verilog-syntax-ppss))))
    (nth 7 state)))

(defun verilog-in-comment-or-string-p ()
  "Return non-nil if in a string or comment."
  (let ((state (save-excursion (verilog-syntax-ppss))))
    (or (nth 3 state) (nth 4 state) (nth 7 state)))) ; Inside string or comment)

(defun verilog-in-attribute-p ()
  "Return non-nil if point is in an attribute (* [] attribute *)."
  (let ((pos (point)))
    (save-match-data
      (save-excursion
        (and (verilog-re-search-backward "(\\*" nil 'move)
             (progn (forward-sexp)
                    (skip-chars-backward "*)"))
             (< pos (point)))))))

(defun verilog-in-parameter-p ()
  "Return non-nil if point is in a parameter assignment #( p1=1, p2=5)."
  (save-match-data
    (save-excursion
      (and (progn
             (verilog-backward-up-list 1)
             (verilog-backward-syntactic-ws)
             (= (preceding-char) ?\#))
           (progn
             (verilog-beg-of-statement-1)
             (looking-at verilog-defun-re))))))

(defun verilog-in-escaped-name-p ()
  "Return non-nil if in an escaped name."
  (save-excursion
    (backward-char)
    (skip-chars-backward "^ \t\n\f")
    (if (equal (char-after (point) ) ?\\ )
        t
      nil)))

(defun verilog-in-directive-p ()
  "Return non-nil if in a directive."
  (save-excursion
    (beginning-of-line)
    (looking-at verilog-directive-re-1)))

(defun verilog-in-parenthesis-p ()
  "Return non-nil if in a ( ) expression (but not { } or [ ])."
  (save-match-data
    (save-excursion
      (verilog-re-search-backward "\\((\\)\\|\\()\\)" nil 'move)
      (numberp (match-beginning 1)))))

(defun verilog-in-paren ()
  "Return non-nil if in a parenthetical expression.
May cache result using `verilog-syntax-ppss'."
  (let ((state (save-excursion (verilog-syntax-ppss))))
    (> (nth 0 state) 0 )))

(defun verilog-in-paren-count ()
  "Return paren depth, floor to 0.
May cache result using `verilog-syntax-ppss'."
  (let ((state (save-excursion (verilog-syntax-ppss))))
    (if (> (nth 0 state) 0)
        (nth 0 state)
      0 )))

(defun verilog-in-paren-quick ()
  "Return non-nil if in a parenthetical expression.
Always starts from `point-min', to allow inserts with hooks disabled."
  ;; The -quick refers to its use alongside the other -quick functions,
  ;; not that it's likely to be faster than verilog-in-paren.
  (let ((state (save-excursion (parse-partial-sexp (point-min) (point)))))
    (> (nth 0 state) 0 )))

(defun verilog-in-struct-p ()
  "Return non-nil if in a struct declaration."
  (interactive)
  (save-excursion
    (if (verilog-in-paren)
        (progn
          (verilog-backward-up-list 1)
          (verilog-at-struct-p)
          )
      nil)))

(defun verilog-in-struct-nested-p ()
  "Return nil for not in struct.
Return 0 for in non-nested struct.
Return >0 for nested struct."
  (interactive)
  (let (col)
    (save-excursion
      (if (verilog-in-paren)
          (progn
            (verilog-backward-up-list 1)
            (setq col (verilog-at-struct-mv-p))
            (if col
                (if (verilog-in-struct-p) (current-column) 0)))
        nil))))

(defun verilog-in-coverage-p ()
  "Return non-nil if in a constraint or coverpoint expression."
  (interactive)
  (save-excursion
    (if (verilog-in-paren)
        (progn
          (verilog-backward-up-list 1)
          (verilog-at-constraint-p)
          )
      nil)))

(defun verilog-at-close-constraint-p ()
  "If at the } that closes a constraint or covergroup, return true."
  (if (and
       (equal (char-after) ?\})
       (verilog-in-coverage-p))

      (save-excursion
	(verilog-backward-ws&directives)
	(if (or (equal (char-before) ?\;)
                (equal (char-before) ?\})  ; can end with inner constraint { } block or ;
                (equal (char-before) ?\{))  ; empty constraint block
	    (point)
	  nil))))

(defun verilog-at-constraint-p ()
  "If at the { of a constraint or coverpoint definition, return true.
Also move point to constraint."
  (if (save-excursion
	(let ((p (point)))
          (and
           (equal (char-after) ?\{)
           (not (verilog-at-streaming-op-p))
           (ignore-errors (forward-list))
           (progn (backward-char 1)
                  (verilog-backward-ws&directives)
                  (and
                   (or (equal (char-before) ?\{)  ; empty case
                       (equal (char-before) ?\;)
                       (equal (char-before) ?\}))
                   ;; skip what looks like bus repetition operator {#{
                   (not (string-match "^{\\s-*[][()0-9a-zA-Z_,:\\]*\\s-*{"
                                      (buffer-substring p (point)))))))))
      (progn
        (let ( (pt (point)) (pass 0))
          (verilog-backward-ws&directives)
          (verilog-backward-token)
          (if (looking-at (concat "\\<\\(?:constraint\\|coverpoint\\|cross\\|with\\)\\>\\|" verilog-in-constraint-re))
              (progn (setq pass 1)
                     (if (looking-at "\\<with\\>")
                         (progn (verilog-backward-ws&directives)
                                (beginning-of-line)  ; 1
                                (verilog-forward-ws&directives)
                                1 )
                       (verilog-beg-of-statement)
                       ))
            ;; if first word token not keyword, it maybe the instance name
            ;;   check next word token
            (if (looking-at "\\<\\w+\\>\\|\\s-*[[(}]\\s-*\\S-+")
                (progn (verilog-beg-of-statement)
                       (if (and
                            (not (string-match verilog-named-block-re (buffer-substring pt (point)))) ;; Abort if 'begin' keyword is found
                            (looking-at (concat "\\<\\(constraint\\|"
                                               "\\(?:\\w+\\s-*:\\s-*\\)?\\(coverpoint\\|cross\\)"
                                               "\\|with\\)\\>\\|" verilog-in-constraint-re)))
                           (setq pass 1)))))
          (if (eq pass 0)
              (progn (goto-char pt) nil) 1)))
    ;; not
    nil))

(defconst verilog-streaming-op-re
  ;; Regexp to detect Streaming Operator expressions
  (concat
   "{" "\\s-*"
   "\\(<<\\|>>\\)" ".*"
   "{" ".*" "}" "\\s-*" "}"
   ))

(defun verilog-at-streaming-op-p ()
  "If at the { of a streaming operator, return t."
  (looking-at verilog-streaming-op-re))

(defun verilog-at-struct-p ()
  "If at the { of a struct, return true, not moving point."
  (save-excursion
    (if (and (equal (char-after) ?\{)
             (verilog-backward-token))
        (looking-at "\\<\\(?:struct\\|union\\|packed\\|\\(un\\)?signed\\)\\>")
      nil)))

(defun verilog-at-struct-mv-p ()
  "If at the { of a struct, return true, moving point to struct."
  (let ((pt (point)))
    (if (and (equal (char-after) ?\{)
             (verilog-backward-token))
        (if (looking-at "\\<\\(?:struct\\|union\\|packed\\|\\(un\\)?signed\\)\\>")
            (progn (verilog-beg-of-statement) (point))
          (progn (goto-char pt) nil))
      (progn (goto-char pt) nil))))

(defun verilog-at-close-struct-p ()
  "If at the } that closes a struct, return true."
  (and (equal (char-after) ?\})
       (verilog-in-struct-p)
       (looking-at "}\\(?:\\s-*\\w+\\s-*\\(?:,\\s-*\\w+\\s-*\\)*\\)?;")))

(defun verilog-at-struct-decl-p ()
  "Return non-nil if at a struct declaration."
  (interactive)
  (save-excursion
    (verilog-re-search-forward "{" (point-at-eol) t)
    (unless (bobp)
      (backward-char))
    (verilog-at-struct-p)))

(defun verilog-at-enum-p ()
  "If at the { of a enum, return true, not moving point."
  (save-excursion
    (when (equal (char-after) ?\{)
      (verilog-beg-of-statement)
      (beginning-of-line)
      (when (verilog-re-search-forward verilog-typedef-enum-re (verilog-pos-at-end-of-statement) t)
        t))))

(defun verilog-at-enum-decl-p ()
  "Return non-nil if at a enum declaration."
  (interactive)
  (save-excursion
    (verilog-re-search-forward "{" (verilog-pos-at-end-of-statement) t)
    (unless (bobp)
      (backward-char))
    (verilog-at-enum-p)))

(defun verilog-parenthesis-depth ()
  "Return non zero if in parenthetical-expression."
  (save-excursion (nth 1 (verilog-syntax-ppss))))

(defun verilog-skip-forward-comment-or-string ()
  "Return non-nil if in a string or comment."
  (let ((state (save-excursion (verilog-syntax-ppss))))
    (cond
     ((nth 3 state)			;Inside string
      (search-forward "\"")
      t)
     ((nth 7 state)			;Inside // comment
      (forward-line 1)
      t)
     ((nth 4 state)			;Inside any comment (hence /**/)
      (search-forward "*/"))
     (t
      nil))))

(defun verilog-skip-backward-comment-or-string ()
  "Return non-nil if in a string or comment."
  (let ((state (save-excursion (verilog-syntax-ppss))))
    (cond
     ((nth 3 state)			;Inside string
      (search-backward "\"")
      t)
     ((nth 7 state)			;Inside // comment
      (search-backward "//")
      (skip-chars-backward "/")
      t)
     ((nth 4 state)			;Inside /* */ comment
      (search-backward "/*")
      t)
     (t
      nil))))

(defun verilog-skip-backward-comments ()
  "Return non-nil if a comment was skipped."
  (let ((more t))
    (while more
      (setq more
            (let ((state (save-excursion (verilog-syntax-ppss))))
              (cond
               ((nth 7 state)			;Inside // comment
                (search-backward "//")
                (skip-chars-backward "/")
                (skip-chars-backward " \t\n\f")
                t)
               ((nth 4 state)			;Inside /* */ comment
                (search-backward "/*")
                (skip-chars-backward " \t\n\f")
                t)
               ((and (not (bobp))
                     (= (char-before) ?\/)
                     (= (char-before (1- (point))) ?\*))
                (goto-char (- (point) 2))
                t)  ; Let nth 4 state handle the rest
               ((and (not (bobp))
                     ;;(verilog-looking-back "\\*)" nil) ;; super slow, use two char-before instead
                     (= (char-before) ?\))
                     (= (char-before (1- (point))) ?\*)
                     (not (verilog-looking-back "(\\s-*\\*)" nil))) ;; slow but unlikely to be called
                (goto-char (- (point) 2))
                (if (search-backward "(*" nil t)
                    (progn
                      (skip-chars-backward " \t\n\f")
                      t)
                  (progn
                    (goto-char (+ (point) 2))
                    nil)))
               (t
                (/= (skip-chars-backward " \t\n\f") 0))))))))

(defun verilog-skip-forward-comment-p ()
  "If in comment, move to end and return true."
  (let* (h
	 (state (save-excursion (verilog-syntax-ppss)))
	 (skip (cond
		((nth 3 state)		;Inside string
		 t)
		((nth 7 state)		;Inside // comment
		 (end-of-line)
		 (forward-char 1)
		 t)
		((nth 4 state)		;Inside /* comment
		 (search-forward "*/")
		 t)
		((verilog-in-attribute-p)  ;Inside (* attribute
		 (search-forward "*)" nil t)
		 t)
		(t nil))))
    (skip-chars-forward " \t\n\f")
    (while
        (cond
         ((looking-at "/\\*")
          (progn
	    (setq h (point))
	    (goto-char (match-end 0))
	    (if (search-forward "*/" nil t)
		(progn
		  (skip-chars-forward " \t\n\f")
		  (setq skip 't))
	      (progn
		(goto-char h)
		nil))))
         ((and (looking-at "(\\*")  ; attribute start, but not an event (*) or (* )
	       (not (looking-at "(\\*\\s-*)")))
	  (progn
	    (setq h (point))
	    (goto-char (match-end 0))
	    (if (search-forward "*)" nil t)
		(progn
		  (skip-chars-forward " \t\n\f")
		  (setq skip 't))
	      (progn
		(goto-char h)
		nil))))
	 (t nil)))
    skip))

(defun verilog-indent-line-relative ()
  "Cheap version of indent line.
Only look at a few lines to determine indent level."
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
		(progn
		  (goto-char sp)
		  (setq indent-str
			(list 'statement (verilog-current-indent-level))))
	      (goto-char sp1)
	      (setq indent-str (list 'block (verilog-current-indent-level)))))
	  (goto-char sp))
	 ((goto-char sp)
	  (setq indent-str (verilog-calculate-indent))))
      (progn (skip-chars-forward " \t")
	     (setq indent-str (verilog-calculate-indent))))
    (verilog-do-indent indent-str)))

(defun verilog-indent-line ()
  "Indent for special part of code."
  (verilog-do-indent (verilog-calculate-indent)))

(defun verilog-do-indent (indent-str)
  ;; `ind' is used in expressions stored in `verilog-indent-alist'.
  (verilog--suppressed-warnings ((lexical ind)) (defvar ind))
  (let ((type (car indent-str))
	(ind (car (cdr indent-str))))
    (cond
     (; handle indentation ignoring
      (verilog-indent-ignore-p)
      nil)
     (; handle continued exp
      (eq type 'cexp)
      (let ((here (point)))
	(verilog-backward-syntactic-ws)
	(cond
	 ((or
	   (= (preceding-char) ?\,)
	   (save-excursion
	     (verilog-beg-of-statement-1)
	     (verilog-looking-at-decl-to-align)))
	  (let* ( fst
		  (val
		   (save-excursion
		     (backward-char 1)
		     (verilog-beg-of-statement-1)
		     (setq fst (point))
		     (if (looking-at (verilog-get-declaration-re))
                         (progn  ; we have multiple words
			   (goto-char (match-end 0))
			   (skip-chars-forward " \t")
			   (cond
			    ((and verilog-indent-declaration-macros
				  (= (following-char) ?\`))
			     (progn
			       (forward-char 1)
			       (forward-word-strictly 1)
			       (skip-chars-forward " \t")))
			    ((= (following-char) ?\[)
			     (progn
			       (forward-char 1)
			       (verilog-backward-up-list -1)
			       (skip-chars-forward " \t"))))
			   (current-column))
		       (progn
			 (goto-char fst)
			 (+ (current-column) verilog-cexp-indent))))))
	    (goto-char here)
	    (indent-line-to val)
            (when (and (not verilog-indent-lists)
                       (verilog-in-paren))
              (verilog-pretty-declarations-auto))
	    ))
	 ((= (preceding-char) ?\) )
	  (goto-char here)
	  (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
	    (indent-line-to val)))
	 (t
	  (goto-char here)
         (verilog-beg-of-statement-1)
         (let ((val
                (if (and (< (point) here)
                         (verilog-re-search-forward "=[ \t]*\\(#[ \t]*[0-9]+[ \t]*\\)?" here 'move)
                         ;; not at a |=>, #=#, or [=n] operator
                         (not (string-match "\\[=.\\|#=#\\||=>"
                                             (or (buffer-substring
                                                  (- (point) 2) (1+ (point)))
                                                 ;; Don't let buffer over/under
                                                 ;; run spoil the party.
                                                 ""))))
                    (current-column)
                  (eval (cdr (assoc type verilog-indent-alist))))))
	    (goto-char here)
	    (indent-line-to val))))))

     (; handle inside parenthetical expressions
      (eq type 'cparenexp)
      (let* ((val (verilog-cparenexp-indent-level))
             (here (save-excursion
                     (verilog-backward-up-list 1)
                     (forward-char 1)
                     (skip-chars-forward " \t")
                     (point)))
             (decl (save-excursion
                     (goto-char here)
                     (verilog-forward-syntactic-ws)
                     (setq here (point))
                     (looking-at (verilog-get-declaration-re)))))
        (indent-line-to val)
        (if decl
            (verilog-pretty-declarations-auto))))

     (;-- Handle the ends
      (or
       (looking-at verilog-end-block-re)
       (verilog-at-close-constraint-p)
       (verilog-at-close-struct-p))
      (let ((val (if (eq type 'statement)
		     (- ind verilog-indent-level)
		   ind)))
	(indent-line-to val)))

     (;-- Case -- maybe line 'em up
      (and (eq type 'case) (not (looking-at "^[ \t]*$")))
      (progn
	(cond
	 ((looking-at "\\<endcase\\>")
	  (indent-line-to ind))
	 (t
	  (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
	    (indent-line-to val))))))

     (;-- defun
      (and (eq type 'defun)
	   (or (and verilog-indent-class-inside-pkg
                    (looking-at verilog-zero-indent-no-class-re))
               (and (not verilog-indent-class-inside-pkg)
                    (looking-at verilog-zero-indent-re))))
      (indent-line-to 0))

     (;-- declaration
      (and (or
	    (eq type 'defun)
	    (eq type 'block))
           (verilog-looking-at-decl-to-align)
           ;; Do not consider "virtual function", "virtual task", "virtual class"
           ;; as declarations
           (not (looking-at (concat (verilog-get-declaration-re)
                                    "\\s-+\\(function\\|task\\|class\\)\\b"))))
      (verilog-indent-declaration ind))

     (;-- form feeds - ignored as bug in indent-line-to in < 24.5
      (looking-at "\f"))

     (;-- Everything else
      t
      (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
	(indent-line-to val))))

    (if (looking-at "[ \t]+$")
	(skip-chars-forward " \t"))
    indent-str				; Return indent data
    ))

(defun verilog-current-indent-level ()
  "Return the indent-level of the current statement."
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
  "Return the indent-level of the current statement.
Do not count named blocks or case-statements."
  (save-excursion
    (skip-chars-forward " \t")
    (cond
     ((looking-at verilog-named-block-re)
      (current-column))
     ((and (not (looking-at verilog-extended-case-re))
	   (looking-at "^[^:;]+:"))
      (verilog-re-search-forward ":" nil t)
      (skip-chars-forward " \t")
      (current-column))
     (t
      (current-column)))))

(defun verilog-cparenexp-indent-level ()
  "Return indent level for current line inside a parenthetical expression."
  (let ((start-pos (point))
        (close-par (looking-at "[)}]"))
        pos pos-arg-paren)
    (save-excursion
      (verilog-backward-up-list 1)
      (if verilog-indent-lists
          (progn
            (forward-char 1)
            (skip-chars-forward " \t")
            (current-column))
        ;; Indentation with `verilog-indent-lists' set to nil
        (verilog-beg-of-statement-1)
        (when (looking-at "\\<\\(function\\|task\\)\\>")
          (verilog-beg-of-statement)) ; find virtual/protected/static
        (cond (;; 1) Closing ); of a module/function/task
               (and close-par
                    (save-excursion
                      (verilog-beg-of-statement-1)
                      (or (looking-at verilog-complete-re)
                          (progn (beginning-of-line)
                                 (not (looking-at verilog-assignment-operation-re))))))
               (current-column))
              (;; 2) if (condition)
               (looking-at "(")
               (forward-char 1)
               (skip-chars-forward " \t\f" (point-at-eol))
               (current-column))
              (;; 3) Inside a module/defun param list or function/task argument list
               (or (looking-at verilog-defun-level-re)
                   (looking-at "\\(\\<\\(virtual\\|protected\\|static\\)\\>\\s-+\\)?\\(\\<task\\>\\|\\<function\\>\\)"))
               (setq pos-arg-paren (save-excursion
                                     (goto-char start-pos)
                                     (verilog-backward-up-list 1)
                                     (forward-char)
                                     (skip-chars-forward " \t")
                                     (when (not (eolp))
                                       (current-column))))
               (or pos-arg-paren
                   ;; arg in next line after (
                   (+ (current-column) verilog-indent-level)))
              (;; 4) Assignment operation
               (save-excursion
                 (beginning-of-line)
                 (and (looking-at verilog-assignment-operation-re)
                      (save-excursion
                        (goto-char (match-beginning 2))
                        (not (verilog-within-string)))
                      (progn (verilog-forward-syntactic-ws)
                             (not (looking-at verilog-complete-re)))))
               (goto-char (match-end 2))
               (skip-chars-forward " \t\f" (point-at-eol))
               (skip-chars-forward "{(" (1+ (point)))
               (skip-chars-forward " \t\f" (point-at-eol))
               (current-column))
              (;; 5) Typedef enum declaration
               (verilog-at-enum-decl-p)
               (verilog-re-search-forward "{" (verilog-pos-at-end-of-statement) t)
               (if (> (verilog-pos-at-forward-syntactic-ws) (point-at-eol))
                   (+ (verilog-col-at-beg-of-statement) verilog-indent-level)
                 (verilog-col-at-forward-syntactic-ws)))
              (;; 6) Long reporting strings (e.g. $display or $sformatf inside `uvm_info)
               (save-excursion
                 (goto-char start-pos)
                 (verilog-backward-up-list 1)
                 (setq pos (1+ (point)))
                 (backward-word)
                 (or (looking-at (concat "\\$" verilog-identifier-re)) ; System function/task
                     (looking-at verilog-uvm-statement-re)))         ; `uvm_* macros
               (goto-char pos)
               (current-column))
              (t ;; 7) Default
               (+ (current-column) verilog-indent-level)))))))

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
	      (current-column))))))
    (indent-line-to stcol)
    stcol))

(defun verilog-more-comment ()
  "Make more comment lines like the previous."
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
	      (current-column))))))
    (progn
      (indent-to stcol)
      (if (and star
	       (save-excursion
		 (forward-line -1)
		 (skip-chars-forward " \t")
		 (looking-at "\\*")))
	  (insert "* ")))))

(defun verilog-comment-indent (&optional _arg)
  "Return the column number the line should be indented to.
_ARG is ignored, for `comment-indent-function' compatibility."
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
      (current-column)))))

;;

(defun verilog-align-comments (startpos endpos)
  "Align inline comments between STARTPOS and ENDPOS."
  (let (comm-ind e)
    (when verilog-align-decl-expr-comments
      (setq comm-ind (verilog-get-comment-align-indent (marker-position startpos) endpos))
      (save-excursion
        (goto-char (marker-position startpos))
        (while (progn (setq e (marker-position endpos))
                      (< (point) e))
          (when (verilog-search-comment-in-declaration e)
            (goto-char (match-beginning 0))
            (delete-horizontal-space)
            (indent-to (1- (+ comm-ind verilog-align-comment-distance)))))))))

(defun verilog-pretty-declarations-auto (&optional quiet)
  "Call `verilog-pretty-declarations' QUIET based on `verilog-auto-lineup'."
  (when (or (eq 'all verilog-auto-lineup)
	    (eq 'declarations verilog-auto-lineup))
    (verilog-pretty-declarations quiet)))

(defun verilog--pretty-declarations-find-end (&optional reg-end)
  "Find end position for current alignment of declarations.
If region is active, use arg REG-END to set a limit on the alignment."
  (let (e)
    (if (and (verilog-parenthesis-depth)
             (not (verilog-in-struct-p)))
        ;; In an argument list or parameter block
        (progn
          (verilog-backward-up-list -1)
          (forward-char -1)
          (verilog-backward-syntactic-ws)
          (if (region-active-p)
              (min reg-end (point))
            (point)))
      ;; In a declaration block (not in argument list)
      (verilog-end-of-statement)
      (setq e (point)) ; Might be on last line
      (verilog-forward-syntactic-ws)
      (while (verilog-looking-at-decl-to-align)
        (verilog-end-of-statement)
        (setq e (point))
        (verilog-forward-syntactic-ws))
      (if (region-active-p)
          (min reg-end e)
        e))))

(defun verilog--pretty-declarations-find-base-ind ()
  "Find base indentation for current alignment of declarations."
  (if (and (verilog-parenthesis-depth)
           (not (verilog-in-struct-p)))
      ;; In an argument list or parameter block
      (progn
        (unless (or (verilog-looking-back "(" (point-at-bol))
                    (bolp))
          (forward-char 1))
	(skip-chars-forward " \t")
	(current-column))
    ;; In a declaration block (not in argument list)
    (progn
      (verilog-do-indent (verilog-calculate-indent))
      (verilog-forward-ws&directives)
      (current-column))))

(defun verilog-pretty-declarations (&optional quiet)
  "Line up declarations around point.
Be verbose about progress unless optional QUIET set."
  (interactive)
  (let ((m1 (make-marker))
        (e (point))
	(here (point))
	el r ind start startpos end endpos base-ind rstart rend)
    (save-excursion
      (when (region-active-p)
        (setq rstart (region-beginning))
        (setq rend (region-end))
        (goto-char rstart)) ; Shrinks the region but ensures that start is a valid declaration
      (if (progn
            ;; Check if alignment can be performed
            (beginning-of-line)
            (verilog-forward-syntactic-ws)
            (or (and (not (verilog-in-directive-p))  ; could have `define input foo
                     (verilog-looking-at-decl-to-align))
                (and (verilog-parenthesis-depth)
                     (looking-at verilog-interface-modport-re))))
          ;; Find boundaries of alignment
          (progn
            (cond (;; Using region
                   (region-active-p)
                   (setq start rstart
                         startpos (set-marker (make-marker) start)
                         end (progn (goto-char start)
                                    (verilog--pretty-declarations-find-end rend))
                         endpos (set-marker (make-marker) end)
                         base-ind (progn (goto-char start)
                                         (verilog--pretty-declarations-find-base-ind))))
                  (;; In an argument list or parameter block
                   (and (verilog-parenthesis-depth)
                        (not (verilog-in-struct-p)))
                   (setq el (verilog-backward-up-list -1)
		         start (progn
			         (goto-char e)
			         (verilog-backward-up-list 1)
			         (verilog-re-search-forward (verilog-get-declaration-re 'iface-mp) el 'move)
			         (goto-char (match-beginning 0))
			         (skip-chars-backward " \t")
			         (point))
		         startpos (set-marker (make-marker) start)
		         end (progn (goto-char start)
                                    (verilog--pretty-declarations-find-end))
		         endpos (set-marker (make-marker) end)
		         base-ind (progn (goto-char start)
                                         (verilog--pretty-declarations-find-base-ind))))
                  (;; In a declaration block (not in argument list)
                   t
                   (setq
	            start (progn
		            (verilog-beg-of-statement-1)
		            (while (and (verilog-looking-at-decl-to-align)
				        (not (bobp)))
			      (skip-chars-backward " \t")
			      (setq e (point))
			      (verilog-backward-syntactic-ws)
			      (backward-char)
			      (verilog-beg-of-statement-1))
		            e)
	            startpos (set-marker (make-marker) start)
	            end (progn (goto-char here)
                               (verilog--pretty-declarations-find-end))
	            endpos (set-marker (make-marker) end)
	            base-ind (progn (goto-char start)
                                    (verilog--pretty-declarations-find-base-ind)))))
	    ;; OK, start and end are set
	    (goto-char (marker-position startpos))
	    (if (and (not quiet)
		     (> (- end start) 100))
		(message "Lining up declarations..(please stand by)"))
	    ;; Get the beginning of line indent first
	    (while (progn (setq e (marker-position endpos))
			  (< (point) e))
	      (cond
	       ((save-excursion (skip-chars-backward " \t")
				(bolp))
                (verilog-forward-ws&directives)
                (indent-line-to base-ind)
                (verilog-forward-ws&directives)
                (if (< (point) e)
                    (verilog-re-search-forward "[ \t\n\f]" (marker-position endpos) 'move)))
	       (t
                (unless (verilog-looking-back "(" (point-at-bol))
                  (just-one-space))
                (if (looking-at verilog-comment-start-regexp)
                    (verilog-forward-syntactic-ws)
		  (verilog-re-search-forward "[ \t\n\f]" e 'move)))))
	    ;; Now find biggest prefix
	    (setq ind (verilog-get-lineup-indent (marker-position startpos) endpos))
	    ;; Now indent each line.
	    (goto-char (marker-position startpos))
	    (while (progn (setq e (marker-position endpos))
			  (setq r (- e (point)))
			  (> r 0))
	      (setq e (point))
	      (unless quiet (message "%d" r))
	      (verilog-forward-ws&directives)
	      (cond
	       ((looking-at (verilog-get-declaration-re 'iface-mp))
                (unless (looking-at (verilog-get-declaration-re 'embedded-comments))
                  (let ((p (match-end 0)))
                    (set-marker m1 p)
                    (if (verilog-re-search-forward "[[#`]" p 'move)
                        (progn
                          (forward-char -1)
                          (just-one-space)
                          (goto-char (marker-position m1))
                          (delete-horizontal-space)
                          (indent-to ind 1))
                      (progn
                        (delete-horizontal-space)
                        (indent-to ind 1))))))
	       ((verilog-continued-line-1 (marker-position startpos))
		(goto-char e)
                (unless (and (verilog-in-parenthesis-p)
                             (looking-at (concat "\\s-*" verilog-identifier-sym-re "\\s-+" verilog-identifier-sym-re "\\s-*")))
                  (indent-line-to ind)))
	       ((verilog-in-struct-p)
		;; could have a declaration of a user defined item
		(goto-char e)
		(verilog-end-of-statement))
	       (t		; Must be comment or white space
		(goto-char e)
		(verilog-forward-ws&directives)
		(forward-line -1)))
	      (forward-line 1))
            ;; Align comments if enabled
            (when verilog-align-decl-expr-comments
              (verilog-align-comments startpos endpos)))
        ;; Exit
	(unless quiet (message ""))))))

(defun verilog--pretty-expr-assignment-found (&optional discard-re)
  "Return non-nil if point is at a valid assignment operation to be aligned.
Ensure cursor is not over DISCARD-RE (e.g. Verilog keywords).
If returned non-nil, update match data according to `verilog-assignment-operation-re'."
  ;; Not looking at a verilog keyword sentence (i.e looking at a potential assignment)
  (and (if discard-re
           (not (looking-at discard-re))
         t)
       ;; Corner case to filter first parameter on param lists
       (save-excursion
         (if (and (verilog-re-search-forward verilog-assignment-operation-re (point-at-eol) 'move)
                  (verilog-in-parenthesis-p))
             (progn (verilog-backward-up-list 1)
                    (forward-char 1)
                    (not (eq 0 (string-match discard-re (buffer-substring-no-properties (point) (point-at-eol))))))
           t))
       ;; Don't work on multiline assignments unless they are continued lines
       ;; e.g, multiple parameters or variable declarations in the same statement
       (if (save-excursion
             (and (not (verilog-in-parameter-p))
                  (verilog-continued-line)
                  (not (looking-at verilog-basic-complete-re))))
           (save-excursion
             (verilog-beg-of-statement-1)
             (looking-at (verilog-get-declaration-re)))
         t)
       ;; Ensure it's not any kind of logical comparison
       (save-excursion
         (unless (and (not (verilog-in-parameter-p))
                      (verilog-re-search-forward (verilog-regexp-words '("if" "for" "assert" "with")) (point-at-eol) 'move))
           t))
       ;; Looking at an assignment (last check, provides match data)
       (looking-at verilog-assignment-operation-re)))

(defun verilog--pretty-expr-find-end (&optional discard-re reg-end)
  "Find end position for current alignment of expressions.
Use optional arg DISCARD-RE when aligning expressions outside of an
argument list and REG-END to set a limit on the alignment when the
region is active."
  (if (verilog-in-parenthesis-p)
      ;; Limit end in argument list
      (progn
        (verilog-backward-up-list -1)
        (forward-char -1)
        (verilog-backward-syntactic-ws)
        (if (region-active-p)
            (min reg-end (point))
          (point)))
    ;; Limit end in non-argument list
    (save-excursion ; EOL of the last line of the assignment block
      (end-of-line)
      (let ((pt (point))) ; Might be on last line
        (verilog-forward-syntactic-ws)
        (beginning-of-line)
        (while (and (verilog--pretty-expr-assignment-found discard-re)
                    (progn
                      (end-of-line)
                      (not (eq pt (point)))))
          (setq pt (point))
          (verilog-forward-syntactic-ws)
          (beginning-of-line))
        (if (region-active-p)
            (min reg-end pt)
          pt)))))

(defun verilog-pretty-expr (&optional quiet)
  "Line up expressions around point.
If QUIET is non-nil, do not print messages showing the progress of line-up."
  (interactive)
  (let* ((basic-complete-pretty-expr-re (if verilog-align-assign-expr
                                            verilog-basic-complete-expr-no-assign-re
                                          verilog-basic-complete-expr-re))
         (complete-pretty-expr-re (concat verilog-extended-complete-re "\\|\\(" basic-complete-pretty-expr-re "\\)"))
         (discard-re (concat "^\\s-*\\(" complete-pretty-expr-re "\\)"))
         rstart rend)
    (save-excursion
      (when (region-active-p)
        (setq rstart (region-beginning))
        (setq rend (region-end))
        (goto-char rstart))
      (unless (verilog-in-comment-or-string-p)
        (beginning-of-line)
        (when (and (verilog--pretty-expr-assignment-found discard-re)
                   (save-excursion
                     (goto-char (match-end 2))
                     (and (not (verilog-in-attribute-p))
                          (not (verilog-in-comment-or-string-p)))))
          (let* ((start (cond (;; Using region
                               (region-active-p)
                               rstart)
                              (;; Parameter list
                               (verilog-in-parenthesis-p)
                               (progn
                                 (verilog-backward-up-list 1)
                                 (forward-char)
                                 (verilog-re-search-forward verilog-assignment-operation-re-2 nil 'move)
                                 (goto-char (match-beginning 0))
                                 (point)))
                              (t ;; Declarations
                               (save-excursion ; BOL of the first line of the assignment block
                                 (beginning-of-line)
                                 (let ((pt (point)))
                                   (verilog-backward-syntactic-ws)
                                   (beginning-of-line)
                                   (while (and (verilog--pretty-expr-assignment-found discard-re)
                                               (not (bobp)))
                                     (setq pt (point))
                                     (verilog-backward-syntactic-ws)
                                     (beginning-of-line)) ; Ack, need to grok `define
                                   pt)))))
                 (startpos (set-marker (make-marker) start))
                 (end (cond (;; Using region
                             (region-active-p)
                             (verilog--pretty-expr-find-end discard-re rend))
                            (;; Parameter list
                             (verilog-in-parenthesis-p)
                             (verilog--pretty-expr-find-end))
                            (t ;; Declarations
                             (verilog--pretty-expr-find-end discard-re))))
		 (endpos (set-marker (make-marker) end))
                 (contains-2-char-operator (string-match "<=" (buffer-substring-no-properties start end))))
            ;; Start with alignment
            (goto-char startpos)
            (unless (save-excursion
                      (beginning-of-line)
                      (looking-at discard-re))
              (verilog-do-indent (verilog-calculate-indent)))
            (when (and (not quiet)
                       (> (- (marker-position endpos) (marker-position startpos)) 100))
              (message "Lining up expressions.. (please stand by)"))
            ;; Set indent to minimum throughout region
            ;; Rely on mark rather than on point as the indentation changes can
            ;; make the older point reference obsolete
            (while (< (point) (marker-position endpos))
              (beginning-of-line)
              (save-excursion
                (if (looking-at verilog-complete-re)
                    (progn (goto-char (marker-position startpos))
                           (verilog-just-one-space verilog-assignment-operation-re-2))
                  (verilog-just-one-space verilog-assignment-operation-re)))
              (verilog-do-indent (verilog-calculate-indent))
              (end-of-line)
              (verilog-forward-syntactic-ws))

            (let ((ind (verilog-get-lineup-indent-2 verilog-assignment-operation-re (marker-position startpos) (marker-position endpos))) ; Find the biggest prefix
                  e)
              ;; Now indent each line.
              (goto-char (marker-position startpos))
              (while (progn
                       (setq e (marker-position endpos))
                       (> e (point)))
                (unless quiet
                  (message " verilog-pretty-expr: %d" (- e (point))))
                (setq e (point))
                (cond
                 ((or (looking-at verilog-assignment-operation-re)
                      (and (verilog-in-parenthesis-p)
                           (looking-at verilog-assignment-operation-re-2)))
                  (goto-char (match-beginning 2))
                  (unless (or (and (verilog-in-parenthesis-p) ; Leave attributes and comparisons alone
                                   (save-excursion ; Allow alignment of some expressions inside param/port list
                                     (verilog-backward-up-list 1)
                                     (verilog-beg-of-statement-1)
                                     (not (looking-at verilog-defun-level-re))))
                              (verilog-in-coverage-p))
                    (if (and contains-2-char-operator
                             (eq (char-after) ?=))
                        (indent-to (1+ ind)) ; Line up the = of the <= with surrounding =
                      (indent-to ind)))
                  (forward-line 1))
                 ((and (save-excursion
                         (verilog-forward-syntactic-ws)
                         (not (looking-at verilog-complete-re)))
                       (verilog-continued-line-1 (marker-position startpos)))
                  (goto-char e)
                  (indent-line-to ind)
                  (forward-line 1))
                 (t ; Must be comment, white space or syntax error
                  (goto-char e)
                  (forward-line 1))))
              ;; Align comments if enabled
              (when verilog-align-decl-expr-comments
                (verilog-align-comments startpos endpos))
              (unless quiet
                (message "")))))))))

(defun verilog-just-one-space (myre)
  "Remove extra spaces around regular expression MYRE."
  (interactive)
  (if (and (not(looking-at verilog-complete-re))
	   (looking-at myre))
      (let ((p1 (match-end 1))
	    (p2 (match-end 2)))
	(progn
	  (goto-char p2)
	  (just-one-space)
	  (goto-char p1)
	  (just-one-space)))))

(defun verilog-indent-declaration (baseind)
  "Indent current lines as declaration.
Line up the variable names based on previous declaration's indentation.
BASEIND is the base indent to offset everything."
  (interactive)
  ;; `ind' is used in expressions stored in `verilog-indent-alist'.
  (verilog--suppressed-warnings ((lexical ind)) (defvar ind))
  (let ((pos (point-marker))
        (m1 (make-marker))
        (in-paren (verilog-parenthesis-depth))
        (val (+ baseind (eval (cdr (assoc 'declaration verilog-indent-alist)))))
        ind)
    (indent-line-to val)
    ;; Use previous declaration (in this module) as template.
    (when (and (or (eq 'all verilog-auto-lineup)
                   (eq 'declarations verilog-auto-lineup))
               ;; Limit alignment to consecutive statements
               (progn
                 (verilog-backward-syntactic-ws)
                 (backward-char)
                 (looking-at ";"))
               (progn
                 (verilog-beg-of-statement)
                 (looking-at (verilog-get-declaration-re)))
               ;; Make sure that we don't jump to an argument list or parameter block if
               ;; we were in a declaration block (not in argument list)
               (or (and in-paren
                        (verilog-parenthesis-depth))
                   (and (not in-paren)
                        (not (verilog-parenthesis-depth))))
               ;; Skip variable declarations inside functions/tasks
               (skip-chars-backward " \t\f")
               (bolp))
      (goto-char (match-end 0))
      (skip-chars-forward " \t")
      (setq ind (current-column))
      (goto-char pos)
      (setq val
            (+ baseind
               (eval (cdr (assoc 'declaration verilog-indent-alist)))))
      (indent-line-to val)
      (if (looking-at (verilog-get-declaration-re))
          (let ((p (match-end 0)))
            (set-marker m1 p)
            (if (verilog-re-search-forward "[[#`]" p 'move)
                (progn
                  (forward-char -1)
                  (just-one-space)
                  (goto-char (marker-position m1))
                  (delete-horizontal-space)
                  (indent-to ind 1))
              (delete-horizontal-space)
              (indent-to ind 1)))
        (when (looking-at (verilog-get-declaration-re))
          (let ((p (match-end 0)))
            (set-marker m1 p)
            (if (verilog-re-search-forward "[[`#]" p 'move)
                (progn
                  (forward-char -1)
                  (just-one-space)
                  (goto-char (marker-position m1))
                  (delete-horizontal-space)
                  (indent-to ind 1))
              (delete-horizontal-space)
              (indent-to ind 1))))))
    (goto-char pos)))

(defun verilog-get-lineup-indent (b edpos)
  "Return the indent level that will line up several lines within the region.
Region is defined by B and EDPOS."
  (save-excursion
    (let ((ind 0) e)
      (goto-char b)
      ;; Get rightmost position
      (while (progn (setq e (marker-position edpos))
		    (< (point) e))
	(when (verilog-re-search-forward (verilog-get-declaration-re 'iface-mp) e 'move)
	  (goto-char (match-end 0))
	  (verilog-backward-syntactic-ws)
	  (if (> (current-column) ind)
	      (setq ind (current-column)))
          (goto-char (match-end 0))
          (forward-line 1)))
      (if (> ind 0)
	  (1+ ind)
	;; No lineup-string found
	(goto-char b)
	(end-of-line)
	(verilog-backward-syntactic-ws)
	;;(skip-chars-backward " \t")
	(1+ (current-column))))))

(defun verilog-get-lineup-indent-2 (regexp beg end)
  "Return the indent level that will line up several lines.
The lineup string is searched using REGEXP within the region between points
BEG and END."
  (save-excursion
    (let ((ind 0))
      (goto-char beg)
      (beginning-of-line)
      ;; Get rightmost position
      (while (< (point) end)
	(when (and (verilog-re-search-forward regexp end 'move)
                   (not (verilog-in-attribute-p))) ; skip attribute exprs
	  (goto-char (match-beginning 2))
          (skip-chars-backward " \t")
	  (if (> (current-column) ind)
	      (setq ind (current-column)))
	  (goto-char (match-end 0))))
      (setq ind (if (> ind 0)
	            (1+ ind)
	          ;; No lineup-string found
	          (goto-char beg)
	          (end-of-line)
	          (skip-chars-backward " \t")
	          (1+ (current-column))))
      ind)))

(defun verilog-search-comment-in-declaration (bound)
  "Move cursor to position of comment in declaration and return point.
BOUND is a buffer position that bounds the search."
  (and (verilog-re-search-forward (verilog-get-declaration-re 'iface-mp) bound 'move)
       (not (looking-at (concat "\\s-*" verilog-comment-start-regexp)))
       (re-search-forward verilog-comment-start-regexp (point-at-eol) :noerror)))

(defun verilog-get-comment-align-indent (b endpos)
  "Return the indent level that will line up comments within the region.
Region is defined by B and ENDPOS."
  (save-excursion
    (let ((ind 0)
          e comm-ind)
      (goto-char b)
      ;; Get rightmost position
      (while (progn (setq e (marker-position endpos))
                    (< (point) e))
        (when (verilog-search-comment-in-declaration e)
          (end-of-line)
          (verilog-backward-syntactic-ws)
          (setq comm-ind (1+ (current-column)))
          (when (> comm-ind ind)
            (setq ind comm-ind)))
        (forward-line 1))
      ind)))

(defun verilog-comment-depth (type val)
  "A useful mode debugging aide.  TYPE and VAL are comments for insertion."
  (save-excursion
    (let
	((b (prog2
		(beginning-of-line)
		(point-marker)
	      (end-of-line))))
      (if (re-search-backward " /\\* [#-]# [a-zA-Z]+ [0-9]+ ## \\*/" b t)
	  (progn
	    (replace-match " /* -#  ## */")
	    (end-of-line))
	(progn
	  (end-of-line)
	  (insert " /* ##  ## */"))))
    (backward-char 6)
    (insert
     (format "%s %d" type val))))

(defun verilog-indent-ignore-p ()
  "Return non-nil if current line should ignore indentation."
  (or (and verilog-indent-ignore-multiline-defines
           ;; Line with multiline define, ends with "\" or "\" plus trailing whitespace
           (or (save-excursion
                 (verilog-re-search-forward ".*\\\\\\s-*$" (line-end-position) t))
               (save-excursion  ; Last line after multiline define
                 (verilog-backward-syntactic-ws)
                 (unless (bobp)
                   (backward-char))
                 (looking-at "\\\\"))))
      (and verilog-indent-ignore-regexp ; Ignore lines according to specified regexp
           (looking-at verilog-indent-ignore-regexp))))


;;; Completion:
;;
(defvar verilog-str nil)
(defvar verilog-all nil)
(defvar verilog-buffer-to-use nil)
(defvar verilog-toggle-completions nil
  "Non-nil means \\<verilog-mode-map>\\[verilog-complete-word] should try all possible completions one by one.
Repeated use of \\[verilog-complete-word] will show you all of them.
Normally, when there is more than one possible completion,
it displays a list of all possible completions.")
(when (boundp 'completion-cycle-threshold)
  (make-obsolete-variable
   'verilog-toggle-completions 'completion-cycle-threshold "26.1"))


(defvar verilog-type-keywords
  '(
    "and" "buf" "bufif0" "bufif1" "cmos" "defparam" "inout" "input"
    "integer" "localparam" "logic" "mailbox" "nand" "nmos" "nor" "not" "notif0"
    "notif1" "or" "output" "parameter" "pmos" "pull0" "pull1" "pulldown" "pullup"
    "rcmos" "real" "realtime" "reg" "rnmos" "rpmos" "rtran" "rtranif0"
    "rtranif1" "semaphore" "time" "tran" "tranif0" "tranif1" "tri" "tri0" "tri1"
    "triand" "trior" "trireg" "wand" "wire" "wor" "xnor" "xor"
    )
  "Keywords for types used when completing a word in a declaration or parmlist.
\(integer, real, reg...)")

(defvar verilog-cpp-keywords
  '("connectmodule" "module" "macromodule" "primitive" "timescale" "define" "ifdef" "ifndef" "else"
    "endif")
  "Keywords to complete when at first word of a line in declarative scope.
\(initial, always, begin, assign...)
The procedures and variables defined within the Verilog program
will be completed at runtime and should not be added to this list.")

(defvar verilog-defun-keywords
  (append
   '(
     "always" "always_comb" "always_ff" "always_latch" "analog" "assign"
     "begin" "end" "connectmodule" "endconnectmodule" "generate" "endgenerate" "module" "endmodule"
     "specify" "endspecify" "function" "endfunction" "initial" "final"
     "task" "endtask" "primitive" "endprimitive"
     )
   verilog-type-keywords)
  "Keywords to complete when at first word of a line in declarative scope.
\(initial, always, begin, assign...)
The procedures and variables defined within the Verilog program
will be completed at runtime and should not be added to this list.")

(defvar verilog-block-keywords
  '(
    "begin" "break" "case" "continue" "else" "end" "endfunction"
    "endgenerate" "endinterface" "endpackage" "endspecify" "endtask"
    "for" "fork" "if" "join" "join_any" "join_none" "repeat" "return"
    "while")
  "Keywords to complete when at first word of a line in behavioral scope.
\(begin, if, then, else, for, fork...)
The procedures and variables defined within the Verilog program
will be completed at runtime and should not be added to this list.")

(defvar verilog-tf-keywords
  '("begin" "break" "fork" "join" "join_any" "join_none" "case" "end" "endtask" "endfunction" "if" "else" "for" "while" "repeat")
  "Keywords to complete when at first word of a line in a task or function.
\(begin, if, then, else, for, fork.)
The procedures and variables defined within the Verilog program
will be completed at runtime and should not be added to this list.")

(defvar verilog-case-keywords
  '("begin" "fork" "join" "join_any" "join_none" "case" "end" "endcase" "if" "else" "for" "repeat")
  "Keywords to complete when at first word of a line in case scope.
\(begin, if, then, else, for, fork...)
The procedures and variables defined within the Verilog program
will be completed at runtime and should not be added to this list.")

(defvar verilog-separator-keywords
  '("else" "then" "begin")
  "Keywords to complete when NOT standing at the first word of a statement.
\(else, then, begin...)
Variables and function names defined within the Verilog program
will be completed at runtime and should not be added to this list.")

(defvar verilog-gate-ios
  ;; All these have an implied {"input"...} at the end
  '(("and"	"output")
    ("buf"	"output")
    ("bufif0"	"output")
    ("bufif1"	"output")
    ("cmos"	"output")
    ("nand"	"output")
    ("nmos"	"output")
    ("nor"	"output")
    ("not"	"output")
    ("notif0"	"output")
    ("notif1"	"output")
    ("or"	"output")
    ("pmos"	"output")
    ("pulldown"	"output")
    ("pullup"	"output")
    ("rcmos"	"output")
    ("rnmos"	"output")
    ("rpmos"	"output")
    ("rtran"	"inout" "inout")
    ("rtranif0"	"inout" "inout")
    ("rtranif1"	"inout" "inout")
    ("tran"	"inout" "inout")
    ("tranif0"	"inout" "inout")
    ("tranif1"	"inout" "inout")
    ("xnor"	"output")
    ("xor"	"output"))
  "Map of direction for each positional argument to each gate primitive.")

(defvar verilog-gate-keywords (mapcar #'car verilog-gate-ios)
  "Keywords for gate primitives.")

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
  "Build regular expression for module/task/function names.
TYPE is `module', `tf' for task or function, or t if unknown."
  (if (string= verilog-str "")
      (setq verilog-str "[a-zA-Z_]"))
  (let ((verilog-str
         (concat (cond
                  ((eq type 'module) "\\<\\(module\\|connectmodule\\)\\s +")
                  ((eq type 'tf) "\\<\\(task\\|function\\)\\s +")
                  (t "\\<\\(task\\|function\\|module\\|connectmodule\\)\\s +"))
                 "\\<\\(" verilog-str "[a-zA-Z0-9_.]*\\)\\>"))
	match)

    (save-excursion
      (if (not (looking-at verilog-defun-re))
	  (verilog-re-search-backward verilog-defun-re nil t))
      (forward-char 1)

      ;; Search through all reachable functions
      (goto-char (point-min))
      (while (verilog-re-search-forward verilog-str (point-max) t)
        (setq match (buffer-substring (match-beginning 2)
				      (match-end 2)))
        (setq verilog-all (cons match verilog-all))))))

(defun verilog-get-completion-decl (end)
  "Macro for searching through current declaration (var, type or const)
for matches of `str' and adding the occurrence tp `all' through point END."
  (let ((re (verilog-get-declaration-re))
	decl-end match)
    ;; Traverse lines
    (while (and (< (point) end)
		(verilog-re-search-forward re end t))
      ;; Traverse current line
      (setq decl-end (save-excursion (verilog-declaration-end)))
      (while (and (verilog-re-search-forward verilog-identifier-sym-re decl-end t)
		  (not (match-end 1)))
	(setq match (buffer-substring (match-beginning 0) (match-end 0)))
	(if (string-match (concat "\\<" verilog-str) match)
            (setq verilog-all (cons match verilog-all))))
      (forward-line 1)))
  verilog-all)

(defun verilog-var-completion ()
  "Calculate all possible completions for variables (or constants)."
  (let ((start (point)))
    ;; Search for all reachable var declarations
    (verilog-re-search-backward verilog-defun-re nil 'move)
    (save-excursion
      ;; Check var declarations
      (verilog-get-completion-decl start))))

(defun verilog-keyword-completion (keyword-list)
  "Give list of all possible completions of keywords in KEYWORD-LIST."
  (dolist (s keyword-list)
    (if (string-match (concat "\\<" verilog-str) s)
        (push s verilog-all))))


(defun verilog-completion (str pred flag)
  "Completion table for Verilog tokens.
Function passed to `completing-read', `try-completion' or `all-completions'.
Called to get completion on STR.
If FLAG is t, the function returns a list of all possible completions.
If FLAG is nil it returns a string, the longest possible completion,
or t if STR is an exact match.
If FLAG is `lambda', the function returns t if STR is an exact match,
nil otherwise."
  (let ((verilog-str str)
        (verilog-all nil))
    ;; Set buffer to use for searching labels. This should be set
    ;; within functions which use verilog-completions
    (with-current-buffer verilog-buffer-to-use

      ;; Determine what should be completed
      (let ((state (car (verilog-calculate-indent))))
	(cond ((eq state 'defun)
	       (save-excursion (verilog-var-completion))
	       (verilog-func-completion 'module)
	       (verilog-keyword-completion verilog-defun-keywords))

	      ((eq state 'behavioral)
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

	      ((eq state 'cpp)
	       (save-excursion (verilog-var-completion))
	       (verilog-keyword-completion verilog-cpp-keywords))

	      ((eq state 'cparenexp)
	       (save-excursion (verilog-var-completion)))

	      (t;--Anywhere else
	       (save-excursion (verilog-var-completion))
	       (verilog-func-completion 'both)
	       (verilog-keyword-completion verilog-separator-keywords))))

      ;; Now we have built a list of all matches. Give response to caller
      (verilog--complete-with-action flag verilog-all verilog-str pred))))


(defalias 'verilog--complete-with-action
  (if (fboundp 'complete-with-action)
      #'complete-with-action
    (lambda (flag collection string _predicate)
      (cond ((or (equal flag 'lambda) (null flag))
            ;; This was not called by all-completions
            (if (null collection)
                ;; Return nil if there was no matching label
                nil
              ;; Get longest string common in the labels
              (let* ((elm (cdr collection))
                     (match (car collection))
                     (min (length match))
                     tmp)
                (if (string= match string)
                    ;; Return t if first match was an exact match
                    (setq match t)
                  (while (not (null elm))
                    ;; Find longest common string
                    (if (< (setq tmp (verilog-string-diff match (car elm)))
                           min)
                        (progn
                          (setq min tmp)
                          (setq match (substring match 0 min))))
                    ;; Terminate with match=t if this is an exact match
                    (if (string= (car elm) string)
                        (progn
                          (setq match t)
                          (setq elm nil))
                      (setq elm (cdr elm)))))
                ;; If this is a test just for exact match, return nil or t
                (if (and (equal flag 'lambda) (not (equal match 't)))
                    nil
                  match))))
           ;; If flag is t, this was called by all-completions. Return
           ;; list of all possible completions
           (flag
            collection)))))

(defvar verilog-last-word-numb 0)
(defvar verilog-last-word-shown nil)
(defvar verilog-last-completions nil)

(defun verilog-completion-at-point ()
  "Used as an element of `completion-at-point-functions'.
\(See also `verilog-type-keywords' and
`verilog-separator-keywords'.)"
  (let* ((b (save-excursion (skip-chars-backward "a-zA-Z0-9_") (point)))
         (e (save-excursion (skip-chars-forward "a-zA-Z0-9_") (point)))
         (verilog-str (buffer-substring b e))
         ;; The following variable is used in verilog-completion
         (verilog-buffer-to-use (current-buffer))
         (allcomp (if (and verilog-toggle-completions
                           (string= verilog-last-word-shown verilog-str))
                      verilog-last-completions
                    (all-completions verilog-str #'verilog-completion))))
    (list b e allcomp)))

(defun verilog-complete-word ()
  "Complete word at current point.
\(See also `verilog-toggle-completions', `verilog-type-keywords',
and `verilog-separator-keywords'.)"
  ;; NOTE: This is just a fallback for Emacs versions lacking
  ;; `completion-at-point'.
  (interactive)
  (let* ((comp-info (verilog-completion-at-point))
         (b (nth 0 comp-info))
	 (e (nth 1 comp-info))
	 (verilog-str (buffer-substring b e))
	 (allcomp (nth 2 comp-info))
	 (match (if verilog-toggle-completions
                   "" (try-completion verilog-str allcomp))))
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
      ;; The other form of completion does not necessarily do that.

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
	     ;; Wait for a key press. Then delete *Completion*  window
	     (momentary-string-display "" (point))
	     (verilog-quit-window nil (get-buffer-window "*Completions*"))
	     )))))

(defun verilog-show-completions ()
  "Show all possible completions at current point."
  ;; NOTE: This is just a fallback for Emacs versions lacking
  ;; `completion-help-at-point'.
  (interactive)
  ;; Show possible completions in a temporary buffer.
  (with-output-to-temp-buffer "*Completions*"
    (display-completion-list (nth 2 (verilog-completion-at-point))))
  ;; Wait for a key press. Then delete *Completion*  window
  (momentary-string-display "" (point))
  (verilog-quit-window nil (get-buffer-window "*Completions*")))

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
With optional second ARG non-nil, STR is the complete name of the instruction."
  (unless arg
    (setq str (concat str "[a-zA-Z0-9_]*")))
  (concat "^\\s-*\\(function\\|task\\|module\\)[ \t]+\\(?:\\(?:static\\|automatic\\)\\s-+\\)?\\(" str "\\)\\>"))

(defun verilog-comp-defun (str pred flag)
  "Completion table for function names.
Function passed to `completing-read', `try-completion' or `all-completions'.
Returns a completion on any function name based on STR prefix.
If FLAG is t, the function returns a list of all possible completions.
If it is nil it returns a string, the longest possible completion,
or t if STR is an exact match.
If FLAG is `lambda', the function returns t if STR is an exact match,
nil otherwise."
  (let ((verilog-all nil)
       (verilog-str str)
       match)

    ;; Set buffer to use for searching labels. This should be set
    ;; within functions which use verilog-completions
    (with-current-buffer verilog-buffer-to-use

      (let ((verilog-str verilog-str))
	;; Build regular expression for functions
       (setq verilog-str
             (verilog-build-defun-re (if (string= verilog-str "")
                                         "[a-zA-Z_]"
                                       verilog-str)))
	(goto-char (point-min))

	;; Build a list of all possible completions
	(while (verilog-re-search-forward verilog-str nil t)
	  (setq match (buffer-substring (match-beginning 2) (match-end 2)))
         (setq verilog-all (cons match verilog-all))))

      ;; Now we have built a list of all matches. Give response to caller
      (verilog--complete-with-action flag verilog-all verilog-str pred))))

(defun verilog-goto-defun ()
  "Move to specified Verilog module/interface/task/function.
The default is a name found in the buffer around point.
If search fails, other files are checked based on
`verilog-library-flags'."
  (interactive)
  (let* ((default (verilog-get-default-symbol))
	 ;; The following variable is used in verilog-comp-function
	 (verilog-buffer-to-use (current-buffer))
         (label
          (completing-read (cond ((fboundp 'format-prompt)
                                  ;; `format-prompt' is new in Emacs 28.1.
                                  (format-prompt "Goto-Label" default))
                                 ((not (string= default ""))
                                  (concat "Goto-Label (default " default "): "))
                                 (t "Goto-Label: "))
                           #'verilog-comp-defun nil nil ""))
	 pt)
    ;; Make sure library paths are correct, in case need to resolve module
    (verilog-auto-reeval-locals)
    (verilog-getopt-flags)
    ;; If there was no response on prompt, use default value
    (if (string= label "")
	(setq label default))
    ;; Goto right place in buffer if label is not an empty string
    (or (string= label "")
	(progn
	  (save-excursion
	    (goto-char (point-min))
	    (setq pt
		  (re-search-forward (verilog-build-defun-re label t) nil t)))
	  (when pt
	    (goto-char pt)
	    (beginning-of-line))
	  pt)
	(verilog-goto-defun-file label))))

;; Eliminate compile warning
(defvar occur-pos-list)

(defun verilog-showscopes ()
  "List all scopes in this module."
  (interactive)
  (let ((buffer (current-buffer))
	(linenum 1)
	(nlines 0)
	(first 1)
	(prevpos (point-min))
        (final-context-start (make-marker))
       (regexp "\\(\\(connect\\)?module\\s-+\\w+\\s-*(\\)\\|\\(\\w+\\s-+\\w+\\s-*(\\)"))
    (with-output-to-temp-buffer "*Occur*"
      (save-excursion
	(message "Searching for %s ..." regexp)
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
           (setq tem (make-marker))
           (set-marker tem (point))
           (with-current-buffer standard-output
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


;; Highlight helper functions
(defconst verilog-directive-regexp "\\(translate\\|coverage\\|lint\\)_")

(defun verilog-within-translate-off ()
  "Return point if within translate-off region, else nil."
  (and (save-excursion
	 (re-search-backward
	  (concat "//.*" verilog-directive-regexp "\\(on\\|off\\)\\>")
	  nil t))
       (equal "off" (match-string 2))
       (point)))

(defun verilog-start-translate-off (limit)
  "Return point before translate-off directive if before LIMIT, else nil."
  (when (re-search-forward
         (concat "//.*" verilog-directive-regexp "off\\>")
         limit t)
    (match-beginning 0)))

(defun verilog-back-to-start-translate-off (limit)
  "Return point before translate-off directive if before LIMIT, else nil."
  (when (re-search-backward
         (concat "//.*" verilog-directive-regexp "off\\>")
         limit t)
    (match-beginning 0)))

(defun verilog-end-translate-off (limit)
  "Return point after translate-on directive if before LIMIT, else nil."

  (re-search-forward (concat
		      "//.*" verilog-directive-regexp "on\\>") limit t))

(defun verilog-match-translate-off (limit)
  "Match a translate-off block, setting `match-data' and returning t, else nil.
Bound search by LIMIT."
  (when (< (point) limit)
    (let ((start (or (verilog-within-translate-off)
		     (verilog-start-translate-off limit)))
	  (case-fold-search t))
      (when start
	(let ((end (or (verilog-end-translate-off limit) limit)))
	  (set-match-data (list start end))
	  (goto-char end))))))

(defun verilog-font-lock-match-item (limit)
  "Match, and move over, any declaration item after point.
Bound search by LIMIT.  Adapted from
`font-lock-match-c-style-declaration-item-and-skip-to-next'."
  (condition-case nil
      (save-restriction
	(narrow-to-region (point-min) limit)
	;; match item
	(when (looking-at "\\s-*\\([a-zA-Z]\\w*\\)")
	  (save-match-data
	    (goto-char (match-end 1))
	    ;; move to next item
	    (if (looking-at "\\(\\s-*,\\)")
		(goto-char (match-end 1))
	      (end-of-line) t))))
    (error nil)))


;; Added by Subbu Meiyappan for Header

(defun verilog-header ()
  "Insert a standard Verilog file header.
See also `verilog-sk-header' for an alternative format."
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
// Copyright (c) <copydate> by <company> This model is the confidential and
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
    (verilog-insert-date)
    (search-forward "<moddate>") (replace-match "" t t)
    (verilog-insert-date)
    (search-forward "<copydate>") (replace-match "" t t)
    (verilog-insert-year)
    (search-forward "<modhist>") (replace-match "" t t)
    (verilog-insert-date)
    (insert " : created")
    (goto-char start)
    (let (string)
      (setq string (read-string "title: "))
      (search-forward "<title>")
      (replace-match string t t)
      (setq string (read-string "project: " verilog-project))
      (setq verilog-project string)
      (search-forward "<project>")
      (replace-match string t t)
      (setq string (read-string "Company: " verilog-company))
      (setq verilog-company string)
      (search-forward "<company>")
      (replace-match string t t)
      (search-forward "<company>")
      (replace-match string t t)
      (search-forward "<company>")
      (replace-match string t t)
      (search-backward "<description>")
      (replace-match "" t t))))

;; verilog-header Uses the verilog-insert-date function

(defun verilog-insert-date ()
  "Insert date from the system."
  (interactive)
  (if verilog-date-scientific-format
      (insert (format-time-string "%Y/%m/%d"))
    (insert (format-time-string "%d.%m.%Y"))))

(defun verilog-insert-year ()
  "Insert year from the system."
  (interactive)
  (insert (format-time-string "%Y")))


;;; Signal list parsing:
;;

;; Elements of a signal list
;; Unfortunately we use 'assoc' on this, so can't be a vector
(defsubst verilog-sig-new (name bits comment mem enum signed type multidim modport)
  (list name bits comment mem enum signed type multidim modport))
(defsubst verilog-sig-new-renamed (name old-sig)
  (cons name (cdr old-sig)))
(defsubst verilog-sig-name (sig)
  (car sig))
(defsubst verilog-sig-bits (sig)  ; First element of packed array (pre signal-name)
  (nth 1 sig))
(defsubst verilog-sig-comment (sig)
  (nth 2 sig))
(defsubst verilog-sig-memory (sig)  ; Unpacked array (post signal-name)
  (nth 3 sig))
(defsubst verilog-sig-enum (sig)
  (nth 4 sig))
(defsubst verilog-sig-signed (sig)
  (nth 5 sig))
(defsubst verilog-sig-type (sig)
  (nth 6 sig))
(defsubst verilog-sig-type-set (sig type)
  (setcar (nthcdr 6 sig) type))
(defsubst verilog-sig-multidim (sig)  ; Second and additional elements of packed array
  (nth 7 sig))
(defsubst verilog-sig-multidim-string (sig)
  (if (verilog-sig-multidim sig)
      (let ((str "") (args (verilog-sig-multidim sig)))
	(while args
	  (setq str (concat (car args) str))
	  (setq args (cdr args)))
	str)))
(defsubst verilog-sig-modport (sig)
  (nth 8 sig))
(defsubst verilog-sig-width (sig)
  (verilog-make-width-expression (verilog-sig-bits sig)))

(defsubst verilog-alw-new (outputs-del outputs-imm temps inputs)
  (vector outputs-del outputs-imm temps inputs))
(defsubst verilog-alw-get-outputs-delayed (sigs)
  (aref sigs 0))
(defsubst verilog-alw-get-outputs-immediate (sigs)
  (aref sigs 1))
(defsubst verilog-alw-get-temps (sigs)
  (aref sigs 2))
(defsubst verilog-alw-get-inputs (sigs)
  (aref sigs 3))
(defsubst verilog-alw-get-uses-delayed (sigs)
  (aref sigs 0))

(defsubst verilog-modport-new (name clockings decls)
  (list name clockings decls))
(defsubst verilog-modport-name (sig)
  (car sig))
(defsubst verilog-modport-clockings (sig)
  (nth 1 sig))  ; Returns list of names
(defsubst verilog-modport-clockings-add (sig val)
  (setcar (nthcdr 1 sig) (cons val (nth 1 sig))))
(defsubst verilog-modport-decls (sig)
  (nth 2 sig))  ; Returns verilog-decls-* structure
(defsubst verilog-modport-decls-set (sig val)
  (setcar (nthcdr 2 sig) val))

(defsubst verilog-modi-new (name fob pt type)
  (vector name fob pt type))
(defsubst verilog-modi-name (modi)
  (aref modi 0))
(defsubst verilog-modi-file-or-buffer (modi)
  (aref modi 1))
(defsubst verilog-modi-get-point (modi)
  (aref modi 2))
(defsubst verilog-modi-get-type (modi)  ; "module" or "interface"
  (aref modi 3))
(defsubst verilog-modi-get-decls (modi)
  (verilog-modi-cache-results modi 'verilog-read-decls))
(defsubst verilog-modi-get-sub-decls (modi)
  (verilog-modi-cache-results modi 'verilog-read-sub-decls))

;; Signal reading for given module
;; Note these all take modi's - as returned from verilog-modi-current
(defsubst verilog-decls-new (out inout in vars modports assigns consts gparams interfaces)
  (vector out inout in vars modports assigns consts gparams interfaces))
(defsubst verilog-decls-append (a b)
  (cond ((not a) b) ((not b) a)
	(t (vector (append (aref a 0) (aref b 0))   (append (aref a 1) (aref b 1))
		   (append (aref a 2) (aref b 2))   (append (aref a 3) (aref b 3))
		   (append (aref a 4) (aref b 4))   (append (aref a 5) (aref b 5))
		   (append (aref a 6) (aref b 6))   (append (aref a 7) (aref b 7))
		   (append (aref a 8) (aref b 8))))))
(defsubst verilog-decls-get-outputs (decls)
  (aref decls 0))
(defsubst verilog-decls-get-inouts (decls)
  (aref decls 1))
(defsubst verilog-decls-get-inputs (decls)
  (aref decls 2))
(defsubst verilog-decls-get-vars (decls)
  (aref decls 3))
(defsubst verilog-decls-get-modports (decls)  ; Also for clocking blocks; contains another verilog-decls struct
  (aref decls 4))  ; Returns verilog-modport* structure
(defsubst verilog-decls-get-assigns (decls)
  (aref decls 5))
(defsubst verilog-decls-get-consts (decls)
  (aref decls 6))
(defsubst verilog-decls-get-gparams (decls)
  (aref decls 7))
(defsubst verilog-decls-get-interfaces (decls)
  (aref decls 8))


(defsubst verilog-subdecls-new (out inout in intf intfd)
  (vector out inout in intf intfd))
(defsubst verilog-subdecls-get-outputs (subdecls)
  (aref subdecls 0))
(defsubst verilog-subdecls-get-inouts (subdecls)
  (aref subdecls 1))
(defsubst verilog-subdecls-get-inputs (subdecls)
  (aref subdecls 2))
(defsubst verilog-subdecls-get-interfaces (subdecls)
  (aref subdecls 3))
(defsubst verilog-subdecls-get-interfaced (subdecls)
  (aref subdecls 4))

(defun verilog-signals-from-signame (signame-list)
  "Return signals in standard form from SIGNAME-LIST, a simple list of names."
  (mapcar (lambda (name) (verilog-sig-new name nil nil nil nil nil nil nil nil))
	  signame-list))

(defun verilog-signals-in (in-list not-list)
  "Return list of signals in IN-LIST that are also in NOT-LIST.
Also remove any duplicates in IN-LIST.
Signals must be in standard (base vector) form."
  ;; This function is hot, so implemented as O(1)
  (cond ((eval-when-compile (fboundp 'make-hash-table))
	 (let ((ht (make-hash-table :test 'equal :rehash-size 4.0))
	       (ht-not (make-hash-table :test 'equal :rehash-size 4.0))
	       out-list)
	   (while not-list
	     (puthash (car (car not-list)) t ht-not)
	     (setq not-list (cdr not-list)))
	   (while in-list
	     (when (and (gethash (verilog-sig-name (car in-list)) ht-not)
			(not (gethash (verilog-sig-name (car in-list)) ht)))
	       (setq out-list (cons (car in-list) out-list))
	       (puthash (verilog-sig-name (car in-list)) t ht))
	     (setq in-list (cdr in-list)))
	   (nreverse out-list)))
	;; Slower Fallback if no hash tables (pre Emacs 21.1/XEmacs 21.4)
	(t
	 (let (out-list)
	   (while in-list
	     (if (and (assoc (verilog-sig-name (car in-list)) not-list)
		      (not (assoc (verilog-sig-name (car in-list)) out-list)))
		 (setq out-list (cons (car in-list) out-list)))
	     (setq in-list (cdr in-list)))
	   (nreverse out-list)))))
;;(verilog-signals-in '(("A" "") ("B" "") ("DEL" "[2:3]")) '(("DEL" "") ("C" "")))

(defun verilog-signals-not-in (in-list not-list)
  "Return list of signals in IN-LIST that aren't also in NOT-LIST.
Also remove any duplicates in IN-LIST.
Signals must be in standard (base vector) form."
  ;; This function is hot, so implemented as O(1)
  (cond ((eval-when-compile (fboundp 'make-hash-table))
	 (let ((ht (make-hash-table :test 'equal :rehash-size 4.0))
	       out-list)
	   (while not-list
	     (puthash (car (car not-list)) t ht)
	     (setq not-list (cdr not-list)))
	   (while in-list
	     (when (not (gethash (verilog-sig-name (car in-list)) ht))
	       (setq out-list (cons (car in-list) out-list))
	       (puthash (verilog-sig-name (car in-list)) t ht))
	     (setq in-list (cdr in-list)))
	   (nreverse out-list)))
	;; Slower Fallback if no hash tables (pre Emacs 21.1/XEmacs 21.4)
	(t
	 (let (out-list)
	   (while in-list
	     (if (and (not (assoc (verilog-sig-name (car in-list)) not-list))
		      (not (assoc (verilog-sig-name (car in-list)) out-list)))
		 (setq out-list (cons (car in-list) out-list)))
	     (setq in-list (cdr in-list)))
	   (nreverse out-list)))))
;;(verilog-signals-not-in '(("A" "") ("B" "") ("DEL" "[2:3]")) '(("DEL" "") ("EXT" "")))

(defun verilog-signals-not-in-struct (in-list not-list)
  "Return list of signals in IN-LIST that aren't also in NOT-LIST.
Also remove any duplicates in IN-LIST.
Any structure in not-list will remove all members in in-list.
Signals must be in standard (base vector) form."
  (cond ((eval-when-compile (fboundp 'make-hash-table))
	 (let ((ht (make-hash-table :test 'equal :rehash-size 4.0))
	       out-list addit nm)
	   (while not-list
	     (puthash (car (car not-list)) t ht)
	     (setq not-list (cdr not-list)))
	   (while in-list
	     (setq nm (verilog-sig-name (car in-list)))
	     (when (not (gethash nm ht))
	       (setq addit t)
	       (while (string-match "^\\([^\\].*\\)\\.[^.]+$" nm)
		 (setq nm (match-string 1 nm))
		 (setq addit (and addit
				  (not (gethash nm ht)))))
	       (when addit
		 (setq out-list (cons (car in-list) out-list))
		 (puthash (verilog-sig-name (car in-list)) t ht)))
	     (setq in-list (cdr in-list)))
	   (nreverse out-list)))
	;; Slower Fallback if no hash tables (pre Emacs 21.1/XEmacs 21.4)
	(t
	 (let (out-list addit nm)
	   (while in-list
	     (setq nm (verilog-sig-name (car in-list)))
	     (when (and (not (assoc nm not-list))
			(not (assoc nm out-list)))
	       (setq addit t)
	       (while (string-match "^\\([^\\].*\\)\\.[^.]+$" nm)
		 (setq nm (match-string 1 nm))
		 (setq addit (and addit
				  (not (assoc nm not-list)))))
	       (when addit
		 (setq out-list (cons (car in-list) out-list))))
	     (setq in-list (cdr in-list)))
	   (nreverse out-list)))))
;;(verilog-signals-not-in-struct '(("A" "") ("B" "") ("DEL.SUB.A" "[2:3]")) '(("DEL.SUB" "") ("EXT" "")))

(defun verilog-signals-memory (in-list)
  "Return list of signals in IN-LIST that are memorized (multidimensional)."
  (let (out-list)
    (while in-list
      (if (nth 3 (car in-list))
	  (setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    out-list))
;;(verilog-signals-memory '(("A" nil nil "[3:0]")) '(("B" nil nil nil)))

(defun verilog-signals-sort-compare (a b)
  "Compare signal A and B for sorting."
  (string< (verilog-sig-name a) (verilog-sig-name b)))

(defun verilog-signals-not-params (in-list)
  "Return list of signals in IN-LIST that aren't parameters or numeric constants."
  (let (out-list)
    (while in-list
      ;; Namespace intentionally short for AUTOs and compatibility
      (unless (boundp (intern (concat "vh-" (verilog-sig-name (car in-list)))))
	(setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    (nreverse out-list)))

(defun verilog-signals-with (func in-list)
  "Return list of signals where FUNC is true executed on each signal in IN-LIST."
  (let (out-list)
    (while in-list
      (when (funcall func (car in-list))
	(setq out-list (cons (car in-list) out-list)))
      (setq in-list (cdr in-list)))
    (nreverse out-list)))

(defun verilog-signals-combine-bus (in-list)
  "Return a list of signals in IN-LIST, with buses combined.
Duplicate signals are also removed.  For example A[2] and A[1] become A[2:1]."
  (let (combo
        buswarn
	out-list
	sig highbit lowbit		; Temp information about current signal
	sv-name sv-highbit sv-lowbit	; Details about signal we are forming
	sv-comment sv-memory sv-enum sv-signed sv-type sv-multidim sv-busstring
	sv-modport
	bus)
    ;; Shove signals so duplicated signals will be adjacent
    (setq in-list (sort in-list #'verilog-signals-sort-compare))
    (while in-list
      (setq sig (car in-list))
      ;; No current signal; form from existing details
      (unless sv-name
	(setq sv-name    (verilog-sig-name sig)
	      sv-highbit nil
	      sv-busstring nil
	      sv-comment (verilog-sig-comment sig)
	      sv-memory  (verilog-sig-memory sig)
	      sv-enum    (verilog-sig-enum sig)
	      sv-signed  (verilog-sig-signed sig)
	      sv-type    (verilog-sig-type sig)
	      sv-multidim (verilog-sig-multidim sig)
	      sv-modport  (verilog-sig-modport sig)
	      combo ""
	      buswarn ""))
      ;; Extract bus details
      (setq bus (verilog-sig-bits sig))
      (setq bus (and bus (verilog-simplify-range-expression bus)))
      (cond ((and bus
		  (or (and (string-match "^\\[\\([0-9]+\\):\\([0-9]+\\)\\]$" bus)
			   (setq highbit (string-to-number (match-string 1 bus))
				 lowbit  (string-to-number
					  (match-string 2 bus))))
		      (and (string-match "^\\[\\([0-9]+\\)\\]$" bus)
			   (setq highbit (string-to-number (match-string 1 bus))
				 lowbit  highbit))))
	     ;; Combine bits in bus
	     (if sv-highbit
		 (setq sv-highbit (max highbit sv-highbit)
		       sv-lowbit  (min lowbit  sv-lowbit))
	       (setq sv-highbit highbit
		     sv-lowbit  lowbit)))
	    (bus
	     ;; String, probably something like `preproc:0
	     (setq sv-busstring bus)))
      ;; Peek ahead to next signal
      (setq in-list (cdr in-list))
      (setq sig (car in-list))
      (cond ((and sig (equal sv-name (verilog-sig-name sig)))
	     ;; Combine with this signal
	     (when (and sv-busstring
			(not (equal sv-busstring (verilog-sig-bits sig))))
               (when nil  ; Debugging
		 (message (concat "Warning, can't merge into single bus `%s%s'"
				  ", the AUTOs may be wrong")
			  sv-name bus))
	       (setq buswarn ", Couldn't Merge"))
	     (if (verilog-sig-comment sig) (setq combo ", ..."))
	     (setq sv-memory (or sv-memory (verilog-sig-memory sig))
		   sv-enum   (or sv-enum   (verilog-sig-enum sig))
		   sv-signed (or sv-signed (verilog-sig-signed sig))
                   sv-type   (or sv-type   (verilog-sig-type sig))
                   sv-multidim (or sv-multidim (verilog-sig-multidim sig))
                   sv-modport  (or sv-modport  (verilog-sig-modport sig))))
	    ;; Doesn't match next signal, add to queue, zero in prep for next
	    ;; Note sig may also be nil for the last signal in the list
	    (t
	     (setq out-list
		   (cons (verilog-sig-new
			  sv-name
			  (or sv-busstring
			      (if sv-highbit
				  (concat "[" (int-to-string sv-highbit) ":"
					  (int-to-string sv-lowbit) "]")))
			  (concat sv-comment combo buswarn)
			  sv-memory sv-enum sv-signed sv-type sv-multidim sv-modport)
			 out-list)
		   sv-name nil))))
    ;;
    out-list))

(defun verilog-sig-tieoff (sig)
  "Return tieoff expression for given SIG, with appropriate width.
Tieoff value uses `verilog-active-low-regexp' and
`verilog-auto-reset-widths'."
  (concat
   (if (and verilog-active-low-regexp
	    (verilog-string-match-fold verilog-active-low-regexp (verilog-sig-name sig)))
       "~" "")
   (cond ((not verilog-auto-reset-widths)
	  "0")
	 ((equal verilog-auto-reset-widths 'unbased)
	  "'0")
	 ;; Else presume verilog-auto-reset-widths is true
	 (t
	  (let* ((width (verilog-sig-width sig)))
	    (cond ((not width)
		   "'0/*NOWIDTH*/")
		  ((string-match "^[0-9]+$" width)
		   (concat width (if (verilog-sig-signed sig) "'sh0" "'h0")))
		  (t
		   (concat "{" width "{1'b0}}"))))))))

;;
;; Dumping
;;

(defun verilog-decls-princ (decls &optional header prefix)
  "For debug, dump the `verilog-read-decls' structure DECLS.
Use optional HEADER and PREFIX."
  (when decls
    (if header (princ header))
    (setq prefix (or prefix ""))
    (verilog-signals-princ (verilog-decls-get-outputs decls)
			   (concat prefix "Outputs:\n") (concat prefix "  "))
    (verilog-signals-princ (verilog-decls-get-inouts decls)
			   (concat prefix "Inout:\n") (concat prefix "  "))
    (verilog-signals-princ (verilog-decls-get-inputs decls)
			   (concat prefix "Inputs:\n") (concat prefix "  "))
    (verilog-signals-princ (verilog-decls-get-vars decls)
			   (concat prefix "Vars:\n") (concat prefix "  "))
    (verilog-signals-princ (verilog-decls-get-assigns decls)
			   (concat prefix "Assigns:\n") (concat prefix "  "))
    (verilog-signals-princ (verilog-decls-get-consts decls)
			   (concat prefix "Consts:\n") (concat prefix "  "))
    (verilog-signals-princ (verilog-decls-get-gparams decls)
			   (concat prefix "Gparams:\n") (concat prefix "  "))
    (verilog-signals-princ (verilog-decls-get-interfaces decls)
			   (concat prefix "Interfaces:\n") (concat prefix "  "))
    (verilog-modport-princ (verilog-decls-get-modports decls)
			   (concat prefix "Modports:\n") (concat prefix "  "))
    (princ "\n")))

(defun verilog-signals-princ (signals &optional header prefix)
  "For debug, dump internal SIGNALS structures, with HEADER and PREFIX."
  (when signals
    (if header (princ header))
    (while signals
      (let ((sig (car signals)))
	(setq signals (cdr signals))
	(princ prefix)
	(princ "\"") (princ (verilog-sig-name sig)) (princ "\"")
	(princ "  bits=") (princ (verilog-sig-bits sig))
	(princ "  cmt=") (princ (verilog-sig-comment sig))
	(princ "  mem=") (princ (verilog-sig-memory sig))
	(princ "  enum=") (princ (verilog-sig-enum sig))
	(princ "  sign=") (princ (verilog-sig-signed sig))
	(princ "  type=") (princ (verilog-sig-type sig))
	(princ "  dim=") (princ (verilog-sig-multidim sig))
	(princ "  modp=") (princ (verilog-sig-modport sig))
	(princ "\n")))))

(defun verilog-modport-princ (modports &optional header prefix)
  "For debug, dump internal MODPORTS structures, with HEADER and PREFIX."
  (when modports
    (if header (princ header))
    (while modports
      (let ((sig (car modports)))
	(setq modports (cdr modports))
	(princ prefix)
	(princ "\"") (princ (verilog-modport-name sig)) (princ "\"")
	(princ "  clockings=") (princ (verilog-modport-clockings sig))
	(princ "\n")
	(verilog-decls-princ (verilog-modport-decls sig)
			     (concat prefix "  syms:\n")
			     (concat prefix "    "))))))

;;
;; Port/Wire/Etc Reading
;;

(defun verilog-read-inst-backward-name ()
  "Internal.  Move point back to beginning of inst-name."
  (verilog-backward-open-paren)
  (let (done)
    (while (not done)
      (verilog-re-search-backward-quick "\\()\\|\\b[a-zA-Z0-9`_$]\\|\\]\\)" nil nil)  ; ] isn't word boundary
      (cond ((looking-at ")")
             (verilog-backward-open-paren))
            (t (setq done t)))))
  (while (looking-at "\\]")
    (verilog-backward-open-bracket)
    (verilog-re-search-backward-quick "\\(\\b[a-zA-Z0-9`_$]\\|\\]\\)" nil nil))
  (skip-chars-backward "a-zA-Z0-9`_$"))

(defun verilog-read-inst-module-matcher ()
  "Set match data 0 with module_name when point is inside instantiation."
  (verilog-read-inst-backward-name)
  ;; Skip over instantiation name
  (verilog-re-search-backward-quick "\\(\\b[a-zA-Z0-9`_$]\\|)\\)" nil nil)  ; ) isn't word boundary
  ;; Check for parameterized instantiations
  (when (looking-at ")")
    (verilog-backward-open-paren)
    (verilog-re-search-backward-quick "\\b[a-zA-Z0-9`_$]" nil nil))
  (skip-chars-backward "a-zA-Z0-9`_$")
  ;; #1 is legal syntax for gate primitives
  (when (save-excursion
          (verilog-backward-syntactic-ws-quick)
          (eq ?# (char-before)))
    (verilog-re-search-backward-quick "\\b[a-zA-Z0-9`_$]" nil nil)
    (skip-chars-backward "a-zA-Z0-9`_$"))
  (looking-at "[a-zA-Z0-9`_$]+")
  ;; Important: don't use match string, this must work with Emacs 19 font-lock on
  (buffer-substring-no-properties (match-beginning 0) (match-end 0))
  ;; Caller assumes match-beginning/match-end is still set
  )

(defun verilog-read-inst-module ()
  "Return module_name when point is inside instantiation."
  (save-excursion
    (verilog-read-inst-module-matcher)))

(defun verilog-read-inst-name ()
  "Return instance_name when point is inside instantiation."
  (save-excursion
    (verilog-read-inst-backward-name)
    (looking-at "[a-zA-Z0-9`_$]+")
    ;; Important: don't use match string, this must work with Emacs 19 font-lock on
    (buffer-substring-no-properties (match-beginning 0) (match-end 0))))

(defun verilog-read-module-name ()
  "Return module name when after its ( or ;."
  (save-excursion
    (re-search-backward "[(;]")
    ;; Due to "module x import y (" we must search for declaration begin
    (verilog-re-search-backward-quick verilog-defun-re nil nil)
    (goto-char (match-end 0))
    (verilog-re-search-forward-quick "\\b[a-zA-Z0-9`_$]+" nil nil)
    ;; Important: don't use match string, this must work with Emacs 19 font-lock on
    (verilog-symbol-detick
     (buffer-substring-no-properties (match-beginning 0) (match-end 0)) t)))

(defun verilog-read-inst-param-value ()
  "Return list of parameters and values when point is inside instantiation."
  (save-excursion
    (verilog-read-inst-backward-name)
    ;; Skip over instantiation name
    (verilog-re-search-backward-quick "\\(\\b[a-zA-Z0-9`_$]\\|)\\)" nil nil)  ; ) isn't word boundary
    ;; If there are parameterized instantiations
    (when (looking-at ")")
      (let ((end-pt (point))
	    params
	    param-name paren-beg-pt param-value)
	(verilog-backward-open-paren)
	(while (verilog-re-search-forward-quick "\\." end-pt t)
	  (verilog-re-search-forward-quick "\\([a-zA-Z0-9`_$]\\)" nil nil)
	  (skip-chars-backward "a-zA-Z0-9'_$")
	  (looking-at "[a-zA-Z0-9`_$]+")
	  (setq param-name (buffer-substring-no-properties
			    (match-beginning 0) (match-end 0)))
	  (verilog-re-search-forward-quick "(" nil nil)
	  (setq paren-beg-pt (point))
	  (verilog-forward-close-paren)
	  (setq param-value (verilog-string-remove-spaces
			     (buffer-substring-no-properties
			      paren-beg-pt (1- (point)))))
	  (setq params (cons (list param-name param-value) params)))
	params))))

(defun verilog-read-auto-params (num-param &optional max-param)
  "Return parameter list inside auto.
Optional NUM-PARAM and MAX-PARAM check for a specific number of parameters."
  (let ((olist))
    (save-excursion
      ;; /*AUTOPUNT("parameter", "parameter")*/
      (when (not (eq (char-before) ?\*))  ; Not .*
        (backward-sexp 1))
      (while (looking-at "(?\\s *\"\\([^\"]*\\)\"\\s *,?")
        (setq olist (cons (match-string-no-properties 1) olist))
	(goto-char (match-end 0))))
    (or (eq nil num-param)
	(<= num-param (length olist))
	(error "%s: Expected %d parameters" (verilog-point-text) num-param))
    (if (eq max-param nil) (setq max-param num-param))
    (or (eq nil max-param)
	(>= max-param (length olist))
	(error "%s: Expected <= %d parameters" (verilog-point-text) max-param))
    (nreverse olist)))

;; Prevent compile warnings; these are let's, not globals.
(defvar sigs-in)
(defvar sigs-inout)
(defvar sigs-intf)
(defvar sigs-intfd)
(defvar sigs-out)
(defvar sigs-out-d)
(defvar sigs-out-i)
(defvar sigs-out-unk)
(defvar sigs-temp)

(defun verilog-read-decls ()
  "Compute signal declaration information for the current module at point.
Return an array of [outputs inouts inputs wire reg assign const gparam intf]."
  (verilog--suppressed-warnings
      ((lexical sigs-intf sigs-var sigs-const sigs-assign sigs-var
                sigs-gparam sigs-inout sigs-out sigs-in))
    ;; The local variable below are accessed via (symbol-value expect-signal).
    (defvar sigs-intf) (defvar sigs-var) (defvar sigs-const)
    (defvar sigs-assign) (defvar sigs-var) (defvar sigs-gparam)
    (defvar sigs-inout) (defvar sigs-out) (defvar sigs-in))
  (let ((end-mod-point (or (verilog-get-end-of-defun) (point-max)))
	(functask 0) (paren 0) (sig-paren 0) (v2kargs-ok t)
	in-modport in-clocking in-ign-to-semi ptype ign-prop
	sigs-in sigs-out sigs-inout sigs-var sigs-assign sigs-const
	sigs-gparam sigs-intf sigs-modports
	vec expect-signal keywd last-keywd newsig rvalue enum io
	signed typedefed multidim
	modport
	varstack tmp)
    ;;(if dbg (setq dbg (concat dbg (format "\n\nverilog-read-decls START PT %s END %s\n" (point) end-mod-point))))
    (save-excursion
      (verilog-beg-of-defun-quick)
      (setq sigs-const (verilog-read-auto-constants (point) end-mod-point))
      (while (< (point) end-mod-point)
	;;(if dbg (setq dbg (concat dbg (format "Pt %s  Vec %s   C%c Kwd'%s'\n" (point) vec (following-char) keywd))))
	(cond
	 ((looking-at "//")
	  (when (looking-at "[^\n]*\\(auto\\|synopsys\\)\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
            (setq enum (match-string-no-properties 2)))
	  (search-forward "\n"))
	 ((looking-at "/\\*")
	  (forward-char 2)
	  (when (looking-at "[^\n]*\\(auto\\|synopsys\\)\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
            (setq enum (match-string-no-properties 2)))
	  (or (search-forward "*/")
	      (error "%s: Unmatched /* */, at char %d" (verilog-point-text) (point))))
         ;; Skip over protected sections with Base64-encoded data
         ((looking-at "^\\s *`pragma\\s +protect\\s +begin_protected")
          (or (re-search-forward "^\\s *`pragma\\s +protect\\s +end_protected" nil t)
              (forward-line)))
         ((looking-at "^\\s *`protected\\>")
          (or (re-search-forward "^\\s *`endprotected\\>" nil t)
              (forward-line)))
	 ((looking-at "(\\*")
	  ;; To advance past either "(*)" or "(* ... *)" don't forward past first *
	  (forward-char 1)
	  (or (looking-at "\\*\\s-*)")  ; (* )
              (search-forward "*)")  ; end attribute
	      (error "%s: Unmatched (* *), at char %d" (verilog-point-text) (point))))
	 ((eq ?\" (following-char))
          (or (re-search-forward "[^\\]\"" nil t)  ; don't forward-char first, since we look for a non backslash first
	      (error "%s: Unmatched quotes, at char %d" (verilog-point-text) (point))))
	 ((eq ?\; (following-char))
          (cond (in-ign-to-semi  ; Such as inside a "import ...;" in a module header
                 (setq in-ign-to-semi nil  rvalue nil))
                ((and in-modport (not (eq in-modport t)))  ; end of a modport declaration
		 (verilog-modport-decls-set
		  in-modport
		  (verilog-decls-new sigs-out sigs-inout sigs-in
				     nil nil nil nil nil nil))
		 ;; Pop from varstack to restore state to pre-clocking
		 (setq tmp (car varstack)
		       varstack (cdr varstack)
		       sigs-out (aref tmp 0)
		       sigs-inout (aref tmp 1)
		       sigs-in (aref tmp 2))
		 (setq vec nil  io nil  expect-signal nil  newsig nil  paren 0  rvalue nil
		       v2kargs-ok nil  in-modport nil  ign-prop nil))
		(t
		 (setq vec nil  io nil  expect-signal nil  newsig nil  paren 0  rvalue nil
		       v2kargs-ok nil  in-modport nil  ign-prop nil)))
	  (forward-char 1))
	 ((eq ?= (following-char))
	  (setq rvalue t  newsig nil)
	  (forward-char 1))
	 ((and (eq ?, (following-char))
	       (eq paren sig-paren))
	  (setq rvalue nil)
	  (forward-char 1))
	 ;; ,'s can occur inside {} & funcs
	 ((looking-at "[{(]")
	  (setq paren (1+ paren))
	  (forward-char 1))
	 ((looking-at "[})]")
	  (setq paren (1- paren))
	  (forward-char 1)
	  (when (< paren sig-paren)
	    (setq expect-signal nil rvalue nil)))   ; ) that ends variables inside v2k arg list
	 ((looking-at "\\[")
          (setq keywd (buffer-substring-no-properties
                       (point)
                       (progn (forward-sexp 1) (point))))
	  (cond (newsig	; Memory, not just width.  Patch last signal added's memory (nth 3)
		 (setcar (cdr (cdr (cdr newsig)))
			 (if (verilog-sig-memory newsig)
                             (concat (verilog-sig-memory newsig)
                                     keywd)
			   keywd)))
                (vec  ; Multidimensional
		 (setq multidim (cons vec multidim))
		 (setq vec (verilog-string-replace-matches
			    "\\s-+" "" nil nil keywd)))
                (t  ; Bit width
		 (setq vec (verilog-string-replace-matches
			    "\\s-+" "" nil nil keywd)))))
         ;; int'(a) is cast, not declaration of a
         ((and (looking-at "'")
               (not rvalue))
          (forward-char 1)
          (setq expect-signal nil rvalue nil))
	 ;; Normal or escaped identifier -- note we remember the \ if escaped
	 ((looking-at "\\s-*\\([a-zA-Z0-9`_$]+\\|\\\\[^ \t\n\f]+\\)")
	  (goto-char (match-end 0))
	  (setq last-keywd keywd
                keywd (match-string-no-properties 1))
          (when (string-match "^\\\\" (match-string-no-properties 1))
            (setq keywd (concat keywd " ")))  ; Escaped ID needs space at end
	  ;; Add any :: package names to same identifier
          ;; '*' here is for "import x::*"
          (while (looking-at "\\s-*::\\s-*\\(\\*\\|[a-zA-Z0-9`_$]+\\|\\\\[^ \t\n\f]+\\)")
	    (goto-char (match-end 0))
            (setq keywd (concat keywd "::" (match-string-no-properties 1)))
            (when (string-match "^\\\\" (match-string-no-properties 1))
              (setq keywd (concat keywd " "))))  ; Escaped ID needs space at end
	  (cond ((equal keywd "input")
		 (setq vec nil        enum nil      rvalue nil  newsig nil  signed nil
		       typedefed nil  multidim nil  ptype nil   modport nil
		       expect-signal 'sigs-in       io t        sig-paren paren))
		((equal keywd "output")
		 (setq vec nil        enum nil      rvalue nil  newsig nil  signed nil
		       typedefed nil  multidim nil  ptype nil   modport nil
		       expect-signal 'sigs-out      io t        sig-paren paren))
		((equal keywd "inout")
		 (setq vec nil        enum nil      rvalue nil  newsig nil  signed nil
		       typedefed nil  multidim nil  ptype nil   modport nil
		       expect-signal 'sigs-inout    io t        sig-paren paren))
		((equal keywd "parameter")
		 (setq vec nil        enum nil      rvalue nil  signed nil
		       typedefed nil  multidim nil  ptype nil   modport nil
		       expect-signal 'sigs-gparam   io t        sig-paren paren))
		((member keywd '("wire" "reg"  ; Fast
				 ;; net_type
				 "tri" "tri0" "tri1" "triand" "trior" "trireg"
				 "uwire" "wand" "wor"
				 ;; integer_atom_type
				 "byte" "shortint" "int" "longint" "integer" "time"
				 "supply0" "supply1"
				 ;; integer_vector_type - "reg" above
				 "bit" "logic"
				 ;; non_integer_type
				 "shortreal" "real" "realtime"
				 ;; data_type
				 "string" "event" "chandle"))
		 (cond (io
			(setq typedefed
			      (if typedefed (concat typedefed " " keywd) keywd)))
		       (t (setq vec nil  enum nil  rvalue nil  signed nil
				typedefed nil  multidim nil  sig-paren paren
				expect-signal 'sigs-var  modport nil))))
		((equal keywd "assign")
		 (setq vec nil        enum nil        rvalue nil  signed nil
		       typedefed nil  multidim nil    ptype nil   modport nil
		       expect-signal 'sigs-assign     sig-paren paren))
		((member keywd '("localparam" "genvar"))
		 (setq vec nil        enum nil      rvalue nil  signed nil
		       typedefed nil  multidim nil  ptype nil   modport nil
		       expect-signal 'sigs-const    sig-paren paren))
		((member keywd '("signed" "unsigned"))
		 (setq signed keywd))
		((member keywd '("assert" "assume" "cover" "expect" "restrict"))
		 (setq ign-prop t))
		((member keywd '("class" "covergroup" "function"
				 "property" "randsequence" "sequence" "task"))
		 (unless ign-prop
		   (setq functask (1+ functask))))
		((member keywd '("endclass" "endgroup" "endfunction"
				 "endproperty" "endsequence" "endtask"))
		 (setq functask (1- functask)))
		((equal keywd "modport")
		 (setq in-modport t))
		((and (equal keywd "clocking")
                      (not (equal last-keywd "default")))
		 (setq in-clocking t))
		((equal keywd "import")
                 (when v2kargs-ok  ; import in module header, not a modport import
                   (setq in-ign-to-semi t  rvalue t)))
		((equal keywd "type")
		 (setq ptype t))
		((equal keywd "var"))
		;; Ifdef?  Ignore name of define
		((member keywd '("`ifdef" "`ifndef" "`elsif"))
		 (setq rvalue t))
                ;; Line directive? Skip over the rest of the line
                ((equal keywd "`line")
                 (forward-line))
		;; Type?
		((unless ptype
		   (verilog-typedef-name-p keywd))
		 (cond (io
			(setq typedefed
			      (if typedefed (concat typedefed " " keywd) keywd)))
		       (t (setq vec nil  enum nil  rvalue nil  signed nil
				typedefed keywd  ; Have a type
				multidim nil  sig-paren paren
				expect-signal 'sigs-var  modport nil))))
		;; Interface with optional modport in v2k arglist?
		;; Skip over parsing modport, and take the interface name as the type
		((and v2kargs-ok
		      (eq paren 1)
		      (not rvalue)
                      (or (looking-at "\\s-*#")
                          (looking-at "\\s-*\\(\\.\\(\\s-*[a-zA-Z`_$][a-zA-Z0-9`_$]*\\)\\|\\)\\s-*[a-zA-Z`_$][a-zA-Z0-9`_$]*")))
		 (when (match-end 2) (goto-char (match-end 2)))
		 (setq vec nil          enum nil       rvalue nil  signed nil
                       typedefed keywd  multidim nil   ptype nil
                       modport (match-string-no-properties 2)
		       newsig nil    sig-paren paren
		       expect-signal 'sigs-intf  io t  ))
		;; Ignore dotted LHS assignments: "assign foo.bar = z;"
		((looking-at "\\s-*\\.")
		 (goto-char (match-end 0))
		 (when (not rvalue)
		   (setq expect-signal nil)))
		;; "modport <keywd>"
		((and (eq in-modport t)
		      (not (member keywd verilog-keywords)))
		 (setq in-modport (verilog-modport-new keywd nil nil))
		 (setq sigs-modports (cons in-modport sigs-modports))
		 ;; Push old sig values to stack and point to new signal list
		 (setq varstack (cons (vector sigs-out sigs-inout sigs-in)
				      varstack))
		 (setq sigs-in nil  sigs-inout nil  sigs-out nil))
		;; "modport x (clocking <keywd>)"
		((and in-modport in-clocking)
		 (verilog-modport-clockings-add in-modport keywd)
		 (setq in-clocking nil))
		;; endclocking
		((and in-clocking
		      (equal keywd "endclocking"))
		 (unless (eq in-clocking t)
		   (verilog-modport-decls-set
		    in-clocking
		    (verilog-decls-new sigs-out sigs-inout sigs-in
				       nil nil nil nil nil nil))
		   ;; Pop from varstack to restore state to pre-clocking
		   (setq tmp (car varstack)
			 varstack (cdr varstack)
			 sigs-out (aref tmp 0)
			 sigs-inout (aref tmp 1)
			 sigs-in (aref tmp 2)))
		 (setq in-clocking nil))
		;; "clocking <keywd>"
		((and (eq in-clocking t)
		      (not (member keywd verilog-keywords)))
		 (setq in-clocking (verilog-modport-new keywd nil nil))
		 (setq sigs-modports (cons in-clocking sigs-modports))
		 ;; Push old sig values to stack and point to new signal list
		 (setq varstack (cons (vector sigs-out sigs-inout sigs-in)
				      varstack))
		 (setq sigs-in nil  sigs-inout nil  sigs-out nil))
		;; New signal, maybe?
		((and expect-signal
		      (not rvalue)
		      (eq functask 0)
                      (not (member keywd verilog-keywords))
                      (or (not io) (eq paren sig-paren)))
		 ;; Add new signal to expect-signal's variable
		 ;;(if dbg (setq dbg (concat dbg (format "Pt %s  New sig %s'\n" (point) keywd))))
		 (setq newsig (verilog-sig-new keywd vec nil nil enum signed typedefed multidim modport))
		 (set expect-signal (cons newsig
					  (symbol-value expect-signal))))))
	 (t
	  (forward-char 1)))
	(skip-syntax-forward " "))
      ;; Return arguments
      (setq tmp (verilog-decls-new (nreverse sigs-out)
				   (nreverse sigs-inout)
				   (nreverse sigs-in)
				   (nreverse sigs-var)
				   (nreverse sigs-modports)
				   (nreverse sigs-assign)
				   (nreverse sigs-const)
				   (nreverse sigs-gparam)
				   (nreverse sigs-intf)))
      ;;(if dbg (verilog-decls-princ tmp))
      tmp)))

(defvar verilog-read-sub-decls-in-interfaced nil
  "For `verilog-read-sub-decls', process next signal as under interfaced block.")

(defvar verilog-read-sub-decls-gate-ios nil
  "For `verilog-read-sub-decls', gate IO pins remaining, nil if non-primitive.")

(defun verilog-read-sub-decls-type (par-values portdata)
  "For `verilog-read-sub-decls-line', decode a signal type."
  (let* ((type (verilog-sig-type portdata))
         (pvassoc (assoc type par-values)))
    (cond ((member type '("wire" "reg")) nil)
          (pvassoc (nth 1 pvassoc))
          (t type))))

(defun verilog-read-sub-decls-sig (submoddecls par-values comment port sig vec multidim mem)
  "For `verilog-read-sub-decls-line', add a signal."
  ;; sig eq t to indicate .name syntax
  ;;(message "vrsds: %s(%S)" port sig)
  (let ((dotname (eq sig t))
        portdata)
    (when sig
      (setq port (verilog-symbol-detick-denumber port))
      (setq sig  (if dotname port (verilog-symbol-detick-denumber sig)))
      (if vec (setq vec  (verilog-symbol-detick-denumber vec)))
      (if multidim (setq multidim  (mapcar #'verilog-symbol-detick-denumber multidim)))
      (if mem (setq mem (verilog-symbol-detick-denumber mem)))
      (unless (or (not sig)
                  (equal sig ""))  ; Ignore .foo(1'b1) assignments
	(cond ((or (setq portdata (assoc port (verilog-decls-get-inouts submoddecls)))
		   (equal "inout" verilog-read-sub-decls-gate-ios))
	       (setq sigs-inout
		     (cons (verilog-sig-new
			    sig
			    (if dotname (verilog-sig-bits portdata) vec)
			    (concat "To/From " comment)
                            mem
			    nil
			    (verilog-sig-signed portdata)
                            (verilog-read-sub-decls-type par-values portdata)
			    multidim nil)
			   sigs-inout)))
	      ((or (setq portdata (assoc port (verilog-decls-get-outputs submoddecls)))
		   (equal "output" verilog-read-sub-decls-gate-ios))
	       (setq sigs-out
		     (cons (verilog-sig-new
			    sig
			    (if dotname (verilog-sig-bits portdata) vec)
			    (concat "From " comment)
			    mem
			    nil
			    (verilog-sig-signed portdata)
			    ;; Though ok in SV, in V2K code, propagating the
			    ;;  "reg" in "output reg" upwards isn't legal.
			    ;; Also for backwards compatibility we don't propagate
			    ;;  "input wire" upwards.
			    ;; See also `verilog-signals-edit-wire-reg'.
                            (verilog-read-sub-decls-type par-values portdata)
			    multidim nil)
			   sigs-out)))
	      ((or (setq portdata (assoc port (verilog-decls-get-inputs submoddecls)))
		   (equal "input" verilog-read-sub-decls-gate-ios))
	       (setq sigs-in
		     (cons (verilog-sig-new
			    sig
			    (if dotname (verilog-sig-bits portdata) vec)
			    (concat "To " comment)
			    mem
			    nil
			    (verilog-sig-signed portdata)
                            (verilog-read-sub-decls-type par-values portdata)
			    multidim nil)
			   sigs-in)))
	      ((setq portdata (assoc port (verilog-decls-get-interfaces submoddecls)))
	       (setq sigs-intf
		     (cons (verilog-sig-new
			    sig
			    (if dotname (verilog-sig-bits portdata) vec)
			    (concat "To/From " comment)
			    mem
			    nil
			    (verilog-sig-signed portdata)
                            (verilog-read-sub-decls-type par-values portdata)
			    multidim nil)
			   sigs-intf)))
	      ((setq portdata (and verilog-read-sub-decls-in-interfaced
				   (assoc port (verilog-decls-get-vars submoddecls))))
	       (setq sigs-intfd
		     (cons (verilog-sig-new
			    sig
			    (if dotname (verilog-sig-bits portdata) vec)
			    (concat "To/From " comment)
			    mem
			    nil
			    (verilog-sig-signed portdata)
                            (verilog-read-sub-decls-type par-values portdata)
			    multidim nil)
			   sigs-intf)))
	      ;; (t  -- warning pin isn't defined.)   ; Leave for lint tool
	      )))))

(defun verilog-read-sub-decls-expr (submoddecls par-values comment port expr)
  "For `verilog-read-sub-decls-line', parse a subexpression and add signals."
  ;;(message "vrsde: `%s'" expr)
  ;; Replace special /*[....]*/ comments inserted by verilog-auto-inst-port
  (setq expr (verilog-string-replace-matches
              "/\\*\\(\\.?\\[\\([^*]+\\|[*][^/]\\)+\\]\\)\\*/" "\\1" nil nil expr))
  ;; Remove front operators
  (setq expr (verilog-string-replace-matches "^\\s-*[---+~!|&]+\\s-*" "" nil nil expr))
  ;;
  (cond
   ;; {..., a, b} requires us to recurse on a,b
   ;; To support {#{},{#{a,b}} we'll just split everything on [{},]
   ((string-match "^\\s-*'?{\\(.*\\)}\\s-*$" expr)
    (let ((mlst (split-string (match-string 1 expr) "[{},]"))
          mstr)
      (while (setq mstr (pop mlst))
        (verilog-read-sub-decls-expr submoddecls par-values comment port mstr))))
   (t
    (let (sig vec multidim mem)
      ;; Remove leading reduction operators, etc
      (setq expr (verilog-string-replace-matches "^\\s-*[---+~!|&]+\\s-*" "" nil nil expr))
      ;; Remove casting types
      (setq expr (verilog-string-replace-matches
                  "^\\s-*[a-zA-Z_][a-zA-Z_0-9]*\\s-*'" "" nil nil expr))
      ;; Remove simple single set of parens (perhaps from cast, or perhaps not)
      (setq expr (verilog-string-replace-matches
                  "^\\s-*(\\([^)]*\\))\\s-*$" "\\1" nil nil expr))
      ;;(message "vrsde-ptop: `%s'" expr)
      (cond  ; Find \signal. Final space is part of escaped signal name
       ((string-match "^\\s-*\\(\\\\[^ \t\n\f]+\\s-\\)" expr)
	;;(message "vrsde-s: `%s'" (match-string 1 expr))
	(setq sig (match-string 1 expr)
	      expr (substring expr (match-end 0))))
       ;; Find signal
       ((string-match "^\\s-*\\([a-zA-Z_][a-zA-Z_0-9]*\\)" expr)
	;;(message "vrsde-s: `%s'" (match-string 1 expr))
	(setq sig (verilog-string-remove-spaces (match-string 1 expr))
	      expr (substring expr (match-end 0)))))
      ;; Find [vector] or [multi][multi][multi][vector] or [vector[VEC2]]
      ;; Unfortunately Emacs regexps don't allow matching bracket searches, so just 2 deep.
      (while (string-match "^\\s-*\\(\\[\\([^][]+\\|\\[[^][]+\\]\\)*\\]\\)" expr)
	;;(message "vrsde-v: `%s'" (match-string 1 expr))
	(when vec (setq multidim (cons vec multidim)))
	(setq vec (match-string 1 expr)
	      expr (substring expr (match-end 0))))
      ;; Find .[unpacked_memory] or .[unpacked][unpacked]...
      (while (string-match "^\\s-*\\.\\(\\(\\[[^]]+\\]\\)+\\)" expr)
	;;(message "vrsde-m: `%s'" (match-string 1 expr))
	(setq mem (match-string 1 expr)
	      expr (substring expr (match-end 0))))
      ;; If found signal, and nothing unrecognized, add the signal
      ;;(message "vrsde-rem: `%s'" expr)
      (when (and sig (string-match "^\\s-*$" expr))
        (verilog-read-sub-decls-sig submoddecls par-values comment port sig vec multidim mem))))))

(defun verilog-read-sub-decls-line (submoddecls par-values comment)
  "For `verilog-read-sub-decls', read lines of port defs until none match.
Inserts the list of signals found, using submodi to look up each port."
  (let (done port)
    (save-excursion
      (forward-line 1)
      (while (not done)
	;; Get port name
	(cond ((looking-at "\\s-*\\.\\s-*\\([a-zA-Z0-9`_$]*\\)\\s-*(\\s-*")
	       (setq port (match-string-no-properties 1))
	       (goto-char (match-end 0)))
	      ;; .\escaped (
	      ((looking-at "\\s-*\\.\\s-*\\(\\\\[^ \t\n\f]*\\)\\s-*(\\s-*")
               (setq port (concat (match-string-no-properties 1) " "))  ; escaped id's need trailing space
	       (goto-char (match-end 0)))
	      ;; .name
	      ((looking-at "\\s-*\\.\\s-*\\([a-zA-Z0-9`_$]*\\)\\s-*[,)/]")
	       (verilog-read-sub-decls-sig
                submoddecls par-values comment (match-string-no-properties 1) t ; sig==t for .name
		nil nil nil) ; vec multidim mem
	       (setq port nil))
	      ;; .\escaped_name
	      ((looking-at "\\s-*\\.\\s-*\\(\\\\[^ \t\n\f]*\\)\\s-*[,)/]")
	       (verilog-read-sub-decls-sig
                submoddecls par-values comment (concat (match-string-no-properties 1) " ") t ; sig==t for .name
		nil nil nil) ; vec multidim mem
	       (setq port nil))
	      ;; random
	      ((looking-at "\\s-*\\.[^(]*(")
               (setq port nil)  ; skip this line
	       (goto-char (match-end 0)))
	      (t
               (setq port nil  done t)))  ; Unknown, ignore rest of line
	;; Get signal name.  Point is at the first-non-space after (
	;; We intentionally ignore (non-escaped) signals with .s in them
	;; this prevents AUTOWIRE etc from noticing hierarchical sigs.
	(when port
          (cond ((and verilog-auto-ignore-concat
                      (looking-at "[({]"))
                 nil) ; {...} or (...) historically ignored with auto-ignore-concat
                ((looking-at "[^\n]*AUTONOHOOKUP"))
                ((looking-at "\\([a-zA-Z_][a-zA-Z_0-9]*\\)\\s-*)")
		 (verilog-read-sub-decls-sig
                  submoddecls par-values comment port
		  (verilog-string-remove-spaces (match-string-no-properties 1)) ; sig
		  nil nil nil)) ; vec multidim mem
		;;
		((looking-at "\\([a-zA-Z_][a-zA-Z_0-9]*\\)\\s-*\\(\\[[^][]+\\]\\)\\s-*)")
		 (verilog-read-sub-decls-sig
                  submoddecls par-values comment port
		  (verilog-string-remove-spaces (match-string-no-properties 1)) ; sig
		  (match-string-no-properties 2) nil nil)) ; vec multidim mem
		;; Fastpath was above looking-at's.
		;; For something more complicated invoke a parser
		((looking-at "[^)]+")
		 (verilog-read-sub-decls-expr
                  submoddecls par-values comment port
		  (buffer-substring-no-properties
		   (point) (1- (progn (search-backward "(") ; start at (
				      (verilog-forward-sexp-ign-cmt 1)
				      (point)))))))) ; expr
	;;
	(forward-line 1)))))
;;(verilog-read-sub-decls-line (verilog-decls-new nil nil nil nil nil nil nil nil nil) nil "Cmt")

(defun verilog-read-sub-decls-gate (submoddecls par-values comment submod end-inst-point)
  "For `verilog-read-sub-decls', read lines of UDP gate decl until none match.
Inserts the list of signals found."
  (save-excursion
    (let ((iolist (cdr (assoc submod verilog-gate-ios))))
      (while (< (point) end-inst-point)
	;; Get primitive's signal name, as will never have port, and no trailing )
	(cond ((looking-at "//")
	       (search-forward "\n"))
	      ((looking-at "/\\*")
	       (or (search-forward "*/")
		   (error "%s: Unmatched /* */, at char %d" (verilog-point-text) (point))))
	      ((looking-at "(\\*")
	       ;; To advance past either "(*)" or "(* ... *)" don't forward past first *
	       (forward-char 1)
	       (or (search-forward "*)")
		   (error "%s: Unmatched (* *), at char %d" (verilog-point-text) (point))))
              ;; On pins, parse and advance to next pin
              ;; Looking at pin, but *not* an // Output comment, or ) to end the inst
              ((looking-at "\\s-*[a-zA-Z0-9`_$({}\\][^,]*")
               (goto-char (match-end 0))
	       (setq verilog-read-sub-decls-gate-ios (or (car iolist) "input")
		     iolist (cdr iolist))
	       (verilog-read-sub-decls-expr
                submoddecls par-values comment "primitive_port"
                (match-string-no-properties 0)))
	      (t
	       (forward-char 1)
	       (skip-syntax-forward " ")))))))

(defun verilog-read-sub-decls ()
  "Internally parse signals going to modules under this module.
Return an array of [ outputs inouts inputs ] signals for modules that are
instantiated in this module.  For example if declare A A (.B(SIG)) and SIG
is an output, then SIG will be included in the list.

This only works on instantiations created with /*AUTOINST*/ converted by
\\[verilog-auto-inst].  Otherwise, it would have to read in the whole
component library to determine connectivity of the design.

One work around for this problem is to manually create // Inputs
and // Outputs comments above subcell signals, then have an empty
AUTOINST, for example:

        submod SubModuleName (
            // Outputs
            .out (out),
            // Inputs
            .in  (in)
            /*AUTOINST*/);"
  (save-excursion
    (let ((end-mod-point (verilog-get-end-of-defun))
          st-point end-inst-point par-values
	  ;; below 3 modified by verilog-read-sub-decls-line
	  sigs-out sigs-inout sigs-in sigs-intf sigs-intfd)
      (verilog-beg-of-defun-quick)
      (while (verilog-re-search-forward-quick "\\(/\\*AUTOINST\\((.*?)\\)?\\*/\\|\\.\\*\\)" end-mod-point t)
	(save-excursion
	  (goto-char (match-beginning 0))
          (setq par-values (and verilog-auto-inst-param-value
                                verilog-auto-inst-param-value-type
                                (verilog-read-inst-param-value)))
	  (unless (verilog-inside-comment-or-string-p)
	    ;; Attempt to snarf a comment
	    (let* ((submod (verilog-read-inst-module))
		   (inst (verilog-read-inst-name))
		   (subprim (member submod verilog-gate-keywords))
		   (comment (concat inst " of " submod ".v"))
		   submodi submoddecls)
	      (cond
	       (subprim
		(setq submodi 'primitive
		      submoddecls (verilog-decls-new nil nil nil nil nil nil nil nil nil)
		      comment (concat inst " of " submod))
		(verilog-backward-open-paren)
		(setq end-inst-point (save-excursion (verilog-forward-sexp-ign-cmt 1)
						     (point))
		      st-point (point))
		(forward-char 1)
                (verilog-read-sub-decls-gate submoddecls par-values comment submod end-inst-point))
	       ;; Non-primitive
	       (t
		(when (setq submodi (verilog-modi-lookup submod t))
		  (setq submoddecls (verilog-modi-get-decls submodi)
			verilog-read-sub-decls-gate-ios nil)
		  (verilog-backward-open-paren)
		  (setq end-inst-point (save-excursion (verilog-forward-sexp-ign-cmt 1)
						       (point))
			st-point (point))
		  ;; This could have used a list created by verilog-auto-inst
		  ;; However I want it to be runnable even on user's manually added signals
		  (let ((verilog-read-sub-decls-in-interfaced t))
		    (while (re-search-forward "\\s *(?\\s *// Interfaced" end-inst-point t)
                      (verilog-read-sub-decls-line submoddecls par-values comment)))  ; Modifies sigs-ifd
		  (goto-char st-point)
		  (while (re-search-forward "\\s *(?\\s *// Interfaces" end-inst-point t)
                    (verilog-read-sub-decls-line submoddecls par-values comment))  ; Modifies sigs-out
		  (goto-char st-point)
		  (while (re-search-forward "\\s *(?\\s *// Outputs" end-inst-point t)
                    (verilog-read-sub-decls-line submoddecls par-values comment))  ; Modifies sigs-out
		  (goto-char st-point)
		  (while (re-search-forward "\\s *(?\\s *// Inouts" end-inst-point t)
                    (verilog-read-sub-decls-line submoddecls par-values comment))  ; Modifies sigs-inout
		  (goto-char st-point)
		  (while (re-search-forward "\\s *(?\\s *// Inputs" end-inst-point t)
                    (verilog-read-sub-decls-line submoddecls par-values comment))  ; Modifies sigs-in
		  )))))))
      ;; Combine duplicate bits
      ;;(setq rr (vector sigs-out sigs-inout sigs-in))
      (verilog-subdecls-new
       (verilog-signals-combine-bus (nreverse sigs-out))
       (verilog-signals-combine-bus (nreverse sigs-inout))
       (verilog-signals-combine-bus (nreverse sigs-in))
       (verilog-signals-combine-bus (nreverse sigs-intf))
       (verilog-signals-combine-bus (nreverse sigs-intfd))))))

(defun verilog-read-inst-pins ()
  "Return an array of [ pins ] for the current instantiation at point.
For example if declare A A (.B(SIG)) then B will be included in the list."
  (save-excursion
    (let ((end-mod-point (point))  ; presume at /*AUTOINST*/ point
	  pins pin)
      (verilog-backward-open-paren)
      (while (re-search-forward "\\.\\([^(,) \t\n\f]*\\)\\s-*" end-mod-point t)
        (setq pin (match-string-no-properties 1))
	(unless (verilog-inside-comment-or-string-p)
	  (setq pins (cons (list pin) pins))
	  (when (looking-at "(")
	    (verilog-forward-sexp-ign-cmt 1))))
      (vector pins))))

(defun verilog-read-arg-pins ()
  "Return an array of [ pins ] for the current argument declaration at point."
  (save-excursion
    (let ((end-mod-point (point))  ; presume at /*AUTOARG*/ point
	  pins pin)
      (verilog-backward-open-paren)
      (while (re-search-forward "\\([a-zA-Z0-9$_.%`]+\\)" end-mod-point t)
        (setq pin (match-string-no-properties 1))
	(unless (verilog-inside-comment-or-string-p)
	  (setq pins (cons (list pin) pins))))
      (vector pins))))

(defun verilog-read-auto-constants (beg end-mod-point)
  "Return a list of AUTO_CONSTANTs used in the region from BEG to END-MOD-POINT."
  ;; Insert new
  (save-excursion
    (let (sig-list tpl-end-pt)
      (goto-char beg)
      (while (re-search-forward "\\<AUTO_CONSTANT" end-mod-point t)
	(if (not (looking-at "\\s *("))
	    (error "%s: Missing () after AUTO_CONSTANT" (verilog-point-text)))
	(search-forward "(" end-mod-point)
	(setq tpl-end-pt (save-excursion
			   (backward-char 1)
                           (verilog-forward-sexp-cmt 1)  ; Moves to paren that closes argdecl's
			   (backward-char 1)
			   (point)))
	(while (re-search-forward "\\s-*\\([\"a-zA-Z0-9$_.%`]+\\)\\s-*,*" tpl-end-pt t)
          (setq sig-list (cons (list (match-string-no-properties 1) nil nil) sig-list))))
      sig-list)))

(defvar verilog-cache-has-lisp nil "Non-nil if any AUTO_LISP in buffer.")
(make-variable-buffer-local 'verilog-cache-has-lisp)

(defun verilog-read-auto-lisp-present ()
  "Set `verilog-cache-has-lisp' if any AUTO_LISP in this buffer."
  (save-excursion
    (goto-char (point-min))
    (setq verilog-cache-has-lisp (re-search-forward "\\<AUTO_LISP(" nil t))))

(defun verilog-read-auto-lisp (start end)
  "Look for and evaluate an AUTO_LISP between START and END.
Must call `verilog-read-auto-lisp-present' before this function."
  ;; This function is expensive for large buffers, so we cache if any AUTO_LISP exists
  (when verilog-cache-has-lisp
    (save-excursion
      (goto-char start)
      (while (re-search-forward "\\<AUTO_LISP(" end t)
	(backward-char)
	(let* ((beg-pt (prog1 (point)
                         (verilog-forward-sexp-cmt 1)))  ; Closing paren
	       (end-pt (point))
	       (verilog-in-hooks t))
	  (eval-region beg-pt end-pt nil))))))

(defun verilog-read-always-signals-recurse
    (exit-keywd rvalue temp-next)
  "Recursive routine for parentheses/bracket matching.
EXIT-KEYWD is expression to stop at, nil if top level.
RVALUE is true if at right hand side of equal.
TEMP-NEXT is true to ignore next token, fake from inside case statement."
  (verilog--suppressed-warnings ((lexical sigs-temp sigs-in sigs-out-unk))
    ;; The local variable below are accessed via (symbol-value got-list).
    (defvar sigs-temp) (defvar sigs-in) (defvar sigs-out-unk))
  (let* ((semi-rvalue (equal "endcase" exit-keywd))  ; true if after a ; we are looking for rvalue
	 keywd last-keywd sig-tolk sig-last-tolk gotend got-sig got-list end-else-check
	 ignore-next)
    ;;(if dbg (setq dbg (concat dbg (format "Recursion %S %S %S\n" exit-keywd rvalue temp-next))))
    (while (not (or (eobp) gotend))
      (cond
       ((looking-at "//")
	(search-forward "\n"))
       ((looking-at "/\\*")
	(or (search-forward "*/")
	    (error "%s: Unmatched /* */, at char %d" (verilog-point-text) (point))))
       ((looking-at "(\\*")
	;; To advance past either "(*)" or "(* ... *)" don't forward past first *
	(forward-char 1)
	(or (search-forward "*)")
	    (error "%s: Unmatched (* *), at char %d" (verilog-point-text) (point))))
       (t (setq keywd (buffer-substring-no-properties
		       (point)
		       (save-excursion (when (eq 0 (skip-chars-forward "a-zA-Z0-9$_.%`"))
					 (forward-char 1))
				       (point)))
		sig-last-tolk sig-tolk
		sig-tolk nil)
	  ;;(if dbg (setq dbg (concat dbg (format "\tPt=%S %S\trv=%S in=%S ee=%S gs=%S\n" (point) keywd rvalue ignore-next end-else-check got-sig))))
	  (cond
	   ((equal keywd "\"")
	    (or (re-search-forward "[^\\]\"" nil t)
		(error "%s: Unmatched quotes, at char %d" (verilog-point-text) (point))))
	   ;; else at top level loop, keep parsing
	   ((and end-else-check (equal keywd "else"))
	    ;;(if dbg (setq dbg (concat dbg (format "\tif-check-else %s\n" keywd))))
	    ;; no forward movement, want to see else in lower loop
	    (setq end-else-check nil))
	   ;; End at top level loop
	   ((and end-else-check (looking-at "[^ \t\n\f]"))
	    ;;(if dbg (setq dbg (concat dbg (format "\tif-check-else-other %s\n" keywd))))
	    (setq gotend t))
	   ;; Final statement?
	   ((and exit-keywd (and (or (equal keywd exit-keywd)
                                     (and (equal exit-keywd "'}")
                                          (equal keywd "}")))
                                 (not (looking-at "::"))))
	    (setq gotend t)
	    (forward-char (length keywd)))
	   ;; Standard tokens...
	   ((equal keywd ";")
	    (setq ignore-next nil  rvalue semi-rvalue)
	    ;; Final statement at top level loop?
	    (when (not exit-keywd)
	      ;;(if dbg (setq dbg (concat dbg (format "\ttop-end-check %s\n" keywd))))
	      (setq end-else-check t))
	    (forward-char 1))
	   ((equal keywd "'")
	    (cond ((looking-at "'[sS]?[hdxboHDXBO]?[ \t]*[0-9a-fA-F_xzXZ?]+")
                   (goto-char (match-end 0)))
                  ((looking-at "'{")
                   (forward-char 2)
                   (verilog-read-always-signals-recurse "'}" t nil))
                  (t
                   (forward-char 1))))
           ((equal keywd ":")  ; Case statement, begin/end label, x?y:z
            (cond ((looking-at "::")
                   (forward-char 1))  ; Another forward-char below
                  ((equal "endcase" exit-keywd)  ; case x: y=z; statement next
		   (setq ignore-next nil rvalue nil))
                  ((equal "?" exit-keywd)  ; x?y:z rvalue
                   )  ; NOP
                  ((equal "]" exit-keywd)  ; [x:y] rvalue
                   )  ; NOP
                  ((equal "'}" exit-keywd)  ; Pattern assignment
                   )  ; NOP
                  (got-sig  ; label: statement
		   (setq ignore-next nil rvalue semi-rvalue got-sig nil))
                  ((not rvalue)  ; begin label
		   (setq ignore-next t rvalue nil)))
	    (forward-char 1))
	   ((equal keywd "=")
	    (when got-sig
	      ;;(if dbg (setq dbg (concat dbg (format "\t\tequal got-sig=%S got-list=%s\n" got-sig got-list))))
	      (set got-list (cons got-sig (symbol-value got-list)))
	      (setq got-sig nil))
	    (when (not rvalue)
	      (if (eq (char-before) ?< )
		  (setq sigs-out-d (append sigs-out-d sigs-out-unk)
			sigs-out-unk nil)
		(setq sigs-out-i (append sigs-out-i sigs-out-unk)
		      sigs-out-unk nil)))
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
            (cond (sig-last-tolk  ; Function call; zap last signal
		   (setq got-sig nil)))
	    (cond ((equal last-keywd "for")
		   ;; temp-next: Variables on LHS are lvalues, but generally we want
		   ;; to ignore them, assuming they are loop increments
		   (verilog-read-always-signals-recurse ";" nil t)
		   (verilog-read-always-signals-recurse ";" t nil)
		   (verilog-read-always-signals-recurse ")" nil nil))
		  (t (verilog-read-always-signals-recurse ")" t nil))))
	   ((equal keywd "begin")
	    (skip-syntax-forward "w_")
	    (verilog-read-always-signals-recurse "end" nil nil)
	    ;;(if dbg (setq dbg (concat dbg (format "\tgot-end %s\n" exit-keywd))))
	    (setq ignore-next nil  rvalue semi-rvalue)
	    (if (not exit-keywd) (setq end-else-check t)))
	   ((member keywd '("case" "casex" "casez" "randcase"))
	    (skip-syntax-forward "w_")
	    (verilog-read-always-signals-recurse "endcase" t nil)
	    (setq ignore-next nil  rvalue semi-rvalue)
            (if (not exit-keywd) (setq gotend t)))  ; top level begin/end
           ((string-match "^[$`a-zA-Z_]" keywd)  ; not exactly word constituent
	    (cond ((member keywd '("`ifdef" "`ifndef" "`elsif"))
		   (setq ignore-next t))
		  ((or ignore-next
		       (member keywd verilog-keywords)
                       (string-match "^\\$" keywd))  ; PLI task
		   (setq ignore-next nil))
		  (t
		   (setq keywd (verilog-symbol-detick-denumber keywd))
		   (when got-sig
		     (set got-list (cons got-sig (symbol-value got-list)))
		     ;;(if dbg (setq dbg (concat dbg (format "\t\tgot-sig=%S got-list=%S\n" got-sig got-list))))
		     )
		   (setq got-list (cond (temp-next 'sigs-temp)
					(rvalue 'sigs-in)
					(t 'sigs-out-unk))
			 got-sig (if (or (not keywd)
					 (assoc keywd (symbol-value got-list)))
				     nil (list keywd nil nil))
			 temp-next nil
			 sig-tolk t)))
	    (skip-chars-forward "a-zA-Z0-9$_.%`"))
	   (t
	    (forward-char 1)))
	  ;; End of non-comment token
	  (setq last-keywd keywd)))
      (skip-syntax-forward " "))
    ;; Append the final pending signal
    (when got-sig
      ;;(if dbg (setq dbg (concat dbg (format "\t\tfinal got-sig=%S got-list=%s\n" got-sig got-list))))
      (set got-list (cons got-sig (symbol-value got-list)))
      (setq got-sig nil))
    ;;(if dbg (setq dbg (concat dbg (format "ENDRecursion %s\n" exit-keywd))))
    ))

(defun verilog-read-always-signals ()
  "Parse always block at point and return list of (outputs inout inputs)."
  (save-excursion
    (let* (;(dbg "")
	   sigs-out-d sigs-out-i sigs-out-unk sigs-temp sigs-in)
      (verilog-read-always-signals-recurse nil nil nil)
      (setq sigs-out-i (append sigs-out-i sigs-out-unk)
	    sigs-out-unk nil)
      ;;(if dbg (with-current-buffer (get-buffer-create "*vl-dbg*") (delete-region (point-min) (point-max)) (insert dbg) (setq dbg "")))
      ;; Return what was found
      (verilog-alw-new sigs-out-d sigs-out-i sigs-temp sigs-in))))

(defun verilog-read-instants ()
  "Parse module at point and return list of ( ( file instance ) ... )."
  (verilog-beg-of-defun-quick)
  (let* ((end-mod-point (verilog-get-end-of-defun))
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
            (let ((module (match-string-no-properties 1))
                  (instant (match-string-no-properties 2)))
	      (if (not (member module verilog-keywords))
		  (setq instants-list (cons (list module instant) instants-list)))))
	(forward-line 1)))
    instants-list))


(defun verilog-read-auto-template-middle ()
  "With point in middle of an AUTO_TEMPLATE, parse it.
Returns REGEXP and list of ( (signal_name connection_name)... )."
  (save-excursion
    ;; Find beginning
    (let ((tpl-regexp "\\([0-9]+\\)")
	  (lineno -1)  ; -1 to offset for the AUTO_TEMPLATE's newline
	  (templateno 0)
	  tpl-sig-list tpl-wild-list tpl-end-pt rep)
      ;; Parse "REGEXP"
      ;; We reserve @"..." for future lisp expressions that evaluate
      ;; once-per-AUTOINST
      (when (looking-at "\\s-*\"\\([^\"]*\\)\"")
        (setq tpl-regexp (match-string-no-properties 1))
	(goto-char (match-end 0)))
      (search-forward "(")
      (while (verilog-within-string)  ;; e.g. inside a tpl-regexp spec
        (search-forward "("))
      ;; Parse lines in the template
      (when (or verilog-auto-inst-template-numbers
		verilog-auto-template-warn-unused)
	(save-excursion
	  (let ((pre-pt (point)))
	    (goto-char (point-min))
	    (while (search-forward "AUTO_TEMPLATE" pre-pt t)
	      (setq templateno (1+ templateno)))
	    (while (< (point) pre-pt)
	      (forward-line 1)
	      (setq lineno (1+ lineno))))))
      (setq tpl-end-pt (save-excursion
			 (backward-char 1)
                         (verilog-forward-sexp-cmt 1)  ; Moves to paren that closes argdecl's
			 (backward-char 1)
			 (point)))
      ;;
      (while (< (point) tpl-end-pt)
	(cond ((looking-at "\\s-*\\.\\([a-zA-Z0-9`_$]+\\)\\s-*(\\(.*\\))\\s-*\\(,\\|)\\s-*;\\)")
	       (setq tpl-sig-list
		     (cons (list
			    (match-string-no-properties 1)
			    (match-string-no-properties 2)
                            templateno lineno
                            (save-excursion
                              (goto-char (match-end 0))
                              (looking-at "[^\n]*AUTONOHOOKUP")))
			   tpl-sig-list))
	       (goto-char (match-end 0)))
              ;; Regexp form??
              ((looking-at
                ;; Regexp bug in XEmacs disallows ][ inside [], and wants + last
                "\\s-*\\.\\(\\([-a-zA-Z0-9`_$+@^.*?|]\\|[][]\\|\\\\[()|0-9]\\)+\\)\\s-*(\\(.*\\))\\s-*\\(,\\|)\\s-*;\\)")
	       (setq rep (match-string-no-properties 3))
	       (goto-char (match-end 0))
	       (setq tpl-wild-list
		     (cons (list
			    (concat "^"
				    (verilog-string-replace-matches "@" "\\\\([0-9]+\\\\)" nil nil
								    (match-string 1))
				    "$")
			    rep
                            templateno lineno
                            (save-excursion
                              (goto-char (match-end 0))
                              (looking-at "[^\n]*AUTONOHOOKUP")))
			   tpl-wild-list)))
	      ((looking-at "[ \t\f]+")
	       (goto-char (match-end 0)))
	      ((looking-at "\n")
	       (setq lineno (1+ lineno))
	       (goto-char (match-end 0)))
	      ((looking-at "//")
	       (search-forward "\n")
	       (setq lineno (1+ lineno)))
	      ((looking-at "/\\*")
	       (forward-char 2)
	       (or (search-forward "*/")
		   (error "%s: Unmatched /* */, at char %d" (verilog-point-text) (point))))
	      (t
	       (error "%s: AUTO_TEMPLATE parsing error: %s"
		      (verilog-point-text)
		      (progn (looking-at ".*$") (match-string 0))))))
      ;; Return
      (vector tpl-regexp
	      (list tpl-sig-list tpl-wild-list)))))

(defun verilog-read-auto-template (module)
  "Look for an auto_template for the instantiation of the given MODULE.
If found returns `verilog-read-auto-template-middle' structure."
  (save-excursion
    ;; Find beginning
    (let ((pt (point)))
      ;; Note this search is expensive, as we hunt from mod-begin to point
      ;; for every instantiation.  Likewise in verilog-read-auto-lisp.
      ;; So, we look first for an exact string rather than a slow regexp.
      ;; Someday we may keep a cache of every template, but this would also
      ;; need to record the relative position of each AUTOINST, as multiple
      ;; templates exist for each module, and we're inserting lines.
      (cond ((or
	      ;; See also regexp in `verilog-auto-template-lint'
	      (verilog-re-search-backward-substr
	       "AUTO_TEMPLATE"
	       (concat "^\\s-*/?\\*?\\s-*" module "\\s-+AUTO_TEMPLATE") nil t)
	      ;; Also try forward of this AUTOINST
	      ;; This is for historical support; this isn't speced as working
	      (progn
		(goto-char pt)
		(verilog-re-search-forward-substr
		 "AUTO_TEMPLATE"
		 (concat "^\\s-*/?\\*?\\s-*" module "\\s-+AUTO_TEMPLATE") nil t)))
	     (goto-char (match-end 0))
	     (verilog-read-auto-template-middle))
	    ;; If no template found
	    (t (vector "" nil))))))
;;(progn (find-file "auto-template.v") (verilog-read-auto-template "ptl_entry"))

(defvar verilog-auto-template-hits nil "Successful lookups with `verilog-read-auto-template-hit'.")
(make-variable-buffer-local 'verilog-auto-template-hits)

(defun verilog-read-auto-template-init ()
  "Initialize `verilog-read-auto-template'."
  (when (eval-when-compile (fboundp 'make-hash-table))  ; else feature not allowed
    (when verilog-auto-template-warn-unused
      (setq verilog-auto-template-hits
	    (make-hash-table :test 'equal :rehash-size 4.0)))))

(defun verilog-read-auto-template-hit (tpl-ass)
  "Record that TPL-ASS template from `verilog-read-auto-template' was used."
  (when (eval-when-compile (fboundp 'make-hash-table))  ; else feature not allowed
    (when verilog-auto-template-warn-unused
      (unless verilog-auto-template-hits
	(verilog-read-auto-template-init))
      (puthash (vector (nth 2 tpl-ass) (nth 3 tpl-ass)) t
	       verilog-auto-template-hits))))

(defun verilog-set-define (defname defvalue &optional buffer enumname)
  "Set the definition DEFNAME to the DEFVALUE in the given BUFFER.
Optionally associate it with the specified enumeration ENUMNAME."
  (with-current-buffer (or buffer (current-buffer))
    ;; Namespace intentionally short for AUTOs and compatibility
    (let ((mac (intern (concat "vh-" defname))))
      ;;(message "Define %s=%s" defname defvalue) (sleep-for 1)
      ;; Need to define to a constant if no value given
      (set (make-local-variable mac)
	   (if (equal defvalue "") "1" defvalue)))
    (if enumname
	;; Namespace intentionally short for AUTOs and compatibility
	(let ((enumvar (intern (concat "venum-" enumname))))
	  ;;(message "Define %s=%s" defname defvalue) (sleep-for 1)
	  (unless (boundp enumvar) (set enumvar nil))
          (add-to-list (make-local-variable enumvar) defname)))))

(defun verilog-read-defines (&optional filename recurse subcall)
  "Read \\=`defines and parameters for the current file, or optional FILENAME.
If the filename is provided, `verilog-library-flags' will be used to
resolve it.  If optional RECURSE is non-nil, recurse through \\=`includes.

Localparams must be simple assignments to constants, or have their own
\"localparam\" label rather than a list of localparams.  Thus:

    localparam X = 5, Y = 10;   // Ok
    localparam X = {1\\='b1, 2\\='h2};  // Ok
    localparam X = {1\\='b1, 2\\='h2}, Y = 10;  // Bad, make into 2 localparam lines

Defines must be simple text substitutions, one on a line, starting
at the beginning of the line.  Any ifdefs or multiline comments around the
define are ignored.

Defines are stored inside Emacs variables using the name
vh-{definename}.

Localparams define what symbols are constants so that AUTOSENSE
will not include them in sensitivity lists.  However any
parameters in the include file are not considered ports in the
including file, thus will not appear in AUTOINSTPARAM lists for a
parent module..

The file variables feature can be used to set defines that
`verilog-mode' can see; put at the *END* of your file something
like:

    // Local Variables:
    // vh-macro:\"macro_definition\"
    // End:

If macros are defined earlier in the same file and you want their values,
you can read them automatically with:

    // Local Variables:
    // verilog-auto-read-includes:t
    // End:

Or a more specific alternative example, which requires having
`enable-local-eval' non-nil:

    // Local Variables:
    // eval:(verilog-read-defines)
    // eval:(verilog-read-defines \"group_standard_includes.v\")
    // End:

Note these are only read when the file is first visited, you must use
\\[find-alternate-file] RET  to have these take effect after editing them!

If you want to disable the \"Process `eval' or hook local variables\"
warning message, you need to add to your init file:

    (setq enable-local-eval t)"
  (let ((origbuf (current-buffer)))
    (save-excursion
      (unless subcall (verilog-getopt-flags))
      (when filename
	(let ((fns (verilog-library-filenames filename (buffer-file-name))))
	  (if fns
	      (set-buffer (find-file-noselect (car fns)))
	    (error "%s: Can't find verilog-read-defines file: %s"
		   (verilog-point-text) filename))))
      (when recurse
	(goto-char (point-min))
	(while (re-search-forward "^\\s-*`include\\s-+\\([^ \t\n\f]+\\)" nil t)
	  (let ((inc (verilog-substitute-include-name
                      (match-string-no-properties 1))))
	    (unless (verilog-inside-comment-or-string-p)
	      (verilog-read-defines inc recurse t)))))
      ;; Read `defines
      ;; note we don't use verilog-re... it's faster this way, and that
      ;; function has problems when comments are at the end of the define
      (goto-char (point-min))
      (while (re-search-forward "^\\s-*`define\\s-+\\([a-zA-Z0-9_$]+\\)\\s-+\\(.*\\)$" nil t)
	(let ((defname (match-string-no-properties 1))
	      (defvalue (match-string-no-properties 2)))
	  (unless (verilog-inside-comment-or-string-p (match-beginning 0))
	    (setq defvalue (verilog-string-replace-matches "\\s-*/[/*].*$" "" nil nil defvalue))
	    (verilog-set-define defname defvalue origbuf))))
      ;; Hack: Read parameters
      (goto-char (point-min))
      (while (re-search-forward
	      "^\\s-*\\(parameter\\|localparam\\)\\(\\s-*\\[[^]]*\\]\\)?\\s-*" nil t)
	(let (enumname)
          ;; Advance over parameter's type if present
          (if (looking-at "\\([a-zA-Z0-9_]+\\s-+\\)[a-zA-Z0-9_]+")
              (goto-char (match-end 1)))
	  ;; The primary way of getting defines is verilog-read-decls
	  ;; However, that isn't called yet for included files, so we'll add another scheme
	  (if (looking-at "[^\n]*\\(auto\\|synopsys\\)\\s +enum\\s +\\([a-zA-Z0-9_]+\\)")
	      (setq enumname (match-string-no-properties 2)))
	  (forward-comment 99999)
	  (while (looking-at (concat "\\s-*,?\\s-*\\(?:/[/*].*?$\\)?\\s-*\\([a-zA-Z0-9_$]+\\)"
				     "\\s-*=\\s-*\\([^;,]*\\),?\\s-*\\(/[/*].*?$\\)?\\s-*"))
	    (unless (verilog-inside-comment-or-string-p (match-beginning 0))
	      (verilog-set-define (match-string-no-properties 1)
				  (match-string-no-properties 2) origbuf enumname))
	    (goto-char (match-end 0))
	    (forward-comment 99999)))))))

(defun verilog-read-includes ()
  "Read \\=`includes for the current file.
This will find all of the \\=`includes which are at the beginning of lines,
ignoring any ifdefs or multiline comments around them.
`verilog-read-defines' is then performed on the current and each included
file.

It is often useful put at the *END* of your file something like:

    // Local Variables:
    // verilog-auto-read-includes:t
    // End:

Or the equivalent longer version, which requires having
`enable-local-eval' non-nil:

    // Local Variables:
    // eval:(verilog-read-defines)
    // eval:(verilog-read-includes)
    // End:

Note includes are only read when the file is first visited, you must use
\\[find-alternate-file] RET  to have these take effect after editing them!

It is good to get in the habit of including all needed files in each .v
file that needs it, rather than waiting for compile time.  This will aid
this process, Verilint, and readability.  To prevent defining the same
variable over and over when many modules are compiled together, put a test
around the inside each include file:

foo.v (an include file):
        \\=`ifndef _FOO_V        // include if not already included
        \\=`define _FOO_V
        ... contents of file
        \\=`endif // _FOO_V"
  ;;slow:  (verilog-read-defines nil t)
  (save-excursion
    (verilog-getopt-flags)
    (goto-char (point-min))
    (while (re-search-forward "^\\s-*`include\\s-+\\([^ \t\n\f]+\\)" nil t)
      (let ((inc (verilog-substitute-include-name
                  (match-string-no-properties 1))))
	(verilog-read-defines inc nil t)))))

(defun verilog-read-signals (&optional start end)
  "Return a simple list of all possible signals in the file.
Bounded by optional region from START to END.  Overly aggressive but fast.
Some macros and such are also found and included.  For dinotrace.el."
  (let (sigs-all keywd)
    (progn;save-excursion
      (goto-char (or start (point-min)))
      (setq end (or end (point-max)))
      (while (re-search-forward "[\"/a-zA-Z_.%`]" end t)
	(forward-char -1)
	(cond
	 ((looking-at "//")
	  (search-forward "\n"))
	 ((looking-at "/\\*")
	  (search-forward "*/"))
	 ((looking-at "(\\*")
          (or (looking-at "(\\*\\s-*)")  ; It's an "always @ (*)"
	      (search-forward "*)")))
	 ((eq ?\" (following-char))
          (re-search-forward "[^\\]\""))  ; don't forward-char first, since we look for a non backslash first
	 ((looking-at "\\s-*\\([a-zA-Z0-9$_.%`]+\\)")
	  (goto-char (match-end 0))
	  (setq keywd (match-string-no-properties 1))
	  (or (member keywd verilog-keywords)
	      (member keywd sigs-all)
	      (setq sigs-all (cons keywd sigs-all))))
	 (t (forward-char 1))))
      ;; Return list
      sigs-all)))

;;
;; Argument file parsing
;;

(defun verilog-getopt (arglist &optional default-dir)
  "Parse -f, -v etc arguments in ARGLIST list or string.
Use DEFAULT-DIR to anchor paths if non-nil."
  (unless (listp arglist) (setq arglist (list arglist)))
  (let ((space-args '())
	arg next-param)
    ;; Split on spaces, so users can pass whole command lines
    (while arglist
      (setq arg (car arglist)
	    arglist (cdr arglist))
      (while (string-match "^\\([^ \t\n\f]+\\)[ \t\n\f]*\\(.*$\\)" arg)
	(setq space-args (append space-args
				 (list (match-string-no-properties 1 arg))))
	(setq arg (match-string 2 arg))))
    ;; Parse arguments
    (while space-args
      (setq arg (car space-args)
	    space-args (cdr space-args))
      (cond
       ;; Need another arg
       ((equal arg "-F")
	(setq next-param arg))
       ((equal arg "-f")
	(setq next-param arg))
       ((equal arg "-v")
	(setq next-param arg))
       ((equal arg "-y")
	(setq next-param arg))
       ;; +libext+(ext1)+(ext2)...
       ((string-match "^\\+libext\\+\\(.*\\)" arg)
	(setq arg (match-string 1 arg))
	(while (string-match "\\([^+]+\\)\\+?\\(.*\\)" arg)
	  (verilog-add-list-unique 'verilog-library-extensions
				   (match-string 1 arg))
	  (setq arg (match-string 2 arg))))
       ;;
       ((or (string-match "^-D\\([^+=]*\\)[+=]\\(.*\\)" arg)  ; -Ddefine=val
            (string-match "^-D\\([^+=]*\\)\\(\\)" arg)  ; -Ddefine
            (string-match "^\\+define\\([^+=]*\\)[+=]\\(.*\\)" arg)  ; +define+val
            (string-match "^\\+define\\([^+=]*\\)\\(\\)" arg))  ; +define+define
	(verilog-set-define (match-string 1 arg) (match-string 2 arg)))
       ;;
       ((or (string-match "^\\+incdir\\+\\(.*\\)" arg)  ; +incdir+dir
            (string-match "^-I\\(.*\\)" arg))   ; -Idir
	(verilog-add-list-unique 'verilog-library-directories
				 (substitute-in-file-name (match-string 1 arg))))
       ;; Ignore
       ((equal "+librescan" arg))
       ((string-match "^-U\\(.*\\)" arg))  ; -Udefine
       ;; Second parameters
       ((equal next-param "-F")
	(setq next-param nil)
	(verilog-getopt-file (verilog-substitute-file-name-path arg default-dir)
                             (file-name-directory (verilog-substitute-file-name-path arg default-dir))))
       ((equal next-param "-f")
	(setq next-param nil)
	(verilog-getopt-file (verilog-substitute-file-name-path arg default-dir) nil))
       ((equal next-param "-v")
	(setq next-param nil)
	(verilog-add-list-unique 'verilog-library-files
				 (verilog-substitute-file-name-path arg default-dir)))
       ((equal next-param "-y")
	(setq next-param nil)
	(verilog-add-list-unique 'verilog-library-directories
				 (verilog-substitute-file-name-path arg default-dir)))
       ;; Filename
       ((string-match "^[^-+]" arg)
	(verilog-add-list-unique 'verilog-library-files
				 (verilog-substitute-file-name-path arg default-dir)))
       ;; Default - ignore; no warning
       ))))
;;(verilog-getopt (list "+libext+.a+.b" "+incdir+foodir" "+define+a+aval" "-f" "otherf" "-v" "library" "-y" "dir"))

(defun verilog-getopt-file (filename &optional default-dir)
  "Read Verilog options from the specified FILENAME.
Use DEFAULT-DIR to anchor paths if non-nil."
  (save-excursion
    (let ((fns (verilog-library-filenames filename (buffer-file-name)))
	  (orig-buffer (current-buffer))
	  line)
      (if fns
	  (set-buffer (find-file-noselect (car fns)))
	(error "%s: Can't find verilog-getopt-file -f file: %s"
	       (verilog-point-text) filename))
      (goto-char (point-min))
      (while (not (eobp))
        (setq line (buffer-substring (point) (line-end-position)))
	(forward-line 1)
	(when (string-match "//" line)
	  (setq line (substring line 0 (match-beginning 0))))
	(with-current-buffer orig-buffer  ; Variables are buffer-local, so need right context.
	  (verilog-getopt line default-dir))))))

(defun verilog-getopt-flags ()
  "Convert `verilog-library-flags' into standard library variables."
  ;; If the flags are local, then all the outputs should be local also
  (when (local-variable-p 'verilog-library-flags (current-buffer))
    (mapc #'make-local-variable '(verilog-library-extensions
                                  verilog-library-directories
                                  verilog-library-files
                                  verilog-library-flags)))
  ;; Allow user to customize
  (verilog-run-hooks 'verilog-before-getopt-flags-hook)
  ;; Process arguments
  (verilog-getopt verilog-library-flags)
  ;; Allow user to customize
  (verilog-run-hooks 'verilog-getopt-flags-hook))

(defun verilog-substitute-file-name-path (filename default-dir)
  "Return FILENAME with environment variables substituted.
Use DEFAULT-DIR to anchor paths if non-nil."
  (if default-dir
      (expand-file-name (substitute-in-file-name filename) default-dir)
  (substitute-in-file-name filename)))

(defun verilog-substitute-include-name (filename)
  "Return FILENAME for include with define substituted."
  (setq filename (verilog-string-replace-matches "\"" "" nil nil filename))
  (verilog-string-replace-matches "\"" "" nil nil
                                  (verilog-symbol-detick filename t)))

(defun verilog-add-list-unique (varref object)
  "Append to VARREF list the given OBJECT,
unless it is already a member of the variable's list."
  (unless (member object (symbol-value varref))
    (set varref (append (symbol-value varref) (list object))))
  varref)
;;(progn (setq l '()) (verilog-add-list-unique `l "a") (verilog-add-list-unique `l "a") l)

(defun verilog-current-flags ()
  "Convert `verilog-library-flags' and similar variables to command line.
Used for __FLAGS__ in `verilog-expand-command'."
  (let ((cmd (mapconcat #'concat verilog-library-flags " ")))
    (when (equal cmd "")
      (setq cmd (concat
		 "+libext+" (mapconcat #'concat verilog-library-extensions "+")
		 (mapconcat (lambda (i) (concat " -y " i " +incdir+" i))
			    verilog-library-directories "")
		 (mapconcat (lambda (i) (concat " -v " i))
			    verilog-library-files ""))))
    cmd))
;;(verilog-current-flags)


;;; Cached directory support:
;;

(defvar verilog-dir-cache-preserving nil
  "If true, the directory cache is enabled, and file system changes are ignored.
See `verilog-dir-file-exists-p' and `verilog-dir-files'.")

;; If adding new cached variable, add also to verilog-preserve-dir-cache
(defvar verilog-dir-cache-list nil
  "Alist of (((Cwd Dirname) Results)...) for caching `verilog-dir-files'.")
(defvar verilog-dir-cache-lib-filenames nil
  "Cached data for `verilog-library-filenames'.")

(defmacro verilog-preserve-dir-cache (&rest body)
  "Execute the BODY forms, allowing directory cache preservation within BODY.
This means that changes inside BODY made to the file system will not be
seen by the `verilog-dir-files' and related functions."
  `(let ((verilog-dir-cache-preserving (current-buffer))
	 verilog-dir-cache-list
	 verilog-dir-cache-lib-filenames)
     (progn ,@body)))

(defun verilog-dir-files (dirname)
  "Return all filenames in the DIRNAME directory.
Relative paths depend on the `default-directory'.
Results are cached if inside `verilog-preserve-dir-cache'."
  (unless verilog-dir-cache-preserving
    (setq verilog-dir-cache-list nil))  ; Cache disabled
  ;; We don't use expand-file-name on the dirname to make key, as it's slow
  (let* ((cache-key (list dirname default-directory))
	 (fass (assoc cache-key verilog-dir-cache-list))
	 exp-dirname data)
    (cond (fass  ; Return data from cache hit
	   (nth 1 fass))
	  (t
	   (setq exp-dirname (expand-file-name dirname)
		 data (and (file-directory-p exp-dirname)
			   (directory-files exp-dirname nil nil nil)))
	   ;; Note we also encache nil for non-existing dirs.
	   (setq verilog-dir-cache-list (cons (list cache-key data)
					      verilog-dir-cache-list))
	   data))))
;; Miss-and-hit test:
;;(verilog-preserve-dir-cache (prin1 (verilog-dir-files "."))
;; (prin1 (verilog-dir-files ".")) nil)

(defun verilog-dir-file-exists-p (filename)
  "Return non-nil if FILENAME exists.
Like `file-exists-p' but results are cached if inside
`verilog-preserve-dir-cache'."
  (let* ((dirname (file-name-directory filename))
	 ;; Correct for file-name-nondirectory returning same if no slash.
	 (dirnamed (if (or (not dirname) (equal dirname filename))
		       default-directory dirname))
	 (flist (verilog-dir-files dirnamed)))
    (and flist
	 (member (file-name-nondirectory filename) flist)
	 t)))
;;(verilog-dir-file-exists-p "verilog-mode.el")
;;(verilog-dir-file-exists-p "../verilog-mode/verilog-mode.el")


;;; Module name lookup:
;;

(defun verilog-module-inside-filename-p (module filename)
  "Return modi if MODULE is specified inside FILENAME, else nil.
Allows version control to check out the file if need be."
  (and (or (file-exists-p filename)
	   (and (fboundp 'vc-backend)
		(vc-backend filename)))
       (let (modi type)
	 (with-current-buffer (find-file-noselect filename)
	   (save-excursion
	     (goto-char (point-min))
	     (while (and
		     ;; It may be tempting to look for verilog-defun-re,
		     ;; don't, it slows things down a lot!
                    (verilog-re-search-forward-quick "\\<\\(connectmodule\\|module\\|interface\\|program\\)\\>" nil t)
		     (setq type (match-string-no-properties 0))
		     (verilog-re-search-forward-quick "[(;]" nil t))
	       (if (equal module (verilog-read-module-name))
		   (setq modi (verilog-modi-new module filename (point) type))))
	     modi)))))

(defun verilog-is-number (symbol)
  "Return non-nil if SYMBOL is number-like."
  (or (string-match "^[0-9 \t:]+$" symbol)
      (string-match "^[---]*[0-9]+$" symbol)
      (string-match "^[0-9 \t]+'s?[hdxbo][0-9a-fA-F_xz? \t]*$" symbol)))

(defun verilog-symbol-detick (symbol wing-it)
  "Return an expanded SYMBOL name without any defines.
If the variable vh-{symbol} is defined, return that value.
If undefined, and WING-IT, return just SYMBOL without the tick, else nil."
  (while (and symbol (string-match "^`" symbol))
    (setq symbol (substring symbol 1))
    (setq symbol
	  ;; Namespace intentionally short for AUTOs and compatibility
	  (if (boundp (intern (concat "vh-" symbol)))
	      ;; Emacs has a bug where boundp on a buffer-local
	      ;; variable in only one buffer returns t in another.
	      ;; This can confuse, so check for nil.
	      ;; Namespace intentionally short for AUTOs and compatibility
             (let ((val (symbol-value (intern (concat "vh-" symbol)))))
		(if (eq val nil)
		    (if wing-it symbol nil)
		  val))
	    (if wing-it symbol nil))))
  symbol)
;;(verilog-symbol-detick "`mod" nil)

(defun verilog-symbol-detick-denumber (symbol)
  "Return SYMBOL with defines converted and any numbers dropped to nil."
  (when (string-match "^`" symbol)
    ;; This only will work if the define is a simple signal, not
    ;; something like a[b].  Sorry, it should be substituted into the parser
    (setq symbol
	  (verilog-string-replace-matches
	   "\\[[^0-9: \t]+\\]" "" nil nil
	   (or (verilog-symbol-detick symbol nil)
	       (if verilog-auto-sense-defines-constant
		   "0"
		 symbol)))))
  (if (verilog-is-number symbol)
      nil
    symbol))

(defun verilog-symbol-detick-text (text)
  "Return TEXT without any known defines.
If the variable vh-{symbol} is defined, substitute that value.
This function is intended for use in AUTO_TEMPLATE Lisp expressions."
  (let ((ok t) symbol val)
    (while (and ok (string-match "`\\([a-zA-Z0-9_]+\\)" text))
      (setq symbol (match-string 1 text))
      ;;(message symbol)
      (cond ((and
	      ;; Namespace intentionally short for AUTOs and compatibility
	      (boundp (intern (concat "vh-" symbol)))
	      ;; Emacs has a bug where boundp on a buffer-local
	      ;; variable in only one buffer returns t in another.
	      ;; This can confuse, so check for nil.
	      ;; Namespace intentionally short for AUTOs and compatibility
             (setq val (symbol-value (intern (concat "vh-" symbol)))))
	     (setq text (replace-match val nil nil text)))
	    (t (setq ok nil)))))
  text)
;;(progn (setq vh-mod "`foo" vh-foo "bar") (verilog-symbol-detick-text "bar `mod `undefed"))

(defun verilog-expand-dirnames (&optional dirnames)
  "Return a list of existing directories given a list of wildcarded DIRNAMES.
Or, just the existing dirnames themselves if there are no wildcards."
  ;; Note this function is performance critical.
  ;; Do not call anything that requires disk access that cannot be cached.
  (interactive)
  (unless dirnames
    (error "`verilog-library-directories' should include at least `.'"))
  (save-match-data
    (setq dirnames (reverse dirnames))  ; not nreverse
    (let ((dirlist nil)
          pattern dirfile dirfiles dirname root filename rest basefile)
      (setq dirnames (mapcar #'substitute-in-file-name dirnames))
      (while dirnames
        (setq dirname (car dirnames)
              dirnames (cdr dirnames))
        (cond ((string-match (concat "^\\(\\|[^*?]*[/\\]\\)"  ; root
                                     "\\([^/\\]*[*?][^/\\]*\\)"     ; filename with *?
                                     "\\(.*\\)")                    ; rest
                             dirname)
               (setq root (match-string 1 dirname)
                     filename (match-string 2 dirname)
                     rest (match-string 3 dirname)
                     pattern filename)
               ;; now replace those * and ? with .+ and .
               ;; use ^ and /> to get only whole file names
               (setq pattern (verilog-string-replace-matches "[*]" ".+" nil nil pattern)
                     pattern (verilog-string-replace-matches "[?]" "." nil nil pattern)
                     pattern (concat "^" pattern "$")
                     dirfiles (verilog-dir-files root))
               (while dirfiles
                 (setq basefile (car dirfiles)
                       dirfile (expand-file-name (concat root basefile rest))
                       dirfiles (cdr dirfiles))
                 (when (and (string-match pattern basefile)
                            ;; Don't allow abc/*/rtl to match abc/rtl via ..
                            (not (equal basefile "."))
                            (not (equal basefile "..")))
                   ;; Might have more wildcards, so process again
                   (setq dirnames (cons dirfile dirnames)))))
              ;; Defaults
              (t
               (if (file-directory-p dirname)
                   (setq dirlist (cons dirname dirlist))))))
      dirlist)))
;;(verilog-expand-dirnames (list "." ".." "nonexist" "../*" "/home/wsnyder/*/v" "../*/*"))

(defun verilog-library-filenames (filename &optional current check-ext)
  "Return a search path to find the given FILENAME or module name.
Uses the optional CURRENT filename or variable `buffer-file-name', plus
`verilog-library-directories' and `verilog-library-extensions'
variables to build the path.  With optional CHECK-EXT also check
`verilog-library-extensions'."
  (unless current (setq current (buffer-file-name)))
  (unless verilog-dir-cache-preserving
    (setq verilog-dir-cache-lib-filenames nil))
  (let* ((cache-key (list filename current check-ext))
	 (fass (assoc cache-key verilog-dir-cache-lib-filenames))
	 chkdirs chkdir chkexts fn outlist)
    (cond (fass  ; Return data from cache hit
	   (nth 1 fass))
	  (t
	   ;; Note this expand can't be easily cached, as we need to
	   ;; pick up buffer-local variables for newly read sub-module files
	   (setq chkdirs (verilog-expand-dirnames verilog-library-directories))
	   (while chkdirs
	     (setq chkdir (expand-file-name (car chkdirs)
					    (file-name-directory current))
		   chkexts (if check-ext verilog-library-extensions '("")))
	     (while chkexts
	       (setq fn (expand-file-name (concat filename (car chkexts))
					  chkdir))
	       ;;(message "Check for %s" fn)
	       (if (verilog-dir-file-exists-p fn)
		   (setq outlist (cons (expand-file-name
					fn (file-name-directory current))
				       outlist)))
	       (setq chkexts (cdr chkexts)))
	     (setq chkdirs (cdr chkdirs)))
	   (setq outlist (nreverse outlist))
	   (setq verilog-dir-cache-lib-filenames
		 (cons (list cache-key outlist)
		       verilog-dir-cache-lib-filenames))
	   outlist))))

(defun verilog-module-filenames (module current)
  "Return a search path to find the given MODULE name.
Uses the CURRENT filename, `verilog-library-extensions',
`verilog-library-directories' and `verilog-library-files'
variables to build the path."
  ;; Return search locations for it
  (append (list current)                ; first, current buffer
          (verilog-library-filenames module current t)
          ;; Finally any libraries; fixed up if using e.g. tramp
          (mapcar (lambda (fname)
                    (if (file-name-absolute-p fname)
                        (concat (file-remote-p current) fname)
                      fname))
                  verilog-library-files)))

;;
;; Module Information
;;
;; Many of these functions work on "modi" a module information structure
;; A modi is:  [module-name-string file-name begin-point]

(defvar verilog-cache-enabled t
  "Non-nil enables caching of signals, etc.
Set to nil for debugging to make things SLOW!")

(defvar verilog-modi-cache-list nil
  "Cache of ((Module Function) Buf-Tick Buf-Modtime Func-Returns)...
For speeding up verilog-modi-get-* commands.
Buffer-local.")
(make-variable-buffer-local 'verilog-modi-cache-list)

(defvar verilog-modi-cache-preserve-tick nil
  "Modification tick after which the cache is still considered valid.
Use `verilog-preserve-modi-cache' to set it.")
(defvar verilog-modi-cache-preserve-buffer nil
  "Modification tick after which the cache is still considered valid.
Use `verilog-preserve-modi-cache' to set it.")
(defvar verilog-modi-cache-current-enable nil
  "Non-nil means allow caching `verilog-modi-current', set by let().")
(defvar verilog-modi-cache-current nil
  "Currently active `verilog-modi-current', if any, set by let().")
(defvar verilog-modi-cache-current-max nil
  "Current endmodule point for `verilog-modi-cache-current', if any.")

(defun verilog-modi-current ()
  "Return the modi structure for the module currently at point, possibly cached."
  (cond ((and verilog-modi-cache-current
	      (>= (point) (verilog-modi-get-point verilog-modi-cache-current))
	      (<= (point) verilog-modi-cache-current-max))
	 ;; Slow assertion, for debugging the cache:
	 ;;(or (equal verilog-modi-cache-current (verilog-modi-current-get)) (debug))
	 verilog-modi-cache-current)
	(verilog-modi-cache-current-enable
	 (setq verilog-modi-cache-current (verilog-modi-current-get)
	       verilog-modi-cache-current-max
	       ;; The cache expires when we pass "endmodule" as then the
	       ;; current modi may change to the next module
	       ;; This relies on the AUTOs generally inserting, not deleting text
	       (save-excursion
		 (verilog-re-search-forward-quick verilog-end-defun-re nil nil)))
	 verilog-modi-cache-current)
	(t
	 (verilog-modi-current-get))))

(defun verilog-modi-current-get ()
  "Return the modi structure for the module currently at point."
  (let* (name type pt)
    ;; read current module's name
    (save-excursion
      (verilog-re-search-backward-quick verilog-defun-re nil nil)
      (setq type (match-string-no-properties 0))
      (verilog-re-search-forward-quick "(" nil nil)
      (setq name (verilog-read-module-name))
      (setq pt (point)))
    ;; return modi - note this vector built two places
    (verilog-modi-new name (or (buffer-file-name) (current-buffer)) pt type)))

(defvar verilog-modi-lookup-cache nil "Hash of (modulename modi).")
(make-variable-buffer-local 'verilog-modi-lookup-cache)
(defvar verilog-modi-lookup-last-current nil "Cache of `current-buffer' at last lookup.")
(defvar verilog-modi-lookup-last-tick nil "Cache of `buffer-chars-modified-tick' at last lookup.")

(defun verilog-modi-lookup (module allow-cache &optional ignore-error)
  "Find the file and point at which MODULE is defined.
If ALLOW-CACHE is set, check and remember cache of previous lookups.
Return modi if successful, else print message unless IGNORE-ERROR is true."
  (let* ((current (or (buffer-file-name) (current-buffer)))
	 modi)
    ;; Check cache
    ;;(message "verilog-modi-lookup: %s" module)
    (cond ((and verilog-modi-lookup-cache
		verilog-cache-enabled
		allow-cache
		(setq modi (gethash module verilog-modi-lookup-cache))
		(equal verilog-modi-lookup-last-current current)
		;; If hit is in current buffer, then tick must match
		(or (equal verilog-modi-lookup-last-tick (buffer-chars-modified-tick))
		    (not (equal current (verilog-modi-file-or-buffer modi)))))
	   ;;(message "verilog-modi-lookup: HIT %S" modi)
	   modi)
	  ;; Miss
	  (t (let* ((realname (verilog-symbol-detick module t))
		    (orig-filenames (verilog-module-filenames realname current))
		    (filenames orig-filenames)
		    mif)
	       (while (and filenames (not mif))
		 (if (not (setq mif (verilog-module-inside-filename-p realname (car filenames))))
		     (setq filenames (cdr filenames))))
	       ;; mif has correct form to become later elements of modi
	       (setq modi mif)
	       (or mif ignore-error
		   (error
		    (concat
		     "%s: Can't locate `%s' module definition%s"
		     "\n    Check the verilog-library-directories variable."
		     "\n    I looked in (if not listed, doesn't exist):\n\t%s")
		    (verilog-point-text) module
		    (if (not (equal module realname))
			(concat " (Expanded macro to " realname ")")
		      "")
                    (mapconcat #'concat orig-filenames "\n\t")))
	       (when (eval-when-compile (fboundp 'make-hash-table))
		 (unless verilog-modi-lookup-cache
		   (setq verilog-modi-lookup-cache
			 (make-hash-table :test 'equal :rehash-size 4.0)))
		 (puthash module modi verilog-modi-lookup-cache))
	       (setq verilog-modi-lookup-last-current current
		     verilog-modi-lookup-last-tick (buffer-chars-modified-tick)))))
    modi))

(defun verilog-modi-filename (modi)
  "Filename of MODI, or name of buffer if it's never been saved."
  (if (bufferp (verilog-modi-file-or-buffer modi))
      (or (buffer-file-name (verilog-modi-file-or-buffer modi))
	  (buffer-name (verilog-modi-file-or-buffer modi)))
    (verilog-modi-file-or-buffer modi)))

(defun verilog-modi-goto (modi)
  "Move point/buffer to specified MODI."
  (or modi (error "Passed unfound modi to goto, check earlier"))
  (set-buffer (if (bufferp (verilog-modi-file-or-buffer modi))
		  (verilog-modi-file-or-buffer modi)
		(find-file-noselect (verilog-modi-file-or-buffer modi))))
  (or (equal major-mode 'verilog-mode)  ; Put into Verilog mode to get syntax
      (verilog-mode))
  (goto-char (verilog-modi-get-point modi)))

(defun verilog-goto-defun-file (module)
  "Move point to the file at which a given MODULE is defined."
  (interactive "sGoto File for Module: ")
  (let* ((modi (verilog-modi-lookup module nil)))
    (when modi
      (verilog-modi-goto modi)
      (switch-to-buffer (current-buffer)))))

(defun verilog-modi-cache-results (modi function)
  "Run on MODI the given FUNCTION.  Locate the module in a file.
Cache the output of function so next call may have faster access."
  (let (fass)
    (save-excursion  ; Cache is buffer-local so can't avoid this.
      (verilog-modi-goto modi)
      (if (and (setq fass (assoc (list modi function)
				 verilog-modi-cache-list))
	       ;; Destroy caching when incorrect; Modified or file changed
	       (not (and verilog-cache-enabled
			 (or (equal (buffer-chars-modified-tick) (nth 1 fass))
			     (and verilog-modi-cache-preserve-tick
				  (<= verilog-modi-cache-preserve-tick  (nth 1 fass))
				  (equal  verilog-modi-cache-preserve-buffer (current-buffer))))
			 (equal (visited-file-modtime) (nth 2 fass)))))
	  (setq verilog-modi-cache-list nil
		fass nil))
      (cond (fass
	     ;; Return data from cache hit
	     (nth 3 fass))
	    (t
	     ;; Read from file
	     ;; Clear then restore any highlighting to make emacs19 happy
             (let ((func-returns
                    (verilog-save-font-no-change-functions
                     (funcall function))))
	       ;; Cache for next time
	       (setq verilog-modi-cache-list
		     (cons (list (list modi function)
				 (buffer-chars-modified-tick)
				 (visited-file-modtime)
				 func-returns)
			   verilog-modi-cache-list))
	       func-returns))))))

(defun verilog-modi-cache-add (modi function element sig-list)
  "Add function return results to the module cache.
Update MODI's cache for given FUNCTION so that the return ELEMENT of that
function now contains the additional SIG-LIST parameters."
  (let (fass)
    (save-excursion
      (verilog-modi-goto modi)
      (if (setq fass (assoc (list modi function)
			    verilog-modi-cache-list))
	  (let ((func-returns (nth 3 fass)))
	    (aset func-returns element
		  (append sig-list (aref func-returns element))))))))

(defmacro verilog-preserve-modi-cache (&rest body)
  "Execute the BODY forms, allowing cache preservation within BODY.
This means that changes to the buffer will not result in the cache being
flushed.  If the changes affect the modsig state, they must call the
modsig-cache-add-* function, else the results of later calls may be
incorrect.  Without this, changes are assumed to be adding/removing signals
and invalidating the cache."
  `(let ((verilog-modi-cache-preserve-tick (buffer-chars-modified-tick))
	 (verilog-modi-cache-preserve-buffer (current-buffer)))
     (progn ,@body)))


(defun verilog-modi-modport-lookup-one (modi name &optional ignore-error)
  "Given a MODI, return the declarations related to the given modport NAME.
Report errors unless optional IGNORE-ERROR."
  ;; Recursive routine - see below
  (let* ((realname (verilog-symbol-detick name t))
	 (modport (assoc name (verilog-decls-get-modports (verilog-modi-get-decls modi)))))
    (or modport ignore-error
	(error "%s: Can't locate `%s' modport definition%s"
               (verilog-point-text) name
               (if (not (equal name realname))
                   (concat " (Expanded macro to " realname ")")
                 "")))
    (let* ((decls (verilog-modport-decls modport))
	   (clks (verilog-modport-clockings modport)))
      ;; Now expand any clocking's
      (while clks
	(setq decls (verilog-decls-append
		     decls
		     (verilog-modi-modport-lookup-one modi (car clks) ignore-error)))
	(setq clks (cdr clks)))
      decls)))

(defun verilog-modi-modport-lookup (modi name-re &optional ignore-error)
  "Given a MODI, return the declarations related to the given modport NAME-RE.
If the modport points to any clocking blocks, expand the signals to include
those clocking block's signals."
  ;; Recursive routine - see below
  (let* ((mod-decls (verilog-modi-get-decls modi))
	 (clks (verilog-decls-get-modports mod-decls))
	 (name-re (concat "^" name-re "$"))
	 (decls (verilog-decls-new nil nil nil nil nil nil nil nil nil)))
    ;; Pull in all modports
    (while clks
      (when (string-match name-re (verilog-modport-name (car clks)))
	(setq decls (verilog-decls-append
		     decls
		     (verilog-modi-modport-lookup-one modi (verilog-modport-name (car clks)) ignore-error))))
      (setq clks (cdr clks)))
    decls))

(defun verilog-signals-matching-enum (in-list enum)
  "Return all signals in IN-LIST matching the given ENUM."
  (let (out-list)
    (dolist (sig in-list)
      (if (equal (verilog-sig-enum sig) enum)
          (push sig out-list)))
    ;; New scheme
    ;; Namespace intentionally short for AUTOs and compatibility
    (let* ((enumvar (intern (concat "venum-" enum))))
      (dolist (en (and (boundp enumvar) (symbol-value enumvar)))
        (let ((sig (list en)))
          (unless (member sig out-list)
            (push sig out-list)))))
    (nreverse out-list)))

(defun verilog-signals-matching-regexp (in-list regexp)
  "Return all signals in IN-LIST matching the given REGEXP, if non-nil.
Allow regexp inversion if REGEXP begins with ?!."
  (if (or (not regexp) (equal regexp ""))
      in-list
    (if (string-match "^\\?!" regexp)
        (verilog-signals-not-matching-regexp in-list (substring regexp 2))
      (let ((case-fold-search verilog-case-fold)
            out-list)
        (while in-list
          (if (string-match regexp (verilog-sig-name (car in-list)))
              (setq out-list (cons (car in-list) out-list)))
          (setq in-list (cdr in-list)))
        (nreverse out-list)))))

(defun verilog-signals-not-matching-regexp (in-list regexp)
  "Return all signals in IN-LIST not matching the given REGEXP, if non-nil.
Allow regexp inversion if REGEXP begins with ?!."
  (if (or (not regexp) (equal regexp ""))
      in-list
    (if (string-match "^\\?!" regexp)
        (verilog-signals-matching-regexp in-list (substring regexp 2))
      (let ((case-fold-search verilog-case-fold)
            out-list)
        (while in-list
          (if (not (string-match regexp (verilog-sig-name (car in-list))))
              (setq out-list (cons (car in-list) out-list)))
          (setq in-list (cdr in-list)))
        (nreverse out-list)))))

(defun verilog-signals-matching-dir-re (in-list decl-type regexp)
  "Return all signals in IN-LIST matching the given DECL-TYPE and REGEXP,
if non-nil."
  (if (or (not regexp) (equal regexp ""))
      in-list
    (let (out-list to-match)
      (while in-list
	;; Note verilog-insert-one-definition matches on this order
	(setq to-match (concat
			decl-type
			" " (verilog-sig-signed (car in-list))
                        " " (verilog-sig-multidim-string (car in-list))
			(verilog-sig-bits (car in-list))))
	(if (string-match regexp to-match)
	    (setq out-list (cons (car in-list) out-list)))
	(setq in-list (cdr in-list)))
      (nreverse out-list))))

(defun verilog-signals-edit-wire-reg (in-list)
  "Return all signals in IN-LIST with wire/reg data types made blank."
  (mapcar (lambda (sig)
	    (when (member (verilog-sig-type sig) '("wire" "reg"))
	      (verilog-sig-type-set sig nil))
	    sig) in-list))

(defun verilog-signals-add-prefix (in-list prefix)
  "Return all signals in IN-LIST with PREFIX added."
  (if (or (not prefix) (equal prefix ""))
      in-list
    (let (out-list)
      (while in-list
        (setq out-list (cons (verilog-sig-new-renamed
                              (concat prefix (verilog-sig-name (car in-list)))
                              (car in-list))
                             out-list))
        (setq in-list (cdr in-list)))
      (nreverse out-list))))
;(verilog-signals-add-prefix (list (list "foo" "...") (list "bar" "...")) "p_")

;; Combined
(defun verilog-decls-get-signals (decls)
  "Return all declared signals in DECLS, excluding `assign' statements."
  (append
   (verilog-decls-get-outputs decls)
   (verilog-decls-get-inouts decls)
   (verilog-decls-get-inputs decls)
   (verilog-decls-get-vars decls)
   (verilog-decls-get-consts decls)
   (verilog-decls-get-gparams decls)))

(defun verilog-decls-get-ports (decls)
  (append
   (verilog-decls-get-outputs decls)
   (verilog-decls-get-inouts decls)
   (verilog-decls-get-inputs decls)))

(defun verilog-decls-get-iovars (decls)
  (append
   (verilog-decls-get-vars decls)
   (verilog-decls-get-outputs decls)
   (verilog-decls-get-inouts decls)
   (verilog-decls-get-inputs decls)))

(defsubst verilog-modi-cache-add-outputs (modi sig-list)
  (verilog-modi-cache-add modi 'verilog-read-decls 0 sig-list))
(defsubst verilog-modi-cache-add-inouts (modi sig-list)
  (verilog-modi-cache-add modi 'verilog-read-decls 1 sig-list))
(defsubst verilog-modi-cache-add-inputs (modi sig-list)
  (verilog-modi-cache-add modi 'verilog-read-decls 2 sig-list))
(defsubst verilog-modi-cache-add-vars (modi sig-list)
  (verilog-modi-cache-add modi 'verilog-read-decls 3 sig-list))
(defsubst verilog-modi-cache-add-gparams (modi sig-list)
  (verilog-modi-cache-add modi 'verilog-read-decls 7 sig-list))


;;; Auto creation utilities:
;;

(defun verilog-auto-re-search-do (search-for func)
  "Given start brace BRA, and end brace KET, expand one line into many lines."
  (goto-char (point-min))
  (while (verilog-re-search-forward-quick search-for nil t)
    (funcall func)))

(defun verilog-insert-one-definition (sig type indent-pt)
  "Print out a definition for SIG of the given TYPE,
with appropriate INDENT-PT indentation."
  (indent-to indent-pt)
  ;; Note verilog-signals-matching-dir-re matches on this order
  (insert type)
  (when (verilog-sig-modport sig)
    (insert "." (verilog-sig-modport sig)))
  (when (verilog-sig-signed sig)
    (insert " " (verilog-sig-signed sig)))
  (when (verilog-sig-multidim sig)
    (insert " " (verilog-sig-multidim-string sig)))
  (when (verilog-sig-bits sig)
    (insert " " (verilog-sig-bits sig)))
  (indent-to (max 24 (+ indent-pt 16)))
  (unless (= (char-syntax (preceding-char)) ?\  )
    (insert " "))  ; Need space between "]name" if indent-to did nothing
  (insert (verilog-sig-name sig))
  (when (verilog-sig-memory sig)
    (insert " " (verilog-sig-memory sig))))

(defun verilog-insert-definition (modi sigs direction indent-pt v2k &optional dont-sort)
  "Print out a definition for MODI's list of SIGS of the given DIRECTION,
with appropriate INDENT-PT indentation.  If V2K, use Verilog 2001 I/O
format.  Sort unless DONT-SORT.  DIRECTION is normally wire/reg/output.
When MODI is non-null, also add to modi-cache, for tracking."
  (when modi
    (cond ((equal direction "wire")
	   (verilog-modi-cache-add-vars modi sigs))
	  ((equal direction "reg")
	   (verilog-modi-cache-add-vars modi sigs))
	  ((equal direction "output")
	   (verilog-modi-cache-add-outputs modi sigs)
	   (when verilog-auto-declare-nettype
	     (verilog-modi-cache-add-vars modi sigs)))
	  ((equal direction "input")
	   (verilog-modi-cache-add-inputs modi sigs)
	   (when verilog-auto-declare-nettype
	     (verilog-modi-cache-add-vars modi sigs)))
	  ((equal direction "inout")
	   (verilog-modi-cache-add-inouts modi sigs)
	   (when verilog-auto-declare-nettype
	     (verilog-modi-cache-add-vars modi sigs)))
	  ((equal direction "interface"))
	  ((equal direction "parameter")
	   (verilog-modi-cache-add-gparams modi sigs))
	  (t
	   (error "Unsupported verilog-insert-definition direction: `%s'" direction))))
  (or dont-sort
      (setq sigs (sort (copy-alist sigs) #'verilog-signals-sort-compare)))
  (while sigs
    (let ((sig (car sigs)))
      (verilog-insert-one-definition
       sig
       ;; Want "type x" or "output type x", not "wire type x"
       (cond ((and (equal "wire" verilog-auto-wire-type)
                   (or (not (verilog-sig-type sig))
                       (equal "logic" (verilog-sig-type sig))))
              (if (member direction '("input" "output" "inout"))
                  direction
                "wire"))
             ;;
             ((or (verilog-sig-type sig)
		  verilog-auto-wire-type)
	      (concat
	       (when (member direction '("input" "output" "inout"))
		 (concat direction " "))
               (or (verilog-sig-type sig)
                   verilog-auto-wire-type)))
             ;;
	     ((and verilog-auto-declare-nettype
		   (member direction '("input" "output" "inout")))
	      (concat direction " " verilog-auto-declare-nettype))
	     (t
	      direction))
       indent-pt)
      (insert (if v2k "," ";"))
      (if (or (not verilog-auto-wire-comment)
              (not (verilog-sig-comment sig))
              (equal "" (verilog-sig-comment sig)))
	  (insert "\n")
	(indent-to (max 48 (+ indent-pt 40)))
	(verilog-insert "// " (verilog-sig-comment sig) "\n"))
      (setq sigs (cdr sigs)))))

(defun verilog--insert-indent (indent-pt &rest stuff)
  "Indent to position stored in local `indent-pt' variable, then insert STUFF.
Presumes that any newlines end a list element."
  (let ((need-indent t))
    (while stuff
      (if need-indent (indent-to indent-pt))
      (setq need-indent nil)
      (verilog-insert (car stuff))
      (setq need-indent (string-match "\n$" (car stuff))
	    stuff (cdr stuff)))))

(defmacro verilog-insert-indent (&rest stuff)
  `(verilog--insert-indent indent-pt ,@stuff))

;;(let ((indent-pt 10)) (verilog-insert-indent "hello\n" "addon" "there\n"))

(defun verilog-forward-or-insert-line ()
  "Move forward a line, unless at EOB, then insert a newline."
  (if (eobp) (insert "\n")
    (forward-line)))

(defun verilog-repair-open-comma ()
  "Insert comma if previous argument is other than an open parenthesis or endif."
  ;; We can't just search backward for ) as it might be inside another expression.
  ;; Also want "`ifdef X   input foo   `endif" to just leave things to the human to deal with
  (save-excursion
    (verilog-backward-syntactic-ws-quick)
    (when (and (not (save-excursion  ; Not beginning (, or existing ,
		      (backward-char 1)
		      (looking-at "[(,]")))
               (not (save-excursion  ; Not attribute *)
		      (backward-char 2)
		      (looking-at "\\*)")))
               (not (save-excursion  ; Not `endif, or user define
		      (backward-char 1)
		      (skip-chars-backward "a-zA-Z0-9_`")
		      (looking-at "`"))))
      (insert ","))))

(defun verilog-repair-close-comma ()
  "If point is at a comma followed by a close parenthesis, fix it.
This repairs those mis-inserted by an AUTOARG."
  ;; It would be much nicer if Verilog allowed extra commas like Perl does!
  (save-excursion
    (verilog-forward-close-paren)
    (backward-char 1)
    (verilog-backward-syntactic-ws-quick)
    (backward-char 1)
    (when (looking-at ",")
      (delete-char 1))))

(defun verilog-make-width-expression (range-exp)
  "Return an expression calculating the length of a range [x:y] in RANGE-EXP."
  ;; strip off the []
  (cond ((not range-exp)
	 "1")
	(t
	 (if (string-match "^\\[\\(.*\\)\\]$" range-exp)
	     (setq range-exp (match-string 1 range-exp)))
	 (cond ((not range-exp)
		"1")
	       ;; [#:#] We can compute a numeric result
	       ((string-match "^\\s *\\([0-9]+\\)\\s *:\\s *\\([0-9]+\\)\\s *$"
			      range-exp)
		(int-to-string
		 (1+ (abs (- (string-to-number (match-string 1 range-exp))
			     (string-to-number (match-string 2 range-exp)))))))
	       ;; [PARAM-1:0] can just return PARAM
	       ((string-match "^\\s *\\([a-zA-Z_][a-zA-Z0-9_]*\\)\\s *-\\s *1\\s *:\\s *0\\s *$" range-exp)
		(match-string 1 range-exp))
	       ;; [arbitrary] need math
	       ((string-match "^\\(.*\\)\\s *:\\s *\\(.*\\)\\s *$" range-exp)
		(concat "(1+(" (match-string 1 range-exp) ")"
			(if (equal "0" (match-string 2 range-exp))
			    ""  ; Don't bother with -(0)
			  (concat "-(" (match-string 2 range-exp) ")"))
			")"))
	       (t nil)))))
;;(verilog-make-width-expression "`A:`B")

(defun verilog-simplify-range-expression (expr)
  "Return a simplified range expression with constants eliminated from EXPR."
  ;; Note this is always called with brackets; ie [z] or [z:z]
  (if (or (not verilog-auto-simplify-expressions)
          (not (string-match "[---+*/<>()]" expr)))
      expr  ; disabled or short-circuited
    (let ((out expr)
	  (last-pass ""))
      (while (not (equal last-pass out))
        (while (not (equal last-pass out))
          (setq last-pass out)
          ;; Prefix regexp needs beginning of match, or some symbol of
          ;; lesser or equal precedence.  We assume the [:]'s exist in expr.
          ;; Ditto the end.
          ;;(message "sre: out=%s" out)
          (while (string-match
                  (concat "\\([[({:*/<>+-]\\)"  ; - must be last
                          "(\\<\\([0-9A-Za-z_]+\\))"
                          "\\([])}:*/<>.+-]\\)")
                  out)
            (setq out (replace-match "\\1\\2\\3" nil nil out)))
          (while (string-match
                  (concat "\\([[({:*/<>+-]\\)"  ; - must be last
                          "\\$clog2\\s *(\\<\\([0-9]+\\))"
                          "\\([])}:*/<>+-]\\)")
                  out)
            (setq out (replace-match
                       (concat
                        (match-string 1 out)
                        (int-to-string (verilog-clog2 (string-to-number (match-string 2 out))))
                        (match-string 3 out))
                       nil nil out)))
          ;; For precedence do *,/ before +,-,>>,<<
          (while (and
                  (string-match
                   (concat "\\([[({:*/<>+-]\\)"
                           "\\([0-9]+\\)\\s *\\([*/]\\)\\s *\\([0-9]+\\)"
                           "\\([])}:*/<>+-]\\)")
                   out)
                  (not (and (equal (match-string 3 out) "/")
                            (not (equal 0 (% (string-to-number (match-string 2 out))
                                             (string-to-number (match-string 4 out))))))))
            (setq out (replace-match
                       (concat (match-string 1 out)
                               (if (equal (match-string 3 out) "/")
                                   (int-to-string (/ (string-to-number (match-string 2 out))
                                                     (string-to-number (match-string 4 out)))))
                               (if (equal (match-string 3 out) "*")
                                   (int-to-string (* (string-to-number (match-string 2 out))
                                                     (string-to-number (match-string 4 out)))))
                               (match-string 5 out))
                       nil nil out)))
          ;; Next precedence is +,-
          (while (string-match
                  (concat "\\([[({:<>+-]\\)"  ; No *,/ here as higher prec
                          "\\([0-9]+\\)\\s *\\([---+]\\)\\s *\\([0-9]+\\)"
                          "\\([])}:<>+-]\\)")
                  out)
            (let ((pre (match-string 1 out))
                  (lhs (string-to-number (match-string 2 out)))
                  (op (match-string 3 out))
                  (rhs (string-to-number (match-string 4 out)))
                  (post (match-string 5 out))
                  val)
              (when (equal pre "-")
                (setq lhs (- lhs)))
              (setq val (if (equal op "-")
                            (- lhs rhs)
                          (+ lhs rhs))
                    out (replace-match
                         (concat (cond ((and (equal pre "-")
                                             (< val 0))
                                        "")  ; Not "--20" but just "-20"
                                       ((and (equal pre "-")
                                             (> val 0))
                                        "+")  ; Not "-+20" but just "+20"
                                       (t pre))
                                 (int-to-string val)
                                 post)
                         nil nil out)) ))
          ;; Next precedence is >>,<<
          (while (string-match
                  (concat "\\([[({:]\\)"  ;; No << as not transitive
                          "\\([0-9]+\\)\\s *\\([<]\\{2,3\\}\\|[>]\\{2,3\\}\\)\\s *\\([0-9]+\\)"
                          "\\([])}:<>]\\)")
                  out)
            (setq out (replace-match
                       (concat (match-string 1 out)
                               (if (equal (match-string 3 out) ">>")
                                   (int-to-string (ash (string-to-number (match-string 2 out))
                                                       (* -1 (string-to-number (match-string 4 out))))))
                               (if (equal (match-string 3 out) ">>>")
                                   (int-to-string (ash (string-to-number (match-string 2 out))
                                                       (* -1 (string-to-number (match-string 4 out))))))
                               (if (equal (match-string 3 out) "<<")
                                   (int-to-string (ash (string-to-number (match-string 2 out))
                                                       (string-to-number (match-string 4 out)))))
                               (if (equal (match-string 3 out) "<<<")
                                   (int-to-string (ash (string-to-number (match-string 2 out))
                                                       (string-to-number (match-string 4 out)))))
                               (match-string 5 out))
                       nil nil out)))))
      out)))

;;(verilog-simplify-range-expression "[1:3]")  ; "[1:3]"
;;(verilog-simplify-range-expression "[(1):3]")  ; "[1:3]"
;;(verilog-simplify-range-expression "[(((16)+1)+1+(1+1))]")  ; "[20]"
;;(verilog-simplify-range-expression "[(2*3+6*7)]")  ; "[48]"
;;(verilog-simplify-range-expression "[(FOO*4-1*2)]")  ; "[FOO*4-2]"
;;(verilog-simplify-range-expression "[(FOO*4+1-1)]")  ; "[FOO*4+0]"
;;(verilog-simplify-range-expression "[(func(BAR))]")  ; "[func(BAR)]"
;;(verilog-simplify-range-expression "[FOO-1+1-1+1]")  ; "[FOO-0]"
;;(verilog-simplify-range-expression "[FOO-1+2:LSB-3+1]")  ; "[FOO+1:LSB-1]"
;;(verilog-simplify-range-expression "[$clog2(2)]")  ; "[1]"
;;(verilog-simplify-range-expression "[$clog2(7)]")  ; "[3]"
;;(verilog-simplify-range-expression "[(TEST[1])-1:0]")  ; "[(TEST[1])-1:0]"
;;(verilog-simplify-range-expression "[1<<2:8>>2]")  ; "[4:2]"
;;(verilog-simplify-range-expression "[2*4/(4-2) +2+4 <<4 >>2]")  ; "[8/(2) +2+4 <<4 >>2]"
;;(verilog-simplify-range-expression "[WIDTH*2/8-1:0]")  ; "[WIDTH*2/8-1:0]"
;;(verilog-simplify-range-expression "[(FOO).size:0]")  ; "[FOO.size:0]"

(defun verilog-clog2 (value)
  "Compute $clog2 - ceiling log2 of VALUE."
  (if (< value 1)
      0
    (ceiling (/ (log value) (log 2)))))

(defun verilog-typedef-name-p (variable-name)
  "Return non-nil if the VARIABLE-NAME is a type definition."
  (when verilog-typedef-regexp
    (verilog-string-match-fold verilog-typedef-regexp variable-name)))

;;; Auto deletion:
;;

(defun verilog-delete-autos-lined ()
  "Delete autos that occupy multiple lines, between begin and end comments."
  ;; The newline must not have a comment property, so we must
  ;; delete the end auto's newline, not the first newline
  (forward-line 1)
  (let ((pt (point)))
    (when (and
	   (looking-at "\\s-*// Beginning")
	   (search-forward "// End of automatic" nil t))
      ;; End exists
      (end-of-line)
      (forward-line 1)
      (delete-region pt (point)))))

(defun verilog-delete-empty-auto-pair ()
  "Delete begin/end auto pair at point, if empty."
  (forward-line 0)
  (when (looking-at (concat "\\s-*// Beginning of automatic.*\n"
			    "\\s-*// End of automatics\n"))
    (delete-region (point) (save-excursion (forward-line 2) (point)))))

(defun verilog-forward-close-paren ()
  "Find the close parenthesis that match the current point.
Ignore other close parenthesis with matching open parens."
  (let ((parens 1))
    (while (> parens 0)
      (unless (verilog-re-search-forward-quick "[()]" nil t)
	(error "%s: Mismatching ()" (verilog-point-text)))
      (cond ((= (preceding-char) ?\( )
	     (setq parens (1+ parens)))
	    ((= (preceding-char) ?\) )
	     (setq parens (1- parens)))))))

(defun verilog-backward-open-paren ()
  "Find the open parenthesis that match the current point.
Ignore other open parenthesis with matching close parens."
  (let ((parens 1))
    (while (> parens 0)
      (unless (verilog-re-search-backward-quick "[()]" nil t)
	(error "%s: Mismatching ()" (verilog-point-text)))
      (cond ((= (following-char) ?\) )
	     (setq parens (1+ parens)))
	    ((= (following-char) ?\( )
	     (setq parens (1- parens)))))))

(defun verilog-backward-open-bracket ()
  "Find the open bracket that match the current point.
Ignore other open bracket with matching close bracket."
  (let ((parens 1))
    (while (> parens 0)
      (unless (verilog-re-search-backward-quick "[][]" nil t)
	(error "%s: Mismatching []" (verilog-point-text)))
      (cond ((= (following-char) ?\] )
	     (setq parens (1+ parens)))
	    ((= (following-char) ?\[ )
	     (setq parens (1- parens)))))))

(defun verilog-delete-to-paren ()
  "Delete the automatic inst/sense/arg created by autos.
Deletion stops at the matching end parenthesis, outside comments."
  (delete-region (point)
		 (save-excursion
		   (verilog-backward-open-paren)
                   (verilog-forward-sexp-ign-cmt 1)  ; Moves to paren that closes argdecl's
		   (backward-char 1)
		   (point))))

(defun verilog-auto-star-safe ()
  "Return if a .* AUTOINST is safe to delete or expand.
It was created by the AUTOS themselves, or by the user."
  (and verilog-auto-star-expand
       (looking-at
	(concat "[ \t\n\f,]*\\([)]\\|// " verilog-inst-comment-re "\\)"))))

(defun verilog-delete-auto-star-all ()
  "Delete a .* AUTOINST, if it is safe."
  (when (verilog-auto-star-safe)
    (verilog-delete-to-paren)))

(defun verilog-delete-auto-star-implicit ()
  "Delete all .* implicit connections created by `verilog-auto-star'.
This function will be called automatically at save unless
`verilog-auto-star-save' is set, any non-templated expanded pins will be
removed."
  (interactive)
  (let (paren-pt indent have-close-paren)
    (save-excursion
      (goto-char (point-min))
      ;; We need to match these even outside of comments.
      ;; For reasonable performance, we don't check if inside comments, sorry.
      (while (re-search-forward "// Implicit \\.\\*" nil t)
	(setq paren-pt (point))
	(beginning-of-line)
	(setq have-close-paren
	      (save-excursion
		(when (search-forward ");" paren-pt t)
		  (setq indent (current-indentation))
		  t)))
	(delete-region (point) (+ 1 paren-pt))  ; Nuke line incl CR
	(when have-close-paren
	  ;; Delete extra commentary
	  (save-excursion
	    (while (progn
		     (forward-line -1)
		     (looking-at (concat "\\s *//\\s *" verilog-inst-comment-re "\n")))
	      (delete-region (match-beginning 0) (match-end 0))))
	  ;; If it is simple, we can put the ); on the same line as the last text
	  (let ((rtn-pt (point)))
	    (save-excursion
	      (while (progn (backward-char 1)
			    (looking-at "[ \t\n\f]")))
	      (when (looking-at ",")
		(delete-region (+ 1 (point)) rtn-pt))))
	  (when (bolp)
	    (indent-to indent))
	  (insert ");\n")
	  ;; Still need to kill final comma - always is one as we put one after the .*
	  (re-search-backward ",")
	  (delete-char 1))))))

(defun verilog-delete-auto-buffer ()
  "Perform `verilog-delete-auto' on the current buffer.
Intended for internal use inside a
`verilog-save-font-no-change-functions' block."
  ;; Allow user to customize
  (verilog-run-hooks 'verilog-before-delete-auto-hook)

  ;; Remove those that have multi-line insertions, possibly with parameters
  ;; We allow anything beginning with AUTO, so that users can add their own
  ;; patterns
  (verilog-auto-re-search-do
   (concat "/\\*AUTO[A-Za-z0-9_]+"
           ;; Optional parens or quoted parameter or .* for (((...)))
           "\\(\\|([^)]*)\\|(\"[^\"]*\")\\).*?"
           "\\*/")
   'verilog-delete-autos-lined)
  ;; Remove those that are in parenthesis
  (verilog-auto-re-search-do
   (concat "/\\*"
           (eval-when-compile
             (verilog-regexp-words
              '("AS" "AUTOARG" "AUTOCONCATWIDTH" "AUTOINST" "AUTOINSTPARAM"
                "AUTOSENSE")))
           "\\((.*?)\\)?"
           "\\*/")
   'verilog-delete-to-paren)
  ;; Do .* instantiations, but avoid removing any user pins by looking for our magic comments
  (verilog-auto-re-search-do "\\.\\*"
                             'verilog-delete-auto-star-all)
  ;; Remove template comments ... anywhere in case was pasted after AUTOINST removed
  (goto-char (point-min))
  (while (re-search-forward "\\s-*// \\(Templated\\(\\s-*AUTONOHOOKUP\\)?\\|Implicit \\.\\*\\)\\([ \tLT0-9]*\\| LHS: .*\\)$" nil t)
    (replace-match ""))

  ;; Final customize
  (verilog-run-hooks 'verilog-delete-auto-hook))

(defun verilog-delete-auto ()
  "Delete the automatic outputs, regs, and wires created by \\[verilog-auto].
Use \\[verilog-auto] to re-insert the updated AUTOs.

The hooks `verilog-before-delete-auto-hook' and `verilog-delete-auto-hook' are
called before and after this function, respectively."
  (interactive)
  (save-excursion
    (if (buffer-file-name)
        (find-file-noselect (buffer-file-name)))  ; To check we have latest version
    (verilog-save-font-no-change-functions
     (verilog-save-scan-cache
      (verilog-delete-auto-buffer)))))


;;; Auto inject:
;;

(defun verilog-inject-auto ()
  "Examine legacy non-AUTO code and insert AUTOs in appropriate places.

Any always @ blocks with sensitivity lists that match computed lists will
be replaced with /*AS*/ comments.

Any cells will get /*AUTOINST*/ added to the end of the pin list.
Pins with have identical names will be deleted.

Argument lists will not be deleted, /*AUTOARG*/ will only be inserted to
support adding new ports.  You may wish to delete older ports yourself.

For example:

        module ExampInject (i, o);
          input i;
          input j;
          output o;
          always @ (i or j)
             o = i | j;
          InstModule instName
            (.foobar(baz),
             .j(j));
        endmodule

Typing \\[verilog-inject-auto] (with an appropriate submodule not
shown) will make this into:

        module ExampInject (i, o/*AUTOARG*/
          // Inputs
          j);
          input i;
          output o;
          always @ (/*AS*/i or j)
             o = i | j;
          InstModule instName
            (.foobar(baz),
             /*AUTOINST*/
             // Outputs
             j(j));
        endmodule"
  (interactive)
  (verilog-auto t))

(defun verilog-inject-arg ()
  "Inject AUTOARG into new code.  See `verilog-inject-auto'."
  ;; Presume one module per file.
  (save-excursion
    (goto-char (point-min))
    (while (verilog-re-search-forward-quick "\\<\\(connect\\)?module\\>" nil t)
      (let ((endmodp (save-excursion
                      (verilog-re-search-forward-quick "\\<end\\(connect\\)?module\\>" nil t)
		       (point))))
	;; See if there's already a comment .. inside a comment so not verilog-re-search
	(when (not (re-search-forward "/\\*AUTOARG\\*/" endmodp t))
	  (verilog-re-search-forward-quick ";" nil t)
	  (backward-char 1)
	  (verilog-backward-syntactic-ws-quick)
	  (backward-char 1) ; Moves to paren that closes argdecl's
	  (when (looking-at ")")
	    (verilog-insert "/*AUTOARG*/")))))))

(defun verilog-inject-sense ()
  "Inject AUTOSENSE into new code.  See `verilog-inject-auto'."
  (save-excursion
    (goto-char (point-min))
    (while (verilog-re-search-forward-quick "\\<always\\s *@\\s *(" nil t)
      (let* ((start-pt (point))
	     (modi (verilog-modi-current))
	     (moddecls (verilog-modi-get-decls modi))
	     pre-sigs
	     got-sigs)
	(backward-char 1)
	(verilog-forward-sexp-ign-cmt 1)
        (backward-char 1)  ; End )
	(when (not (verilog-re-search-backward-quick "/\\*\\(AUTOSENSE\\|AS\\)\\*/" start-pt t))
	  (setq pre-sigs (verilog-signals-from-signame
			  (verilog-read-signals start-pt (point)))
		got-sigs (verilog-auto-sense-sigs moddecls nil))
	  (when (not (or (verilog-signals-not-in pre-sigs got-sigs)  ; Both are equal?
			 (verilog-signals-not-in got-sigs pre-sigs)))
	    (delete-region start-pt (point))
	    (verilog-insert "/*AS*/")))))))

(defun verilog-inject-inst ()
  "Inject AUTOINST into new code.  See `verilog-inject-auto'."
  (save-excursion
    (goto-char (point-min))
    ;; It's hard to distinguish modules; we'll instead search for pins.
    (while (verilog-re-search-forward-quick "\\.\\s *[a-zA-Z0-9`_$]+\\s *(\\s *[a-zA-Z0-9`_$]+\\s *)" nil t)
      (verilog-backward-open-paren)  ; Inst start
      (cond
       ((= (preceding-char) ?\#)  ; #(...) parameter section, not pin.  Skip.
	(forward-char 1)
        (verilog-forward-close-paren))  ; Parameters done
       (t
	(forward-char 1)
	(let ((indent-pt (+ (current-column)))
	      (end-pt (save-excursion (verilog-forward-close-paren) (point))))
	  (cond ((verilog-re-search-forward-quick "\\(/\\*AUTOINST\\((.*?)\\)?\\*/\\|\\.\\*\\)" end-pt t)
                 (goto-char end-pt))  ; Already there, continue search with next instance
		(t
		 ;; Delete identical interconnect
                 (let ((case-fold-search nil))  ; So we don't convert upper-to-lower, etc
		   (while (verilog-re-search-forward-quick "\\.\\s *\\([a-zA-Z0-9`_$]+\\)\\s *(\\s *\\1\\s *)\\s *" end-pt t)
		     (delete-region (match-beginning 0) (match-end 0))
                     (setq end-pt (- end-pt (- (match-end 0) (match-beginning 0))))  ; Keep it correct
		     (while (or (looking-at "[ \t\n\f,]+")
				(looking-at "//[^\n]*"))
		       (delete-region (match-beginning 0) (match-end 0))
		       (setq end-pt (- end-pt (- (match-end 0) (match-beginning 0)))))))
		 (verilog-forward-close-paren)
		 (backward-char 1)
		 ;; Not verilog-re-search, as we don't want to strip comments
		 (while (re-search-backward "[ \t\n\f]+" (- (point) 1) t)
		   (delete-region (match-beginning 0) (match-end 0)))
		 (verilog-insert "\n")
		 (verilog-insert-indent "/*AUTOINST*/")))))))))

;;
;; Auto diff:
;;

(defun verilog-diff-buffers-p (b1 b2 &optional whitespace regexp)
  "Return nil if buffers B1 and B2 have same contents.
Else, return point in B1 that first mismatches.
If optional WHITESPACE true, ignore whitespace.
If optional REGEXP, ignore differences matching it."
  (save-excursion
    (let* ((case-fold-search nil)  ; compare-buffer-substrings cares
	   (p1 (with-current-buffer b1 (goto-char (point-min))))
	   (p2 (with-current-buffer b2 (goto-char (point-min))))
	   (maxp1 (with-current-buffer b1 (point-max)))
	   (maxp2 (with-current-buffer b2 (point-max)))
	   (op1 -1) (op2 -1)
	   progress size)
      (while (not (and (eq p1 op1) (eq p2 op2)))
	;; If both windows have whitespace optionally skip over it.
	(when whitespace
	  ;; skip-syntax-* doesn't count \n
	  (with-current-buffer b1
	    (goto-char p1)
	    (skip-chars-forward " \t\n\r\f\v")
	    (setq p1 (point)))
	  (with-current-buffer b2
	    (goto-char p2)
	    (skip-chars-forward " \t\n\r\f\v")
	    (setq p2 (point))))
	(when regexp
	  (with-current-buffer b1
	    (goto-char p1)
	    (when (looking-at regexp)
              (setq p1 (match-end 0))))
	  (with-current-buffer b2
	    (goto-char p2)
	    (when (looking-at regexp)
              (setq p2 (match-end 0)))))
	(setq size (min (- maxp1 p1) (- maxp2 p2)))
	(setq progress (compare-buffer-substrings b2 p2 (+ size p2)
						  b1 p1 (+ size p1)))
	(setq progress (if (zerop progress) size (1- (abs progress))))
	(setq op1 p1  op2 p2
	      p1 (+ p1 progress)
	      p2 (+ p2 progress)))
      ;; Return value
      (if (and (eq p1 maxp1) (eq p2 maxp2))
	  nil p1))))

(defun verilog-diff-file-with-buffer (f1 b2 &optional whitespace show)
  "View the differences between file F1 and buffer B2.
This requires the external program `diff-command' to be in your `exec-path',
and uses `diff-switches' in which you may want to have \"-u\" flag.
Ignores WHITESPACE if t, and writes output to stdout if SHOW."
  ;; Similar to `diff-buffer-with-file' but works on Emacs 21, and
  ;; doesn't call `diff' as `diff' has different calling semantics on
  ;; different versions of Emacs.
  (if (not (file-exists-p f1))
      (message "Buffer `%s' has no associated file on disk" b2)
    (let ((outbuf (get-buffer "*Verilog-Diff*"))
          (f2 (make-temp-file "vm-diff-auto-")))
      (unwind-protect
          ;; User may want -u in `diff-switches'.
          (let ((args `(,@(if (listp diff-switches)
                              diff-switches
                            (list diff-switches))
                        ,@(and whitespace '("-b"))
                        ,f1 ,f2)))
            (with-current-buffer b2
              (save-restriction
                (widen)
                (write-region (point-min) (point-max) f2 nil 'nomessage)))
            (apply #'call-process diff-command nil outbuf t args)
            ;; Print out results.  Alternatively we could have call-processed
            ;; ourself, but this way we can reuse diff switches.
            (when show
              (with-current-buffer outbuf (message "%s" (buffer-string)))))
        (sit-for 0)
        (condition-case nil
            (delete-file f2)
          (error nil))))))

(defun verilog-diff-report (b1 b2 diffpt)
  "Report differences detected with `verilog-diff-auto'.
Differences are between buffers B1 and B2, starting at point
DIFFPT.  This function is called via `verilog-diff-function'."
  (let ((name1 (with-current-buffer b1 (buffer-file-name))))
    (verilog-warn-error "%s:%d: Difference in AUTO expansion found"
                        name1 (with-current-buffer b1
                                (count-lines (point-min) diffpt)))
    (cond (noninteractive
	   (verilog-diff-file-with-buffer name1 b2 t t))
	  (t
	   (ediff-buffers b1 b2)))))

(defun verilog-diff-auto ()
  "Expand AUTOs in a temporary buffer and indicate any change.
Whitespace is ignored when detecting differences, but once a
difference is detected, whitespace differences may be shown.

To call this from the command line, see \\[verilog-batch-diff-auto].

The action on differences is selected with
`verilog-diff-function'.  The default is `verilog-diff-report'
which will report an error and run `ediff' in interactive mode,
or `diff' in batch mode."
  (interactive)
  (let ((b1 (current-buffer)) b2 diffpt
	(name1 (buffer-file-name))
	(newname "*Verilog-Diff*"))
    (save-excursion
      (when (get-buffer newname)
	(kill-buffer newname))
      (setq b2 (let (buffer-file-name)  ; Else clone is upset
		 (clone-buffer newname)))
      (with-current-buffer b2
	;; auto requires the filename, but can't have same filename in two
	;; buffers; so override both b1 and b2's names
	(let ((buffer-file-name name1))
	  (unwind-protect
	      (progn
		(with-current-buffer b1 (setq buffer-file-name nil))
		(verilog-auto)
                (verilog-star-cleanup))
	    ;; Restore name if unwind
	    (with-current-buffer b1 (setq buffer-file-name name1)))))
      ;;
      (setq diffpt (verilog-diff-buffers-p b1 b2 t verilog-diff-ignore-regexp))
      (cond ((not diffpt)
	     (unless noninteractive (message "AUTO expansion identical"))
             (kill-buffer newname))  ; Nice to cleanup after oneself
	    (t
	     (funcall verilog-diff-function b1 b2 diffpt)))
      ;; Return result of compare
      diffpt)))

;;
;; Auto save
;;

(defun verilog-star-cleanup ()
  "On saving or diff, cleanup .* expansions."
  (when (not verilog-auto-star-save)
    (verilog-delete-auto-star-implicit)))

(defun verilog-auto-save-check ()
  "On saving see if we need auto update."
  (cond ((not verilog-auto-save-policy)) ; disabled
	((not (save-excursion
		(save-match-data
		  (let ((case-fold-search nil))
		    (goto-char (point-min))
		    (re-search-forward "AUTO" nil t))))))
	((eq verilog-auto-save-policy 'force)
	 (verilog-auto))
	((not (buffer-modified-p)))
	((eq verilog-auto-update-tick (buffer-chars-modified-tick))) ; up-to-date
	((eq verilog-auto-save-policy 'detect)
	 (verilog-auto))
	(t
	 (when (yes-or-no-p "AUTO statements not recomputed, do it now? ")
	   (verilog-auto))
	 ;; Don't ask again if didn't update
	 (set (make-local-variable 'verilog-auto-update-tick) (buffer-chars-modified-tick))))
  (verilog-star-cleanup)
  nil)  ; Always return nil -- we don't write the file ourselves

(defun verilog-auto-read-locals ()
  "Return file local variable segment at bottom of file."
  (save-excursion
    (goto-char (point-max))
    (if (re-search-backward "Local Variables:" nil t)
	(buffer-substring-no-properties (point) (point-max))
      "")))

(defun verilog-auto-reeval-locals (&optional force)
  "Read file local variable segment at bottom of file if it has changed.
If FORCE, always reread it."
  (let ((curlocal (verilog-auto-read-locals)))
    (when (or force (not (equal verilog-auto-last-file-locals curlocal)))
      (set (make-local-variable 'verilog-auto-last-file-locals) curlocal)
      ;; Note this may cause this function to be recursively invoked,
      ;; because hack-local-variables may call (verilog-mode)
      ;; The above when statement will prevent it from recursing forever.
      (hack-local-variables)
      t)))

;;; Auto creation:
;;

(defun verilog-auto-arg-ports (sigs message indent-pt)
  "Print a list of ports for AUTOARG.
Takes SIGS list, adds MESSAGE to front and inserts each at INDENT-PT."
  (when sigs
    (when verilog-auto-arg-sort
      (setq sigs (sort (copy-alist sigs) #'verilog-signals-sort-compare)))
    (insert "\n")
    (indent-to indent-pt)
    (insert message)
    (insert "\n")
    (let ((space ""))
      (indent-to indent-pt)
      (while sigs
	(cond ((equal verilog-auto-arg-format 'single)
	       (insert space)
	       (indent-to indent-pt)
	       (setq space "\n"))
	      ;; verilog-auto-arg-format 'packed
	      ((> (+ 2 (current-column) (length (verilog-sig-name (car sigs)))) fill-column)
	       (insert "\n")
	       (indent-to indent-pt)
	       (setq space " "))
	      (t
	       (insert space)
	       (setq space " ")))
	(insert (verilog-sig-name (car sigs)) ",")
	(setq sigs (cdr sigs))))))

(defun verilog-auto-arg ()
  "Expand AUTOARG statements.
Replace the argument declarations at the beginning of the
module with ones automatically derived from input and output
statements.  This can be dangerous if the module is instantiated
using position-based connections, so use only name-based when
instantiating the resulting module.  Long lines are split based
on the `fill-column', see \\[set-fill-column].

Limitations:
  Concatenation and outputting partial buses is not supported.

  Typedefs must match `verilog-typedef-regexp', which is disabled by default.

For example:

        module ExampArg (/*AUTOARG*/);
          input i;
          output o;
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampArg (/*AUTOARG*/
          // Outputs
          o,
          // Inputs
          i);
          input i;
          output o;
        endmodule

The argument declarations may be printed in declaration order to
best suit order based instantiations, or alphabetically, based on
the `verilog-auto-arg-sort' variable.

Formatting is controlled with `verilog-auto-arg-format' variable.

Any ports declared between the ( and /*AUTOARG*/ are presumed to be
predeclared and are not redeclared by AUTOARG.  AUTOARG will make a
conservative guess on adding a comma for the first signal, if you have
any ifdefs or complicated expressions before the AUTOARG you will need
to choose the comma yourself.

Avoid declaring ports manually, as it makes code harder to maintain."
  (save-excursion
    (let* ((modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (skip-pins (aref (verilog-read-arg-pins) 0)))
      (verilog-repair-open-comma)
      (verilog-auto-arg-ports (verilog-signals-not-in
			       (verilog-decls-get-outputs moddecls)
			       skip-pins)
			      "// Outputs"
			      verilog-indent-level-declaration)
      (verilog-auto-arg-ports (verilog-signals-not-in
			       (verilog-decls-get-inouts moddecls)
			       skip-pins)
			      "// Inouts"
			      verilog-indent-level-declaration)
      (verilog-auto-arg-ports (verilog-signals-not-in
			       (verilog-decls-get-inputs moddecls)
			       skip-pins)
			      "// Inputs"
			      verilog-indent-level-declaration)
      (verilog-repair-close-comma)
      (unless (eq (char-before) ?/ )
	(insert "\n"))
      (indent-to verilog-indent-level-declaration))))

(defun verilog-auto-assign-modport ()
  "Expand AUTOASSIGNMODPORT statements, as part of \\[verilog-auto].
Take input/output/inout statements from the specified interface
and modport and use to build assignments into the modport, for
making verification modules that connect to UVM interfaces.

  The first parameter is the name of an interface.

  The second parameter is a regexp of modports to read from in
  that interface.

  The third parameter is the instance name to use to dot reference into.

  The optional fourth parameter is a regular expression, and only
  signals matching the regular expression will be included.

  The optional fifth parameter is a prefix to add to the signals.

Limitations:

  Interface names must be resolvable to filenames.  See `verilog-auto-inst'.

  Inouts are not supported, as assignments must be unidirectional.

  If a signal is part of the interface header and in both a
  modport and the interface itself, it will not be listed.  (As
  this would result in a syntax error when the connections are
  made.)

See the example in `verilog-auto-inout-modport'."
  (save-excursion
    (let* ((params (verilog-read-auto-params 3 5))
	   (submod (nth 0 params))
	   (modport-re (nth 1 params))
	   (inst-name (nth 2 params))
	   (regexp (nth 3 params))
           (prefix (nth 4 params))
           ;; direction-re  ; direction argument not supported until requested
           submodi)
      ;; Lookup position, etc of co-module
      ;; Note this may raise an error
      (when (setq submodi (verilog-modi-lookup submod t))
	(let* ((indent-pt (current-indentation))
	       (submoddecls (verilog-modi-get-decls submodi))
	       (submodportdecls (verilog-modi-modport-lookup submodi modport-re))
               (sig-list-i (verilog-signals-in  ; Decls doesn't have data types, must resolve
			    (verilog-decls-get-vars submoddecls)
			    (verilog-signals-not-in
			     (verilog-decls-get-inputs submodportdecls)
			     (verilog-decls-get-ports submoddecls))))
               (sig-list-o (verilog-signals-in  ; Decls doesn't have data types, must resolve
			    (verilog-decls-get-vars submoddecls)
			    (verilog-signals-not-in
			     (verilog-decls-get-outputs submodportdecls)
			     (verilog-decls-get-ports submoddecls)))))
	  (forward-line 1)
	  (setq sig-list-i  (verilog-signals-edit-wire-reg
			     (verilog-signals-matching-dir-re
			      (verilog-signals-matching-regexp sig-list-i regexp)
                             "input" nil)) ;; direction-re
		sig-list-o  (verilog-signals-edit-wire-reg
			     (verilog-signals-matching-dir-re
			      (verilog-signals-matching-regexp sig-list-o regexp)
                             "output" nil))) ;; direction-re
	  (setq sig-list-i (sort (copy-alist sig-list-i) #'verilog-signals-sort-compare))
	  (setq sig-list-o (sort (copy-alist sig-list-o) #'verilog-signals-sort-compare))
	  (when (or sig-list-i sig-list-o)
	    (verilog-insert-indent "// Beginning of automatic assignments from modport\n")
	    ;; Don't sort them so an upper AUTOINST will match the main module
	    (let ((sigs sig-list-o))
	      (while sigs
                (verilog-insert-indent "assign "
                                       (concat prefix (verilog-sig-name (car sigs)))
                                       " = " inst-name
                                       "." (verilog-sig-name (car sigs)) ";\n")
		(setq sigs (cdr sigs))))
	    (let ((sigs sig-list-i))
	      (while sigs
                (verilog-insert-indent "assign " inst-name
                                       "." (verilog-sig-name (car sigs))
                                       " = "
                                       (concat prefix (verilog-sig-name (car sigs)))
                                       ";\n")
		(setq sigs (cdr sigs))))
	    (verilog-insert-indent "// End of automatics\n")))))))

(defun verilog-auto-inst-port-map (_port-st)
  nil)

;; These are used by user's AUTO_TEMPLATE Lisp expressions
(defvar vl-cell-type nil "See `verilog-auto-inst'.") ; Prevent compile warning
(defvar vl-cell-name nil "See `verilog-auto-inst'.") ; Prevent compile warning
(defvar vl-memory    nil "See `verilog-auto-inst'.") ; Prevent compile warning
(defvar vl-modport   nil "See `verilog-auto-inst'.") ; Prevent compile warning
(defvar vl-name  nil "See `verilog-auto-inst'.") ; Prevent compile warning
(defvar vl-width nil "See `verilog-auto-inst'.") ; Prevent compile warning
(defvar vl-dir   nil "See `verilog-auto-inst'.") ; Prevent compile warning
(defvar vl-bits  nil "See `verilog-auto-inst'.") ; Prevent compile warning
(defvar vl-mbits nil "See `verilog-auto-inst'.") ; Prevent compile warning

(defun verilog-auto-inst-port (section port-st indent-pt moddecls tpl-list tpl-num
                                       for-star par-values)
  "Print out an instantiation connection for this PORT-ST.
Inside SECTION, insert to INDENT-PT, use template TPL-LIST.
@ are instantiation numbers, replaced with TPL-NUM.
@\"(expression @)\" are evaluated, with @ as a variable.
If FOR-STAR add comment it is a .* expansion.
If PAR-VALUES replace final strings with these parameter values."
  (let* ((port (verilog-sig-name port-st))
	 (tpl-ass (or (assoc port (car tpl-list))
		      (verilog-auto-inst-port-map port-st)))
	 ;; vl-* are documented for user use
	 (vl-name (verilog-sig-name port-st))
	 (vl-width (verilog-sig-width port-st))
	 (vl-modport (verilog-sig-modport port-st))
	 (vl-memory (verilog-sig-memory port-st))
	 (vl-mbits (if (verilog-sig-multidim port-st)
                       (verilog-sig-multidim-string port-st) ""))
         (vl-bits (or (verilog-sig-bits port-st) ""))
	 (case-fold-search nil)
	 (check-values par-values)
         auto-inst-vector
         auto-inst-vector-tpl
         tpl-net dflt-bits)
    ;; Replace parameters in bit-width
    (when (and check-values
	       (not (equal vl-bits "")))
      (while check-values
	(setq vl-bits (verilog-string-replace-matches
		       (concat "\\<" (nth 0 (car check-values)) "\\>")
		       (concat "(" (nth 1 (car check-values)) ")")
		       t t vl-bits)
	      vl-mbits (verilog-string-replace-matches
			(concat "\\<" (nth 0 (car check-values)) "\\>")
			(concat "(" (nth 1 (car check-values)) ")")
			t t vl-mbits)
	      vl-memory (when vl-memory
                          (verilog-string-replace-matches
                           (concat "\\<" (nth 0 (car check-values)) "\\>")
                           (concat "(" (nth 1 (car check-values)) ")")
                           t t vl-memory))
	      check-values (cdr check-values)))
      (setq vl-bits (verilog-simplify-range-expression vl-bits)
	    vl-mbits (verilog-simplify-range-expression vl-mbits)
	    vl-memory (when vl-memory (verilog-simplify-range-expression vl-memory))
	    vl-width (verilog-make-width-expression vl-bits))) ; Not in the loop for speed
    (setq auto-inst-vector
          (if (or (eq verilog-auto-inst-vector t)
                  (and (eq verilog-auto-inst-vector `unsigned)
                       (not (verilog-sig-signed port-st)))
                  (not (assoc port (verilog-decls-get-signals moddecls)))
                  (not (equal (verilog-sig-bits port-st)
                              (verilog-sig-bits
                               (assoc port (verilog-decls-get-signals moddecls))))))
              vl-bits
            ""))
    ;; Default net value if not found
    (setq dflt-bits (if (or (and (verilog-sig-bits port-st)
                                 (verilog-sig-multidim port-st))
                            (verilog-sig-memory port-st))
			(concat "/*" vl-mbits vl-bits
                                ;; .[ used to separate packed from unpacked
                                (if vl-memory "." "")
                                (if vl-memory vl-memory "")
                                "*/")
                      (concat auto-inst-vector))
	  tpl-net (concat port
			  (if (and vl-modport
				   ;; .modport cannot be added if attachment is
				   ;; already declared as modport, VCS croaks
				   (let ((sig (assoc port (verilog-decls-get-interfaces moddecls))))
				     (not (and sig (verilog-sig-modport sig)))))
			      (concat "." vl-modport) "")
			  dflt-bits))
    ;; Find template
    (cond (tpl-ass  ; Template of exact port name
	   (setq tpl-net (nth 1 tpl-ass)))
	  ((nth 1 tpl-list) ; Wildcards in template, search them
	   (let ((wildcards (nth 1 tpl-list)))
	     (while wildcards
	       (when (string-match (nth 0 (car wildcards)) port)
		 (setq tpl-ass (car wildcards)  ; so allow @ parsing
		       tpl-net (replace-match (nth 1 (car wildcards))
					      t nil port)))
	       (setq wildcards (cdr wildcards))))))
    ;; Parse Templated variable
    (when tpl-ass
      ;; Evaluate @"(lispcode)"
      (when (string-match "@\".*[^\\]\"" tpl-net)
        (while (string-match "@\"\\(\\([^\\\"]\\|\\\\.\\)*\\)\"" tpl-net)
	  (setq tpl-net
		(concat
		 (substring tpl-net 0 (match-beginning 0))
		 (save-match-data
		   (let* ((expr (match-string 1 tpl-net))
			  (value
			   (progn
			     (setq expr (verilog-string-replace-matches "\\\\\"" "\"" nil nil expr))
			     (setq expr (verilog-string-replace-matches "@" tpl-num nil nil expr))
			     (prin1 (eval (car (read-from-string expr)))
				    (lambda (_ch) ())))))
		     (if (numberp value) (setq value (number-to-string value)))
		     value))
		 (substring tpl-net (match-end 0))))))
      ;; Get range based off template net
      (setq auto-inst-vector-tpl
            (if (or (eq verilog-auto-inst-vector t)
                    (and (eq verilog-auto-inst-vector `unsigned)
                         (not (verilog-sig-signed port-st)))
                    (not (assoc tpl-net (verilog-decls-get-signals moddecls)))
                    (not (equal (verilog-sig-bits port-st)
                                (verilog-sig-bits
                                 (assoc tpl-net (verilog-decls-get-signals moddecls))))))
                vl-bits
              ""))
      ;; Replace @ and [] magic variables in final output
      (setq tpl-net (verilog-string-replace-matches "@" tpl-num nil nil tpl-net))
      (setq tpl-net (verilog-string-replace-matches "\\[\\]\\[\\]" dflt-bits nil nil tpl-net))
      (setq tpl-net (verilog-string-replace-matches "\\[\\]" auto-inst-vector-tpl nil nil tpl-net)))
    ;; Insert it
    (when (or tpl-ass (not verilog-auto-inst-template-required))
      (verilog--auto-inst-first indent-pt section)
      (indent-to indent-pt)
      (insert "." port)
      (unless (and verilog-auto-inst-dot-name
                   (equal port tpl-net))
        (indent-to verilog-auto-inst-column)
        (insert "(" tpl-net ")"))
      (insert ",")
      (cond (tpl-ass
             (verilog-read-auto-template-hit tpl-ass)
             (indent-to (+ (if (< verilog-auto-inst-column 48) 24 16)
                           verilog-auto-inst-column))
             ;; verilog-insert requires the complete comment in one call - including the newline
             (cond ((equal verilog-auto-inst-template-numbers 'lhs)
                    (verilog-insert " // Templated"
                                    " LHS: " (nth 0 tpl-ass)))
                   (verilog-auto-inst-template-numbers
                    (verilog-insert " // Templated"
                                    " T" (int-to-string (nth 2 tpl-ass))
                                    " L" (int-to-string (nth 3 tpl-ass))))
                   (t
                    (verilog-insert " // Templated")))
             (verilog-insert (if (nth 4 tpl-ass) " AUTONOHOOKUP\n" "\n")))
            (for-star
             (indent-to (+ (if (< verilog-auto-inst-column 48) 24 16)
                           verilog-auto-inst-column))
             (verilog-insert " // Implicit .*\n"))
            (t
             (insert "\n"))))))
;;(verilog-auto-inst-port "" (list "foo" "[5:0]") 10 (list (list "foo" "a@\"(% (+ @ 1) 4)\"a")) "3")
;;(x "incom[@\"(+ (* 8 @) 7)\":@\"(* 8 @)\"]")
;;(x ".out (outgo[@\"(concat (+ (* 8 @) 7) \\\":\\\" ( * 8 @))\"]));")

(defvar verilog-auto-inst-first-section nil
  "Local first-in-section for `verilog-auto-inst-first'.")
(defvar verilog-auto-inst-first-any nil
  "Local first-in-any-section for `verilog-auto-inst-first'.")

(defun verilog--auto-inst-first (indent-pt section)
  "Insert , and SECTION before port, as part of \\[verilog-auto-inst]."
  ;; Do we need a trailing comma?
  ;; There maybe an ifdef or something similar before us.  What a mess.  Thus
  ;; to avoid trouble we only insert on preceding ) or *.
  ;; Insert first port on new line
  (when verilog-auto-inst-first-any
    (setq verilog-auto-inst-first-any nil)
    (insert "\n")  ; Must insert before search, so point will move forward if insert comma
    (save-excursion
      (verilog-re-search-backward-quick "[^ \t\n\f]" nil nil)
      (when (looking-at ")\\|\\*")  ; Generally don't insert, unless we are fairly sure
        (forward-char 1)
        (insert ","))))
  (when verilog-auto-inst-first-section
    (setq verilog-auto-inst-first-section nil)
    (verilog-insert-indent section)))

(defun verilog-auto-inst-port-list (section sig-list indent-pt moddecls
                                            tpl-list tpl-num for-star par-values)
  "For `verilog-auto-inst' print a list of ports using `verilog-auto-inst-port'."
  (when verilog-auto-inst-sort
    (setq sig-list (sort (copy-alist sig-list) #'verilog-signals-sort-compare)))
  (let ((verilog-auto-inst-first-section t))
    (mapc (lambda (port)
            (verilog-auto-inst-port section port indent-pt moddecls
                                    tpl-list tpl-num for-star par-values))
          sig-list)))

(defun verilog-auto-star ()
  "Expand SystemVerilog .* pins, as part of \\[verilog-auto].

If `verilog-auto-star-expand' is set, .* pins are treated if they were
AUTOINST statements, otherwise they are ignored.  For safety, Verilog mode
will also ignore any .* that are not last in your pin list (this prevents
it from deleting pins following the .* when it expands the AUTOINST.)

On writing your file, unless `verilog-auto-star-save' is set, any
non-templated expanded pins will be removed.  You may do this at any time
with \\[verilog-delete-auto-star-implicit].

If you are converting a module to use .* for the first time, you may wish
to use \\[verilog-inject-auto] and then replace the created AUTOINST with .*.

See `verilog-auto-inst' for examples, templates, and more information."
  (when (verilog-auto-star-safe)
    (verilog-auto-inst)))

(defun verilog-auto-inst ()
  "Expand AUTOINST statements, as part of \\[verilog-auto].
Replace the pin connections to an instantiation or interface
declaration with ones automatically derived from the module or
interface header of the instantiated item.

You may also provide an optional regular expression, in which
case only I/O matching the regular expression will be included,
or excluded if the regexp begins with ?! (question-mark
exclamation-mark).

If `verilog-auto-star-expand' is set, also expand SystemVerilog .* ports,
and delete them before saving unless `verilog-auto-star-save' is set.
See `verilog-auto-star' for more information.

The pins are printed in declaration order or alphabetically,
based on the `verilog-auto-inst-sort' variable.

To debug what file a submodule comes from, in a buffer with
AUTOINST, use \\[verilog-goto-defun] to switch buffers to the
point containing the given symbol (i.e. a submodule name)'s
module definition.

Limitations:
  Module names must be resolvable to filenames by adding a
  `verilog-library-extensions', and being found in the same directory, or
  by changing the variable `verilog-library-flags' or
  `verilog-library-directories'.  Macros `modname are translated through the
  vh-{name} Emacs variable, if that is not found, it just ignores the \\=`.

  In templates you must have one signal per line, ending in a ), or ));,
  and have proper () nesting, including a final ); to end the template.

  Typedefs must match `verilog-typedef-regexp', which is disabled by default.

  SystemVerilog multidimensional input/output has only experimental support.

  SystemVerilog .name syntax is used if `verilog-auto-inst-dot-name' is set.

  Parameters referenced by the instantiation will remain symbolic, unless
  `verilog-auto-inst-param-value' is set.

  Gate primitives (and/or) may have AUTOINST for the purpose of
  AUTOWIRE declarations, etc.  Gates are the only case when
  position based connections are passed.

  The array part of arrayed instances are ignored; this may
  result in undesirable default AUTOINST connections; use a
  template instead.

For example, first take the submodule InstModule.v:

        module InstModule (o,i);
           output [31:0] o;
           input i;
           wire [31:0] o = {32{i}};
        endmodule

This is then used in an upper level module:

        module ExampInst (o,i);
           output o;
           input i;
           InstModule instName
             (/*AUTOINST*/);
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampInst (o,i);
           output o;
           input i;
           InstModule instName
             (/*AUTOINST*/
              // Outputs
              .o        (o[31:0]),
              // Inputs
              .i        (i));
        endmodule

Where the list of inputs and outputs came from the inst module.

Exceptions:

  Unless you are instantiating a module multiple times, or the module is
  something trivial like an adder, DO NOT CHANGE SIGNAL NAMES ACROSS HIERARCHY.
  It just makes for unmaintainable code.  To sanitize signal names, try
  vrename from URL `https://www.veripool.org'.

  When you need to violate this suggestion there are two ways to list
  exceptions, placing them before the AUTOINST, or using templates.

  Any ports defined before the /*AUTOINST*/ are not included in the list of
  automatics.  This is similar to making a template as described below, but
  is restricted to simple connections just like you normally make.  Also note
  that any signals before the AUTOINST will only be picked up by AUTOWIRE if
  you have the appropriate // Input or // Output comment, and exactly the
  same line formatting as AUTOINST itself uses.

        InstModule instName
          (// Inputs
           .i           (my_i_dont_mess_with_it),
           /*AUTOINST*/
           // Outputs
           .o           (o[31:0]));


Templates:

  For multiple instantiations based upon a single template, create a
  commented out template:

        /* InstModule AUTO_TEMPLATE (
                .sig3   (sigz[]),
                );
        */

  Templates go ABOVE the instantiation(s).  When an instantiation is
  expanded `verilog-mode' simply searches up for the closest template.
  Thus you can have multiple templates for the same module, just alternate
  between the template for an instantiation and the instantiation itself.
  (For backward compatibility if no template is found above, it
  will also look below, but do not use this behavior in new designs.)

  The module name must be the same as the name of the module in the
  instantiation name, and the code \"AUTO_TEMPLATE\" must be in these exact
  words and capitalized.  Only signals that must be different for each
  instantiation need to be listed.

  Inside a template, a [] in a connection name (with nothing else
  inside the brackets) will be replaced by the same bus subscript
  as it is being connected to, or the [] will be removed if it is
  a single bit signal.

  Inside a template, a [][] in a connection name will behave
  similarly to a [] for scalar or single-dimensional connection;
  for a multidimensional connection it will print a comment
  similar to that printed when a template is not used.  Generally
  it is a good idea to do this for all connections in a template,
  as then they will work for any width signal, and with AUTOWIRE.
  See PTL_BUS becoming PTL_BUSNEW below.

  Inside a template, a [] in a connection name (with nothing else inside
  the brackets) will be replaced by the same bus subscript as it is being
  connected to, or the [] will be removed if it is a single bit signal.
  Generally it is a good idea to do this for all connections in a template,
  as then they will work for any width signal, and with AUTOWIRE.  See
  PTL_BUS becoming PTL_BUSNEW below.

  If you have a complicated template, set `verilog-auto-inst-template-numbers'
  to see which regexps are matching.  Don't leave that mode set after
  debugging is completed though, it will result in lots of extra differences
  and merge conflicts.

  If a connection name does not match any template, it is
  connected to a net by the same name as the port (unless
  `verilog-auto-inst-template-required' is true).

  Setting `verilog-auto-template-warn-unused' will report errors
  if any template lines are unused.

  For example:

        /* InstModule AUTO_TEMPLATE (
                .ptl_bus        (ptl_busnew[]),
                );
        */
        InstModule ms2m (/*AUTOINST*/);

  Typing \\[verilog-auto] will make this into:

        InstModule ms2m (/*AUTOINST*/
            // Outputs
            .NotInTemplate      (NotInTemplate),
            .ptl_bus            (ptl_busnew[3:0]),
            ....


Multiple Module Templates:

  The same template lines can be applied to multiple modules with
  the syntax as follows:

        /* InstModuleA AUTO_TEMPLATE
           InstModuleB AUTO_TEMPLATE
           InstModuleC AUTO_TEMPLATE
           InstModuleD AUTO_TEMPLATE (
                .ptl_bus        (ptl_busnew[]),
                );
        */

  Note there is only one AUTO_TEMPLATE opening parenthesis.

@ Templates:

  It is common to instantiate a cell multiple times, so templates make it
  trivial to substitute part of the cell name into the connection name.

        /* InstName AUTO_TEMPLATE <optional \"REGEXP\"> (
                .sig1   (sigx[@]),
                .sig2   (sigy[@\"(% (+ 1 @) 4)\"]),
                );
        */

  If no regular expression is provided immediately after the AUTO_TEMPLATE
  keyword, then the @ character in any connection names will be replaced
  with the instantiation number; the first digits found in the cell's
  instantiation name.

  If a regular expression is provided, the @ character will be replaced
  with the first () grouping that matches against the cell name.  Using a
  regexp of `\\([0-9]+\\)' provides identical values for @ as when no
  regexp is provided.  If you use multiple layers of parenthesis,
  `test\\([^0-9]+\\)_\\([0-9]+\\)' would replace @ with non-number
  characters after test and before _, whereas
  `\\(test\\([a-z]+\\)_\\([0-9]+\\)\\)' would replace @ with the entire
  match.

  For example:

        /* InstModule AUTO_TEMPLATE (
                .ptl_mapvalidx          (ptl_mapvalid[@]),
                .ptl_mapvalidp1x        (ptl_mapvalid[@\"(% (+ 1 @) 4)\"]),
                );
        */
        InstModule ms2m (/*AUTOINST*/);

  Typing \\[verilog-auto] will make this into:

        InstModule ms2m (/*AUTOINST*/
            // Outputs
            .ptl_mapvalidx              (ptl_mapvalid[2]),
            .ptl_mapvalidp1x            (ptl_mapvalid[3]));

  Note the @ character was replaced with the 2 from \"ms2m\".

  Alternatively, using a regular expression for @:

        /* InstModule AUTO_TEMPLATE \"_\\([a-z]+\\)\" (
                .ptl_mapvalidx          (@_ptl_mapvalid),
                .ptl_mapvalidp1x        (ptl_mapvalid_@),
                );
        */
        InstModule ms2_FOO (/*AUTOINST*/);
        InstModule ms2_BAR (/*AUTOINST*/);

  Typing \\[verilog-auto] will make this into:

        InstModule ms2_FOO (/*AUTOINST*/
            // Outputs
            .ptl_mapvalidx              (FOO_ptl_mapvalid),
            .ptl_mapvalidp1x            (ptl_mapvalid_FOO));
        InstModule ms2_BAR (/*AUTOINST*/
            // Outputs
            .ptl_mapvalidx              (BAR_ptl_mapvalid),
            .ptl_mapvalidp1x            (ptl_mapvalid_BAR));


Regexp Templates:

  A template entry of the form

            .pci_req\\([0-9]+\\)_l      (pci_req_jtag_[\\1]),

  will apply an Emacs style regular expression search for any port beginning
  in pci_req followed by numbers and ending in _l and connecting that to
  the pci_req_jtag_[] net, with the bus subscript coming from what matches
  inside the first set of \\( \\).  Thus pci_req2_l becomes pci_req_jtag_[2].

  Since \\([0-9]+\\) is so common and ugly to read, a @ in the port name
  does the same thing.  (Note a @ in the connection/replacement text is
  completely different -- still use \\1 there!)  Thus this is the same as
  the above template:

            .pci_req@_l         (pci_req_jtag_[\\1]),

  Here's another example to remove the _l, useful when naming conventions
  specify _ alone to mean active low.  Note the use of [] to keep the bus
  subscript:

            .\\(.*\\)_l         (\\1_[]),

Lisp Templates:

  First any regular expression template is expanded.

  If the syntax @\"( ... )\" is found in a connection, the expression in
  quotes will be evaluated as a Lisp expression, with @ replaced by the
  instantiation number.  The MAPVALIDP1X example above would put @+1 modulo
  4 into the brackets.  Quote all double-quotes inside the expression with
  a leading backslash (\\\"...\\\"); or if the Lisp template is also a
  regexp template backslash the backslash quote (\\\\\"...\\\\\").

  There are special variables defined that are useful in these
  Lisp functions:

        vl-name        Name portion of the input/output port.
        vl-bits        Bus bits portion of the input/output port (`[2:0]').
        vl-mbits       Multidimensional array bits for port (`[2:0][3:0]').
        vl-width       Width of the input/output port (`3' for [2:0]).
                       May be a (...) expression if bits isn't a constant.
        vl-dir         Direction of the pin input/output/inout/interface.
        vl-memory      The unpacked array part of the I/O port (`[5:0]').
        vl-modport     The modport, if an interface with a modport.
        vl-cell-type   Module name/type of the cell (`InstModule').
        vl-cell-name   Instance name of the cell (`instName').

  Normal Lisp variables may be used in expressions.  See
  `verilog-read-defines' which can set vh-{definename} variables for use
  here.  Also, any comments of the form:

        /*AUTO_LISP(setq foo 1)*/

  will evaluate any Lisp expression inside the parenthesis between the
  beginning of the buffer and the point of the AUTOINST.  This allows
  functions to be defined or variables to be changed between instantiations.
  (See also `verilog-auto-insert-lisp' if you want the output from your
  lisp function to be inserted.)

  Note that when using lisp expressions errors may occur when @ is not a
  number; you may need to use the standard Emacs Lisp functions
  `number-to-string' and `string-to-number'.

  After the evaluation is completed, @ substitution and [] substitution
  occur.


Ignoring Hookup:

  AUTOWIRE and related AUTOs will read the signals created by a template.
  To specify that a signal should not be parsed to participate in this
  hookup, add a AUTONOHOOKUP comment to the template.  For example:

            .pci_req_l  (pci_req_not_to_wire),  //AUTONOHOOKUP


For more information see the \\[verilog-faq] and forums at URL
`https://www.veripool.org'."
  (save-excursion
    ;; Find beginning
    (let* ((params (verilog-read-auto-params 0 1))
           (regexp (nth 0 params))
           (pt (point))
           (for-star (save-excursion (backward-char 2) (looking-at "\\.\\*")))
	   (indent-pt (save-excursion (verilog-backward-open-paren)
				      (1+ (current-column))))
	   (verilog-auto-inst-column (max verilog-auto-inst-column
					  (+ 16 (* 8 (/ (+ indent-pt 7) 8)))))
           (verilog-auto-inst-first-any t)
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   submod submodi submoddecls
           inst skip-pins tpl-list tpl-num par-values)

      ;; Find module name that is instantiated
      (setq submod  (verilog-read-inst-module)
	    inst (verilog-read-inst-name)
	    vl-cell-type submod
	    vl-cell-name inst
	    skip-pins (aref (verilog-read-inst-pins) 0))

      ;; Parse any AUTO_LISP() before here
      (verilog-read-auto-lisp (point-min) pt)

      ;; Read parameters (after AUTO_LISP)
      (setq par-values (and verilog-auto-inst-param-value
			    (verilog-read-inst-param-value)))

      ;; Lookup position, etc of submodule
      ;; Note this may raise an error
      (when (and (not (member submod verilog-gate-keywords))
		 (setq submodi (verilog-modi-lookup submod t)))
	(setq submoddecls (verilog-modi-get-decls submodi))
	;; If there's a number in the instantiation, it may be an argument to the
	;; automatic variable instantiation program.
	(let* ((tpl-info (verilog-read-auto-template submod))
	       (tpl-regexp (aref tpl-info 0)))
	  (setq tpl-num (if (verilog-string-match-fold tpl-regexp inst)
			    (match-string 1 inst)
			  "")
		tpl-list (aref tpl-info 1)))
	;; Find submodule's signals and dump
	(let ((sig-list (and (equal (verilog-modi-get-type submodi) "interface")
			     (verilog-signals-not-in
			      (verilog-decls-get-vars submoddecls)
			      skip-pins)))
	      (vl-dir "interfaced"))
          (when regexp
            (setq sig-list (verilog-signals-matching-regexp sig-list regexp)))
	  (when (and sig-list
		     verilog-auto-inst-interfaced-ports)
            ;; Note these are searched for in verilog-read-sub-decls.
            (verilog-auto-inst-port-list "// Interfaced\n"
                                         sig-list indent-pt moddecls
					 tpl-list tpl-num for-star par-values)))
	(let ((sig-list (verilog-signals-not-in
			 (verilog-decls-get-interfaces submoddecls)
			 skip-pins))
	      (vl-dir "interface"))
          (when regexp
            (setq sig-list (verilog-signals-matching-regexp sig-list regexp)))
	  (when sig-list
            ;; Note these are searched for in verilog-read-sub-decls.
            (verilog-auto-inst-port-list "// Interfaces\n"
                                         sig-list indent-pt moddecls
                                         tpl-list tpl-num for-star par-values)))
	(let ((sig-list (verilog-signals-not-in
			 (verilog-decls-get-outputs submoddecls)
			 skip-pins))
	      (vl-dir "output"))
          (when regexp
            (setq sig-list (verilog-signals-matching-regexp sig-list regexp)))
	  (when sig-list
            (verilog-auto-inst-port-list "// Outputs\n"
                                         sig-list indent-pt moddecls
					 tpl-list tpl-num for-star par-values)))
	(let ((sig-list (verilog-signals-not-in
			 (verilog-decls-get-inouts submoddecls)
			 skip-pins))
	      (vl-dir "inout"))
          (when regexp
            (setq sig-list (verilog-signals-matching-regexp sig-list regexp)))
	  (when sig-list
            (verilog-auto-inst-port-list "// Inouts\n"
                                         sig-list indent-pt moddecls
					 tpl-list tpl-num for-star par-values)))
	(let ((sig-list (verilog-signals-not-in
			 (verilog-decls-get-inputs submoddecls)
			 skip-pins))
	      (vl-dir "input"))
          (when regexp
            (setq sig-list (verilog-signals-matching-regexp sig-list regexp)))
	  (when sig-list
            (verilog-auto-inst-port-list "// Inputs\n"
                                         sig-list indent-pt moddecls
					 tpl-list tpl-num for-star par-values)))
	;; Kill extra semi
	(save-excursion
          (cond ((not verilog-auto-inst-first-any)
		 (re-search-backward "," pt t)
		 (delete-char 1)
                 (when (looking-at "  ")
                   (delete-char 1))  ; so we can align // Templated comments
                 (insert ");")
                 (search-forward "\n")  ; Added by inst-port
		 (delete-char -1)
                 (if (search-forward ")" nil t)  ; From user, moved up a line
		     (delete-char -1))
                 (if (search-forward ";" nil t)  ; Don't error if user had syntax error and forgot it
		     (delete-char -1)))))))))

(defun verilog-auto-inst-param ()
  "Expand AUTOINSTPARAM statements, as part of \\[verilog-auto].
Replace the parameter connections to an instantiation with ones
automatically derived from the module header of the instantiated netlist.

You may also provide an optional regular expression, in which
case only parameters matching the regular expression will be
included, or excluded if the regexp begins with ?! (question-mark
exclamation-mark).

See \\[verilog-auto-inst] for limitations, and templates to customize the
output.

For example, first take the submodule InstModule.v:

        module InstModule (o,i);
           parameter PAR;
        endmodule

This is then used in an upper level module:

        module ExampInstParam (o,i);
           parameter PAR;
           InstModule #(/*AUTOINSTPARAM*/)
                instName (/*AUTOINST*/);
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampInstParam (o,i);
           parameter PAR;
           InstModule #(/*AUTOINSTPARAM*/
                        // Parameters
                        .PAR    (PAR))
                instName (/*AUTOINST*/);
        endmodule

Where the list of parameter connections come from the inst module.

Templates:

  You can customize the parameter connections using AUTO_TEMPLATEs,
  just as you would with \\[verilog-auto-inst]."
  (save-excursion
    ;; Find beginning
    (let* ((params (verilog-read-auto-params 0 1))
           (regexp (nth 0 params))
           (pt (point))
	   (indent-pt (save-excursion (verilog-backward-open-paren)
				      (1+ (current-column))))
	   (verilog-auto-inst-column (max verilog-auto-inst-column
					  (+ 16 (* 8 (/ (+ indent-pt 7) 8)))))
           (verilog-auto-inst-first-any t)
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   submod submodi submoddecls
           inst skip-pins tpl-list tpl-num)
      ;; Find module name that is instantiated
      (setq submod (save-excursion
		     ;; Get to the point where AUTOINST normally is to read the module
		     (verilog-re-search-forward-quick "[(;]" nil nil)
		     (verilog-read-inst-module))
	    inst   (save-excursion
		     ;; Get to the point where AUTOINST normally is to read the module
		     (verilog-re-search-forward-quick "[(;]" nil nil)
		     (verilog-read-inst-name))
	    vl-cell-type submod
	    vl-cell-name inst
	    skip-pins (aref (verilog-read-inst-pins) 0))

      ;; Parse any AUTO_LISP() before here
      (verilog-read-auto-lisp (point-min) pt)

      ;; Lookup position, etc of submodule
      ;; Note this may raise an error
      (when (setq submodi (verilog-modi-lookup submod t))
	(setq submoddecls (verilog-modi-get-decls submodi))
	;; If there's a number in the instantiation, it may be an argument to the
	;; automatic variable instantiation program.
	(let* ((tpl-info (verilog-read-auto-template submod))
	       (tpl-regexp (aref tpl-info 0)))
	  (setq tpl-num (if (verilog-string-match-fold tpl-regexp inst)
			    (match-string 1 inst)
			  "")
		tpl-list (aref tpl-info 1)))
	;; Find submodule's signals and dump
	(let ((sig-list (verilog-signals-not-in
			 (verilog-decls-get-gparams submoddecls)
			 skip-pins))
	      (vl-dir "parameter"))
          (when regexp
            (setq sig-list (verilog-signals-matching-regexp sig-list regexp)))
	  (when sig-list
            ;; Note these are searched for in verilog-read-sub-decls.
            (verilog-auto-inst-port-list "// Parameters\n"
                                         sig-list indent-pt moddecls
					 tpl-list tpl-num nil nil)))
	;; Kill extra semi
	(save-excursion
          (cond ((not verilog-auto-inst-first-any)
		 (re-search-backward "," pt t)
		 (delete-char 1)
		 (insert ")")
                 (search-forward "\n")  ; Added by inst-port
		 (delete-char -1)
                 (if (search-forward ")" nil t)  ; From user, moved up a line
		     (delete-char -1)))))))))

(defun verilog-auto-reg ()
  "Expand AUTOREG statements, as part of \\[verilog-auto].
Make reg statements for any output that isn't already declared,
and isn't a wire output from a block.  `verilog-auto-wire-type'
may be used to change the datatype of the declarations.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see `verilog-read-sub-decls').

  This does NOT work on memories, declare those yourself.

An example:

        module ExampReg (o,i);
           output o;
           input i;
           /*AUTOREG*/
           always o = i;
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampReg (o,i);
           output o;
           input i;
           /*AUTOREG*/
           // Beginning of automatic regs
           reg          o;
           // End of automatics
           always o = i;
        endmodule"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (modsubdecls (verilog-modi-get-sub-decls modi))
	   (sig-list (verilog-signals-not-in
		      (verilog-decls-get-outputs moddecls)
                      (append (verilog-signals-with  ; ignore typed signals
			       'verilog-sig-type
			       (verilog-decls-get-outputs moddecls))
			      (verilog-decls-get-vars moddecls)
			      (verilog-decls-get-assigns moddecls)
			      (verilog-decls-get-consts moddecls)
			      (verilog-decls-get-gparams moddecls)
			      (verilog-subdecls-get-interfaced modsubdecls)
			      (verilog-subdecls-get-outputs modsubdecls)
			      (verilog-subdecls-get-inouts modsubdecls)))))
      (when sig-list
	(verilog-forward-or-insert-line)
	(verilog-insert-indent "// Beginning of automatic regs (for this module's undeclared outputs)\n")
	(verilog-insert-definition modi sig-list "reg" indent-pt nil)
	(verilog-insert-indent "// End of automatics\n")))))

(defun verilog-auto-reg-input ()
  "Expand AUTOREGINPUT statements, as part of \\[verilog-auto].
Make reg statements instantiation inputs that aren't already
declared or assigned to.  This is useful for making a top level
shell for testing the module that is to be instantiated.

Limitations:
  This ONLY detects inputs of AUTOINSTants (see `verilog-read-sub-decls').

  This does NOT work on memories, declare those yourself.

  Assignments cause the assigned-to variable not to be declared unless
  the name matches `verilog-auto-reg-input-assigned-ignore-regexp'.

An example (see `verilog-auto-inst' for what else is going on here):

        module InstModule (input i);
        endmodule

        module ExampRegInput ();
           /*AUTOREGINPUT*/
           InstModule instName
             (/*AUTOINST*/);
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampRegInput ();
           /*AUTOREGINPUT*/
           // Beginning of automatic reg inputs
           reg          i;      // To instName of InstModule.v
           // End of automatics
           InstModule instName
             (/*AUTOINST*/
              // Inputs
              .i                (i));
        endmodule"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (modsubdecls (verilog-modi-get-sub-decls modi))
	   (sig-list (verilog-signals-combine-bus
		      (verilog-signals-not-in
		       (append (verilog-subdecls-get-inputs modsubdecls)
			       (verilog-subdecls-get-inouts modsubdecls))
		       (append (verilog-decls-get-signals moddecls)
                               (verilog-signals-not-matching-regexp
                                (verilog-decls-get-assigns moddecls)
                                verilog-auto-reg-input-assigned-ignore-regexp))))))
      (when sig-list
	(verilog-forward-or-insert-line)
	(verilog-insert-indent "// Beginning of automatic reg inputs (for undeclared instantiated-module inputs)\n")
	(verilog-insert-definition modi sig-list "reg" indent-pt nil)
	(verilog-insert-indent "// End of automatics\n")))))

(defun verilog-auto-logic-setup ()
  "Prepare variables due to AUTOLOGIC."
  (unless verilog-auto-wire-type
    (set (make-local-variable 'verilog-auto-wire-type)
	 "logic")))

(defun verilog-auto-logic ()
  "Expand AUTOLOGIC statements, as part of \\[verilog-auto].
Make wire statements using the SystemVerilog logic keyword.
This is currently equivalent to:

    /*AUTOWIRE*/

with the below at the bottom of the file

    // Local Variables:
    // verilog-auto-wire-type:\"logic\"
    // End:

In the future AUTOLOGIC may declare additional identifiers,
while AUTOWIRE will not."
  (save-excursion
    (verilog-auto-logic-setup)
    (verilog-auto-wire)))

(defun verilog-auto-wire ()
  "Expand AUTOWIRE statements, as part of \\[verilog-auto].
Make wire statements for instantiations outputs that aren't
already declared.  `verilog-auto-wire-type' may be used to change
the datatype of the declarations.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see `verilog-read-sub-decls'),
  and all buses must have widths, such as those from AUTOINST, or using []
  in AUTO_TEMPLATEs.

  This does NOT work on memories or SystemVerilog .name connections,
  declare those yourself.

  Verilog mode will add \"Couldn't Merge\" comments to signals it cannot
  determine how to bus together.  This occurs when you have ports with
  non-numeric or non-sequential bus subscripts.  If Verilog mode
  mis-guessed, you'll have to declare them yourself.

An example (see `verilog-auto-inst' for what else is going on here):

        module ExampWire (i);
           input i;
           /*AUTOWIRE*/
           InstModule instName
             (/*AUTOINST*/);
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampWire (i);
           input i;
           /*AUTOWIRE*/
           // Beginning of automatic wires
           wire [31:0]  o;      // From instName of InstModule.v
           // End of automatics
           InstModule instName
             (/*AUTOINST*/
              // Outputs
              .o        (o[31:0]),
              // Inputs
              .i        (i));
           wire o = | ov;
        endmodule"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (modsubdecls (verilog-modi-get-sub-decls modi))
	   (sig-list (verilog-signals-combine-bus
		      (verilog-signals-not-in
		       (append (verilog-subdecls-get-outputs modsubdecls)
			       (verilog-subdecls-get-inouts modsubdecls))
		       (verilog-decls-get-signals moddecls)))))
      (when sig-list
	(verilog-forward-or-insert-line)
	(verilog-insert-indent "// Beginning of automatic wires (for undeclared instantiated-module outputs)\n")
	(verilog-insert-definition modi sig-list "wire" indent-pt nil)
	(verilog-insert-indent "// End of automatics\n")
	;; We used to optionally call verilog-pretty-declarations and
	;; verilog-pretty-expr here, but it's too slow on huge modules,
	;; plus makes everyone's module change. Finally those call
	;; syntax-ppss which is broken when change hooks are disabled.
	))))

(defun verilog-auto-output ()
  "Expand AUTOOUTPUT statements, as part of \\[verilog-auto].
Make output statements for any output signal from an /*AUTOINST*/ that
isn't an input to another AUTOINST.  This is useful for modules which
only instantiate other modules.

Limitations:
  This ONLY detects outputs of AUTOINSTants (see `verilog-read-sub-decls').

  If placed inside the parenthesis of a module declaration, it creates
  Verilog 2001 style, else uses Verilog 1995 style.

  If any concatenation, or bit-subscripts are missing in the AUTOINSTant's
  instantiation, all bets are off.  (For example due to an AUTO_TEMPLATE).

  Typedefs must match `verilog-typedef-regexp', which is disabled by default.

  Types are added to declarations if an AUTOLOGIC or
  `verilog-auto-wire-type' is set to logic.

  Signals matching `verilog-auto-output-ignore-regexp' are not included.

An example (see `verilog-auto-inst' for what else is going on here):

        module InstModule (output o);
        endmodule

        module ExampOutput
           (/*AUTOOUTPUT*/
           );
           InstModule instName
             (/*AUTOINST*/);
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampOutput
          (/*AUTOOUTPUT*/
           // Beginning of automatic outputs
           output          o    // From instName of InstModule.v
           // End of automatics
           );
          InstModule instName
            (/*AUTOINST*/
             // Outputs
             .o          (o));
        endmodule

You may also provide an optional regular expression, in which case only
signals matching the regular expression will be included.  For example the
same expansion will result from only extracting outputs starting with ov:

           /*AUTOOUTPUT(\"^ov\")*/"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (params (verilog-read-auto-params 0 1))
	   (regexp (nth 0 params))
	   (v2k  (verilog-in-paren-quick))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (modsubdecls (verilog-modi-get-sub-decls modi))
	   (sig-list (verilog-signals-not-in
		      (verilog-subdecls-get-outputs modsubdecls)
		      (append (verilog-decls-get-outputs moddecls)
			      (verilog-decls-get-inouts moddecls)
			      (verilog-decls-get-inputs moddecls)
			      (verilog-subdecls-get-inputs modsubdecls)
			      (verilog-subdecls-get-inouts modsubdecls)))))
      (when regexp
	(setq sig-list (verilog-signals-matching-regexp
			sig-list regexp)))
      (setq sig-list (verilog-signals-not-matching-regexp
		      sig-list verilog-auto-output-ignore-regexp))
      (verilog-forward-or-insert-line)
      (when v2k (verilog-repair-open-comma))
      (when sig-list
	(verilog-insert-indent "// Beginning of automatic outputs (from unused autoinst outputs)\n")
	(verilog-insert-definition modi sig-list "output" indent-pt v2k)
	(verilog-insert-indent "// End of automatics\n"))
      (when v2k (verilog-repair-close-comma)))))

(defun verilog-auto-output-every ()
  "Expand AUTOOUTPUTEVERY statements, as part of \\[verilog-auto].
Make output statements for any signals that aren't primary inputs or
outputs already.  This makes every signal in the design an output.  This is
useful to get synthesis to preserve every signal in the design, since it
won't optimize away the outputs.

An example:

        module ExampOutputEvery (o,i,tempa,tempb);
           output o;
           input i;
           /*AUTOOUTPUTEVERY*/
           wire tempa = i;
           wire tempb = tempa;
           wire o = tempb;
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampOutputEvery (
           /*AUTOOUTPUTEVERY*/
           // Beginning of automatic outputs (every signal)
           output          o,
           output          tempa,
           output          tempb,
           // End of automatics
           input i
           );
           wire tempa = i;
           wire tempb = tempa;
           wire o = tempb;
        endmodule

You may also provide an optional regular expression, in which
case only signals matching the regular expression will be
included,or excluded if the regexp begins with ?! (question-mark
exclamation-mark).  For example the same expansion will result
from only extracting outputs starting with ov:

           /*AUTOOUTPUTEVERY(\"^ov\")*/"
  (save-excursion
    ;;Point must be at insertion point
    (let* ((indent-pt (current-indentation))
	   (params (verilog-read-auto-params 0 1))
	   (regexp (nth 0 params))
	   (v2k  (verilog-in-paren-quick))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (sig-list (verilog-signals-combine-bus
		      (verilog-signals-not-in
		       (verilog-decls-get-signals moddecls)
		       (verilog-decls-get-ports moddecls)))))
      (when regexp
	(setq sig-list (verilog-signals-matching-regexp
			sig-list regexp)))
      (setq sig-list (verilog-signals-not-matching-regexp
		      sig-list verilog-auto-output-ignore-regexp))
      (verilog-forward-or-insert-line)
      (when v2k (verilog-repair-open-comma))
      (when sig-list
	(verilog-insert-indent "// Beginning of automatic outputs (every signal)\n")
	(verilog-insert-definition modi sig-list "output" indent-pt v2k)
	(verilog-insert-indent "// End of automatics\n"))
      (when v2k (verilog-repair-close-comma)))))

(defun verilog-auto-input ()
  "Expand AUTOINPUT statements, as part of \\[verilog-auto].
Make input statements for any input signal into an /*AUTOINST*/ that
isn't declared elsewhere inside the module.  This is useful for modules which
only instantiate other modules.

Limitations:
  This ONLY detects inputs of AUTOINSTants (see `verilog-read-sub-decls').

  If placed inside the parenthesis of a module declaration, it creates
  Verilog 2001 style, else uses Verilog 1995 style.

  If any concatenation, or bit-subscripts are missing in the AUTOINSTant's
  instantiation, all bets are off.  (For example due to an AUTO_TEMPLATE).

  Typedefs must match `verilog-typedef-regexp', which is disabled by default.

  Types are added to declarations if an AUTOLOGIC or
  `verilog-auto-wire-type' is set to logic.

  Signals matching `verilog-auto-input-ignore-regexp' are not included.

An example (see `verilog-auto-inst' for what else is going on here):

        module InstModule (input i);
        endmodule

        module ExampInput (
           /*AUTOINPUT*/
           );
           InstModule instName
             (/*AUTOINST*/);
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampInput (
           /*AUTOINPUT*/
           // Beginning of automatic inputs (from unused autoinst inputs)
           input           i       // To instName of InstModule.v
           // End of automatics
           );
           InstModule instName
             (/*AUTOINST*/
              // Inputs
              .i        (i));
        endmodule

You may also provide an optional regular expression, in which
case only signals matching the regular expression will be
included.  or excluded if the regexp begins with
?! (question-mark exclamation-mark).  For example the same
expansion will result from only extracting inputs starting with
i:

           /*AUTOINPUT(\"^i\")*/"
  (save-excursion
    (let* ((indent-pt (current-indentation))
	   (params (verilog-read-auto-params 0 1))
	   (regexp (nth 0 params))
	   (v2k  (verilog-in-paren-quick))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (modsubdecls (verilog-modi-get-sub-decls modi))
	   (sig-list (verilog-signals-not-in
		      (verilog-subdecls-get-inputs modsubdecls)
		      (append (verilog-decls-get-inputs moddecls)
			      (verilog-decls-get-inouts moddecls)
			      (verilog-decls-get-outputs moddecls)
			      (verilog-decls-get-vars moddecls)
			      (verilog-decls-get-consts moddecls)
			      (verilog-decls-get-gparams moddecls)
			      (verilog-subdecls-get-interfaced modsubdecls)
			      (verilog-subdecls-get-outputs modsubdecls)
			      (verilog-subdecls-get-inouts modsubdecls)))))
      (when regexp
	(setq sig-list (verilog-signals-matching-regexp
			sig-list regexp)))
      (setq sig-list (verilog-signals-not-matching-regexp
		      sig-list verilog-auto-input-ignore-regexp))
      (verilog-forward-or-insert-line)
      (when v2k (verilog-repair-open-comma))
      (when sig-list
	(verilog-insert-indent "// Beginning of automatic inputs (from unused autoinst inputs)\n")
	(verilog-insert-definition modi sig-list "input" indent-pt v2k)
	(verilog-insert-indent "// End of automatics\n"))
      (when v2k (verilog-repair-close-comma)))))

(defun verilog-auto-inout ()
  "Expand AUTOINOUT statements, as part of \\[verilog-auto].
Make inout statements for any inout signal in an /*AUTOINST*/ that
isn't declared elsewhere inside the module.

Limitations:
  This ONLY detects inouts of AUTOINSTants (see `verilog-read-sub-decls').

  If placed inside the parenthesis of a module declaration, it creates
  Verilog 2001 style, else uses Verilog 1995 style.

  If any concatenation, or bit-subscripts are missing in the AUTOINSTant's
  instantiation, all bets are off.  (For example due to an AUTO_TEMPLATE).

  Typedefs must match `verilog-typedef-regexp', which is disabled by default.

  Types are added to declarations if an AUTOLOGIC or
  `verilog-auto-wire-type' is set to logic.

  Signals matching `verilog-auto-inout-ignore-regexp' are not included.

An example (see `verilog-auto-inst' for what else is going on here):

        module InstModule (inout io);
        endmodule

        module ExampInout (
           /*AUTOINOUT*/
           );
           InstModule instName
             (/*AUTOINST*/);
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampInout (
           /*AUTOINOUT*/
           // Beginning of automatic inouts
           inout           io      // To/From instName of InstModule.v
           // End of automatics
           );
           InstModule instName
             (/*AUTOINST*/
              // Inouts
              .io       (io));
        endmodule

You may also provide an optional regular expression, in which
case only signals matching the regular expression will be
included, or excluded if the regexp begins with ?! (question-mark
exclamation-mark).  For example the same expansion will result
from only extracting inouts starting with i:

           /*AUTOINOUT(\"^i\")*/"
  (save-excursion
    ;; Point must be at insertion point.
    (let* ((indent-pt (current-indentation))
	   (params (verilog-read-auto-params 0 1))
	   (regexp (nth 0 params))
	   (v2k  (verilog-in-paren-quick))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (modsubdecls (verilog-modi-get-sub-decls modi))
	   (sig-list (verilog-signals-not-in
		      (verilog-subdecls-get-inouts modsubdecls)
		      (append (verilog-decls-get-outputs moddecls)
			      (verilog-decls-get-inouts moddecls)
			      (verilog-decls-get-inputs moddecls)
			      (verilog-subdecls-get-inputs modsubdecls)
			      (verilog-subdecls-get-outputs modsubdecls)))))
      (when regexp
	(setq sig-list (verilog-signals-matching-regexp
			sig-list regexp)))
      (setq sig-list (verilog-signals-not-matching-regexp
		      sig-list verilog-auto-inout-ignore-regexp))
      (verilog-forward-or-insert-line)
      (when v2k (verilog-repair-open-comma))
      (when sig-list
	(verilog-insert-indent "// Beginning of automatic inouts (from unused autoinst inouts)\n")
	(verilog-insert-definition modi sig-list "inout" indent-pt v2k)
	(verilog-insert-indent "// End of automatics\n"))
      (when v2k (verilog-repair-close-comma)))))

(defun verilog-auto-inout-module (&optional complement all-in)
  "Expand AUTOINOUTMODULE statements, as part of \\[verilog-auto].
Take input/output/inout statements from the specified module and insert
into the current module.  This is useful for making null templates and
shell modules which need to have identical I/O with another module.
Any I/O which are already defined in this module will not be redefined.
For the complement of this function, see `verilog-auto-inout-comp',
and to make monitors with all inputs, see `verilog-auto-inout-in'.

Limitations:
  If placed inside the parenthesis of a module declaration, it creates
  Verilog 2001 style, else uses Verilog 1995 style.

  Concatenation and outputting partial buses is not supported.

  Module names must be resolvable to filenames.  See `verilog-auto-inst'.

  Signals are not inserted in the same order as in the original module,
  though they will appear to be in the same order to an AUTOINST
  instantiating either module.

  Signals declared as \"output reg\" or \"output wire\" etc will
  lose the wire/reg declaration so that shell modules may
  generate those outputs differently.  However, \"output logic\"
  is propagated.

An example:

        module ExampMain
          (input i,
           output o,
           inout io);
        endmodule

        module ExampShell (/*AUTOARG*/);
           /*AUTOINOUTMODULE(\"ExampMain\")*/
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampShell (/*AUTOARG*/o, io, o);
           /*AUTOINOUTMODULE(\"ExampMain\")*/
           // Beginning of automatic in/out/inouts
           output o;
           inout io;
           input i;
           // End of automatics
        endmodule

You may also provide an optional regular expression, in which
case only signals matching the regular expression will be
included, or excluded if the regexp begins with ?! (question-mark
exclamation-mark).  For example the same expansion will result
from only extracting signals starting with i:

           /*AUTOINOUTMODULE(\"ExampMain\",\"^i\")*/

You may also provide an optional third argument regular
expression, in which case only signals which have that pin
direction and data type matching that regular expression will be
included.  This matches against everything before the signal name
in the declaration, for example against \"input\" (single
bit), \"output logic\" (direction and type) or
\"output [1:0]\" (direction and implicit type).  You also
probably want to skip spaces in your regexp.

For example, the below will result in matching the output \"o\"
against the previous example's module:

           /*AUTOINOUTMODULE(\"ExampMain\",\"\",\"^output.*\")*/

You may also provide an optional fourth argument regular
expression, which if not \"\" only signals which do NOT match
that expression are included."
  ;; Beware spacing of quotes in above as can mess up Emacs indenter
  (save-excursion
    (let* ((params (verilog-read-auto-params 1 4))
	   (submod (nth 0 params))
	   (regexp (nth 1 params))
	   (direction-re (nth 2 params))
	   (not-re (nth 3 params))
	   submodi)
      ;; Lookup position, etc of co-module
      ;; Note this may raise an error
      (when (setq submodi (verilog-modi-lookup submod t))
	(let* ((indent-pt (current-indentation))
	       (v2k  (verilog-in-paren-quick))
	       (modi (verilog-modi-current))
	       (moddecls (verilog-modi-get-decls modi))
	       (submoddecls (verilog-modi-get-decls submodi))
	       (sig-list-i  (verilog-signals-not-in
			     (cond (all-in
				    (append
				     (verilog-decls-get-inputs submoddecls)
				     (verilog-decls-get-inouts submoddecls)
				     (verilog-decls-get-outputs submoddecls)))
				   (complement
				    (verilog-decls-get-outputs submoddecls))
				   (t (verilog-decls-get-inputs submoddecls)))
			     (append (verilog-decls-get-inputs moddecls))))
	       (sig-list-o  (verilog-signals-not-in
			     (cond (all-in nil)
				   (complement
				    (verilog-decls-get-inputs submoddecls))
				   (t (verilog-decls-get-outputs submoddecls)))
			     (append (verilog-decls-get-outputs moddecls))))
	       (sig-list-io (verilog-signals-not-in
			     (cond (all-in nil)
				   (t (verilog-decls-get-inouts submoddecls)))
			     (append (verilog-decls-get-inouts moddecls))))
	       (sig-list-if (verilog-signals-not-in
			     (verilog-decls-get-interfaces submoddecls)
			     (append (verilog-decls-get-interfaces moddecls)))))
	  (forward-line 1)
	  (setq sig-list-i  (verilog-signals-edit-wire-reg
			     (verilog-signals-not-matching-regexp
			      (verilog-signals-matching-dir-re
			       (verilog-signals-matching-regexp sig-list-i regexp)
                              "input" direction-re)
                             not-re))
		sig-list-o  (verilog-signals-edit-wire-reg
			     (verilog-signals-not-matching-regexp
			      (verilog-signals-matching-dir-re
			       (verilog-signals-matching-regexp sig-list-o regexp)
                              "output" direction-re)
                             not-re))
		sig-list-io (verilog-signals-edit-wire-reg
			     (verilog-signals-not-matching-regexp
			      (verilog-signals-matching-dir-re
			       (verilog-signals-matching-regexp sig-list-io regexp)
                              "inout" direction-re)
                             not-re))
		sig-list-if (verilog-signals-not-matching-regexp
			     (verilog-signals-matching-dir-re
			      (verilog-signals-matching-regexp sig-list-if regexp)
                             "interface" direction-re)
                            not-re))
	  (when v2k (verilog-repair-open-comma))
	  (when (or sig-list-i sig-list-o sig-list-io sig-list-if)
	    (verilog-insert-indent "// Beginning of automatic in/out/inouts (from specific module)\n")
	    ;; Don't sort them so an upper AUTOINST will match the main module
	    (verilog-insert-definition modi sig-list-o  "output" indent-pt v2k t)
	    (verilog-insert-definition modi sig-list-io "inout" indent-pt v2k t)
	    (verilog-insert-definition modi sig-list-i  "input" indent-pt v2k t)
	    (verilog-insert-definition modi sig-list-if "interface" indent-pt v2k t)
	    (verilog-insert-indent "// End of automatics\n"))
	  (when v2k (verilog-repair-close-comma)))))))

(defun verilog-auto-inout-comp ()
  "Expand AUTOINOUTCOMP statements, as part of \\[verilog-auto].
Take input/output/inout statements from the specified module and
insert the inverse into the current module (inputs become outputs
and vice-versa.)  This is useful for making test and stimulus
modules which need to have complementing I/O with another module.
Any I/O which are already defined in this module will not be
redefined.  For the complement of this function, see
`verilog-auto-inout-module'.

Limitations:
  If placed inside the parenthesis of a module declaration, it creates
  Verilog 2001 style, else uses Verilog 1995 style.

  Concatenation and outputting partial buses is not supported.

  Module names must be resolvable to filenames.  See `verilog-auto-inst'.

  Signals are not inserted in the same order as in the original module,
  though they will appear to be in the same order to an AUTOINST
  instantiating either module.

An example:

        module ExampMain
          (input i,
           output o,
           inout io);
        endmodule

        module ExampBench (/*AUTOARG*/);
           /*AUTOINOUTCOMP(\"ExampMain\")*/
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampShell (/*AUTOARG*/i, io, o);
           /*AUTOINOUTCOMP(\"ExampMain\")*/
           // Beginning of automatic in/out/inouts
           output i;
           inout io;
           input o;
           // End of automatics
        endmodule

You may also provide an optional regular expression, in which case only
signals matching the regular expression will be included.  For example the
same expansion will result from only extracting signals starting with i:

           /*AUTOINOUTCOMP(\"ExampMain\",\"^i\")*/

You may also provide an optional third argument regular
expression, in which case only signals which have that pin
direction and data type matching that regular expression will be
included.  This matches against everything before the signal name
in the declaration, for example against \"input\" (single
bit), \"output logic\" (direction and type)
or \"output [1:0]\" (direction and implicit type).  You also
probably want to skip spaces in your regexp.

For example, the below will result in matching the output \"o\"
against the previous example's module:

           /*AUTOINOUTCOMP(\"ExampMain\",\"\",\"^output.*\")*/

You may also provide an optional fourth argument regular
expression, which if not \"\" only signals which do NOT match
that expression are included."
  ;; Beware spacing of quotes in above as can mess up Emacs indenter
  (verilog-auto-inout-module t nil))

(defun verilog-auto-inout-in ()
  "Expand AUTOINOUTIN statements, as part of \\[verilog-auto].
Take input/output/inout statements from the specified module and
insert them as all inputs into the current module.  This is
useful for making monitor modules which need to see all signals
as inputs based on another module.  Any I/O which are already
defined in this module will not be redefined.  See also
`verilog-auto-inout-module'.

Limitations:
  If placed inside the parenthesis of a module declaration, it creates
  Verilog 2001 style, else uses Verilog 1995 style.

  Concatenation and outputting partial buses is not supported.

  Module names must be resolvable to filenames.  See `verilog-auto-inst'.

  Signals are not inserted in the same order as in the original module,
  though they will appear to be in the same order to an AUTOINST
  instantiating either module.

An example:

        module ExampMain
          (input i,
           output o,
           inout io);
        endmodule

        module ExampInoutIn (/*AUTOARG*/);
           /*AUTOINOUTIN(\"ExampMain\")*/
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampInoutIn (/*AUTOARG*/i, io, o);
           /*AUTOINOUTIN(\"ExampMain\")*/
           // Beginning of automatic in/out/inouts
           input i;
           input io;
           input o;
           // End of automatics
        endmodule

You may also provide an optional regular expression, in which
case only signals matching the regular expression will be
included, or excluded if the regexp begins with ?! (question-mark
exclamation-mark).  For example the same expansion will result
from only extracting signals starting with i:

           /*AUTOINOUTIN(\"ExampMain\",\"^i\")*/"
  (verilog-auto-inout-module nil t))

(defun verilog-auto-inout-param ()
  "Expand AUTOINOUTPARAM statements, as part of \\[verilog-auto].
Take input/output/inout statements from the specified module and insert
into the current module.  This is useful for making null templates and
shell modules which need to have identical I/O with another module.
Any I/O which are already defined in this module will not be redefined.
For the complement of this function, see `verilog-auto-inout-comp',
and to make monitors with all inputs, see `verilog-auto-inout-in'.

Limitations:
  If placed inside the parenthesis of a module declaration, it creates
  Verilog 2001 style, else uses Verilog 1995 style.

  Module names must be resolvable to filenames.  See `verilog-auto-inst'.

  Parameters are inserted in the same order as in the original module.

  Parameters do not have values, which is SystemVerilog 2009 syntax.

An example:

        module ExampMain ();
          parameter PARAM = 22;
        endmodule

        module ExampInoutParam ();
           /*AUTOINOUTPARAM(\"ExampMain\")*/
        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampInoutParam ();
           /*AUTOINOUTPARAM(\"ExampMain\")*/
           // Beginning of automatic parameters (from specific module)
           parameter       PARAM;
           // End of automatics
        endmodule

You may also provide an optional regular expression, in which case only
parameters matching the regular expression will be included.  For example the
same expansion will result from only extracting parameters starting with i:

           /*AUTOINOUTPARAM(\"ExampMain\",\"^i\")*/"
  (save-excursion
    (let* ((params (verilog-read-auto-params 1 2))
	   (submod (nth 0 params))
	   (regexp (nth 1 params))
	   submodi)
      ;; Lookup position, etc of co-module
      ;; Note this may raise an error
      (when (setq submodi (verilog-modi-lookup submod t))
	(let* ((indent-pt (current-indentation))
	       (v2k  (verilog-in-paren-quick))
	       (modi (verilog-modi-current))
	       (moddecls (verilog-modi-get-decls modi))
	       (submoddecls (verilog-modi-get-decls submodi))
	       (sig-list-p  (verilog-signals-not-in
			     (verilog-decls-get-gparams submoddecls)
			     (append (verilog-decls-get-gparams moddecls)))))
	  (forward-line 1)
	  (setq sig-list-p  (verilog-signals-matching-regexp sig-list-p regexp))
	  (when v2k (verilog-repair-open-comma))
	  (when sig-list-p
	    (verilog-insert-indent "// Beginning of automatic parameters (from specific module)\n")
	    ;; Don't sort them so an upper AUTOINST will match the main module
	    (verilog-insert-definition modi sig-list-p  "parameter" indent-pt v2k t)
	    (verilog-insert-indent "// End of automatics\n"))
	  (when v2k (verilog-repair-close-comma)))))))

(defun verilog-auto-inout-modport ()
  "Expand AUTOINOUTMODPORT statements, as part of \\[verilog-auto].
Take input/output/inout statements from the specified interface
and modport and insert into the current module.  This is useful
for making verification modules that connect to UVM interfaces.

  The first parameter is the name of an interface.

  The second parameter is a regexp of modports to read from in
  that interface.

  The optional third parameter is a regular expression, and only
  signals matching the regular expression will be included.

  The optional fourth parameter is a prefix to add to the signals.

Limitations:
  If placed inside the parenthesis of a module declaration, it creates
  Verilog 2001 style, else uses Verilog 1995 style.

  Interface names must be resolvable to filenames.  See `verilog-auto-inst'.

As with other autos, any inputs/outputs declared in the module
will suppress the AUTO from redeclaring an inputs/outputs by
the same name.

An example:

        interface ExampIf
          ( input logic clk );
           logic        req_val;
           logic [7:0]  req_dat;
           clocking mon_clkblk @(posedge clk);
              input     req_val;
              input     req_dat;
           endclocking
           modport mp(clocking mon_clkblk);
        endinterface


        module ExampMain
        ( input clk,
          /*AUTOINOUTMODPORT(\"ExampIf\", \"mp\")*/
        );

        ExampleIf i;

        /*AUTOASSIGNMODPORT(\"ExampIf\", \"mp\", \"i\")*/

        endmodule

Typing \\[verilog-auto] will make this into:

        module ExampMain
        ( input clk,
          /*AUTOINOUTMODPORT(\"ExampIf\", \"mp\")*/
          // Beginning of automatic in/out/inouts (from modport)
          input        req_val,
          input [7:0]  req_dat
          // End of automatics
        );

        ExampleIf i;

        /*AUTOASSIGNMODPORT(\"ExampIf\", \"mp\", \"i\")*/
        // Beginning of automatic assignments from modport
        assign i.req_dat = req_dat;
        assign i.req_val = req_val;
        // End of automatics

        endmodule

If the modport is part of a UVM monitor/driver class, this
creates a wrapper module that may be used to instantiate the
driver/monitor using AUTOINST in the testbench."
  (save-excursion
    (let* ((params (verilog-read-auto-params 2 4))
	   (submod (nth 0 params))
	   (modport-re (nth 1 params))
	   (regexp (nth 2 params))
           (prefix (nth 3 params))
           ;; direction-re  ; direction argument not supported until requested
           submodi)
      ;; Lookup position, etc of co-module
      ;; Note this may raise an error
      (when (setq submodi (verilog-modi-lookup submod t))
	(let* ((indent-pt (current-indentation))
	       (v2k  (verilog-in-paren-quick))
	       (modi (verilog-modi-current))
	       (moddecls (verilog-modi-get-decls modi))
	       (submoddecls (verilog-modi-get-decls submodi))
	       (submodportdecls (verilog-modi-modport-lookup submodi modport-re))
               (sig-list-i (verilog-signals-in  ; Decls doesn't have data types, must resolve
			    (verilog-decls-get-vars submoddecls)
			    (verilog-signals-not-in
			     (verilog-decls-get-inputs submodportdecls)
                             (verilog-decls-get-ports submoddecls))))
               (sig-list-o (verilog-signals-in  ; Decls doesn't have data types, must resolve
			    (verilog-decls-get-vars submoddecls)
			    (verilog-signals-not-in
			     (verilog-decls-get-outputs submodportdecls)
                             (verilog-decls-get-ports submoddecls))))
               (sig-list-io (verilog-signals-in  ; Decls doesn't have data types, must resolve
			     (verilog-decls-get-vars submoddecls)
			     (verilog-signals-not-in
			      (verilog-decls-get-inouts submodportdecls)
                              (verilog-decls-get-ports submoddecls)))))
	  (forward-line 1)
	  (setq sig-list-i  (verilog-signals-edit-wire-reg
                             (verilog-signals-not-in
                              (verilog-signals-add-prefix
                               (verilog-signals-matching-dir-re
                                (verilog-signals-matching-regexp sig-list-i regexp)
                                "input" nil) ;; direction-re
                               prefix)
                              (verilog-decls-get-ports moddecls)))
		sig-list-o  (verilog-signals-edit-wire-reg
                             (verilog-signals-not-in
                              (verilog-signals-add-prefix
                               (verilog-signals-matching-dir-re
                                (verilog-signals-matching-regexp sig-list-o regexp)
                                "output" nil) ;; direction-re
                               prefix)
                              (verilog-decls-get-ports moddecls)))
		sig-list-io (verilog-signals-edit-wire-reg
                             (verilog-signals-not-in
                              (verilog-signals-add-prefix
                               (verilog-signals-matching-dir-re
                                (verilog-signals-matching-regexp sig-list-io regexp)
                                "inout" nil) ;; direction-re
                               prefix)
                              (verilog-decls-get-ports moddecls))))
	  (when v2k (verilog-repair-open-comma))
	  (when (or sig-list-i sig-list-o sig-list-io)
	    (verilog-insert-indent "// Beginning of automatic in/out/inouts (from modport)\n")
	    ;; Don't sort them so an upper AUTOINST will match the main module
	    (verilog-insert-definition modi sig-list-o  "output" indent-pt v2k t)
	    (verilog-insert-definition modi sig-list-io "inout" indent-pt v2k t)
	    (verilog-insert-definition modi sig-list-i  "input" indent-pt v2k t)
	    (verilog-insert-indent "// End of automatics\n"))
	  (when v2k (verilog-repair-close-comma)))))))

(defun verilog-auto-insert-lisp ()
  "Expand AUTOINSERTLISP statements, as part of \\[verilog-auto].
The Lisp code provided is called before other AUTOS are expanded,
and the Lisp code generally will call `insert' to insert text
into the current file beginning on the line after the
AUTOINSERTLISP.

See also AUTOINSERTLAST and `verilog-auto-insert-last' which
executes after (as opposed to before) other AUTOs.

See also AUTO_LISP, which takes a Lisp expression and evaluates
it during `verilog-auto-inst' but does not insert any text.

An example:

        module ExampInsertLisp;
           /*AUTOINSERTLISP(my-verilog-insert-hello \"world\")*/
        endmodule

        // For this example we declare the function in the
        // module's file itself.  Often you'd define it instead
        // in a site-start.el or init file.
        /*
         Local Variables:
         eval:
           (defun my-verilog-insert-hello (who)
             (insert (concat \"initial $write(\\\"hello \" who \"\\\");\\n\")))
         End:
        */

Typing \\[verilog-auto] will call my-verilog-insert-hello and
expand the above into:

           /*AUTOINSERTLISP(my-verilog-insert-hello \"world\")*/
           // Beginning of automatic insert Lisp
           initial $write(\"hello world\");
           // End of automatics

You can also call an external program and insert the returned
text:

           /*AUTOINSERTLISP(insert (shell-command-to-string \"echo //hello\"))*/
           // Beginning of automatic insert lisp
           //hello
           // End of automatics"
  (save-excursion
    ;; Point is at end of /*AUTO...*/
    (let* ((indent-pt (current-indentation))
	   (cmd-end-pt (save-excursion (search-backward ")")
				       (forward-char)
                                       (point)))  ; Closing paren
	   (cmd-beg-pt (save-excursion (goto-char cmd-end-pt)
                                       (backward-sexp 1)  ; Inside comment
                                       (point)))  ; Beginning paren
	   (cmd (buffer-substring-no-properties cmd-beg-pt cmd-end-pt)))
      (verilog-forward-or-insert-line)
      ;; Some commands don't move point (like insert-file) so we always
      ;; add the begin/end comments, then delete it if not needed
      (verilog-insert-indent "// Beginning of automatic insert lisp\n")
      (verilog-insert-indent "// End of automatics\n")
      (forward-line -1)
      (eval (read cmd))
      (forward-line -1)
      (setq verilog-scan-cache-tick nil)  ; Clear cache; inserted unknown text
      (verilog-delete-empty-auto-pair))))

(defun verilog-auto-insert-last ()
  "Expand AUTOINSERTLAST statements, as part of \\[verilog-auto].
The Lisp code provided is called after all other AUTOS have been
expanded, and the Lisp code generally will call `insert' to
insert text into the current file beginning on the line after the
AUTOINSERTLAST.

Other than when called (after AUTOs are expanded), the functionality
is otherwise identical to AUTOINSERTLISP and `verilog-auto-insert-lisp' which
executes before (as opposed to after) other AUTOs.

See `verilog-auto-insert-lisp' for examples."
  (verilog-auto-insert-lisp))

(defun verilog-auto-sense-sigs (moddecls presense-sigs)
  "Return list of signals for current AUTOSENSE block."
  (let* ((sigss (save-excursion
		  (search-forward ")")
		  (verilog-read-always-signals)))
	 (sig-list (verilog-signals-not-params
		    (verilog-signals-not-in (verilog-alw-get-inputs sigss)
					    (append (and (not verilog-auto-sense-include-inputs)
							 (verilog-alw-get-outputs-delayed sigss))
						    (and (not verilog-auto-sense-include-inputs)
							 (verilog-alw-get-outputs-immediate sigss))
						    (verilog-alw-get-temps sigss)
						    (verilog-decls-get-consts moddecls)
						    (verilog-decls-get-gparams moddecls)
						    presense-sigs)))))
    sig-list))

(defun verilog-auto-sense ()
  "Expand AUTOSENSE statements, as part of \\[verilog-auto].
Replace the always (/*AUTOSENSE*/) sensitivity list (/*AS*/ for short)
with one automatically derived from all inputs declared in the always
statement.  Signals that are generated within the same always block are NOT
placed into the sensitivity list (see `verilog-auto-sense-include-inputs').
Long lines are split based on the `fill-column', see \\[set-fill-column].

Limitations:
  Verilog does not allow memories (multidimensional arrays) in sensitivity
  lists.  AUTOSENSE will thus exclude them, and add a /*memory or*/ comment.

Constant signals:
  AUTOSENSE cannot always determine if a \\=`define is a constant or a signal
  (it could be in an include file for example).  If a \\=`define or other signal
  is put into the AUTOSENSE list and is not desired, use the AUTO_CONSTANT
  declaration anywhere in the module (parenthesis are required):

        /* AUTO_CONSTANT( \\=`this_is_really_constant_dont_autosense_it ) */

  Better yet, use a parameter, which will be understood to be constant
  automatically.

OOps!
  If AUTOSENSE makes a mistake, please report it.  (First try putting
  a begin/end after your always!) As a workaround, if a signal that
  shouldn't be in the sensitivity list was, use the AUTO_CONSTANT above.
  If a signal should be in the sensitivity list wasn't, placing it before
  the /*AUTOSENSE*/ comment will prevent it from being deleted when the
  autos are updated (or added if it occurs there already).

An example:

           always @ (/*AS*/) begin
              /*AUTO_CONSTANT(\\=`constant) */
              outin = ina | inb | \\=`constant;
              out = outin;
           end

Typing \\[verilog-auto] will make this into:

           always @ (/*AS*/ina or inb) begin
              /*AUTO_CONSTANT(\\=`constant) */
              outin = ina | inb | \\=`constant;
              out = outin;
           end

Note in Verilog 2001, you can often get the same result from the new @*
operator.  (This was added to the language in part due to AUTOSENSE!)

           always @* begin
              outin = ina | inb | \\=`constant;
              out = outin;
           end"
  (save-excursion
    ;; Find beginning
    (let* ((start-pt (save-excursion
		       (verilog-re-search-backward-quick "(" nil t)
		       (point)))
	   (indent-pt (save-excursion
			(or (and (goto-char start-pt) (1+ (current-column)))
			    (current-indentation))))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (sig-memories (verilog-signals-memory
			  (verilog-decls-get-vars moddecls)))
	   sig-list not-first presense-sigs)
      ;; Read signals in always, eliminate outputs from sense list
      (setq presense-sigs (verilog-signals-from-signame
			   (save-excursion
			     (verilog-read-signals start-pt (point)))))
      (setq sig-list (verilog-auto-sense-sigs moddecls presense-sigs))
      (when sig-memories
	(let ((tlen (length sig-list)))
	  (setq sig-list (verilog-signals-not-in sig-list sig-memories))
	  (if (not (eq tlen (length sig-list))) (verilog-insert " /*memory or*/ "))))
      (if (and presense-sigs  ; Add a "or" if not "(.... or /*AUTOSENSE*/"
	       (save-excursion (goto-char (point))
			       (verilog-re-search-backward-quick "[a-zA-Z0-9$_.%`]+" start-pt t)
			       (verilog-re-search-backward-quick "\\s-" start-pt t)
			       (while (looking-at "\\s-`endif")
				 (verilog-re-search-backward-quick "[a-zA-Z0-9$_.%`]+" start-pt t)
				 (verilog-re-search-backward-quick "\\s-" start-pt t))
			       (not (looking-at "\\s-or\\b"))))
	  (setq not-first t))
      (setq sig-list (sort sig-list #'verilog-signals-sort-compare))
      (while sig-list
	(cond ((> (+ 4 (current-column) (length (verilog-sig-name (car sig-list)))) fill-column) ;+4 for width of or
	       (insert "\n")
	       (indent-to indent-pt)
	       (if not-first (insert "or ")))
	      (not-first (insert " or ")))
	(insert (verilog-sig-name (car sig-list)))
	(setq sig-list (cdr sig-list)
	      not-first t)))))

(defun verilog-auto-reset ()
  "Expand AUTORESET statements, as part of \\[verilog-auto].
Replace the /*AUTORESET*/ comment with code to initialize all
registers set elsewhere in the always block.

Limitations:
  AUTORESET will not clear memories.

  AUTORESET uses <= if the signal has a <= assignment in the block,
  else it uses =.

  If <= is used, all = assigned variables are ignored if
  `verilog-auto-reset-blocking-in-non' is nil; they are presumed
  to be temporaries.

/*AUTORESET*/ presumes that any signals mentioned between the previous
begin/case/if statement and the AUTORESET comment are being reset manually
and should not be automatically reset.  This includes omitting any signals
used on the right hand side of assignments.

By default, AUTORESET will include the width of the signal in the
autos, SystemVerilog designs may want to change this.  To control
this behavior, see `verilog-auto-reset-widths'.  In some cases
AUTORESET must use a \\='0 assignment and it will print NOWIDTH; use
`verilog-auto-reset-widths' unbased to prevent this.

AUTORESET ties signals to deasserted, which is presumed to be zero.
Signals that match `verilog-active-low-regexp' will be deasserted by tying
them to a one.

AUTORESET may try to reset arrays or structures that cannot be
reset by a simple assignment, resulting in compile errors.  This
is a feature to be taken as a hint that you need to reset these
signals manually (or put them into a \"\\=`ifdef NEVER signal<=\\='0;
\\=`endif\" so Verilog-Mode ignores them.)

An example:

        module ExampReset ();
           always @(posedge clk or negedge reset_l) begin
              if (!reset_l) begin
                  c <= 1;
                  /*AUTORESET*/
              end
              else begin
                  a <= in_a;
                  b <= in_b;
                  c <= in_c;
              end
           end
        endmodule

Typing \\[verilog-auto] will make this into:

        ...
                  c <= 1;
                  /*AUTORESET*/
                  // Beginning of autoreset for uninitialized flops
                  a <= 1'h0;
                  b <= 1'h0;
                  // End of automatics
        ..."

  (interactive)
  (save-excursion
    ;; Find beginning
    (let* ((indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (all-list (verilog-decls-get-signals moddecls))
	   sigss sig-list dly-list prereset-sigs)
      ;; Read signals in always, eliminate outputs from reset list
      (setq prereset-sigs (verilog-signals-from-signame
			   (save-excursion
			     (verilog-read-signals
			      (save-excursion
				(verilog-re-search-backward-quick
				 "\\(@\\|\\<\\(begin\\|if\\|case[xz]?\\|always\\(_latch\\|_ff\\|_comb\\)?\\)\\>\\)" nil t)
				(point))
			      (point)))))
      (save-excursion
	(verilog-re-search-backward-quick "\\(@\\|\\<\\(always\\(_latch\\|_ff\\|_comb\\)?\\)\\>\\)" nil t)
        (setq sigss (verilog-read-always-signals)))
      (setq dly-list (verilog-alw-get-outputs-delayed sigss))
      (setq sig-list (verilog-signals-not-in-struct
		      (append
		       (verilog-alw-get-outputs-delayed sigss)
		       (when (or (not (verilog-alw-get-uses-delayed sigss))
				 verilog-auto-reset-blocking-in-non)
			 (verilog-alw-get-outputs-immediate sigss)))
		      (append
		       (verilog-alw-get-temps sigss)
		       prereset-sigs)))
      (setq sig-list (sort sig-list #'verilog-signals-sort-compare))
      (when sig-list
	(insert "\n");
	(verilog-insert-indent "// Beginning of autoreset for uninitialized flops\n");
	(while sig-list
          (let ((sig (or (assoc (verilog-sig-name (car sig-list)) all-list)  ; As sig-list has no widths
			 (car sig-list))))
	    (indent-to indent-pt)
	    (insert (verilog-sig-name sig)
		    (if (assoc (verilog-sig-name sig) dly-list)
			(concat " <= " verilog-assignment-delay)
		      " = ")
		    (verilog-sig-tieoff sig)
		    ";\n")
	    (setq sig-list (cdr sig-list))))
	(verilog-insert-indent "// End of automatics")))))

(defun verilog-auto-tieoff ()
  "Expand AUTOTIEOFF statements, as part of \\[verilog-auto].
Replace the /*AUTOTIEOFF*/ comment with code to wire-tie all unused output
signals to deasserted.

/*AUTOTIEOFF*/ is used to make stub modules; modules that have
the same input/output list as another module, but no internals.
Specifically, it finds all outputs in the module, and if that
input is not otherwise declared as a register or wire, nor comes
from a AUTOINST submodule's output, creates a tieoff.  AUTOTIEOFF
does not examine assignments to determine what is already driven.

AUTORESET ties signals to deasserted, which is presumed to be zero.
Signals that match `verilog-active-low-regexp' will be deasserted by tying
them to a one.

You can add signals you do not want included in AUTOTIEOFF with
`verilog-auto-tieoff-ignore-regexp'.

`verilog-auto-wire-type' may be used to change the datatype of
the declarations.

`verilog-auto-reset-widths' may be used to change how the tieoff
value's width is generated.

An example of making a stub for another module:

        module ExampMain
          #(parameter P)
          (input i, output o, inout io);
        endmodule

        module ExampStub (/*AUTOARG*/);
            /*AUTOINOUTPARAM(\"ExampMain\")*/
            /*AUTOINOUTMODULE(\"ExampMain\")*/

            /*AUTOTIEOFF*/

            // verilator lint_off UNUSED
            wire _unused_ok = &{1\\='b0,
                                /*AUTOUNUSED*/
                                1\\='b0};
            // verilator lint_on  UNUSED
        endmodule

Typing \\[verilog-auto] will make this into:

        ...
        /*AUTOTIEOFF*/
        // Beginning of automatic tieoffs
        wire [2:0] o = 3\\='b0;
        // End of automatics
        ..."
  (interactive)
  (save-excursion
    ;; Find beginning
    (let* ((indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (modsubdecls (verilog-modi-get-sub-decls modi))
	   (sig-list (verilog-signals-not-in
		      (verilog-decls-get-outputs moddecls)
		      (append (verilog-decls-get-vars moddecls)
			      (verilog-decls-get-assigns moddecls)
			      (verilog-decls-get-consts moddecls)
			      (verilog-decls-get-gparams moddecls)
			      (verilog-subdecls-get-interfaced modsubdecls)
			      (verilog-subdecls-get-outputs modsubdecls)
			      (verilog-subdecls-get-inouts modsubdecls)))))
      (setq sig-list (verilog-signals-not-matching-regexp
		      sig-list verilog-auto-tieoff-ignore-regexp))
      (when sig-list
	(verilog-forward-or-insert-line)
	(verilog-insert-indent "// Beginning of automatic tieoffs (for this module's unterminated outputs)\n")
	(setq sig-list (sort (copy-alist sig-list) #'verilog-signals-sort-compare))
	(verilog-modi-cache-add-vars modi sig-list)  ; Before we trash list
	(while sig-list
	  (let ((sig (car sig-list)))
	    (cond ((equal verilog-auto-tieoff-declaration "assign")
		   (indent-to indent-pt)
		   (insert "assign " (verilog-sig-name sig)))
		  (t
		   (verilog-insert-one-definition sig verilog-auto-tieoff-declaration indent-pt)))
	    (indent-to (max 48 (+ indent-pt 40)))
	    (insert "= " (verilog-sig-tieoff sig)
		    ";\n")
	    (setq sig-list (cdr sig-list))))
	(verilog-insert-indent "// End of automatics\n")))))

(defun verilog-auto-undef ()
  "Expand AUTOUNDEF statements, as part of \\[verilog-auto].
Take any \\=`defines since the last AUTOUNDEF in the current file
and create \\=`undefs for them.  This is used to insure that
file-local defines do not pollute the global \\=`define name space.

Limitations:
  AUTOUNDEF presumes any identifier following \\=`define is the
  name of a define.  Any \\=`ifdefs are ignored.

  AUTOUNDEF suppresses creating an \\=`undef for any define that was
  \\=`undefed before the AUTOUNDEF.  This may be used to work around
  the ignoring of \\=`ifdefs as shown below.

An example:

        \\=`define XX_FOO
        \\=`define M_BAR(x)
        \\=`define M_BAZ
        ...
        \\=`ifdef NEVER
          \\=`undef M_BAZ       // Emacs will see this and not \\=`undef M_BAZ
        \\=`endif
        ...
        /*AUTOUNDEF*/

Typing \\[verilog-auto] will make this into:

        ...
        /*AUTOUNDEF*/
        // Beginning of automatic undefs
        \\=`undef M_BAR
        \\=`undef XX_FOO
        // End of automatics

You may also provide an optional regular expression, in which case only
defines the regular expression will be undefed."
  (save-excursion
    (let* ((params (verilog-read-auto-params 0 1))
	   (regexp (nth 0 params))
	   (indent-pt (current-indentation))
	   (end-pt (point))
	   defs def)
      (save-excursion
	;; Scan from start of file, or last AUTOUNDEF
	(or (verilog-re-search-backward-quick "/\\*AUTOUNDEF\\>" end-pt t)
	    (goto-char (point-min)))
	(while (verilog-re-search-forward-quick
		"`\\(define\\|undef\\)\\s-*\\([a-zA-Z_][a-zA-Z_0-9]*\\)" end-pt t)
	  (cond ((equal (match-string-no-properties 1) "define")
		 (setq def (match-string-no-properties 2))
		 (when (and (or (not regexp)
				(string-match regexp def))
                            (not (member def defs)))  ; delete-dups not in 21.1
		   (setq defs (cons def defs))))
		(t
		 (setq defs (delete (match-string-no-properties 2) defs))))))
      ;; Insert
      (setq defs (sort defs #'string<))
      (when defs
	(verilog-forward-or-insert-line)
	(verilog-insert-indent "// Beginning of automatic undefs\n")
	(while defs
	  (verilog-insert-indent "`undef " (car defs) "\n")
	  (setq defs (cdr defs)))
	(verilog-insert-indent "// End of automatics\n")))))

(defun verilog-auto-unused ()
  "Expand AUTOUNUSED statements, as part of \\[verilog-auto].
Replace the /*AUTOUNUSED*/ comment with a comma separated list of all unused
input and inout signals.

/*AUTOUNUSED*/ is used to make stub modules; modules that have the same
input/output list as another module, but no internals.  Specifically, it
finds all inputs and inouts in the module, and if that input is not otherwise
used, adds it to a comma separated list.

The comma separated list is intended to be used to create a _unused_ok
signal.  Using the exact name \"_unused_ok\" for name of the temporary
signal is recommended as it will insure maximum forward compatibility, it
also makes lint warnings easy to understand; ignore any unused warnings
with \"unused\" in the signal name.

To reduce simulation time, the _unused_ok signal should be forced to a
constant to prevent wiggling.  The easiest thing to do is use a
reduction-and with 1\\='b0 as shown.

This way all unused signals are in one place, making it convenient to add
your tool's specific pragmas around the assignment to disable any unused
warnings.

You can add signals you do not want included in AUTOUNUSED with
`verilog-auto-unused-ignore-regexp'.

An example of making a stub for another module:

        module ExampMain
          (input unused_input_a, input unused_input_b);
        endmodule

        module ExampStub2 (/*AUTOARG*/);
            /*AUTOINOUTPARAM(\"ExampMain\")*/
            /*AUTOINOUTMODULE(\"ExampMain\")*/

            /*AUTOTIEOFF*/

            // verilator lint_off UNUSED
            wire _unused_ok = &{1\\='b0,
                                /*AUTOUNUSED*/
                                1\\='b0};
            // verilator lint_on  UNUSED
        endmodule

Typing \\[verilog-auto] will make this into:

            ...
            // verilator lint_off UNUSED
            wire _unused_ok = &{1\\='b0,
                                /*AUTOUNUSED*/
                                // Beginning of automatics
                                unused_input_a,
                                unused_input_b
                                // End of automatics
                                1\\='b0};
            // verilator lint_on  UNUSED
        endmodule"
  (interactive)
  (save-excursion
    ;; Find beginning
    (let* ((indent-pt (progn (search-backward "/*") (current-column)))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   (modsubdecls (verilog-modi-get-sub-decls modi))
	   (sig-list (verilog-signals-not-in
		      (append (verilog-decls-get-inputs moddecls)
			      (verilog-decls-get-inouts moddecls))
		      (append (verilog-subdecls-get-inputs modsubdecls)
			      (verilog-subdecls-get-inouts modsubdecls)))))
      (setq sig-list (verilog-signals-not-matching-regexp
		      sig-list verilog-auto-unused-ignore-regexp))
      (when sig-list
	(verilog-forward-or-insert-line)
	(verilog-insert-indent "// Beginning of automatic unused inputs\n")
	(setq sig-list (sort (copy-alist sig-list) #'verilog-signals-sort-compare))
	(while sig-list
	  (let ((sig (car sig-list)))
	    (indent-to indent-pt)
	    (insert (verilog-sig-name sig) ",\n")
	    (setq sig-list (cdr sig-list))))
	(verilog-insert-indent "// End of automatics\n")))))

(defun verilog-enum-ascii (signm elim-regexp)
  "Convert an enum name SIGNM to an ascii string for insertion.
Remove user provided prefix ELIM-REGEXP."
  (or elim-regexp (setq elim-regexp "_ DONT MATCH IT_"))
  (let ((case-fold-search t))
    ;; All upper becomes all lower for readability
    (downcase (verilog-string-replace-matches elim-regexp "" nil nil signm))))

(defun verilog-auto-ascii-enum ()
  "Expand AUTOASCIIENUM statements, as part of \\[verilog-auto].
Create a register to contain the ASCII decode of an enumerated signal type.
This will allow trace viewers to show the ASCII name of states.

First, parameters are built into an enumeration using the synopsys enum
comment.  The comment must be between the keyword and the symbol.
\(Annoying, but that's what Synopsys's dc_shell FSM reader requires.)

Next, registers which that enum applies to are also tagged with the same
enum.

Finally, an AUTOASCIIENUM command is used.

  The first parameter is the name of the signal to be decoded.

  The second parameter is the name to store the ASCII code into.  For the
  signal foo, I suggest the name _foo__ascii, where the leading _ indicates
  a signal that is just for simulation, and the magic characters _ascii
  tell viewers like Dinotrace to display in ASCII format.

  The third optional parameter is a string which will be removed
  from the state names.  It defaults to \"\" which removes nothing.

  The fourth optional parameter is \"onehot\" to force one-hot
  decoding.  If unspecified, if and only if the first parameter
  width is 2^(number of states in enum) and does NOT match the
  width of the enum, the signal is assumed to be a one-hot
  decode.  Otherwise, it's a normal encoded state vector.

  `verilog-auto-wire-type' may be used to change the datatype of
  the declarations.

  \"synopsys enum\" may be used in place of \"auto enum\".

An example:

        //== State enumeration
        parameter [2:0] // auto enum state_info
                           SM_IDLE =  3\\='b000,
                           SM_SEND =  3\\='b001,
                           SM_WAIT1 = 3\\='b010;
        //== State variables
        reg [2:0]  /* auto enum state_info */
                   state_r;  /* auto state_vector state_r */
        reg [2:0]  /* auto enum state_info */
                   state_e1;

        /*AUTOASCIIENUM(\"state_r\", \"state_ascii_r\", \"SM_\")*/

Typing \\[verilog-auto] will make this into:

        ...
        /*AUTOASCIIENUM(\"state_r\", \"state_ascii_r\", \"SM_\")*/
        // Beginning of automatic ASCII enum decoding
        reg [39:0]              state_ascii_r;          // Decode of state_r
        always @(state_r) begin
           case ({state_r})
                SM_IDLE:  state_ascii_r = \"idle \";
                SM_SEND:  state_ascii_r = \"send \";
                SM_WAIT1: state_ascii_r = \"wait1\";
                default:  state_ascii_r = \"%Erro\";
           endcase
        end
        // End of automatics"
  (save-excursion
    (let* ((params (verilog-read-auto-params 2 4))
	   (undecode-name (nth 0 params))
	   (ascii-name (nth 1 params))
	   (elim-regexp (and (nth 2 params)
			     (not (equal (nth 2 params) ""))
			     (nth 2 params)))
	   (one-hot-flag (nth 3 params))
	   ;;
	   (indent-pt (current-indentation))
	   (modi (verilog-modi-current))
	   (moddecls (verilog-modi-get-decls modi))
	   ;;
	   (sig-list-consts (append (verilog-decls-get-consts moddecls)
				    (verilog-decls-get-gparams moddecls)))
	   (sig-list-all  (verilog-decls-get-iovars moddecls))
	   ;;
	   (undecode-sig (or (assoc undecode-name sig-list-all)
			     (error "%s: Signal `%s' not found in design"
                                    (verilog-point-text) undecode-name)))
	   (undecode-enum (or (verilog-sig-enum undecode-sig)
			      (error "%s: Signal `%s' does not have an enum tag"
                                     (verilog-point-text) undecode-name)))
	   ;;
	   (enum-sigs (verilog-signals-not-in
		       (or (verilog-signals-matching-enum sig-list-consts undecode-enum)
			   (error "%s: No state definitions for `%s'"
                                  (verilog-point-text) undecode-enum))
		       nil))
	   ;;
	   (one-hot (or
		     (string-match "onehot" (or one-hot-flag ""))
                     (and  ; width(enum) != width(sig)
		      (or (not (verilog-sig-bits (car enum-sigs)))
			  (not (equal (verilog-sig-width (car enum-sigs))
				      (verilog-sig-width undecode-sig))))
		      ;; count(enums) == width(sig)
		      (equal (number-to-string (length enum-sigs))
			     (verilog-sig-width undecode-sig)))))
	   (enum-chars 0)
	   (ascii-chars 0))
      ;;
      ;; Find number of ascii chars needed
      (let ((tmp-sigs enum-sigs))
	(while tmp-sigs
	  (setq enum-chars (max enum-chars (length (verilog-sig-name (car tmp-sigs))))
		ascii-chars (max ascii-chars (length (verilog-enum-ascii
						      (verilog-sig-name (car tmp-sigs))
						      elim-regexp)))
		tmp-sigs (cdr tmp-sigs))))
      ;;
      (verilog-forward-or-insert-line)
      (verilog-insert-indent "// Beginning of automatic ASCII enum decoding\n")
      (let ((decode-sig-list (list (list ascii-name (format "[%d:0]" (- (* ascii-chars 8) 1))
					 (concat "Decode of " undecode-name) nil nil))))
	(verilog-insert-definition modi decode-sig-list "reg" indent-pt nil))
      ;;
      (verilog-insert-indent "always @(" undecode-name ") begin\n")
      (setq indent-pt (+ indent-pt verilog-indent-level))
      (verilog-insert-indent "case ({" undecode-name "})\n")
      (setq indent-pt (+ indent-pt verilog-case-indent))
      ;;
      (let ((tmp-sigs enum-sigs)
	    (chrfmt (format "%%-%ds %s = \"%%-%ds\";\n"
			    (+ (if one-hot 9 1) (max 8 enum-chars))
			    ascii-name ascii-chars))
	    (errname (substring "%Error" 0 (min 6 ascii-chars))))
	(while tmp-sigs
	  (verilog-insert-indent
	   (concat
	    (format chrfmt
		    (concat (if one-hot "(")
			    ;; Use enum-sigs length as that's numeric
			    ;; verilog-sig-width undecode-sig might not be.
			    (if one-hot (number-to-string (length enum-sigs)))
			    ;; We use a shift instead of var[index]
			    ;; so that a non-one hot value will show as error.
			    (if one-hot "'b1<<")
			    (verilog-sig-name (car tmp-sigs))
			    (if one-hot ")") ":")
		    (verilog-enum-ascii (verilog-sig-name (car tmp-sigs))
					elim-regexp))))
	  (setq tmp-sigs (cdr tmp-sigs)))
	(verilog-insert-indent (format chrfmt "default:" errname)))
      ;;
      (setq indent-pt (- indent-pt verilog-case-indent))
      (verilog-insert-indent "endcase\n")
      (setq indent-pt (- indent-pt verilog-indent-level))
      (verilog-insert-indent "end\n"
			     "// End of automatics\n"))))

(defun verilog-auto-templated-rel ()
  "Replace Templated relative line numbers with absolute line numbers.
Internal use only.  This hacks around the line numbers in AUTOINST Templates
being different from the final output's line numbering."
  (let ((templateno 0) (template-line (list 0)) (buf-line 1))
    ;; Find line number each template is on
    ;; Count lines as we go, as otherwise it's O(n^2) to use count-lines
    (goto-char (point-min))
    (while (not (eobp))
      (when (looking-at ".*AUTO_TEMPLATE")
	(setq templateno (1+ templateno))
	(setq template-line (cons buf-line template-line)))
      (setq buf-line (1+ buf-line))
      (forward-line 1))
    (setq template-line (nreverse template-line))
    ;; Replace T# L# with absolute line number
    (goto-char (point-min))
    (while (re-search-forward " Templated T\\([0-9]+\\) L\\([0-9]+\\)" nil t)
      (replace-match
       (concat " Templated "
               (int-to-string (+ (nth (string-to-number
                                       (match-string-no-properties 1))
				      template-line)
                                 (string-to-number
                                  (match-string-no-properties 2)))))
       t t))))

(defun verilog-auto-template-lint ()
  "Check AUTO_TEMPLATEs for unused lines.
Enable with `verilog-auto-template-warn-unused'."
  (let ((name1 (or (buffer-file-name) (buffer-name))))
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward
	      "^\\s-*/?\\*?\\s-*[a-zA-Z0-9`_$]+\\s-+AUTO_TEMPLATE" nil t)
	(let* ((tpl-info (verilog-read-auto-template-middle))
	       (tpl-list (aref tpl-info 1))
	       (tlines (append (nth 0 tpl-list) (nth 1 tpl-list)))
	       tpl-ass)
	  (while tlines
	    (setq tpl-ass (car tlines)
		  tlines (cdr tlines))
	    ;;
            (unless (or (not (eval-when-compile (fboundp 'make-hash-table)))  ; Not supported, no warning
			(not verilog-auto-template-hits)
			(gethash (vector (nth 2 tpl-ass) (nth 3 tpl-ass))
				 verilog-auto-template-hits))
	      (verilog-warn-error "%s:%d: AUTO_TEMPLATE line unused: \".%s (%s)\""
				  name1
                                  (+ (elt tpl-ass 3)  ; Template line number
				     (count-lines (point-min) (point)))
				  (elt tpl-ass 0) (elt tpl-ass 1))
	      )))))))


;;; Auto top level:
;;

(defun verilog-auto (&optional inject)  ; Use verilog-inject-auto instead of passing an arg
  "Expand AUTO statements.
Look for any /*AUTO...*/ commands in the code, as used in
instantiations or argument headers.  Update the list of signals
following the /*AUTO...*/ command.

Use \\[verilog-delete-auto] to remove the AUTOs.

Use \\[verilog-diff-auto] to see differences in AUTO expansion.

Use \\[verilog-inject-auto] to insert AUTOs for the first time.

Use \\[verilog-faq] for a pointer to frequently asked questions.

For new users, we recommend setting `verilog-case-fold' to nil
and `verilog-auto-arg-sort' to t.

The hooks `verilog-before-auto-hook' and `verilog-auto-hook' are
called before and after this function, respectively.

For example:
        module ExampModule (/*AUTOARG*/);
            /*AUTOINPUT*/
            /*AUTOOUTPUT*/
            /*AUTOWIRE*/
            /*AUTOREG*/
            InstMod instName #(/*AUTOINSTPARAM*/) (/*AUTOINST*/);
        endmodule

You can also update the AUTOs from the shell using:
        emacs --batch  <filenames.v>  -f verilog-batch-auto
Or fix indentation with:
        emacs --batch  <filenames.v>  -f verilog-batch-indent
Likewise, you can delete or inject AUTOs with:
        emacs --batch  <filenames.v>  -f verilog-batch-delete-auto
        emacs --batch  <filenames.v>  -f verilog-batch-inject-auto
Or check if AUTOs have the same expansion
        emacs --batch  <filenames.v>  -f verilog-batch-diff-auto

Using \\[describe-function], see also:
    `verilog-auto-arg'          for AUTOARG module instantiations
    `verilog-auto-ascii-enum'   for AUTOASCIIENUM enumeration decoding
    `verilog-auto-assign-modport' for AUTOASSIGNMODPORT assignment to/from modport
    `verilog-auto-inout'        for AUTOINOUT making hierarchy inouts
    `verilog-auto-inout-comp'   for AUTOINOUTCOMP copy complemented i/o
    `verilog-auto-inout-in'     for AUTOINOUTIN inputs for all i/o
    `verilog-auto-inout-modport'  for AUTOINOUTMODPORT i/o from an interface modport
    `verilog-auto-inout-module' for AUTOINOUTMODULE copying i/o from elsewhere
    `verilog-auto-inout-param'  for AUTOINOUTPARAM copying params from elsewhere
    `verilog-auto-input'        for AUTOINPUT making hierarchy inputs
    `verilog-auto-insert-lisp'  for AUTOINSERTLISP insert code from lisp function
    `verilog-auto-insert-last'  for AUTOINSERTLAST insert code from lisp function
    `verilog-auto-inst'         for AUTOINST instantiation pins
    `verilog-auto-star'         for AUTOINST .* SystemVerilog pins
    `verilog-auto-inst-param'   for AUTOINSTPARAM instantiation params
    `verilog-auto-logic'        for AUTOLOGIC declaring logic signals
    `verilog-auto-output'       for AUTOOUTPUT making hierarchy outputs
    `verilog-auto-output-every' for AUTOOUTPUTEVERY making all outputs
    `verilog-auto-reg'          for AUTOREG registers
    `verilog-auto-reg-input'    for AUTOREGINPUT instantiation registers
    `verilog-auto-reset'        for AUTORESET flop resets
    `verilog-auto-sense'        for AUTOSENSE or AS always sensitivity lists
    `verilog-auto-tieoff'       for AUTOTIEOFF output tieoffs
    `verilog-auto-undef'        for AUTOUNDEF \\=`undef of local \\=`defines
    `verilog-auto-unused'       for AUTOUNUSED unused inputs/inouts
    `verilog-auto-wire'         for AUTOWIRE instantiation wires

    `verilog-read-defines'      for reading \\=`define values
    `verilog-read-includes'     for reading \\=`includes

If you have bugs with these autos, please file an issue at
URL `https://www.veripool.org/verilog-mode' or contact the AUTOAUTHOR
Wilson Snyder (wsnyder@wsnyder.org)."
  (interactive)
  (unless noninteractive (message "Updating AUTOs..."))
  (if (fboundp 'dinotrace-unannotate-all)
      (dinotrace-unannotate-all))
  ;; Disable change hooks for speed
  ;; This let can't be part of above let; must restore
  ;; after-change-functions before font-lock resumes
  (verilog-save-font-no-change-functions
   (let ((oldbuf (if (not (buffer-modified-p))
                     (buffer-string)))
         (case-fold-search verilog-case-fold)
         ;; Cache directories; we don't write new files, so can't change
         (verilog-dir-cache-preserving t)
         ;; Cache current module
         (verilog-modi-cache-current-enable t)
         (verilog-modi-cache-current-max (point-min)) ; IE it's invalid
         verilog-modi-cache-current)
     (verilog-save-scan-cache
      (save-excursion
        ;; Wipe cache; otherwise if we AUTOed a block above this one,
        ;; we'll misremember we have generated IOs, confusing AUTOOUTPUT
        (setq verilog-modi-cache-list nil)
        ;; Local state
        (verilog-read-auto-template-init)
        ;; If we're not in verilog-mode, change syntax table so parsing works right
        (unless (eq major-mode 'verilog-mode) (verilog-mode))
        ;; Allow user to customize
        (verilog-run-hooks 'verilog-before-auto-hook)
        ;; Try to save the user from needing to revert-file to reread file local-variables
        (verilog-auto-reeval-locals)
        (verilog-read-auto-lisp-present)
        (verilog-read-auto-lisp (point-min) (point-max))
        (verilog-getopt-flags)
        ;; From here on out, we can cache anything we read from disk
        (verilog-preserve-dir-cache
         ;; These two may seem obvious to do always, but on large includes it can be way too slow
         (when verilog-auto-read-includes
           (verilog-read-includes)
           (verilog-read-defines nil nil t))
         ;; Setup variables due to SystemVerilog expansion
         (verilog-auto-re-search-do "/\\*AUTOLOGIC\\*/" 'verilog-auto-logic-setup)
         ;; This particular ordering is important
         ;; INST: Lower modules correct, no internal dependencies, FIRST
         (verilog-preserve-modi-cache
          ;; Clear existing autos else we'll be screwed by existing ones
          (verilog-delete-auto-buffer)
          ;; Injection if appropriate
          (when inject
            (verilog-inject-inst)
            (verilog-inject-sense)
            (verilog-inject-arg))
          ;;
          ;; Do user inserts first, so their code can insert AUTOs
          (verilog-auto-re-search-do "/\\*AUTOINSERTLISP(.*?)\\*/"
                                     'verilog-auto-insert-lisp)
          ;; Expand instances before need the signals the instances input/output
          (verilog-auto-re-search-do "/\\*AUTOINSTPARAM\\((.*?)\\)?\\*/" 'verilog-auto-inst-param)
          (verilog-auto-re-search-do "/\\*AUTOINST\\((.*?)\\)?\\*/" 'verilog-auto-inst)
          (verilog-auto-re-search-do "\\.\\*" 'verilog-auto-star)
          ;; Must be done before autoin/out as creates a reg
          (verilog-auto-re-search-do "/\\*AUTOASCIIENUM(.*?)\\*/" 'verilog-auto-ascii-enum)
          ;;
          ;; first in/outs from other files
          (verilog-auto-re-search-do "/\\*AUTOINOUTMODPORT(.*?)\\*/" 'verilog-auto-inout-modport)
          (verilog-auto-re-search-do "/\\*AUTOINOUTMODULE(.*?)\\*/" 'verilog-auto-inout-module)
          (verilog-auto-re-search-do "/\\*AUTOINOUTCOMP(.*?)\\*/" 'verilog-auto-inout-comp)
          (verilog-auto-re-search-do "/\\*AUTOINOUTIN(.*?)\\*/" 'verilog-auto-inout-in)
          (verilog-auto-re-search-do "/\\*AUTOINOUTPARAM(.*?)\\*/" 'verilog-auto-inout-param)
          ;; next in/outs which need previous sucked inputs first
          (verilog-auto-re-search-do "/\\*AUTOOUTPUT\\((.*?)\\)?\\*/" 'verilog-auto-output)
          (verilog-auto-re-search-do "/\\*AUTOINPUT\\((.*?)\\)?\\*/" 'verilog-auto-input)
          (verilog-auto-re-search-do "/\\*AUTOINOUT\\((.*?)\\)?\\*/" 'verilog-auto-inout)
          ;; Then tie off those in/outs
          (verilog-auto-re-search-do "/\\*AUTOTIEOFF\\*/" 'verilog-auto-tieoff)
          ;; These can be anywhere after AUTOINSERTLISP
          (verilog-auto-re-search-do "/\\*AUTOUNDEF\\((.*?)\\)?\\*/" 'verilog-auto-undef)
          ;; Wires/regs must be after inputs/outputs
          (verilog-auto-re-search-do "/\\*AUTOASSIGNMODPORT(.*?)\\*/" 'verilog-auto-assign-modport)
          (verilog-auto-re-search-do "/\\*AUTOLOGIC\\*/" 'verilog-auto-logic)
          (verilog-auto-re-search-do "/\\*AUTOWIRE\\*/" 'verilog-auto-wire)
          (verilog-auto-re-search-do "/\\*AUTOREG\\*/" 'verilog-auto-reg)
          (verilog-auto-re-search-do "/\\*AUTOREGINPUT\\*/" 'verilog-auto-reg-input)
          ;; outputevery needs AUTOOUTPUTs done first
          (verilog-auto-re-search-do "/\\*AUTOOUTPUTEVERY\\((.*?)\\)?\\*/" 'verilog-auto-output-every)
          ;; Doesn't matter when done, but combine it with a common changer
          (verilog-auto-re-search-do "/\\*\\(AUTOSENSE\\|AS\\)\\*/" 'verilog-auto-sense)
          ;; After AUTOREG*, as they may have set signal widths
          (verilog-auto-re-search-do "/\\*AUTORESET\\*/" 'verilog-auto-reset)
          ;; After we've created all new variables
          (verilog-auto-re-search-do "/\\*AUTOUNUSED\\*/" 'verilog-auto-unused)
          ;; Must be after all inputs outputs are generated
          (verilog-auto-re-search-do "/\\*AUTOARG\\*/" 'verilog-auto-arg)
          ;; User inserts
          (verilog-auto-re-search-do "/\\*AUTOINSERTLAST(.*?)\\*/" 'verilog-auto-insert-last)
          ;; Fix line numbers (comments only)
          (when verilog-auto-inst-template-numbers
            (verilog-auto-templated-rel))
          (when verilog-auto-template-warn-unused
            (verilog-auto-template-lint))))
        ;;
        (verilog-run-hooks 'verilog-auto-hook)
        ;;
        (when verilog-auto-delete-trailing-whitespace
          (verilog-delete-trailing-whitespace))
        ;;
        (set (make-local-variable 'verilog-auto-update-tick) (buffer-chars-modified-tick))
        ;;
        ;; If end result is same as when started, clear modified flag
        (cond ((and oldbuf (equal oldbuf (buffer-string)))
               (verilog-restore-buffer-modified-p nil)
               (unless noninteractive (message "Updating AUTOs...done (no changes)")))
              (t (unless noninteractive (message "Updating AUTOs...done"))))
        ;; End of save-cache
        )))))

;;; Skeletons:
;;

(defvar verilog-template-map
  (let ((map (make-sparse-keymap)))
    (define-key map "a" #'verilog-sk-always)
    (define-key map "b" #'verilog-sk-begin)
    (define-key map "c" #'verilog-sk-case)
    (define-key map "f" #'verilog-sk-for)
    (define-key map "g" #'verilog-sk-generate)
    (define-key map "h" #'verilog-sk-header)
    (define-key map "i" #'verilog-sk-initial)
    (define-key map "j" #'verilog-sk-fork)
    (define-key map "m" #'verilog-sk-module)
    (define-key map "o" #'verilog-sk-ovm-class)
    (define-key map "p" #'verilog-sk-primitive)
    (define-key map "r" #'verilog-sk-repeat)
    (define-key map "s" #'verilog-sk-specify)
    (define-key map "t" #'verilog-sk-task)
    (define-key map "u" #'verilog-sk-uvm-object)
    (define-key map "w" #'verilog-sk-while)
    (define-key map "x" #'verilog-sk-casex)
    (define-key map "z" #'verilog-sk-casez)
    (define-key map "?" #'verilog-sk-if)
    (define-key map ":" #'verilog-sk-else-if)
    (define-key map "/" #'verilog-sk-comment)
    (define-key map "A" #'verilog-sk-assign)
    (define-key map "F" #'verilog-sk-function)
    (define-key map "I" #'verilog-sk-input)
    (define-key map "O" #'verilog-sk-output)
    (define-key map "S" #'verilog-sk-state-machine)
    (define-key map "=" #'verilog-sk-inout)
    (define-key map "U" #'verilog-sk-uvm-component)
    (define-key map "W" #'verilog-sk-wire)
    (define-key map "R" #'verilog-sk-reg)
    (define-key map "D" #'verilog-sk-define-signal)
    map)
  "Keymap used in Verilog mode for smart template operations.")


;;
;; Place the templates into Verilog Mode.  They may be inserted under any key.
;; C-c C-t will be the default.  If you use templates a lot, you
;; may want to consider moving the binding to another key in your init
;; file.
;;
;; Note \C-c and letter are reserved for users
(define-key verilog-mode-map "\C-c\C-t" verilog-template-map)

;; ---- statement skeletons ------------------------------------------

(define-skeleton verilog-sk-prompt-condition
  "Prompt for the loop condition."
  "[condition]: " str )

(define-skeleton verilog-sk-prompt-init
  "Prompt for the loop init statement."
  "[initial statement]: " str )

(define-skeleton verilog-sk-prompt-inc
  "Prompt for the loop increment statement."
  "[increment statement]: " str )

(define-skeleton verilog-sk-prompt-name
  "Prompt for the name of something."
  "[name]: " str)

(define-skeleton verilog-sk-prompt-clock
  "Prompt for the name of something."
  "name and edge of clock(s): " str)

(defvar verilog-sk-reset nil)
(defun verilog-sk-prompt-reset ()
  "Prompt for the name of a state machine reset."
  (setq verilog-sk-reset (read-string "name of reset: " "rst")))


(define-skeleton verilog-sk-prompt-state-selector
  "Prompt for the name of a state machine selector."
  "name of selector (eg {a,b,c,d}): " str )

(define-skeleton verilog-sk-prompt-output
  "Prompt for the name of something."
  "output: " str)

(define-skeleton verilog-sk-prompt-msb
  "Prompt for most significant bit specification."
  "msb:" str & ?: & '(verilog-sk-prompt-lsb) | -1 )

(define-skeleton verilog-sk-prompt-lsb
  "Prompt for least significant bit specification."
  "lsb:" str )

(defvar verilog-sk-p nil)
(define-skeleton verilog-sk-prompt-width
  "Prompt for a width specification."
  ()
  (progn
    (setq verilog-sk-p (point))
    (verilog-sk-prompt-msb)
    (if (> (point) verilog-sk-p) "] " " ")))

(defun verilog-sk-header ()
  "Insert a descriptive header at the top of the file.
See also `verilog-header' for an alternative format."
  (interactive "*")
  (save-excursion
    (goto-char (point-min))
    (verilog-sk-header-tmpl)))

(define-skeleton verilog-sk-header-tmpl
  "Insert a comment block containing the module title, author, etc."
  "[Description]: "
  "//                              -*- Mode: Verilog -*-"
  "\n// Filename        : " (buffer-name)
  "\n// Description     : " str
  "\n// Author          : " (user-full-name)
  "\n// Created On      : " (current-time-string)
  "\n// Last Modified By: " (user-full-name)
  "\n// Last Modified On: " (current-time-string)
  "\n// Update Count    : 0"
  "\n// Status          : Unknown, Use with caution!"
  "\n")

(define-skeleton verilog-sk-module
  "Insert a module definition."
  ()
  > "module " '(verilog-sk-prompt-name) " (/*AUTOARG*/ ) ;" \n
  > _ \n
  > (- verilog-indent-level-behavioral) "endmodule" (progn (electric-verilog-terminate-line) nil))

;; ------------------------------------------------------------------------
;; Define a default OVM class, with macros and new()
;; ------------------------------------------------------------------------

(define-skeleton verilog-sk-ovm-class
  "Insert a class definition."
  ()
  > "class " (setq name (skeleton-read "Name: ")) " extends " (skeleton-read "Extends: ") ";" \n
  > _ \n
  > "`ovm_object_utils_begin(" name ")" \n
  > (- verilog-indent-level) " `ovm_object_utils_end" \n
  > _ \n
  > "function new(string name=\"" name "\");" \n
  > "super.new(name);" \n
  > (- verilog-indent-level) "endfunction" \n
  > _ \n
  > "endclass" (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-uvm-object
  "Insert a class definition."
  ()
  > "class " (setq name (skeleton-read "Name: ")) " extends " (skeleton-read "Extends: ") ";" \n
  > _ \n
  > "`uvm_object_utils_begin(" name ")" \n
  > (- verilog-indent-level) "`uvm_object_utils_end" \n
  > _ \n
  > "function new(string name=\"" name "\");" \n
  > "super.new(name);" \n
  > (- verilog-indent-level) "endfunction" \n
  > _ \n
  > "endclass" (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-uvm-component
  "Insert a class definition."
  ()
  > "class " (setq name (skeleton-read "Name: ")) " extends " (skeleton-read "Extends: ") ";" \n
  > _ \n
  > "`uvm_component_utils_begin(" name ")" \n
  > (- verilog-indent-level) "`uvm_component_utils_end" \n
  > _ \n
  > "function new(string name=\"\", uvm_component parent);" \n
  > "super.new(name, parent);" \n
  > (- verilog-indent-level) "endfunction" \n
  > _ \n
  > "endclass" (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-primitive
  "Insert a task definition."
  ()
  > "primitive " '(verilog-sk-prompt-name) " ( " '(verilog-sk-prompt-output) ("input:" ", " str ) " );"\n
  > _ \n
  > (- verilog-indent-level-behavioral) "endprimitive" (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-task
  "Insert a task definition."
  ()
  > "task " '(verilog-sk-prompt-name) & ?\; \n
  > _ \n
  > "begin" \n
  > \n
  > (- verilog-indent-level-behavioral) "end" \n
  > (- verilog-indent-level-behavioral) "endtask" (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-function
  "Insert a function definition."
  ()
  > "function [" '(verilog-sk-prompt-width) | -1 '(verilog-sk-prompt-name) ?\; \n
  > _ \n
  > "begin" \n
  > \n
  > (- verilog-indent-level-behavioral) "end" \n
  > (- verilog-indent-level-behavioral) "endfunction" (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-always
  "Insert always block.  Prompt for sensitivity list."
  ()
  > "always @ ( /*AUTOSENSE*/ ) begin\n"
  > _ \n
  > (- verilog-indent-level-behavioral) "end" \n >
  )

(define-skeleton verilog-sk-initial
  "Insert an initial block."
  ()
  > "initial begin\n"
  > _ \n
  > (- verilog-indent-level-behavioral) "end" \n > )

(define-skeleton verilog-sk-specify
  "Insert specify block."
  ()
  > "specify\n"
  > _ \n
  > (- verilog-indent-level-behavioral) "endspecify" \n > )

(define-skeleton verilog-sk-generate
  "Insert generate block."
  ()
  > "generate\n"
  > _ \n
  > (- verilog-indent-level-behavioral) "endgenerate" \n > )

(define-skeleton verilog-sk-begin
  "Insert begin end block.  Uses the minibuffer to prompt for name."
  ()
  > "begin" '(verilog-sk-prompt-name) \n
  > _ \n
  > (- verilog-indent-level-behavioral) "end" )

(define-skeleton verilog-sk-fork
  "Insert a fork join block."
  ()
  > "fork\n"
  > "begin" \n
  > _ \n
  > (- verilog-indent-level-behavioral) "end" \n
  > "begin" \n
  > \n
  > (- verilog-indent-level-behavioral) "end" \n
  > (- verilog-indent-level-behavioral) "join" \n
  > )


(define-skeleton verilog-sk-case
  "Build skeleton case statement, prompting for the selector expression,
and the case items."
  "[selector expression]: "
  > "case (" str ") " \n
  > ("case selector: " str ": begin" \n > _ \n > (- verilog-indent-level-behavioral) "end" \n > )
  resume: >  (- verilog-case-indent) "endcase" (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-casex
  "Build skeleton casex statement, prompting for the selector expression,
and the case items."
  "[selector expression]: "
  > "casex (" str ") " \n
  > ("case selector: " str ": begin" \n > _ \n > (- verilog-indent-level-behavioral) "end" \n > )
  resume: >  (- verilog-case-indent) "endcase" (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-casez
  "Build skeleton casez statement, prompting for the selector expression,
and the case items."
  "[selector expression]: "
  > "casez (" str ") " \n
  > ("case selector: " str ": begin" \n > _ \n > (- verilog-indent-level-behavioral) "end" \n > )
  resume: >  (- verilog-case-indent) "endcase" (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-if
  "Insert a skeleton if statement."
  > "if (" '(verilog-sk-prompt-condition) & ")" " begin" \n
  > _ \n
  > (- verilog-indent-level-behavioral) "end " \n )

(define-skeleton verilog-sk-else-if
  "Insert a skeleton else if statement."
  > (verilog-indent-line) "else if ("
  (progn (setq verilog-sk-p (point)) nil) '(verilog-sk-prompt-condition) (if (> (point) verilog-sk-p) ") " -1 ) & " begin" \n
  > _ \n
  > "end" (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-datadef
  "Common routine to get data definition."
  ()
  '(verilog-sk-prompt-width) | -1 ("name (RET to end):" str ", ") -2 ";" \n)

(define-skeleton verilog-sk-input
  "Insert an input definition."
  ()
  > "input  [" '(verilog-sk-datadef))

(define-skeleton verilog-sk-output
  "Insert an output definition."
  ()
  > "output [" '(verilog-sk-datadef))

(define-skeleton verilog-sk-inout
  "Insert an inout definition."
  ()
  > "inout  [" '(verilog-sk-datadef))

(defvar verilog-sk-signal nil)
(define-skeleton verilog-sk-def-reg
  "Insert a reg definition."
  ()
  > "reg    [" '(verilog-sk-prompt-width) | -1 verilog-sk-signal ";" \n (verilog-pretty-declarations-auto) )

(defun verilog-sk-define-signal ()
  "Insert a definition of signal under point at top of module."
  (interactive "*")
  (let* ((sig-chars "a-zA-Z0-9_")
	 (v1 (buffer-substring
              (save-excursion
                (skip-chars-backward sig-chars)
                (point))
              (save-excursion
                (skip-chars-forward sig-chars)
                (point)))))
    (if (not (member v1 verilog-keywords))
	(save-excursion
	  (setq verilog-sk-signal v1)
	  (verilog-re-search-backward verilog-defun-re nil 'move)
	  (verilog-end-of-statement)
	  (verilog-forward-syntactic-ws)
	  (verilog-sk-def-reg)
	  (message "signal at point is %s" v1))
      (message "object at point (%s) is a keyword" v1))))

(define-skeleton verilog-sk-wire
  "Insert a wire definition."
  ()
  > "wire   [" '(verilog-sk-datadef))

(define-skeleton verilog-sk-reg
  "Insert a reg definition."
  ()
  > "reg   [" '(verilog-sk-datadef))

(define-skeleton verilog-sk-assign
  "Insert a skeleton assign statement."
  ()
  > "assign " '(verilog-sk-prompt-name) " = " _ ";" \n)

(define-skeleton verilog-sk-while
  "Insert a skeleton while loop statement."
  ()
  > "while ("  '(verilog-sk-prompt-condition)  ") begin" \n
  > _ \n
  > (- verilog-indent-level-behavioral) "end " (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-repeat
  "Insert a skeleton repeat loop statement."
  ()
  > "repeat ("  '(verilog-sk-prompt-condition)  ") begin" \n
  > _ \n
  > (- verilog-indent-level-behavioral) "end " (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-for
  "Insert a skeleton while loop statement."
  ()
  > "for ("
  '(verilog-sk-prompt-init) "; "
  '(verilog-sk-prompt-condition) "; "
  '(verilog-sk-prompt-inc)
  ") begin" \n
  > _ \n
  > (- verilog-indent-level-behavioral) "end " (progn (electric-verilog-terminate-line) nil))

(define-skeleton verilog-sk-comment
  "Inserts three comment lines, making a display comment."
  ()
  > "/*\n"
  > "* " _ \n
  > "*/")

(define-skeleton verilog-sk-state-machine
  "Insert a state machine definition."
  "Name of state variable: "
  '(setq input "state")
  > "// State registers for " str | -23 \n
  '(setq verilog-sk-state str)
  > "reg [" '(verilog-sk-prompt-width) | -1 verilog-sk-state ", next_" verilog-sk-state ?\; \n
  '(setq input nil)
  > \n
  > "// State FF for " verilog-sk-state \n
  > "always @ ( " (read-string "clock:" "posedge clk") " or " (verilog-sk-prompt-reset) " ) begin" \n
  > "if ( " verilog-sk-reset " ) " verilog-sk-state " = 0; else" \n
  > verilog-sk-state " = next_" verilog-sk-state ?\; \n
  > (- verilog-indent-level-behavioral) "end" (progn (electric-verilog-terminate-line) nil)
  > \n
  > "// Next State Logic for " verilog-sk-state \n
  > "always @ ( /*AUTOSENSE*/ ) begin\n"
  > "case (" '(verilog-sk-prompt-state-selector) ") " \n
  > ("case selector: " str ": begin" \n > "next_" verilog-sk-state " = " _ ";" \n > (- verilog-indent-level-behavioral) "end" \n )
  resume: >  (- verilog-case-indent) "endcase" (progn (electric-verilog-terminate-line) nil)
  > (- verilog-indent-level-behavioral) "end" (progn (electric-verilog-terminate-line) nil))

;;; Mouse Events:
;;
;; Include file loading with mouse/return event
;;
;; idea & first impl.: M. Rouat (eldo-mode.el)
;; second (emacs/xemacs) impl.: G. Van der Plas (spice-mode.el)

(if (featurep 'xemacs)
    (require 'overlay))

(defconst verilog-include-file-regexp
  "^`include\\s-+\"\\([^\n\"]*\\)\""
  "Regexp that matches the include file.")

(defvar verilog-mode-mouse-map
  (let ((map (make-sparse-keymap))) ; as described in info pages, make a map
    (set-keymap-parent map verilog-mode-map)
    ;; mouse button bindings
    (define-key map "\r"            #'verilog-load-file-at-point)
    (define-key map
      (if (featurep 'xemacs) 'button2 [mouse-2])
      #'verilog-load-file-at-mouse)
    (if (featurep 'xemacs)
       (define-key map 'Sh-button2 #'mouse-yank) ; you wanna paste don't you ?
      (define-key map [S-mouse-2]   #'mouse-yank-at-click))
    map)
  "Map containing mouse bindings for `verilog-mode'.")


(defun verilog-highlight-region (beg end _old-len)
  "Colorize included files and modules in the (changed?) region.
Clicking on the middle-mouse button loads them in a buffer (as in Dired)."
  (when (or verilog-highlight-includes
	    verilog-highlight-modules)
    (save-excursion
      (save-match-data  ; A query-replace may call this function - do not disturb
	(verilog-save-buffer-state
	 (verilog-save-scan-cache
	  (let (end-point)
	    (goto-char end)
            (setq end-point (line-end-position))
	    (goto-char beg)
	    (beginning-of-line)  ; scan entire line
	    ;; delete overlays existing on this line
	    (let ((overlays (overlays-in (point) end-point)))
	      (while overlays
		(if (and
		     (overlay-get (car overlays) 'detachable)
		     (or (overlay-get (car overlays) 'verilog-include-file)
			 (overlay-get (car overlays) 'verilog-inst-module)))
		    (delete-overlay (car overlays)))
		(setq overlays (cdr overlays))))
	    ;;
	    ;; make new include overlays
	    (when verilog-highlight-includes
	      (while (search-forward-regexp verilog-include-file-regexp end-point t)
		(goto-char (match-beginning 1))
		(let ((ov (make-overlay (match-beginning 1) (match-end 1))))
		  (overlay-put ov 'start-closed 't)
		  (overlay-put ov 'end-closed 't)
		  (overlay-put ov 'evaporate 't)
		  (overlay-put ov 'verilog-include-file 't)
		  (overlay-put ov 'mouse-face 'highlight)
		  (overlay-put ov 'local-map verilog-mode-mouse-map))))
	    ;;
	    ;; make new module overlays
	    (goto-char beg)
	    ;; This scanner is syntax-fragile, so don't get bent
	    (when verilog-highlight-modules
	      (condition-case nil
		  (while (verilog-re-search-forward-quick "\\(/\\*AUTOINST\\((.*?)\\)?\\*/\\|\\.\\*\\)" end-point t)
		    (save-excursion
		      (goto-char (match-beginning 0))
		      (unless (verilog-inside-comment-or-string-p)
                        (verilog-read-inst-module-matcher)  ; sets match 0
			(let* ((ov (make-overlay (match-beginning 0) (match-end 0))))
			  (overlay-put ov 'start-closed 't)
			  (overlay-put ov 'end-closed 't)
			  (overlay-put ov 'evaporate 't)
			  (overlay-put ov 'verilog-inst-module 't)
			  (overlay-put ov 'mouse-face 'highlight)
			  (overlay-put ov 'local-map verilog-mode-mouse-map)))))
		(error nil)))
	    ;;
	    ;; Future highlights:
	    ;;  variables - make an Occur buffer of where referenced
	    ;;  pins - make an Occur buffer of the sig in the declaration module
	    )))))))

(defun verilog-highlight-buffer ()
  "Colorize included files and modules across the whole buffer."
  ;; Invoked via verilog-mode calling font-lock then `font-lock-mode-hook'
  (interactive)
  ;; delete and remake overlays
  (verilog-highlight-region (point-min) (point-max) nil))

;; Deprecated, but was interactive, so we'll keep it around
(defalias 'verilog-colorize-include-files-buffer #'verilog-highlight-buffer)

;; ffap-at-mouse isn't useful for Verilog mode. It uses library paths.
;; so define this function to do more or less the same as ffap-at-mouse
;; but first resolve filename...
(defun verilog-load-file-at-mouse (event)
  "Load file under button 2 click's EVENT.
Files are checked based on `verilog-library-flags'."
  (interactive "@e")
  (save-excursion  ; implement a Verilog specific ffap-at-mouse
    (mouse-set-point event)
    (verilog-load-file-at-point t)))

;; ffap isn't usable for Verilog mode. It uses library paths.
;; so define this function to do more or less the same as ffap
;; but first resolve filename...
(defun verilog-load-file-at-point (&optional warn)
  "Load file under point.
If WARN, throw warning if not found.
Files are checked based on `verilog-library-flags'."
  (interactive)
  (save-excursion  ; implement a Verilog specific ffap
    (let ((overlays (overlays-in (point) (point)))
	  hit)
      (while (and overlays (not hit))
	(when (overlay-get (car overlays) 'verilog-inst-module)
	  (verilog-goto-defun-file (buffer-substring
				    (overlay-start (car overlays))
				    (overlay-end (car overlays))))
	  (setq hit t))
	(setq overlays (cdr overlays)))
      ;; Include?
      (beginning-of-line)
      (when (and (not hit)
		 (looking-at verilog-include-file-regexp))
	(if (and (car (verilog-library-filenames
                       (match-string-no-properties 1)
                       (buffer-file-name)))
		 (file-readable-p (car (verilog-library-filenames
                                        (match-string-no-properties 1)
                                        (buffer-file-name)))))
	    (find-file (car (verilog-library-filenames
                             (match-string-no-properties 1)
                             (buffer-file-name))))
	  (when warn
	    (message
	     "File `%s' isn't readable, use shift-mouse2 to paste in this field"
	     (match-string 1))))))))


;;; Bug reporting:
;;

(defun verilog-faq ()
  "Tell the user their current version, and where to get the FAQ etc."
  (interactive)
  (with-output-to-temp-buffer "*verilog-mode help*"
    (princ (format "You are using verilog-mode %s\n" verilog-mode-version))
    (princ "\n")
    (princ "For new releases, see https://www.veripool.org/verilog-mode\n")
    (princ "\n")
    (princ "For frequently asked questions, see https://www.veripool.org/verilog-mode-faq.html\n")
    (princ "\n")
    (princ "To submit a bug, use M-x verilog-submit-bug-report\n")
    (princ "\n")))

(autoload 'reporter-submit-bug-report "reporter")
(defvar reporter-prompt-for-summary-p)

(defun verilog-submit-bug-report ()
  "Submit via mail a bug report on verilog-mode.el."
  (interactive)
  (let ((reporter-prompt-for-summary-p t))
    (reporter-submit-bug-report
     "wsnyder@wsnyder.org"
     (concat "verilog-mode v" verilog-mode-version)
     '(
       verilog-active-low-regexp
       verilog-after-save-font-hook
       verilog-align-assign-expr
       verilog-align-comment-distance
       verilog-align-decl-expr-comments
       verilog-align-ifelse
       verilog-align-typedef-regexp
       verilog-align-typedef-words
       verilog-assignment-delay
       verilog-auto-arg-sort
       verilog-auto-declare-nettype
       verilog-auto-delete-trailing-whitespace
       verilog-auto-endcomments
       verilog-auto-hook
       verilog-auto-ignore-concat
       verilog-auto-indent-on-newline
       verilog-auto-inout-ignore-regexp
       verilog-auto-input-ignore-regexp
       verilog-auto-inst-column
       verilog-auto-inst-dot-name
       verilog-auto-inst-interfaced-ports
       verilog-auto-inst-param-value
       verilog-auto-inst-sort
       verilog-auto-inst-template-numbers
       verilog-auto-inst-vector
       verilog-auto-lineup
       verilog-auto-newline
       verilog-auto-output-ignore-regexp
       verilog-auto-read-includes
       verilog-auto-reset-blocking-in-non
       verilog-auto-reset-widths
       verilog-auto-save-policy
       verilog-auto-sense-defines-constant
       verilog-auto-sense-include-inputs
       verilog-auto-star-expand
       verilog-auto-star-save
       verilog-auto-template-warn-unused
       verilog-auto-tieoff-declaration
       verilog-auto-tieoff-ignore-regexp
       verilog-auto-unused-ignore-regexp
       verilog-auto-wire-type
       verilog-before-auto-hook
       verilog-before-delete-auto-hook
       verilog-before-getopt-flags-hook
       verilog-before-save-font-hook
       verilog-cache-enabled
       verilog-case-fold
       verilog-case-indent
       verilog-cexp-indent
       verilog-compiler
       verilog-coverage
       verilog-delete-auto-hook
       verilog-fontify-variables
       verilog-getopt-flags-hook
       verilog-highlight-grouping-keywords
       verilog-highlight-includes
       verilog-highlight-modules
       verilog-highlight-translate-off
       verilog-indent-begin-after-if
       verilog-indent-class-inside-pkg
       verilog-indent-declaration-macros
       verilog-indent-ignore-multiline-defines
       verilog-indent-ignore-regexp
       verilog-indent-level
       verilog-indent-level-behavioral
       verilog-indent-level-declaration
       verilog-indent-level-directive
       verilog-indent-level-module
       verilog-indent-lists
       verilog-library-directories
       verilog-library-extensions
       verilog-library-files
       verilog-library-flags
       verilog-linter
       verilog-minimum-comment-distance
       verilog-mode-hook
       verilog-mode-release-emacs
       verilog-mode-version
       verilog-preprocessor
       verilog-simulator
       verilog-tab-always-indent
       verilog-tab-to-comment
       verilog-typedef-regexp
       verilog-warn-fatal
       )
     nil nil
     (concat "Hi,

I want to report a bug.

Before I go further, I want to say that Verilog mode has changed my life.
I save so much time, my files are colored nicely, my co workers respect
my coding ability... until now.  I'd really appreciate anything you
could do to help me out with this minor deficiency in the product.

I've taken a look at the Verilog-Mode FAQ at
https://www.veripool.org/verilog-mode-faq.html.

And, I've considered filing the bug on the issue tracker at
https://www.veripool.org/verilog-mode-bugs
since I realize that public bugs are easier for you to track,
and for others to search, but would prefer to email.

So, to reproduce the bug, start a fresh Emacs via " invocation-name "
-no-init-file -no-site-file'.  In a new buffer, in Verilog mode, type
the code included below.

Given those lines, I expected [[Fill in here]] to happen;
but instead, [[Fill in here]] happens!.

== The code: =="))))

(provide 'verilog-mode)

;;TODO: Could `byte-compile-docstring-max-column' be decreased?
;; Local Variables:
;; byte-compile-docstring-max-column: 90
;; checkdoc-permit-comma-termination-flag:t
;; checkdoc-force-docstrings-flag:nil
;; indent-tabs-mode:nil
;; End:

;;; verilog-mode.el ends here
