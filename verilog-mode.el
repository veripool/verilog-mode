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

;;; This mode borrows heavily from the pascal-mode and the cc-mode of emacs

;;; USAGE
;;; =====

;;; A major mode for editing Verilog HDL source code. When you have
;;; entered Verilog mode, you may get more info by pressing C-h m. You
;;; may also get online help describing various functions by: C-h f
;;; <Name of function you want described>

;;; To set up automatic verilog mode, put this file in your load path,
;;; and include stuff like this in your .emacs:

; (autoload 'verilog-mode "verilog-mode" "Verilog mode" t )
; (setq auto-mode-alist (cons  '("\\.v\\'" . verilog-mode) auto-mode-alist))
; (setq auto-mode-alist (cons  '("\\.dv\\'" . verilog-mode) auto-mode-alist))

;;; If you want to customize Verilog mode to fit your needs better,
;;; you may add these lines (the values of the variables presented
;;; here are the defaults):
;;;
;;; ;; User customization for Verilog mode
;;; (setq verilog-indent-level           3
;;;       verilog-case-indent            2
;;;       verilog-auto-newline           t
;;;       verilog-auto-indent-on-newline t
;;;       verilog-tab-always-indent      t
;;;       verilog-auto-endcomments       t
;;;       verilog-indent-begin-after-if  t
;;;       verilog-auto-lineup            '(all))

;;; I've put in the common support for colored displays for older
;;; emacs-19 behaviour, and newer emacs-19 behaviour, as well as
;;; support for xemacs.  After that, customizing according to your
;;; particular emacs version is up to you.  I've used the following
;;; for emacs 19.27 and emacs 19.30; also xemacs seems to work for me
;;; as well.  I must caution that A) I always use dark background, so
;;; you may have to hack a bit to get the light version working with
;;; decent colors; and B) I've edited the code below from what I use,
;;; and haven't tested it. (much).  Also since the font-lock package
;;; doesn't have a version number, I've had to key off the emacs
;;; version number, which might not corrolate with the font-lock
;;; package you happen to be using.

;;(defvar background-mode 'dark)
;;(defvar display-type 'color)

;;(cond 
;; (window-system
;;  (if (string-match "XEmacs\\|Lucid" emacs-version)
;;      ()
;;    (progn
;;      (setq display-type 
;;	    (condition-case nil
;;		(let ((display-resource (x-get-resource ".displayType" "DisplayType")))
;;		  (cond (display-resource (intern (downcase display-resource)))
;;			((x-display-color-p) 'color)
;;			((x-display-grayscale-p) 'grayscale)
;;			(t 'mono)))
;;	      (error 'mono))
;;	    background-mode 
;;	    (condition-case nil
;;		(let ((bg-resource (x-get-resource ".backgroundMode"
;;						   "BackgroundMode"))
;;		      (params (frame-parameters)))
;;		  (cond (bg-resource (intern (downcase bg-resource)))
;;			((and (cdr (assq 'background-color params))
;;			      (< (apply '+ (x-color-values
;;					    (cdr (assq 'background-color params))))
;;				 (/ (apply '+ (x-color-values "white")) 3)))
;;			 'dark)
;;			(t 'light)))
;;	      (error 'light)))
;;      (message "It appears you have a %s background" background-mode)))
;;  (cond
;;   ((eq display-type 'color)
    
;;    ;; Pretty Colors in source windows.
;;    (require 'font-lock)
;;    (autoload 'turn-on-fast-lock "fast-lock"
;;      "Unconditionally turn on Fast Lock mode.")
;;    (add-hook 'c-mode-hook 'font-lock-mode)
;;    (add-hook 'perl-mode-hook 'font-lock-mode)
;;    (add-hook 'elisp-mode-hook 'font-lock-mode)
;;    (add-hook 'asm-mode-hook 'font-lock-mode)
;;    (setq fast-lock-cache-directories '("~/.backups" "."))
;;    (setq c-font-lock-keywords c-font-lock-keywords-2)
;;    (setq c++-font-lock-keywords c++-font-lock-keywords-2)
;;    (add-hook 'font-lock-mode-hook 'make-faces)
;;    (if (eq background-mode 'dark)
;;	;; Make background a light gray
;;	(set-face-background (quote region) "gray30")
;;      ;; Make background a dark gray
;;      (set-face-background (quote region) "gray70"))
;;    )
;;   ((eq display-type 'mono)
;;    (progn
;;      ;; Frames are too expensive to create
;;      ;; on my NCD running x-remote, which happens
;;      ;; to be the only place I run X mono color
;;      (setq vm-frame-per-composition nil
;;	    vm-frame-per-folder nil)
;;      )
;;    )
;;   )
;;  )
;; )

;;(defun make-my-faces ()
;;  "Customize faces the way I like to see them"
;;  (interactive)
;;  (cond ((> emacs-minor-version 29)
;;	 ;; Make background a light gray
;;	 (setq font-lock-face-attributes
;;	       '(
;;		 (font-lock-comment-face "#efc80c"		nil nil t   nil) 
;;		 (font-lock-function-name-face "red"		nil t   nil nil) 
;;		 (font-lock-keyword-face "tan" 		nil nil nil nil) 
;;		 (font-lock-reference-face "indianred"         nil t nil nil  )
;;		 (font-lock-string-face  "lightskyblue1"	nil nil nil nil) 
;;		 (font-lock-type-face 	  "Aquamarine"          nil nil nil nil) 
;;		 (font-lock-variable-name-face "LightGoldenrod") 
;;		 )))
;;	(t
;;	 (if (eq background-mode 'dark)
;;	     (progn
;;	       (make-face 'my-font-lock-function-name-face)
;;	       (set-face-foreground 'my-font-lock-function-name-face "red") 
;;	       (setq  font-lock-function-name-face  'my-font-lock-function-name-face)
	       
;;	       (make-face 'my-font-lock-keyword-face)
;;	       (set-face-foreground 'my-font-lock-keyword-face "tan")
;;	       (setq  font-lock-keyword-face  'my-font-lock-keyword-face)
	       
;;	       (make-face 'my-font-lock-string-face)
;;	       (set-face-foreground 'my-font-lock-string-face      "lightskyblue1")
;;	       (setq  font-lock-string-face  'my-font-lock-string-face)
	       
;;	       (make-face 'my-font-lock-type-face)
;;	       (set-face-foreground 'my-font-lock-type-face        "#efc80c") ; yellow
;;	       (setq  font-lock-type-face  'my-font-lock-type-face)
	       
;;	       (make-face 'my-font-lock-variable-name-face)
;;	       (set-face-foreground 'my-font-lock-variable-name-face "LightGoldenrod") 
;;	       (setq  font-lock-variable-name-face  'my-font-lock-variable-name-face)
;;	       )
;;	   (progn
;;	     (make-face 'my-font-lock-function-name-face)
;;	     (set-face-foreground 'my-font-lock-function-name-face "DarkGreen") 
;;	     (setq  font-lock-function-name-face  'my-font-lock-function-name-face)
	     
;;	     (make-face 'my-font-lock-keyword-face)
;;	     (set-face-foreground 'my-font-lock-keyword-face "indianred")
;;	     (setq  font-lock-keyword-face  'my-font-lock-keyword-face)
	     
;;	     (make-face 'my-font-lock-string-face)
;;	     (set-face-foreground 'my-font-lock-string-face      "RoyalBlue4")
;;	     (setq  font-lock-string-face  'my-font-lock-string-face)
	     
;;	     (make-face 'my-font-lock-type-face)
;;	     (set-face-foreground 'my-font-lock-type-face        "#003800") ; yellow
;;	     (setq  font-lock-type-face  'my-font-lock-type-face)
	     
;;	     (make-face 'my-font-lock-variable-name-face)
;;	     (set-face-foreground 'my-font-lock-variable-name-face "LightGoldenrod") 
;;	     (setq  font-lock-variable-name-face  'my-font-lock-variable-name-face)
;;	     )
;;	   )
;;	 )
;;	)
;;  (turn-on-fast-lock)
;;  )


;;; KNOWN BUGS / BUGREPORTS
;;; ======================= This is beta code, and likely has
;;; bugs. Please report any and all bugs to me at mac@verilog.com.
;; 
;;; Code:

(provide 'verilog-mode)

;; This variable will always hold the version number of the mode
(defconst verilog-mode-version "$$Revision$$"
  "Version of this verilog mode.")

(defvar verilog-indent-level 3
  "*Indentation of Verilog statements with respect to containing block.")

(defvar verilog-cexp-indent 1
  "*Indentation of Verilog statements split across lines.")

(defvar verilog-case-indent 2
  "*Indentation for case statements.")

(defvar verilog-auto-newline t
  "*Non-nil means automatically newline after semicolons")

(defvar verilog-auto-indent-on-newline t
  "*Non-nil means automatically indent line after newline")

(defvar verilog-tab-always-indent t
  "*Non-nil means TAB in Verilog mode should always reindent the current line,
regardless of where in the line point is when the TAB command is used.")

(defvar verilog-indent-begin-after-if t
  "*If true, indent begin statements following if, else, while, for and repeat.
otherwise, line them up.")

(defvar verilog-auto-endcomments t
  "*Non-nil means a comment /* ... */ is set after the ends which ends cases and
functions. The name of the function or case will be set between the braces.")

(defvar verilog-auto-lineup '(all) "*List of contexts where auto
  lineup of :'s or ='s should be done.  Elements can be of type:
  'declaration' or 'case', which will do auto lineup in declarations
  or case-statements respectively. The word 'all' will do all
  lineups. '(case declaration) for instance will do lineup in
  case-statements and parameterlist, while '(all) will do all
  lineups." )

(defvar verilog-mode-abbrev-table nil
  "Abbrev table in use in Verilog-mode buffers.")

(defvar verilog-font-lock-keywords-after-1930
  '(
   ("^[ \t]*\\(function\\|task\\|module\\|macromodule\\|primitive\\)\\>[ \t]*"  1 font-lock-keyword-face) 
   ("^[ \t]*\\(function\\|task\\|module\\|macromodule\\|primitive\\)\\>[ \t]*\\(\\sw+\\)"  2 font-lock-function-name-face nil t)
   ("\\\\[^ \t]*" 0 'font-lock-function-name-face)  (
    "\\(@\\)\\|\\(#\[ \t\]*\\(\\(\[0-9\]+\\('[hdxbo][0-9_xz]*\\)?\\)\\|\\((\[^)\]*)\\)\\)\\)"

    0 font-lock-type-face)  ("\\(`[ \t]*[A-Za-z][A-Za-z0-9_]*\\)" 
    0 font-lock-type-face)  
    ("\\<\\(in\\(teger\\|put\\|out\\)\\|parameter\\|output\\|event\\|tri[01]?\\|w\\(ire\\|or\\|and\\)\\|time\\|re\\(al\\(time\\)?\\|g\\)\\)\\>" 
     0 font-lock-type-face)  
    ("\\(\\$[a-zA-Z][a-zA-Z0-9_\\$]*\\)\\|\\(\\<\\(begin\\|case[xz]?\\|end\\(case\\|function\\|task\\|module\\|table\\|primitive\\|specify\\)?\\|a\\(ssign\\|lways\\)\\|initial\\|table\\|\\(pos\\|neg\\)edge\\|else\\|for\\(ever\\|k\\)?\\|join\\|if\\|repeat\\|then\\|while\\|specify\\)\\>\\)" 
     0 font-lock-keyword-face)
   )
)
(defvar verilog-font-lock-keywords nil)
(defvar verilog-font-lock-keywords-before-1930
  '(
    ("^[ \t]*\\(function\\|task\\|module\\|macromodule\\|primitive\\)\\>[ \t]*"  . 1)
    ("^[ \t]*\\(function\\|task\\|module\\|macromodule\\|primitive\\)\\>[ \t]*\\(\\sw+\\)"  2 font-lock-function-name-face nil t)
    ("\\(\\\\[^ \t]*\\)\\|\\(`[ \t]*[A-Za-z][A-Za-z0-9_]*\\)" 0 font-lock-function-name-face)
    ("[@#]" . font-lock-type-face)
    ("\\<\\(in\\(teger\\|put\\|out\\)\\|parameter\\|output\\|event\\|tri[01]?\\|w\\(ire\\|or\\|and\\)\\|time\\|re\\(al\\(time\\)?\\|g\\)\\)\\>" 
     0 font-lock-type-face)
    ("\\(\\$[a-zA-Z][a-zA-Z0-9_\\$]*\\)\\|\\(\\<\\(begin\\|case[xz]?\\|end\\(case\\|function\\|task\\|module\\|table\\|primitive\\|specify\\)?\\|a\\(ssign\\|lways\\)\\|initial\\|table\\|\\(pos\\|neg\\)edge\\|else\\|for\\(ever\\|k\\)?\\|join\\|if\\|repeat\\|then\\|while\\|specify\\)\\>\\)" . font-lock-keyword-face)
    )
)

(defvar verilog-imenu-generic-expression
  '("^[ \t]*\\(module\\|macromodule\\|primitive\\)[ \t\n]+\\([a-zA-Z0-9_.:]+\\)" . (2))
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
  (define-key verilog-mode-map ":"        'electric-verilog-colon)
  (define-key verilog-mode-map "="        'electric-verilog-equal)
  (define-key verilog-mode-map "\`"       'electric-verilog-tick)
  (define-key verilog-mode-map "\t"       'electric-verilog-tab)
  (define-key verilog-mode-map "\r"       'electric-verilog-terminate-line)
  (define-key verilog-mode-map "\M-\r"    (function (lambda ()
						      (interactive) (electric-verilog-terminate-line 1))))
  (define-key verilog-mode-map "\177"     'backward-delete-char-untabify)
  (define-key verilog-mode-map "\M-\t"    'verilog-complete-word)
  (define-key verilog-mode-map "\M-?"     'verilog-show-completions)
  (define-key verilog-mode-map "\M-\C-h"  'verilog-mark-defun)
  (define-key verilog-mode-map "\C-c\C-b" 'verilog-insert-block)
  (define-key verilog-mode-map "\C-cb"    'verilog-label-be)
  (define-key verilog-mode-map "\M-*"     'verilog-star-comment)
  (define-key verilog-mode-map "\C-c\C-c" 'verilog-comment-area)
  (define-key verilog-mode-map "\C-c\C-u" 'verilog-uncomment-area)
  (define-key verilog-mode-map "\M-\C-a"  'verilog-beg-of-defun)
  (define-key verilog-mode-map "\M-\C-e"  'verilog-end-of-defun)
  (define-key verilog-mode-map "\C-c\C-d" 'verilog-goto-defun)
  )


  
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
(defconst verilog-no-indent-begin-re "\\<\\(if\\|else\\|while\\|for\\|repeat\\)\\>")
(defconst verilog-endcomment-reason-re 
  (concat 
   "\\(\\<fork\\>\\)\\|\\(\\<begin\\>\\)\\|\\(\\<if\\>\\)\\|\\(\\<else\\>\\)\\|"
   "\\(\\<task\\>\\)\\|\\(\\<function\\>\\)\\|\\(\\<initial\\>\\)\\|\\(\\<always\\>\\(\[ \t\]*@\\)?\\)\\|\\(\\<while\\>\\)\\|\\(\\<for\\(each\\)?\\>\\)")) ;; \\|\\(\\<repeat\\>\\)\\|\\(\\<wait\\>\\)"))

(defconst verilog-named-block-re  "begin[ \t]*:")
(defconst verilog-beg-block-re   "\\<\\(begin\\|case\\|casex\\|casez\\|fork\\|table\\|specify\\)\\>")
(defconst verilog-beg-block-re-1 "\\<\\(begin\\)\\|\\(case[xz]?\\)\\|\\(fork\\)\\|\\(table\\)\\|\\(specify\\)\\>")
(defconst verilog-end-block-re   "\\<\\(end\\|join\\|endcase\\|endtable\\|endspecify\\)\\>")
(defconst verilog-end-block-re-1 "\\(\\<end\\>\\)\\|\\(\\<endcase\\>\\)\\|\\(\\<join\\>\\)\\|\\(\\<endtable\\>\\)\\|\\(\\<endspecify\\>\\)\\|\\(\\<endfunction\\>\\)\\|\\(\\<endtask\\>\\)")
(defconst verilog-beg-tf-re      "\\<\\(task\\|function\\)\\>")
(defconst verilog-end-tf-re      "\\<\\(endtask\\|endfunction\\)\\>")
(defconst verilog-declaration-re     "\\(\\<in\\(put\\|out\\|teger\\)\\>\\|\\<parameter\\>\\|\\<output\\>\\|\\<event\\>\\|re\\(al\\|g\\|altime\\)\\|time\\|tri\\(0\\|1\\|and\\|or\\|reg\\)\\|w\\(and\\|or\\|ire\\)\\)\\>")
(defconst verilog-declaration-re-1 (concat verilog-declaration-re "[ \t]*\\(\\[[^]]*\\][ \t]*\\)?"))
(defconst verilog-defun-re       "\\<\\(module\\|macromodule\\|primitive\\)\\>")
(defconst verilog-end-defun-re   "\\<\\(endmodule\\|endprimitive\\)\\>")
(defconst verilog-zero-indent-re 
  (concat verilog-defun-re "\\|" verilog-end-defun-re))
(defconst verilog-directive-re
  "\\(`else\\)\\|\\(`ifdef\\)\\|\\(`endif\\)\\|\\(`define\\)\\|\\(`undef\\)\\|\\(`include\\)")
(defconst verilog-autoindent-lines-re
  (concat
   "\\<\\(\\(macro\\)?module\\|primitive\\|end\\(case\\|function\\|task\\|module\\|primitive\\|specify\\|table\\)?\\|join\\|begin\\|else\\)\\>\\|`\\(else\\|ifdef\\|endif\\)\\|"
   verilog-directive-re
   "\\>"))
(defconst verilog-behavorial-block-beg-re
  "\\(\\<initial\\>\\|\\<always\\>\\|\\<function\\>\\|\\<task\\>\\)")
(defconst verilog-indent-reg 
  (concat "\\(\\<begin\\>\\|\\<case[xz]?\\>\\|\\<specify\\>\\|\\<fork\\>\\|\\<table\\>\\)\\|"
	  "\\(\\<end\\>\\|\\<join\\>\\|\\<endcase\\>\\|\\<endtable\\>\\|\\<endspecify\\>\\)\\|" 
	  "\\(\\<module\\>\\|\\<macromodule\\>\\|\\<primitive\\>\\)\\|"
	  "\\(\\<endmodule\\>\\|\\<endprimitive\\>\\)\\|"
	  "\\(\\<endtask\\>\\|\\<endfunction\\>\\)\\|"
	  verilog-behavorial-block-beg-re
;;	  "\\|\\(\\<if\\>\\|\\<else\\>\\)"
	  ))
(defconst verilog-complete-reg
  "\\(\\<always\\>\\)\\|\\(\\<case[xz]?\\>\\)\\|\\(\\<while\\>\\)\\|\\(\\<if\\>\\)\\|\\(\\<for\\>\\)")
(defconst verilog-label-re 
  (concat verilog-beg-block-re "\\|" 
	  verilog-end-block-re "\\|"
	  verilog-beg-tf-re "\\|"
	  verilog-end-tf-re ))
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
;;;
;;;  Macros
;;;

(defsubst verilog-re-search-forward (REGEXP BOUND NOERROR)
  "Like re-search-forward, but skips over matches in comments or strings"
  (set-match-data '(nil nil))    
  (while (and
	  (re-search-forward REGEXP BOUND NOERROR)
	  (and (verilog-skip-forward-comment-or-string)
	       (progn (store-match-data '(nil nil))
		      t)))
    ())
  (match-end 0))

(defsubst verilog-re-search-backward (REGEXP BOUND NOERROR)
  "Like re-search-backward, but skips over matches in comments or strings"
  (set-match-data '(nil nil))
  (while (and
	  (re-search-backward REGEXP BOUND NOERROR)
	  (verilog-skip-backward-comment-or-string)
	  (not (set-match-data '(nil nil))))
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


(defun verilog-declaration-beg ()
  (verilog-re-search-backward verilog-declaration-re (bobp) t))
  
(defsubst verilog-within-string ()
  (save-excursion
    (nth 3 (parse-partial-sexp (verilog-get-beg-of-line) (point)))))


;;;###autoload
(defun verilog-mode ()
"Major mode for editing Verilog code. \\<verilog-mode-map>
NEWLINE, TAB indents for Verilog code.  
Delete converts tabs to spaces as it moves back.
Supports highlighting.

Variables controlling indentation/edit style:

 verilog-indent-level           (default 3)
    Indentation of Verilog statements with respect to containing block.
 verilog-cexp-indent            (default 1)
    Indentation of Verilog statements broken across lines.
 verilog-case-indent            (default 2)
    Indentation for case statements.
 verilog-auto-newline           (default nil)
    Non-nil means automatically newline after simcolons and the punctation mark
    after an end.
 verilog-auto-indent-on-newline (default t)
    Non-nil means automatically indent line after newline
 verilog-tab-always-indent      (default t)
    Non-nil means TAB in Verilog mode should always reindent the current line,
    regardless of where in the line point is when the TAB command is used.
 verilog-indent-begin-after-if  (default t)
    Non-nil means to indent begin statements following a preceeding
    if, else, while, for and repeat statements, if any. otherwise,
    the begin is lined up with the preceeding token. If t, you get:
      if (a)
         begin
    otherwise you get:
      if (a)
      begin
 verilog-auto-endcomments       (default t)
    Non-nil means a comment /* ... */ is set after the ends which ends cases, tasks, functions and modules.
    The type and name of the object will be set between the braces.
 verilog-auto-lineup            (default `(all))
    List of contexts where auto lineup of :'s or ='s should be done.

Turning on Verilog mode calls the value of the variable verilog-mode-hook with
no args, if that value is non-nil.
Other useful functions are:
\\[verilog-complete-word]\t-complete word with appropriate possibilities (functions, verilog keywords...)
\\[verilog-comment-area]\t- Put marked area in a comment, fixing nested comments.
\\[verilog-uncomment-area]\t- Uncomment an area commented with \
\\[verilog-comment-area].
\\[verilog-insert-block]\t- insert begin ... end;
\\[verilog-star-comment]\t- insert /* ... */
\\[verilog-mark-defun]\t- Mark function.
\\[verilog-beg-of-defun]\t- Move to beginning of current function.
\\[verilog-end-of-defun]\t- Move to end of current function.
\\[verilog-label-be]\t- Label matching begin ... end, fork ... join and case ... endcase statements;
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
  (setq comment-indent-function 'verilog-indent-comment)
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
  ;; Imenu support
  (make-local-variable 'imenu-generic-expression)
  (setq imenu-generic-expression verilog-imenu-generic-expression)
  ;; Font lock support
  (make-local-variable 'font-lock-keywords)
  (if (string-match "XEmacs\\|Lucid" emacs-version)
      (setq verilog-font-lock-keywords verilog-font-lock-keywords-before-1930 )
    (cond ((> emacs-minor-version 29)
	   (setq verilog-font-lock-keywords verilog-font-lock-keywords-after-1930 ))
	  ('t 	 
	   (setq verilog-font-lock-keywords verilog-font-lock-keywords-before-1930 ))
	  ))
  (setq font-lock-keywords verilog-font-lock-keywords)
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
      (beginning-of-line)
      (verilog-indent-comment)
      (insert-string "* ")
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
	       t))
	   (newline)
	 (forward-line 1))
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
  (save-excursion
    (beginning-of-line)
    (verilog-indent-line))
  (if (and verilog-auto-newline
	   (not (verilog-parenthesis-depth)))
      (electric-verilog-terminate-line)))

(defun electric-verilog-colon ()
  "Insert `:' and do all indentions except line indent on this line."
  (interactive)
  (insert last-command-char)
  ;; Do nothing if within string.
  (if (verilog-within-string)
      ()
    (save-excursion
      (verilog-beg-of-statement)
      (verilog-indent-line))
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
  (if (save-excursion (beginning-of-line) (looking-at "^[ \t]*\`\\(\\<ifdef\\>\\|\\\<else\\>\\|\\<endif\\>\\|\\<define\\>\\)"))
      (save-excursion (beginning-of-line)
		      (delete-horizontal-space))))

(defun electric-verilog-tab ()
  "Function called when TAB is pressed in Verilog mode."
  (interactive)
  ;; If verilog-tab-always-indent, indent the beginning of the line.
  (if verilog-tab-always-indent
      (let* ((boi-point (save-excursion
			  (beginning-of-line)
			  (skip-chars-forward " \t")
			  (let (type state )
			    (setq type (verilog-indent-line))
			    (setq state (car type))
			    (cond
			     ((eq state 'block)
			      (if (looking-at verilog-behavorial-block-beg-re )
				  (error (concat "The reserved word \""
					 (buffer-substring (match-beginning 0) (match-end 0))
					 "\" must be at the behavorial level!"))))
			     ))
			  (back-to-indentation)
			  (point))))
        (if (< (point) boi-point)
            (back-to-indentation)))
    (progn (insert "\t")
	   (save-excursion
	     (beginning-of-line)
	     (verilog-indent-line)))
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
  (verilog-re-search-backward verilog-defun-re (bobp) 'move)
  )
(defun verilog-end-of-defun ()
  (interactive)
  (verilog-re-search-forward verilog-end-defun-re (bobp) 'move)
  )

(defun verilog-label-be (&optional arg)
  "Label matching begin ... end, fork ... join and case ... endcase statements in this module;
With argument, first kill any existing labels."
  (interactive)
  (let ((mod-name "Unknown")
	(fmt " /* [#%s:%s] */")
	(oldpos (point))
	(b (progn 
	     (verilog-beg-of-defun) 
	     (point-marker)))
	(e (progn 
	     (verilog-end-of-defun) 
	     (point-marker)))
	(beg 0)
	(func "Unknown")
	)
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
	    (verilog-re-search-forward verilog-label-re nil 'move))
      (cond ((match-end 1)		; begin|case|fork
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

(defun verilog-beg-of-statement ()
  "Move backward to beginning of statement"
  (interactive)
  (while (verilog-continued-line))
  (verilog-forward-syntactic-ws)
)
(defun verilog-end-of-statement ()
  "Move forward to end of current statement."
  (interactive)
  (let ((nest 0) pos)
    (if (not (looking-at "[ \t\n]")) (forward-sexp -1))
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
  "Return TRUE if in a case region"
  (interactive)
  (save-excursion
    (catch 'found
      (let ((nest 0))
	(while t
	  (verilog-re-search-backward "\\(\\<module\\>\\)\\|\\(\\<case[xz]?\\>\\)\\|\\(\\<endcase\\>\\)\\>" nil 'move)
	  (cond
	   ((match-end 3)
	    (setq nest (1+ nest)))
	   ((match-end 2)
	    (setq nest (1- nest)))
	   ( t
	     (throw 'found (< nest 0)))
	   )
	  )
	)
      )
    )
  )
(defun verilog-backward-case-item (lim)
  "Skip backward to nearest case item"
  (interactive)
  (let (
	(str 'nil)
	(lim1 (progn 
		(save-excursion (verilog-re-search-backward verilog-endcomment-reason-re lim 'move)
				(point)))))
    ;; Try to find the real :
    (if (save-excursion (search-backward ":" lim1 t))
	(let ((colon 0)
	      b e )
	  (while (and (< colon 1)
		      (verilog-re-search-backward "\\(\\[\\)\\|\\(\\]\\)\\|\\(:\\)" lim1 'move))
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
	    (setq b (progn
		      (if (verilog-re-search-backward "\\<\\(case\\)\\>\\|;\\|\\<end\\>" nil 'move)
			  (progn
			    (cond 
			     ((match-end 1)
			      (goto-char (match-end 1))
			      (verilog-forward-ws&directives)
			      (if (looking-at "(")
				  (let ((par 1))
				    (forward-char 1)
				    (while (and (/= par 0) 
						(verilog-re-search-forward "\\((\\)\\|\\()\\)" nil 'move))
				      (cond
				       ((match-end 1)
					(setq par (1+ par)))
				       ((match-end 2)
					(setq par (1- par)))))
				    (verilog-forward-ws&directives)
				    )
				)
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
	    (if (setq e (string-match "\n" str))
		(setq str (concat (substring str 0 e) "...")))
	    str)
      'nil)
    )
  )


;;;
;;; Other functions
;;;

(defun verilog-set-auto-endcomments (indent-str kill-existing-comment)
  "Insert `// case ' or `// NAME ' on this line if appropriate.
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
      (let ( (reg "\\(`else\\)\\|\\(`ifdef\\)\\|\\(`endif\\)")
	     (nest 1)
	     b e 
	     (else (if (match-end 2)
		       1
		     0))
	     )
	(end-of-line)
	(if kill-existing-comment
	    (progn
	      (let ((e (point))
		    (b (search-backward "//" (verilog-get-beg-of-line) t)))
		(if b
		    (delete-region b e)))))
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
	  (setq b (progn 
		    (skip-chars-forward "^ \t")
		    (verilog-forward-syntactic-ws)
		    (point))
		e (progn
		    (skip-chars-forward "a-zA-Z0-9_")
		    (point)
		    )))
	(insert (concat (if 
			    (= else 0)
			    " // ifdef " 
			  " // !ifdef ")
			(buffer-substring b e)))))
     
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
	      (looking-at "\\(\\<endcase\\>\\)\\|\\(\\<end\\>\\)\\|\\(\\<end\\(\\(function\\)\\|\\(task\\)\\|\\(module\\)\\|\\(primitive\\)\\)\\>\\)")
	      (cond
	       (;- This is a case block; search back for the start of this case
		(match-end 1)
		
		(let ((nest 1) 
		      (err 't)
		      (str "UNMATCHED!!"))
		  (save-excursion
		    (backward-sexp 1)
		    (while (and (/= nest 0)
				(verilog-re-search-backward verilog-endcase-re nil 'move))
		      (cond 
		       ((match-end 1) ; case|casex|casez
			(setq nest (1- nest)))
		       ((match-end 2) ; endcase
			(setq nest (1+ nest)))))
		    (if (match-end 0)
			(progn
			  (goto-char (match-end 1))
			  (setq str (verilog-get-expr))
			  (setq err nil)
			  (setq str (concat "case " str)))))
		  (end-of-line)
		  (if kill-existing-comment
		      (progn
			(let ((e (point))
			      (b (search-backward "//" (verilog-get-beg-of-line) t)))
			  (if b
			      (delete-region b e)))))
		  (delete-horizontal-space)
		  (insert (concat " // " str ))
		  (if err (ding 't))
		  ))
	       
	       (;- This is a begin..end block
		(match-end 2)
		(let ((nest 1) 
		      (str " // UNMATCHED !!")
		      (err 't)
		      (reg "\\<\\(begin\\)\\|\\(end\\)\\>")
		      (here (point))
		      cntx
		      )
		  (save-excursion
		    (while (and (/= nest 0)
				(verilog-re-search-backward reg nil 'move))
		      (cond 
		       ((match-end 1) ; begin
			(setq nest (1- nest)))
		       ((match-end 2) ; end
			(setq nest (1+ nest)))))
		    (if (not (match-end 0))
			(progn
			  (goto-char here)
			  (end-of-line)
			  (if kill-existing-comment
			      (progn
				(let ((e (point))
				      (b (search-backward "//" (verilog-get-beg-of-line) t)))
				  (if b
				      (delete-region b e)))))
			  (delete-horizontal-space)
			  (insert str)
			  (ding 't)			  
			  )
		      (let (sp (lim (save-excursion (verilog-beg-of-defun) (point))))
			(cond
			 (;-- handle named block differently
			  (looking-at verilog-named-block-re)
			  (search-forward ":")
			  (setq str (verilog-get-expr))
			  (setq err nil)
			  (setq str (concat " // block: " str )))
			 
			 ((and
			   (verilog-in-case-region-p) ;-- handle case item differently
			   (setq str (verilog-backward-case-item lim)))
			  (setq err nil)
			  (setq str (concat " // case: " str ))
			  )
			 (;- try to find "reason" for this end
			  (progn 
			    (setq sp (point))
			    (verilog-re-search-backward verilog-endcomment-reason-re lim 'move))
			  (setq cntx (concat 
				      (buffer-substring (match-beginning 0) (match-end 0)) " "))
			  (cond
			   (;- fork
			    (match-end 1)
			    (setq err nil)
			    (setq str ""))			  			  
			   (;- begin -- likely no other interesting data
			    (match-end 2)
			    (setq err nil)
			    (save-excursion
			      (goto-char sp)
			      (if (verilog-continued-line)
				  (setq str (progn 
					      (beginning-of-line)
					      (concat " // " (verilog-get-expr))))
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
					  (setq err nil)
					  (setq str (verilog-get-expr))
					  (setq str (concat " // else !if" str ))
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
			    (setq err nil)
			    (setq str (verilog-get-expr))
			    (setq str (concat " // " cntx str )))
			   
			   (;-- otherwise...
			    (setq str " // auto-endcomment confused ")
			    )
			   )
			  )
			 )
			)
		      (goto-char here)
		      (end-of-line)
		      (if kill-existing-comment
			  (progn
			    (let ((e (point))
				  (b (search-backward "//" (verilog-get-beg-of-line) t)))
			      (if b
				  (delete-region b e)))))
		      (delete-horizontal-space)
		      (insert str)
		      (if err (ding 't))
		      )
		    )))
	       (;- this is end{function,task,module}
		t 
		(let (string reg (width nil))
		  (end-of-line)
		  (if kill-existing-comment
		      (progn
			(let ((e (point))
			      (b (search-backward "//" (verilog-get-beg-of-line) t)))
			  (if b
			      (delete-region b e)))))
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
     (;- is it a begin
      (and (looking-at "\\<begin\\>")
	   (not (save-excursion
		  (end-of-line)
		  (search-backward ":" (verilog-get-beg-of-line) t))))
      (let ((str nil)
	    (depth 0)
	    (nest 0)
	    )
	(save-excursion
	  (catch 'done
	    (while (verilog-re-search-backward "\\<\\(begin\\)\\|\\(end\\)\\|\\(fork\\)\\|\\(if\\)\\|\\(else\\)\\|\\(task\\)\\|\\(function\\)\\|\\(initial\\)\\|\\(always\\(\[ \t\]*@\\)?\\)\\|\\(while\\)\\|\\(for\\)\\>" nil 'move))
	    (cond
	     ((match-end 1) ; begin
	      (setq nest (1- nest))
	      (cond
	       ((= 0 nest)
		(setq depth (1+ depth)))
	       ((= -1 nest)
		(throw 'done 1))
	       )
	      )
	     ((match-end 2) ; end
	      (setq nest (1+ nest)))
	     ((match-end 3) ; fork
	      (setq str (concat " // parallel begin # " depth )))
	     (;
	      t
	      (throw 'done 1)
	      ))))
	(if str
	    (progn
	      (end-of-line)
	      (if kill-existing-comment
		  (progn
		    (let ((e (point))
			  (b (search-backward "//" (verilog-get-beg-of-line) t)))
		      (if b
			  (delete-region b e)))))
	      (delete-horizontal-space)
	      (insert str)))))
     )
    )
  )

(defun verilog-get-expr()
  "Grab expression at point, e.g, case ( a | b & (c ^d))"
  (let* ((b (progn 
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
	       ('t
		(skip-chars-forward "^: \t\n")
		(point)
		))))
	 (str (buffer-substring b e)))
    (if (setq e (string-match "\n" str))
	(setq str (concat (substring str 0 e) "...")))
    str)
  )


;;;
;;; Indentation
;;;
(defconst verilog-indent-alist
  '((block       . (+ ind verilog-indent-level))
    (case        . (+ ind verilog-case-indent))
    (cexp     . (+ ind verilog-indent-indent))
    (defun       . verilog-indent-level)
    (declaration . verilog-indent-level)
    (tf          . verilog-indent-level)
    (behavorial  . verilog-indent-level)
    (caseblock   . ind) 
    (endblock    . ind)
    (statement   . ind)
    (cpp         . 0)
    (comment     . (verilog-indent-comment t))
    (unknown     . 3) 
    (string      . 0)))

(defun verilog-calculate-indent ()
  "Calculate the indent of the current Verilog line, through examination
of previous lines.  Once a line is found that is definitive as to the
type of the current line, return that lines' indent level and it's
type. Return a list of two elements: (INDENT-TYPE INDENT-LEVEL)."
  (save-excursion
    (let* ((oldpos (point))
	   (par 0) 
	   (begin (looking-at "[ \t]*begin\\>"))
	   (type (catch 'nesting
		   ;; Keep working backwards until we can figure out
		   ;; what type of statement this is.
		   ;; Basically we need to figure out 
		   ;; 1) if this is a continuation of the previous line;
		   ;; 2) are we in a block scope (begin..end)
		   (if (verilog-in-star-comment)
		       (throw 'nesting 'comment))
		   (if (verilog-in-paren)
		       (progn
			 (setq par 1)
			 (throw 'nesting 'block)))
		   ;; See if we are continuing a previous line
		   (while t
		     (if (bobp)
			 (throw 'nesting 'cpp))
		     (if (verilog-continued-line)
			 (let ((sp (point)))
			   (if (and
				(not (looking-at verilog-complete-reg))
				(verilog-continued-line))
			       (progn (goto-char sp)
				      (throw 'nesting 'statement))
			     (goto-char sp))
			   (if (and begin
				    (not verilog-indent-begin-after-if)
				    (looking-at verilog-no-indent-begin-re))
			       (throw 'nesting 'statement)
			     (throw 'nesting 'block)))
		       (goto-char oldpos))
		     (if (looking-at "\\<else\\>")
			 ;; search back for governing if, striding across begin..end pairs
			 ;; appropriately
			 (let ((reg (concat
				     verilog-end-block-re
				     "\\|\\(\\<else\\>\\)"
				     "\\|\\(\\<if\\>\\)"
				     ))
			       (elsec 1)
			       )
			   (while (verilog-re-search-backward reg nil 'move)
			     (cond 
			      ((match-end 1) ; endblock
					; try to leap back to matching outward block by striding across
					; indent level changing tokens then immediately
					; previous line governs indentation.
			       (let ((reg)(nest 1))
				 (looking-at verilog-end-block-re-1);; end|join|endcase|endtable|endspecify
				 (cond 
				  ((match-end 1) ; end
				   ;; Search back for matching begin
				   (setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" )
				   )
				  ((match-end 2) ; endcase
				   ;; Search back for matching case
				   (setq reg "\\(\\<case[xz]?\\>\\)\\|\\(\\<endcase\\>\\)" )
				   )
				  ((match-end 3) ; join
				   ;; Search back for matching fork
				   (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" )
				   )
				  ((match-end 4) ; endtable
				   ;; Search back for matching table
				   (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" )
				   )
				  ((match-end 5) ; endspecify
				   ;; Search back for matching table
				   (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" )
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
			      ((match-end 2) ; else, we're in deep
			       (setq elsec (1+ elsec))				 
			       )
			      ((match-end 3) ; found it
			       (setq elsec (1- elsec))
			       (if (= 0 elsec)
				   ;; Now previous line describes syntax
				   (throw 'nesting 'statement)
				   )))
			     )
			   )
		       )
		     (while (verilog-re-search-backward verilog-indent-reg nil 'move)
;;		       (setq cnt (1+ cnt)) (message "indent calc: %d" cnt) (sit-for 1)
		       (cond 
			((match-end 2) ; endblock
					; try to leap back to matching outward block by striding across
					; indent level changing tokens then immediately
					; previous line governs indentation.
			 (let ((reg)(nest 1))
			   (looking-at verilog-end-block-re-1);; end|join|endcase|endtable|endspecify
			   (cond 
			    ((match-end 1) ; end
			     ;; Search back for matching begin
			     (setq reg "\\(\\<begin\\>\\)\\|\\(\\<end\\>\\)" )
			     )
			    ((match-end 2) ; endcase
			     ;; Search back for matching case
			     (setq reg "\\(\\<case[xz]?\\>\\)\\|\\(\\<endcase\\>\\)" )
			     )
			    ((match-end 3) ; join
			     ;; Search back for matching fork
			     (setq reg "\\(\\<fork\\>\\)\\|\\(\\<join\\>\\)" )
			     )
			    ((match-end 4) ; endtable
			     ;; Search back for matching table
			     (setq reg "\\(\\<table\\>\\)\\|\\(\\<endtable\\>\\)" )
			     )
			    ((match-end 5) ; endspecify
			     ;; Search back for matching specify
			     (setq reg "\\(\\<specify\\>\\)\\|\\(\\<endspecify\\>\\)" )
			     )
			    )
			   (catch 'skip
			     (while (verilog-re-search-backward reg nil 'move)
			       (cond 
				((match-end 1) ; begin
				 (setq nest (1- nest))
				 (if (= 0 nest)
				     ;; Now previous line describes syntax
				     (throw 'skip 1)))
				((match-end 2) ; end
				 (setq nest (1+ nest)))))
			     )
			   )
			 )

			((match-end 1)   ; beg-block
			 (looking-at verilog-beg-block-re-1)
			 (cond
			  ((match-end 2)  (throw 'nesting 'case))
			  (t              (throw 'nesting 'block))))

			((or (match-end 3) (match-end 5) (match-end 6))  
			 (throw 'nesting 'defun)) 

			((match-end 4)                     (throw 'nesting 'cpp))

			((bobp) (throw 'nesting 'cpp))
			)
		       )
		     )
		   )
		 )
	   )
      ;; Return type of block and indent level.
      (if (not type)
	  (setq type 'cpp))
      (if (> par 0)			; Unclosed Parenthesis 
	  (list 'cexp par)
	(if (eq type 'case)
	    (list type (verilog-case-indent-level))
	  (list type (verilog-indent-level)))))))

(defun verilog-continued-line ()
  "Return true if this is a continued line.
   Keep skipping past comments to find previous token."
  (if (eq 0 (forward-line -1))
      (progn
	(end-of-line)
	(verilog-backward-ws&directives)
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
	    (let ((par 1)
		  )
	      (backward-char 1)
	      (while 
		  (and (/= par 0) 
		       (verilog-re-search-backward 
			"\\((\\)\\|\\()\\)" nil 'move))
		(cond
		 ((match-end 1)
		  (setq par (1- par)))
		 ((match-end 2)
		  (setq par (1+ par)))))
	      (backward-char 1)
	      (verilog-backward-syntactic-ws))
	    (forward-word -1)
	    (not (looking-at "\\<case[xz]?\\>"))))
	 
	 (;-- any of begin|initial|while are complete statements; 'begin : foo' is also complete
	  t
	  (forward-word -1)
	  (cond 
	   ( (looking-at "initial\\>")  t)
	   ( (looking-at verilog-indent-reg) nil)
	   
	   (t
	    (let 
		((back (point)))
	      (verilog-backward-syntactic-ws)
	      (if (= (preceding-char) ?\:)
		  (progn (backward-char)
			 (verilog-backward-syntactic-ws)
			 (backward-sexp)
			 (if (looking-at "begin")
			     nil
			   t)
			 )
		(progn 
		  (goto-char back)
		  t))
	      
	      )
	    )
	   )
	  )
	 )
	)
    nil)
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
      )))

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
		(if (looking-at "[ \t]*\\(`define\\)\\|\\(`ifdef\\)\\|\\(`else\\)\\|\\(`endif\\)\\|\\(`timescale\\)\\|\\(`include\\)")
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
		(if (looking-at "[ \t]*\\(`define\\)\\|\\(`ifdef\\)\\|\\(`else\\)\\|\\(`endif\\)\\|\\(`timescale\\)")
		    (setq jump t)))
	      (if jump
		  (beginning-of-line 2))
	      )))
      )))
(defun verilog-parenthesis-depth ()
 "Return non zero if in parenthetical-expression"
 (save-excursion
   (and (verilog-re-search-backward "\\((\\)\\|\\()\\)" nil 'move)
	(match-end 1))))

(defun verilog-in-comment-or-string-p ()
 "Return true if in a string or comment"
 (let ((state 
	(save-excursion
	  (parse-partial-sexp (point-min) (point)))))
   (or (nth 3 state) (nth 4 state) (nth 7 state))) ; Inside string or comment
 )

(defun verilog-in-star-comment ()
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
    (delete-horizontal-space)
    (cond 
     (;-- Declaration -- maybe line 'em up
      (and (looking-at verilog-declaration-re)
	   (or (memq 'all verilog-auto-lineup)
	       (memq 'declaration  verilog-auto-lineup)))
      (verilog-indent-declaration ind)
      )
     (; handle inside parenthetical expressions
      (eq type 'cexp)
      (let ((column (save-excursion
		      (backward-up-list 1)
		      (forward-char 1)
		      (skip-chars-forward " \t")
		      (current-column))))
	(beginning-of-line)
	(delete-horizontal-space)
	(indent-to  column)))

     (;-- Case -- maybe line 'em up
      (and (eq type 'case) (not (looking-at "^[ \t]*$")))
      (progn
	(cond
	 ((looking-at "\\<endcase\\>")
	  (indent-to ind))
	 (t
	  (indent-to (eval (cdr (assoc type verilog-indent-alist))))
	  ))))
     
     (;-- Handle the ends
      (looking-at verilog-end-block-re)
      (if (eq type 'statement)
	  (indent-to (- ind verilog-indent-level))		 
	(indent-to ind)))
     (;-- defun
      (and (eq type 'defun)
	   (looking-at verilog-zero-indent-re))
      (indent-to 0))
     (;-- Everything else
      t
      (let ((val (eval (cdr (assoc type verilog-indent-alist)))))
	;;	(verilog-comment-depth type val)
	(delete-horizontal-space)
	(indent-to val)
	))
     )
    (if (looking-at "[ \t]+$")
	(skip-chars-forward " \t"))
    indent-str				; Return verilog-calculate-indent data
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
    (beginning-of-line)
    (skip-chars-forward " \t")
    (cond
     ((looking-at verilog-named-block-re)
      (current-column))
     ((and (not (looking-at verilog-case-re))
	   (looking-at "[^:;]+[ \t]*:"))
      (search-forward ":" nil t)
      (skip-chars-forward " \t")
      (current-column))
     (t
      (current-column)))))

(defun verilog-indent-comment (&optional arg)
  "Indent current line as comment.
If optional arg is non-nil, just return the
column number the line should be indented to."
    (let* ((stcol (save-excursion
		    (re-search-backward "/\\*\\|//" nil t)
		    (1+ (current-column)))))
      (if arg stcol
	(delete-horizontal-space)
	(indent-to stcol))))

;;;


(defun verilog-indent-declaration (base-ind &optional arg start end)
  "Indent current lines as declaration, lining up the variable names"
  (interactive)
  (let ((pos (point-marker))
	(lim (save-excursion (progn (end-of-line) (point-marker))))
	)
    (if (and (not (or arg start)) (not (verilog-re-search-forward verilog-declaration-re lim t)))
	()
      (progn
	(beginning-of-line)
	(delete-horizontal-space)
	(indent-to (+ base-ind (eval (cdr (assoc 'declaration verilog-indent-alist)))))
	(let* ((pos2 (point-marker))
	       (more 1)
	       here
	       (stpos (if start start
		       (save-excursion
			 
			 (goto-char pos2)
			 (catch 'first
			   (while more
			     (setq here (point))
			     (verilog-backward-syntactic-ws)
			     (beginning-of-line)
			     (if (bobp)
				 (throw 'first (point-marker)))				 
			     (verilog-forward-syntactic-ws)
			     (if (looking-at verilog-declaration-re)
				 (setq more (/= (point) here))
			       (throw 'first (point-marker))))
			   (throw 'first (point-marker)))
			 )
		       )
		      )
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
		(cond 
		 ((looking-at "^[ \t]*$")
		  ())
		 ((not (looking-at verilog-declaration-re))
		  (indent-to arg))
		 (t
		  (indent-to (+ arg verilog-indent-level))))
		(forward-line 1)))
	  
	  ;; Do lineup
	  (setq ind (verilog-get-lineup-indent stpos edpos))
	  (goto-char stpos)
	  (if (> (- edpos stpos) 100)
	      (message "Lining up declarations..(please stand by)"))
	  (let (e)
	    (while (progn (setq e (marker-position edpos))
			  (< (point) e))
	      (if (verilog-re-search-forward verilog-declaration-re-1 e 'move)
		  (just-one-space))
;;		  (forward-char -1))
	      (save-excursion
		(let ((p (point)))
		  (beginning-of-line)
		  (if (verilog-re-search-forward "\\[" p 'move)
		      (progn
			(forward-char -1)
			(just-one-space)))
		  ))
	      (delete-horizontal-space)
	      (indent-to ind)
	      (beginning-of-line)
	      (delete-horizontal-space)	      
	      (indent-to (+ base-ind (eval (cdr (assoc 'declaration verilog-indent-alist)))))
	      (forward-line 1)))))
	
      ;; If arg - move point
      (message "")
      (if arg (forward-line -1)
	(goto-char (marker-position pos))))))

;  "Return the indent level that will line up several lines within the region
;from b to e nicely. The lineup string is str."
(defun verilog-get-lineup-indent (b edpos)
  (save-excursion
    (let ((ind 0)
	  e
	  (reg (concat verilog-declaration-re "[ \t]*\\(\\[[^]]*\\][ \t]*\\)?")) )
      (goto-char b)
      ;; Get rightmost position
      (while (progn (setq e (marker-position edpos))
		    (< (point) e))
	(if (verilog-re-search-forward reg e 'move)
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
  '("buf" "bufif0" "bufif1" "cmos" "inout" "input"
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
  "*Keywords to complete when standing at first word of a line in behavorial scope.
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
  "*Keywords to complete when standing at first word of a line in behavorial scope.
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

;;; verilog.el ends here
