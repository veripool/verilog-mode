;; $Id$
(defvar diff-flags "-c")
;;
;;   VERILOG_MODE_TEST_NO_INDENTS=1    # Disable indent checks
;;   VERILOG_MODE_TEST_FILE=filename   # Run only specified test
;;   VERILOG_MODE_START_FILE=filename  # Start at specified test

(defun global-replace-regexp (from to)
  (goto-char (point-min))
  (while (re-search-forward from nil t)
    (replace-match to nil nil)))

(defun verilog-test-file (file temp-file)
  (save-excursion
    (message (concat file ": finding..."))
    (find-file (concat "tests/" file))
    (verilog-mode)
    (message (concat file ": deleting indent..."))
    (global-replace-regexp "[ \t]+$" "")
    
    (message (concat file ": deleting autos..."))
    (verilog-delete-auto)
    
    (cond 
     ((string-match "^inject_" file)
      (message (concat file ": testing inject-auto..."))
      (verilog-inject-auto))
     (t
      (message (concat file ": testing auto..."))
      (verilog-auto)))
    (message (concat file ": auto OK..."))
    
    (unless (getenv "VERILOG_MODE_TEST_NO_INDENTS")
      (message (concat file ": testing indent..."))
      (save-excursion
	(goto-char (point-min))
	(let* ((ln 0))
	  (while (not (eobp))
	    (message (format "%d" ln))
	    ;;(message (format "%s : %d - indent" file ln))
	    (electric-verilog-tab)
	    ;;(message (format "%s : %d - pretty-expr" file ln))
	    (verilog-pretty-expr t )
	    ;;(message (format "%s : %d - pretty-declaration" file ln))
	    (verilog-pretty-declarations t)
	    (forward-line 1)
	    (setq ln (1+ ln))
	    )))
      (message (concat file ": indents OK..."))
      
;      (message (concat file ": testing auto endcomments..."))
;      (verilog-label-be)
      )
  
    (untabify (point-min) (point-max))
    
    (write-file (concat "../" temp-file))
    (kill-buffer nil))
  ;;
  (diff-file file temp-file))

(defun diff-file (file temp-file)
  (message (concat file ": running diff of " file " and tests_ok/" file ))
  (with-temp-buffer
    (let* ((status
	    (call-process "diff" nil t t diff-flags "--label" "GOLDEN_REFERENCE" (concat "tests_ok/" file) "--label" "CURRENT_BEHAVIOR" temp-file )))
      (cond ((not (equal status 0))
	     (message (concat "diff -c tests_ok/" file " " temp-file))
	     (message "***Golden Reference File\n---Generated Test File")
	     (message "%s" (buffer-string))
	     (message "To promote current to golden, in shell buffer hit newline anywhere in next line (^P RETURN):")
	     (message (concat "cp " temp-file " tests_ok/" file "; VERILOG_MODE_START_FILE=" file " " again ))
	     (error ""))
	    
	    (t
	     (message "Verified %s" file))))))

(defun verilog-test ()
  (let ((files (directory-files "tests"))
        (tests-run 0)
	file cf
        )
    (when (getenv "VERILOG_MODE_TEST_FILE")
      (setq files (list (getenv "VERILOG_MODE_TEST_FILE")))
      (message "**** Only testing files in $VERILOG_MODE_TEST_FILE"))
    
    (when (getenv "VERILOG_MODE_START_FILE")
      (let* ((startfiles (list (getenv "VERILOG_MODE_START_FILE")))
	     (startfile (car startfiles)))
	(message (concat "Staring from file " startfile))
	(catch 'done
	  (while files
	    (setq file (car files))
	    (if (string-equal file startfile)
		(progn
		  (message (concat "matched " file))
		  (throw 'done 0))
	      (progn
		(setq files (cdr files))))))))
    
    (while files
      (setq file (car files))
      (cond ((equal "." file))
            ((equal ".." file))
            ((string-match "^#" file))  ;; Backups
            ((string-match "~$" file))
            ((string-match "\.f$" file))
            ((string-match "\.dontrun$" file))
            ((string-match "\.\#.*$" file))
            ((file-directory-p (concat "tests/" file)))
            (t
             (message (concat "Considering test " file ))
             (if running-on-xemacs 
                 (progn
                   (setq cf (concat "skip_for_xemacs/" file))
                   (if (file-exists-p cf ) ; 
                       (message (concat "Skipping testing " file " on Xemacs because file " cf "exists"))
                     (progn
                       (verilog-test-file file "tests_ok/0temp.v")
                       (setq tests-run (1+ tests-run))
                       )
                     ))
               (progn
                 (verilog-test-file file "tests_ok/0temp.v")
                 (setq tests-run (1+ tests-run))
                 )
               )
             ))
      (message (format " %d tests run so far, %d left..." tests-run (length files)))
      (setq files (cdr files))))
  (message "Tests Passed on %s" (emacs-version))
  "Tests Passed")

(defun vl-indent-file ()
  "Reindent file"
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (while (not (eobp))
      (electric-verilog-tab)
      (end-of-line)
      (delete-char (- (skip-chars-backward " \t")))
      (forward-line 1)
      )
    )
  (write-file (buffer-file-name))
  )

(progn
  (save-excursion
    (with-temp-buffer
     (verilog-mode)))

  ;; Setup
  (require `compile)
  (setq running-on-xemacs (string-match "XEmacs" emacs-version))
  (setq make-backup-files nil)
  (setq-default make-backup-files nil)
  (setq diff-flags (if (getenv "VERILOG_MODE_TEST_NO_INDENTS") "-wBc" "-c"))
  ;;(setq verilog-auto-lineup 'all)
  (setq enable-local-variables t)
  (setq enable-local-eval t)
  (setq auto-mode-alist (cons  '("\\.v\\'" . verilog-mode) auto-mode-alist))
  (setq-default fill-column 100)
  (if running-on-xemacs 
      (setq again "make test_xemacs")
    (setq again "make test_emacs"))
  (verilog-test)
)

