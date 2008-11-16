;; $Id$
(progn
  (save-excursion
    (with-temp-buffer
     (verilog-mode)))

  ;; Setup
  (require `compile)
  (setq running-on-xemacs (string-match "XEmacs" emacs-version))
  (setq make-backup-files nil)
  (setq-default make-backup-files nil)
  (setq enable-local-variables t)
  (setq enable-local-eval t)
  (setq auto-mode-alist (cons  '("\\.v\\'" . verilog-mode) auto-mode-alist))
  (setq-default fill-column 100)
  (if running-on-xemacs 
      (setq again "!xemacs")
    (setq again "!emacs"))
  ;; Local functions
  (defun global-replace-regexp (from to)
    (goto-char (point-min))
    (while (re-search-forward from nil t)
      (replace-match to nil nil)))

  (defun verilog-test-file (file temp-file)
    (save-excursion
      (message (concat file ": finding..."))
      (find-file (concat "tests/" file))
      (verilog-mode)
      (message (concat file ": deleting autos..."))
      (verilog-delete-auto)
      (message (concat file ": testing indent..."))
      (save-excursion
	(goto-char (point-min))
	(setq ln 0)
	(while (not (eobp))
	  (electric-verilog-tab)
	  ;;(verilog-pretty-expr t )
	  (forward-line 1)
	  ))
      (message (concat file ": indents OK..."))
      (global-replace-regexp "[ \t]+$" "")
      (cond ((string-match "^inject_" file)
	     (message (concat file ": testing inject-auto..."))
	     (verilog-inject-auto))
	    (t
	     (message (concat file ": testing auto..."))
	     (verilog-auto)))
      (message (concat file ": auto OK..."))
      (write-file (concat "../" temp-file))
      (kill-buffer nil))
    ;;
    (diff-file file))

(defun diff-file (file)
  (message (concat file ": running diff of " file " and tests_ok/" file ))
  (with-temp-buffer
    (let* ((status
	    (call-process "diff" nil (current-buffer) nil 
			   (concat "tests_ok/" file) temp-file)))
      ;(delete-file temp-file)
      (cond ((not (equal status 0))
	     (message (concat "#if OK: cp " temp-file " tests_ok/" file "; setenv VERILOG_MODE_START_FILE " file " ; " again " ; cat tests_ok/0temp.v "))
	     (message (concat "diff tests_ok/" file " " temp-file))
	     (message "<Golden Reference File\n>Generated Test File")
	     (message (buffer-string))
	     (message (concat "#if OK: cp " temp-file " tests_ok/" file "; setenv VERILOG_MODE_START_FILE " file " ; " again " ; cat tests_ok/0temp.v "))
	     (error "%%Error: Didn't Verify %s (status %d)" file status))

	    (t
	     (message "Verified %s" file))))))

  (defun verilog-test ()
    (let ((files (directory-files "tests"))
	  (tests-run 0)
	  )
      (when (getenv "VERILOG_MODE_TEST_FILE")
	(setq files (list (getenv "VERILOG_MODE_TEST_FILE")))
	(message "**** Only testing files in $VERILOG_MODE_TEST_FILE"))

      (when (getenv "VERILOG_MODE_START_FILE")
	(setq startfiles (list (getenv "VERILOG_MODE_START_FILE")))
	(setq startfile (car startfiles))
	(message (concat "Staring from file " startfile))
	(catch 'done
	  (while files
	    (setq file (car files))
	    (if (string-equal file startfile)
		(progn
		  (message (concat "matched " file))
		  (throw 'done 0))
	      (progn
		(setq files (cdr files)))))))
    
      (while files
	(setq file (car files))
	(cond ((equal "." file))
	      ((equal ".." file))
	      ((string-match "^#" file))  ;; Backups
	      ((string-match "~$" file))
	      ((string-match "\.f$" file))
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
	(message (format " %d tests run so far..." tests-run ))
	(setq files (cdr files))))
    (message "Tests Passed")
    "Tests Passed")
    
  (verilog-test))

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
  
