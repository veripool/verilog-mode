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

  ;; Local functions
  (defun global-replace-regexp (from to)
    (goto-char (point-min))
    (while (re-search-forward from nil t)
      (replace-match to nil nil)))

  (defun verilog-test-file (file temp-file)
    (save-excursion
      (message (concat file ": finding..."))
      (find-file (concat "tests/" file))
      (message (concat file ": deleting autos..."))
      (verilog-delete-auto)
      (message (concat file ": testing indent..."))
      (save-excursion
	(goto-char (point-min))
	(while (not (eobp))
	  (electric-verilog-tab)
	  (forward-line 1)))
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
    (message (concat file ": running diff..."))
    (with-temp-buffer
      (let* ((status
	      (call-process "diff"
			    nil (current-buffer) nil
			    "-w"
			    (concat "tests_ok/" file)
			    temp-file)))
	;(delete-file temp-file)
	(cond ((not (equal status 0))
	       (message (concat "diff tests_ok/" file " " temp-file))
	       (message "<Golden Reference File\n>Generated Test File")
	       (message (concat "#if OK: cp " temp-file " tests_ok/" file))
	       (message (buffer-string))
	       (error "%%Error: Didn't Verify %s (status %d)" file status))
	      (t
	       (message "Verified %s" file))))))
    
  (defun verilog-test ()
    (let ((files (directory-files "tests")))
      (when (getenv "VERILOG_MODE_TEST_FILE")
	(setq files (list (getenv "VERILOG_MODE_TEST_FILE")))
	(message "**** Only testing files in $VERILOG_MODE_TEST_FILE"))
      (while files
	(setq file (car files))
	(cond ((equal "." file))
	      ((equal ".." file))
	      ((string-match "~$" file))
	      ((string-match "\.f$" file))
	      ((file-directory-p (concat "tests/" file)))
	      (t
	       (message (concat "Considering test " file ))
	       (if running-on-xemacs 
		   (progn
		     (setq cf (concat "skip_for_xemacs/" file))
		     (if (file-exists-p cf ) ; 
			 (message (concat "Skipping testing " file " on Xemacs because file " cf "exists"))
		       (verilog-test-file file "tests_ok/0temp.v")
		       ))
		 (verilog-test-file file "tests_ok/0temp.v")
		 )
	       ))
	(setq files (cdr files))))
    (message "Tests Passed")
    "Tests Passed")
    
  (verilog-test))


