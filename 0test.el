;; DESCRIPTION: Run verilog-mode tests, as part of "make test"
;;
;; Copyright 2008-2013 by Michael McNamara and Wilson Snyder.  This package
;; is free software; you can redistribute it and/or modify it under the
;; terms of either the GNU Lesser General Public License or the Perl
;; Artistic License.
;;
;;   VERILOG_MODE_DEBUG=1	       # Enable verilog-debug
;;   VERILOG_MODE_NO_INDENTS=1         # Disable indent checks
;;   VERILOG_MODE_TEST_FILE=filename.v # Run only specified test
;;   VERILOG_MODE_START_FILE=filename.v  # Start at specified test
;;   VERILOG_MODE_THREAD=#of#          # Multithreaded testing
;;   VERILOG_MODE_PROFILE=1            # Profile - see batch_prof.el
;;   HARNESS_UPDATE_GOLDEN=1	       # Update golden reference files

(defvar diff-flags "-u")
(defvar vl-threading (and (not (getenv "VERILOG_MODE_TEST_FILE"))
			  (getenv "VERILOG_MODE_THREAD")))

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

    (unless (getenv "VERILOG_MODE_NO_INDENTS")
      (verilog-test-indent-buffer file)
      
;;      (message (concat file ": testing auto endcomments..."))
;;      (verilog-label-be)
  
      (untabify (point-min) (point-max))
      )
    (write-file (concat "../" temp-file))
    (kill-buffer nil))
  ;;
  (vl-diff-file (concat "tests_ok/" file) temp-file))

(defun verilog-test-indent-buffer (file )
  (interactive)
  (message (concat file ": testing indent..."))
  (save-excursion
    (goto-char (point-min))
    (let* ((ln 0))
      (while (not (eobp))
	;;(message (format "%d" ln))
	;;(message (format "%s : %d - indent" file ln))
	(electric-verilog-tab)
	;;(message (format "%s : %d - pretty-expr" file ln))
	(verilog-pretty-expr t )
	;;(message (format "%s : %d - pretty-declaration" file ln))
	(verilog-pretty-declarations t)
	(forward-line 1)
	(setq ln (1+ ln))
	)
      (message (format "Indented %d lines" ln))
      ))
  (message (concat file ": indents OK...")))
  
(defun vl-diff-file (golden-file temp-file)
  (message (concat golden-file ": running diff of " golden-file " and " temp-file ))
  (with-temp-buffer
    (let* ((status
	    (call-process "diff" nil t t diff-flags "--label" "GOLDEN_REFERENCE" golden-file "--label" "CURRENT_BEHAVIOR" temp-file )))
      (cond ((and (not (equal status 0))
		  (getenv "HARNESS_UPDATE_GOLDEN"))
	     (message "***HARNESS_UPDATE_GOLDEN set - updating Golden Reference File")
	     (call-process "cp" nil t t temp-file golden-file))
	    ((not (equal status 0))
	     (message (concat "diff -c " golden-file " " temp-file))
	     (message "***Golden Reference File\n---Generated Test File")
	     (message "%s" (buffer-string))
	     (message "To promote current to golden, in shell buffer hit newline anywhere in next line (^P RETURN):")
	     (message (concat "cp " temp-file " " golden-file "; VERILOG_MODE_START_FILE=" golden-file " " again ))
	     (error ""))
	    (t
	     (message "Verified %s" golden-file))))))

(defun vl-do-on-thread (file-num)
  "Return true to process due to multithreading"
  (cond (vl-threading
	 (or (string-match "\\([0-9]+\\)of\\([0-9]+\\)" vl-threading)
	     (error "VERILOG_MODE_THREAD not in #of# form"))
	 (let ((th (string-to-number (match-string 1 vl-threading)))
	       (numth (string-to-number (match-string 2 vl-threading))))
	   (equal (1+ (mod file-num numth)) th)))
	(t t)))

(defun verilog-test ()
  (let ((files (directory-files "tests"))
        (tests-run 0)
	(file-num 0)
	file cf temp-file)

    (when (getenv "VERILOG_MODE_DEBUG")
      (setq verilog-debug t))

    (when (getenv "VERILOG_MODE_TEST_FILE")
      (setq files (list (getenv "VERILOG_MODE_TEST_FILE")))
      (message "**** Only testing files in $VERILOG_MODE_TEST_FILE"))
    
    (when (getenv "VERILOG_MODE_START_FILE")
      (let* ((startfiles (list (getenv "VERILOG_MODE_START_FILE")))
	     (startfile (car startfiles)))
	(message (concat "Starting from file " startfile))
	(catch 'done
	  (while files
	    (setq file (car files))
	    (if (or (string-equal file startfile)
		    (string-equal (concat "tests_ok/" file) startfile))
		(progn
		  (message (concat "matched " file))
		  (throw 'done 0))
	      (progn
		(setq files (cdr files))))))))
    
    (message "emacs-version %s" emacs-version)

    (while files
      (setq file (car files))
      (setq temp-file (concat (if running-on-xemacs "x/t/" "e/t/")
			      file))
      (cond ((equal "." file))
            ((equal ".." file))
            ((string-match "#" file))  ;; Backups
            ((string-match "~$" file))
            ((string-match "\.f$" file))
            ((string-match "\.dontrun$" file))
            ((file-directory-p (concat "tests/" file)))
	    ((progn (setq file-num (1+ file-num))
		    (not (vl-do-on-thread file-num))))
            (t
             (message (concat "Considering test " file ))
             (if running-on-xemacs 
                 (progn
                   (setq cf (concat "skip_for_xemacs/" file))
                   (if (file-exists-p cf ) ; 
                       (message (concat "Skipping testing " file " on Xemacs because file " cf "exists"))
                     (progn
		       (verilog-test-file file temp-file)
                       (setq tests-run (1+ tests-run))
                       )
                     ))
               (progn
		 (verilog-test-file file temp-file)
                 (setq tests-run (1+ tests-run))
                 ))
	     (message (format " %d tests run so far, %d left... %s"
			      tests-run (length files)
			      (if vl-threading (concat "Thread " vl-threading) "")))
	     ))
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
  (defun ask-user-about-lock() nil)  ;; XEmacs - Disable lock conflicts
  (setq running-on-xemacs (string-match "XEmacs" emacs-version))
  (setq make-backup-files nil)
  (setq-default make-backup-files nil)
  (setq diff-flags (if (getenv "VERILOG_MODE_NO_INDENTS") "-wBu" "-u"))
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
