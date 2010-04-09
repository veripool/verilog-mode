;; $Id: batch_test.el 240 2006-05-05 21:46:14Z wsnyder $
;; DESCRIPTION: Profile driven test

(require 'elp)

(defun t-make-test (count filename)
  (save-excursion
    (find-file filename)
    (delete-region (point-min) (point-max))
    (insert "
module EX_TIME_CONSUME (/*AUTOARG*/);
/*AUTOOUTPUT*/
/*AUTOINPUT*/
/*AUTOWIRE*/
")
    (setq i 0)
    (while (< i count)
      (insert "//----------------------------------------------------------------------\n")
      (insert "/* batch_prof_cell AUTO_TEMPLATE (\n")
      (insert (format "  .Z(Z_%d)); */\n" i))
      (insert (format "batch_prof_cell CELL_%d (/*AUTOINST*/);\n" i))
      (setq i (+ 1 i)))
    (insert "endmodule\n")
    (save-buffer)))

(defun t-size-test (count)
  ;; Note is running in tests_batch_ok directory
  (setq filename (format "test_dir/batch_prof_%s.v" count))
  (t-make-test count filename)
  (when profile
    (elp-reset-all))
  (setq start (current-time))
  (save-excursion
    (find-file filename)
    (verilog-auto))
  (setq end (current-time))
  (setq delta (time-to-seconds (time-subtract end start)))
  (setq msper (/ (* 1000 delta) count))
  (message "Count: %5d   Time: %6.3f   msec/inst: %6.3f  File: %s"
	   count delta msper filename)
  (when profile
    (elp-results))
  msper)

;;======================================================================

(setq make-backup-files nil)
(setq verilog-library-flags "-I. -I../tests")
(setq profile nil)

(when profile
  (elp-restore-all)
  (elp-instrument-package "verilog"))

(progn
  ;; Need to read the templated file
  (setq t1 (t-size-test 1))
  (setq t10 (t-size-test 10))
  (setq t100 (t-size-test 100))
  (setq t1000 (t-size-test 1000))
  ;;(setq t10000 (t-size-test 10000))

  (setq slope (/ t1000 t100))
  (setq order (1+ (/ (log slope)
		     (log 10))))
  (message "Slope: %f  Complexity: O(n^%f)" slope order)
  (if (> slope 1.2)
      (error "Test failed, large modules are too slow compared to small modules"))
)
