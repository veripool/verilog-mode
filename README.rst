===================
Verilog-Mode README
===================

Summary
=======

This is the source distribution repository for verilog-mode, the Verilog
editing and AUTOs package which is part of GNU Emacs
(lisp/progmodes/verilog-mode.el).

Verilog-Mode supports syntax highlighting of SystemVerilog (IEEE
1800-2017), Verilog (IEEE 1364-2005), and the Universal Verification
Modeling language (UVM). Verilog-Mode also has AUTOs which greatly
accelerate maintaining interconnect, resets, and other boiler-plate code.

|Example1|


Documentation
=============

See https://www.veripool.org/verilog-mode for more information.


Installation
============

You have several installation options:


Option 1: Sources
-----------------

You may use the `Verilog-Mode Source Tree
<https://github.com/veripool/verilog-mode>`__. If using these sources you
will need to "make" then install e/verilog-mode.el, not the verilog-mode.el
in the top of the directory (which does not have the version number in
it). In detail:

::

   git clone https://github.com/veripool/verilog-mode
   make
   # Copy to somewhere in your Emacs "M-x describe-variable load-path"
   cp e/verilog-mode.el* /usr/share/emacs/site-lisp

(Do not use the github ZIP download option as this will not build
correctly, the version number will be unknown.)


Option 2: ELPA
--------------

Verilog Mode is part of the ELPA (Emacs Lisp Package Archive). Using a
recent version of Emacs:

::

   M-x list-packages RET

then search for Verilog Mode:

::

   C-s verilog-mode RET RET

then click on "Install".


Option 3: Emacs Native
----------------------

Verilog-mode.el also comes included as part of Emacs 21 and later. This
version always lags the version here, often by years. Please consider using
the sources method instead.


Tests
=====

The main purpose of this repository is the extended test suite.
(Verilog-mode.el itself being both here and in the GNU Emacs repository.)

To run the tests, make sure both GNU Emacs and Xemacs are installed, then:

::

   make
   make test

Under the hood this is (mostly) running ``0test.el``. This reads in each
file under ``tests/`` directory, AUTOs, reindents, and compares the result
to the matching filename in the ``tests_ok`` directory.

Test failures generally look like this:

::

   diff -c tests_ok/autoinout_ma.v e/t/autoinout_ma.v
   ***Golden Reference File
   ---Generated Test File
   --- GOLDEN_REFERENCE
   +++ CURRENT_BEHAVIOR
   ...
   -   output sina,
   +   output siuna,
   To promote current to golden, in shell buffer hit newline anywhere in next line (^P RETURN):
   cp e/t/autoinout_ma.v tests_ok/autoinout_ma.v; VERILOG_MODE_START_FILE=tests_ok/autoinout_ma.v make test_emacs

This indicates the generated output doesn't match what is in tests_ok.  To
fix this make sure that the change is expected then do the ``cp`` shown to
update the golden references:

::

   cp e/t/autoinout_ma.v tests_ok/autoinout_ma.v

Then ``make test`` again. The output also suggests a
``VERILOG_MODE_START_FILE`` which can also be used to jump right to that
individual test inside the ``make test``.


License
=======

Verilog-mode itself is part of GNU Emacs, which is Copyright 2001-2021 Free
Software Foundation, Inc. This package is free software; you can
redistribute it and/or modify it under the terms of the GNU General Public
License Version 3.

The Verilog test files unless specified otherwise are released into the
public domain.

.. |Example1| image:: https://www.veripool.org/img/verilogmode_post.gif
