================
Verilog-Mode FAQ
================

.. contents::

This is the Frequently Asked Questions (FAQ) for `Verilog Mode
<https://www.veripool.org/verilog-mode>`__. This FAQ is Copyright 2006-2021
by Michael McNamara and Wilson Snyder. You may redistribute this document
in its entirety only.


Obtaining, and general information
==================================


Where is the most up to date version of this FAQ?
-------------------------------------------------

The official released version of this document is the `Verilog-Mode
FAQ <http://www.veripool.org/verilog-mode/faq>`__: from
http://www.veripool.org/verilog-mode/faq.


Where do I get Verilog-Mode?
----------------------------

Verilog-mode is a standard part of GNU Emacs as of 22.2.

You may wish to still upgrade to the most recent Verilog-Mode, especially
as the GNU Emacs version lags by months to years and as the SystemVerilog
features are under continual improvement. The most recent version is always
available from `Verilog Mode <http://www.veripool.org/verilog-mode>`__.


How do I install Verilog-Mode?
------------------------------

See `Installing Verilog
Mode <https://www.veripool.org/verilog-mode/installing>`__.


Are there other Verilog Modes for Emacs?
----------------------------------------

Sun Yijiang had `vlog-mode.el
<https://sourceforge.net/projects/vlog-mode>`__, but the last updates were
in 2006.


Can I release Verilog-Mode with my tool?
----------------------------------------

Yes. Verilog-Mode is released under the GNU General Public License. See the
license for the full legal details, but fundamentally distributing it
stand-alone with a commercial tool is no problem, you merely need to insure
verilog-mode.el remains available to everyone. If you didn't make any
changes, you're all set, else you'll need to post your version on a public
website, or better, feed the changes back to the authors for inclusion in
the base version.


Entering Verilog-Mode
=====================


Can I run Verilog-Mode from VIM?
--------------------------------

You can run the autos from a VIM macro, see for example:

`verilog_emacsauto.vim : verilog filetype plugin to enable emacs
verilog-mode
autos <http://www.vim.org/scripts/script.php?script_id=1875>`__


Using viper, why when I load a Verilog file does it loose viper?
----------------------------------------------------------------

You need to tell Viper that it is ok with you for files in verilog to come
up in Verilog-Mode and Viper.

To do that, type

::

   M-x customize RET viper-misc

Then scroll down and find the item ``Vi State Mode List`` left-click on the
triangle to open this up. Scroll down through the blizzard of listed modes
to the bottom. You should see:

::

   [INS] [DEL] Symbol: csh-mode
   [INS] [DEL] Symbol: gnus-article-mode
   [INS] [DEL] Symbol: mh-show-mode
   [INS]
      [State]: this option has been set and saved.
   Major modes that require Vi command state

Middle-click on the bare INS; you should get:

::

   [INS] [DEL] Symbol: mh-show-mode
   [INS] [DEL] Symbol: nil
   [INS]
      [State]

Then left-click on nil, and replace the string ``nil`` with
verilog-mode. You should get:

::

   [INS] [DEL] Symbol: mh-show-mode
   [INS] [DEL] Symbol: verilog-mode
   [INS]
      [State]

Now middle-click on ``[State]`` and a pop up menu appears; select ``Set for
Current Session`` and then also middle click again and select ``Save for
Future Sessions``.


Why do I get the message "File mode specification error:"?
----------------------------------------------------------

Or, the similar messages:

::

   File mode specification error:  (void-function define-skeleton)
   File mode specification error: (file-error "Cannot open load file" "overlay")

You need ``skeleton.el``, part of the base package for the first, or
``overlay.el``, part of the fsf-compatibility package for the second, which
are both XEmacs lisp packages, which you somehow have not installed, or
have not updated.

Go to ``Tools -> Packages -> Add download site`` and pick a site
(xemacs.org).

Then select ``Tools -> Packages -> List and Install``

Go to the bottom, and click on the line that says ``xemacs-base``. to get
the skeleton.el file. You will see something like:

::

                    Latest Installed
     Package name   Vers.  Vers.   Description
   ============================================================
     Sun             1.13   1.13   Support for Sparcworks.
        ...
     w3              1.18   1.18   A Web browser.
   * xemacs-base     1.53   1.51   Fundamental XEmacs support.
   - xemacs-devel    1.33   -----  Emacs Lisp developer support.
   - xslt-process    1.03   -----  XSLT processing support.
     zenirc          1.09   1.09   ZENIRC IRC Client.
   ============================================================

For the overlay package, click on the line that says ``fsf-compat``. to get
the ``overlay.el`` file. In this case you will see something like:

::

                    Latest Installed
     Package name   Vers.  Vers.   Description
   ============================================================
     Sun             1.13   1.13   Support for Sparcworks.
        ...
     w3              1.18   1.18   A Web browser.
   * fsf-compat      1.12   ----   FSF EMacs compatibility files
     zenirc          1.09   1.09   ZENIRC IRC Client.
   ============================================================

| When you click on it, the \* changes to a

Then type x, which will install the package.

Then restart XEmacs and things should then work just fine.


Indentation
===========


How do I indent a large region of code?
---------------------------------------

Typing TAB on every line can get old.

Use ``C-M-\`` or ``M-x indent-region`` to indent a region (selected by
setting the point at one end, and having the cursor at the other end, as
usual). Perhaps a future version of the emacs mode will include functions
that mimic some of C's extra bindings.


How do I reindent Verilog code from the command line?
-----------------------------------------------------

You can repair the indentation of a Verilog file from the command line with
the following command:

::

   emacs --batch {filenames...} -f verilog-batch-indent

This will load the file, reindent, and save the file.

If your verilog-mode.el is not installed in a site-wide location, or you
suspect you are getting the wrong version, try specifing the exact path to
Verilog-Mode by adding ``-l {path}/verilog-mode.el`` after ``--batch``.

::

   emacs --batch -l {path}/verilog-mode.el {filenames...} -f verilog-batch-indent

Additional information is in Emacs under ``M-x describe-function
verilog-batch-indent``.


Why when others edit my code does it looks unindented? (aka How do I remove tabs on saving?)
--------------------------------------------------------------------------------------------

This is a general problem sharing files between people. It also occurs
between people using the same editor, as many editors allow one to set the
tab width. The general solution is for you to add a write file hook that
expands tabs to spaces. Add the following to your ``.emacs`` file:

::

   (add-hook 'verilog-mode-hook '(lambda ()
       (add-hook 'local-write-file-hooks (lambda()
          (untabify (point-min) (point-max))))))

This arranges so that any file in verilog mode (the ``add-hook
verilog-mode-hook`` part) gets added to it's ``local-write-file-hooks`` a
call to the function ``untabify`` with arguments that are the first and
last character in the buffer. Untabify converts all tabs in the region to
multiple spaces.


Why can't I insert tabs in some places in the file?
---------------------------------------------------

This is because tab is a electric key that causes reindentation. See
another FAQ for how to disable this.

If you want to manually space something out, in general, in Emacs you can
escape the special meaning of any key by first typing ``C-q``, which quotes
the next key.


How do I prevent tab from automatically indenting?
--------------------------------------------------

Set the ``verilog-tab-always-indent`` variable to nil. If your goal is
minimal intrusion of magic keys, you'll probably also want to set
``verilog-auto-newline`` to nil. Add to your .emacs file:

::

   (add-hook 'verilog-mode-hook
             '(lambda ()
                (setq verilog-auto-newline nil)
                (setq verilog-tab-always-indent nil)
             )))


How do I prevent those // comments at the end of blocks?
--------------------------------------------------------

Set ``verilog-auto-endcomments`` to nil:

::

   (setq verilog-auto-endcomments nil)


Why does Verilog-Mode hang reading a huge file?
-----------------------------------------------

To debug the problem, type:

::

   M-x eval-expression RET
   (setq debug-on-quit t)

Then load the file. After 10 seconds or whatever hit ``Ctrl-G`` to stop
Emacs. It will show in the debugger what it's doing.

If you're using a older flavor of Emacs, most of the time it will stop
somewhere in ``fontification``. Simply disable fontification (coloring) of
larger files. Put into your ``.emacs``:

::

   (setq font-lock-maximum-size 100000)


Why do I not get any colors in huge files?
------------------------------------------

This is sort of the opposite of the last FAQ; any file exceeding the
default size of 256,000 characters will not get font-locked. To override
this, put into your .emacs:

::

   (setq font-lock-maximum-size 2000000)

Alternatively, load the ``lazy-lock`` package. This will only highlight the
region on the screen. To find it, use ``M-x find-library RET lazy-lock``.


Movement
========


How can I jump the cursor to the file that defines a module?
------------------------------------------------------------

Use ``C-c C-d`` or ``M-x verilog-goto-defun``.


How can I invoke my compiler?
-----------------------------

Use ``C-c C-s``, or ``M-x verilog-auto-save-compile``. This looks at the
verilog-tool setting and chooses your linter, coverage, simulator or
compiler. The ``verilog-linter`` is the default.

So, in your .emacs set reasonable defaults for all of them:

::

   (setq verilog-tool 'verilog-linter)
   (setq verilog-linter "vlint ...")
   (setq verilog-coverage "coverage ...)
   (setq verilog-simulator "verilator ... ")
   (setq verilog-compiler "verilator ... "

Then, if a file needs a special setting, override it at the bottom of each
Verilog file:

::

   // Local Variables:
   // verilog-linter:"vlint --local_options __FILE__"
   // End:


How do I go to the next error?
------------------------------

After using ``M-x compile``, or ``C-c C-s`` or ``M-x
verilog-auto-save-compile``, you'll get the ``*compile*`` buffer.  If
errors are printed there, you can jump to the line number the message
mentions with :literal:`C-x \`` or ``M-x next-error``. Or, place the cursor
over the error message and press return.

If this does not work with your tool, the tool probably does not produce
errors in a standard way. You'll need to tweak the ``verilog-error-regexp``
variable. This contains a regular expression which matches a error message
and returns the file and line number.


Language Support
================


Why does the signal "bit", "do", "const" get ignored?
-----------------------------------------------------

Your code is Verilog 2001 (or earlier) code; they're keywords in
SystemVerilog. You need to rename your signals.


Highlighting
============


Why do the simulator errors not highlight or goto-error correctly?
------------------------------------------------------------------

Emacs has a ``gnu`` rule which seems to override several simulator specific
error regexps. The solution is to disable the ``gnu`` rule.

If you're using a recent version of Emacs and ``M-x describe-variable
compilation-error-regexp-alist RET`` gives a simple list of words, then use
this:

::

   (add-hook 'verilog-mode-hook
            '(lambda ()
               (setq compilation-error-regexp-alist
                     (delete 'gnu compilation-error-regexp-alist))))

Otherwise a more brute force solution is to only use Verilog's errors:

::

   (setq-default compilation-error-regexp-alist
     (mapcar 'cdr verilog-error-regexp-emacs-alist))


Autos
=====


How do I start using the autos for the first time?
--------------------------------------------------

There are two easy ways to get started. The first is to convert an existing
file, and the second is covered in the next FAQ.

To convert an existing file to use the autos, use ``C-c C-z`` or ``M-x
verilog-inject-auto``. Then, expand them with ``C-c C-s`` or ``M-x
verilog-auto``.


What AUTOs should I use for a new file?
---------------------------------------

Here's a good template for a first file:

::

   module Modname (/*AUTOARG*/);

      // Input/output
      //input signal;      // Comment on signal

      // Automatics
      /*AUTOWIRE*/
      /*AUTOREG*/

      // Body
      //statements, etc go here.

      // Linting
      wire _unused_ok = &{1'b0,
                          // Put list of unused signals here
                          1'b0};
   endmodule

You'd then add cells using AUTOINST:

::

   InstModule instName
     (/*AUTOINST*/);

(The newline before the open parenthesis is suggested for larger
instantiations to make the lines look nicer.)


How do I make a Stub module?
----------------------------

A stub is a module with the same input/output as another module, but it
simply ignores all the inputs and drives zeros for outputs. This is often
useful for replacing modules that aren't needed for a simulation.

By using several Autos, the entire stub can be created for you:

::

   module ModnameStub (/*AUTOARG*/);
      /*AUTOINOUTPARAM("Modname")*/
      /*AUTOINOUTMODULE("Modname")*/

      /*AUTOWIRE*/
      /*AUTOREG*/

      /*AUTOTIEOFF*/

      wire _unused_ok = &{1'b0,
                          /*AUTOUNUSED*/
                          1'b0};
   endmodule

This presumes ``Modname.v`` already exists and you want to copy the entire
parameter and I/O list from it. Otherwise, remove the ``AUTOINOUTMODULE``
and add the I/O list yourself.

Note ``AUTOINOUTPARAM`` and ``AUTOINOUTMODULE`` also can take an optional
regexp to specify only a subset of directions or signal names.
Alternatively ``AUTOINOUTCOMP`` will create a complementary module; that is
one where inputs and outputs are swapped compared to the original.


How do I make a Testbench module?
---------------------------------

A testbench for the purposes of this question is a module which
instantiates another module for the purpose of testing it.

By using several autos, most of the hookup for the testbench are created
for you:

::

   module ModnameTest;

      /*AUTOWIRE*/
      /*AUTOREGINPUT*/

      InstModule instName
        (/*AUTOINST*/);

      //==== Stimulus
      // You then put code here to set all of the inputs to the DUT.
      // The autos have created registers for all of the needed signals.

      //==== Stimulus
      // You then put code here to check all of the outputs from the DUT.
      // The autos have created wires for all of the needed signals.

   endmodule


How do I use AUTORESET?
-----------------------

Many flops need reset, and it's a hassle to insure that you're resetting
all your signals. ``AUTORESET`` solves this by assuming the first if
statement in an always block is the reset term.

::

       always @(posedge clk or negedge reset_l) begin
           if (!reset_l) begin
               c <= 1;
               /*AUTORESET*/
               a <= 3'b0;
               b <= 1'b0;
           end
           else begin
               a <= in_a;
               b <= in_b;
               c <= in_c;
           end
       end
       always @* begin
           if (!reset_l) begin
               /*AUTORESET*/
               a_combo = 3'b0;
           end
           else begin
               a_combo = in_a;
           end
       end

Autoreset will automatically use ``<=`` or ``=`` based on the type of
assignments in the always block. You can also specify which signals should
be reset high by marking them active low with:

::

   // Local Variables:
   // verilog-active-low-regexp:("_l$")
   // End:


How do I use AUTORESET to insure I haven't missed a reset?
----------------------------------------------------------

You can use ``AUTORESET`` as described above to create your resets. Some
people prefer to reset manually, but want to catch if they forgot to reset
something and not have verilog-mode reset it for them. To do this, you can
use ``AUTORESET`` in a way in which if it creates any resets it will result
in a syntax error. This is as follows:

::

   always @(posedge clk or negedge reset_l) begin
       if (!reset_l) begin
           a <= 3'b0;
       end
       // Syntax error below if I forgot to reset something
       /*AUTORESET*/
       else begin
           a <= in_a;
           b <= in_b;
       end
   end


How do I call Lisp/Perl/Python/Ruby/whatever to do an AUTOs?
------------------------------------------------------------

Sometimes the built-in AUTOs aren't enough and you'd like to have
``verilog-auto`` also call your own lisp function or script.

``AUTOINSERTLISP`` will call the passed lisp code which can insert whatever
it likes. If you wish, that lisp code can even insert text from an external
program.

::

      /*AUTOINSERTLISP(insert "//hello")*/
      // Beginning of automatic insert lisp
      //hello
      // End of automatics"

      /*AUTOINSERTLISP(insert (shell-command-to-string "echo //hello"))*/
      // Beginning of automatic insert lisp
      //hello
      // End of automatics"

If you come up with some really cool extension using this that is also
fairly general, please consider contributing it back to Verilog-Mode, so it
can become a new AUTO for others to use and improve.


How do I update AUTOs from the command line?
--------------------------------------------

Use the following command:

::

   emacs --batch {filenames...} -f verilog-batch-auto

This will load the file, update the automatics, and re-save the file.  The
filenames need to be provided in a bottom-up order. For a utility to
determine the hierarchy of a design, see `vhier in Verilog-Perl
<https://www.veripool.org/verilog-perl>`__.

If your ``verilog-mode.el`` is not installed in a site-wide location, or
you suspect you are getting the wrong version, try specifing the exact path
to Verilog-Mode by adding ``-l {path}/verilog-mode.el`` after ``--batch``.

There are similar functions for deleting automatics using
``verilog-batch-delete-auto``, injecting automatics with
``verilog-batch-inject-auto``, and reindenting with
``verilog-batch-indent``.

Additional information is in Emacs under ``M-x describe-function
verilog-batch-auto``, etc.


How do I tell the AUTOs what directories my files are in?
---------------------------------------------------------

The cleanest way is to use standard Verilog-XL style flags at the bottom of
your Verilog file:

::

   // Local Variables:
   // verilog-library-flags:("-y incdir1/ -y incdir2/")
   // End:

You'll also often see files that do it in the way that old Verilog-Mode
versions required:

::

   // Local Variables:
   // verilog-library-directories:("." "dir1" "dir2" ...)
   // End:

If you find yourself adding the same flags to many files, you can create a
file with all of your include directories in it, then point Emacs to
it. All of your Verilog files would contain:

::

   // Local Variables:
   // verilog-library-flags:("-f ../../up_to_top/include/input.vc")
   // End:

Then input.vc contains the list of flags:

::

   -y incdir1
   -y incdir2

Note reading a file of command flags with the ``-f`` argument is also
supported by Verilog-XL, VCS, Verilator and most other Verilog related
tools. Thus you can write a single input.vc with all of the directories
specified and feed it to all of your tools.

Your ``input.vc`` can also use ``-f`` to reference other lists of flags.
You might want to use ``-F`` (upper-case F versus lower-case f) in this
case, as this makes the filenames relative to the including file, rather
than relative to the path of your original module.


How do I put AUTOLISP or other Lisp subroutines into a common library?
----------------------------------------------------------------------

If many modules use the same Lisp functions you may want them in a
library. One choice is to put them into your site-start file, however it's
often better to locate them in a directory near the Verilog code's
directory. An example is a my-module.el library with the following:

::

   (defun my-function (x) "Documentation"

   (provide `my-module)


How do I use environment variables for a filename, etc?
-------------------------------------------------------

Emacs only expands $'s when you ask it to do so by using
``substitute-in-file-name``. So, if you want to substitute $ENV into a
Local Variables in the bottom of your file, you need something like:

::

   // Local Variables:
   // eval:(setq verilog-library-directories (list (substitute-in-file-name "$W") ))
   // End:


In what order does Verilog-Mode search for modules?
---------------------------------------------------

It first searches the current file, then searches for the ``module.v`` in
each directory you provided in the order you provided. If the module isn't
found, it searches any libraries specified.

Generally it's a really really bad idea to have files with the same name in
different directories - But you probably know that. :)


How do I make defaults common for my entire design team?
--------------------------------------------------------

First, you may not want to. If you're distributing IP you're much better
off using ``Local Variables`` at the bottom of the file, and insuring all
of your file paths are relative. That way your clients can modify the AUTOs
without any tweaks.

That said, add the following to site-start.el in your global Emacs
distribution:

::

   (add-hook 'verilog-mode-hook '(lambda ()
                                   (setq verilog-auto-newline nil
                                         verilog-tab-always-indent nil
                                         verilog-auto-endcomments nil
                                         verilog-compiler "verilator "
                                         ;; etc, etc...
                                         )))

Alternatively, add the above to a group-start.el file and have all users
add a group-startup to their .emacs files:

::

   (when (file-exists-p "/path/to/group/group-start.el")
             (load-file "/path/to/group/group-start.el"))


How do I make a library of Lisp functions available to many modules?
--------------------------------------------------------------------

Extensive use of ``AUTO_LISP`` or Lisp ``AUTO_TEMPLATE`` lines will likely
lead to desiring a common library of AUTO related Lisp functions.  These
functions can be added to a group-start file (see above), but instead it's
often preferable to locate the library in a directory near the Verilog code
so it can be part of the same version control repository, etc.

For example, if there's my-vm-library.el with the following in it:

**my-vm-library.el.**

::

   (defun my-func (z) "Documentation: return z"
      z)
   ;; ...
   (provide `my-vm-library)

You may ensure that this package is loaded before any AUTO expansion by
adding to that module's file:

::

   /*AUTO_LISP(require 'my-vm-library "path/to/my-vm-library.el")*/

``my-func`` will then be available for ``AUTO_LISP`` or ``AUTO_TEMPLATES``
in that module.


How do I use AUTOs to migrate from defines to package localparams?
------------------------------------------------------------------

Projects that began in pre-SystemVerilog times typically have include files
with a large number of defines, e.g.:

::

   `define BUSID_FOO 8'h1
   `define BUSID_BAR 8'h2

In SystemVerilog, a better way to provide constants is with localparams (or
enums, which can be done similarly):

::

   package bus_pkg;
     localparam BUSID_FOO = 8'h1;
     localparam BUSID_BAR = 8'h2;
   endpackage

So code that uses these defines would have to change from
:literal:`\`BUSID_FOO` to ``bus_pkg::BUSID_FOO``. If this migration can't
happen all at once, AUTOS can be used to convert the localparams into
defines, so that the original code can still use :literal:`\`BUSID_FOO` as
follows:

::

   package bus_pkg;
     localparam BUSID_FOO = 8'h1;
     localparam BUSID_BAR = 8'h2;

     /*AUTOINSERTLISP(localparams-to-defs "BUSID_.*")*/
     // Beginning of automatic insert lisp
     `define BUSID_FOO  bus_pkg::BUSID_FOO // AUTO
     `define BUSID_BAR  bus_pkg::BUSID_BAR // AUTO
     // End of automatic insert lisp
   endpackage

This requires the following code at the bottom of the file, or the defun
being in some site-wide emacs-lisp file:

::

   /*
    Local Variables:
    eval:
      (defun localparams-to-defs (regexp)
       (let ((buf (current-buffer)) (ln "") (mod (verilog-read-module-name)))
         (save-excursion
          (goto-char (point-min))
          ;; No ":" in value as ##:## can't be a localparam; no "." as don't want floats
          (while (re-search-forward "^[ \t]*localparam[ \t]*\\([a-zA-Z_0-9]+\\)[ \t]+=" nil t)
            (let ((nm (match-string 1)))
               (when (string-match regexp nm)
                  (setq ln (concat ln "  `define " nm "  " mod "::" nm " // AUTO\n"))))))
        (save-excursion (set-buffer buf) (insert ln))))
    */


AUTO problems
=============


How do I use Verilog 2001 style port lists?
-------------------------------------------

Place ``AUTOINPUT``/``AUTOOUTPUT`` etc inside the module () parenthesis.


Does anything help declare non-instance wires and regs?
-------------------------------------------------------

No. ``AUTOWIRE`` and ``AUTOREG`` all assume that somewhere in your design
you've declared the signal. This is based on the belief that there should
be at least one point where you've declared the signal, and hopefully
documented it on the same line.


Why does Emacs keep asking "Process \`eval' or hook local variables in file?"
-----------------------------------------------------------------------------

You need to put in your global .emacs

::

   (setq enable-local-eval t)


Why doesn't Emacs save SystemVerilog .\* expanded instantiations to disk?
-------------------------------------------------------------------------

When you compute autos, Verilog-Mode will find any SystemVerilog .\* pins
and expand them into the ports, so that you can debug your code more
easily. By default it will then strip these inserted lines when saving the
file. This allows downstream tools to see the original SystemVerilog
syntax, and not require re-autoing when the submodules change.

If you want to save the expanded .\* pins, add to the Local Variables at
the bottom of your file.

::

   // Local Variables:
   // verilog-auto-star-save: t
   // End:


Why does AUTOSENSE add \`defines to the list?
---------------------------------------------

Call it a misfeature. :-)

Take the case where you have

::

   always @(/*AS*/)
      a = `b;

and ``b`` isn't defined. Is ``b`` a constant, or another signal? No way to
tell, it's safest to put it in the always. Granted, ``b`` could simply be
defined in the file. If so, you can tell Verilog-Mode to read defines in
the current file, and any \`includes using:

::

   // Local Variables:
   // eval:(verilog-read-defines)
   // eval:(verilog-read-includes)
   // End:

If you only use defines to represent constants, it's easier to just tell
Verilog-Mode that fact, and it will exclude all of them:

::

   // Local Variables:
   // verilog-auto-sense-defines-constant: t
   // End:


Why do the AUTOs treat SystemVerilog types as signals?
------------------------------------------------------

You need to tell Verilog-Mode how to recognize a type. All of your types
should match some convention, a ``_t`` suffix is probably the most
common. Then add to your files:

::

   // Local Variables:
   // verilog-typedef-regexp:"_t$"
   // End:


Why do the AUTOS ignore my ifdefs?
----------------------------------

Verilog-Mode simply pretends all :literal:`\`ifdefs` don't exist. This is
done because the permutations across multiple :literal:`\`ifdefs` quickly
results in code that's way too messy. The work around is all the AUTOs
ignore declarations that already exist, or are done before the AUTO itself.

For example:

::

      module foo (
   `ifdef something
           things,
   `endif
           /*AUTOARG*/);

      subfile subcell (
   `ifdef something
           .things,
   `endif
           /*AUTOINST*/);

If your selecting modules, see the next FAQ.

If your ifdefing around signals for only debug, there's rarely a need to do
so. Synthesis programs will remove irrelevant logic and ignore PLI calls.

An alternative technique to have a fake "mode" input wire, rather than a
ifdef or parameter. This also prevents having to lint or run other
translators in 2 different \`define modes, thus reducing bugs. This also
relies on your synthesis program's removal of irrelevant stuff. For example
a unneeded input and output can always be present, and instead:

::

           input         FPGA;
           input         fpga_only_input;
           output [31:0] fpga_only_output;

           if (fpga_only_input && FPGA) ...
           fpga_only_output = {32{FPGA}} & {value_for_output}.

Both will be stripped when ``FPGA==0``, and present when ``FPGA==1``.


How do I ifdef select between modules?
--------------------------------------

Often the purpose of an ifdef is to select between two alternate
implementations of a module with identical pinouts; perhaps a fast RAM and
a slow gate RAM. Your first attempt may be something similar to:

::

   `ifdef SUB_IS_A_FOOBAR
      foobar subcell (/*AUTOINST*/);
   `else
      foobiz subcell (/*AUTOINST*/);
   `endif

However, Verilog-mode ignores ifdefs. Assuming the pinout is the same you
can use the define to instead select which version:

::

   `ifdef SUB_IS_A_FOOBAR
    `define SUB_CELL  foobar
   `else
    `define SUB_CELL  foobiz
   `endif
      `SUB_CELL subcell (/*AUTOINST*/);

for this to work, you need to read the defines with the below at the bottom
of your file. Verilog-mode will use the last definition of ``SUB_CELL`` to
determine which one to pickup the pinlist from.

::

   // Local Variables:
   // eval:(verilog-read-defines)
   // End:


Can I put delays into AUTORESET?
--------------------------------

That is,

::

   /*AUTORESET*/
   foo <= #1 signal;

Do you really want to? You really shouldn't be using delays on your
assignments, as they aren't necessary to prevent races, and slows down
simulation. But if you must:

::

   // Local Variables:
   // verilog-assignment-delay: "#1 "
   // End:


Can AUTOASCIIENUM be changed to put translate_off pragmas around the code?
--------------------------------------------------------------------------

No. First of all, you'd be better off asking to wrap it :literal:`\`ifdef
synthesis` as that lets the tools pick which version of the code you want.

Second, there isn't one standard way that supports all tools.

Third, presuming you never use the value it generates at all (or only in
$display's) there's no reason to disable translation, as the synthesis tool
will rip it all out through its normal dead code optimization stage.


How do I remove outputs from AUTOOUTPUT?
----------------------------------------

Maybe you shouldn't be using ``AUTOOUTPUT``? Consider listing your outputs
manually; this insures your module's interface is documented and remains
constant, even if other lower modules change.

With that warning given, on to the solutions. You have four choices, the
last probably being the most used:

First, just ifdef fake outputs. Verilog-mode will see them, but no other
tool will care. This is cleanest for signals you can list one-by-one, and
are using Verilog 2001 port lists or when you want those listed to still
appear in a ``AUTOARG``.

::

   `ifdef NEVER
           output a_out;   // Fake out Verilog-mode
           output b_out;   // Fake out Verilog-mode
   `endif

Second alternative, simply create a fake module listing them as inputs.
Since Verilog-Mode will then see them as inputs to a submodule, it won't
output them.

::

   `ifdef NEVER
     fake fake (// Inputs
           .fake(a_out),
           .fake(b_out),
           );
   `endif

Third alternative, you can add them to
``verilog-auto-output-ignore-regexp`` using Local Variables:

::

   /*
      Local Variables:
      verilog-auto-output-ignore-regexp: ""
      eval:(setq verilog-auto-output-ignore-regexp (concat
      "^\\("
      "signal1_.*"
      "\\|signal2_.*"
      "\\)$"
      )))
      End:
   */

Finally, you can again use ``verilog-auto-output-ignore-regexp``, but use a
``AUTO_LISP``. This gets around a Emacs limitation of 3000 characters in a
``Local Variable`` statement.

::

   /*AUTO_LISP(setq verilog-auto-output-ignore-regexp
               (verilog-regexp-words `(
                  "q_single_reg_rddata_30"
                  )))*/

Here we've used ``verilog-regexp-words`` to convert a simple list of signal
names to a regular expression. If you prefer, you can just specify a
regular expression directly, perhaps as shown in the ``Local Variables``
alternative above.

Note ``AUTO_LISPs`` are evaluated during AUTO expansion multiple times
instead of only when the file is loaded into Emacs. Thus it's a bit slower,
but unlikely to be noticeable.


Why when expanding autos does Emacs ask "changed on disk; really edit the buffer?"
----------------------------------------------------------------------------------

This is part of normal Emacs lock prevention and isn't really part of
Verilog-mode, but is annoying since the AUTOs may need to rewrite many
files. You can disable this with the following:

::

   (defvar vm-old-revert-without-query nil)

   (add-hook 'verilog-before-auto-hook
             '(lambda ()
                (unless vm-old-revert-without-query
                  (setq vm-old-revert-without-query revert-without-query))
                (setq revert-without-query (list ".*"))))

   (add-hook 'verilog-after-auto-hook
             '(lambda ()
                (setq revert-without-query vm-old-revert-without-query)))

Let us know how this works for you and we will consider having an easier
way to set it.


Auto Instantiations and Related Issues
======================================


Why doesn't AUTOWIRE include the outputs from a submodule?
----------------------------------------------------------

``AUTOWIRE`` requires special comments in your instantiations to determine
the direction of pins. Add ``// Input``, ``// Output`` or ``// Inout``
comments inside each instantiation just before the relevant pins.

::

   foo foo (// Outputs
            .bfm_output(bfm_output),
            /*AUTOINST*/
            ....)


Why doesn't AUTOWIRE create correct widths for AUTO_TEMPLATE signals?
---------------------------------------------------------------------

You need to add [] to the name of the pin connection. This tells
Verilog-Mode to put the bit vectors into the instantiation, where they can
be read by ``AUTOWIRE``.

::

   /* InstModule AUTO_TEMPLATE (
       .signal   (signal[]),
      ); */


What does AUTOWIRE "can't merge into single bus" mean?
------------------------------------------------------

When there are multiple submodules that output the same signal,
``AUTOWIRE`` needs to merge those outputs into a single bus. For example,
if one instantiation outputs ``a[1:0]``, and the second instantiation
outputs ``a[3:2]``, then AUTOWIRE needs to declare ``wire a[3:0].``

This error message means that it cannot determine how to declare that
vector. Usually this is because you used parameters or something
complicated in the instantiations. You'll need to declare that wire
yourself.


How do I use AUTO_TEMPLATE to match multiple port names?
--------------------------------------------------------

Regexps can be used as port names. Furthermore they can be captured to be
used in the connection name. ``\1`` for the first captured regexp in
``\(...\)``, and ``\2`` for the second regexp, etc. Templates also allow a
short-hand whereby the first ``@`` means matches-any-number and put in
``\1``, that is, ``@`` is short-hand for ``\([0-9]+\)``.

::

   /* InstModule AUTO_TEMPLATE (
       .pin@_\(.*\) (wire\1of\2),
      ); */
   InstModule mod (
    .pin1_foo    (wire1offoo)   // Templated
   );


How do I use AUTO_TEMPLATE to tie off inputs to zero?
-----------------------------------------------------

To tie off a single port:

::

   /* InstModule AUTO_TEMPLATE (
       .\(.*\)_test ('0),
   ); */

If you don't want to use SystemVerilog's '0 you can use a Lisp format
template, and the Lisp variable ``vl-width``, which contains the width of
the port:

::

   /* InstModule AUTO_TEMPLATE (
       .\(.*\)_test ({@"vl-width"{1'b0}}),
   ); */

If you want verilog-mode to only tie off input signals, not output port
names that match the port regular expression, then use a Lisp format
template to match inputs:

::

   /* InstModule AUTO_TEMPLATE (
       .\(.*\)_test (@"(if (equal vl-dir \\"input\\") \\"'0\\" \\"\\")"),
   ); */


How do I use AUTO_TEMPLATE to lower case all signals?
-----------------------------------------------------

Use a lisp expression, and the lisp function "downcase".

::

   /* InstModule AUTO_TEMPLATE (
      .\(.*\) (@"(downcase vl-name)"[]),
   */

If you're trying the reverse, namely to upcase your signal names, did you
consider lower case is more readable by 15% or so than all upper case?


How do I use AUTO_TEMPLATE to include the instantiation name for pin?
---------------------------------------------------------------------

Yet another lisp expression:

::

   /* InstModule AUTO_TEMPLATE (
        .a(@"vl-cell-name"_in[]),
        .b(@"vl-cell-name"_out[]),
        );*/
   InstModule u_a0 (/*AUTOINST*/
        // Inouts
        .a (u_a0_in[bitsa:0]),      // Templated
        .b (u_a0_out[bitsb:0]));    // Templated
   InstModule u_a1 (/*AUTOINST*/
        // Inouts
        .a (u_a1_in[bitsa:0]),      // Templated
        .b (u_a1_out[bitsb:0]));    // Templated

Oh, but what if I didn't want the ``u_``?

::

   /* InstModule AUTO_TEMPLATE (
        .a(@"(substring vl-cell-name 2)"_in[]),
        .b(@"(substring vl-cell-name 2)"_out[])
        );*/
   InstModule u_a0 (/*AUTOINST*/
      // Inouts
      .a   (a0_in[bitsa:0]),        // Templated
      .b   (a0_out[bitsb:0]));      // Templated

Substring is very useful in templates. All of your cell names need to be
the same length however. Often you can simply pad the names by adding
zeros, for example use :literal:`\`u_00 ... u_15`, rather than ``u_0
... u_15``.


How do I have AUTO_TEMPLATE use the second number in a instance name?
---------------------------------------------------------------------

The standard ``@`` sign in a template by default returns the first number
in a instance name, so if you want a earlier number, you have three main
choices.

If you only need the second digit, you can define the @ sign to come from
the second digits in the module:

::

   /* InstModule AUTO_TEMPLATE "\([0-9]+\)$" (
                                .a (in_@),
   */

Note this pattern works because it doesn't have to be at the beginning of
the cell name; there's no ``^`` in the regexp to bind to the start of the
string being matched.

Next easiest is to use ``@"(substring vl-cell-name ...)`` to extract the
relevant digits. See the examples above.

The most flexible is to define your own function to do the relevant
extraction, then call it. For example:

::

   /* AUTO_LISP(defun getparam2 (strg)
       (string-match "[^0-9]*[0-9]+[^0-9]*\\([0-9]+\\)" strg)
       (match-string 1 strg)) */
   /* InstModule AUTO_TEMPLATE (
       .in (@"(getparam2 vl-cell-name)"),
       );
       */


How do I use AUTO_TEMPLATE to connect bytes to instances?
---------------------------------------------------------

This is for when you want the first instance to get ``a[7:0]``, the second
``a[15:8]``, and so on.

Use a Lisp template and a little math.

::

   /* InstModule AUTO_TEMPLATE (
        .a(@in[@"(+ (* 8 @) 7)":@"(* 8 @)"]),
        );*/

   InstModule u_a0 (/*AUTOINST*/
        .a (in[7:0]));      // Templated
   InstModule u_a1 (/*AUTOINST*/
        .a (in[15:8]));     // Templated
   InstModule u_a2 (/*AUTOINST*/
        .a (in[23:16]));    // Templated
   InstModule u_a3 (/*AUTOINST*/
        .a (in[31:24]));    // Templated


How do I propagate parameters in an instantiation?
--------------------------------------------------

``AUTOINSTPARAM`` is very similar to ``AUTOINST``, but it pulls parameters
up using Verilog-2001 (and later) syntax:

::

   module InstModule;
      parameter PARAM1 = 1;
      parameter PARAM2 = 2;
   endmodule

   module ModnameTest;
      InstModule #(/*AUTOINSTPARAM*/
            // Parameters
            .PARAM1  (PARAM1),
            .PARAM2  (PARAM2))
        instName
          (/*AUTOINST*/
           ...);

See also the next FAQ.


How do I propagate parameters to pin connections?
-------------------------------------------------

If you set ``verilog-auto-inst-param-value``, a AUTOINST cell that sets a
Verilog-2001 style parameter will have that parameter's value substituted
into the instantiation:

::

   module InstModule;
      # (parameter WIDTH = 32)
      (output wire [WIDTH-1:0] out);
   endmodule

   module ModnameTest;
      InstModule #(.WIDTH(16))
        instName
          (/*AUTOINST*/
           // Outputs
           .out   (out[15:0]));
   endmodule

   // Local Variables:
   // verilog-auto-inst-param-value:t
   // End:

Contrast this with the default:

::

   module ModnameTest;
      InstModule #(.WIDTH(16))
        instName
          (/*AUTOINST*/
           // Outputs
           .out   (out[WIDTH-1:0]));
   endmodule

   // Local Variables:
   // verilog-auto-inst-param-value:nil
   // End:


How do I use AUTOINST with Interfaces?
--------------------------------------

``AUTOINST`` will hook interfaces up similar to how normal inputs and
outputs connect.

::

   interface svi;
      logic       enable;
      modport master (input enable);
   endinterface

   module InstModule
     (input      clk,
      svi.master svi_modport,
      svi        svi_nomodport);
   endmodule

   module top;
      InstModule instName
        (/*AUTOINST*/
         // Interfaces
         .svi_modport         (svi_modport.master),
         .svi_nomodport       (svi_nomodport),
         // Inputs
         .clk                 (clk));
   endmodule

You can also use ``AUTOINOUTMODULE`` and ``AUTOINOUTCOMP`` with interfaced
ports:

::

   module autoinst_interface
     (/*AUTOINOUTMODULE("autoinst_interface_sub")*/
      // Beginning of automatic in/out/inouts (from specific module)
      input      clk,
      svi.master svi_modport,
      svi        svi_nomodport
      // End of automatics
      );
   endmodule


How do I use AUTOINST with Synplify syn_prune attributes?
---------------------------------------------------------

Synplify documentation suggests placing attributes just before the final
semicolon of instance names. Instead place the comment before the list of
ports, which works just as well, and has the additional advantage of being
close to the instantiated module name (instead of potentially pages lower
if there's many pins.) Synplify has been notified of this issue, and is
likely to change their documentation.

::

   InstModule u_a0 /*synthesis syn_noprune=1*/
     (/*AUTOINST*/
        .a (a));


How do I use AUTOINST to tie off unused ports?
----------------------------------------------

Configure your lint program to ignore signals with a certain naming, such
as those with ``unused`` in the name, then use ``AUTO_TEMPLATE`` to make a
unique name for each port.

::

   /* InstModule AUTO_TEMPLATE (
      .out_signal   (unused__@"vl-cell-name"__@"vl-name"[]),   // [] is dropped for single-bit widths
      .out_bus      (unused__@"vl-cell-name"__@"vl-name"[]),   // [] expands to bus range
      .in_signal    ({@"vl-width"{1'b0}}),                     // tie off to zeros
      .in_bus       ({@"vl-width"{1'b1}}),                     // tie off to ones
      .in_bus_SV    ('0),                                      // tie off - if using SystemVerilog
   ); */
   InstModule instname
     (/*AUTOINST*/
      // Outputs
      .out_signal   (unused__instname__out_signal),
      .out_bus      (unused__instname__out_bus[63:0]),
      // Inputs
      .in_signal    ({1{1'b0}}),
      .in_bus       ({64{1'b1}}),
      .in_bus_SV    ('0));


How do I use AUTOINST to connect a daisy-chain between modules?
---------------------------------------------------------------

Solution one uses a local pin override to specify the signal the first
module gets, then chains up the rest:

::

     /* InstName AUTO_TEMPLATE (
      .a            (z@"(number-to-string(- @ 1))"),
      .z            (z@)); */

     InstName sub0 (// Inputs
                    .a (first),
                    /*AUTOINST*/
                    .z (z0));     // Templated

     InstName sub1 (/*AUTOINST*/
                    .a (z0),      // Templated
                    .z (z1));     // Templated

Solution two does it all in a template, the ``.a(first)`` is no longer
required, which is useful if a regular expression is to be used with the
port name:

::

   /* InstModule AUTO_TEMPLATE (
    .a            (@"(if (= @ 0)\"first\" (concat \"z\" (number-to-string(- @ 1))))"),
    .z            (z@));*/
