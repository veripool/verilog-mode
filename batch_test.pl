#!/usr/bin/perl -w
# DESCRIPTION: Run batch tests, as part of "make test"
#
# Copyright 2008-2021 by Michael McNamara and Wilson Snyder.  This package
# is free software; you can redistribute it and/or modify it under the
# terms of either the GNU Lesser General Public License or the Perl
# Artistic License.

my $tmpdir = "e";

my @tests = map { s!^.*/!!; $_;} glob("tests_batch_ok/*");

my @tests_args;
foreach my $test (@tests) {
    run("/bin/cp tests/$test e/b/$test");
    push @tests_args, "e/b/$test";
}

my $Emacs = $ENV{EMACS} || "emacs";

run("$Emacs --version"
    );

run("$Emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." ".join(' ',@tests_args)
    ." -f verilog-batch-delete-auto"
    );

run("$Emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." ".join(' ',@tests_args)
    ." -f verilog-batch-auto"
    );

run("$Emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." e/b/autoinst_lopaz.v"
    ." -f verilog-batch-diff-auto"
    );

run("$Emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." e/b/autoinst_star.v"
    ." -f verilog-batch-diff-auto"
    );

run("$Emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." ".join(' ',@tests_args)
    ." -f verilog-batch-indent"
    );

foreach my $test (@tests) {
    run("diff tests_batch_ok/$test e/b/$test");
}

run("$Emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." ".join(' ',@tests_args)
    ." -f verilog-batch-delete-trailing-whitespace"
    );

run("$Emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_prof.el"
    );

#######################################################################

sub run {
    # Run a system command, check errors
    my $command = shift;
    print "\t$command\n";
    system "$command";
    my $status = $?;
    ($status == 0) or die "%Error: Command Failed $command, stopped";
}
