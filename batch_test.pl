#!/usr/bin/perl -w
# $Id$

my $tmpdir = "e";

my @tests = map { s!^.*/!!; $_;} glob("tests_batch_ok/*");

my @tests_args;
foreach my $test (@tests) {
    run("/bin/cp tests/$test e/b/$test");
    push @tests_args, "e/b/$test";
}

run("emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." ".join(' ',@tests_args)
    ." -f verilog-batch-delete-auto"
    );

run("emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." ".join(' ',@tests_args)
    ." -f verilog-batch-auto"
    );

run("emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." e/b/autoinst_lopaz.v"
    ." -f verilog-batch-diff-auto"
    );

run("emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." e/b/autoinst_star.v"
    ." -f verilog-batch-diff-auto"
    );

run("emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -l ./batch_test.el"
    ." ".join(' ',@tests_args)
    ." -f verilog-batch-indent"
    );

foreach my $test (@tests) {
    run("diff tests_batch_ok/$test e/b/$test");
}

run("emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
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
