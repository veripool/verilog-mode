#!/usr/bin/perl -w
# $Id$

my $tmpdir = "e";

my @tests = map { s!^.*/!!; $_;} glob("tests_batch_ok/*");

my @tests_args;
foreach my $test (@tests) {
    run("/bin/cp tests/$test e/$test");
    push @tests_args, "e/$test";
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

foreach my $test (@tests) {
    run("diff tests_batch_ok/$test e/$test");
}

#######################################################################

sub run {
    # Run a system command, check errors
    my $command = shift;
    print "\t$command\n";
    system "$command";
    my $status = $?;
    ($status == 0) or die "%Error: Command Failed $command, stopped";
}
