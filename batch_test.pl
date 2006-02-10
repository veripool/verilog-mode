#!/usr/bin/perl -w
# $Id:$

my $tmpdir = "e";

my @tests = qw(
	       autoinst_lopaz.v
	       autoinout.v
	       );

my @tests_args;
foreach my $test (@tests) {
    run("/bin/cp tests/$test e/$test");
    push @tests_args, "e/$test";
}

run("emacs --batch --no-site-file -l $tmpdir/verilog-mode.elc"
    ." -f verilog-batch-auto"
    ." ".join(' ',@tests_args)
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
