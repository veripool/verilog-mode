#!/usr/bin/perl
$owner = "mac";
$destination = "mac\@verilog.com";
$verilog =  "/home/mac/development/www.verilog.com/src/data/mmencoded_verilog-mode";

if ( -d ".svn") {
    open(LOG,"<log");
    while(<LOG>) {
	if (/^r([\d\.]+)/) {
	    $rev = $1;
	    last;
	}
    }
} else {
    open(LOG,"<log");
    while(<LOG>) {
	if (/^head: ([\d\.]+)$/) {
	    $rev = $1;
	}
	last if (/^description:$/);
    }
}
open(VM, "< $verilog") || die "Can not open $verilog\n";
open(SM, "|/usr/lib/sendmail -bm -f $owner -F \"Mike McNamara\" -t");

# $destination = "mac\@verilog.com";
# open(SM, "> mail.test");

print SM "To: $destination\nReply-To: mac\@verilog.com\nBCC: mac\@verilog.com\nSubject: SUBSCRIPTION: Emacs Verilog-mode $rev\n";

while(<VM>) {
  print SM $_;
}
close(SM) || die "mailing dies with error: $!\n";
close(VM);
