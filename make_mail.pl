#!/usr/local/bin/perl
$owner = "mac";
$destination = "<verilog-mode-list\@webnexus.com>";
$verilog =  "/home/mac/Verilog-Mode/verilog-mode/verilog-mode/mmencoded_verilog-mode";

open(LOG,"<log");
while(<LOG>) {
  if (/^head: ([\d\.]+)$/) {
    $rev = $1;
  }
  last if (/^description:$/);
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
