#!/usr/local/bin/perl
unlink("verilog-mode.el.gz", "uu", "log");
system("gzip -c9 verilog-mode.el | uuencode verilog-mode.el.gz > uu");
system("cvs log verilog-mode.el > log");
open(LOG,"<log");
while(<LOG>) {
  if (/^head: ([\d\.]+)$/) {
    $rev = $1;
  }
  last if (/^description:$/);
}
open(O,">emacs-version.h");
open(C,">ChangeLog.txt");
print O <<"X";
<define-tag emacs-vid>
$rev
</define-tag>
X
close(O);

open(O,">uuencoded_verilog-mode");
print O "-------------------------------------------------------------------\n";
print O "|         Here is version $rev of verilog-mode for emacs!         |\n";
open(IO, "<README");
while (<IO>){
  print O $_;
}
print O "\nLast few changes to the verilog-mode:\n";
while(<LOG>) {
  $log++ if (/^----------------------------$/);
  print C $_;
  last if ($log > 10);
  print O $_;
}
while(<LOG>) {
  print C $_;
}
close(LOG);
print O "\n\n";
open(U,"<uu");
while(<U>) {
  print O $_;
}
close(U);
close(O);
unlink("verilog-mode.el.gz", "uu", "log");
