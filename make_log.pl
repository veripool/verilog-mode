#!/usr/bin/perl

unlink("log");
$attach_name = "verilog-mode.el.gz";
$encoded_data = `gzip -c9 verilog-mode.el | mmencode `;
if ( -d ".svn") {
    system("svn log verilog-mode.el > log");
    open(LOG,"<log");
    while(<LOG>) {
	if (/^r([\d\.]+)/) {
	    $rev = $1;
	    last;
	}
    }

} else {
    system("cvs log verilog-mode.el > log");
    open(LOG,"<log");
    while(<LOG>) {
	if (/^head: ([\d\.]+)$/) {
	    $rev = $1;
	}
	last if (/^description:$/);
    }
}
open(O,">emacs-version.h");
open(C,">ChangeLog.txt");
$release_date = `date +"%D"`;
print O <<"X";
<define-tag emacs-vid>
$rev
</define-tag>
<define-tag emacs-release-date>
$release_date
</define-tag>
X
close(O);

open(O,">mmencoded_verilog-mode");
print O <<"XX";
MIME-version: 1.0
Content-type: multipart/mixed; boundary="Message-Boundary"
Content-transfer-encoding: 7BIT
X-attachments: verilog-mode.el.gz

--Message-Boundary
Content-type: text/plain; charset=US-ASCII
Content-transfer-encoding: 7BIT
Content-description: Mail message body


+----------------------------------------------------------------+
|         Here is version $rev of verilog-mode for emacs!         |
+----------------------------------------------------------------+
XX
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
print O <<"XX";

--Message-Boundary
Content-type: application/octet-stream; name="$attach_name"
Content-Transfer-Encoding: base64
Content-disposition: attachment; filename="$attach_name"

$encoded_data
--Message-Boundary--
XX
close(O);
unlink("log");
