#!/usr/bin/perl -w
# DESCRIPTION: Query's git to get version number
######################################################################
#
# Copyright 2005-2021 by Wilson Snyder.  This is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
######################################################################

my $dir = $ARGV[0]; defined $dir or die "%Error: No directory argument,";
chdir $dir;
my $file = $ARGV[1]; defined $file or die "%Error: No file argument,";

my $ver = 'UNKNOWN_VER';
my $data = `git log --pretty=format:'%ad' --date=short -1 $file`;
if ($data =~ /(^20.*)/i) {
    $ver = $1;
}
(my $verdot = $ver) =~ s/-/./g;

my $rev = 'UNKNOWN_REV';
$data = `git log --pretty=format:'%h' --date=short -1 $file`;
if ($data =~ /(^[0-9a-f]+)/i) {
    $rev = $1;
}
my $revdot = sprintf("%09d", hex $rev);

$data = `git status $file`;
if ($data =~ /Changed but not updated/i
    || $data =~ /Changes to be committed/i) {
    $rev .= "-mod";
}

# Filter the code
my $wholefile = join('',<STDIN>);
$wholefile =~ s/__VMVERSION__/$ver/mg;
$wholefile =~ s/__VMVERSIONDOT__/$verdot/mg;
$wholefile =~ s/__VMREVISION__/$rev/mg;
$wholefile =~ s/__VMREVISIONDOT__/$revdot/mg;
$wholefile =~ s/__VMPACKAGER__/vpo/mg;
print $wholefile;

# Die after the print, so at least the header has good contents
$rev =~ /UNKNOWN/ and warn "%Warning: No git revision found,";
