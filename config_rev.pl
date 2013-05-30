#!/usr/bin/perl -w
# DESCRIPTION: Query's git to get version number
######################################################################
#
# Copyright 2005-2013 by Wilson Snyder.  This is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
######################################################################

my $dir = $ARGV[0]; defined $dir or die "%Error: No directory argument,";
chdir $dir;
my $file = $ARGV[1]; defined $file or die "%Error: No file argument,";

my $rev = 'UNKNOWN_REV';
my $data = `git log --pretty=format:'%ad-%h' --date=short -1 $file`;
if ($data =~ /(^20.*)/i) {
    $rev = $1;
}

$data = `git status $file`;
if ($data =~ /Changed but not updated/i
    || $data =~ /Changes to be committed/i) {
    $rev .= "-mod";
}

# Filter the code
my $wholefile = join('',<STDIN>);
$wholefile =~ s/__VMVERSION__-__VMREVISION__/$rev/mg;
$wholefile =~ s/__VMPACKAGER__/vpo/mg;
print $wholefile;

# Die after the print, so at least the header has good contents
$rev =~ /UNKNOWN/ and warn "%Warning: No git revision found,";
