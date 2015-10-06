#!/usr/bin/perl
#============================================================= -*-perl-*-
#
# BackupPC_copyPcPool.pl: Reliably & efficiently copy pool and pc tree
#
# DESCRIPTION
#   See below for detailed description of what it does and how it works
#   
# AUTHOR
#   Jeff Kosowsky
#
# COPYRIGHT
#   Copyright (C) 2011-2013  Jeff Kosowsky
#
#   This program is free software; you can redistribute it and/or modify
#   it under the terms of the GNU General Public License as published by
#   the Free Software Foundation; either version 2 of the License, or
#   (at your option) any later version.
#
#   This program is distributed in the hope that it will be useful,
#   but WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#   GNU General Public License for more details.
#
#   You should have received a copy of the GNU General Public License
#   along with this program; if not, write to the Free Software
#   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
#
#========================================================================
#
# Version 0.2.3, April 2013
#
# CHANGELOG:
# 0.1.1 (Feb 2011)
# 0.1.2 (May 2011)
# 0.1.3 (Sep 2011)
# 0.1.4 (Jan 2013) Added options & error checking to set backuppc uid & guid
#                  when not available from passwd & group files, respectively
# 0.2.0 (Feb 2013) Initial release of new version using full in-memory I-node
#                  (hash) caching rather than I-node pooling via file system
#                  tree
# 0.2.1 (Feb 2013) Added packed option for I-node cache hash index & values
#                  Added md5sum output option
# 0.2.2, 0.2.3 (Apr 2013) Minor bug fix
#========================================================================
#
# DESCRIPTION
#
# 1. The program first recurses through the pool/cpool to create a
# perl hash cache (%InodeCache) indexed by inode of all the pool
# entries. This subsequently allow for rapid lookup and association of
# each linked pc file with the corresponding stored pool
# file. Optionally, the cache can be written out to a file as a list
# of "<inode> <pool mdsum>" pairs. This inode chache file can then be
# read in rapidly to populate the chache on subsequent runs, assuming
# the pool hasn't changed in the interim.
#
# 2. The program then runs through the pc tree (or a designated
# subtree thereof) to create a single long list of all of the
# directories, hard links, and zero-length files
# For hard links, the entry is:
#     <path-to-pool-file> <path-to-pc-file>
# For directories, the entry is:
#     D <owner> <group> <mode> <mtime> <path-to-directory>
# For zero-length files, the entry is:
#     Z <owner> <group> <mode> <mtime> <path-to-file>
# For 'errors' (e.g., non-linked, non-zero length files), the entry is:
#     X <owner> <group> <mode> <mtime> <path-to-file>
# Comments can be indicated by:
#     #

# Note: all paths are relative to TopDir

# Any (non-zero length) pc files that are not linked (i.e. only one
# hard link) or that are not found in the InodeCache may optionally be
# corrected and linked to the pool and if this results in a new pool
# entry then that entry is added to the InoceCache too. Files that are
# not corrected are listed for separate examination and manual
# correction or backup.

# The output consists of 3 files:

# <outfile>.links   is the file consisting of the list of links,
#                   directories and zero-length files described above

# <outfile>.nopool  is a listing of the normal top-level log and info
#                   files that are not linked and need to be copied
#                   over directly

# <outfile>.nolinks is a listing of the non-linked, non-zero length
#                   files that either couldn't be linked or that you
#                   decided not to link
#

# If the --Writecache|-W option is set, a 4th output file is generated:

# <outfile>.icache  is a 2 column listing consisting of
#                   <inode number> <pool file name> pairs. 
#                    If the --writecache|-W option is repeated, then a
#                    3rd column is added consisting of the md5sum of
#                    the (uncompressed) contents of the pool file.
#                    One can then check for pool dups by running:
#                        sort -k 3 <outfile>.icache  | uniq -f 2 -D

# NOTE: Backuppc on the source machine should be disabled (or a
# static snapshot used) during the entire backup process

# 3. Restoring then consists of the following steps:

#    A. Copy over the pool/cpool any way you like, including
#       rsync but without having to worry about hard links

#    B. Copy over the non-pooled files (<outfile>.nopool) any way you want,
#       e.g., rsync, tar, etc.

#    C. Run this program again using the -r|--restore flag and the
#       <outfile>.nolinks as the input

#    D. Optionally copy over the non-linked files in <outfile>.nolinks

# NOTE: Backuppc on the target machine should be disabled (or a
# snapshot used) during the entire restore process

# Selected features:
#   --gzip|-g      flag creates compressed output/input
#   --stdio        writes/reads to stdio allowing you to pipe the backup
#                  stage directly into the restore stage
#   --fixlinks|-f  fixes any missing/broken pc links
#   --topdir|-t    allows setting of alternative topdir
#   --dryrun|-d    doesn't make any changes to pool or pc tree
#   --verbose|-v   verbosity (repeat for higher verbosity)
#
#========================================================================

use strict;
use warnings;
use File::Path;
use File::Glob ':glob';
use Getopt::Long qw(:config no_ignore_case bundling);
use Fcntl;  #Required for RW I/O masks
use Switch;

use lib "/usr/share/BackupPC/lib";
use BackupPC::FileZIO;
use BackupPC::Lib;
use BackupPC::jLib v0.4.2;  # Requires version >= 0.4.2
use BackupPC::Attrib qw(:all);

no  utf8;

#use Data::Dumper; #JJK-DEBUG
#use Devel::Size qw(size total_size); #JJK-DEBUG

select(STDERR); #Auto-flush (i.e., unbuffer) STDERR
$| = 1;
select(STDOUT);

#Variables
my $bpc = BackupPC::Lib->new or die "BackupPC::Lib->new failed\n";	
my $md5 = Digest::MD5->new;
my $attr; #Re-bless for each backup since may have different compress level
my $MaxLinks = $bpc->{Conf}{HardLinkMax};
my $CREATMASK = O_WRONLY|O_CREAT|O_TRUNC;
my %InodeCache=(); #Cache for saving pool/cpool inodes
my @nonpooled = ();
my @backups = ();
my @compresslvls=(); #Pool to use for each backup;
my ($compresslvl, $ptype);

my $backuppcuser = $bpc->{Conf}{BackupPCUser}; #User name
my $backuppcgroup = $bpc->{Conf}{BackupPCUser}; #Assumed to be same as user

my $directories = 0;
my $totfiles = 0; #Total of next 6 variables
my $zerolengthfiles = 0;
my $existinglink_pcfiles = 0;
my $fixedlink_pcfiles = 0;
my $unlinkable_pcfiles = 0;
my $unlinked_pcfiles = 0;
my $unlinked_nonpcfiles = 0;
my $unlinked_files = 0; #Total of above three
my $missing_attribs = 0;

#GetOptions defaults:
my $cleanpool;
$dryrun=0;  #Global variable defined in jLib.pm (do not use 'my') #JJK-DEBUG
#$dryrun=1; #Set to 1 to make dry run only
my $fixlinks=0;
my $Force;
my $gzip;
my $giddef = my $giddef_def = getgrnam($backuppcuser); #GID
$giddef_def = "<unavailable>" unless defined $giddef_def;
my $outfile;
my $Overwrite;
my $Pack;
my $pool = my $pool_def = 'both';
my $restore;
my $Readcache;
my $Skip;
my $stdio;
my $TopDir = my	$TopDir_def = $bpc->{TopDir};
my $uiddef = my $uiddef_def = getpwnam($backuppcgroup); #UID
$uiddef_def = "<unavailable>" unless defined $uiddef_def;
my $verbose = my $verbose_def = 2;
my $noverbose;
my $Writecache = 0;;

usage() unless( 
	GetOptions( 
		"cleanpool|c"   => \$cleanpool, #Remove orphan pool entries
		"dryrun|d!"     => \$dryrun,    #1=dry run
		"fixlinks|f"    => \$fixlinks,  #Fix unlinked/broken pc files
		"Force|F"       => \$Force,     #Override stuff...
		"gid|G=i"       => \$giddef,    #default gid if not in group file
		"gzip|g"        => \$gzip,      #Compress files
		"outfile|o=s"   => \$outfile,   #Output file (required)
		"Overwrite|O"   => \$Overwrite, #OVERWRITES existing files/dirs (restore)
		"pool|p=s"      => \$pool,      #Pool (pool|cpool|both)
		"Pack|P"        => \$Pack,      #Pack the InodeCache hash
		"restore|r"     => \$restore,   #Restore rather than backup
		"Readcache|R=s" => \$Readcache, #Read InodeCache from file
		"Skip|S"        => \$Skip,      #Skip existing backups (restore)
		"stdio|s"       => \$stdio,     #Print/read to/from stdout/stdin
		"topdir|t=s"    => \$TopDir,    #Location of TopDir
		"uid|U=i"       => \$uiddef,    #default gid if not in group file
		"verbose|v+"    => \$verbose,   #Verbosity (repeats allowed)
		"noverbose"     => \$noverbose, #Shut off all verbosity
		"Writecache|W+" => \$Writecache,#Write InodeCache out to file
		"help|h"        => \&usage,
	));

if($restore) {
	usage() if $cleanpool || $fixlinks || $outfile ||
		$Readcache || $Writecache ||
		(!$stdio && @ARGV < 1);
} else {
	usage() if ! defined($outfile) ||  ($pool !~ /^(pool|cpool|both)$/) ||
		($Readcache && $Writecache) || $Overwrite;
}

$verbose = 0 if $noverbose;
my $DRYRUN = $dryrun ? "**DRY-RUN** " : "";

die "Error: 'backuppc' not found in password file, so must enter default UID on commandline (--uid|-U option)...\n" unless defined $uiddef;
die "Error: 'backuppc' not found in group file, so must enter default GID on commandline (--gid|-G option)...\n" unless defined $giddef;
my (%USERcache, %GROUPcache, %UIDcache, %GIDcache);
$UIDcache{$uiddef} = $backuppcuser;
$GIDcache{$uiddef} = $backuppcgroup;
$USERcache{$backuppcuser} = $uiddef;
$GROUPcache{$backuppcgroup} = $giddef;

############################################################################
if($TopDir ne $TopDir_def) {
	#NOTE: if we are not using the TopDir in the config file, then we
	# need to manually override the settings of BackupPC::Lib->new
	# which *doesn't* allow you to set TopDir (even though it seems so
	# from the function definition, it gets overwritten later when the
	# config file is read)
	$TopDir =~ s|//*|/|g; #Remove any lurking double slashes
	$TopDir =~ s|/*$||g; #Remove trailing slash
	$bpc->{TopDir} = $TopDir;
	$bpc->{Conf}{TopDir} = $TopDir;

	$bpc->{storage}->setPaths({TopDir => $TopDir});
	$bpc->{PoolDir}  = "$bpc->{TopDir}/pool";
	$bpc->{CPoolDir} = "$bpc->{TopDir}/cpool";
}

%Conf   = $bpc->Conf(); #Global variable defined in jLib.pm (do not use 'my')
#############################################################################
#By convention for the rest of this program, we will assume that all
#directory variables have a trailing "/". This should save us some
#efficiency in terms of not having to always add back the slash.
$TopDir .= "/"; $TopDir =~ s|//*|/|g;
my $pcdir = 'pc/';

die "TopDir = '$TopDir' doesn't exist!\n" unless -d $TopDir;
die "TopDir = '$TopDir' doesn't look like a valid TopDir!\n" 
	unless -d "$TopDir/pool" && -d "$TopDir/cpool" && -d "$TopDir/${pcdir}";

system("$bpc->{InstallDir}/bin/BackupPC_serverMesg status jobs >/dev/null 2>&1");
unless(($? >>8) == 1) {
	die "Dangerous to run when BackupPC is running!!! (use '--Force' to override)\n"
		unless $Force ||
		(stat("$TopDir/"))[0] . "." . (stat(_))[1] !=
		(stat("$TopDir_def/"))[0] . "." . (stat(_))[1]; #different fs & inode
	warn "WARNING: May be dangerous to run when BackupPC is running!!!\n"; 
    #Warn but don't die if *appear* to be in different TopDir
}

############################################################################
if(defined $restore) {
	do_restore(@ARGV);
	exit; #DONE
}
############################################################################
#Open files for reading/writing 
#NOTE: do before chdir to TopDir
my $sfx = $gzip ? ".gz" : "";
my $linksfile = "${outfile}.links${sfx}";
my $nopoolfile = "${outfile}.nopool${sfx}";
my $nolinksfile = "${outfile}.nolinks${sfx}";

die "ERROR: '$linksfile' already exists!\n" if !$stdio && -e $linksfile;
die "ERROR: '$nopoolfile' already exists!\n" if -e $nopoolfile;
die "ERROR: '$nolinksfile' already exists!\n" if -e $nolinksfile;

my $outpipe = $gzip ? "| gzip > " : "> ";

if($stdio) {
	open(LINKS, $gzip ? "| gzip -f" : ">&STDOUT"); #Redirect LINKS to STDOUT
} else {
	open(LINKS,  $outpipe . $linksfile)
		or die "ERROR: Can't open '$linksfile' for writing!($!)\n";
}

open(NOPOOL, $outpipe . $nopoolfile)
	or die "ERROR: Can't open '$nopoolfile' for writing!($!)\n";
open(NOLINKS, $outpipe . $nolinksfile)
	or die "ERROR: Can't open '$nolinksfile' for writing!($!)\n";

my ($read_Icache, $write_Icache);
if($Pack) { #Pack InodeCache entries
	$read_Icache  = \&read_Icache_pack;
	$write_Icache = \&write_Icache_pack;
} else { #Don't pack InodeCache entries
	$read_Icache  = \&read_Icache_nopack;
	$write_Icache = \&write_Icache_nopack;
}

if($Readcache) { #Read in existing InodeCache from file
	open(RCACHE, $gzip ? "/bin/zcat $Readcache |" : "< $Readcache") or
		die "ERROR: Can't open '$Readcache' for reading!($!)\n";
} elsif($Writecache) {
	my $wcachefile = "${outfile}.icache${sfx}";
	die "ERROR: '$wcachefile' already exists!\n" if -e $wcachefile;
	open(WCACHE, $outpipe . $wcachefile)
		or die "ERROR: Can't open '$wcachefile' for writing!($!)\n";
}

############################################################################
chdir($TopDir); #Do this so we don't need to worry about distinguishing
#between absolute and relative (to TopDir) pathnames
#Everything following opening the files occurs in TopDir
############################################################################
initialize_backups();

warn "**Populating Icache...\n" if $verbose>=1;
my $toticache=0;
if($Readcache) { #Read in existing InodeCache from file
	$ptype = $Conf{CompressLevel} ? "cpool" : "pool";
	while(<RCACHE>) {
		if(/^(\d+)\s+(\S+)/) {
			&$write_Icache($ptype, $1, $2);
			$toticache++;
		} elsif(/^#(c?pool)\s*$/) {
			$ptype = $1;
		} else {
			warn "'$_' is not a valid cache entry\n" unless /^#/;
		}
	}
	close RCACHE;
} else { # Create InodeCache
	if($pool eq "both") {
		$toticache += populate_icache("pool");
		$toticache += populate_icache("cpool");
	} else {
		$toticache += populate_icache($pool);
	}
	close WCACHE if $Writecache;
}
warn "*Icache entries created=$toticache\n" if $verbose >=2;
if(defined(&total_size)){ #JJK-DEBUG: Print out sizes used by InodeCache
	warn sprintf("InodeCache total size: %d\n",total_size(\%InodeCache));
	warn sprintf("Cpool cache entries: %d\tSize: %d\tTotal_size: %d\n", 
				 (scalar keys %{$InodeCache{"pool"}}), 
				 size($InodeCache{"pool"}), total_size($InodeCache{"pool"})) 
		if defined $InodeCache{"pool"};
	warn sprintf("Cpool cache entries: %d\tSize: %d\tTotal_size: %d\n",
				 (scalar keys %{$InodeCache{"cpool"}}),
				 size($InodeCache{"cpool"}), total_size($InodeCache{"cpool"})) 
		if defined $InodeCache{"cpool"};
}

exit unless @backups;

warn "**Recording nonpooled top level files...\n" if $verbose>=1;
foreach (@nonpooled) {  #Print out the nonpooled files
	printf NOPOOL "%s\n", $_;
}
close(NOPOOL);

warn "**Recording linked & non-linked pc files...\n" if $verbose>=1;
my $lastmachine = '';
foreach (@backups) {
	m|$pcdir([^/]*)|;
	$lastmachine = $1 if $1 ne $lastmachine;

	warn "* Recursing through backup: $_\n" if $verbose>=1;
	$compresslvl = shift(@compresslvls);
	$attr = BackupPC::Attrib->new({ compress => $compresslvl });
    #Reinitialize this jLib global variable in case new compress level
	$ptype = ($compresslvl > 0 ? "cpool" : "pool");
	m|(.*/)(.*)|;
	find_pool_links($1, $2);
}
close(LINKS);
close(NOLINKS);

##############################################################################
#Print summary & concluding message:
printf STDERR "\nDirectories=%d\tTotal Files=%d\n",
	$directories, ($totfiles + $#nonpooled);
printf STDERR "Link files=%d\t [Zero-length=%d,  Hardlinks=%d (Fixed=%d)]\n",
	($zerolengthfiles+$existinglink_pcfiles+$fixedlink_pcfiles),
	$zerolengthfiles, ($existinglink_pcfiles+$fixedlink_pcfiles),
	$fixedlink_pcfiles;
printf STDERR "Non-pooled Toplevel=%d\n", $#nonpooled;
printf STDERR "Non-pooled Other=%d [Valid-pc=%d (Failed-fixes=%d),  Invalid-pc=%d]\n",
	$unlinked_files, ($unlinked_pcfiles+$unlinkable_pcfiles),
	$unlinkable_pcfiles, $unlinked_nonpcfiles;
printf STDERR "PC files missing attrib entry=%d\n", $missing_attribs;

my ($rsyncnopool, $rsyncnolinks);
if($gzip) {
	$gzip = "-g ";
	$rsyncnopool = "zcat $nopoolfile | rsync -aOH --files-from=- $TopDir <newTopDir>";
	$rsyncnolinks = "zcat $nolinksfile | rsync -aOH --files-from=- $TopDir <newTopDir>";
} else {
	$gzip = "";
	$rsyncnopool = "rsync -aOH --files-from=$nopoolfile $TopDir <newTopDir>";
	$rsyncnolinks = "rsync -aOH --files-from=$nolinksfile $TopDir <newTopDir>";
}

print STDERR <<EOF;
------------------------------------------------------------------------------
To complete copy, do the following as user 'root' or 'backuppc':
  1. Copy/rsync over the pool & cpool directories to the new TopDir
     (note this must be done *before* restoring '$linksfile')
     For rsync:
        rsync -aO $TopDir\{pool,cpool\} <newTopDir>

  2. Copy/rsync over the non-pooled top level files ($nopoolfile)
     For rsync:
        $rsyncnopool

  3. Restore the pc directory tree, hard links and zero-sized files:
        $0 -r ${gzip}[-t <newTopDir>] $linksfile

  4. Optionally, copy/rsync over the non-linked pc files ($nolinksfile)
     For rsync:
        $rsyncnolinks

------------------------------------------------------------------------------

EOF
exit;

##############################################################################
##############################################################################
#SUBROUTINES:

sub usage
{
    print STDERR <<EOF;

usage: $0 [options] -o <outfile> [<relpath-to-pcdir> <relpath-to-pcdir>...]
       $0 [options] -r <restorefile> [<relpath-to-pcdir> <relpath-to-pcdir>...]

  where the optional <relpath-to-pcdir> arguments are paths relative to the pc
  tree of form: 'host' or 'host/share' or 'host/share/n' or 'host/share/n/.../'
  If no optional <relpath-to-pcdir> arguments are given then the entire pc tree
  is backed up or restored.
  
  Options: [Common to copy & restore]
   --dryrun|-d            Dry-run - doesn\'t change pool or pc trees
                          Negate with: --nodryrun
   --Force|-F             Overrides various checks (e.g., if BackupPC running
                          or if directories present)
   --gid|-G <gid>         Set group id for backuppc user
                          [Default = $giddef_def]
   --gzip|-g              Pipe files to/from gzip compression
   --topdir|-t            Location of TopDir.
                          [Default = $TopDir_def]
                          Note you may want to change from default for example
                          if you are working on a shadow copy.
   --uid|-U <uid>         Set user id for backuppc user
                          [Default = $uiddef_def]
   --verbose|-v           Verbose (repeat for more verbosity)
                          [Default level = $verbose_def]
                          Use --noverbose to turn off all verbosity
   --help|-h              This help message

  Options: [Copy only]
   --cleanpool|-c         If orphaned files (nlinks=1) found when populating
                          Icache, remove them (and renumber chain as needed)
                          NOTE: Orphans shouldn\'t exist if you have just run
                          BackupPC_nightly
   --fixlinks|-f          Attempt to link valid pc files back to the pool
                          if not already hard-linked
                          NOTE: this changes files in the pc and\/or pool
                          of your source too!
   --outfile|-o [outfile] Required stem name for the 3 output files
                             <outfile>.nopools
                             <outfile>.links
                             <outfile>.nolinks
   --pool|-p  [pool|cpool|both]  Pools to include in Icache tree
                          [Default = $pool_def]
   --Pack|-P              Pack both the indices and values of the InodeCache.
                          This saves approximately 52 bytes per pool entry.
                          For o(1 million) entries, this reduces usage from
                          ~190 bytes/entry to ~140 bytes/entry
   --Readcache|-R [file]  Read in previously written inode pool cache from
                          file. This allows resuming previously started backups
                          Only use this option if the pool has not changed.
                          Note: can\'t be used with --Writecache|-W
   --stdio|-s             Print the directory tree, links and zero-sized files
                          to stdout so it can be piped directly to another copy
                          of the program running --restore
                          NOTE: Status, Warnings, and Errors are printed to 
                          stdout.
   --WriteCache|-W        Write inode pool cache to file <outfile>.icache
                          as a 2 column list consisting of:
                             <inode number> <pool entry>
                          If repeated, include md5sums of the (uncompressed)
                          pool file contents as a 3rd column (this is slow)
                          If argument path is '-', then quit after writing
                          cache.
                          Note: can\'t be used with --Readcache|-R
  Options: [Restore only]
   --Overwrite|-O         OVERWRITE existing files & directories (Dangerous)
   --Skip|-S              SKIP existing backups
   --stdio                Read the directory tree, links and zero-sized files
                          from stdin so it can be piped directly from another
                          copy of the program running in the create mode.
                          Note <restorefile> should not be used in this case
                          For example, the following pipe works:
                          $0 -t <source TopDir> [-g] --stdio | $0 -t <dest TopDir> [-g] -r --stdio

OVERVIEW:
  First create an inode-indexed cache (hash) of all pool entries.
  Note the cache may optionaly be written out to a file for later re-use
  with the --Readcache|-R flag.

  Then, recurse through the paths specified relative to the pc tree or if no
  paths specified then the entire pc tree. 
  - If the file is a (non-pooled) top-level log file, then write its path
    relative to pcdir out to <outfile>.nopool
    Note this includes all non-directories above the share level plus the
    backInfo files that are covered by the input paths
  - If the file is a directory, zero length file, or an existing hard link to
    the tree, then write it out to <outfile>.links
  - If the file is not hard-linked but is a valid non-zero length pc file 
    (f-mangled and present in the attrib file) and --fixlinks is selected,
    then try to link it properly to the appropriate pool.
  - Otherwise, add it to <outfile>.nolinks

  NOTE: TO ENSURE INTEGRITY OF RESULTS IT IS IMPORTANT THAT BACKUPPC IS NOT
  RUNNING (use --Force to override)

  NOTE: you should run BackupPC_nightly before running this program so that
  no unnecessary links are backed up; alternatively, set the --cleanpool
  option which will remove orphan pool entries.

EOF
exit(1);
}

#Glob to determine what is being backed up. 
#Make sure each backup seems valid and determine it's compress level
#Collect top-level non-pooled files
sub initialize_backups
{
	if (!@ARGV) { # All backups at backup number level
		# TopDir/pc/<host>/<nn>
		@backups = bsd_glob("${pcdir}*/*"); #2 levels down;
		@nonpooled = grep(! -d , bsd_glob("${pcdir}*")); #All non-directories
	} else { # Subset of backups
		return if($Writecache && $ARGV[0] eq '-'); #Don't copy pc tree
		foreach(@ARGV) {
			my $backupdir = $pcdir . $_ . '/';
			$backupdir  =~ s|//*|/|g; #Remove redundant slashes
			$backupdir =~ s|/\.(?=/)||g; #Replace /./ with /
			die "ERROR: '$backupdir' is not a valid pc tree subdirectory\n" if $pcdir eq $backupdir || !-d $backupdir;
			if($backupdir =~ m|^\Q${pcdir}\E[^/]+/$|) {  #Hostname only
				push(@backups, bsd_glob("${backupdir}*"));
			} else { # At share level or below #Backup number or below
				push(@backups, ${backupdir});
			}
		}
		@backups = keys %{{map {$_ => 1} @backups}}; #Eliminate dups
		@nonpooled = keys %{{map {$_ => 1} @nonpooled}}; #Eliminate dups
	}

	push(@nonpooled, grep(! -d, @backups)); #Non-directories
	@backups = grep(-d , @backups); #Directories
	push(@nonpooled, grep(m|/backupInfo$|, @backups)); # backupInfo not pooled
    #Note everything else *should* be pooled - if not, we will catch it later as an error
	@backups = grep(!m|/backupInfo$|, @backups);

	foreach(@backups) {
		s|/*$||; #Remove trailing slash
		m|^(\Q${pcdir}\E[^/]+/[^/]+)(/)?|;
		die "Backup '$1' does not contain a 'backupInfo' file\n"
			unless -f "$1/backupInfo";
		push(@nonpooled, "$1/backupInfo") unless $2; #Don't include if share level or below
		my $compress = get_bakinfo("$1","compress");
		push(@compresslvls, $compress);
		my $thepool = $compress > 0 ? 'cpool' : 'pool';
		die "Backup '$1' links to non-included '$thepool'\n"
			if $pool ne 'both' && $pool ne $thepool;
	}
}

#Iterate through the 'pooldir' tree and populate the InodeCache hash
sub populate_icache
{
	my ($fpool) = @_;
	my (@fstat, $dh, @dirlist);
	my $icachesize = 0;

	return 0 unless bsd_glob("$fpool/[0-9a-f]"); #No entries in pool
	print WCACHE "#$fpool\n" if $Writecache;
	my @hexlist = ('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f');
	my ($idir,$jdir,$kdir);
	print STDERR "\n* Populating Icache with '$fpool' branch:[0-f] " if $verbose >=2;
	foreach my $i (@hexlist) {
		print STDERR "$i " if $verbose >=2;
		$idir = $fpool . "/" . $i . "/";
		foreach my $j (@hexlist) {
			$jdir = $idir . $j . "/";
			foreach my $k (@hexlist) {
				$kdir = $jdir . $k . "/";
				unless(opendir($dh, $kdir)) {
					warn "Can't open pool directory: $kdir\n" if $verbose>=4;
					next;
				}
				my @entries = grep(!/^\.\.?$/, readdir ($dh)); #Exclude dot files
				closedir($dh);
				warn "POOLDIR: $kdir (" . ($#entries+1) ." files)\n"
					if $verbose >=3;

				if($cleanpool) { #Remove orphans & renumber first and then
				#create the Icache after orphan deletion & chain renumbering
				#NOTE: we need to do this before populating the InodeCache
				#since pool deletions & renumbering would change the cache
					my @poolorphans = 
						grep(-f $kdir . $_ && (stat(_))[3] < 2, @entries);
					foreach (sort {poolname2number($b) cmp poolname2number($a)} 							 @poolorphans) { #Reverse sort to minimize moves
						my $pfile = $kdir . $_;
						my $result =delete_pool_file($pfile);
						if($verbose >=1) {
							$result == 1 ?
								warn "WARN: Deleted orphan pool entry: $pfile\n": 
								warn "ERROR: Couldn't properly delete orphan pool entry: $pfile\n"
						}
					}
					@entries = grep(!/^\.\.?$/, readdir ($dh))
						if(@poolorphans); #Reload if orphans renumbered/removed
				}
				foreach (@entries) {
					# Go through all entries in terminal cpool branch
					@fstat = stat($kdir . $_);
					#Note: 0=dev, 1=ino, 2=mode, 3=nlink, 4=uid, 5=gid, 6=rdev
					#7=size, 8=atime, 9=mtime, 10=ctime, 11=blksize, 12=blocks
					if($fstat[3] >= 2) { # Valid (non-orphan) pool entry
                        #Note: No sense in creating icache entries for orphans
						&$write_Icache($fpool, $fstat[1], $_);
						if($Writecache >= 2) {
							printf WCACHE "%d %s %s\n", $fstat[1], $_,
							zFile2FullMD5($bpc, $md5, $kdir . $_);
						}elsif($Writecache) {
							printf WCACHE "%d %s\n", $fstat[1], $_;
						}
						$icachesize++;
					} else { #Orphan pool entry
						warn "WARN: Orphan pool entry: $_\n" 
							if $verbose>=1;
					}
					warn "WARN: Zero-size pool entry: $_\n"
						if $fstat[7] == 0 && $verbose>=1;
				}
			} # kdir
		} # jdir
	} # idir
	print STDERR "\n" if $verbose >=2;
	return $icachesize;
}

#Recursively go through pc tree
sub find_pool_links
{
	my ($dir, $filename) = @_;

	my $dh;
	my $file = $dir . $filename;
	if(-d $file) {
		my @fstat = stat(_); #Note last stat was -d $file
		#Print info to signal & re-create directory:
		#D <user> <group> <mod> <atime> <mtime> <file name>
		print_file_reference("D", $file, \@fstat);
		$directories++;
		opendir($dh,$file);
		my @contents = readdir($dh);
		closedir($dh);
		foreach (@contents) {
			next if /^\.\.?$/;     # skip dot files (. and ..)
			find_pool_links($file . '/', $_); #Recurse
		}
	}
	else { #Not a directory
		my @fstat = stat(_); #Note last stat was -d $file
		$totfiles++;
		if($fstat[7] == 0) { #Zero size file
			print_file_reference("Z", $file, \@fstat);
			$zerolengthfiles++;
			return;
		} elsif($fstat[3] > 1) { #More than one link
			if(defined(my $pooltarget = &$read_Icache($ptype, $fstat[1]))) { 
            #Valid hit: hard link found in InodeCache
				$existinglink_pcfiles++;
				$pooltarget =~ /(.)(.)(.)/;
				print_hardlink_reference("$ptype/$1/$2/$3/$pooltarget", $file);
				return;
			}
		}

		if($file =~ m|^\Q${pcdir}\E[^/]+/[^/]+/backupInfo$|) {
			$totfiles--;
			return;		#BackupInfo already taken care of in 'nonpooled'
		}

		#Non-zero sized file not in InodeCache that is not 'backupInfo'
		if($filename =~ /^f|^attrib$/ && -f $file) {
			#VALID pc file if f-mangled or attrib file
			if( $filename =~ /^f/ && 
				!( -f "$dir/attrib" &&
				   $attr->read($dir,"attrib") == 1 &&
				   defined($attr->get($bpc->fileNameUnmangle($filename))))) {
				#Attrib file error if attrib file missing or
				#unmangled name not an element of the attrib file
				warn "ERROR: $file (inode=$fstat[1], nlinks=$fstat[3]) VALID pc file with MISSING attrib entry\n";
				$missing_attribs++;
			}
			if($fixlinks) {
				if(fix_link($file, \@fstat) == 1) {
					$fixedlink_pcfiles++;
					return;
				} else {$unlinkable_pcfiles++;}
			} else{
				warn "ERROR: $file (inode=$fstat[1], nlinks=$fstat[3]) VALID pc file NOT LINKED to pool\n";
				$unlinked_pcfiles++;
			}
		} else {
			warn "ERROR: $file (inode=$fstat[1], nlinks=$fstat[3]) INVALID pc file and UNLINKED to pool\n";
			$unlinked_nonpcfiles++
		}
		#ERROR: Not linked/linkable to pool (and not zero length file or directory
		print_file_reference("X", $file, \@fstat);
		printf NOLINKS "%s\n", $file;
		$unlinked_files++
	}
}

#Try to fix link by finding/creating new pool-link
sub fix_link
{
	my ($filename, $fstatptr) = @_;

	my ($plink, @pstat);
	my ($md5sum, $result) = zFile2MD5($bpc, $md5, $filename, 0, $compresslvl);
	$result = jMakeFileLink($bpc, $filename, $md5sum, 2, $compresslvl, \$plink)
		if $result > 0;
	#Note we choose NewFile=2 since if we are fixing, we always want to make the link
	if($result > 0) { #(true if both above calls succeed)
		$plink =~ m|.*(\Q${ptype}\E.*/(.*))|;
		$plink = $1; #Path relative to TopDir
		if($dryrun) {
			@pstat = @$fstatptr; 
		} else {
			@pstat  =  stat($plink);
			&$write_Icache($ptype, $pstat[1], $2);
		}
		print_hardlink_reference($plink, $filename);
		if($verbose >=2) {
			warn "${DRYRUN}NOTICE: pool entry '$plink' (inode=$fstatptr->[1]) missing from Icache and added back\n" if $result == 3;
			warn sprintf("${DRYRUN}NOTICE: %s (inode=%d, nlinks=%d) was fixed by linking to *%s* pool entry: %s (inode=%d, nlinks=%d)\n",
						 $filename, $fstatptr->[1], $fstatptr->[3],
						 ($result == 1 ? "existing" : "new"), 
						 $plink, $pstat[1], $pstat[3])
				if $result !=3;
		}
		return 1;
	}
	warn "ERROR: $filename (inode $fstatptr->[1]); fstatptr->[3] links; md5sum=$md5sum) VALID pc file FAILED FIXING by linking to pool\n";
	return 0;
}

sub print_hardlink_reference
{
	my ($poolname, $filename) = @_;
	
	#<poolname> <filename>
	printf LINKS "%s %s\n", $poolname, $filename; #Print hard link
}

sub print_file_reference
{
	my ($firstcol, $filename, $fstatptr) = @_;

	#<firstcol>  <user> <group> <mod> <mtime> <filename>
	printf(LINKS "%s %s %s %04o %u %s\n",
		   $firstcol, UID($fstatptr->[4]), GID($fstatptr->[5]), 
		   $fstatptr->[2] & 07777, $fstatptr->[9], $filename);
}

###############################################################################
##Read/write InodeCache

#Note that without packing, InodeCache hash requireas about 186
#bytes/entry ('total_size') to store each entry with about 74 bytes
#required to store the hash structure ('size') alone and an additional
#exactly 112 byte to store the 32-char hex string (this assumes chains
#are sparse enough not to affect the average storage). The 74 bytes
#for the hash structure consists of about 8 bytes for the inode data
#plus 48 bytes for the overhead of the scalar variable storing the
#index plus ~22 bytes for the magic of hash storage and the pointer to
#the hash value. The additional 112 bytes consists of 64 bytes to
#store the unpacked 32-char hex string plus 48 bytes of overhead for
#the scalar variable storing the hash value.

#If we pack the value, we can reduce the hex string storage from 64
#bytes to 16 bytes by storing 2 hex chars per byte. This reduces the
#total storage by 48 bytes/entry from 186 to 138 bytes/entry.

#If we pack the index as an unsigned 32-bit long (V), then we can
#save an additional 4 bytes, reducing the average storage to about 134
#bytes/entry. But, we need to make sure that the highest inode number
#is less than 2^32 (~4.3 billion). If we pack the index as an unsigned
#64-bit quad (Q), then we use 8 bytes for the index data and we are
#back to a total 138 bytes/entry.

#Note these averages are based on a hash size (i.e. pool size) of 1
#million entries. The 74 bytes/entry for the hash structure alone will
#increase (slowly) as the size of the hash increases but the storage
#size for the hash vaue (112 bytes unpacked, 64 packed) does not
#increase.

sub read_Icache_nopack
{
	$InodeCache{$_[0]}{$_[1]}; #No packing of values & indices
}

sub read_Icache_pack
{
#	join("_", unpack("H32V", $InodeCache{$_[0]}{$_[1]})); #Pack values only

	#Also pack indices:
	join("_", unpack("H32V", $InodeCache{$_[0]}{pack("V",$_[1])}));#32-bit indices
#	join("_", unpack("H32V", $InodeCache{$_[0]}{pack("Q",$_[1])}));#64-bit indices
	#Note: shouldn't need 64 bits for inodes since they are ino_t
	#which are typdef'd as longs
}

sub write_Icache_nopack
{
	$InodeCache{$_[0]}{$_[1]} = $_[2]; #No packing of values & indices
}

sub write_Icache_pack
{
	my ($pool, $index, $value) = @_;

	$value =~ m|(.{32})(.(.*))?|; 
	#Pack values only
#	$InodeCache{$pool}{$index}= defined($3) ? pack("H32V", $1, $3) : pack("H32", $1);

	#Also pack indices:
	$InodeCache{$pool}{pack("V",$index)} = defined($3) ? pack("H32V", $1, $3) : pack("H32", $1); #32-bit indices

#	$InodeCache{$pool}{pack("Q",$index)} = defined($3) ? pack("H32V", $1, $3) : pack("H32", $1); #64-bit indices
	#Note shouldn't need 64 bits for inodes since they are ino_t which
	#are typdef'd as longs
}

###############################################################################
# Return user name corresponding to numerical UID with caching
sub UID
{
	unless(exists($UIDcache{$_[0]})) {
		unless(defined($UIDcache{$_[0]} = getpwuid($_[0]))) {
			printf STDERR "Warning: '%d' not found in password file, writing numerical UID instead...\n", $_[0];
			$UIDcache{$_[0]} = $_[0];
		}
	}
    return $UIDcache{$_[0]};
}

# Return group name corresponding to numerical GID with caching
sub GID
{
	unless(exists($GIDcache{$_[0]})) {
		unless(defined($GIDcache{$_[0]} = getgrgid($_[0]))) {
			printf STDERR "Warning: '%d' not found in group file, writing numerical GID instead...\n", $_[0];
			$GIDcache{$_[0]} = $_[0];
		}
	}
    return $GIDcache{$_[0]};
}

# Return numerical UID corresponding to user name with caching
sub USER
{
	unless(exists($USERcache{$_[0]})) {
		unless(defined($USERcache{$_[0]} = getpwnam($_[0]))) {
			printf STDERR "Warning: '%s' not found in password file, writing default backuppc UID (%d) instead...\n", $_[0], $uiddef;
			$USERcache{$_[0]} = $uiddef;
		}
	}
    return $USERcache{$_[0]};
}

# Return numerical GUID coresponding to group name with caching
sub GROUP
{
	unless(exists($GROUPcache{$_[0]})) {
		unless(defined($GROUPcache{$_[0]} = getgrnam($_[0]))) {
			printf STDERR "Warning: '%s' not found in group file, writing default backuppc GID (%d) instead...\n", $_[0], $giddef;
			$GROUPcache{$_[0]} = $giddef;
		}
	}
    return $GROUPcache{$_[0]};
}
###############################################################################
###############################################################################
sub do_restore
{
	my $currbackup = "";
	my $formaterr = 0;
	my $ownererr = 0;
	my $permserr = 0;
	my $mkdirerr = 0;
	my $mkzeroerr = 0;
	my $mklinkerr = 0;
	my $filexsterr = 0;
	my $utimerr = 0;
	my $newdir = 0;
	my $newzero = 0;
	my $newlink = 0;
	my $skipped = 0;

###############################################################################
	if($stdio) {
		open(LINKS, $gzip ? "/bin/zcat - |" : "<& STDIN");
	} else {
		my $restorefile = shift @_;
		open(LINKS, $gzip ? "/bin/zcat $restorefile |" : "< $restorefile") or
			die "ERROR: Can't open '$restorefile' for reading!($!)\n";
	}
	my @backuplist = @_;
###############################################################################
	chdir($TopDir); #Do this so we don't need to worry about distinguishing
                    #between absolute and relative (to TopDir) pathnames
###############################################################################
	die "ERROR: pool directories empty!\n"
		unless $Force || bsd_glob("{cpool,pool}/*");

	my(@skiplist, $skiplist); #Backups to skip...
	if($Skip) {
		@skiplist = grep(@{[bsd_glob("$_/f*")]}, bsd_glob("${pcdir}*/[0-9]*"));
		#NOTE: glob must be evaulated in list context because stateful...
	} elsif(!$Overwrite && grep(-d, bsd_glob("${pcdir}*/[0-9]*/f*"))) {
		die "ERROR: pc directory contains existing backups!\n(use --Skip to skip or --Overwrite to OVERWRITE)\n"
	}
	$skiplist = "\Q" . join("\E|\Q", @skiplist) . "\E" if @skiplist;

	my $backuplist; #Backups to selectively backup...
	$backuplist = "\Q" . join("\E|\Q", @backuplist) . "\E" if @backuplist;

	umask 0000; #No permission bits disabled
	my $time = time; #We will use this for setting atimes.
	my @dirmtimes =(); #Stack consisting of paired "dir, mtime" entries
	my $matchback = 1;
	my ($line);

LINE:	while($line = <LINKS>) {
		chomp $line;

		unless($line =~ m|^[a-f0-9DZX#]|) { #First character test
			print STDOUT "ERR_CHAR1: $line\n";
			warn sprintf("ERROR: Illegal first line character: %s\n", 
						 substr($line,0,1))
				if $verbose >=1;
			next LINE; #NOTE: next without line would go to next switch case
		}

		switch ($&) { #Go through cases...
			case 'D' {
				unless($line =~ m|^D +([^ ]+) +([^ ]+) +([^ ]+) +([^ ]+) +(\Q${pcdir}\E.*)|) {
					print STDOUT "ERR_DFRMT $line\n";
					$formaterr++;
					next LINE;
				}
				#NOTE: 1=uname 2=group 3=mode 4=mtime 5=dirpath
				print STDERR "$1|$2|$3|$4|$5|\n" if $verbose >=4;
				my $user = USER($1);
				my $group = GROUP($2);
				my $mode = oct($3);
				my $mtime = $4;
				my $dir = $5;  $dir  =~ s|/*$||; #Remove trailing slash
				$dir =~ m|(.*)/|;
				my $pdir = $1; #parent dir

				#Don't restore if on skiplist or if not on backuplist
				if(($skiplist && $dir =~ m|^($skiplist)|) ||
				   ($backuplist && $dir !~ m|^pc/($backuplist)|)) {
					$matchback = 0;
					next LINE;
				} else {
					$matchback = 1;
				}

				if($verbose >= 1) {
					$dir =~ m|pc/([^/]*/[^/]*)|;
					if($1 ne $currbackup) {
						$currbackup = $1;
						warn "RESTORING: $currbackup\n";
					}
				}

				#Look at @dirmtimes stack to see if we have backed out of
				#top directory(ies) on stack and can now set mtime
				my $lastdir; #If in new part of tree, set mtimes for past dirs
				while(defined($lastdir = shift(@dirmtimes)) && 
					  $dir !~ m|^\Q$lastdir\E|) {
					jutime($time, shift(@dirmtimes), $lastdir);
				}
				unshift(@dirmtimes, $lastdir) if $lastdir; #Put back last one

				if(! -e $dir) { #Make directory (nothing in the way)
					unless( -d $pdir ||  jmake_path $pdir){ 
						#Make parent directory if doesn't exist
						#NOTE: typically shouldn't be necesary since list is 
						#created with directories along the way
						print STDOUT "ERR_MKDIR $line\n";
						$mkdirerr++;
						next LINE;
					}
					#Make directory & set perms
					unless(mkdir $dir, $mode) {
						print STDOUT "ERR_MKDIR $line\n";
						$mkdirerr++;
						next LINE;
					}
				} elsif(-d $dir) { #Directory already exists
					#Set perms
					unless(jchmod $mode, $dir) {
						print STDOUT "ERR_PERMS $line\n";
						$permserr++;
						next LINE;
					}
				} else { #Non-directory in the way, abort line
					print STDOUT "ERR_DEXST $line\n";
					$filexsterr++;
					next LINE;
				}

				#Set ownership
				unless(jchown $user, $group, $dir){
						print STDOUT "ERR_OWNER $line\n";
						$ownererr++;
						next LINE;
				}
				#Put dir mtime on stack
				unshift(@dirmtimes, $mtime); #We need to set dir mtime
				unshift(@dirmtimes, $dir);   #when done adding files to dir

				$newdir++;
			}

			case 'Z' {
				next LINE unless $matchback;
				unless($line =~ m|^Z +([^ ]+) +([^ ]+) +([^ ]+) +([^ ]+) +((\Q${pcdir}\E.*/)(.*))|) {
					print STDOUT "ERR_ZFRMT $line\n";
					$formaterr++;
					next LINE;
				}
				#NOTE: 1=uname 2=group 3=mode 4=mtime 5=fullpath 6=dir 7=file
				print STDERR "$1|$2|$3|$4|$5|$6|$7\n" if $verbose >=4;
				my $user = USER($1);
				my $group = GROUP($2);
				my $mode = oct($3);
				my $mtime = $4;
				my $file = $5;
				my $dir = $6;
				my $name = $7;

				#Check if file exists and not overwritable
				if(-e $file && !($Overwrite && -f $file && unlink($file))) {
					print STDOUT "ERR_ZEXST $line\n";
					$filexsterr++;
					next LINE;
				}

				unless( -d $dir || jmake_path $dir){ #Make dir if doesn't exist
					#NOTE: typically shouldn't be necesary since list is
					#created with directories along the way
					print STDOUT "ERR_MKDIR $line\n";
					$mkdirerr++;
					next LINE;
				}
				#Create zero-length file with desired perms
				unless(sysopen(ZERO, $file, $CREATMASK, $mode) && close(ZERO)){
					print STDOUT "ERR_MKZER $line\n";
					$mkzeroerr++;
					next LINE;
				}
				unless(jchown $user, $group, $file){ #Set ownership
					print STDOUT "ERR_OWNER $line\n";
					$ownererr++;
					next LINE;
				}
				unless(jutime $time, $mtime, $file) { #Set timestamps
					$utimerr++;
					next LINE;
				}
				$newzero++;
			}

			case 'X' {$skipped++; next LINE; }  #Error line

			case '#' {next LINE; }  #Comment line

			else { #Hard link is default switch case
				next LINE unless $matchback;
				unless($line =~ m|(c?pool/[0-9a-f]/[0-9a-f]/[0-9a-f]/[^/]+) +((\Q${pcdir}\E.*/).*)|) {
					print STDOUT "ERR_LFRMT $line\n";
					$formaterr++;
					next LINE;
				}
				print STDERR "$1|$2|$3\n" if $verbose >=4; # 1=source 2=target 3=targetdir
				my $source = $1;
				my $target = $2;
				my $targetdir = $3;

				if(-e $target && 
				   !($Overwrite && -f $target && unlink($target))){
					print STDOUT "ERR_LEXST $line\n"; 
					$filexsterr++; #Target exists and not overwritable
					next LINE;
				}

				unless(-d $targetdir || jmake_path $targetdir){
					#Make targetdir if doesn't exist
					#NOTE: typically shouldn't be necesary since list is
					#created with directories along the way
					print STDOUT "ERR_MKDIR $line\n";
					$mkdirerr++;
					next LINE;
				}

				unless(jlink $source, $target) { #Make link
					print STDOUT "ERR_MKLNK $line\n";
					$mklinkerr++;
					next LINE;
				}
				$newlink++
			}
		} #SWITCH end
	} # WHILE reading lines

	#Set mtimes for any remaining directories in @dirmtimes stack
	while(my $dir = shift(@dirmtimes)){
		jutime($time, shift(@dirmtimes), $dir);
	}

###############################################################################
	#Print results:
	

	printf("\nSUCCESSES: Restores=%d [Dirs=%d Zeros=%d Links=%d] Skipped=%d\n", 
		   ($newdir+$newzero+$newlink), $newdir, $newzero, $newlink, $skipped);
	printf("ERRORS: TOTAL=%d Format=%d Mkdir=%d Mkzero=%d Mklink=%d\n",
		   ($formaterr + $mkdirerr + $mkzeroerr + $mklinkerr +
			$filexsterr + $ownererr + $permserr + $utimerr),
		   $formaterr, $mkdirerr, $mkzeroerr, $mklinkerr);
	printf("        File_exists=%d Owner=%d Perms=%d Mtime=%d\n\n",
		   $filexsterr, $ownererr, $permserr, $utimerr);

	exit; #RESTORE done
}
###############################################################################

