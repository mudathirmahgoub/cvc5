#!/usr/bin/perl
# macOS replacement for `timeout SECS cmd...` + wall-clock timing.
#
# Why this exists: macOS ships neither GNU `timeout` (nor coreutils `gtimeout`)
# nor bash 5's $EPOCHREALTIME, so the Linux harness's
#     start=$EPOCHREALTIME; out=$(... timeout 100 cvc5 ...); end=$EPOCHREALTIME
# does not run. This wrapper does both in one process so there is no extra
# shell/perl startup folded into the measured duration:
#   * forks the command, arms alarm(SECS) in the child (preserved across exec),
#   * the parent waits and measures Time::HiRes wall clock around the child,
#   * prints the child's stdout/stderr verbatim, then a final line
#         __DURATION__ <seconds>
#   * exit code mirrors GNU timeout: 124 on timeout, else the child's code
#     (128+signal if the child was killed).
#
# Usage:  timed_run.pl <timeout_secs> <cmd> [args...]
use strict;
use warnings;
use Time::HiRes qw(time);

my $timeout = shift @ARGV;
die "usage: timed_run.pl <secs> <cmd> [args...]\n" unless defined $timeout && @ARGV;

my $start = time;
my $pid = fork();
die "fork failed: $!" unless defined $pid;
if ($pid == 0) {
    alarm $timeout;                 # SIGALRM survives exec(); default action terminates
    exec { $ARGV[0] } @ARGV or do { print STDERR "exec failed: $!\n"; exit 127; };
}
waitpid($pid, 0);
my $status  = $?;
my $elapsed = time - $start;
my $sig     = $status & 127;
my $code    = $status >> 8;

printf("__DURATION__ %.3f\n", $elapsed);
exit(124)             if $sig == 14;          # SIGALRM => timeout (GNU timeout uses 124)
exit(128 + $sig)      if $sig;                # other signal
exit($code);
