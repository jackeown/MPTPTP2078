%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0222+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VFsajzsJ8V

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:50 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    5
%              Number of atoms          :   73 (  89 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ ( A @ B ) )
     => ( r1_xboole_0 @ ( k1_tarski @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X981: $i,X982: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X981 @ X982 ) )
      | ( r2_hidden @ ( X981 @ X982 ) ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t17_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != B )
       => ( r1_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_zfmisc_1])).

thf('1',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( C = A ) ) ) )).

thf('3',plain,(
    ! [X436: $i,X438: $i,X439: $i] :
      ( ~ ( r2_hidden @ ( X439 @ X438 ) )
      | ( X439 = X436 )
      | ( X438
       != ( k1_tarski @ X436 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('4',plain,(
    ! [X436: $i,X439: $i] :
      ( ( X439 = X436 )
      | ~ ( r2_hidden @ ( X439 @ ( k1_tarski @ X436 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    sk_A_2 = sk_B_2 ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    sk_A_2 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

%------------------------------------------------------------------------------
