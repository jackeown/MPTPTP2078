%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0228+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fr0JN6BG2B

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:50 EST 2020

% Result     : Theorem 11.82s
% Output     : Refutation 11.82s
% Verified   : 
% Statistics : Number of formulae       :   22 (  24 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :  128 ( 152 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1012: $i,X1013: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1012 @ ( k1_tarski @ X1013 ) ) )
      | ( X1012 = X1013 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X388: $i,X389: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X388 @ X389 ) @ X389 ) )
        = X388 )
      | ~ ( r1_xboole_0 @ ( X388 @ X389 ) ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X702: $i,X703: $i] :
      ( ( k2_tarski @ ( X702 @ X703 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X702 @ ( k1_tarski @ X703 ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ ( X1 @ X0 ) @ ( k1_tarski @ X0 ) ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t23_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_tarski @ ( A @ B ) @ ( k1_tarski @ B ) ) )
        = ( k1_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != B )
       => ( ( k4_xboole_0 @ ( k2_tarski @ ( A @ B ) @ ( k1_tarski @ B ) ) )
          = ( k1_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_zfmisc_1])).

thf('5',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ ( k1_tarski @ sk_B_2 ) ) )
 != ( k1_tarski @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_A_2 )
     != ( k1_tarski @ sk_A_2 ) )
    | ( sk_A_2 = sk_B_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    sk_A_2 = sk_B_2 ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    sk_A_2 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

%------------------------------------------------------------------------------
