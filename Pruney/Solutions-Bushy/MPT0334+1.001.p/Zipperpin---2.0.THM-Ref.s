%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0334+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kApue85Pp7

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:43 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   19 (  21 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    5
%              Number of atoms          :  138 ( 174 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X3 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X2 ) @ X3 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X3 ) @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) @ ( k1_tarski @ X0 ) )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t147_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( A != B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_zfmisc_1])).

thf('3',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).


%------------------------------------------------------------------------------
