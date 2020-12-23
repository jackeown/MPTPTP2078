%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0234+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jq0gzSsWoM

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:51 EST 2020

% Result     : Theorem 25.33s
% Output     : Refutation 25.33s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  195 ( 219 expanded)
%              Number of equality atoms :   28 (  32 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t23_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_tarski @ ( A @ B ) @ ( k1_tarski @ B ) ) )
        = ( k1_tarski @ A ) ) ) )).

thf('0',plain,(
    ! [X1029: $i,X1030: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ ( X1029 @ X1030 ) @ ( k1_tarski @ X1030 ) ) )
        = ( k1_tarski @ X1029 ) )
      | ( X1029 = X1030 ) ) ),
    inference(cnf,[status(esa)],[t23_zfmisc_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X414: $i,X415: $i] :
      ( ( k2_xboole_0 @ ( X414 @ X415 ) )
      = ( k5_xboole_0 @ ( X414 @ ( k4_xboole_0 @ ( X415 @ X414 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 @ ( k2_tarski @ ( X0 @ X1 ) ) ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ A @ ( k2_tarski @ ( B @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X704: $i,X705: $i,X706: $i] :
      ( ( k1_enumset1 @ ( X704 @ ( X705 @ X706 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X704 @ ( k2_tarski @ ( X705 @ X706 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_enumset1 @ ( X1 @ ( X0 @ X1 ) ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t29_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ ( A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != B )
       => ( ( k5_xboole_0 @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) )
          = ( k2_tarski @ ( A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_zfmisc_1])).

thf('5',plain,(
    ( k5_xboole_0 @ ( k1_tarski @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
 != ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_A_2 ) ) )
     != ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) )
    | ( sk_B_2 = sk_A_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t100_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k1_enumset1 @ ( B @ ( C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X544: $i,X545: $i,X546: $i] :
      ( ( k1_enumset1 @ ( X546 @ ( X544 @ X545 ) ) )
      = ( k1_enumset1 @ ( X544 @ ( X545 @ X546 ) ) ) ) ),
    inference(cnf,[status(esa)],[t100_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ ( A @ ( A @ B ) ) )
      = ( k2_tarski @ ( A @ B ) ) ) )).

thf('8',plain,(
    ! [X871: $i,X872: $i] :
      ( ( k1_enumset1 @ ( X871 @ ( X871 @ X872 ) ) )
      = ( k2_tarski @ ( X871 @ X872 ) ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ ( X0 @ ( X1 @ X0 ) ) )
      = ( k2_tarski @ ( X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) )
     != ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) )
    | ( sk_B_2 = sk_A_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    sk_B_2 = sk_A_2 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    sk_A_2 != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

%------------------------------------------------------------------------------
