%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0155+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LofGjTxyuv

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:47 EST 2020

% Result     : Theorem 14.96s
% Output     : Refutation 14.96s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  153 ( 164 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_6_type,type,(
    sk_C_6: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t71_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ ( A @ ( A @ ( B @ C ) ) ) )
      = ( k1_enumset1 @ ( A @ ( B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_enumset1 @ ( A @ ( A @ ( B @ C ) ) ) )
        = ( k1_enumset1 @ ( A @ ( B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ ( sk_A_2 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) ) )
 != ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ ( A @ ( B @ C ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ A @ ( k2_tarski @ ( B @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X479: $i,X480: $i,X481: $i] :
      ( ( k1_enumset1 @ ( X479 @ ( X480 @ X481 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X479 @ ( k2_tarski @ ( X480 @ X481 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = ( k2_xboole_0 @ ( A @ B ) ) ) )).

thf('2',plain,(
    ! [X329: $i,X330: $i] :
      ( ( k2_xboole_0 @ ( X329 @ ( k2_xboole_0 @ ( X329 @ X330 ) ) ) )
      = ( k2_xboole_0 @ ( X329 @ X330 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 @ ( k1_enumset1 @ ( X2 @ ( X1 @ X0 ) ) ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 @ ( k2_tarski @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X479: $i,X480: $i,X481: $i] :
      ( ( k1_enumset1 @ ( X479 @ ( X480 @ X481 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X479 @ ( k2_tarski @ ( X480 @ X481 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X2 @ ( k1_enumset1 @ ( X2 @ ( X1 @ X0 ) ) ) ) )
      = ( k1_enumset1 @ ( X2 @ ( X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ ( A @ ( B @ ( C @ D ) ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ A @ ( k1_enumset1 @ ( B @ ( C @ D ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X485: $i,X486: $i,X487: $i,X488: $i] :
      ( ( k2_enumset1 @ ( X485 @ ( X486 @ ( X487 @ X488 ) ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X485 @ ( k1_enumset1 @ ( X486 @ ( X487 @ X488 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ ( X2 @ ( X2 @ ( X1 @ X0 ) ) ) )
      = ( k1_enumset1 @ ( X2 @ ( X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) )
 != ( k1_enumset1 @ ( sk_A_2 @ ( sk_B_2 @ sk_C_6 ) ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
