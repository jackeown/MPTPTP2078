%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0157+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sI5GSVYy3i

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  24 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :  162 ( 162 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t73_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) ),
    inference('cnf.neg',[status(esa)],[t73_enumset1])).

thf('0',plain,(
    ( k4_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t52_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_enumset1 @ C @ D @ E @ F ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k4_enumset1 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X6 ) @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t52_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X1 @ X2 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E )
 != ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).


%------------------------------------------------------------------------------
