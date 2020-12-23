%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0159+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tLfaNY7Aus

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :  202 ( 202 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(t75_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
        ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
        = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) ),
    inference('cnf.neg',[status(esa)],[t75_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t63_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k4_enumset1 @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X8 ) @ ( k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t63_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_enumset1 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k5_enumset1 @ X0 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    $false ),
    inference(simplify,[status(thm)],['6'])).


%------------------------------------------------------------------------------
