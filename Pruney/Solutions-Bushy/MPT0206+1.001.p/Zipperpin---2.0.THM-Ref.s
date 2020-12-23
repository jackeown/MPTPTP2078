%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0206+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0mhzV0xKCk

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 (  32 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :  292 ( 292 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k7_enumset1_type,type,(
    k7_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t132_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_enumset1 @ G @ H @ I ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
        ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
        = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_enumset1 @ G @ H @ I ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_enumset1])).

thf('0',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k2_xboole_0 @ ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_enumset1 @ sk_G @ sk_H @ sk_I ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf(t54_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_tarski @ E @ F ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t54_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k2_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X8 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(l142_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i,I: $i] :
      ( ( k7_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H @ I )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k3_enumset1 @ E @ F @ G @ H @ I ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k7_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l142_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k7_enumset1 @ X8 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I )
 != ( k7_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H @ sk_I ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).


%------------------------------------------------------------------------------
