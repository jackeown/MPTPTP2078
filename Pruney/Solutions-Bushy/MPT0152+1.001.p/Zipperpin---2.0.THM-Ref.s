%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0152+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yTKkMteDl0

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:24 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :  278 ( 278 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   20 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t68_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) @ ( k1_tarski @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X15 @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf(l68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k2_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X7 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X7 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k5_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k5_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).


%------------------------------------------------------------------------------
