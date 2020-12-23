%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3ic9i5u4ik

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 123 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  824 (1454 expanded)
%              Number of equality atoms :   51 ( 105 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(t67_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k2_tarski @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k1_enumset1 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('32',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['0','31'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k5_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X28 ) @ ( k4_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('38',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k6_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ ( k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3ic9i5u4ik
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:46:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 122 iterations in 0.110s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.56  thf(sk_H_type, type, sk_H: $i).
% 0.21/0.56  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.56  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.56                                           $i > $i).
% 0.21/0.56  thf(t67_enumset1, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.56     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.56       ( k2_xboole_0 @
% 0.21/0.56         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.56        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.56          ( k2_xboole_0 @
% 0.21/0.56            ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t67_enumset1])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.56         != (k2_xboole_0 @ 
% 0.21/0.56             (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.21/0.56             (k2_tarski @ sk_G @ sk_H)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t42_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.56       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.56  thf(t41_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k2_tarski @ A @ B ) =
% 0.21/0.56       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i]:
% 0.21/0.56         ((k2_tarski @ X8 @ X9)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.56  thf(t4_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.56       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.56           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.56              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.56  thf(t44_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.56       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         ((k2_enumset1 @ X13 @ X14 @ X15 @ X16)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_enumset1 @ X14 @ X15 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.56           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ 
% 0.21/0.56              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X4)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.56           (k2_tarski @ X1 @ X0))
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.21/0.56              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['7', '10'])).
% 0.21/0.56  thf(t47_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.56     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.56       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.56         ((k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X17) @ 
% 0.21/0.56              (k2_enumset1 @ X18 @ X19 @ X20 @ X21)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.56              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.21/0.56           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.21/0.56              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf(t51_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.56     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.56       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.56         ((k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.21/0.56              (k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.21/0.56              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.56           (k2_tarski @ X1 @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['11', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.21/0.56              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.56           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.21/0.56              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X6)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.56           (k2_tarski @ X1 @ X0))
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.21/0.56              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['17', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.56         ((k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.21/0.56              (k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i]:
% 0.21/0.56         ((k2_tarski @ X8 @ X9)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.56              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         ((k1_enumset1 @ X10 @ X11 @ X12)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.21/0.56           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.21/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.56           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.21/0.56              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.56           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.21/0.56              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['22', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.56           (k2_tarski @ X1 @ X0))
% 0.21/0.56           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.56              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['21', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.56         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.56             (k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.21/0.56      inference('demod', [status(thm)], ['0', '31'])).
% 0.21/0.56  thf(t56_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.56     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.21/0.56       ( k2_xboole_0 @
% 0.21/0.56         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.56         ((k5_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X28) @ 
% 0.21/0.56              (k4_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.21/0.56              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.21/0.56           (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.21/0.56              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.56           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.56           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.21/0.56              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['22', '29'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.56           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.56           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.21/0.56              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.57  thf(t62_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.57     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.57       ( k2_xboole_0 @
% 0.21/0.57         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, 
% 0.21/0.57         X42 : $i]:
% 0.21/0.57         ((k6_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.21/0.57           = (k2_xboole_0 @ (k1_tarski @ X35) @ 
% 0.21/0.57              (k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.57         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.21/0.57           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.21/0.57              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.21/0.57         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.21/0.57             sk_H))),
% 0.21/0.57      inference('demod', [status(thm)], ['32', '39'])).
% 0.21/0.57  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
