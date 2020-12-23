%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VxdBoPuuP5

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:19 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 109 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  816 (1376 expanded)
%              Number of equality atoms :   49 (  91 expanded)
%              Maximal formula depth    :   20 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf(t113_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ ( k2_xboole_0 @ B @ C ) @ D ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t113_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X4 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X11 @ X12 @ X13 ) @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t113_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) @ X3 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t113_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) @ X4 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) @ X2 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k1_tarski @ X1 ) ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k2_xboole_0 @ ( k2_tarski @ X3 @ X1 ) @ ( k1_tarski @ X0 ) ) ) @ X2 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k1_tarski @ X3 ) ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k1_enumset1 @ X3 @ X1 @ X0 ) ) @ X2 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k1_tarski @ X3 ) ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k1_tarski @ X3 ) ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_tarski @ X2 ) ) @ ( k1_enumset1 @ X1 @ X0 @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['11','22'])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X8 @ X9 @ X10 )
      = ( k2_xboole_0 @ ( k2_tarski @ X8 @ X9 ) @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X1 @ X0 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k1_tarski @ X3 ) ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_tarski @ X2 ) ) @ ( k1_enumset1 @ X1 @ X0 @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X11 @ X12 @ X13 ) @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X1 @ X0 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X4 @ ( k1_tarski @ X3 ) ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X7 ) )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_tarski @ X2 ) ) @ ( k1_enumset1 @ X1 @ X0 @ X7 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X15 @ X16 @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X7 ) )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k1_enumset1 @ X1 @ X0 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('36',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k6_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 ) @ ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X7 ) )
      = ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VxdBoPuuP5
% 0.14/0.37  % Computer   : n015.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 12:31:38 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.60/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.78  % Solved by: fo/fo7.sh
% 0.60/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.78  % done 70 iterations in 0.309s
% 0.60/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.78  % SZS output start Refutation
% 0.60/0.78  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.60/0.78                                           $i > $i).
% 0.60/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.78  thf(sk_G_type, type, sk_G: $i).
% 0.60/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.78  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.60/0.78  thf(sk_H_type, type, sk_H: $i).
% 0.60/0.78  thf(sk_F_type, type, sk_F: $i).
% 0.60/0.78  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.60/0.78  thf(sk_E_type, type, sk_E: $i).
% 0.60/0.78  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.60/0.78  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.60/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.78  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.78  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.60/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.78  thf(t68_enumset1, conjecture,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.60/0.78     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.60/0.78       ( k2_xboole_0 @
% 0.60/0.78         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.60/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.78    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.60/0.78        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.60/0.78          ( k2_xboole_0 @
% 0.60/0.78            ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )),
% 0.60/0.78    inference('cnf.neg', [status(esa)], [t68_enumset1])).
% 0.60/0.78  thf('0', plain,
% 0.60/0.78      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.60/0.78         != (k2_xboole_0 @ 
% 0.60/0.78             (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G) @ 
% 0.60/0.78             (k1_tarski @ sk_H)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(t43_enumset1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.60/0.78       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.60/0.78  thf('1', plain,
% 0.60/0.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.78         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.60/0.78           = (k2_xboole_0 @ (k2_tarski @ X8 @ X9) @ (k1_tarski @ X10)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.60/0.78  thf(t41_enumset1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( k2_tarski @ A @ B ) =
% 0.60/0.78       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.60/0.78  thf('2', plain,
% 0.60/0.78      (![X6 : $i, X7 : $i]:
% 0.60/0.78         ((k2_tarski @ X6 @ X7)
% 0.60/0.78           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X7)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.60/0.78  thf('3', plain,
% 0.60/0.78      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.78         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.60/0.78           = (k2_xboole_0 @ (k2_tarski @ X8 @ X9) @ (k1_tarski @ X10)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.60/0.78  thf(t113_xboole_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) @ D ) =
% 0.60/0.78       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ ( k2_xboole_0 @ B @ C ) @ D ) ) ))).
% 0.60/0.78  thf('4', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.78         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2) @ X3)
% 0.60/0.78           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t113_xboole_1])).
% 0.60/0.78  thf('5', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.78         ((k2_xboole_0 @ (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4) @ X3)
% 0.60/0.78           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.60/0.78              (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X4) @ X3)))),
% 0.60/0.78      inference('sup+', [status(thm)], ['3', '4'])).
% 0.60/0.78  thf('6', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.78         ((k2_xboole_0 @ 
% 0.60/0.78           (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X1) @ (k1_tarski @ X0)) @ X2)
% 0.60/0.78           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.60/0.78              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.60/0.78      inference('sup+', [status(thm)], ['2', '5'])).
% 0.60/0.78  thf(t46_enumset1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.79     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.60/0.79       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.60/0.79  thf('7', plain,
% 0.60/0.79      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.60/0.79         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.60/0.79           = (k2_xboole_0 @ (k1_enumset1 @ X11 @ X12 @ X13) @ (k1_tarski @ X14)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.60/0.79  thf('8', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X1 @ X0) @ X2)
% 0.60/0.79           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.60/0.79              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.60/0.79      inference('demod', [status(thm)], ['6', '7'])).
% 0.60/0.79  thf('9', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.60/0.79           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.60/0.79              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['1', '8'])).
% 0.60/0.79  thf(t50_enumset1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.60/0.79     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.60/0.79       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.60/0.79  thf('10', plain,
% 0.60/0.79      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.60/0.79         ((k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.60/0.79           = (k2_xboole_0 @ (k2_enumset1 @ X15 @ X16 @ X17 @ X18) @ 
% 0.60/0.79              (k1_tarski @ X19)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.60/0.79  thf('11', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.79         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.60/0.79           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.60/0.79              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['9', '10'])).
% 0.60/0.79  thf('12', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.79         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.60/0.79           = (k2_xboole_0 @ (k2_tarski @ X8 @ X9) @ (k1_tarski @ X10)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.60/0.79  thf('13', plain,
% 0.60/0.79      (![X6 : $i, X7 : $i]:
% 0.60/0.79         ((k2_tarski @ X6 @ X7)
% 0.60/0.79           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X7)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.60/0.79  thf('14', plain,
% 0.60/0.79      (![X6 : $i, X7 : $i]:
% 0.60/0.79         ((k2_tarski @ X6 @ X7)
% 0.60/0.79           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k1_tarski @ X7)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.60/0.79  thf('15', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2) @ X3)
% 0.60/0.79           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t113_xboole_1])).
% 0.60/0.79  thf('16', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2) @ X3)
% 0.60/0.79           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ X3)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t113_xboole_1])).
% 0.60/0.79  thf('17', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ 
% 0.60/0.79           (k2_xboole_0 @ X3 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0)) @ 
% 0.60/0.79           X4)
% 0.60/0.79           = (k2_xboole_0 @ (k2_xboole_0 @ X3 @ X2) @ 
% 0.60/0.79              (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X4)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['15', '16'])).
% 0.60/0.79  thf('18', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ 
% 0.60/0.79           (k2_xboole_0 @ X4 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)) @ X2)
% 0.60/0.79           = (k2_xboole_0 @ (k2_xboole_0 @ X4 @ (k1_tarski @ X1)) @ 
% 0.60/0.79              (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X3) @ X2)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['14', '17'])).
% 0.60/0.79  thf('19', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ 
% 0.60/0.79           (k2_xboole_0 @ X4 @ 
% 0.60/0.79            (k2_xboole_0 @ (k2_tarski @ X3 @ X1) @ (k1_tarski @ X0))) @ 
% 0.60/0.79           X2)
% 0.60/0.79           = (k2_xboole_0 @ (k2_xboole_0 @ X4 @ (k1_tarski @ X3)) @ 
% 0.60/0.79              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['13', '18'])).
% 0.60/0.79  thf('20', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.79         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.60/0.79           = (k2_xboole_0 @ (k2_tarski @ X8 @ X9) @ (k1_tarski @ X10)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.60/0.79  thf('21', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ (k1_enumset1 @ X3 @ X1 @ X0)) @ X2)
% 0.60/0.79           = (k2_xboole_0 @ (k2_xboole_0 @ X4 @ (k1_tarski @ X3)) @ 
% 0.60/0.79              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.60/0.79      inference('demod', [status(thm)], ['19', '20'])).
% 0.60/0.79  thf('22', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ (k1_enumset1 @ X3 @ X2 @ X1)) @ 
% 0.60/0.79           (k1_tarski @ X0))
% 0.60/0.79           = (k2_xboole_0 @ (k2_xboole_0 @ X4 @ (k1_tarski @ X3)) @ 
% 0.60/0.79              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['12', '21'])).
% 0.60/0.79  thf('23', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.60/0.79           (k1_tarski @ X5))
% 0.60/0.79           = (k2_xboole_0 @ 
% 0.60/0.79              (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ (k1_tarski @ X2)) @ 
% 0.60/0.79              (k1_enumset1 @ X1 @ X0 @ X5)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['11', '22'])).
% 0.60/0.79  thf(t55_enumset1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.60/0.79     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.60/0.79       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 0.60/0.79  thf('24', plain,
% 0.60/0.79      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.60/0.79         ((k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25)
% 0.60/0.79           = (k2_xboole_0 @ (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.60/0.79              (k1_tarski @ X25)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t55_enumset1])).
% 0.60/0.79  thf('25', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.79         ((k1_enumset1 @ X8 @ X9 @ X10)
% 0.60/0.79           = (k2_xboole_0 @ (k2_tarski @ X8 @ X9) @ (k1_tarski @ X10)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.60/0.79  thf('26', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.79         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.60/0.79           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.60/0.79              (k1_enumset1 @ X1 @ X0 @ X5)))),
% 0.60/0.79      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.60/0.79  thf('27', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ (k1_enumset1 @ X3 @ X2 @ X1)) @ 
% 0.60/0.79           (k1_tarski @ X0))
% 0.60/0.79           = (k2_xboole_0 @ (k2_xboole_0 @ X4 @ (k1_tarski @ X3)) @ 
% 0.60/0.79              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['12', '21'])).
% 0.60/0.79  thf('28', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.60/0.79           (k1_tarski @ X6))
% 0.60/0.79           = (k2_xboole_0 @ 
% 0.60/0.79              (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ (k1_tarski @ X2)) @ 
% 0.60/0.79              (k1_enumset1 @ X1 @ X0 @ X6)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['26', '27'])).
% 0.60/0.79  thf(t61_enumset1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.60/0.79     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.60/0.79       ( k2_xboole_0 @
% 0.60/0.79         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.60/0.79  thf('29', plain,
% 0.60/0.79      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.60/0.79         ((k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.60/0.79           = (k2_xboole_0 @ 
% 0.60/0.79              (k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31) @ 
% 0.60/0.79              (k1_tarski @ X32)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.60/0.79  thf('30', plain,
% 0.60/0.79      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.60/0.79         ((k2_enumset1 @ X11 @ X12 @ X13 @ X14)
% 0.60/0.79           = (k2_xboole_0 @ (k1_enumset1 @ X11 @ X12 @ X13) @ (k1_tarski @ X14)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.60/0.79  thf('31', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.79         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.60/0.79           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.60/0.79              (k1_enumset1 @ X1 @ X0 @ X6)))),
% 0.60/0.79      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.60/0.79  thf('32', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k2_xboole_0 @ X4 @ (k1_enumset1 @ X3 @ X2 @ X1)) @ 
% 0.60/0.79           (k1_tarski @ X0))
% 0.60/0.79           = (k2_xboole_0 @ (k2_xboole_0 @ X4 @ (k1_tarski @ X3)) @ 
% 0.60/0.79              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['12', '21'])).
% 0.60/0.79  thf('33', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.60/0.79           (k1_tarski @ X7))
% 0.60/0.79           = (k2_xboole_0 @ 
% 0.60/0.79              (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 0.60/0.79               (k1_tarski @ X2)) @ 
% 0.60/0.79              (k1_enumset1 @ X1 @ X0 @ X7)))),
% 0.60/0.79      inference('sup+', [status(thm)], ['31', '32'])).
% 0.60/0.79  thf('34', plain,
% 0.60/0.79      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.60/0.79         ((k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.60/0.79           = (k2_xboole_0 @ (k2_enumset1 @ X15 @ X16 @ X17 @ X18) @ 
% 0.60/0.79              (k1_tarski @ X19)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.60/0.79  thf('35', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.60/0.79           (k1_tarski @ X7))
% 0.60/0.79           = (k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.60/0.79              (k1_enumset1 @ X1 @ X0 @ X7)))),
% 0.60/0.79      inference('demod', [status(thm)], ['33', '34'])).
% 0.60/0.79  thf(t66_enumset1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.60/0.79     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.60/0.79       ( k2_xboole_0 @
% 0.60/0.79         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 0.60/0.79  thf('36', plain,
% 0.60/0.79      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, 
% 0.60/0.79         X48 : $i]:
% 0.60/0.79         ((k6_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.60/0.79           = (k2_xboole_0 @ (k3_enumset1 @ X41 @ X42 @ X43 @ X44 @ X45) @ 
% 0.60/0.79              (k1_enumset1 @ X46 @ X47 @ X48)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t66_enumset1])).
% 0.60/0.79  thf('37', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.79         ((k2_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.60/0.79           (k1_tarski @ X7))
% 0.60/0.79           = (k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X7))),
% 0.60/0.79      inference('demod', [status(thm)], ['35', '36'])).
% 0.60/0.79  thf('38', plain,
% 0.60/0.79      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.60/0.79         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.60/0.79             sk_H))),
% 0.60/0.79      inference('demod', [status(thm)], ['0', '37'])).
% 0.60/0.79  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 0.60/0.79  
% 0.60/0.79  % SZS output end Refutation
% 0.60/0.79  
% 0.60/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
