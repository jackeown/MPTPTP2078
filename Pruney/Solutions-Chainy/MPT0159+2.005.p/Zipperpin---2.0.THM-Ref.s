%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6q8q5jX7nc

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:39 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 153 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   19
%              Number of atoms          :  825 (1627 expanded)
%              Number of equality atoms :   59 ( 137 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      = ( k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X46: $i] :
      ( ( k2_tarski @ X46 @ X46 )
      = ( k1_tarski @ X46 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X46: $i] :
      ( ( k2_tarski @ X46 @ X46 )
      = ( k1_tarski @ X46 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(l68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l68_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      = ( k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X46: $i] :
      ( ( k2_tarski @ X46 @ X46 )
      = ( k1_tarski @ X46 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(t56_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','25'])).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      = ( k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('43',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k6_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_xboole_0 @ ( k1_tarski @ X38 ) @ ( k5_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t56_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G )
 != ( k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['0','41','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6q8q5jX7nc
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.62/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.83  % Solved by: fo/fo7.sh
% 0.62/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.83  % done 676 iterations in 0.377s
% 0.62/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.83  % SZS output start Refutation
% 0.62/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.83  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.62/0.83                                           $i > $i).
% 0.62/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.83  thf(sk_E_type, type, sk_E: $i).
% 0.62/0.83  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.62/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.83  thf(sk_D_type, type, sk_D: $i).
% 0.62/0.83  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.62/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.83  thf(sk_G_type, type, sk_G: $i).
% 0.62/0.83  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.62/0.83  thf(sk_F_type, type, sk_F: $i).
% 0.62/0.83  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.62/0.83  thf(t75_enumset1, conjecture,
% 0.62/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.62/0.83     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.62/0.83       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.62/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.83    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.62/0.83        ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.62/0.83          ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )),
% 0.62/0.83    inference('cnf.neg', [status(esa)], [t75_enumset1])).
% 0.62/0.83  thf('0', plain,
% 0.62/0.83      (((k6_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.62/0.83         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf(t74_enumset1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.62/0.83     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.62/0.83       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.62/0.83  thf('1', plain,
% 0.62/0.83      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 0.62/0.83           = (k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52))),
% 0.62/0.83      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.62/0.83  thf(t69_enumset1, axiom,
% 0.62/0.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.62/0.83  thf('2', plain, (![X46 : $i]: ((k2_tarski @ X46 @ X46) = (k1_tarski @ X46))),
% 0.62/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.83  thf(t42_enumset1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.62/0.83       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.62/0.83  thf('3', plain,
% 0.62/0.83      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X17 @ X18 @ X19)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X17) @ (k2_tarski @ X18 @ X19)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.62/0.83  thf('4', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.83  thf(t41_enumset1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( k2_tarski @ A @ B ) =
% 0.62/0.83       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.62/0.83  thf('5', plain,
% 0.62/0.83      (![X15 : $i, X16 : $i]:
% 0.62/0.83         ((k2_tarski @ X15 @ X16)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.62/0.83  thf('6', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['4', '5'])).
% 0.62/0.83  thf('7', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['4', '5'])).
% 0.62/0.83  thf(t46_enumset1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.83     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.62/0.83       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.62/0.83  thf('8', plain,
% 0.62/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.62/0.83         ((k2_enumset1 @ X20 @ X21 @ X22 @ X23)
% 0.62/0.83           = (k2_xboole_0 @ (k1_enumset1 @ X20 @ X21 @ X22) @ (k1_tarski @ X23)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.62/0.83  thf('9', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.83         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2)
% 0.62/0.83           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['7', '8'])).
% 0.62/0.83  thf('10', plain,
% 0.62/0.83      (![X46 : $i]: ((k2_tarski @ X46 @ X46) = (k1_tarski @ X46))),
% 0.62/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.83  thf('11', plain,
% 0.62/0.83      (![X15 : $i, X16 : $i]:
% 0.62/0.83         ((k2_tarski @ X15 @ X16)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X16)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.62/0.83  thf('12', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k2_tarski @ X0 @ X1)
% 0.62/0.83           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['10', '11'])).
% 0.62/0.83  thf('13', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['9', '12'])).
% 0.62/0.83  thf('14', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['4', '5'])).
% 0.62/0.83  thf(l68_enumset1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.62/0.83     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.62/0.83       ( k2_xboole_0 @
% 0.62/0.83         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_enumset1 @ E @ F @ G ) ) ))).
% 0.62/0.83  thf('15', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.62/0.83           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3) @ 
% 0.62/0.83              (k1_enumset1 @ X4 @ X5 @ X6)))),
% 0.62/0.83      inference('cnf', [status(esa)], [l68_enumset1])).
% 0.62/0.83  thf('16', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 0.62/0.83           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.62/0.83              (k2_tarski @ X1 @ X0)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['14', '15'])).
% 0.62/0.83  thf('17', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X1 @ X1 @ X1 @ X0 @ X3 @ X2 @ X2)
% 0.62/0.83           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['13', '16'])).
% 0.62/0.83  thf('18', plain,
% 0.62/0.83      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 0.62/0.83           = (k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52))),
% 0.62/0.83      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.62/0.83  thf('19', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.62/0.83         ((k4_enumset1 @ X1 @ X1 @ X0 @ X3 @ X2 @ X2)
% 0.62/0.83           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X3 @ X2)))),
% 0.62/0.83      inference('demod', [status(thm)], ['17', '18'])).
% 0.62/0.83  thf('20', plain,
% 0.62/0.83      (![X46 : $i]: ((k2_tarski @ X46 @ X46) = (k1_tarski @ X46))),
% 0.62/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.83  thf('21', plain,
% 0.62/0.83      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X17 @ X18 @ X19)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X17) @ (k2_tarski @ X18 @ X19)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.62/0.83  thf('22', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X0 @ X2 @ X1)
% 0.62/0.83           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['20', '21'])).
% 0.62/0.83  thf('23', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.62/0.83           = (k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['19', '22'])).
% 0.62/0.83  thf(t56_enumset1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.62/0.83     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.62/0.83       ( k2_xboole_0 @
% 0.62/0.83         ( k1_tarski @ A ) @ ( k4_enumset1 @ B @ C @ D @ E @ F @ G ) ) ))).
% 0.62/0.83  thf('24', plain,
% 0.62/0.83      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X24) @ 
% 0.62/0.83              (k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.62/0.83  thf('25', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['23', '24'])).
% 0.62/0.83  thf('26', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['6', '25'])).
% 0.62/0.83  thf('27', plain,
% 0.62/0.83      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X17 @ X18 @ X19)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X17) @ (k2_tarski @ X18 @ X19)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.62/0.83  thf('28', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X2 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0)
% 0.62/0.83           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['26', '27'])).
% 0.62/0.83  thf('29', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k4_enumset1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0)
% 0.62/0.83           = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['1', '28'])).
% 0.62/0.83  thf('30', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.62/0.83           = (k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0))),
% 0.62/0.83      inference('sup+', [status(thm)], ['19', '22'])).
% 0.62/0.83  thf('31', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['29', '30'])).
% 0.62/0.83  thf('32', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['4', '5'])).
% 0.62/0.83  thf('33', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['31', '32'])).
% 0.62/0.83  thf('34', plain,
% 0.62/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.62/0.83         ((k2_enumset1 @ X20 @ X21 @ X22 @ X23)
% 0.62/0.83           = (k2_xboole_0 @ (k1_enumset1 @ X20 @ X21 @ X22) @ (k1_tarski @ X23)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.62/0.83  thf('35', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.83         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.62/0.83           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['33', '34'])).
% 0.62/0.83  thf('36', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.83         ((k2_enumset1 @ X1 @ X0 @ X0 @ X2)
% 0.62/0.83           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['7', '8'])).
% 0.62/0.83  thf(l75_enumset1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.62/0.83     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.62/0.83       ( k2_xboole_0 @
% 0.62/0.83         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.62/0.83  thf('37', plain,
% 0.62/0.83      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.62/0.83         X14 : $i]:
% 0.62/0.83         ((k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.62/0.83           = (k2_xboole_0 @ (k2_enumset1 @ X7 @ X8 @ X9 @ X10) @ 
% 0.62/0.83              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 0.62/0.83      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.62/0.83  thf('38', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.62/0.83         ((k6_enumset1 @ X2 @ X1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.62/0.83           = (k2_xboole_0 @ 
% 0.62/0.83              (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)) @ 
% 0.62/0.83              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['36', '37'])).
% 0.62/0.83  thf('39', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.62/0.83         ((k6_enumset1 @ X2 @ X1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.62/0.83           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ 
% 0.62/0.83              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['35', '38'])).
% 0.62/0.83  thf('40', plain,
% 0.62/0.83      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.62/0.83         X14 : $i]:
% 0.62/0.83         ((k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.62/0.83           = (k2_xboole_0 @ (k2_enumset1 @ X7 @ X8 @ X9 @ X10) @ 
% 0.62/0.83              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 0.62/0.83      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.62/0.83  thf('41', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.62/0.83         ((k6_enumset1 @ X2 @ X1 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.62/0.83           = (k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3))),
% 0.62/0.83      inference('demod', [status(thm)], ['39', '40'])).
% 0.62/0.83  thf('42', plain,
% 0.62/0.83      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 0.62/0.83           = (k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52))),
% 0.62/0.83      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.62/0.83  thf(t62_enumset1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.62/0.83     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.62/0.83       ( k2_xboole_0 @
% 0.62/0.83         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.62/0.83  thf('43', plain,
% 0.62/0.83      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.62/0.83         X45 : $i]:
% 0.62/0.83         ((k6_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X38) @ 
% 0.62/0.83              (k5_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.62/0.83  thf('44', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.62/0.83         ((k6_enumset1 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X6) @ 
% 0.62/0.83              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.62/0.83      inference('sup+', [status(thm)], ['42', '43'])).
% 0.62/0.83  thf('45', plain,
% 0.62/0.83      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.62/0.83         ((k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.62/0.83           = (k2_xboole_0 @ (k1_tarski @ X24) @ 
% 0.62/0.83              (k4_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t56_enumset1])).
% 0.62/0.83  thf('46', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.62/0.83         ((k6_enumset1 @ X6 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.62/0.83           = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.62/0.83      inference('demod', [status(thm)], ['44', '45'])).
% 0.62/0.83  thf('47', plain,
% 0.62/0.83      (((k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G)
% 0.62/0.83         != (k5_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G))),
% 0.62/0.83      inference('demod', [status(thm)], ['0', '41', '46'])).
% 0.62/0.83  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.62/0.83  
% 0.62/0.83  % SZS output end Refutation
% 0.62/0.83  
% 0.67/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
