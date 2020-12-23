%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cWPFVNHMoZ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:03 EST 2020

% Result     : Theorem 14.66s
% Output     : Refutation 14.66s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 306 expanded)
%              Number of leaves         :   25 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          : 1145 (3643 expanded)
%              Number of equality atoms :   88 ( 292 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t104_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ C @ B @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ C @ B @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t104_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k6_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) @ ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k6_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) @ ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X4 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('11',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k5_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 ) @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('17',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 )
      = ( k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('18',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k3_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf(t99_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf('22',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k1_enumset1 @ X54 @ X53 @ X55 )
      = ( k1_enumset1 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf('23',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( k2_enumset1 @ X35 @ X35 @ X36 @ X37 )
      = ( k1_enumset1 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('32',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( k1_enumset1 @ X54 @ X53 @ X55 )
      = ( k1_enumset1 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_enumset1 @ X0 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X2 @ X0 )
      = ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X2 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_enumset1 @ X0 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','45','46','47'])).

thf('49',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k6_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k4_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 )
      = ( k3_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('55',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('56',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','57','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','57','66'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','67','68'])).

thf('70',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 )
      = ( k2_enumset1 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','73'])).

thf('75',plain,(
    $false ),
    inference(simplify,[status(thm)],['74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cWPFVNHMoZ
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:00:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 14.66/14.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.66/14.90  % Solved by: fo/fo7.sh
% 14.66/14.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.66/14.90  % done 7688 iterations in 14.401s
% 14.66/14.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.66/14.90  % SZS output start Refutation
% 14.66/14.90  thf(sk_D_type, type, sk_D: $i).
% 14.66/14.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 14.66/14.90  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 14.66/14.90  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 14.66/14.90  thf(sk_B_type, type, sk_B: $i).
% 14.66/14.90  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 14.66/14.90                                           $i > $i).
% 14.66/14.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 14.66/14.90  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 14.66/14.90  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 14.66/14.90  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 14.66/14.90  thf(sk_C_type, type, sk_C: $i).
% 14.66/14.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 14.66/14.90  thf(sk_A_type, type, sk_A: $i).
% 14.66/14.90  thf(t104_enumset1, conjecture,
% 14.66/14.90    (![A:$i,B:$i,C:$i,D:$i]:
% 14.66/14.90     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 14.66/14.90  thf(zf_stmt_0, negated_conjecture,
% 14.66/14.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 14.66/14.90        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ) )),
% 14.66/14.90    inference('cnf.neg', [status(esa)], [t104_enumset1])).
% 14.66/14.90  thf('0', plain,
% 14.66/14.90      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 14.66/14.90         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 14.66/14.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.66/14.90  thf(t71_enumset1, axiom,
% 14.66/14.90    (![A:$i,B:$i,C:$i]:
% 14.66/14.90     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 14.66/14.90  thf('1', plain,
% 14.66/14.90      (![X35 : $i, X36 : $i, X37 : $i]:
% 14.66/14.90         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 14.66/14.90           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 14.66/14.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 14.66/14.90  thf(l75_enumset1, axiom,
% 14.66/14.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 14.66/14.90     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 14.66/14.90       ( k2_xboole_0 @
% 14.66/14.90         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 14.66/14.90  thf('2', plain,
% 14.66/14.90      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, 
% 14.66/14.90         X11 : $i]:
% 14.66/14.90         ((k6_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 14.66/14.90           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X5 @ X6 @ X7) @ 
% 14.66/14.90              (k2_enumset1 @ X8 @ X9 @ X10 @ X11)))),
% 14.66/14.90      inference('cnf', [status(esa)], [l75_enumset1])).
% 14.66/14.90  thf('3', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 14.66/14.90         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X2 @ X1 @ X0)
% 14.66/14.90           = (k2_xboole_0 @ (k2_enumset1 @ X6 @ X5 @ X4 @ X3) @ 
% 14.66/14.90              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['1', '2'])).
% 14.66/14.90  thf(t70_enumset1, axiom,
% 14.66/14.90    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 14.66/14.90  thf('4', plain,
% 14.66/14.90      (![X33 : $i, X34 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 14.66/14.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 14.66/14.90  thf('5', plain,
% 14.66/14.90      (![X35 : $i, X36 : $i, X37 : $i]:
% 14.66/14.90         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 14.66/14.90           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 14.66/14.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 14.66/14.90  thf('6', plain,
% 14.66/14.90      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, 
% 14.66/14.90         X11 : $i]:
% 14.66/14.90         ((k6_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 @ X10 @ X11)
% 14.66/14.90           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X5 @ X6 @ X7) @ 
% 14.66/14.90              (k2_enumset1 @ X8 @ X9 @ X10 @ X11)))),
% 14.66/14.90      inference('cnf', [status(esa)], [l75_enumset1])).
% 14.66/14.90  thf('7', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 14.66/14.90         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 14.66/14.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 14.66/14.90              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['5', '6'])).
% 14.66/14.90  thf('8', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 14.66/14.90         ((k6_enumset1 @ X1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 14.66/14.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 14.66/14.90              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['4', '7'])).
% 14.66/14.90  thf('9', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.66/14.90         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X4 @ X4 @ X3) @ 
% 14.66/14.90           (k1_enumset1 @ X2 @ X1 @ X0))
% 14.66/14.90           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 14.66/14.90              (k2_enumset1 @ X2 @ X2 @ X1 @ X0)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['3', '8'])).
% 14.66/14.90  thf(t72_enumset1, axiom,
% 14.66/14.90    (![A:$i,B:$i,C:$i,D:$i]:
% 14.66/14.90     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 14.66/14.90  thf('10', plain,
% 14.66/14.90      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 14.66/14.90           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 14.66/14.90      inference('cnf', [status(esa)], [t72_enumset1])).
% 14.66/14.90  thf('11', plain,
% 14.66/14.90      (![X35 : $i, X36 : $i, X37 : $i]:
% 14.66/14.90         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 14.66/14.90           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 14.66/14.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 14.66/14.90  thf('12', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['10', '11'])).
% 14.66/14.90  thf(t69_enumset1, axiom,
% 14.66/14.90    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 14.66/14.90  thf('13', plain,
% 14.66/14.90      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 14.66/14.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 14.66/14.90  thf('14', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['10', '11'])).
% 14.66/14.90  thf(t60_enumset1, axiom,
% 14.66/14.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 14.66/14.90     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 14.66/14.90       ( k2_xboole_0 @
% 14.66/14.90         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 14.66/14.90  thf('15', plain,
% 14.66/14.90      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 14.66/14.90         ((k5_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23)
% 14.66/14.90           = (k2_xboole_0 @ (k3_enumset1 @ X17 @ X18 @ X19 @ X20 @ X21) @ 
% 14.66/14.90              (k2_tarski @ X22 @ X23)))),
% 14.66/14.90      inference('cnf', [status(esa)], [t60_enumset1])).
% 14.66/14.90  thf('16', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.66/14.90         ((k5_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X4 @ X3)
% 14.66/14.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 14.66/14.90              (k2_tarski @ X4 @ X3)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['14', '15'])).
% 14.66/14.90  thf(t74_enumset1, axiom,
% 14.66/14.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 14.66/14.90     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 14.66/14.90       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 14.66/14.90  thf('17', plain,
% 14.66/14.90      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 14.66/14.90         ((k5_enumset1 @ X47 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52)
% 14.66/14.90           = (k4_enumset1 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52))),
% 14.66/14.90      inference('cnf', [status(esa)], [t74_enumset1])).
% 14.66/14.90  thf(t73_enumset1, axiom,
% 14.66/14.90    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 14.66/14.90     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 14.66/14.90       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 14.66/14.90  thf('18', plain,
% 14.66/14.90      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 14.66/14.90         ((k4_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46)
% 14.66/14.90           = (k3_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 14.66/14.90      inference('cnf', [status(esa)], [t73_enumset1])).
% 14.66/14.90  thf('19', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.66/14.90         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 14.66/14.90           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['17', '18'])).
% 14.66/14.90  thf('20', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X2 @ X1 @ X0 @ X4 @ X3)
% 14.66/14.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 14.66/14.90              (k2_tarski @ X4 @ X3)))),
% 14.66/14.90      inference('demod', [status(thm)], ['16', '19'])).
% 14.66/14.90  thf('21', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 14.66/14.90           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['13', '20'])).
% 14.66/14.90  thf(t99_enumset1, axiom,
% 14.66/14.90    (![A:$i,B:$i,C:$i]:
% 14.66/14.90     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 14.66/14.90  thf('22', plain,
% 14.66/14.90      (![X53 : $i, X54 : $i, X55 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X54 @ X53 @ X55) = (k1_enumset1 @ X53 @ X54 @ X55))),
% 14.66/14.90      inference('cnf', [status(esa)], [t99_enumset1])).
% 14.66/14.90  thf('23', plain,
% 14.66/14.90      (![X35 : $i, X36 : $i, X37 : $i]:
% 14.66/14.90         ((k2_enumset1 @ X35 @ X35 @ X36 @ X37)
% 14.66/14.90           = (k1_enumset1 @ X35 @ X36 @ X37))),
% 14.66/14.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 14.66/14.90  thf(t50_enumset1, axiom,
% 14.66/14.90    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 14.66/14.90     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 14.66/14.90       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 14.66/14.90  thf('24', plain,
% 14.66/14.90      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16)
% 14.66/14.90           = (k2_xboole_0 @ (k2_enumset1 @ X12 @ X13 @ X14 @ X15) @ 
% 14.66/14.90              (k1_tarski @ X16)))),
% 14.66/14.90      inference('cnf', [status(esa)], [t50_enumset1])).
% 14.66/14.90  thf('25', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 14.66/14.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['23', '24'])).
% 14.66/14.90  thf('26', plain,
% 14.66/14.90      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 14.66/14.90           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 14.66/14.90      inference('cnf', [status(esa)], [t72_enumset1])).
% 14.66/14.90  thf('27', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 14.66/14.90           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['25', '26'])).
% 14.66/14.90  thf('28', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 14.66/14.90           = (k2_enumset1 @ X1 @ X2 @ X0 @ X3))),
% 14.66/14.90      inference('sup+', [status(thm)], ['22', '27'])).
% 14.66/14.90  thf('29', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 14.66/14.90           = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 14.66/14.90      inference('demod', [status(thm)], ['21', '28'])).
% 14.66/14.90  thf('30', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['12', '29'])).
% 14.66/14.90  thf('31', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['10', '11'])).
% 14.66/14.90  thf('32', plain,
% 14.66/14.90      (![X53 : $i, X54 : $i, X55 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X54 @ X53 @ X55) = (k1_enumset1 @ X53 @ X54 @ X55))),
% 14.66/14.90      inference('cnf', [status(esa)], [t99_enumset1])).
% 14.66/14.90  thf('33', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X1 @ X2 @ X0) = (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['31', '32'])).
% 14.66/14.90  thf('34', plain,
% 14.66/14.90      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 14.66/14.90           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 14.66/14.90      inference('cnf', [status(esa)], [t72_enumset1])).
% 14.66/14.90  thf('35', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X1 @ X2 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['33', '34'])).
% 14.66/14.90  thf('36', plain,
% 14.66/14.90      (![X33 : $i, X34 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 14.66/14.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 14.66/14.90  thf('37', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 14.66/14.90      inference('demod', [status(thm)], ['30', '35', '36'])).
% 14.66/14.90  thf('38', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 14.66/14.90           = (k2_enumset1 @ X1 @ X2 @ X0 @ X3))),
% 14.66/14.90      inference('sup+', [status(thm)], ['22', '27'])).
% 14.66/14.90  thf('39', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 14.66/14.90           = (k2_enumset1 @ X0 @ X1 @ X0 @ X2))),
% 14.66/14.90      inference('sup+', [status(thm)], ['37', '38'])).
% 14.66/14.90  thf('40', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X1 @ X2 @ X0) = (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['31', '32'])).
% 14.66/14.90  thf('41', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 14.66/14.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['23', '24'])).
% 14.66/14.90  thf('42', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X2 @ X1 @ X0)
% 14.66/14.90           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X2) @ (k1_tarski @ X0)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['40', '41'])).
% 14.66/14.90  thf('43', plain,
% 14.66/14.90      (![X33 : $i, X34 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 14.66/14.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 14.66/14.90  thf('44', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X2 @ X1 @ X0)
% 14.66/14.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X2) @ (k1_tarski @ X0)))),
% 14.66/14.90      inference('demod', [status(thm)], ['42', '43'])).
% 14.66/14.90  thf('45', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X0 @ X1 @ X2) = (k2_enumset1 @ X0 @ X1 @ X0 @ X2))),
% 14.66/14.90      inference('demod', [status(thm)], ['39', '44'])).
% 14.66/14.90  thf('46', plain,
% 14.66/14.90      (![X33 : $i, X34 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 14.66/14.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 14.66/14.90  thf('47', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X1 @ X2 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['33', '34'])).
% 14.66/14.90  thf('48', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.66/14.90         ((k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 14.66/14.90           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 14.66/14.90              (k1_enumset1 @ X1 @ X2 @ X0)))),
% 14.66/14.90      inference('demod', [status(thm)], ['9', '45', '46', '47'])).
% 14.66/14.90  thf('49', plain,
% 14.66/14.90      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 14.66/14.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 14.66/14.90  thf(t67_enumset1, axiom,
% 14.66/14.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 14.66/14.90     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 14.66/14.90       ( k2_xboole_0 @
% 14.66/14.90         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 14.66/14.90  thf('50', plain,
% 14.66/14.90      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 14.66/14.90         X31 : $i]:
% 14.66/14.90         ((k6_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 14.66/14.90           = (k2_xboole_0 @ 
% 14.66/14.90              (k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29) @ 
% 14.66/14.90              (k2_tarski @ X30 @ X31)))),
% 14.66/14.90      inference('cnf', [status(esa)], [t67_enumset1])).
% 14.66/14.90  thf('51', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 14.66/14.90         ((k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 14.66/14.90           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 14.66/14.90              (k1_tarski @ X0)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['49', '50'])).
% 14.66/14.90  thf('52', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 14.66/14.90         ((k6_enumset1 @ X1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 14.66/14.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 14.66/14.90              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['4', '7'])).
% 14.66/14.90  thf('53', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.66/14.90         ((k2_xboole_0 @ (k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 14.66/14.90           (k1_tarski @ X0))
% 14.66/14.90           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 14.66/14.90              (k2_enumset1 @ X2 @ X1 @ X0 @ X0)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['51', '52'])).
% 14.66/14.90  thf('54', plain,
% 14.66/14.90      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 14.66/14.90         ((k4_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46)
% 14.66/14.90           = (k3_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46))),
% 14.66/14.90      inference('cnf', [status(esa)], [t73_enumset1])).
% 14.66/14.90  thf('55', plain,
% 14.66/14.90      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 14.66/14.90           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 14.66/14.90      inference('cnf', [status(esa)], [t72_enumset1])).
% 14.66/14.90  thf('56', plain,
% 14.66/14.90      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16)
% 14.66/14.90           = (k2_xboole_0 @ (k2_enumset1 @ X12 @ X13 @ X14 @ X15) @ 
% 14.66/14.90              (k1_tarski @ X16)))),
% 14.66/14.90      inference('cnf', [status(esa)], [t50_enumset1])).
% 14.66/14.90  thf('57', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 14.66/14.90           = (k2_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0) @ 
% 14.66/14.90              (k1_tarski @ X4)))),
% 14.66/14.90      inference('sup+', [status(thm)], ['55', '56'])).
% 14.66/14.90  thf('58', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 14.66/14.90           = (k2_enumset1 @ X1 @ X2 @ X0 @ X3))),
% 14.66/14.90      inference('sup+', [status(thm)], ['22', '27'])).
% 14.66/14.90  thf('59', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 14.66/14.90           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['25', '26'])).
% 14.66/14.90  thf('60', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['58', '59'])).
% 14.66/14.90  thf('61', plain,
% 14.66/14.90      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 14.66/14.90           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 14.66/14.90      inference('cnf', [status(esa)], [t72_enumset1])).
% 14.66/14.90  thf('62', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X2 @ X2 @ X3 @ X1 @ X0)
% 14.66/14.90           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['60', '61'])).
% 14.66/14.90  thf('63', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.90         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0)
% 14.66/14.90           = (k2_enumset1 @ X2 @ X3 @ X1 @ X0))),
% 14.66/14.90      inference('demod', [status(thm)], ['21', '28'])).
% 14.66/14.90  thf('64', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k2_enumset1 @ X1 @ X1 @ X2 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['62', '63'])).
% 14.66/14.90  thf('65', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X1 @ X1 @ X2 @ X0))),
% 14.66/14.90      inference('sup+', [status(thm)], ['33', '34'])).
% 14.66/14.90  thf('66', plain,
% 14.66/14.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.66/14.90         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 14.66/14.90      inference('demod', [status(thm)], ['64', '65'])).
% 14.66/14.91  thf('67', plain,
% 14.66/14.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.66/14.91         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 14.66/14.91           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 14.66/14.91              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 14.66/14.91      inference('demod', [status(thm)], ['53', '54', '57', '66'])).
% 14.66/14.91  thf('68', plain,
% 14.66/14.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.66/14.91         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 14.66/14.91           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 14.66/14.91              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 14.66/14.91      inference('demod', [status(thm)], ['53', '54', '57', '66'])).
% 14.66/14.91  thf('69', plain,
% 14.66/14.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 14.66/14.91         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 14.66/14.91           = (k3_enumset1 @ X4 @ X3 @ X1 @ X2 @ X0))),
% 14.66/14.91      inference('demod', [status(thm)], ['48', '67', '68'])).
% 14.66/14.91  thf('70', plain,
% 14.66/14.91      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 14.66/14.91         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 14.66/14.91           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 14.66/14.91      inference('cnf', [status(esa)], [t72_enumset1])).
% 14.66/14.91  thf('71', plain,
% 14.66/14.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.91         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 14.66/14.91           = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 14.66/14.91      inference('sup+', [status(thm)], ['69', '70'])).
% 14.66/14.91  thf('72', plain,
% 14.66/14.91      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 14.66/14.91         ((k3_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41)
% 14.66/14.91           = (k2_enumset1 @ X38 @ X39 @ X40 @ X41))),
% 14.66/14.91      inference('cnf', [status(esa)], [t72_enumset1])).
% 14.66/14.91  thf('73', plain,
% 14.66/14.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 14.66/14.91         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 14.66/14.91      inference('sup+', [status(thm)], ['71', '72'])).
% 14.66/14.91  thf('74', plain,
% 14.66/14.91      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 14.66/14.91         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 14.66/14.91      inference('demod', [status(thm)], ['0', '73'])).
% 14.66/14.91  thf('75', plain, ($false), inference('simplify', [status(thm)], ['74'])).
% 14.66/14.91  
% 14.66/14.91  % SZS output end Refutation
% 14.66/14.91  
% 14.66/14.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
