%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YHhXEbHbmz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:00 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 143 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  862 (1606 expanded)
%              Number of equality atoms :   71 ( 130 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t99_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_enumset1 @ A @ B @ C )
        = ( k1_enumset1 @ B @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t99_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_B @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('5',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k5_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('8',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X1 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('23',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('24',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i,X65: $i,X66: $i,X67: $i] :
      ( ( k6_enumset1 @ X61 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 )
      = ( k5_enumset1 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('25',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k5_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k6_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('34',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','35'])).

thf('37',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','43','44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k1_enumset1 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14','49'])).

thf('51',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('52',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( k1_enumset1 @ X68 @ X70 @ X69 )
      = ( k1_enumset1 @ X68 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( k1_enumset1 @ X68 @ X70 @ X69 )
      = ( k1_enumset1 @ X68 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('56',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','54','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YHhXEbHbmz
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:34:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.48/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.70  % Solved by: fo/fo7.sh
% 0.48/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.70  % done 753 iterations in 0.245s
% 0.48/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.70  % SZS output start Refutation
% 0.48/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.70  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.48/0.70                                           $i > $i).
% 0.48/0.70  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.48/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.70  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.48/0.70  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.48/0.70  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.48/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.70  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.48/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.70  thf(t99_enumset1, conjecture,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 0.48/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.48/0.70        ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ) )),
% 0.48/0.70    inference('cnf.neg', [status(esa)], [t99_enumset1])).
% 0.48/0.70  thf('0', plain,
% 0.48/0.70      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.48/0.70         != (k1_enumset1 @ sk_B @ sk_A @ sk_C))),
% 0.48/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.70  thf(t71_enumset1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.48/0.70  thf('1', plain,
% 0.48/0.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.48/0.70         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.48/0.70           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.48/0.70      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.48/0.70  thf(t70_enumset1, axiom,
% 0.48/0.70    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.48/0.70  thf('2', plain,
% 0.48/0.70      (![X41 : $i, X42 : $i]:
% 0.48/0.70         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.48/0.70      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.48/0.70  thf('3', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['1', '2'])).
% 0.48/0.70  thf(t72_enumset1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.70     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.48/0.70  thf('4', plain,
% 0.48/0.70      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.48/0.70         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 0.48/0.70           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 0.48/0.70      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.48/0.70  thf(t73_enumset1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.48/0.70     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.48/0.70       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.48/0.70  thf('5', plain,
% 0.48/0.70      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.48/0.70         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.48/0.70           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.48/0.70      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.48/0.70  thf(t61_enumset1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.48/0.70     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.48/0.70       ( k2_xboole_0 @
% 0.48/0.70         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.48/0.70  thf('6', plain,
% 0.48/0.70      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.48/0.70         ((k5_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.48/0.70           = (k2_xboole_0 @ (k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14) @ 
% 0.48/0.70              (k1_tarski @ X15)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.48/0.70  thf('7', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.70         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.48/0.70           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.48/0.70              (k1_tarski @ X5)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['5', '6'])).
% 0.48/0.70  thf(t74_enumset1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.48/0.70     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.48/0.70       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.48/0.70  thf('8', plain,
% 0.48/0.70      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.48/0.70         ((k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 0.48/0.70           = (k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 0.48/0.70      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.48/0.70  thf('9', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.70         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.48/0.70           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.48/0.70              (k1_tarski @ X5)))),
% 0.48/0.70      inference('demod', [status(thm)], ['7', '8'])).
% 0.48/0.70  thf('10', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.70         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.48/0.70           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.48/0.70              (k1_tarski @ X4)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['4', '9'])).
% 0.48/0.70  thf('11', plain,
% 0.48/0.70      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.48/0.70         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.48/0.70           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.48/0.70      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.48/0.70  thf('12', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.70         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.48/0.70           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.48/0.70              (k1_tarski @ X4)))),
% 0.48/0.70      inference('demod', [status(thm)], ['10', '11'])).
% 0.48/0.70  thf('13', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.48/0.70           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['3', '12'])).
% 0.48/0.70  thf('14', plain,
% 0.48/0.70      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.48/0.70         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 0.48/0.70           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 0.48/0.70      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.48/0.70  thf(t69_enumset1, axiom,
% 0.48/0.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.48/0.70  thf('15', plain,
% 0.48/0.70      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.48/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.70  thf(t42_enumset1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.48/0.70       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.48/0.70  thf('16', plain,
% 0.48/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.48/0.70         ((k1_enumset1 @ X6 @ X7 @ X8)
% 0.48/0.70           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k2_tarski @ X7 @ X8)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.48/0.70  thf('17', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.48/0.70           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['15', '16'])).
% 0.48/0.70  thf(commutativity_k2_xboole_0, axiom,
% 0.48/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.48/0.70  thf('18', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.70  thf('19', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.48/0.70           = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.70  thf('20', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.48/0.70           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['15', '16'])).
% 0.48/0.70  thf('21', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k1_enumset1 @ X0 @ X1 @ X1) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['19', '20'])).
% 0.48/0.70  thf('22', plain,
% 0.48/0.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.48/0.70         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.48/0.70           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.48/0.70      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.48/0.70  thf('23', plain,
% 0.48/0.70      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.48/0.70         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.48/0.70           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.48/0.70      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.48/0.70  thf(t75_enumset1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.48/0.70     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.48/0.70       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.48/0.70  thf('24', plain,
% 0.48/0.70      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i]:
% 0.48/0.70         ((k6_enumset1 @ X61 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67)
% 0.48/0.70           = (k5_enumset1 @ X61 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67))),
% 0.48/0.70      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.48/0.70  thf('25', plain,
% 0.48/0.70      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.48/0.70         ((k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 0.48/0.70           = (k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 0.48/0.70      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.48/0.70  thf('26', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.70         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.70           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['24', '25'])).
% 0.48/0.70  thf('27', plain,
% 0.48/0.70      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.48/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.70  thf('28', plain,
% 0.48/0.70      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.48/0.70         ((k5_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.48/0.70           = (k2_xboole_0 @ (k4_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14) @ 
% 0.48/0.70              (k1_tarski @ X15)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.48/0.70  thf('29', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.48/0.70         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.70           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.48/0.70              (k2_tarski @ X0 @ X0)))),
% 0.48/0.70      inference('sup+', [status(thm)], ['27', '28'])).
% 0.48/0.70  thf(t67_enumset1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.48/0.70     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.48/0.70       ( k2_xboole_0 @
% 0.48/0.70         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.48/0.70  thf('30', plain,
% 0.48/0.70      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, 
% 0.48/0.70         X31 : $i]:
% 0.48/0.70         ((k6_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.48/0.70           = (k2_xboole_0 @ 
% 0.48/0.70              (k4_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29) @ 
% 0.48/0.70              (k2_tarski @ X30 @ X31)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.48/0.70  thf('31', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.48/0.70         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.70           = (k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['29', '30'])).
% 0.48/0.70  thf('32', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.70         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.70           = (k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['26', '31'])).
% 0.48/0.70  thf('33', plain,
% 0.48/0.70      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 0.48/0.70         ((k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 0.48/0.70           = (k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 0.48/0.70      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.48/0.70  thf('34', plain,
% 0.48/0.70      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.48/0.70         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.48/0.70           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.48/0.70      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.48/0.70  thf('35', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.70         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.70           = (k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.48/0.70  thf('36', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.70         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.70           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['23', '35'])).
% 0.48/0.70  thf('37', plain,
% 0.48/0.70      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.48/0.70         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 0.48/0.70           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 0.48/0.70      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.48/0.70  thf('38', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.48/0.70         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.70           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['36', '37'])).
% 0.48/0.70  thf('39', plain,
% 0.48/0.70      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.48/0.70         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 0.48/0.70           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 0.48/0.70      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.48/0.70  thf('40', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['38', '39'])).
% 0.48/0.70  thf('41', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['22', '40'])).
% 0.48/0.70  thf('42', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['1', '2'])).
% 0.48/0.70  thf('43', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['41', '42'])).
% 0.48/0.70  thf('44', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]:
% 0.48/0.70         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['41', '42'])).
% 0.48/0.70  thf('45', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 0.48/0.70      inference('demod', [status(thm)], ['21', '43', '44'])).
% 0.48/0.70  thf('46', plain,
% 0.48/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.48/0.70         ((k1_enumset1 @ X6 @ X7 @ X8)
% 0.48/0.70           = (k2_xboole_0 @ (k1_tarski @ X6) @ (k2_tarski @ X7 @ X8)))),
% 0.48/0.70      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.48/0.70  thf('47', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.70      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.70  thf('48', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.48/0.70           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['46', '47'])).
% 0.48/0.70  thf('49', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.48/0.70           = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.48/0.70      inference('sup+', [status(thm)], ['45', '48'])).
% 0.48/0.70  thf('50', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X0 @ X1))),
% 0.48/0.70      inference('demod', [status(thm)], ['13', '14', '49'])).
% 0.48/0.70  thf('51', plain,
% 0.48/0.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.48/0.70         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.48/0.70           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.48/0.70      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.48/0.70  thf(t98_enumset1, axiom,
% 0.48/0.70    (![A:$i,B:$i,C:$i]:
% 0.48/0.70     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.48/0.70  thf('52', plain,
% 0.48/0.70      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.48/0.70         ((k1_enumset1 @ X68 @ X70 @ X69) = (k1_enumset1 @ X68 @ X69 @ X70))),
% 0.48/0.70      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.48/0.70  thf('53', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((k1_enumset1 @ X2 @ X0 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['51', '52'])).
% 0.48/0.70  thf('54', plain,
% 0.48/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.70         ((k1_enumset1 @ X0 @ X2 @ X1) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.48/0.70      inference('sup+', [status(thm)], ['50', '53'])).
% 0.48/0.70  thf('55', plain,
% 0.48/0.70      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.48/0.70         ((k1_enumset1 @ X68 @ X70 @ X69) = (k1_enumset1 @ X68 @ X69 @ X70))),
% 0.48/0.70      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.48/0.70  thf('56', plain,
% 0.48/0.70      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.48/0.70         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.48/0.70      inference('demod', [status(thm)], ['0', '54', '55'])).
% 0.48/0.70  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.48/0.70  
% 0.48/0.70  % SZS output end Refutation
% 0.48/0.70  
% 0.48/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
