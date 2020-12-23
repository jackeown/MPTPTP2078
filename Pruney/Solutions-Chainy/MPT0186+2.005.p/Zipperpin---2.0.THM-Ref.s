%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dcYB6vyxAS

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:04 EST 2020

% Result     : Theorem 27.86s
% Output     : Refutation 27.86s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 668 expanded)
%              Number of leaves         :   22 ( 233 expanded)
%              Depth                    :   18
%              Number of atoms          : 1412 (8775 expanded)
%              Number of equality atoms :  104 ( 655 expanded)
%              Maximal formula depth    :   16 (  11 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k5_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k2_tarski @ X18 @ X19 ) @ ( k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('5',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('8',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t99_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ B @ A @ C ) ) )).

thf('17',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k1_enumset1 @ X62 @ X61 @ X63 )
      = ( k1_enumset1 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t99_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('27',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('37',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','54'])).

thf('56',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('57',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 )
      = ( k2_enumset1 @ X46 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 ) @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i] :
      ( ( k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 )
      = ( k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X5 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X0 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X1 @ X2 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X2 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X1 @ X2 @ X0 ) )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','73','86','87'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69','88','89','90'])).

thf('92',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','91'])).

thf('93',plain,(
    $false ),
    inference(simplify,[status(thm)],['92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dcYB6vyxAS
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:03:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 27.86/28.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 27.86/28.07  % Solved by: fo/fo7.sh
% 27.86/28.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.86/28.07  % done 14520 iterations in 27.602s
% 27.86/28.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 27.86/28.07  % SZS output start Refutation
% 27.86/28.07  thf(sk_A_type, type, sk_A: $i).
% 27.86/28.07  thf(sk_D_type, type, sk_D: $i).
% 27.86/28.07  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 27.86/28.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 27.86/28.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 27.86/28.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 27.86/28.07  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 27.86/28.07  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 27.86/28.07  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 27.86/28.07  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 27.86/28.07  thf(sk_B_type, type, sk_B: $i).
% 27.86/28.07  thf(sk_C_type, type, sk_C: $i).
% 27.86/28.07  thf(t104_enumset1, conjecture,
% 27.86/28.07    (![A:$i,B:$i,C:$i,D:$i]:
% 27.86/28.07     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ))).
% 27.86/28.07  thf(zf_stmt_0, negated_conjecture,
% 27.86/28.07    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 27.86/28.07        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ C @ B @ D ) ) )),
% 27.86/28.07    inference('cnf.neg', [status(esa)], [t104_enumset1])).
% 27.86/28.07  thf('0', plain,
% 27.86/28.07      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 27.86/28.07         != (k2_enumset1 @ sk_A @ sk_C @ sk_B @ sk_D))),
% 27.86/28.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.86/28.07  thf(t72_enumset1, axiom,
% 27.86/28.07    (![A:$i,B:$i,C:$i,D:$i]:
% 27.86/28.07     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 27.86/28.07  thf('1', plain,
% 27.86/28.07      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 27.86/28.07         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 27.86/28.07           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 27.86/28.07      inference('cnf', [status(esa)], [t72_enumset1])).
% 27.86/28.07  thf(t69_enumset1, axiom,
% 27.86/28.07    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 27.86/28.07  thf('2', plain, (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 27.86/28.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 27.86/28.07  thf(t57_enumset1, axiom,
% 27.86/28.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 27.86/28.07     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 27.86/28.07       ( k2_xboole_0 @
% 27.86/28.07         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 27.86/28.07  thf('3', plain,
% 27.86/28.07      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 27.86/28.07         ((k5_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24)
% 27.86/28.07           = (k2_xboole_0 @ (k2_tarski @ X18 @ X19) @ 
% 27.86/28.07              (k3_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24)))),
% 27.86/28.07      inference('cnf', [status(esa)], [t57_enumset1])).
% 27.86/28.07  thf('4', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 27.86/28.07         ((k5_enumset1 @ X0 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 27.86/28.07              (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['2', '3'])).
% 27.86/28.07  thf(t74_enumset1, axiom,
% 27.86/28.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 27.86/28.07     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 27.86/28.07       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 27.86/28.07  thf('5', plain,
% 27.86/28.07      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 27.86/28.07         ((k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 27.86/28.07           = (k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 27.86/28.07      inference('cnf', [status(esa)], [t74_enumset1])).
% 27.86/28.07  thf('6', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 27.86/28.07              (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 27.86/28.07      inference('demod', [status(thm)], ['4', '5'])).
% 27.86/28.07  thf('7', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 27.86/28.07              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['1', '6'])).
% 27.86/28.07  thf(t73_enumset1, axiom,
% 27.86/28.07    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 27.86/28.07     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 27.86/28.07       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 27.86/28.07  thf('8', plain,
% 27.86/28.07      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 27.86/28.07           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 27.86/28.07      inference('cnf', [status(esa)], [t73_enumset1])).
% 27.86/28.07  thf('9', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X0 @ X5 @ X4 @ X3 @ X2 @ X1)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 27.86/28.07              (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1)))),
% 27.86/28.07      inference('demod', [status(thm)], ['4', '5'])).
% 27.86/28.07  thf('10', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 27.86/28.07              (k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['8', '9'])).
% 27.86/28.07  thf('11', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 27.86/28.07              (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 27.86/28.07               (k2_enumset1 @ X3 @ X2 @ X1 @ X0))))),
% 27.86/28.07      inference('sup+', [status(thm)], ['7', '10'])).
% 27.86/28.07  thf('12', plain,
% 27.86/28.07      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 27.86/28.07         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 27.86/28.07           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 27.86/28.07      inference('cnf', [status(esa)], [t72_enumset1])).
% 27.86/28.07  thf(t55_enumset1, axiom,
% 27.86/28.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 27.86/28.07     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 27.86/28.07       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 27.86/28.07  thf('13', plain,
% 27.86/28.07      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 27.86/28.07           = (k2_xboole_0 @ (k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16) @ 
% 27.86/28.07              (k1_tarski @ X17)))),
% 27.86/28.07      inference('cnf', [status(esa)], [t55_enumset1])).
% 27.86/28.07  thf('14', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 27.86/28.07              (k1_tarski @ X4)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['12', '13'])).
% 27.86/28.07  thf('15', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 27.86/28.07              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['1', '6'])).
% 27.86/28.07  thf('16', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 27.86/28.07              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['14', '15'])).
% 27.86/28.07  thf(t99_enumset1, axiom,
% 27.86/28.07    (![A:$i,B:$i,C:$i]:
% 27.86/28.07     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ B @ A @ C ) ))).
% 27.86/28.07  thf('17', plain,
% 27.86/28.07      (![X61 : $i, X62 : $i, X63 : $i]:
% 27.86/28.07         ((k1_enumset1 @ X62 @ X61 @ X63) = (k1_enumset1 @ X61 @ X62 @ X63))),
% 27.86/28.07      inference('cnf', [status(esa)], [t99_enumset1])).
% 27.86/28.07  thf('18', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 27.86/28.07              (k1_tarski @ X4)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['12', '13'])).
% 27.86/28.07  thf('19', plain,
% 27.86/28.07      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 27.86/28.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 27.86/28.07  thf(t60_enumset1, axiom,
% 27.86/28.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 27.86/28.07     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 27.86/28.07       ( k2_xboole_0 @
% 27.86/28.07         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 27.86/28.07  thf('20', plain,
% 27.86/28.07      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 27.86/28.07         ((k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 27.86/28.07           = (k2_xboole_0 @ (k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29) @ 
% 27.86/28.07              (k2_tarski @ X30 @ X31)))),
% 27.86/28.07      inference('cnf', [status(esa)], [t60_enumset1])).
% 27.86/28.07  thf('21', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 27.86/28.07         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 27.86/28.07              (k1_tarski @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['19', '20'])).
% 27.86/28.07  thf('22', plain,
% 27.86/28.07      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 27.86/28.07           = (k2_xboole_0 @ (k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16) @ 
% 27.86/28.07              (k1_tarski @ X17)))),
% 27.86/28.07      inference('cnf', [status(esa)], [t55_enumset1])).
% 27.86/28.07  thf('23', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 27.86/28.07         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 27.86/28.07           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('demod', [status(thm)], ['21', '22'])).
% 27.86/28.07  thf('24', plain,
% 27.86/28.07      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 27.86/28.07         ((k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 27.86/28.07           = (k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 27.86/28.07      inference('cnf', [status(esa)], [t74_enumset1])).
% 27.86/28.07  thf('25', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['23', '24'])).
% 27.86/28.07  thf('26', plain,
% 27.86/28.07      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 27.86/28.07         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 27.86/28.07           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 27.86/28.07      inference('cnf', [status(esa)], [t72_enumset1])).
% 27.86/28.07  thf(t71_enumset1, axiom,
% 27.86/28.07    (![A:$i,B:$i,C:$i]:
% 27.86/28.07     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 27.86/28.07  thf('27', plain,
% 27.86/28.07      (![X43 : $i, X44 : $i, X45 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 27.86/28.07           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 27.86/28.07      inference('cnf', [status(esa)], [t71_enumset1])).
% 27.86/28.07  thf('28', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['26', '27'])).
% 27.86/28.07  thf('29', plain,
% 27.86/28.07      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 27.86/28.07           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 27.86/28.07      inference('cnf', [status(esa)], [t73_enumset1])).
% 27.86/28.07  thf('30', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['28', '29'])).
% 27.86/28.07  thf('31', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 @ X0)
% 27.86/28.07           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['25', '30'])).
% 27.86/28.07  thf('32', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0) @ (k1_tarski @ X0))
% 27.86/28.07           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['18', '31'])).
% 27.86/28.07  thf('33', plain,
% 27.86/28.07      (![X43 : $i, X44 : $i, X45 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 27.86/28.07           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 27.86/28.07      inference('cnf', [status(esa)], [t71_enumset1])).
% 27.86/28.07  thf('34', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X0))
% 27.86/28.07           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('demod', [status(thm)], ['32', '33'])).
% 27.86/28.07  thf('35', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X0))
% 27.86/28.07           = (k1_enumset1 @ X1 @ X2 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['17', '34'])).
% 27.86/28.07  thf('36', plain,
% 27.86/28.07      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 27.86/28.07           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 27.86/28.07      inference('cnf', [status(esa)], [t73_enumset1])).
% 27.86/28.07  thf('37', plain,
% 27.86/28.07      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 27.86/28.07         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 27.86/28.07           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 27.86/28.07      inference('cnf', [status(esa)], [t72_enumset1])).
% 27.86/28.07  thf('38', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['36', '37'])).
% 27.86/28.07  thf('39', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 27.86/28.07              (k1_tarski @ X4)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['12', '13'])).
% 27.86/28.07  thf('40', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X3 @ X2 @ X1) @ 
% 27.86/28.07              (k1_tarski @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['38', '39'])).
% 27.86/28.07  thf('41', plain,
% 27.86/28.07      (![X43 : $i, X44 : $i, X45 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 27.86/28.07           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 27.86/28.07      inference('cnf', [status(esa)], [t71_enumset1])).
% 27.86/28.07  thf('42', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 27.86/28.07      inference('demod', [status(thm)], ['40', '41'])).
% 27.86/28.07  thf('43', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 27.86/28.07      inference('demod', [status(thm)], ['35', '42'])).
% 27.86/28.07  thf('44', plain,
% 27.86/28.07      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 27.86/28.07         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 27.86/28.07           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 27.86/28.07      inference('cnf', [status(esa)], [t72_enumset1])).
% 27.86/28.07  thf('45', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k3_enumset1 @ X1 @ X1 @ X2 @ X0 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['43', '44'])).
% 27.86/28.07  thf('46', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['23', '24'])).
% 27.86/28.07  thf('47', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['36', '37'])).
% 27.86/28.07  thf('48', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X0)
% 27.86/28.07           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['46', '47'])).
% 27.86/28.07  thf('49', plain,
% 27.86/28.07      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X50 @ X50 @ X51 @ X52 @ X53 @ X54)
% 27.86/28.07           = (k3_enumset1 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 27.86/28.07      inference('cnf', [status(esa)], [t73_enumset1])).
% 27.86/28.07  thf('50', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['48', '49'])).
% 27.86/28.07  thf('51', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['45', '50'])).
% 27.86/28.07  thf('52', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X1) @ (k1_tarski @ X0))
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 27.86/28.07              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 27.86/28.07      inference('demod', [status(thm)], ['16', '51'])).
% 27.86/28.07  thf('53', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 27.86/28.07      inference('demod', [status(thm)], ['40', '41'])).
% 27.86/28.07  thf('54', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 27.86/28.07              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 27.86/28.07      inference('demod', [status(thm)], ['52', '53'])).
% 27.86/28.07  thf('55', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 27.86/28.07              (k2_enumset1 @ X2 @ X3 @ X1 @ X0)))),
% 27.86/28.07      inference('demod', [status(thm)], ['11', '54'])).
% 27.86/28.07  thf('56', plain,
% 27.86/28.07      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 27.86/28.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 27.86/28.07  thf('57', plain,
% 27.86/28.07      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 27.86/28.07         ((k3_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49)
% 27.86/28.07           = (k2_enumset1 @ X46 @ X47 @ X48 @ X49))),
% 27.86/28.07      inference('cnf', [status(esa)], [t72_enumset1])).
% 27.86/28.07  thf('58', plain,
% 27.86/28.07      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 27.86/28.07         ((k5_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31)
% 27.86/28.07           = (k2_xboole_0 @ (k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29) @ 
% 27.86/28.07              (k2_tarski @ X30 @ X31)))),
% 27.86/28.07      inference('cnf', [status(esa)], [t60_enumset1])).
% 27.86/28.07  thf('59', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 27.86/28.07         ((k5_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 27.86/28.07              (k2_tarski @ X5 @ X4)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['57', '58'])).
% 27.86/28.07  thf('60', plain,
% 27.86/28.07      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i]:
% 27.86/28.07         ((k5_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60)
% 27.86/28.07           = (k4_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60))),
% 27.86/28.07      inference('cnf', [status(esa)], [t74_enumset1])).
% 27.86/28.07  thf('61', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X5 @ X4)
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 27.86/28.07              (k2_tarski @ X5 @ X4)))),
% 27.86/28.07      inference('demod', [status(thm)], ['59', '60'])).
% 27.86/28.07  thf('62', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 27.86/28.07              (k1_tarski @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['56', '61'])).
% 27.86/28.07  thf('63', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 27.86/28.07              (k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['8', '9'])).
% 27.86/28.07  thf('64', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 27.86/28.07              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X3 @ X2 @ X1) @ 
% 27.86/28.07               (k1_tarski @ X0))))),
% 27.86/28.07      inference('sup+', [status(thm)], ['62', '63'])).
% 27.86/28.07  thf('65', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['45', '50'])).
% 27.86/28.07  thf('66', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 27.86/28.07      inference('demod', [status(thm)], ['40', '41'])).
% 27.86/28.07  thf('67', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 27.86/28.07              (k2_enumset1 @ X2 @ X3 @ X1 @ X0)))),
% 27.86/28.07      inference('demod', [status(thm)], ['64', '65', '66'])).
% 27.86/28.07  thf('68', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k2_enumset1 @ X2 @ X1 @ X0 @ X0))
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 27.86/28.07              (k2_enumset1 @ X1 @ X1 @ X2 @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['55', '67'])).
% 27.86/28.07  thf('69', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 27.86/28.07      inference('demod', [status(thm)], ['35', '42'])).
% 27.86/28.07  thf('70', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 27.86/28.07              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['1', '6'])).
% 27.86/28.07  thf('71', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 27.86/28.07              (k1_tarski @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['56', '61'])).
% 27.86/28.07  thf('72', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k2_enumset1 @ X2 @ X1 @ X0 @ X0))
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X2 @ X1) @ 
% 27.86/28.07              (k1_tarski @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['70', '71'])).
% 27.86/28.07  thf('73', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X2 @ X0))),
% 27.86/28.07      inference('demod', [status(thm)], ['35', '42'])).
% 27.86/28.07  thf('74', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['28', '29'])).
% 27.86/28.07  thf('75', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['23', '24'])).
% 27.86/28.07  thf('76', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0)
% 27.86/28.07           = (k1_enumset1 @ X1 @ X0 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['74', '75'])).
% 27.86/28.07  thf('77', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['28', '29'])).
% 27.86/28.07  thf('78', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i]:
% 27.86/28.07         ((k1_enumset1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X0 @ X0))),
% 27.86/28.07      inference('demod', [status(thm)], ['76', '77'])).
% 27.86/28.07  thf('79', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X2 @ X2 @ X2 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['28', '29'])).
% 27.86/28.07  thf('80', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 27.86/28.07         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 27.86/28.07              (k1_tarski @ X4)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['12', '13'])).
% 27.86/28.07  thf('81', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k1_enumset1 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X2 @ X1) @ 
% 27.86/28.07              (k1_tarski @ X0)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['79', '80'])).
% 27.86/28.07  thf('82', plain,
% 27.86/28.07      (![X43 : $i, X44 : $i, X45 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 27.86/28.07           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 27.86/28.07      inference('cnf', [status(esa)], [t71_enumset1])).
% 27.86/28.07  thf('83', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k1_enumset1 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 27.86/28.07      inference('demod', [status(thm)], ['81', '82'])).
% 27.86/28.07  thf('84', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k1_enumset1 @ X1 @ X0 @ X2)
% 27.86/28.07           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X0 @ X0) @ (k1_tarski @ X2)))),
% 27.86/28.07      inference('sup+', [status(thm)], ['78', '83'])).
% 27.86/28.07  thf('85', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 27.86/28.07      inference('demod', [status(thm)], ['40', '41'])).
% 27.86/28.07  thf('86', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k1_enumset1 @ X1 @ X0 @ X2) = (k2_enumset1 @ X1 @ X0 @ X0 @ X2))),
% 27.86/28.07      inference('demod', [status(thm)], ['84', '85'])).
% 27.86/28.07  thf('87', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 27.86/28.07           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 27.86/28.07      inference('demod', [status(thm)], ['40', '41'])).
% 27.86/28.07  thf('88', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X1 @ X2 @ X0))
% 27.86/28.07           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('demod', [status(thm)], ['72', '73', '86', '87'])).
% 27.86/28.07  thf('89', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X1 @ X1 @ X2 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('sup+', [status(thm)], ['45', '50'])).
% 27.86/28.07  thf('90', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X1 @ X2 @ X0))
% 27.86/28.07           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 27.86/28.07      inference('demod', [status(thm)], ['72', '73', '86', '87'])).
% 27.86/28.07  thf('91', plain,
% 27.86/28.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.86/28.07         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X1 @ X2 @ X0))),
% 27.86/28.07      inference('demod', [status(thm)], ['68', '69', '88', '89', '90'])).
% 27.86/28.07  thf('92', plain,
% 27.86/28.07      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 27.86/28.07         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 27.86/28.07      inference('demod', [status(thm)], ['0', '91'])).
% 27.86/28.07  thf('93', plain, ($false), inference('simplify', [status(thm)], ['92'])).
% 27.86/28.07  
% 27.86/28.07  % SZS output end Refutation
% 27.86/28.07  
% 27.91/28.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
