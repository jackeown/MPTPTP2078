%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZkFh8UPORf

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:37 EST 2020

% Result     : Theorem 17.59s
% Output     : Refutation 17.59s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 847 expanded)
%              Number of leaves         :   31 ( 293 expanded)
%              Depth                    :   19
%              Number of atoms          : 1461 (10789 expanded)
%              Number of equality atoms :  123 ( 827 expanded)
%              Maximal formula depth    :   17 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X10 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X10 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('9',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k4_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 @ X57 )
      = ( k3_enumset1 @ X53 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('13',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ( k5_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 )
      = ( k4_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('14',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k4_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 @ X57 )
      = ( k3_enumset1 @ X53 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X2 @ X3 @ X4 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('24',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( k2_enumset1 @ X10 @ X9 @ X8 @ X7 )
      = ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t58_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ) )).

thf('34',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) @ ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X0 @ X1 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('44',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X0 @ X0 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X2 @ X3 @ X4 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('60',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 )
      = ( k2_enumset1 @ X49 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X2 @ X3 @ X3 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X2 @ X3 @ X3 @ X0 @ X4 )
      = ( k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X0 @ X0 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['58','65','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','55'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X1 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X1 @ X1 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X1 @ X2 @ X3 @ X4 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','82'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','83','84'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('86',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('90',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X5 @ X6 ) @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('92',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['90','93'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','102'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('104',plain,(
    ! [X64: $i,X65: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X64 ) @ X65 )
      | ( r2_hidden @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('105',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['104','105'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('107',plain,(
    ! [X66: $i,X67: $i] :
      ( ( ( k3_xboole_0 @ X67 @ ( k1_tarski @ X66 ) )
        = ( k1_tarski @ X66 ) )
      | ~ ( r2_hidden @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('108',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','103','108'])).

thf('110',plain,(
    $false ),
    inference(simplify,[status(thm)],['109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZkFh8UPORf
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:23:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 17.59/17.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 17.59/17.82  % Solved by: fo/fo7.sh
% 17.59/17.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.59/17.82  % done 2344 iterations in 17.353s
% 17.59/17.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 17.59/17.82  % SZS output start Refutation
% 17.59/17.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.59/17.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.59/17.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 17.59/17.82  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 17.59/17.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.59/17.82  thf(sk_A_type, type, sk_A: $i).
% 17.59/17.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 17.59/17.82  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 17.59/17.82  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 17.59/17.82  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 17.59/17.82  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 17.59/17.82  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 17.59/17.82  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 17.59/17.82  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 17.59/17.82  thf(sk_B_type, type, sk_B: $i).
% 17.59/17.82  thf(t58_zfmisc_1, conjecture,
% 17.59/17.82    (![A:$i,B:$i]:
% 17.59/17.82     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 17.59/17.82       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 17.59/17.82  thf(zf_stmt_0, negated_conjecture,
% 17.59/17.82    (~( ![A:$i,B:$i]:
% 17.59/17.82        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 17.59/17.82          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 17.59/17.82    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 17.59/17.82  thf('0', plain,
% 17.59/17.82      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 17.59/17.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.59/17.82  thf(t125_enumset1, axiom,
% 17.59/17.82    (![A:$i,B:$i,C:$i,D:$i]:
% 17.59/17.82     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 17.59/17.82  thf('1', plain,
% 17.59/17.82      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 17.59/17.82         ((k2_enumset1 @ X10 @ X9 @ X8 @ X7)
% 17.59/17.82           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 17.59/17.82      inference('cnf', [status(esa)], [t125_enumset1])).
% 17.59/17.82  thf(t71_enumset1, axiom,
% 17.59/17.82    (![A:$i,B:$i,C:$i]:
% 17.59/17.82     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 17.59/17.82  thf('2', plain,
% 17.59/17.82      (![X46 : $i, X47 : $i, X48 : $i]:
% 17.59/17.82         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 17.59/17.82           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 17.59/17.82      inference('cnf', [status(esa)], [t71_enumset1])).
% 17.59/17.82  thf('3', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 17.59/17.82      inference('sup+', [status(thm)], ['1', '2'])).
% 17.59/17.82  thf('4', plain,
% 17.59/17.82      (![X46 : $i, X47 : $i, X48 : $i]:
% 17.59/17.82         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 17.59/17.82           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 17.59/17.82      inference('cnf', [status(esa)], [t71_enumset1])).
% 17.59/17.82  thf('5', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 17.59/17.82      inference('sup+', [status(thm)], ['3', '4'])).
% 17.59/17.82  thf(t72_enumset1, axiom,
% 17.59/17.82    (![A:$i,B:$i,C:$i,D:$i]:
% 17.59/17.82     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 17.59/17.82  thf('6', plain,
% 17.59/17.82      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 17.59/17.82           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 17.59/17.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 17.59/17.82  thf('7', plain,
% 17.59/17.82      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 17.59/17.82         ((k2_enumset1 @ X10 @ X9 @ X8 @ X7)
% 17.59/17.82           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 17.59/17.82      inference('cnf', [status(esa)], [t125_enumset1])).
% 17.59/17.82  thf('8', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.59/17.82         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 17.59/17.82           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['6', '7'])).
% 17.59/17.82  thf(t73_enumset1, axiom,
% 17.59/17.82    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 17.59/17.82     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 17.59/17.82       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 17.59/17.82  thf('9', plain,
% 17.59/17.82      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 17.59/17.82         ((k4_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 @ X57)
% 17.59/17.82           = (k3_enumset1 @ X53 @ X54 @ X55 @ X56 @ X57))),
% 17.59/17.82      inference('cnf', [status(esa)], [t73_enumset1])).
% 17.59/17.82  thf(t61_enumset1, axiom,
% 17.59/17.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 17.59/17.82     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 17.59/17.82       ( k2_xboole_0 @
% 17.59/17.82         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 17.59/17.82  thf('10', plain,
% 17.59/17.82      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 17.59/17.82           = (k2_xboole_0 @ 
% 17.59/17.82              (k4_enumset1 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41) @ 
% 17.59/17.82              (k1_tarski @ X42)))),
% 17.59/17.82      inference('cnf', [status(esa)], [t61_enumset1])).
% 17.59/17.82  thf('11', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 17.59/17.82           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X5)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['9', '10'])).
% 17.59/17.82  thf('12', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X3 @ X4)
% 17.59/17.82           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X4)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['8', '11'])).
% 17.59/17.82  thf(t74_enumset1, axiom,
% 17.59/17.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 17.59/17.82     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 17.59/17.82       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 17.59/17.82  thf('13', plain,
% 17.59/17.82      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X58 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63)
% 17.59/17.82           = (k4_enumset1 @ X58 @ X59 @ X60 @ X61 @ X62 @ X63))),
% 17.59/17.82      inference('cnf', [status(esa)], [t74_enumset1])).
% 17.59/17.82  thf('14', plain,
% 17.59/17.82      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 17.59/17.82         ((k4_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 @ X57)
% 17.59/17.82           = (k3_enumset1 @ X53 @ X54 @ X55 @ X56 @ X57))),
% 17.59/17.82      inference('cnf', [status(esa)], [t73_enumset1])).
% 17.59/17.82  thf('15', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 17.59/17.82           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['13', '14'])).
% 17.59/17.82  thf('16', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 17.59/17.82           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X4)))),
% 17.59/17.82      inference('demod', [status(thm)], ['12', '15'])).
% 17.59/17.82  thf('17', plain,
% 17.59/17.82      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 17.59/17.82           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 17.59/17.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 17.59/17.82  thf('18', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 17.59/17.82           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X5)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['9', '10'])).
% 17.59/17.82  thf('19', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 17.59/17.82           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X4)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['17', '18'])).
% 17.59/17.82  thf('20', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 17.59/17.82           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['13', '14'])).
% 17.59/17.82  thf('21', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 17.59/17.82           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X4)))),
% 17.59/17.82      inference('demod', [status(thm)], ['19', '20'])).
% 17.59/17.82  thf('22', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X1 @ X2 @ X3 @ X4 @ X0)
% 17.59/17.82           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['16', '21'])).
% 17.59/17.82  thf('23', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 17.59/17.82      inference('sup+', [status(thm)], ['1', '2'])).
% 17.59/17.82  thf('24', plain,
% 17.59/17.82      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 17.59/17.82           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 17.59/17.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 17.59/17.82  thf('25', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['23', '24'])).
% 17.59/17.82  thf(t70_enumset1, axiom,
% 17.59/17.82    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 17.59/17.82  thf('26', plain,
% 17.59/17.82      (![X44 : $i, X45 : $i]:
% 17.59/17.82         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 17.59/17.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 17.59/17.82  thf('27', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 17.59/17.82      inference('sup+', [status(thm)], ['25', '26'])).
% 17.59/17.82  thf('28', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X0 @ X1 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 17.59/17.82      inference('sup+', [status(thm)], ['22', '27'])).
% 17.59/17.82  thf('29', plain,
% 17.59/17.82      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 17.59/17.82           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 17.59/17.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 17.59/17.82  thf('30', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X0 @ X1))),
% 17.59/17.82      inference('sup+', [status(thm)], ['28', '29'])).
% 17.59/17.82  thf('31', plain,
% 17.59/17.82      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 17.59/17.82         ((k2_enumset1 @ X10 @ X9 @ X8 @ X7)
% 17.59/17.82           = (k2_enumset1 @ X7 @ X8 @ X9 @ X10))),
% 17.59/17.82      inference('cnf', [status(esa)], [t125_enumset1])).
% 17.59/17.82  thf(t69_enumset1, axiom,
% 17.59/17.82    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 17.59/17.82  thf('32', plain,
% 17.59/17.82      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 17.59/17.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 17.59/17.82  thf('33', plain,
% 17.59/17.82      (![X44 : $i, X45 : $i]:
% 17.59/17.82         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 17.59/17.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 17.59/17.82  thf(t58_enumset1, axiom,
% 17.59/17.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 17.59/17.82     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 17.59/17.82       ( k2_xboole_0 @
% 17.59/17.82         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 17.59/17.82  thf('34', plain,
% 17.59/17.82      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 17.59/17.82           = (k2_xboole_0 @ (k1_enumset1 @ X29 @ X30 @ X31) @ 
% 17.59/17.82              (k2_enumset1 @ X32 @ X33 @ X34 @ X35)))),
% 17.59/17.82      inference('cnf', [status(esa)], [t58_enumset1])).
% 17.59/17.82  thf('35', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2)
% 17.59/17.82           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 17.59/17.82              (k2_enumset1 @ X5 @ X4 @ X3 @ X2)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['33', '34'])).
% 17.59/17.82  thf('36', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)
% 17.59/17.82           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 17.59/17.82              (k2_enumset1 @ X4 @ X3 @ X2 @ X1)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['32', '35'])).
% 17.59/17.82  thf('37', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 17.59/17.82           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['13', '14'])).
% 17.59/17.82  thf('38', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1)
% 17.59/17.82           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 17.59/17.82              (k2_enumset1 @ X4 @ X3 @ X2 @ X1)))),
% 17.59/17.82      inference('demod', [status(thm)], ['36', '37'])).
% 17.59/17.82  thf('39', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X4 @ X0 @ X1 @ X2 @ X3)
% 17.59/17.82           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 17.59/17.82              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['31', '38'])).
% 17.59/17.82  thf('40', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X1)
% 17.59/17.82           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['30', '39'])).
% 17.59/17.82  thf('41', plain,
% 17.59/17.82      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 17.59/17.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 17.59/17.82  thf('42', plain,
% 17.59/17.82      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 17.59/17.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 17.59/17.82  thf('43', plain,
% 17.59/17.82      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 17.59/17.82           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 17.59/17.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 17.59/17.82  thf('44', plain,
% 17.59/17.82      (![X46 : $i, X47 : $i, X48 : $i]:
% 17.59/17.82         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 17.59/17.82           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 17.59/17.82      inference('cnf', [status(esa)], [t71_enumset1])).
% 17.59/17.82  thf('45', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['43', '44'])).
% 17.59/17.82  thf('46', plain,
% 17.59/17.82      (![X44 : $i, X45 : $i]:
% 17.59/17.82         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 17.59/17.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 17.59/17.82  thf('47', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['45', '46'])).
% 17.59/17.82  thf('48', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 17.59/17.82           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X5)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['9', '10'])).
% 17.59/17.82  thf('49', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 17.59/17.82           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['47', '48'])).
% 17.59/17.82  thf('50', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 17.59/17.82           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['13', '14'])).
% 17.59/17.82  thf('51', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 17.59/17.82           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 17.59/17.82      inference('demod', [status(thm)], ['49', '50'])).
% 17.59/17.82  thf('52', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 17.59/17.82           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['42', '51'])).
% 17.59/17.82  thf('53', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['45', '46'])).
% 17.59/17.82  thf('54', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k2_tarski @ X0 @ X1)
% 17.59/17.82           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 17.59/17.82      inference('demod', [status(thm)], ['52', '53'])).
% 17.59/17.82  thf('55', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k2_tarski @ X1 @ X0)
% 17.59/17.82           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['41', '54'])).
% 17.59/17.82  thf('56', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k2_tarski @ X1 @ X0) = (k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['40', '55'])).
% 17.59/17.82  thf('57', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 17.59/17.82           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X5)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['9', '10'])).
% 17.59/17.82  thf('58', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X1 @ X1 @ X0 @ X0 @ X0 @ X0 @ X2)
% 17.59/17.82           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['56', '57'])).
% 17.59/17.82  thf('59', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X1 @ X2 @ X3 @ X4 @ X0)
% 17.59/17.82           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['16', '21'])).
% 17.59/17.82  thf('60', plain,
% 17.59/17.82      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52)
% 17.59/17.82           = (k2_enumset1 @ X49 @ X50 @ X51 @ X52))),
% 17.59/17.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 17.59/17.82  thf('61', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 17.59/17.82           = (k2_enumset1 @ X1 @ X2 @ X3 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['59', '60'])).
% 17.59/17.82  thf('62', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 17.59/17.82           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X5)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['9', '10'])).
% 17.59/17.82  thf('63', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X1 @ X1 @ X2 @ X3 @ X3 @ X0 @ X4)
% 17.59/17.82           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X4)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['61', '62'])).
% 17.59/17.82  thf('64', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4)
% 17.59/17.82           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X4)))),
% 17.59/17.82      inference('demod', [status(thm)], ['12', '15'])).
% 17.59/17.82  thf('65', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X1 @ X1 @ X2 @ X3 @ X3 @ X0 @ X4)
% 17.59/17.82           = (k3_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4))),
% 17.59/17.82      inference('demod', [status(thm)], ['63', '64'])).
% 17.59/17.82  thf('66', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 17.59/17.82           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 17.59/17.82      inference('demod', [status(thm)], ['49', '50'])).
% 17.59/17.82  thf('67', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['43', '44'])).
% 17.59/17.82  thf('68', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 17.59/17.82           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['66', '67'])).
% 17.59/17.82  thf('69', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X1 @ X0 @ X0 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 17.59/17.82      inference('demod', [status(thm)], ['58', '65', '68'])).
% 17.59/17.82  thf('70', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k2_tarski @ X1 @ X0) = (k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['40', '55'])).
% 17.59/17.82  thf('71', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 17.59/17.82      inference('sup+', [status(thm)], ['25', '26'])).
% 17.59/17.82  thf('72', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 17.59/17.82           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 17.59/17.82              (k1_tarski @ X5)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['9', '10'])).
% 17.59/17.82  thf('73', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X0 @ X0 @ X0 @ X1 @ X1 @ X1 @ X2)
% 17.59/17.82           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['71', '72'])).
% 17.59/17.82  thf('74', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 17.59/17.82           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['13', '14'])).
% 17.59/17.82  thf('75', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X1 @ X1 @ X1 @ X2)
% 17.59/17.82           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 17.59/17.82      inference('demod', [status(thm)], ['73', '74'])).
% 17.59/17.82  thf('76', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 17.59/17.82           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['66', '67'])).
% 17.59/17.82  thf('77', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X1 @ X1 @ X1 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 17.59/17.82      inference('demod', [status(thm)], ['75', '76'])).
% 17.59/17.82  thf('78', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['70', '77'])).
% 17.59/17.82  thf('79', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X1 @ X2 @ X3 @ X4 @ X0)
% 17.59/17.82           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['16', '21'])).
% 17.59/17.82  thf('80', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['23', '24'])).
% 17.59/17.82  thf('81', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X0 @ X2 @ X1))),
% 17.59/17.82      inference('sup+', [status(thm)], ['79', '80'])).
% 17.59/17.82  thf('82', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_enumset1 @ X0 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['78', '81'])).
% 17.59/17.82  thf('83', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['69', '82'])).
% 17.59/17.82  thf('84', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['69', '82'])).
% 17.59/17.82  thf('85', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 17.59/17.82      inference('demod', [status(thm)], ['5', '83', '84'])).
% 17.59/17.82  thf(l51_zfmisc_1, axiom,
% 17.59/17.82    (![A:$i,B:$i]:
% 17.59/17.82     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 17.59/17.82  thf('86', plain,
% 17.59/17.82      (![X68 : $i, X69 : $i]:
% 17.59/17.82         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 17.59/17.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 17.59/17.82  thf('87', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 17.59/17.82      inference('sup+', [status(thm)], ['85', '86'])).
% 17.59/17.82  thf('88', plain,
% 17.59/17.82      (![X68 : $i, X69 : $i]:
% 17.59/17.82         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 17.59/17.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 17.59/17.82  thf('89', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 17.59/17.82      inference('sup+', [status(thm)], ['87', '88'])).
% 17.59/17.82  thf(t95_xboole_1, axiom,
% 17.59/17.82    (![A:$i,B:$i]:
% 17.59/17.82     ( ( k3_xboole_0 @ A @ B ) =
% 17.59/17.82       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 17.59/17.82  thf('90', plain,
% 17.59/17.82      (![X5 : $i, X6 : $i]:
% 17.59/17.82         ((k3_xboole_0 @ X5 @ X6)
% 17.59/17.82           = (k5_xboole_0 @ (k5_xboole_0 @ X5 @ X6) @ (k2_xboole_0 @ X5 @ X6)))),
% 17.59/17.82      inference('cnf', [status(esa)], [t95_xboole_1])).
% 17.59/17.82  thf(commutativity_k5_xboole_0, axiom,
% 17.59/17.82    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 17.59/17.82  thf('91', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 17.59/17.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 17.59/17.82  thf(t91_xboole_1, axiom,
% 17.59/17.82    (![A:$i,B:$i,C:$i]:
% 17.59/17.82     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 17.59/17.82       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 17.59/17.82  thf('92', plain,
% 17.59/17.82      (![X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_xboole_0 @ (k5_xboole_0 @ X2 @ X3) @ X4)
% 17.59/17.82           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 17.59/17.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 17.59/17.82  thf('93', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 17.59/17.82           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['91', '92'])).
% 17.59/17.82  thf('94', plain,
% 17.59/17.82      (![X5 : $i, X6 : $i]:
% 17.59/17.82         ((k3_xboole_0 @ X5 @ X6)
% 17.59/17.82           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6))))),
% 17.59/17.82      inference('demod', [status(thm)], ['90', '93'])).
% 17.59/17.82  thf('95', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_xboole_0 @ X0 @ X1)
% 17.59/17.82           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 17.59/17.82      inference('sup+', [status(thm)], ['89', '94'])).
% 17.59/17.82  thf('96', plain,
% 17.59/17.82      (![X2 : $i, X3 : $i, X4 : $i]:
% 17.59/17.82         ((k5_xboole_0 @ (k5_xboole_0 @ X2 @ X3) @ X4)
% 17.59/17.82           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 17.59/17.82      inference('cnf', [status(esa)], [t91_xboole_1])).
% 17.59/17.82  thf('97', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 17.59/17.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 17.59/17.82  thf('98', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.59/17.82         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 17.59/17.82           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['96', '97'])).
% 17.59/17.82  thf('99', plain,
% 17.59/17.82      (![X5 : $i, X6 : $i]:
% 17.59/17.82         ((k3_xboole_0 @ X5 @ X6)
% 17.59/17.82           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6))))),
% 17.59/17.82      inference('demod', [status(thm)], ['90', '93'])).
% 17.59/17.82  thf('100', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_xboole_0 @ X1 @ X0)
% 17.59/17.82           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 17.59/17.82      inference('sup+', [status(thm)], ['98', '99'])).
% 17.59/17.82  thf('101', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 17.59/17.82      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 17.59/17.82  thf('102', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]:
% 17.59/17.82         ((k3_xboole_0 @ X1 @ X0)
% 17.59/17.82           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 17.59/17.82      inference('demod', [status(thm)], ['100', '101'])).
% 17.59/17.82  thf('103', plain,
% 17.59/17.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 17.59/17.82      inference('sup+', [status(thm)], ['95', '102'])).
% 17.59/17.82  thf(l27_zfmisc_1, axiom,
% 17.59/17.82    (![A:$i,B:$i]:
% 17.59/17.82     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 17.59/17.82  thf('104', plain,
% 17.59/17.82      (![X64 : $i, X65 : $i]:
% 17.59/17.82         ((r1_xboole_0 @ (k1_tarski @ X64) @ X65) | (r2_hidden @ X64 @ X65))),
% 17.59/17.82      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 17.59/17.82  thf('105', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 17.59/17.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.59/17.82  thf('106', plain, ((r2_hidden @ sk_A @ sk_B)),
% 17.59/17.82      inference('sup-', [status(thm)], ['104', '105'])).
% 17.59/17.82  thf(l31_zfmisc_1, axiom,
% 17.59/17.82    (![A:$i,B:$i]:
% 17.59/17.82     ( ( r2_hidden @ A @ B ) =>
% 17.59/17.82       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 17.59/17.82  thf('107', plain,
% 17.59/17.82      (![X66 : $i, X67 : $i]:
% 17.59/17.82         (((k3_xboole_0 @ X67 @ (k1_tarski @ X66)) = (k1_tarski @ X66))
% 17.59/17.82          | ~ (r2_hidden @ X66 @ X67))),
% 17.59/17.82      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 17.59/17.82  thf('108', plain,
% 17.59/17.82      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 17.59/17.82      inference('sup-', [status(thm)], ['106', '107'])).
% 17.59/17.82  thf('109', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 17.59/17.82      inference('demod', [status(thm)], ['0', '103', '108'])).
% 17.59/17.82  thf('110', plain, ($false), inference('simplify', [status(thm)], ['109'])).
% 17.59/17.82  
% 17.59/17.82  % SZS output end Refutation
% 17.59/17.82  
% 17.59/17.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
