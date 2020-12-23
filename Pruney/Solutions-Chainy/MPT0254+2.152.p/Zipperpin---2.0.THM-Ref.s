%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h2Xk1eZn20

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:54 EST 2020

% Result     : Theorem 17.68s
% Output     : Refutation 17.68s
% Verified   : 
% Statistics : Number of formulae       :  195 (1675 expanded)
%              Number of leaves         :   37 ( 589 expanded)
%              Depth                    :   19
%              Number of atoms          : 1616 (17295 expanded)
%              Number of equality atoms :  185 (1720 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X49 )
      = ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('13',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k4_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61 )
      = ( k3_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('14',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 )
      = ( k2_enumset1 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('16',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i,X66: $i,X67: $i] :
      ( ( k5_enumset1 @ X62 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 )
      = ( k4_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('17',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t60_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k5_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t60_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 )
      = ( k2_enumset1 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X2 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k2_enumset1 @ X15 @ X14 @ X13 @ X12 )
      = ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('25',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('31',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','28'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('38',plain,(
    ! [X78: $i,X79: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X78 ) @ ( k1_tarski @ X79 ) )
        = ( k1_tarski @ X78 ) )
      | ( X78 = X79 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X1 ) @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
        = ( k1_tarski @ X1 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X1 ) @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('44',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('45',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 )
      = ( k2_enumset1 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k6_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 ) @ ( k1_enumset1 @ X28 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('48',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ( k6_enumset1 @ X68 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 )
      = ( k5_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i,X66: $i,X67: $i] :
      ( ( k5_enumset1 @ X62 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 )
      = ( k4_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X5 @ X4 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_enumset1 @ X0 @ X1 @ X1 )
        = ( k1_enumset1 @ X0 @ X0 @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['42','43','52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['55'])).

thf('57',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X49 )
      = ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','28'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','60','61'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('63',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','66'])).

thf('68',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('69',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('73',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('76',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('77',plain,(
    ! [X80: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X80 ) )
      = X80 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','81'])).

thf('83',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['68','82'])).

thf('84',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('85',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('87',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('89',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['67','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','80'])).

thf('92',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('93',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('94',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('97',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','104'])).

thf('106',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['67','89'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['55'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['55'])).

thf('112',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X49 )
      = ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('113',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['111','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ k1_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['110','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['109','118'])).

thf('120',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X49 )
      = ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('121',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k5_xboole_0 @ X11 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','81'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','80'])).

thf('130',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','80'])).

thf('136',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['67','89'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('141',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','81'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['71','81'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','80'])).

thf('150',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['8','90','107','108','134','135','136','139','148','149'])).

thf('151',plain,(
    ! [X77: $i,X78: $i] :
      ( ( X78 != X77 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X78 ) @ ( k1_tarski @ X77 ) )
       != ( k1_tarski @ X78 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('152',plain,(
    ! [X77: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X77 ) @ ( k1_tarski @ X77 ) )
     != ( k1_tarski @ X77 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('154',plain,(
    ! [X77: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X77 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['150','154'])).

thf('156',plain,(
    $false ),
    inference(simplify,[status(thm)],['155'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h2Xk1eZn20
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:16:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 17.68/17.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.68/17.95  % Solved by: fo/fo7.sh
% 17.68/17.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.68/17.95  % done 8703 iterations in 17.493s
% 17.68/17.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.68/17.95  % SZS output start Refutation
% 17.68/17.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 17.68/17.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.68/17.95  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 17.68/17.95  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 17.68/17.95  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 17.68/17.95                                           $i > $i).
% 17.68/17.95  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 17.68/17.95  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 17.68/17.95  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 17.68/17.95  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 17.68/17.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.68/17.95  thf(sk_A_type, type, sk_A: $i).
% 17.68/17.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 17.68/17.95  thf(sk_B_type, type, sk_B: $i).
% 17.68/17.95  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 17.68/17.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.68/17.95  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 17.68/17.95  thf(t100_xboole_1, axiom,
% 17.68/17.95    (![A:$i,B:$i]:
% 17.68/17.95     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 17.68/17.95  thf('0', plain,
% 17.68/17.95      (![X1 : $i, X2 : $i]:
% 17.68/17.95         ((k4_xboole_0 @ X1 @ X2)
% 17.68/17.95           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 17.68/17.95  thf(t49_zfmisc_1, conjecture,
% 17.68/17.95    (![A:$i,B:$i]:
% 17.68/17.95     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 17.68/17.95  thf(zf_stmt_0, negated_conjecture,
% 17.68/17.95    (~( ![A:$i,B:$i]:
% 17.68/17.95        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 17.68/17.95    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 17.68/17.95  thf('1', plain,
% 17.68/17.95      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 17.68/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.68/17.95  thf(t95_xboole_1, axiom,
% 17.68/17.95    (![A:$i,B:$i]:
% 17.68/17.95     ( ( k3_xboole_0 @ A @ B ) =
% 17.68/17.95       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 17.68/17.95  thf('2', plain,
% 17.68/17.95      (![X10 : $i, X11 : $i]:
% 17.68/17.95         ((k3_xboole_0 @ X10 @ X11)
% 17.68/17.95           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 17.68/17.95              (k2_xboole_0 @ X10 @ X11)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t95_xboole_1])).
% 17.68/17.95  thf('3', plain,
% 17.68/17.95      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 17.68/17.95         = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 17.68/17.95            k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['1', '2'])).
% 17.68/17.95  thf(t5_boole, axiom,
% 17.68/17.95    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 17.68/17.95  thf('4', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 17.68/17.95      inference('cnf', [status(esa)], [t5_boole])).
% 17.68/17.95  thf('5', plain,
% 17.68/17.95      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 17.68/17.95         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 17.68/17.95      inference('demod', [status(thm)], ['3', '4'])).
% 17.68/17.95  thf(t91_xboole_1, axiom,
% 17.68/17.95    (![A:$i,B:$i,C:$i]:
% 17.68/17.95     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 17.68/17.95       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 17.68/17.95  thf('6', plain,
% 17.68/17.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 17.68/17.95           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 17.68/17.95  thf('7', plain,
% 17.68/17.95      (![X0 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)
% 17.68/17.95           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ sk_B @ X0)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['5', '6'])).
% 17.68/17.95  thf('8', plain,
% 17.68/17.95      (![X0 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 17.68/17.95           (k3_xboole_0 @ sk_B @ X0))
% 17.68/17.95           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ sk_B @ X0)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['0', '7'])).
% 17.68/17.95  thf('9', plain,
% 17.68/17.95      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 17.68/17.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.68/17.95  thf(t70_enumset1, axiom,
% 17.68/17.95    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 17.68/17.95  thf('10', plain,
% 17.68/17.95      (![X48 : $i, X49 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X48 @ X48 @ X49) = (k2_tarski @ X48 @ X49))),
% 17.68/17.95      inference('cnf', [status(esa)], [t70_enumset1])).
% 17.68/17.95  thf(t69_enumset1, axiom,
% 17.68/17.95    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 17.68/17.95  thf('11', plain,
% 17.68/17.95      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 17.68/17.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 17.68/17.95  thf('12', plain,
% 17.68/17.95      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['10', '11'])).
% 17.68/17.95  thf(t73_enumset1, axiom,
% 17.68/17.95    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 17.68/17.95     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 17.68/17.95       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 17.68/17.95  thf('13', plain,
% 17.68/17.95      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 17.68/17.95         ((k4_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61)
% 17.68/17.95           = (k3_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61))),
% 17.68/17.95      inference('cnf', [status(esa)], [t73_enumset1])).
% 17.68/17.95  thf(t72_enumset1, axiom,
% 17.68/17.95    (![A:$i,B:$i,C:$i,D:$i]:
% 17.68/17.95     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 17.68/17.95  thf('14', plain,
% 17.68/17.95      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 17.68/17.95         ((k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56)
% 17.68/17.95           = (k2_enumset1 @ X53 @ X54 @ X55 @ X56))),
% 17.68/17.95      inference('cnf', [status(esa)], [t72_enumset1])).
% 17.68/17.95  thf('15', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.68/17.95         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 17.68/17.95           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['13', '14'])).
% 17.68/17.95  thf(t74_enumset1, axiom,
% 17.68/17.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 17.68/17.95     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 17.68/17.95       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 17.68/17.95  thf('16', plain,
% 17.68/17.95      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i]:
% 17.68/17.95         ((k5_enumset1 @ X62 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67)
% 17.68/17.95           = (k4_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67))),
% 17.68/17.95      inference('cnf', [status(esa)], [t74_enumset1])).
% 17.68/17.95  thf('17', plain,
% 17.68/17.95      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 17.68/17.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 17.68/17.95  thf(t60_enumset1, axiom,
% 17.68/17.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 17.68/17.95     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 17.68/17.95       ( k2_xboole_0 @
% 17.68/17.95         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k2_tarski @ F @ G ) ) ))).
% 17.68/17.95  thf('18', plain,
% 17.68/17.95      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 17.68/17.95         ((k5_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20 @ X21 @ X22)
% 17.68/17.95           = (k2_xboole_0 @ (k3_enumset1 @ X16 @ X17 @ X18 @ X19 @ X20) @ 
% 17.68/17.95              (k2_tarski @ X21 @ X22)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t60_enumset1])).
% 17.68/17.95  thf('19', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 17.68/17.95         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 17.68/17.95           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 17.68/17.95              (k1_tarski @ X0)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['17', '18'])).
% 17.68/17.95  thf('20', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.68/17.95         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 17.68/17.95           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 17.68/17.95              (k1_tarski @ X0)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['16', '19'])).
% 17.68/17.95  thf('21', plain,
% 17.68/17.95      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 17.68/17.95         ((k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56)
% 17.68/17.95           = (k2_enumset1 @ X53 @ X54 @ X55 @ X56))),
% 17.68/17.95      inference('cnf', [status(esa)], [t72_enumset1])).
% 17.68/17.95  thf('22', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 17.68/17.95         ((k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0)
% 17.68/17.95           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 17.68/17.95              (k1_tarski @ X0)))),
% 17.68/17.95      inference('demod', [status(thm)], ['20', '21'])).
% 17.68/17.95  thf('23', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.68/17.95         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0)
% 17.68/17.95           = (k2_xboole_0 @ (k2_enumset1 @ X2 @ X2 @ X2 @ X1) @ 
% 17.68/17.95              (k1_tarski @ X0)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['15', '22'])).
% 17.68/17.95  thf(t125_enumset1, axiom,
% 17.68/17.95    (![A:$i,B:$i,C:$i,D:$i]:
% 17.68/17.95     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 17.68/17.95  thf('24', plain,
% 17.68/17.95      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 17.68/17.95         ((k2_enumset1 @ X15 @ X14 @ X13 @ X12)
% 17.68/17.95           = (k2_enumset1 @ X12 @ X13 @ X14 @ X15))),
% 17.68/17.95      inference('cnf', [status(esa)], [t125_enumset1])).
% 17.68/17.95  thf(t71_enumset1, axiom,
% 17.68/17.95    (![A:$i,B:$i,C:$i]:
% 17.68/17.95     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 17.68/17.95  thf('25', plain,
% 17.68/17.95      (![X50 : $i, X51 : $i, X52 : $i]:
% 17.68/17.95         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 17.68/17.95           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 17.68/17.95      inference('cnf', [status(esa)], [t71_enumset1])).
% 17.68/17.95  thf('26', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.68/17.95         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 17.68/17.95      inference('sup+', [status(thm)], ['24', '25'])).
% 17.68/17.95  thf('27', plain,
% 17.68/17.95      (![X50 : $i, X51 : $i, X52 : $i]:
% 17.68/17.95         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 17.68/17.95           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 17.68/17.95      inference('cnf', [status(esa)], [t71_enumset1])).
% 17.68/17.95  thf('28', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X0 @ X1 @ X2)
% 17.68/17.95           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 17.68/17.95      inference('demod', [status(thm)], ['23', '26', '27'])).
% 17.68/17.95  thf('29', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X1 @ X0 @ X0)
% 17.68/17.95           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['12', '28'])).
% 17.68/17.95  thf('30', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.68/17.95         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 17.68/17.95      inference('sup+', [status(thm)], ['24', '25'])).
% 17.68/17.95  thf('31', plain,
% 17.68/17.95      (![X50 : $i, X51 : $i, X52 : $i]:
% 17.68/17.95         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 17.68/17.95           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 17.68/17.95      inference('cnf', [status(esa)], [t71_enumset1])).
% 17.68/17.95  thf('32', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 17.68/17.95      inference('sup+', [status(thm)], ['30', '31'])).
% 17.68/17.95  thf('33', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 17.68/17.95           = (k1_enumset1 @ X1 @ X0 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['29', '32'])).
% 17.68/17.95  thf('34', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X1 @ X0 @ X0)
% 17.68/17.95           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['12', '28'])).
% 17.68/17.95  thf('35', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 17.68/17.95           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['33', '34'])).
% 17.68/17.95  thf('36', plain,
% 17.68/17.95      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['10', '11'])).
% 17.68/17.95  thf('37', plain,
% 17.68/17.95      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['10', '11'])).
% 17.68/17.95  thf(t20_zfmisc_1, axiom,
% 17.68/17.95    (![A:$i,B:$i]:
% 17.68/17.95     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 17.68/17.95         ( k1_tarski @ A ) ) <=>
% 17.68/17.95       ( ( A ) != ( B ) ) ))).
% 17.68/17.95  thf('38', plain,
% 17.68/17.95      (![X78 : $i, X79 : $i]:
% 17.68/17.95         (((k4_xboole_0 @ (k1_tarski @ X78) @ (k1_tarski @ X79))
% 17.68/17.95            = (k1_tarski @ X78))
% 17.68/17.95          | ((X78) = (X79)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 17.68/17.95  thf('39', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         (((k4_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ (k1_tarski @ X1))
% 17.68/17.95            = (k1_tarski @ X0))
% 17.68/17.95          | ((X0) = (X1)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['37', '38'])).
% 17.68/17.95  thf('40', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         (((k4_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X1) @ 
% 17.68/17.95            (k1_enumset1 @ X0 @ X0 @ X0)) = (k1_tarski @ X1))
% 17.68/17.95          | ((X1) = (X0)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['36', '39'])).
% 17.68/17.95  thf(t39_xboole_1, axiom,
% 17.68/17.95    (![A:$i,B:$i]:
% 17.68/17.95     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 17.68/17.95  thf('41', plain,
% 17.68/17.95      (![X3 : $i, X4 : $i]:
% 17.68/17.95         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 17.68/17.95           = (k2_xboole_0 @ X3 @ X4))),
% 17.68/17.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 17.68/17.95  thf('42', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         (((k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X1) @ (k1_tarski @ X0))
% 17.68/17.95            = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X1) @ 
% 17.68/17.95               (k1_enumset1 @ X0 @ X0 @ X0)))
% 17.68/17.95          | ((X0) = (X1)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['40', '41'])).
% 17.68/17.95  thf('43', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X0 @ X1 @ X2)
% 17.68/17.95           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 17.68/17.95      inference('demod', [status(thm)], ['23', '26', '27'])).
% 17.68/17.95  thf('44', plain,
% 17.68/17.95      (![X50 : $i, X51 : $i, X52 : $i]:
% 17.68/17.95         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 17.68/17.95           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 17.68/17.95      inference('cnf', [status(esa)], [t71_enumset1])).
% 17.68/17.95  thf('45', plain,
% 17.68/17.95      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 17.68/17.95         ((k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56)
% 17.68/17.95           = (k2_enumset1 @ X53 @ X54 @ X55 @ X56))),
% 17.68/17.95      inference('cnf', [status(esa)], [t72_enumset1])).
% 17.68/17.95  thf(t66_enumset1, axiom,
% 17.68/17.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 17.68/17.95     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 17.68/17.95       ( k2_xboole_0 @
% 17.68/17.95         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 17.68/17.95  thf('46', plain,
% 17.68/17.95      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, 
% 17.68/17.95         X30 : $i]:
% 17.68/17.95         ((k6_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 17.68/17.95           = (k2_xboole_0 @ (k3_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27) @ 
% 17.68/17.95              (k1_enumset1 @ X28 @ X29 @ X30)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t66_enumset1])).
% 17.68/17.95  thf('47', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 17.68/17.95         ((k6_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4)
% 17.68/17.95           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 17.68/17.95              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['45', '46'])).
% 17.68/17.95  thf(t75_enumset1, axiom,
% 17.68/17.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 17.68/17.95     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 17.68/17.95       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 17.68/17.95  thf('48', plain,
% 17.68/17.95      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 17.68/17.95         ((k6_enumset1 @ X68 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74)
% 17.68/17.95           = (k5_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74))),
% 17.68/17.95      inference('cnf', [status(esa)], [t75_enumset1])).
% 17.68/17.95  thf('49', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 17.68/17.95         ((k5_enumset1 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4)
% 17.68/17.95           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 17.68/17.95              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 17.68/17.95      inference('demod', [status(thm)], ['47', '48'])).
% 17.68/17.95  thf('50', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 17.68/17.95         ((k5_enumset1 @ X2 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 17.68/17.95           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 17.68/17.95              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['44', '49'])).
% 17.68/17.95  thf('51', plain,
% 17.68/17.95      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i]:
% 17.68/17.95         ((k5_enumset1 @ X62 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67)
% 17.68/17.95           = (k4_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67))),
% 17.68/17.95      inference('cnf', [status(esa)], [t74_enumset1])).
% 17.68/17.95  thf('52', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 17.68/17.95         ((k4_enumset1 @ X2 @ X1 @ X0 @ X5 @ X4 @ X3)
% 17.68/17.95           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 17.68/17.95              (k1_enumset1 @ X5 @ X4 @ X3)))),
% 17.68/17.95      inference('demod', [status(thm)], ['50', '51'])).
% 17.68/17.95  thf('53', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.68/17.95         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 17.68/17.95           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['13', '14'])).
% 17.68/17.95  thf('54', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.68/17.95         ((k2_enumset1 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 17.68/17.95      inference('sup+', [status(thm)], ['24', '25'])).
% 17.68/17.95  thf('55', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         (((k1_enumset1 @ X0 @ X1 @ X1) = (k1_enumset1 @ X0 @ X0 @ X1))
% 17.68/17.95          | ((X0) = (X1)))),
% 17.68/17.95      inference('demod', [status(thm)], ['42', '43', '52', '53', '54'])).
% 17.68/17.95  thf('56', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 17.68/17.95      inference('condensation', [status(thm)], ['55'])).
% 17.68/17.95  thf('57', plain,
% 17.68/17.95      (![X48 : $i, X49 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X48 @ X48 @ X49) = (k2_tarski @ X48 @ X49))),
% 17.68/17.95      inference('cnf', [status(esa)], [t70_enumset1])).
% 17.68/17.95  thf('58', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['56', '57'])).
% 17.68/17.95  thf('59', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X1 @ X0 @ X0)
% 17.68/17.95           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['12', '28'])).
% 17.68/17.95  thf('60', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k2_tarski @ X1 @ X0)
% 17.68/17.95           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['58', '59'])).
% 17.68/17.95  thf('61', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k2_tarski @ X1 @ X0)
% 17.68/17.95           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['58', '59'])).
% 17.68/17.95  thf('62', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]: ((k2_tarski @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['35', '60', '61'])).
% 17.68/17.95  thf(l51_zfmisc_1, axiom,
% 17.68/17.95    (![A:$i,B:$i]:
% 17.68/17.95     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 17.68/17.95  thf('63', plain,
% 17.68/17.95      (![X75 : $i, X76 : $i]:
% 17.68/17.95         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 17.68/17.95      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 17.68/17.95  thf('64', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 17.68/17.95      inference('sup+', [status(thm)], ['62', '63'])).
% 17.68/17.95  thf('65', plain,
% 17.68/17.95      (![X75 : $i, X76 : $i]:
% 17.68/17.95         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 17.68/17.95      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 17.68/17.95  thf('66', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 17.68/17.95      inference('sup+', [status(thm)], ['64', '65'])).
% 17.68/17.95  thf('67', plain,
% 17.68/17.95      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 17.68/17.95      inference('demod', [status(thm)], ['9', '66'])).
% 17.68/17.95  thf('68', plain,
% 17.68/17.95      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 17.68/17.95         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 17.68/17.95      inference('demod', [status(thm)], ['3', '4'])).
% 17.68/17.95  thf(t92_xboole_1, axiom,
% 17.68/17.95    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 17.68/17.95  thf('69', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 17.68/17.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 17.68/17.95  thf('70', plain,
% 17.68/17.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 17.68/17.95           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 17.68/17.95  thf('71', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 17.68/17.95           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['69', '70'])).
% 17.68/17.95  thf('72', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 17.68/17.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 17.68/17.95  thf('73', plain,
% 17.68/17.95      (![X10 : $i, X11 : $i]:
% 17.68/17.95         ((k3_xboole_0 @ X10 @ X11)
% 17.68/17.95           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 17.68/17.95              (k2_xboole_0 @ X10 @ X11)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t95_xboole_1])).
% 17.68/17.95  thf('74', plain,
% 17.68/17.95      (![X0 : $i]:
% 17.68/17.95         ((k3_xboole_0 @ X0 @ X0)
% 17.68/17.95           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['72', '73'])).
% 17.68/17.95  thf(idempotence_k3_xboole_0, axiom,
% 17.68/17.95    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 17.68/17.95  thf('75', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 17.68/17.95      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 17.68/17.95  thf('76', plain,
% 17.68/17.95      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 17.68/17.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 17.68/17.95  thf(t31_zfmisc_1, axiom,
% 17.68/17.95    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 17.68/17.95  thf('77', plain, (![X80 : $i]: ((k3_tarski @ (k1_tarski @ X80)) = (X80))),
% 17.68/17.95      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 17.68/17.95  thf('78', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['76', '77'])).
% 17.68/17.95  thf('79', plain,
% 17.68/17.95      (![X75 : $i, X76 : $i]:
% 17.68/17.95         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 17.68/17.95      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 17.68/17.95  thf('80', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['78', '79'])).
% 17.68/17.95  thf('81', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['74', '75', '80'])).
% 17.68/17.95  thf('82', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.68/17.95      inference('demod', [status(thm)], ['71', '81'])).
% 17.68/17.95  thf('83', plain,
% 17.68/17.95      (((sk_B)
% 17.68/17.95         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 17.68/17.95            (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['68', '82'])).
% 17.68/17.95  thf('84', plain,
% 17.68/17.95      (![X1 : $i, X2 : $i]:
% 17.68/17.95         ((k4_xboole_0 @ X1 @ X2)
% 17.68/17.95           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 17.68/17.95  thf('85', plain, (((sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 17.68/17.95      inference('demod', [status(thm)], ['83', '84'])).
% 17.68/17.95  thf('86', plain,
% 17.68/17.95      (![X3 : $i, X4 : $i]:
% 17.68/17.95         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 17.68/17.95           = (k2_xboole_0 @ X3 @ X4))),
% 17.68/17.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 17.68/17.95  thf('87', plain,
% 17.68/17.95      (((k2_xboole_0 @ sk_B @ sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['85', '86'])).
% 17.68/17.95  thf('88', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['78', '79'])).
% 17.68/17.95  thf('89', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 17.68/17.95      inference('demod', [status(thm)], ['87', '88'])).
% 17.68/17.95  thf('90', plain, (((sk_B) = (k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['67', '89'])).
% 17.68/17.95  thf('91', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['74', '75', '80'])).
% 17.68/17.95  thf('92', plain,
% 17.68/17.95      (![X10 : $i, X11 : $i]:
% 17.68/17.95         ((k3_xboole_0 @ X10 @ X11)
% 17.68/17.95           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 17.68/17.95              (k2_xboole_0 @ X10 @ X11)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t95_xboole_1])).
% 17.68/17.95  thf('93', plain,
% 17.68/17.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 17.68/17.95           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 17.68/17.95  thf('94', plain,
% 17.68/17.95      (![X10 : $i, X11 : $i]:
% 17.68/17.95         ((k3_xboole_0 @ X10 @ X11)
% 17.68/17.95           = (k5_xboole_0 @ X10 @ 
% 17.68/17.95              (k5_xboole_0 @ X11 @ (k2_xboole_0 @ X10 @ X11))))),
% 17.68/17.95      inference('demod', [status(thm)], ['92', '93'])).
% 17.68/17.95  thf('95', plain,
% 17.68/17.95      (![X0 : $i]:
% 17.68/17.95         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 17.68/17.95           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['91', '94'])).
% 17.68/17.95  thf('96', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 17.68/17.95      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 17.68/17.95  thf('97', plain,
% 17.68/17.95      (![X1 : $i, X2 : $i]:
% 17.68/17.95         ((k4_xboole_0 @ X1 @ X2)
% 17.68/17.95           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 17.68/17.95  thf('98', plain,
% 17.68/17.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['96', '97'])).
% 17.68/17.95  thf('99', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 17.68/17.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 17.68/17.95  thf('100', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['98', '99'])).
% 17.68/17.95  thf('101', plain,
% 17.68/17.95      (![X3 : $i, X4 : $i]:
% 17.68/17.95         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 17.68/17.95           = (k2_xboole_0 @ X3 @ X4))),
% 17.68/17.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 17.68/17.95  thf('102', plain,
% 17.68/17.95      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['100', '101'])).
% 17.68/17.95  thf('103', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['78', '79'])).
% 17.68/17.95  thf('104', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['102', '103'])).
% 17.68/17.95  thf('105', plain,
% 17.68/17.95      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['95', '104'])).
% 17.68/17.95  thf('106', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 17.68/17.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 17.68/17.95  thf('107', plain,
% 17.68/17.95      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['105', '106'])).
% 17.68/17.95  thf('108', plain, (((sk_B) = (k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['67', '89'])).
% 17.68/17.95  thf('109', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 17.68/17.95      inference('condensation', [status(thm)], ['55'])).
% 17.68/17.95  thf('110', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 17.68/17.95      inference('sup+', [status(thm)], ['30', '31'])).
% 17.68/17.95  thf('111', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X1 @ X0 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 17.68/17.95      inference('condensation', [status(thm)], ['55'])).
% 17.68/17.95  thf('112', plain,
% 17.68/17.95      (![X48 : $i, X49 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X48 @ X48 @ X49) = (k2_tarski @ X48 @ X49))),
% 17.68/17.95      inference('cnf', [status(esa)], [t70_enumset1])).
% 17.68/17.95  thf('113', plain,
% 17.68/17.95      (![X75 : $i, X76 : $i]:
% 17.68/17.95         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 17.68/17.95      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 17.68/17.95  thf('114', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['112', '113'])).
% 17.68/17.95  thf('115', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['102', '103'])).
% 17.68/17.95  thf('116', plain,
% 17.68/17.95      (![X0 : $i]: ((k3_tarski @ (k1_enumset1 @ X0 @ X0 @ k1_xboole_0)) = (X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['114', '115'])).
% 17.68/17.95  thf('117', plain,
% 17.68/17.95      (![X0 : $i]:
% 17.68/17.95         ((k3_tarski @ (k1_enumset1 @ X0 @ k1_xboole_0 @ k1_xboole_0)) = (X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['111', '116'])).
% 17.68/17.95  thf('118', plain,
% 17.68/17.95      (![X0 : $i]: ((k3_tarski @ (k1_enumset1 @ k1_xboole_0 @ X0 @ X0)) = (X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['110', '117'])).
% 17.68/17.95  thf('119', plain,
% 17.68/17.95      (![X0 : $i]:
% 17.68/17.95         ((k3_tarski @ (k1_enumset1 @ k1_xboole_0 @ k1_xboole_0 @ X0)) = (X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['109', '118'])).
% 17.68/17.95  thf('120', plain,
% 17.68/17.95      (![X48 : $i, X49 : $i]:
% 17.68/17.95         ((k1_enumset1 @ X48 @ X48 @ X49) = (k2_tarski @ X48 @ X49))),
% 17.68/17.95      inference('cnf', [status(esa)], [t70_enumset1])).
% 17.68/17.95  thf('121', plain,
% 17.68/17.95      (![X75 : $i, X76 : $i]:
% 17.68/17.95         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 17.68/17.95      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 17.68/17.95  thf('122', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['119', '120', '121'])).
% 17.68/17.95  thf('123', plain,
% 17.68/17.95      (![X10 : $i, X11 : $i]:
% 17.68/17.95         ((k3_xboole_0 @ X10 @ X11)
% 17.68/17.95           = (k5_xboole_0 @ X10 @ 
% 17.68/17.95              (k5_xboole_0 @ X11 @ (k2_xboole_0 @ X10 @ X11))))),
% 17.68/17.95      inference('demod', [status(thm)], ['92', '93'])).
% 17.68/17.95  thf('124', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.68/17.95      inference('demod', [status(thm)], ['71', '81'])).
% 17.68/17.95  thf('125', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 17.68/17.95           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 17.68/17.95      inference('sup+', [status(thm)], ['123', '124'])).
% 17.68/17.95  thf('126', plain,
% 17.68/17.95      (![X1 : $i, X2 : $i]:
% 17.68/17.95         ((k4_xboole_0 @ X1 @ X2)
% 17.68/17.95           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 17.68/17.95  thf('127', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 17.68/17.95           = (k4_xboole_0 @ X1 @ X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['125', '126'])).
% 17.68/17.95  thf('128', plain,
% 17.68/17.95      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['122', '127'])).
% 17.68/17.95  thf('129', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['74', '75', '80'])).
% 17.68/17.95  thf('130', plain,
% 17.68/17.95      (![X1 : $i, X2 : $i]:
% 17.68/17.95         ((k4_xboole_0 @ X1 @ X2)
% 17.68/17.95           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t100_xboole_1])).
% 17.68/17.95  thf('131', plain,
% 17.68/17.95      (![X0 : $i]:
% 17.68/17.95         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['129', '130'])).
% 17.68/17.95  thf('132', plain,
% 17.68/17.95      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['128', '131'])).
% 17.68/17.95  thf('133', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 17.68/17.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 17.68/17.95  thf('134', plain,
% 17.68/17.95      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['132', '133'])).
% 17.68/17.95  thf('135', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['74', '75', '80'])).
% 17.68/17.95  thf('136', plain, (((sk_B) = (k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['67', '89'])).
% 17.68/17.95  thf('137', plain,
% 17.68/17.95      (![X0 : $i]:
% 17.68/17.95         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['129', '130'])).
% 17.68/17.95  thf('138', plain,
% 17.68/17.95      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['132', '133'])).
% 17.68/17.95  thf('139', plain,
% 17.68/17.95      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 17.68/17.95      inference('demod', [status(thm)], ['137', '138'])).
% 17.68/17.95  thf('140', plain,
% 17.68/17.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 17.68/17.95           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t91_xboole_1])).
% 17.68/17.95  thf('141', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 17.68/17.95      inference('cnf', [status(esa)], [t92_xboole_1])).
% 17.68/17.95  thf('142', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 17.68/17.95           = (k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['140', '141'])).
% 17.68/17.95  thf('143', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.68/17.95      inference('demod', [status(thm)], ['71', '81'])).
% 17.68/17.95  thf('144', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 17.68/17.95           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['142', '143'])).
% 17.68/17.95  thf('145', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 17.68/17.95      inference('cnf', [status(esa)], [t5_boole])).
% 17.68/17.95  thf('146', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 17.68/17.95      inference('demod', [status(thm)], ['144', '145'])).
% 17.68/17.95  thf('147', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]:
% 17.68/17.95         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.68/17.95      inference('demod', [status(thm)], ['71', '81'])).
% 17.68/17.95  thf('148', plain,
% 17.68/17.95      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['146', '147'])).
% 17.68/17.95  thf('149', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 17.68/17.95      inference('demod', [status(thm)], ['74', '75', '80'])).
% 17.68/17.95  thf('150', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 17.68/17.95      inference('demod', [status(thm)],
% 17.68/17.95                ['8', '90', '107', '108', '134', '135', '136', '139', '148', 
% 17.68/17.95                 '149'])).
% 17.68/17.95  thf('151', plain,
% 17.68/17.95      (![X77 : $i, X78 : $i]:
% 17.68/17.95         (((X78) != (X77))
% 17.68/17.95          | ((k4_xboole_0 @ (k1_tarski @ X78) @ (k1_tarski @ X77))
% 17.68/17.95              != (k1_tarski @ X78)))),
% 17.68/17.95      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 17.68/17.95  thf('152', plain,
% 17.68/17.95      (![X77 : $i]:
% 17.68/17.95         ((k4_xboole_0 @ (k1_tarski @ X77) @ (k1_tarski @ X77))
% 17.68/17.95           != (k1_tarski @ X77))),
% 17.68/17.95      inference('simplify', [status(thm)], ['151'])).
% 17.68/17.95  thf('153', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 17.68/17.95      inference('sup+', [status(thm)], ['98', '99'])).
% 17.68/17.95  thf('154', plain, (![X77 : $i]: ((k1_xboole_0) != (k1_tarski @ X77))),
% 17.68/17.95      inference('demod', [status(thm)], ['152', '153'])).
% 17.68/17.95  thf('155', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 17.68/17.95      inference('sup-', [status(thm)], ['150', '154'])).
% 17.68/17.95  thf('156', plain, ($false), inference('simplify', [status(thm)], ['155'])).
% 17.68/17.95  
% 17.68/17.95  % SZS output end Refutation
% 17.68/17.95  
% 17.77/17.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
