%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tX3fbCp8hr

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 199 expanded)
%              Number of leaves         :   22 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  781 (2272 expanded)
%              Number of equality atoms :   58 ( 187 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t92_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t92_enumset1])).

thf('0',plain,(
    ( k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_enumset1,axiom,(
    ! [A: $i] :
      ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X54: $i] :
      ( ( k4_enumset1 @ X54 @ X54 @ X54 @ X54 @ X54 @ X54 )
      = ( k1_tarski @ X54 ) ) ),
    inference(cnf,[status(esa)],[t91_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k4_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 @ X50 )
      = ( k3_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t83_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X52 @ X52 @ X53 )
      = ( k2_tarski @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t83_enumset1])).

thf('4',plain,(
    ! [X54: $i] :
      ( ( k2_tarski @ X54 @ X54 )
      = ( k1_tarski @ X54 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t67_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf('7',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k6_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 ) @ ( k2_tarski @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t67_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X54: $i] :
      ( ( k2_tarski @ X54 @ X54 )
      = ( k1_tarski @ X54 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf(t82_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X51: $i] :
      ( ( k2_enumset1 @ X51 @ X51 @ X51 @ X51 )
      = ( k1_tarski @ X51 ) ) ),
    inference(cnf,[status(esa)],[t82_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('11',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('12',plain,(
    ! [X51: $i] :
      ( ( k1_enumset1 @ X51 @ X51 @ X51 )
      = ( k1_tarski @ X51 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('16',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) @ ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X6 @ X5 @ X4 @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X54: $i] :
      ( ( k2_tarski @ X54 @ X54 )
      = ( k1_tarski @ X54 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('24',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) @ ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_enumset1 @ X52 @ X52 @ X52 @ X52 @ X53 )
      = ( k2_tarski @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t83_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t58_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) @ ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t58_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k5_enumset1 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 )
      = ( k5_enumset1 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tX3fbCp8hr
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 165 iterations in 0.112s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.20/0.57                                           $i > $i).
% 0.20/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.57  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(t92_enumset1, conjecture,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i,B:$i]:
% 0.20/0.57        ( ( k5_enumset1 @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t92_enumset1])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      (((k5_enumset1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B)
% 0.20/0.57         != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t91_enumset1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k4_enumset1 @ A @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      (![X54 : $i]:
% 0.20/0.57         ((k4_enumset1 @ X54 @ X54 @ X54 @ X54 @ X54 @ X54) = (k1_tarski @ X54))),
% 0.20/0.57      inference('cnf', [status(esa)], [t91_enumset1])).
% 0.20/0.57  thf(t73_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.57     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.57       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.20/0.57         ((k4_enumset1 @ X46 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.20/0.57           = (k3_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 0.20/0.57      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.57  thf(t83_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k3_enumset1 @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X52 : $i, X53 : $i]:
% 0.20/0.57         ((k3_enumset1 @ X52 @ X52 @ X52 @ X52 @ X53) = (k2_tarski @ X52 @ X53))),
% 0.20/0.57      inference('cnf', [status(esa)], [t83_enumset1])).
% 0.20/0.57  thf('4', plain, (![X54 : $i]: ((k2_tarski @ X54 @ X54) = (k1_tarski @ X54))),
% 0.20/0.57      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.20/0.57  thf(t61_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.57     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.57       ( k2_xboole_0 @
% 0.20/0.57         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.57         ((k5_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.20/0.57           = (k2_xboole_0 @ 
% 0.20/0.57              (k4_enumset1 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25) @ 
% 0.20/0.57              (k1_tarski @ X26)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.57         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.57           = (k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.20/0.57              (k2_tarski @ X0 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.57  thf(t67_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.57     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.57       ( k2_xboole_0 @
% 0.20/0.57         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, 
% 0.20/0.57         X42 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42)
% 0.20/0.57           = (k2_xboole_0 @ 
% 0.20/0.57              (k4_enumset1 @ X35 @ X36 @ X37 @ X38 @ X39 @ X40) @ 
% 0.20/0.57              (k2_tarski @ X41 @ X42)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t67_enumset1])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.57         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.57           = (k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.57  thf('9', plain, (![X54 : $i]: ((k2_tarski @ X54 @ X54) = (k1_tarski @ X54))),
% 0.20/0.57      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.20/0.57  thf(t82_enumset1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k2_enumset1 @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (![X51 : $i]: ((k2_enumset1 @ X51 @ X51 @ X51 @ X51) = (k1_tarski @ X51))),
% 0.20/0.57      inference('cnf', [status(esa)], [t82_enumset1])).
% 0.20/0.57  thf(t71_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.57  thf('11', plain,
% 0.20/0.57      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.20/0.57         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.20/0.57           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.20/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X51 : $i]: ((k1_enumset1 @ X51 @ X51 @ X51) = (k1_tarski @ X51))),
% 0.20/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k2_tarski @ X0 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['9', '12'])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.20/0.57         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.20/0.57           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.20/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k2_tarski @ X0 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['9', '12'])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.20/0.57         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.20/0.57           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.20/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.57  thf(l75_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.20/0.57     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.20/0.57       ( k2_xboole_0 @
% 0.20/0.57         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.20/0.57           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3) @ 
% 0.20/0.57              (k2_enumset1 @ X4 @ X5 @ X6 @ X7)))),
% 0.20/0.57      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.20/0.57  thf('18', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X2 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 @ X3)
% 0.20/0.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ 
% 0.20/0.57              (k2_enumset1 @ X6 @ X5 @ X4 @ X3)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.20/0.57           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 0.20/0.57              (k2_enumset1 @ X4 @ X3 @ X2 @ X1)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['15', '18'])).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.20/0.57           = (k2_xboole_0 @ (k2_tarski @ X3 @ X3) @ 
% 0.20/0.57              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['14', '19'])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0 @ X0)
% 0.20/0.57           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['13', '20'])).
% 0.20/0.57  thf('22', plain,
% 0.20/0.57      (![X54 : $i]: ((k2_tarski @ X54 @ X54) = (k1_tarski @ X54))),
% 0.20/0.57      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k2_tarski @ X0 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['9', '12'])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.20/0.57         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 0.20/0.57           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 0.20/0.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.57  thf(t50_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.57     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.20/0.57       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.57         ((k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.57           = (k2_xboole_0 @ (k2_enumset1 @ X8 @ X9 @ X10 @ X11) @ 
% 0.20/0.57              (k1_tarski @ X12)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.20/0.57           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.20/0.57           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['23', '26'])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      (![X52 : $i, X53 : $i]:
% 0.20/0.57         ((k3_enumset1 @ X52 @ X52 @ X52 @ X52 @ X53) = (k2_tarski @ X52 @ X53))),
% 0.20/0.57      inference('cnf', [status(esa)], [t83_enumset1])).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k2_tarski @ X0 @ X1)
% 0.20/0.57           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.57      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k2_tarski @ X1 @ X0)
% 0.20/0.57           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['22', '29'])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0 @ X0)
% 0.20/0.57           = (k2_tarski @ X1 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['21', '30'])).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0)
% 0.20/0.57           = (k2_tarski @ X1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['8', '31'])).
% 0.20/0.57  thf('33', plain,
% 0.20/0.57      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k2_tarski @ X0 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['9', '12'])).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.20/0.57           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 0.20/0.57              (k2_enumset1 @ X4 @ X3 @ X2 @ X1)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['15', '18'])).
% 0.20/0.57  thf('35', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.20/0.57           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ 
% 0.20/0.57              (k2_enumset1 @ X4 @ X3 @ X2 @ X1)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf(t58_enumset1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.57     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.57       ( k2_xboole_0 @
% 0.20/0.57         ( k1_enumset1 @ A @ B @ C ) @ ( k2_enumset1 @ D @ E @ F @ G ) ) ))).
% 0.20/0.57  thf('36', plain,
% 0.20/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.57         ((k5_enumset1 @ X13 @ X14 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.57           = (k2_xboole_0 @ (k1_enumset1 @ X13 @ X14 @ X15) @ 
% 0.20/0.57              (k2_enumset1 @ X16 @ X17 @ X18 @ X19)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t58_enumset1])).
% 0.20/0.57  thf('37', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.20/0.57           = (k5_enumset1 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 0.20/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.57  thf('38', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0)
% 0.20/0.57           = (k2_tarski @ X1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['32', '37'])).
% 0.20/0.57  thf('39', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.57         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.57           = (k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.57  thf('40', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0)
% 0.20/0.57           = (k2_tarski @ X1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.57  thf('41', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X0 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1)
% 0.20/0.57           = (k5_enumset1 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 0.20/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.57  thf('42', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k6_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X0)
% 0.20/0.57           = (k2_tarski @ X1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['40', '41'])).
% 0.20/0.57  thf('43', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.57         ((k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.57           = (k6_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.57  thf('44', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k5_enumset1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X1 @ X0)
% 0.20/0.57           = (k2_tarski @ X1 @ X0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.57  thf('45', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.57      inference('demod', [status(thm)], ['0', '44'])).
% 0.20/0.57  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
