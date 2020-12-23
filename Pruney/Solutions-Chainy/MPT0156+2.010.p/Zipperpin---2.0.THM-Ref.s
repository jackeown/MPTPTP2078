%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qrHcINMVd4

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:32 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  594 ( 809 expanded)
%              Number of equality atoms :   42 (  60 expanded)
%              Maximal formula depth    :   18 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t72_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k3_enumset1 @ A @ A @ B @ C @ D )
        = ( k2_enumset1 @ A @ B @ C @ D ) ) ),
    inference('cnf.neg',[status(esa)],[t72_enumset1])).

thf('0',plain,(
    ( k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( k2_enumset1 @ X57 @ X57 @ X58 @ X59 )
      = ( k1_enumset1 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X54: $i] :
      ( ( k2_tarski @ X54 @ X54 )
      = ( k1_tarski @ X54 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_enumset1 @ X9 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X3 ) @ ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t57_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k2_tarski @ X24 @ X25 ) @ ( k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t57_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k5_enumset1 @ X3 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('14',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k6_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_xboole_0 @ ( k1_tarski @ X38 ) @ ( k5_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X3 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X12 ) @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X3 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(l62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t64_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ) )).

thf('21',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k6_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X46 @ X47 @ X48 ) @ ( k3_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t64_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k6_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X56 )
      = ( k2_tarski @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X3 @ X4 ) @ ( k1_enumset1 @ X5 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l62_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_enumset1 @ X4 @ X3 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['0','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qrHcINMVd4
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.70/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.90  % Solved by: fo/fo7.sh
% 0.70/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.90  % done 725 iterations in 0.454s
% 0.70/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.90  % SZS output start Refutation
% 0.70/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.70/0.90  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.70/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.70/0.90  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.70/0.90  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.70/0.90                                           $i > $i).
% 0.70/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.70/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.90  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.70/0.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.70/0.90  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.70/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.90  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.70/0.90  thf(t72_enumset1, conjecture,
% 0.70/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.90     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.70/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.90        ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ) )),
% 0.70/0.90    inference('cnf.neg', [status(esa)], [t72_enumset1])).
% 0.70/0.90  thf('0', plain,
% 0.70/0.90      (((k3_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.70/0.90         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.70/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.90  thf(t71_enumset1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i]:
% 0.70/0.90     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.70/0.90  thf('1', plain,
% 0.70/0.90      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.70/0.90         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 0.70/0.90           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 0.70/0.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.70/0.90  thf(t47_enumset1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.70/0.90     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.70/0.90       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.70/0.90  thf('2', plain,
% 0.70/0.90      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.70/0.90         ((k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.70/0.90           = (k2_xboole_0 @ (k1_tarski @ X12) @ 
% 0.70/0.90              (k2_enumset1 @ X13 @ X14 @ X15 @ X16)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.70/0.90  thf('3', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.90         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k2_xboole_0 @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['1', '2'])).
% 0.70/0.90  thf(t44_enumset1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.90     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.70/0.90       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.70/0.90  thf('4', plain,
% 0.70/0.90      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.70/0.90         ((k2_enumset1 @ X8 @ X9 @ X10 @ X11)
% 0.70/0.90           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.70/0.90  thf('5', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.90         ((k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.70/0.90      inference('demod', [status(thm)], ['3', '4'])).
% 0.70/0.90  thf('6', plain,
% 0.70/0.90      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.70/0.90         ((k2_enumset1 @ X57 @ X57 @ X58 @ X59)
% 0.70/0.90           = (k1_enumset1 @ X57 @ X58 @ X59))),
% 0.70/0.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.70/0.90  thf('7', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.70/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.70/0.90  thf(t69_enumset1, axiom,
% 0.70/0.90    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.70/0.90  thf('8', plain, (![X54 : $i]: ((k2_tarski @ X54 @ X54) = (k1_tarski @ X54))),
% 0.70/0.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.70/0.90  thf('9', plain,
% 0.70/0.90      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.70/0.90         ((k2_enumset1 @ X8 @ X9 @ X10 @ X11)
% 0.70/0.90           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_enumset1 @ X9 @ X10 @ X11)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.70/0.90  thf('10', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.90         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 0.70/0.90           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 0.70/0.90              (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['8', '9'])).
% 0.70/0.90  thf('11', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.90         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k2_xboole_0 @ (k2_tarski @ X3 @ X3) @ 
% 0.70/0.90              (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['7', '10'])).
% 0.70/0.90  thf(t57_enumset1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.70/0.90     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.70/0.90       ( k2_xboole_0 @
% 0.70/0.90         ( k2_tarski @ A @ B ) @ ( k3_enumset1 @ C @ D @ E @ F @ G ) ) ))).
% 0.70/0.90  thf('12', plain,
% 0.70/0.90      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.70/0.90         ((k5_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.70/0.90           = (k2_xboole_0 @ (k2_tarski @ X24 @ X25) @ 
% 0.70/0.90              (k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t57_enumset1])).
% 0.70/0.90  thf('13', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.90         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k5_enumset1 @ X3 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 0.70/0.90      inference('demod', [status(thm)], ['11', '12'])).
% 0.70/0.90  thf(t62_enumset1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.70/0.90     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.70/0.90       ( k2_xboole_0 @
% 0.70/0.90         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.70/0.90  thf('14', plain,
% 0.70/0.90      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, 
% 0.70/0.90         X45 : $i]:
% 0.70/0.90         ((k6_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45)
% 0.70/0.90           = (k2_xboole_0 @ (k1_tarski @ X38) @ 
% 0.70/0.90              (k5_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t62_enumset1])).
% 0.70/0.90  thf('15', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.90         ((k6_enumset1 @ X4 @ X3 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.70/0.90              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['13', '14'])).
% 0.70/0.90  thf('16', plain,
% 0.70/0.90      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.70/0.90         ((k3_enumset1 @ X12 @ X13 @ X14 @ X15 @ X16)
% 0.70/0.90           = (k2_xboole_0 @ (k1_tarski @ X12) @ 
% 0.70/0.90              (k2_enumset1 @ X13 @ X14 @ X15 @ X16)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.70/0.90  thf('17', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.90         ((k6_enumset1 @ X4 @ X3 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.70/0.90      inference('demod', [status(thm)], ['15', '16'])).
% 0.70/0.90  thf('18', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.90         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.70/0.90      inference('sup+', [status(thm)], ['5', '6'])).
% 0.70/0.90  thf(l62_enumset1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.70/0.90     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.70/0.90       ( k2_xboole_0 @
% 0.70/0.90         ( k1_enumset1 @ A @ B @ C ) @ ( k1_enumset1 @ D @ E @ F ) ) ))).
% 0.70/0.90  thf('19', plain,
% 0.70/0.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.90         ((k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.70/0.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.70/0.90              (k1_enumset1 @ X5 @ X6 @ X7)))),
% 0.70/0.90      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.70/0.90  thf('20', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.70/0.90         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.70/0.90              (k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['18', '19'])).
% 0.70/0.90  thf(t64_enumset1, axiom,
% 0.70/0.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.70/0.90     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.70/0.90       ( k2_xboole_0 @
% 0.70/0.90         ( k1_enumset1 @ A @ B @ C ) @ ( k3_enumset1 @ D @ E @ F @ G @ H ) ) ))).
% 0.70/0.90  thf('21', plain,
% 0.70/0.90      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, 
% 0.70/0.90         X53 : $i]:
% 0.70/0.90         ((k6_enumset1 @ X46 @ X47 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53)
% 0.70/0.90           = (k2_xboole_0 @ (k1_enumset1 @ X46 @ X47 @ X48) @ 
% 0.70/0.90              (k3_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53)))),
% 0.70/0.90      inference('cnf', [status(esa)], [t64_enumset1])).
% 0.70/0.90  thf('22', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.70/0.90         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k6_enumset1 @ X5 @ X4 @ X3 @ X2 @ X2 @ X2 @ X1 @ X0))),
% 0.70/0.90      inference('demod', [status(thm)], ['20', '21'])).
% 0.70/0.90  thf('23', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.90         ((k4_enumset1 @ X4 @ X3 @ X3 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.70/0.90      inference('demod', [status(thm)], ['17', '22'])).
% 0.70/0.90  thf(t70_enumset1, axiom,
% 0.70/0.90    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.70/0.90  thf('24', plain,
% 0.70/0.90      (![X55 : $i, X56 : $i]:
% 0.70/0.90         ((k1_enumset1 @ X55 @ X55 @ X56) = (k2_tarski @ X55 @ X56))),
% 0.70/0.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.70/0.90  thf('25', plain,
% 0.70/0.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.90         ((k4_enumset1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.70/0.90           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X3 @ X4) @ 
% 0.70/0.90              (k1_enumset1 @ X5 @ X6 @ X7)))),
% 0.70/0.90      inference('cnf', [status(esa)], [l62_enumset1])).
% 0.70/0.90  thf('26', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.90         ((k4_enumset1 @ X1 @ X1 @ X0 @ X4 @ X3 @ X2)
% 0.70/0.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 0.70/0.90              (k1_enumset1 @ X4 @ X3 @ X2)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['24', '25'])).
% 0.70/0.90  thf('27', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.90         ((k2_enumset1 @ X0 @ X3 @ X2 @ X1)
% 0.70/0.90           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 0.70/0.90              (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.70/0.90      inference('sup+', [status(thm)], ['8', '9'])).
% 0.70/0.90  thf('28', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.90         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 0.70/0.90      inference('sup+', [status(thm)], ['26', '27'])).
% 0.70/0.90  thf('29', plain,
% 0.70/0.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.70/0.90         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.70/0.90           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 0.70/0.90      inference('sup+', [status(thm)], ['23', '28'])).
% 0.70/0.90  thf('30', plain,
% 0.70/0.90      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.70/0.90         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.70/0.90      inference('demod', [status(thm)], ['0', '29'])).
% 0.70/0.90  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.70/0.90  
% 0.70/0.90  % SZS output end Refutation
% 0.70/0.90  
% 0.70/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
