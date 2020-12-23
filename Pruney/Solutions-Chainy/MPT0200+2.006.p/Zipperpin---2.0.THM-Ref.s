%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QPy2vLkmDW

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:24 EST 2020

% Result     : Theorem 6.43s
% Output     : Refutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 113 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  459 (1323 expanded)
%              Number of equality atoms :   38 ( 102 expanded)
%              Maximal formula depth    :   14 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t125_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( k2_enumset1 @ A @ B @ C @ D )
        = ( k2_enumset1 @ D @ C @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t125_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ C @ B @ D @ A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X8 @ X6 @ X5 @ X7 )
      = ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

thf('2',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_C @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X4 @ X3 @ X2 )
      = ( k1_enumset1 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k2_tarski @ X9 @ X10 ) @ ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X0 @ X1 @ X2 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t85_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k5_enumset1 @ X24 @ X24 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t85_enumset1])).

thf(t80_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k5_enumset1 @ X19 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t80_enumset1])).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X0 @ X1 @ X2 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X8 @ X6 @ X5 @ X7 )
      = ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X3 @ X1 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X3 @ X1 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X8 @ X6 @ X5 @ X7 )
      = ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t117_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X0 @ X3 @ X1 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X2 @ X3 @ X1 )
      = ( k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X3 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X0 @ X2 @ X1 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D )
 != ( k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['14','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QPy2vLkmDW
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.43/6.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.43/6.61  % Solved by: fo/fo7.sh
% 6.43/6.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.43/6.61  % done 9366 iterations in 6.178s
% 6.43/6.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.43/6.61  % SZS output start Refutation
% 6.43/6.61  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 6.43/6.61  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 6.43/6.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.43/6.61  thf(sk_C_type, type, sk_C: $i).
% 6.43/6.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.43/6.61  thf(sk_A_type, type, sk_A: $i).
% 6.43/6.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.43/6.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.43/6.61  thf(sk_B_type, type, sk_B: $i).
% 6.43/6.61  thf(sk_D_type, type, sk_D: $i).
% 6.43/6.61  thf(t125_enumset1, conjecture,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i]:
% 6.43/6.61     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 6.43/6.61  thf(zf_stmt_0, negated_conjecture,
% 6.43/6.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 6.43/6.61        ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ) )),
% 6.43/6.61    inference('cnf.neg', [status(esa)], [t125_enumset1])).
% 6.43/6.61  thf('0', plain,
% 6.43/6.61      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 6.43/6.61         != (k2_enumset1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 6.43/6.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.43/6.61  thf(t117_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i]:
% 6.43/6.61     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ C @ B @ D @ A ) ))).
% 6.43/6.61  thf('1', plain,
% 6.43/6.61      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X8 @ X6 @ X5 @ X7) = (k2_enumset1 @ X5 @ X6 @ X7 @ X8))),
% 6.43/6.61      inference('cnf', [status(esa)], [t117_enumset1])).
% 6.43/6.61  thf('2', plain,
% 6.43/6.61      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 6.43/6.61         != (k2_enumset1 @ sk_A @ sk_C @ sk_D @ sk_B))),
% 6.43/6.61      inference('demod', [status(thm)], ['0', '1'])).
% 6.43/6.61  thf(t102_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i]:
% 6.43/6.61     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 6.43/6.61  thf('3', plain,
% 6.43/6.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 6.43/6.61         ((k1_enumset1 @ X4 @ X3 @ X2) = (k1_enumset1 @ X2 @ X3 @ X4))),
% 6.43/6.61      inference('cnf', [status(esa)], [t102_enumset1])).
% 6.43/6.61  thf(t48_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.43/6.61     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 6.43/6.61       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 6.43/6.61  thf('4', plain,
% 6.43/6.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 6.43/6.61           = (k2_xboole_0 @ (k2_tarski @ X9 @ X10) @ 
% 6.43/6.61              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 6.43/6.61      inference('cnf', [status(esa)], [t48_enumset1])).
% 6.43/6.61  thf('5', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X4 @ X3 @ X0 @ X1 @ X2)
% 6.43/6.61           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 6.43/6.61              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 6.43/6.61      inference('sup+', [status(thm)], ['3', '4'])).
% 6.43/6.61  thf('6', plain,
% 6.43/6.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13)
% 6.43/6.61           = (k2_xboole_0 @ (k2_tarski @ X9 @ X10) @ 
% 6.43/6.61              (k1_enumset1 @ X11 @ X12 @ X13)))),
% 6.43/6.61      inference('cnf', [status(esa)], [t48_enumset1])).
% 6.43/6.61  thf('7', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X4 @ X3 @ X0 @ X1 @ X2)
% 6.43/6.61           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['5', '6'])).
% 6.43/6.61  thf(t85_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i]:
% 6.43/6.61     ( ( k5_enumset1 @ A @ A @ A @ A @ B @ C @ D ) =
% 6.43/6.61       ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 6.43/6.61  thf('8', plain,
% 6.43/6.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.43/6.61         ((k5_enumset1 @ X24 @ X24 @ X24 @ X24 @ X25 @ X26 @ X27)
% 6.43/6.61           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 6.43/6.61      inference('cnf', [status(esa)], [t85_enumset1])).
% 6.43/6.61  thf(t80_enumset1, axiom,
% 6.43/6.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.43/6.61     ( ( k5_enumset1 @ A @ A @ A @ B @ C @ D @ E ) =
% 6.43/6.61       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 6.43/6.61  thf('9', plain,
% 6.43/6.61      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 6.43/6.61         ((k5_enumset1 @ X19 @ X19 @ X19 @ X20 @ X21 @ X22 @ X23)
% 6.43/6.61           = (k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23))),
% 6.43/6.61      inference('cnf', [status(esa)], [t80_enumset1])).
% 6.43/6.61  thf('10', plain,
% 6.43/6.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27)
% 6.43/6.61           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 6.43/6.61      inference('demod', [status(thm)], ['8', '9'])).
% 6.43/6.61  thf('11', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 6.43/6.61           = (k2_enumset1 @ X3 @ X0 @ X1 @ X2))),
% 6.43/6.61      inference('sup+', [status(thm)], ['7', '10'])).
% 6.43/6.61  thf('12', plain,
% 6.43/6.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27)
% 6.43/6.61           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 6.43/6.61      inference('demod', [status(thm)], ['8', '9'])).
% 6.43/6.61  thf('13', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X0 @ X1 @ X2))),
% 6.43/6.61      inference('sup+', [status(thm)], ['11', '12'])).
% 6.43/6.61  thf('14', plain,
% 6.43/6.61      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 6.43/6.61         != (k2_enumset1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 6.43/6.61      inference('demod', [status(thm)], ['2', '13'])).
% 6.43/6.61  thf('15', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X4 @ X3 @ X0 @ X1 @ X2)
% 6.43/6.61           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['5', '6'])).
% 6.43/6.61  thf('16', plain,
% 6.43/6.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27)
% 6.43/6.61           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 6.43/6.61      inference('demod', [status(thm)], ['8', '9'])).
% 6.43/6.61  thf('17', plain,
% 6.43/6.61      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X8 @ X6 @ X5 @ X7) = (k2_enumset1 @ X5 @ X6 @ X7 @ X8))),
% 6.43/6.61      inference('cnf', [status(esa)], [t117_enumset1])).
% 6.43/6.61  thf('18', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X0 @ X2 @ X3 @ X1)
% 6.43/6.61           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['16', '17'])).
% 6.43/6.61  thf('19', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X2 @ X0 @ X3 @ X1)
% 6.43/6.61           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['15', '18'])).
% 6.43/6.61  thf('20', plain,
% 6.43/6.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27)
% 6.43/6.61           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 6.43/6.61      inference('demod', [status(thm)], ['8', '9'])).
% 6.43/6.61  thf('21', plain,
% 6.43/6.61      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X8 @ X6 @ X5 @ X7) = (k2_enumset1 @ X5 @ X6 @ X7 @ X8))),
% 6.43/6.61      inference('cnf', [status(esa)], [t117_enumset1])).
% 6.43/6.61  thf('22', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0)
% 6.43/6.61           = (k2_enumset1 @ X1 @ X2 @ X0 @ X3))),
% 6.43/6.61      inference('sup+', [status(thm)], ['20', '21'])).
% 6.43/6.61  thf('23', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 6.43/6.61      inference('sup+', [status(thm)], ['19', '22'])).
% 6.43/6.61  thf('24', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X2 @ X0 @ X3 @ X1)
% 6.43/6.61           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['15', '18'])).
% 6.43/6.61  thf('25', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X0 @ X2 @ X3 @ X1)
% 6.43/6.61           = (k3_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['16', '17'])).
% 6.43/6.61  thf('26', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X2 @ X3 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['24', '25'])).
% 6.43/6.61  thf('27', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X3 @ X0 @ X2 @ X1) = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 6.43/6.61      inference('sup+', [status(thm)], ['23', '26'])).
% 6.43/6.61  thf('28', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X0 @ X1 @ X2))),
% 6.43/6.61      inference('sup+', [status(thm)], ['11', '12'])).
% 6.43/6.61  thf('29', plain,
% 6.43/6.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.43/6.61         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X3 @ X2 @ X0 @ X1))),
% 6.43/6.61      inference('sup+', [status(thm)], ['27', '28'])).
% 6.43/6.61  thf('30', plain,
% 6.43/6.61      (((k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 6.43/6.61         != (k2_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 6.43/6.61      inference('demod', [status(thm)], ['14', '29'])).
% 6.43/6.61  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 6.43/6.61  
% 6.43/6.61  % SZS output end Refutation
% 6.43/6.61  
% 6.43/6.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
