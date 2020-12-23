%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FtELgz1T7z

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:27 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 105 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  487 (1013 expanded)
%              Number of equality atoms :   44 (  95 expanded)
%              Maximal formula depth    :   12 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t71_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_enumset1 @ A @ A @ B @ C )
        = ( k1_enumset1 @ A @ B @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_enumset1])).

thf('0',plain,(
    ( k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X76: $i,X77: $i] :
      ( ( k1_enumset1 @ X76 @ X76 @ X77 )
      = ( k2_tarski @ X76 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X75: $i] :
      ( ( k2_tarski @ X75 @ X75 )
      = ( k1_tarski @ X75 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('5',plain,(
    ! [X75: $i] :
      ( ( k2_tarski @ X75 @ X75 )
      = ( k1_tarski @ X75 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k2_tarski @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X76: $i,X77: $i] :
      ( ( k1_enumset1 @ X76 @ X76 @ X77 )
      = ( k2_tarski @ X76 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X76: $i,X77: $i] :
      ( ( k1_enumset1 @ X76 @ X76 @ X77 )
      = ( k2_tarski @ X76 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_tarski @ X27 @ X28 ) @ ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X75: $i] :
      ( ( k2_tarski @ X75 @ X75 )
      = ( k1_tarski @ X75 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k2_tarski @ X15 @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X75: $i] :
      ( ( k2_tarski @ X75 @ X75 )
      = ( k1_tarski @ X75 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k2_tarski @ X27 @ X28 ) @ ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('35',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','33','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FtELgz1T7z
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:28:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.56/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.73  % Solved by: fo/fo7.sh
% 0.56/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.73  % done 432 iterations in 0.282s
% 0.56/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.73  % SZS output start Refutation
% 0.56/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.73  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.56/0.73  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.56/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.56/0.73  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.56/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.56/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.56/0.73  thf(t71_enumset1, conjecture,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.56/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.73        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.56/0.73    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.56/0.73  thf('0', plain,
% 0.56/0.73      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.56/0.73         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(t70_enumset1, axiom,
% 0.56/0.73    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.56/0.73  thf('1', plain,
% 0.56/0.73      (![X76 : $i, X77 : $i]:
% 0.56/0.73         ((k1_enumset1 @ X76 @ X76 @ X77) = (k2_tarski @ X76 @ X77))),
% 0.56/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.73  thf(t44_enumset1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.73     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.56/0.73       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.56/0.73  thf('2', plain,
% 0.56/0.73      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.56/0.73  thf('3', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['1', '2'])).
% 0.56/0.73  thf(t69_enumset1, axiom,
% 0.56/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.56/0.73  thf('4', plain, (![X75 : $i]: ((k2_tarski @ X75 @ X75) = (k1_tarski @ X75))),
% 0.56/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.56/0.73  thf('5', plain, (![X75 : $i]: ((k2_tarski @ X75 @ X75) = (k1_tarski @ X75))),
% 0.56/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.56/0.73  thf(t43_enumset1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.56/0.73       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.56/0.73  thf('6', plain,
% 0.56/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.73         ((k1_enumset1 @ X15 @ X16 @ X17)
% 0.56/0.73           = (k2_xboole_0 @ (k2_tarski @ X15 @ X16) @ (k1_tarski @ X17)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.56/0.73  thf('7', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['5', '6'])).
% 0.56/0.73  thf('8', plain,
% 0.56/0.73      (![X76 : $i, X77 : $i]:
% 0.56/0.73         ((k1_enumset1 @ X76 @ X76 @ X77) = (k2_tarski @ X76 @ X77))),
% 0.56/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.73  thf('9', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k2_tarski @ X0 @ X1)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.56/0.73      inference('demod', [status(thm)], ['7', '8'])).
% 0.56/0.73  thf('10', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k2_tarski @ X1 @ X0)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['4', '9'])).
% 0.56/0.73  thf('11', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X0 @ X0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['3', '10'])).
% 0.56/0.73  thf('12', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['1', '2'])).
% 0.56/0.73  thf('13', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.56/0.73              (k2_enumset1 @ X1 @ X0 @ X0 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['11', '12'])).
% 0.56/0.73  thf(t47_enumset1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.56/0.73     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.56/0.73       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.56/0.73  thf('14', plain,
% 0.56/0.73      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.56/0.73         ((k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.56/0.73              (k2_enumset1 @ X23 @ X24 @ X25 @ X26)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.56/0.73  thf('15', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.56/0.73           = (k3_enumset1 @ X2 @ X1 @ X0 @ X0 @ X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['13', '14'])).
% 0.56/0.73  thf('16', plain,
% 0.56/0.73      (![X76 : $i, X77 : $i]:
% 0.56/0.73         ((k1_enumset1 @ X76 @ X76 @ X77) = (k2_tarski @ X76 @ X77))),
% 0.56/0.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.73  thf(t48_enumset1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.56/0.73     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.56/0.73       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.56/0.73  thf('17', plain,
% 0.56/0.73      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.56/0.73         ((k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.56/0.73           = (k2_xboole_0 @ (k2_tarski @ X27 @ X28) @ 
% 0.56/0.73              (k1_enumset1 @ X29 @ X30 @ X31)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.56/0.73  thf('18', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.73         ((k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0)
% 0.56/0.73           = (k2_xboole_0 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['16', '17'])).
% 0.56/0.73  thf('19', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.56/0.73           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['15', '18'])).
% 0.56/0.73  thf('20', plain,
% 0.56/0.73      (![X75 : $i]: ((k2_tarski @ X75 @ X75) = (k1_tarski @ X75))),
% 0.56/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.56/0.73  thf('21', plain,
% 0.56/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.56/0.73         ((k1_enumset1 @ X15 @ X16 @ X17)
% 0.56/0.73           = (k2_xboole_0 @ (k2_tarski @ X15 @ X16) @ (k1_tarski @ X17)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.56/0.73  thf('22', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.73         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.56/0.73           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['20', '21'])).
% 0.56/0.73  thf('23', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['19', '22'])).
% 0.56/0.73  thf('24', plain,
% 0.56/0.73      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.56/0.73  thf('25', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.56/0.73              (k2_enumset1 @ X2 @ X1 @ X1 @ X0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['23', '24'])).
% 0.56/0.73  thf('26', plain,
% 0.56/0.73      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.56/0.73         ((k3_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X22) @ 
% 0.56/0.73              (k2_enumset1 @ X23 @ X24 @ X25 @ X26)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.56/0.73  thf('27', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.56/0.73           = (k3_enumset1 @ X3 @ X2 @ X1 @ X1 @ X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['25', '26'])).
% 0.56/0.73  thf('28', plain,
% 0.56/0.73      (![X75 : $i]: ((k2_tarski @ X75 @ X75) = (k1_tarski @ X75))),
% 0.56/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.56/0.73  thf('29', plain,
% 0.56/0.73      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.56/0.73         ((k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.56/0.73           = (k2_xboole_0 @ (k2_tarski @ X27 @ X28) @ 
% 0.56/0.73              (k1_enumset1 @ X29 @ X30 @ X31)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.56/0.73  thf('30', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.73         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['28', '29'])).
% 0.56/0.73  thf('31', plain,
% 0.56/0.73      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.56/0.73           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_enumset1 @ X19 @ X20 @ X21)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.56/0.73  thf('32', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.56/0.73         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.56/0.73           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.56/0.73      inference('demod', [status(thm)], ['30', '31'])).
% 0.56/0.73  thf('33', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X2 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X1 @ X0))),
% 0.56/0.73      inference('sup+', [status(thm)], ['27', '32'])).
% 0.56/0.73  thf('34', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.73         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['19', '22'])).
% 0.56/0.73  thf('35', plain,
% 0.56/0.73      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.56/0.73         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.56/0.73      inference('demod', [status(thm)], ['0', '33', '34'])).
% 0.56/0.73  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.56/0.73  
% 0.56/0.73  % SZS output end Refutation
% 0.56/0.73  
% 0.56/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
