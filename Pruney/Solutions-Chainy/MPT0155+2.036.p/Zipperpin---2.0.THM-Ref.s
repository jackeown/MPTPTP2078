%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KQuoav6rhl

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  408 ( 568 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t48_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X14 @ X15 ) @ ( k1_enumset1 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t48_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','20'])).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KQuoav6rhl
% 0.13/0.36  % Computer   : n016.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 09:18:34 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 32 iterations in 0.022s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.49  thf(t71_enumset1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.21/0.49         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t69_enumset1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.49  thf('1', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf(t48_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.49       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.21/0.49           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ 
% 0.21/0.49              (k1_enumset1 @ X16 @ X17 @ X18)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(t44_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.21/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.21/0.49           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf(t70_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X37 : $i, X38 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.49  thf(t43_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.21/0.49       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.21/0.49           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X37 : $i, X38 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k2_tarski @ X0 @ X1)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k2_tarski @ X1 @ X0)
% 0.21/0.49           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['9', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['8', '15'])).
% 0.21/0.49  thf(t50_enumset1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.21/0.49       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.21/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.21/0.49              (k1_tarski @ X23)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X2)
% 0.21/0.49           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.21/0.49           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['5', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X37 : $i, X38 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.21/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.21/0.49           = (k2_xboole_0 @ (k2_enumset1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.21/0.49              (k1_tarski @ X23)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.21/0.49           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.21/0.49           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.49         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.21/0.49           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.21/0.49         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '28'])).
% 0.21/0.49  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
