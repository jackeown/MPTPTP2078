%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zQgamiObEq

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:31 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   49 (  64 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  420 ( 580 expanded)
%              Number of equality atoms :   39 (  54 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X53: $i] :
      ( ( k2_tarski @ X53 @ X53 )
      = ( k1_tarski @ X53 ) ) ),
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

thf('6',plain,(
    ! [X53: $i] :
      ( ( k2_tarski @ X53 @ X53 )
      = ( k1_tarski @ X53 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_enumset1 @ X54 @ X54 @ X55 )
      = ( k2_tarski @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_enumset1 @ X5 @ X6 @ X7 @ X8 )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k1_enumset1 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X53: $i] :
      ( ( k2_tarski @ X53 @ X53 )
      = ( k1_tarski @ X53 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k1_enumset1 @ X54 @ X54 @ X55 )
      = ( k2_tarski @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

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
    ! [X54: $i,X55: $i] :
      ( ( k1_enumset1 @ X54 @ X54 @ X55 )
      = ( k2_tarski @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','22'])).

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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k1_enumset1 @ X2 @ X3 @ X4 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X3 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1 )
      = ( k2_enumset1 @ X0 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
 != ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zQgamiObEq
% 0.18/0.38  % Computer   : n025.cluster.edu
% 0.18/0.38  % Model      : x86_64 x86_64
% 0.18/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.38  % Memory     : 8042.1875MB
% 0.18/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.38  % CPULimit   : 60
% 0.18/0.38  % DateTime   : Tue Dec  1 17:00:21 EST 2020
% 0.18/0.38  % CPUTime    : 
% 0.18/0.38  % Running portfolio for 600 s
% 0.18/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.38  % Number of cores: 8
% 0.18/0.38  % Python version: Python 3.6.8
% 0.18/0.39  % Running in FO mode
% 0.25/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.53  % Solved by: fo/fo7.sh
% 0.25/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.53  % done 56 iterations in 0.039s
% 0.25/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.53  % SZS output start Refutation
% 0.25/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.25/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.25/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.25/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.25/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.53  thf(t71_enumset1, conjecture,
% 0.25/0.53    (![A:$i,B:$i,C:$i]:
% 0.25/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.25/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.25/0.53        ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ) )),
% 0.25/0.53    inference('cnf.neg', [status(esa)], [t71_enumset1])).
% 0.25/0.53  thf('0', plain,
% 0.25/0.53      (((k2_enumset1 @ sk_A @ sk_A @ sk_B @ sk_C)
% 0.25/0.53         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf(t69_enumset1, axiom,
% 0.25/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.25/0.53  thf('1', plain, (![X53 : $i]: ((k2_tarski @ X53 @ X53) = (k1_tarski @ X53))),
% 0.25/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.25/0.53  thf(t48_enumset1, axiom,
% 0.25/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.25/0.53     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.25/0.53       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_enumset1 @ C @ D @ E ) ) ))).
% 0.25/0.53  thf('2', plain,
% 0.25/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X14 @ X15 @ X16 @ X17 @ X18)
% 0.25/0.53           = (k2_xboole_0 @ (k2_tarski @ X14 @ X15) @ 
% 0.25/0.53              (k1_enumset1 @ X16 @ X17 @ X18)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t48_enumset1])).
% 0.25/0.53  thf('3', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.25/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X3 @ X2 @ X1)))),
% 0.25/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.25/0.53  thf(t44_enumset1, axiom,
% 0.25/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.25/0.53     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.25/0.53       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.25/0.53  thf('4', plain,
% 0.25/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.25/0.53         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.25/0.53           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.25/0.53  thf('5', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.25/0.53           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.25/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.25/0.53  thf('6', plain, (![X53 : $i]: ((k2_tarski @ X53 @ X53) = (k1_tarski @ X53))),
% 0.25/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.25/0.53  thf(t70_enumset1, axiom,
% 0.25/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.25/0.53  thf('7', plain,
% 0.25/0.53      (![X54 : $i, X55 : $i]:
% 0.25/0.53         ((k1_enumset1 @ X54 @ X54 @ X55) = (k2_tarski @ X54 @ X55))),
% 0.25/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.25/0.53  thf('8', plain,
% 0.25/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.25/0.53         ((k2_enumset1 @ X5 @ X6 @ X7 @ X8)
% 0.25/0.53           = (k2_xboole_0 @ (k1_tarski @ X5) @ (k1_enumset1 @ X6 @ X7 @ X8)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.25/0.53  thf('9', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         ((k2_enumset1 @ X2 @ X1 @ X1 @ X0)
% 0.25/0.53           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.25/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.25/0.53  thf('10', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]:
% 0.25/0.53         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0)
% 0.25/0.53           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.25/0.53      inference('sup+', [status(thm)], ['6', '9'])).
% 0.25/0.53  thf('11', plain,
% 0.25/0.53      (![X53 : $i]: ((k2_tarski @ X53 @ X53) = (k1_tarski @ X53))),
% 0.25/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.25/0.53  thf(t43_enumset1, axiom,
% 0.25/0.53    (![A:$i,B:$i,C:$i]:
% 0.25/0.53     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.25/0.53       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.25/0.53  thf('12', plain,
% 0.25/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.53         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.25/0.53           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X4)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.25/0.53  thf('13', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]:
% 0.25/0.53         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.25/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.25/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.25/0.53  thf('14', plain,
% 0.25/0.53      (![X54 : $i, X55 : $i]:
% 0.25/0.53         ((k1_enumset1 @ X54 @ X54 @ X55) = (k2_tarski @ X54 @ X55))),
% 0.25/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.25/0.53  thf('15', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]:
% 0.25/0.53         ((k2_tarski @ X0 @ X1)
% 0.25/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.25/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.25/0.53  thf('16', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]:
% 0.25/0.53         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.25/0.53      inference('demod', [status(thm)], ['10', '15'])).
% 0.25/0.53  thf(t50_enumset1, axiom,
% 0.25/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.25/0.53     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.25/0.53       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.25/0.53  thf('17', plain,
% 0.25/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.25/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.25/0.53              (k1_tarski @ X23)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.25/0.53  thf('18', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X2)
% 0.25/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.25/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.25/0.53  thf('19', plain,
% 0.25/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.53         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.25/0.53           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X4)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.25/0.53  thf('20', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X1 @ X0 @ X0 @ X0 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.25/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.25/0.53  thf('21', plain,
% 0.25/0.53      (![X54 : $i, X55 : $i]:
% 0.25/0.53         ((k1_enumset1 @ X54 @ X54 @ X55) = (k2_tarski @ X54 @ X55))),
% 0.25/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.25/0.53  thf('22', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.25/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.25/0.53  thf('23', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]:
% 0.25/0.53         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.25/0.53      inference('sup+', [status(thm)], ['5', '22'])).
% 0.25/0.53  thf('24', plain,
% 0.25/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23)
% 0.25/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X19 @ X20 @ X21 @ X22) @ 
% 0.25/0.53              (k1_tarski @ X23)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.25/0.53  thf('25', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.25/0.53           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.25/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.25/0.53  thf('26', plain,
% 0.25/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.53         ((k1_enumset1 @ X2 @ X3 @ X4)
% 0.25/0.53           = (k2_xboole_0 @ (k2_tarski @ X2 @ X3) @ (k1_tarski @ X4)))),
% 0.25/0.53      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.25/0.53  thf('27', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X1 @ X0 @ X2))),
% 0.25/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.25/0.53  thf('28', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.25/0.53         ((k3_enumset1 @ X0 @ X0 @ X3 @ X2 @ X1)
% 0.25/0.53           = (k2_enumset1 @ X0 @ X3 @ X2 @ X1))),
% 0.25/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.25/0.53  thf('29', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.25/0.53      inference('sup+', [status(thm)], ['27', '28'])).
% 0.25/0.53  thf('30', plain,
% 0.25/0.53      (((k1_enumset1 @ sk_A @ sk_B @ sk_C)
% 0.25/0.53         != (k1_enumset1 @ sk_A @ sk_B @ sk_C))),
% 0.25/0.53      inference('demod', [status(thm)], ['0', '29'])).
% 0.25/0.53  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.25/0.53  
% 0.25/0.53  % SZS output end Refutation
% 0.25/0.53  
% 0.25/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
