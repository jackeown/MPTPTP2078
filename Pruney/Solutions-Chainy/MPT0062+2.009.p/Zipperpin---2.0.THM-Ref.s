%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g2gJM7AtUx

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:23 EST 2020

% Result     : Theorem 39.00s
% Output     : Refutation 39.00s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :  169 ( 178 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t55_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X18 ) @ X17 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    $false ),
    inference(simplify,[status(thm)],['8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.g2gJM7AtUx
% 0.15/0.38  % Computer   : n019.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 18:35:22 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 39.00/39.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 39.00/39.20  % Solved by: fo/fo7.sh
% 39.00/39.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 39.00/39.20  % done 11905 iterations in 38.708s
% 39.00/39.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 39.00/39.20  % SZS output start Refutation
% 39.00/39.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 39.00/39.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 39.00/39.20  thf(sk_A_type, type, sk_A: $i).
% 39.00/39.20  thf(sk_B_type, type, sk_B: $i).
% 39.00/39.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 39.00/39.20  thf(t55_xboole_1, conjecture,
% 39.00/39.20    (![A:$i,B:$i]:
% 39.00/39.20     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 39.00/39.20       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 39.00/39.20  thf(zf_stmt_0, negated_conjecture,
% 39.00/39.20    (~( ![A:$i,B:$i]:
% 39.00/39.20        ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 39.00/39.20          ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 39.00/39.20    inference('cnf.neg', [status(esa)], [t55_xboole_1])).
% 39.00/39.20  thf('0', plain,
% 39.00/39.20      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 39.00/39.20         (k3_xboole_0 @ sk_A @ sk_B))
% 39.00/39.20         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 39.00/39.20             (k4_xboole_0 @ sk_B @ sk_A)))),
% 39.00/39.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.00/39.20  thf(commutativity_k3_xboole_0, axiom,
% 39.00/39.20    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 39.00/39.20  thf('1', plain,
% 39.00/39.20      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 39.00/39.20      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 39.00/39.20  thf(t47_xboole_1, axiom,
% 39.00/39.20    (![A:$i,B:$i]:
% 39.00/39.20     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 39.00/39.20  thf('2', plain,
% 39.00/39.20      (![X21 : $i, X22 : $i]:
% 39.00/39.20         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 39.00/39.20           = (k4_xboole_0 @ X21 @ X22))),
% 39.00/39.20      inference('cnf', [status(esa)], [t47_xboole_1])).
% 39.00/39.20  thf('3', plain,
% 39.00/39.20      (![X0 : $i, X1 : $i]:
% 39.00/39.20         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 39.00/39.20           = (k4_xboole_0 @ X0 @ X1))),
% 39.00/39.20      inference('sup+', [status(thm)], ['1', '2'])).
% 39.00/39.20  thf('4', plain,
% 39.00/39.20      (![X21 : $i, X22 : $i]:
% 39.00/39.20         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 39.00/39.20           = (k4_xboole_0 @ X21 @ X22))),
% 39.00/39.20      inference('cnf', [status(esa)], [t47_xboole_1])).
% 39.00/39.20  thf(t42_xboole_1, axiom,
% 39.00/39.20    (![A:$i,B:$i,C:$i]:
% 39.00/39.20     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 39.00/39.20       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 39.00/39.20  thf('5', plain,
% 39.00/39.20      (![X16 : $i, X17 : $i, X18 : $i]:
% 39.00/39.20         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X18) @ X17)
% 39.00/39.20           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 39.00/39.20              (k4_xboole_0 @ X18 @ X17)))),
% 39.00/39.20      inference('cnf', [status(esa)], [t42_xboole_1])).
% 39.00/39.20  thf('6', plain,
% 39.00/39.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.00/39.20         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 39.00/39.20           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 39.00/39.20              (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 39.00/39.20      inference('sup+', [status(thm)], ['4', '5'])).
% 39.00/39.20  thf('7', plain,
% 39.00/39.20      (![X0 : $i, X1 : $i]:
% 39.00/39.20         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 39.00/39.20           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 39.00/39.20      inference('sup+', [status(thm)], ['3', '6'])).
% 39.00/39.20  thf('8', plain,
% 39.00/39.20      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 39.00/39.20         (k3_xboole_0 @ sk_A @ sk_B))
% 39.00/39.20         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 39.00/39.20             (k3_xboole_0 @ sk_A @ sk_B)))),
% 39.00/39.20      inference('demod', [status(thm)], ['0', '7'])).
% 39.00/39.20  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 39.00/39.20  
% 39.00/39.20  % SZS output end Refutation
% 39.00/39.20  
% 39.00/39.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
