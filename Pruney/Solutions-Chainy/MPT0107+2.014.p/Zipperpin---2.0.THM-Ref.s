%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zcKNBG0DkF

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:12 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   44 (  71 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :  285 ( 472 expanded)
%              Number of equality atoms :   36 (  63 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t100_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t100_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','19'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zcKNBG0DkF
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 342 iterations in 0.174s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(t100_xboole_1, conjecture,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i]:
% 0.38/0.62        ( ( k4_xboole_0 @ A @ B ) =
% 0.38/0.62          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.38/0.62         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t95_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k3_xboole_0 @ A @ B ) =
% 0.38/0.62       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         ((k3_xboole_0 @ X20 @ X21)
% 0.38/0.62           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.38/0.62              (k2_xboole_0 @ X20 @ X21)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.38/0.62  thf(t91_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.38/0.62           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         ((k3_xboole_0 @ X20 @ X21)
% 0.38/0.62           = (k5_xboole_0 @ X20 @ 
% 0.38/0.62              (k5_xboole_0 @ X21 @ (k2_xboole_0 @ X20 @ X21))))),
% 0.38/0.62      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.62  thf(t98_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X22 @ X23)
% 0.38/0.62           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.62  thf(t92_xboole_1, axiom,
% 0.38/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.38/0.62  thf('6', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.38/0.62           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.38/0.62           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.38/0.62  thf(t3_boole, axiom,
% 0.38/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.62  thf('9', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X22 @ X23)
% 0.38/0.62           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.62  thf(t40_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X6)
% 0.38/0.62           = (k4_xboole_0 @ X5 @ X6))),
% 0.38/0.62      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.38/0.62  thf('13', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf('15', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.62  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.62  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['16', '17'])).
% 0.38/0.62  thf('19', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['11', '18'])).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['8', '19'])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.62           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['5', '20'])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X1 @ X0)
% 0.38/0.62           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['4', '21'])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X20 : $i, X21 : $i]:
% 0.38/0.62         ((k3_xboole_0 @ X20 @ X21)
% 0.38/0.62           = (k5_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21)))),
% 0.38/0.62      inference('demod', [status(thm)], ['3', '22'])).
% 0.38/0.62  thf('24', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['8', '19'])).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X1 @ X0)
% 0.38/0.62           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['23', '24'])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['0', '25'])).
% 0.38/0.62  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
