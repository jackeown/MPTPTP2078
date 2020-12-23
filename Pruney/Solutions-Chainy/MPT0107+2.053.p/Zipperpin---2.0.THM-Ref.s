%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rhY6A7cLV7

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:17 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  265 ( 317 expanded)
%              Number of equality atoms :   30 (  38 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','18','19'])).

thf('21',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rhY6A7cLV7
% 0.15/0.36  % Computer   : n023.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 20:43:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.52/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.76  % Solved by: fo/fo7.sh
% 0.52/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.76  % done 503 iterations in 0.280s
% 0.52/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.76  % SZS output start Refutation
% 0.52/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.76  thf(t100_xboole_1, conjecture,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.76    (~( ![A:$i,B:$i]:
% 0.52/0.76        ( ( k4_xboole_0 @ A @ B ) =
% 0.52/0.76          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.52/0.76    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.52/0.76  thf('0', plain,
% 0.52/0.76      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.52/0.76         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf(t47_xboole_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.52/0.76  thf('1', plain,
% 0.52/0.76      (![X16 : $i, X17 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17))
% 0.52/0.76           = (k4_xboole_0 @ X16 @ X17))),
% 0.52/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.76  thf(d6_xboole_0, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( k5_xboole_0 @ A @ B ) =
% 0.52/0.76       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.52/0.76  thf('2', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k5_xboole_0 @ X0 @ X1)
% 0.52/0.76           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.52/0.76  thf('3', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.76           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.52/0.76              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.52/0.76      inference('sup+', [status(thm)], ['1', '2'])).
% 0.52/0.76  thf('4', plain,
% 0.52/0.76      (![X16 : $i, X17 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17))
% 0.52/0.76           = (k4_xboole_0 @ X16 @ X17))),
% 0.52/0.76      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.52/0.76  thf(t48_xboole_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.52/0.76  thf('5', plain,
% 0.52/0.76      (![X18 : $i, X19 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.52/0.76           = (k3_xboole_0 @ X18 @ X19))),
% 0.52/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.76  thf('6', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.76           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.52/0.76      inference('sup+', [status(thm)], ['4', '5'])).
% 0.52/0.76  thf('7', plain,
% 0.52/0.76      (![X18 : $i, X19 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.52/0.76           = (k3_xboole_0 @ X18 @ X19))),
% 0.52/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.52/0.76  thf('8', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.76           = (k3_xboole_0 @ X1 @ X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['6', '7'])).
% 0.52/0.76  thf(t1_boole, axiom,
% 0.52/0.76    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.76  thf('9', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.52/0.76      inference('cnf', [status(esa)], [t1_boole])).
% 0.52/0.76  thf(t46_xboole_1, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.52/0.76  thf('10', plain,
% 0.52/0.76      (![X14 : $i, X15 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (k1_xboole_0))),
% 0.52/0.76      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.52/0.76  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.76  thf(l36_xboole_1, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.52/0.76       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.52/0.76  thf('12', plain,
% 0.52/0.76      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.52/0.76           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X2 @ X4)))),
% 0.52/0.76      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.52/0.76  thf('13', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.76           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['11', '12'])).
% 0.52/0.76  thf('14', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.52/0.76      inference('cnf', [status(esa)], [t1_boole])).
% 0.52/0.76  thf('15', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.76           = (k4_xboole_0 @ X0 @ X1))),
% 0.52/0.76      inference('demod', [status(thm)], ['13', '14'])).
% 0.52/0.76  thf('16', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.76           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.52/0.76      inference('sup+', [status(thm)], ['8', '15'])).
% 0.52/0.76  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['9', '10'])).
% 0.52/0.76  thf('18', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.52/0.76      inference('demod', [status(thm)], ['16', '17'])).
% 0.52/0.76  thf('19', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.52/0.76      inference('cnf', [status(esa)], [t1_boole])).
% 0.52/0.76  thf('20', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.76           = (k4_xboole_0 @ X1 @ X0))),
% 0.52/0.76      inference('demod', [status(thm)], ['3', '18', '19'])).
% 0.52/0.76  thf('21', plain,
% 0.52/0.76      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.76      inference('demod', [status(thm)], ['0', '20'])).
% 0.52/0.76  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.52/0.76  
% 0.52/0.76  % SZS output end Refutation
% 0.52/0.76  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
