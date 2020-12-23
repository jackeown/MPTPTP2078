%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F7gqyVfdiN

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :  169 ( 178 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X4 @ X3 ) ) ) ),
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
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F7gqyVfdiN
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:36:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 220 iterations in 0.112s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(t55_xboole_1, conjecture,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 0.20/0.57       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i,B:$i]:
% 0.20/0.57        ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) =
% 0.20/0.57          ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t55_xboole_1])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.57         (k3_xboole_0 @ sk_A @ sk_B))
% 0.20/0.57         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.57             (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.57  thf(t47_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X5 : $i, X6 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.20/0.57           = (k4_xboole_0 @ X5 @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.57           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.57      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.57  thf('4', plain,
% 0.20/0.57      (![X5 : $i, X6 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6))
% 0.20/0.57           = (k4_xboole_0 @ X5 @ X6))),
% 0.20/0.57      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.57  thf(t42_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.57       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X4) @ X3)
% 0.20/0.57           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X4 @ X3)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.57           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.20/0.57              (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.20/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 0.20/0.57           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['3', '6'])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.57         (k3_xboole_0 @ sk_A @ sk_B))
% 0.20/0.57         != (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.57             (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.57  thf('9', plain, ($false), inference('simplify', [status(thm)], ['8'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.20/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
