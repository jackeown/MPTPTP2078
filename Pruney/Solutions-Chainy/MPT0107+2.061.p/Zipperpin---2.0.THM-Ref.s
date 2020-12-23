%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AlRzsm5IgL

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :  184 ( 202 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X3 )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    $false ),
    inference(simplify,[status(thm)],['12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AlRzsm5IgL
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 22 iterations in 0.012s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(t100_xboole_1, conjecture,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i]:
% 0.22/0.46        ( ( k4_xboole_0 @ A @ B ) =
% 0.22/0.46          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.22/0.46         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(t47_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i]:
% 0.22/0.46         ((k4_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5))
% 0.22/0.46           = (k4_xboole_0 @ X4 @ X5))),
% 0.22/0.46      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.22/0.46  thf(t48_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X6 : $i, X7 : $i]:
% 0.22/0.46         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.22/0.46           = (k3_xboole_0 @ X6 @ X7))),
% 0.22/0.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.22/0.46           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (![X6 : $i, X7 : $i]:
% 0.22/0.46         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.22/0.46           = (k3_xboole_0 @ X6 @ X7))),
% 0.22/0.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.46           = (k3_xboole_0 @ X1 @ X0))),
% 0.22/0.46      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.46  thf(l98_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( k5_xboole_0 @ A @ B ) =
% 0.22/0.46       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k5_xboole_0 @ X0 @ X1)
% 0.22/0.46           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.46      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.46           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.22/0.46              (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.46  thf(t40_xboole_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.46  thf('8', plain,
% 0.22/0.46      (![X2 : $i, X3 : $i]:
% 0.22/0.46         ((k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X3)
% 0.22/0.46           = (k4_xboole_0 @ X2 @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.46           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i]:
% 0.22/0.46         ((k4_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5))
% 0.22/0.46           = (k4_xboole_0 @ X4 @ X5))),
% 0.22/0.46      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.46           = (k4_xboole_0 @ X1 @ X0))),
% 0.22/0.46      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.46  thf('12', plain,
% 0.22/0.46      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['0', '11'])).
% 0.22/0.46  thf('13', plain, ($false), inference('simplify', [status(thm)], ['12'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
