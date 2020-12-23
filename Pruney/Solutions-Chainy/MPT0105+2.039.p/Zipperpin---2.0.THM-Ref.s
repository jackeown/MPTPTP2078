%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lQ5FgKFtPD

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:09 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  237 ( 237 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t98_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t98_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lQ5FgKFtPD
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:50:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.52  % Solved by: fo/fo7.sh
% 0.36/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.52  % done 231 iterations in 0.076s
% 0.36/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.52  % SZS output start Refutation
% 0.36/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.52  thf(t98_xboole_1, conjecture,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.52    (~( ![A:$i,B:$i]:
% 0.36/0.52        ( ( k2_xboole_0 @ A @ B ) =
% 0.36/0.52          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.36/0.52    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.36/0.52  thf('0', plain,
% 0.36/0.52      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.36/0.52         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(t48_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.52  thf('1', plain,
% 0.36/0.52      (![X9 : $i, X10 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.36/0.52           = (k3_xboole_0 @ X9 @ X10))),
% 0.36/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.52  thf(t36_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.52  thf('2', plain,
% 0.36/0.52      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.36/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.52  thf(t37_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.52  thf('3', plain,
% 0.36/0.52      (![X4 : $i, X6 : $i]:
% 0.36/0.52         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.36/0.52      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.36/0.52  thf('4', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.36/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.52  thf('5', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.36/0.52      inference('sup+', [status(thm)], ['1', '4'])).
% 0.36/0.52  thf(t49_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.36/0.52       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.36/0.52  thf('6', plain,
% 0.36/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.52         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.36/0.52           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.36/0.52      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.36/0.52  thf(t94_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k2_xboole_0 @ A @ B ) =
% 0.36/0.52       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.52  thf('7', plain,
% 0.36/0.52      (![X18 : $i, X19 : $i]:
% 0.36/0.52         ((k2_xboole_0 @ X18 @ X19)
% 0.36/0.52           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.36/0.52              (k3_xboole_0 @ X18 @ X19)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.36/0.52  thf(t91_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.52       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.36/0.52  thf('8', plain,
% 0.36/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.52         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.36/0.52           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.36/0.52  thf('9', plain,
% 0.36/0.52      (![X18 : $i, X19 : $i]:
% 0.36/0.52         ((k2_xboole_0 @ X18 @ X19)
% 0.36/0.52           = (k5_xboole_0 @ X18 @ 
% 0.36/0.52              (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X18 @ X19))))),
% 0.36/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.52  thf('10', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.52         ((k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.52           = (k5_xboole_0 @ X2 @ 
% 0.36/0.52              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.36/0.52               (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))))),
% 0.36/0.52      inference('sup+', [status(thm)], ['6', '9'])).
% 0.36/0.52  thf('11', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.36/0.52           = (k5_xboole_0 @ X0 @ 
% 0.36/0.52              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)))),
% 0.36/0.52      inference('sup+', [status(thm)], ['5', '10'])).
% 0.36/0.52  thf(t39_xboole_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.52  thf('12', plain,
% 0.36/0.52      (![X7 : $i, X8 : $i]:
% 0.36/0.52         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.36/0.52           = (k2_xboole_0 @ X7 @ X8))),
% 0.36/0.52      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.36/0.52  thf(t5_boole, axiom,
% 0.36/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.52  thf('13', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.36/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.36/0.52  thf('14', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((k2_xboole_0 @ X0 @ X1)
% 0.36/0.52           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.36/0.52      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.36/0.52  thf('15', plain,
% 0.36/0.52      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.52      inference('demod', [status(thm)], ['0', '14'])).
% 0.36/0.52  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.36/0.52  
% 0.36/0.52  % SZS output end Refutation
% 0.36/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
