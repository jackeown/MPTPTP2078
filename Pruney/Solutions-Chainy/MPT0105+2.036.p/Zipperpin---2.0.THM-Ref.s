%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G09PiH9NAG

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  44 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  265 ( 274 expanded)
%              Number of equality atoms :   29 (  30 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','12'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G09PiH9NAG
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 67 iterations in 0.030s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(t98_xboole_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( k2_xboole_0 @ A @ B ) =
% 0.20/0.48          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.20/0.48         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t79_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X10)),
% 0.20/0.48      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.48  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf(t83_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf(t48_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.20/0.48           = (k3_xboole_0 @ X6 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X0 @ X0)
% 0.20/0.48           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(t3_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('8', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.20/0.48           = (k3_xboole_0 @ X6 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf(t2_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.48  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '12'])).
% 0.20/0.48  thf(t94_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k2_xboole_0 @ A @ B ) =
% 0.20/0.48       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X17 @ X18)
% 0.20/0.48           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.20/0.48              (k3_xboole_0 @ X17 @ X18)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.20/0.48  thf(t91_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.48       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.48         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.20/0.48           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X17 @ X18)
% 0.20/0.48           = (k5_xboole_0 @ X17 @ 
% 0.20/0.48              (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X18))))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.48           = (k5_xboole_0 @ X0 @ 
% 0.20/0.48              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '16'])).
% 0.20/0.48  thf(t39_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.20/0.48           = (k2_xboole_0 @ X3 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.48  thf(t5_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('19', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X0 @ X1)
% 0.20/0.48           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '20'])).
% 0.20/0.48  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
