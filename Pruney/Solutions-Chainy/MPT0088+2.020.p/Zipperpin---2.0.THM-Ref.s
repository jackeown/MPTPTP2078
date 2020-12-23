%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9e7ygQui3z

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:37 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   48 (  58 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  342 ( 447 expanded)
%              Number of equality atoms :   32 (  40 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X17 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9e7ygQui3z
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 780 iterations in 0.291s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.73  thf(t81_xboole_1, conjecture,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.54/0.73       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.73        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.54/0.73          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 0.54/0.73  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t48_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.54/0.73           = (k3_xboole_0 @ X12 @ X13))),
% 0.54/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.73  thf('2', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(d7_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.54/0.73       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf(t50_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.54/0.73       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.54/0.73           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ 
% 0.54/0.73              (k3_xboole_0 @ X17 @ X19)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.54/0.73  thf(t49_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.54/0.73       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.54/0.73           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.54/0.73      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.54/0.73           = (k3_xboole_0 @ X17 @ 
% 0.54/0.73              (k4_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X19))))),
% 0.54/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ sk_A @ 
% 0.54/0.73           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.54/0.73           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['4', '7'])).
% 0.54/0.73  thf(t3_boole, axiom,
% 0.54/0.73    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.73  thf('9', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ sk_A @ 
% 0.54/0.73           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.54/0.73           = (k3_xboole_0 @ sk_A @ X0))),
% 0.54/0.73      inference('demod', [status(thm)], ['8', '9'])).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.54/0.73         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['1', '10'])).
% 0.54/0.73  thf(t47_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X10 : $i, X11 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.54/0.73           = (k4_xboole_0 @ X10 @ X11))),
% 0.54/0.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.54/0.73         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['11', '12'])).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (![X10 : $i, X11 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.54/0.73           = (k4_xboole_0 @ X10 @ X11))),
% 0.54/0.73      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.54/0.73         = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.54/0.73      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.54/0.73           = (k3_xboole_0 @ X17 @ 
% 0.54/0.73              (k4_xboole_0 @ X18 @ (k3_xboole_0 @ X17 @ X19))))),
% 0.54/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))
% 0.54/0.73         = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['15', '16'])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.54/0.73           = (k3_xboole_0 @ X12 @ X13))),
% 0.54/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.73  thf(t36_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.54/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.54/0.73  thf(l32_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (![X3 : $i, X5 : $i]:
% 0.54/0.73         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.54/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['18', '21'])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X16))
% 0.54/0.73           = (k4_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16))),
% 0.54/0.73      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.54/0.73      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 0.54/0.73      inference('demod', [status(thm)], ['17', '24'])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (![X0 : $i, X2 : $i]:
% 0.54/0.73         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.54/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.73        | (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.54/0.73  thf('28', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C))),
% 0.54/0.73      inference('simplify', [status(thm)], ['27'])).
% 0.54/0.73  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
