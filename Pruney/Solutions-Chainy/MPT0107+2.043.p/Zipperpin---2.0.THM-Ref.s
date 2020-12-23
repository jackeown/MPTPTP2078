%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YMQOMILhaq

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:15 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   51 (  56 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  349 ( 394 expanded)
%              Number of equality atoms :   40 (  45 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['8','9','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YMQOMILhaq
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:37:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 202 iterations in 0.135s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(t100_xboole_1, conjecture,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i]:
% 0.39/0.57        ( ( k4_xboole_0 @ A @ B ) =
% 0.39/0.57          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.39/0.57  thf('0', plain,
% 0.39/0.57      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.39/0.57         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t48_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X8 : $i, X9 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.39/0.57           = (k3_xboole_0 @ X8 @ X9))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf(t95_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k3_xboole_0 @ A @ B ) =
% 0.39/0.57       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X15 : $i, X16 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X15 @ X16)
% 0.39/0.57           = (k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ 
% 0.39/0.57              (k2_xboole_0 @ X15 @ X16)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.39/0.57  thf(t91_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.57       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.39/0.57           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X15 : $i, X16 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X15 @ X16)
% 0.39/0.57           = (k5_xboole_0 @ X15 @ 
% 0.39/0.57              (k5_xboole_0 @ X16 @ (k2_xboole_0 @ X15 @ X16))))),
% 0.39/0.57      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.39/0.57           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.57  thf(commutativity_k5_xboole_0, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.39/0.57           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['5', '6'])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ X0)
% 0.39/0.57           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['4', '7'])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.39/0.57  thf(t98_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X17 : $i, X18 : $i]:
% 0.39/0.57         ((k2_xboole_0 @ X17 @ X18)
% 0.39/0.57           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.39/0.57  thf(t92_xboole_1, axiom,
% 0.39/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.39/0.57  thf('11', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.57         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.39/0.57           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.57  thf('13', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.57           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.39/0.57  thf(t5_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.57  thf('15', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.39/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.39/0.57  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['13', '16'])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.39/0.57           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['10', '17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ X1 @ X0)
% 0.39/0.57           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.39/0.57      inference('demod', [status(thm)], ['8', '9', '18'])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.39/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['1', '19'])).
% 0.39/0.57  thf(t36_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.39/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.57  thf(l32_xboole_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X2 : $i, X4 : $i]:
% 0.39/0.57         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.39/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X8 : $i, X9 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.39/0.57           = (k3_xboole_0 @ X8 @ X9))),
% 0.39/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.39/0.57           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf(t3_boole, axiom,
% 0.39/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.57  thf('26', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.39/0.57           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((k4_xboole_0 @ X1 @ X0)
% 0.39/0.57           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['20', '27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['0', '28'])).
% 0.39/0.57  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
