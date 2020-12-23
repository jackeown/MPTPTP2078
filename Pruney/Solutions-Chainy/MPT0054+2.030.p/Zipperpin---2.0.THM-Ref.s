%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dAi5AwTeUJ

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:11 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  413 ( 543 expanded)
%              Number of equality atoms :   46 (  62 expanded)
%              Maximal formula depth    :    9 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t47_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t47_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','33'])).

thf('35',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dAi5AwTeUJ
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 1.65/1.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.65/1.81  % Solved by: fo/fo7.sh
% 1.65/1.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.81  % done 1846 iterations in 1.367s
% 1.65/1.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.65/1.81  % SZS output start Refutation
% 1.65/1.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.65/1.81  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.65/1.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.65/1.81  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.81  thf(t47_xboole_1, conjecture,
% 1.65/1.81    (![A:$i,B:$i]:
% 1.65/1.81     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.65/1.81  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.81    (~( ![A:$i,B:$i]:
% 1.65/1.81        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 1.65/1.81          ( k4_xboole_0 @ A @ B ) ) )),
% 1.65/1.81    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 1.65/1.81  thf('0', plain,
% 1.65/1.81      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 1.65/1.81         != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.65/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.81  thf(commutativity_k3_xboole_0, axiom,
% 1.65/1.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.65/1.81  thf('1', plain,
% 1.65/1.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.65/1.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.81  thf('2', plain,
% 1.65/1.81      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.65/1.81         != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.65/1.81      inference('demod', [status(thm)], ['0', '1'])).
% 1.65/1.81  thf('3', plain,
% 1.65/1.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.65/1.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.81  thf(t39_xboole_1, axiom,
% 1.65/1.81    (![A:$i,B:$i]:
% 1.65/1.81     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.65/1.81  thf('4', plain,
% 1.65/1.81      (![X14 : $i, X15 : $i]:
% 1.65/1.81         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 1.65/1.81           = (k2_xboole_0 @ X14 @ X15))),
% 1.65/1.81      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.65/1.81  thf(t36_xboole_1, axiom,
% 1.65/1.81    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.65/1.81  thf('5', plain,
% 1.65/1.81      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.65/1.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.65/1.81  thf(t12_xboole_1, axiom,
% 1.65/1.81    (![A:$i,B:$i]:
% 1.65/1.81     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.65/1.81  thf('6', plain,
% 1.65/1.81      (![X5 : $i, X6 : $i]:
% 1.65/1.81         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.65/1.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.65/1.81  thf('7', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.65/1.81      inference('sup-', [status(thm)], ['5', '6'])).
% 1.65/1.81  thf(commutativity_k2_xboole_0, axiom,
% 1.65/1.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.65/1.81  thf('8', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.81  thf('9', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.65/1.81      inference('demod', [status(thm)], ['7', '8'])).
% 1.65/1.81  thf(idempotence_k3_xboole_0, axiom,
% 1.65/1.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.65/1.81  thf('10', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.65/1.81      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.65/1.81  thf(t23_xboole_1, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i]:
% 1.65/1.81     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.65/1.81       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.65/1.81  thf('11', plain,
% 1.65/1.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.65/1.81         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 1.65/1.81           = (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 1.65/1.81      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.65/1.81  thf('12', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.65/1.81           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.65/1.81      inference('sup+', [status(thm)], ['10', '11'])).
% 1.65/1.81  thf('13', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.81  thf(t22_xboole_1, axiom,
% 1.65/1.81    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.65/1.81  thf('14', plain,
% 1.65/1.81      (![X7 : $i, X8 : $i]:
% 1.65/1.81         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 1.65/1.81      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.65/1.81  thf('15', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.65/1.81      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.65/1.81  thf('16', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.65/1.81           = (k4_xboole_0 @ X0 @ X1))),
% 1.65/1.81      inference('sup+', [status(thm)], ['9', '15'])).
% 1.65/1.81  thf('17', plain,
% 1.65/1.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.65/1.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.81  thf('18', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.65/1.81           = (k4_xboole_0 @ X0 @ X1))),
% 1.65/1.81      inference('demod', [status(thm)], ['16', '17'])).
% 1.65/1.81  thf('19', plain,
% 1.65/1.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.65/1.81         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 1.65/1.81           = (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 1.65/1.81      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.65/1.81  thf('20', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.81         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.65/1.81           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.65/1.81      inference('sup+', [status(thm)], ['18', '19'])).
% 1.65/1.81  thf('21', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.65/1.81           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.65/1.81      inference('sup+', [status(thm)], ['4', '20'])).
% 1.65/1.81  thf('22', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.65/1.81      inference('demod', [status(thm)], ['12', '13', '14'])).
% 1.65/1.81  thf('23', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((X0)
% 1.65/1.81           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.65/1.81      inference('demod', [status(thm)], ['21', '22'])).
% 1.65/1.81  thf('24', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.81      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.65/1.81  thf(t40_xboole_1, axiom,
% 1.65/1.81    (![A:$i,B:$i]:
% 1.65/1.81     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.65/1.81  thf('25', plain,
% 1.65/1.81      (![X16 : $i, X17 : $i]:
% 1.65/1.81         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 1.65/1.81           = (k4_xboole_0 @ X16 @ X17))),
% 1.65/1.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.65/1.81  thf('26', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.65/1.81           = (k4_xboole_0 @ X0 @ X1))),
% 1.65/1.81      inference('sup+', [status(thm)], ['24', '25'])).
% 1.65/1.81  thf('27', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.65/1.81           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.65/1.81      inference('sup+', [status(thm)], ['23', '26'])).
% 1.65/1.81  thf('28', plain,
% 1.65/1.81      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.65/1.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.65/1.81  thf('29', plain,
% 1.65/1.81      (![X7 : $i, X8 : $i]:
% 1.65/1.81         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 1.65/1.81      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.65/1.81  thf('30', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.65/1.81      inference('sup+', [status(thm)], ['28', '29'])).
% 1.65/1.81  thf(t41_xboole_1, axiom,
% 1.65/1.81    (![A:$i,B:$i,C:$i]:
% 1.65/1.81     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.65/1.81       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.65/1.81  thf('31', plain,
% 1.65/1.81      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.65/1.81         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 1.65/1.81           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 1.65/1.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.65/1.81  thf('32', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.81         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.65/1.81           = (k4_xboole_0 @ X2 @ X0))),
% 1.65/1.81      inference('sup+', [status(thm)], ['30', '31'])).
% 1.65/1.81  thf('33', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.65/1.81           = (k4_xboole_0 @ X0 @ X1))),
% 1.65/1.81      inference('demod', [status(thm)], ['27', '32'])).
% 1.65/1.81  thf('34', plain,
% 1.65/1.81      (![X0 : $i, X1 : $i]:
% 1.65/1.81         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.65/1.81           = (k4_xboole_0 @ X0 @ X1))),
% 1.65/1.81      inference('sup+', [status(thm)], ['3', '33'])).
% 1.65/1.81  thf('35', plain,
% 1.65/1.81      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.65/1.81      inference('demod', [status(thm)], ['2', '34'])).
% 1.65/1.81  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 1.65/1.81  
% 1.65/1.81  % SZS output end Refutation
% 1.65/1.81  
% 1.65/1.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
