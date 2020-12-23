%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4SsFQrL2sp

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:53 EST 2020

% Result     : Theorem 2.84s
% Output     : Refutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   49 (  68 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  401 ( 564 expanded)
%              Number of equality atoms :   42 (  61 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t93_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t93_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k2_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['19','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ X2 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8','30','31'])).

thf('33',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4SsFQrL2sp
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:07:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 2.84/3.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.84/3.04  % Solved by: fo/fo7.sh
% 2.84/3.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.84/3.04  % done 1159 iterations in 2.564s
% 2.84/3.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.84/3.04  % SZS output start Refutation
% 2.84/3.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.84/3.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.84/3.04  thf(sk_B_type, type, sk_B: $i).
% 2.84/3.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.84/3.04  thf(sk_A_type, type, sk_A: $i).
% 2.84/3.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.84/3.04  thf(t93_xboole_1, conjecture,
% 2.84/3.04    (![A:$i,B:$i]:
% 2.84/3.04     ( ( k2_xboole_0 @ A @ B ) =
% 2.84/3.04       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.84/3.04  thf(zf_stmt_0, negated_conjecture,
% 2.84/3.04    (~( ![A:$i,B:$i]:
% 2.84/3.04        ( ( k2_xboole_0 @ A @ B ) =
% 2.84/3.04          ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 2.84/3.04    inference('cnf.neg', [status(esa)], [t93_xboole_1])).
% 2.84/3.04  thf('0', plain,
% 2.84/3.04      (((k2_xboole_0 @ sk_A @ sk_B)
% 2.84/3.04         != (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 2.84/3.04             (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.84/3.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.84/3.04  thf(d6_xboole_0, axiom,
% 2.84/3.04    (![A:$i,B:$i]:
% 2.84/3.04     ( ( k5_xboole_0 @ A @ B ) =
% 2.84/3.04       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.84/3.04  thf('1', plain,
% 2.84/3.04      (![X4 : $i, X5 : $i]:
% 2.84/3.04         ((k5_xboole_0 @ X4 @ X5)
% 2.84/3.04           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 2.84/3.04      inference('cnf', [status(esa)], [d6_xboole_0])).
% 2.84/3.04  thf(t51_xboole_1, axiom,
% 2.84/3.04    (![A:$i,B:$i]:
% 2.84/3.04     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 2.84/3.04       ( A ) ))).
% 2.84/3.04  thf('2', plain,
% 2.84/3.04      (![X12 : $i, X13 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))
% 2.84/3.04           = (X12))),
% 2.84/3.04      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.84/3.04  thf(t4_xboole_1, axiom,
% 2.84/3.04    (![A:$i,B:$i,C:$i]:
% 2.84/3.04     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 2.84/3.04       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.84/3.04  thf('3', plain,
% 2.84/3.04      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 2.84/3.04           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.84/3.04      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.84/3.04  thf(commutativity_k2_xboole_0, axiom,
% 2.84/3.04    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.84/3.04  thf('4', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.04  thf('5', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 2.84/3.04           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.84/3.04      inference('sup+', [status(thm)], ['3', '4'])).
% 2.84/3.04  thf('6', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ X1 @ X0)
% 2.84/3.04           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ 
% 2.84/3.04              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)))),
% 2.84/3.04      inference('sup+', [status(thm)], ['2', '5'])).
% 2.84/3.04  thf('7', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 2.84/3.04           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 2.84/3.04      inference('sup+', [status(thm)], ['1', '6'])).
% 2.84/3.04  thf('8', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.04  thf(commutativity_k3_xboole_0, axiom,
% 2.84/3.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.84/3.04  thf('9', plain,
% 2.84/3.04      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.84/3.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.84/3.04  thf('10', plain,
% 2.84/3.04      (![X12 : $i, X13 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))
% 2.84/3.04           = (X12))),
% 2.84/3.04      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.84/3.04  thf('11', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 2.84/3.04           = (X0))),
% 2.84/3.04      inference('sup+', [status(thm)], ['9', '10'])).
% 2.84/3.04  thf('12', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.04  thf('13', plain,
% 2.84/3.04      (![X12 : $i, X13 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))
% 2.84/3.04           = (X12))),
% 2.84/3.04      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.84/3.04  thf('14', plain,
% 2.84/3.04      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 2.84/3.04           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.84/3.04      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.84/3.04  thf('15', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ X0 @ X1)
% 2.84/3.04           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ 
% 2.84/3.04              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)))),
% 2.84/3.04      inference('sup+', [status(thm)], ['13', '14'])).
% 2.84/3.04  thf(idempotence_k2_xboole_0, axiom,
% 2.84/3.04    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.84/3.04  thf('16', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 2.84/3.04      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.84/3.04  thf('17', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 2.84/3.04           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.84/3.04      inference('sup+', [status(thm)], ['3', '4'])).
% 2.84/3.04  thf('18', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ X1 @ X0)
% 2.84/3.04           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 2.84/3.04      inference('sup+', [status(thm)], ['16', '17'])).
% 2.84/3.04  thf('19', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0) @ 
% 2.84/3.04           (k3_xboole_0 @ X1 @ X2))
% 2.84/3.04           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k2_xboole_0 @ X1 @ X0)))),
% 2.84/3.04      inference('sup+', [status(thm)], ['15', '18'])).
% 2.84/3.04  thf('20', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.04  thf('21', plain,
% 2.84/3.04      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k2_xboole_0 @ X9 @ X10) @ X11)
% 2.84/3.04           = (k2_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 2.84/3.04      inference('cnf', [status(esa)], [t4_xboole_1])).
% 2.84/3.04  thf('22', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 2.84/3.04           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 2.84/3.04      inference('sup+', [status(thm)], ['20', '21'])).
% 2.84/3.04  thf('23', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.04  thf('24', plain,
% 2.84/3.04      (![X12 : $i, X13 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k4_xboole_0 @ X12 @ X13))
% 2.84/3.04           = (X12))),
% 2.84/3.04      inference('cnf', [status(esa)], [t51_xboole_1])).
% 2.84/3.04  thf('25', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 2.84/3.04           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.84/3.04      inference('sup+', [status(thm)], ['3', '4'])).
% 2.84/3.04  thf('26', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ X0 @ X1)
% 2.84/3.04           = (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))))),
% 2.84/3.04      inference('demod', [status(thm)], ['19', '22', '23', '24', '25'])).
% 2.84/3.04  thf('27', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ X0 @ X2)
% 2.84/3.04           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)))),
% 2.84/3.04      inference('sup+', [status(thm)], ['12', '26'])).
% 2.84/3.04  thf('28', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 2.84/3.04           = (k2_xboole_0 @ X1 @ X0))),
% 2.84/3.04      inference('sup+', [status(thm)], ['11', '27'])).
% 2.84/3.04  thf('29', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.04  thf('30', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 2.84/3.04           = (k2_xboole_0 @ X1 @ X0))),
% 2.84/3.04      inference('demod', [status(thm)], ['28', '29'])).
% 2.84/3.04  thf('31', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.84/3.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.84/3.04  thf('32', plain,
% 2.84/3.04      (![X0 : $i, X1 : $i]:
% 2.84/3.04         ((k2_xboole_0 @ X1 @ X0)
% 2.84/3.04           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.84/3.04      inference('demod', [status(thm)], ['7', '8', '30', '31'])).
% 2.84/3.04  thf('33', plain,
% 2.84/3.04      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 2.84/3.04      inference('demod', [status(thm)], ['0', '32'])).
% 2.84/3.04  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 2.84/3.04  
% 2.84/3.04  % SZS output end Refutation
% 2.84/3.04  
% 2.84/3.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
