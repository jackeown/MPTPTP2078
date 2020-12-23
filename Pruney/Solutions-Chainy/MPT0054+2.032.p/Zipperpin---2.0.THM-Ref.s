%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N9C9KBrztV

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:12 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   50 (  56 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  374 ( 422 expanded)
%              Number of equality atoms :   41 (  47 expanded)
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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','28'])).

thf('30',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N9C9KBrztV
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.61/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.84  % Solved by: fo/fo7.sh
% 0.61/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.84  % done 613 iterations in 0.426s
% 0.61/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.84  % SZS output start Refutation
% 0.61/0.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.84  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.84  thf(t47_xboole_1, conjecture,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.61/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.84    (~( ![A:$i,B:$i]:
% 0.61/0.84        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 0.61/0.84          ( k4_xboole_0 @ A @ B ) ) )),
% 0.61/0.84    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 0.61/0.84  thf('0', plain,
% 0.61/0.84      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.61/0.84         != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.84  thf(commutativity_k3_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.61/0.84  thf('1', plain,
% 0.61/0.84      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.61/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.84  thf('2', plain,
% 0.61/0.84      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.61/0.84         != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.84      inference('demod', [status(thm)], ['0', '1'])).
% 0.61/0.84  thf('3', plain,
% 0.61/0.84      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.61/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.84  thf(t39_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.61/0.84  thf('4', plain,
% 0.61/0.84      (![X14 : $i, X15 : $i]:
% 0.61/0.84         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.61/0.84           = (k2_xboole_0 @ X14 @ X15))),
% 0.61/0.84      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.61/0.84  thf(t36_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.84  thf('5', plain,
% 0.61/0.84      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.61/0.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.61/0.84  thf(t28_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.61/0.84  thf('6', plain,
% 0.61/0.84      (![X10 : $i, X11 : $i]:
% 0.61/0.84         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.61/0.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.61/0.84  thf('7', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.61/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.61/0.84      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.84  thf('8', plain,
% 0.61/0.84      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.61/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.84  thf('9', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.61/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.61/0.84      inference('demod', [status(thm)], ['7', '8'])).
% 0.61/0.84  thf(t23_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.61/0.84       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.61/0.84  thf('10', plain,
% 0.61/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.61/0.84         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.61/0.84           = (k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.61/0.84  thf('11', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.84         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.61/0.84           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.61/0.84      inference('sup+', [status(thm)], ['9', '10'])).
% 0.61/0.84  thf('12', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.61/0.84           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.61/0.84      inference('sup+', [status(thm)], ['4', '11'])).
% 0.61/0.84  thf(idempotence_k3_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.61/0.84  thf('13', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.61/0.84      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.61/0.84  thf('14', plain,
% 0.61/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.61/0.84         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.61/0.84           = (k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.61/0.84  thf('15', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.61/0.84           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.61/0.84      inference('sup+', [status(thm)], ['13', '14'])).
% 0.61/0.84  thf(commutativity_k2_xboole_0, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.61/0.84  thf('16', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.84  thf(t22_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.61/0.84  thf('17', plain,
% 0.61/0.84      (![X5 : $i, X6 : $i]:
% 0.61/0.84         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 0.61/0.84      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.61/0.84  thf('18', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 0.61/0.84      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.61/0.84  thf('19', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((X0)
% 0.61/0.84           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.61/0.84      inference('demod', [status(thm)], ['12', '18'])).
% 0.61/0.84  thf('20', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.84      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.84  thf(t40_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i]:
% 0.61/0.84     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.61/0.84  thf('21', plain,
% 0.61/0.84      (![X16 : $i, X17 : $i]:
% 0.61/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 0.61/0.84           = (k4_xboole_0 @ X16 @ X17))),
% 0.61/0.84      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.61/0.84  thf('22', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.61/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.61/0.84      inference('sup+', [status(thm)], ['20', '21'])).
% 0.61/0.84  thf('23', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.61/0.84           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.61/0.84      inference('sup+', [status(thm)], ['19', '22'])).
% 0.61/0.84  thf(t41_xboole_1, axiom,
% 0.61/0.84    (![A:$i,B:$i,C:$i]:
% 0.61/0.84     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.61/0.84       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.61/0.84  thf('24', plain,
% 0.61/0.84      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.61/0.84         ((k4_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.61/0.84           = (k4_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.61/0.84      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.61/0.84  thf('25', plain,
% 0.61/0.84      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.61/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.84  thf('26', plain,
% 0.61/0.84      (![X5 : $i, X6 : $i]:
% 0.61/0.84         ((k2_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)) = (X5))),
% 0.61/0.84      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.61/0.84  thf('27', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.61/0.84      inference('sup+', [status(thm)], ['25', '26'])).
% 0.61/0.84  thf('28', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.61/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.61/0.84      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.61/0.84  thf('29', plain,
% 0.61/0.84      (![X0 : $i, X1 : $i]:
% 0.61/0.84         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.61/0.84           = (k4_xboole_0 @ X0 @ X1))),
% 0.61/0.84      inference('sup+', [status(thm)], ['3', '28'])).
% 0.61/0.84  thf('30', plain,
% 0.61/0.84      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.84      inference('demod', [status(thm)], ['2', '29'])).
% 0.61/0.84  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.61/0.84  
% 0.61/0.84  % SZS output end Refutation
% 0.61/0.84  
% 0.69/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
