%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NQ3JiT9VNd

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:12 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  386 ( 449 expanded)
%              Number of equality atoms :   43 (  52 expanded)
%              Maximal formula depth    :    9 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
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

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','30'])).

thf('32',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NQ3JiT9VNd
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 2.12/2.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.12/2.34  % Solved by: fo/fo7.sh
% 2.12/2.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.12/2.34  % done 1971 iterations in 1.893s
% 2.12/2.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.12/2.34  % SZS output start Refutation
% 2.12/2.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.12/2.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.12/2.34  thf(sk_B_type, type, sk_B: $i).
% 2.12/2.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.12/2.34  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.12/2.34  thf(sk_A_type, type, sk_A: $i).
% 2.12/2.34  thf(t47_xboole_1, conjecture,
% 2.12/2.34    (![A:$i,B:$i]:
% 2.12/2.34     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.12/2.34  thf(zf_stmt_0, negated_conjecture,
% 2.12/2.34    (~( ![A:$i,B:$i]:
% 2.12/2.34        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 2.12/2.34          ( k4_xboole_0 @ A @ B ) ) )),
% 2.12/2.34    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 2.12/2.34  thf('0', plain,
% 2.12/2.34      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 2.12/2.34         != (k4_xboole_0 @ sk_A @ sk_B))),
% 2.12/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.34  thf(commutativity_k3_xboole_0, axiom,
% 2.12/2.34    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.12/2.34  thf('1', plain,
% 2.12/2.34      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.12/2.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.12/2.34  thf('2', plain,
% 2.12/2.34      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 2.12/2.34         != (k4_xboole_0 @ sk_A @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['0', '1'])).
% 2.12/2.34  thf('3', plain,
% 2.12/2.34      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.12/2.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.12/2.34  thf(t39_xboole_1, axiom,
% 2.12/2.34    (![A:$i,B:$i]:
% 2.12/2.34     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.12/2.34  thf('4', plain,
% 2.12/2.34      (![X15 : $i, X16 : $i]:
% 2.12/2.34         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 2.12/2.34           = (k2_xboole_0 @ X15 @ X16))),
% 2.12/2.34      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.12/2.34  thf(t36_xboole_1, axiom,
% 2.12/2.34    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.12/2.34  thf('5', plain,
% 2.12/2.34      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 2.12/2.34      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.12/2.34  thf(t12_xboole_1, axiom,
% 2.12/2.34    (![A:$i,B:$i]:
% 2.12/2.34     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.12/2.34  thf('6', plain,
% 2.12/2.34      (![X4 : $i, X5 : $i]:
% 2.12/2.34         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 2.12/2.34      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.12/2.34  thf('7', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.12/2.34      inference('sup-', [status(thm)], ['5', '6'])).
% 2.12/2.34  thf(commutativity_k2_xboole_0, axiom,
% 2.12/2.34    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.12/2.34  thf('8', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.12/2.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.12/2.34  thf('9', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 2.12/2.34      inference('demod', [status(thm)], ['7', '8'])).
% 2.12/2.34  thf('10', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.12/2.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.12/2.34  thf(t21_xboole_1, axiom,
% 2.12/2.34    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 2.12/2.34  thf('11', plain,
% 2.12/2.34      (![X6 : $i, X7 : $i]:
% 2.12/2.34         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 2.12/2.34      inference('cnf', [status(esa)], [t21_xboole_1])).
% 2.12/2.34  thf('12', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 2.12/2.34      inference('sup+', [status(thm)], ['10', '11'])).
% 2.12/2.34  thf('13', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 2.12/2.34           = (k4_xboole_0 @ X0 @ X1))),
% 2.12/2.34      inference('sup+', [status(thm)], ['9', '12'])).
% 2.12/2.34  thf('14', plain,
% 2.12/2.34      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.12/2.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.12/2.34  thf('15', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.12/2.34           = (k4_xboole_0 @ X0 @ X1))),
% 2.12/2.34      inference('demod', [status(thm)], ['13', '14'])).
% 2.12/2.34  thf(t23_xboole_1, axiom,
% 2.12/2.34    (![A:$i,B:$i,C:$i]:
% 2.12/2.34     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 2.12/2.34       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 2.12/2.34  thf('16', plain,
% 2.12/2.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.12/2.34         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 2.12/2.34           = (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ 
% 2.12/2.34              (k3_xboole_0 @ X10 @ X12)))),
% 2.12/2.34      inference('cnf', [status(esa)], [t23_xboole_1])).
% 2.12/2.34  thf('17', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.34         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 2.12/2.34           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 2.12/2.34      inference('sup+', [status(thm)], ['15', '16'])).
% 2.12/2.34  thf('18', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 2.12/2.34           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 2.12/2.34      inference('sup+', [status(thm)], ['4', '17'])).
% 2.12/2.34  thf('19', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 2.12/2.34      inference('sup+', [status(thm)], ['10', '11'])).
% 2.12/2.34  thf('20', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((X0)
% 2.12/2.34           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 2.12/2.34      inference('demod', [status(thm)], ['18', '19'])).
% 2.12/2.34  thf('21', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.12/2.34      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.12/2.34  thf(t40_xboole_1, axiom,
% 2.12/2.34    (![A:$i,B:$i]:
% 2.12/2.34     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.12/2.34  thf('22', plain,
% 2.12/2.34      (![X17 : $i, X18 : $i]:
% 2.12/2.34         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 2.12/2.34           = (k4_xboole_0 @ X17 @ X18))),
% 2.12/2.34      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.12/2.34  thf('23', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 2.12/2.34           = (k4_xboole_0 @ X0 @ X1))),
% 2.12/2.34      inference('sup+', [status(thm)], ['21', '22'])).
% 2.12/2.34  thf('24', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.12/2.34           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 2.12/2.34      inference('sup+', [status(thm)], ['20', '23'])).
% 2.12/2.34  thf('25', plain,
% 2.12/2.34      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 2.12/2.34      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.12/2.34  thf(t22_xboole_1, axiom,
% 2.12/2.34    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 2.12/2.34  thf('26', plain,
% 2.12/2.34      (![X8 : $i, X9 : $i]:
% 2.12/2.34         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 2.12/2.34      inference('cnf', [status(esa)], [t22_xboole_1])).
% 2.12/2.34  thf('27', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 2.12/2.34      inference('sup+', [status(thm)], ['25', '26'])).
% 2.12/2.34  thf(t41_xboole_1, axiom,
% 2.12/2.34    (![A:$i,B:$i,C:$i]:
% 2.12/2.34     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.12/2.34       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.12/2.34  thf('28', plain,
% 2.12/2.34      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.12/2.34         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 2.12/2.34           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 2.12/2.34      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.12/2.34  thf('29', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.34         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 2.12/2.34           = (k4_xboole_0 @ X2 @ X0))),
% 2.12/2.34      inference('sup+', [status(thm)], ['27', '28'])).
% 2.12/2.34  thf('30', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 2.12/2.34           = (k4_xboole_0 @ X0 @ X1))),
% 2.12/2.34      inference('demod', [status(thm)], ['24', '29'])).
% 2.12/2.34  thf('31', plain,
% 2.12/2.34      (![X0 : $i, X1 : $i]:
% 2.12/2.34         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 2.12/2.34           = (k4_xboole_0 @ X0 @ X1))),
% 2.12/2.34      inference('sup+', [status(thm)], ['3', '30'])).
% 2.12/2.34  thf('32', plain,
% 2.12/2.34      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 2.12/2.34      inference('demod', [status(thm)], ['2', '31'])).
% 2.12/2.34  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 2.12/2.34  
% 2.12/2.34  % SZS output end Refutation
% 2.12/2.34  
% 2.12/2.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
