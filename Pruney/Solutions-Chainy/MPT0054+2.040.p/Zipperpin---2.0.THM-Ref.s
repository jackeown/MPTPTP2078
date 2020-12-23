%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uJCdcb8hPr

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:12 EST 2020

% Result     : Theorem 9.84s
% Output     : Refutation 9.84s
% Verified   : 
% Statistics : Number of formulae       :   52 (  62 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  416 ( 504 expanded)
%              Number of equality atoms :   43 (  53 expanded)
%              Maximal formula depth    :   10 (   7 average)

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

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','21','22'])).

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
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uJCdcb8hPr
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:46:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 9.84/10.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.84/10.06  % Solved by: fo/fo7.sh
% 9.84/10.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.84/10.06  % done 6076 iterations in 9.596s
% 9.84/10.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.84/10.06  % SZS output start Refutation
% 9.84/10.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.84/10.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.84/10.06  thf(sk_B_type, type, sk_B: $i).
% 9.84/10.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.84/10.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.84/10.06  thf(sk_A_type, type, sk_A: $i).
% 9.84/10.06  thf(t47_xboole_1, conjecture,
% 9.84/10.06    (![A:$i,B:$i]:
% 9.84/10.06     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 9.84/10.06  thf(zf_stmt_0, negated_conjecture,
% 9.84/10.06    (~( ![A:$i,B:$i]:
% 9.84/10.06        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 9.84/10.06          ( k4_xboole_0 @ A @ B ) ) )),
% 9.84/10.06    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 9.84/10.06  thf('0', plain,
% 9.84/10.06      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 9.84/10.06         != (k4_xboole_0 @ sk_A @ sk_B))),
% 9.84/10.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.84/10.06  thf(commutativity_k3_xboole_0, axiom,
% 9.84/10.06    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 9.84/10.06  thf('1', plain,
% 9.84/10.06      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 9.84/10.06      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.84/10.06  thf('2', plain,
% 9.84/10.06      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 9.84/10.06         != (k4_xboole_0 @ sk_A @ sk_B))),
% 9.84/10.06      inference('demod', [status(thm)], ['0', '1'])).
% 9.84/10.06  thf(t39_xboole_1, axiom,
% 9.84/10.06    (![A:$i,B:$i]:
% 9.84/10.06     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 9.84/10.06  thf('3', plain,
% 9.84/10.06      (![X15 : $i, X16 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 9.84/10.06           = (k2_xboole_0 @ X15 @ X16))),
% 9.84/10.06      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.84/10.06  thf(commutativity_k2_xboole_0, axiom,
% 9.84/10.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 9.84/10.06  thf('4', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.84/10.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.84/10.06  thf(t24_xboole_1, axiom,
% 9.84/10.06    (![A:$i,B:$i,C:$i]:
% 9.84/10.06     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 9.84/10.06       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 9.84/10.06  thf('5', plain,
% 9.84/10.06      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12))
% 9.84/10.06           = (k3_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 9.84/10.06              (k2_xboole_0 @ X10 @ X12)))),
% 9.84/10.06      inference('cnf', [status(esa)], [t24_xboole_1])).
% 9.84/10.06  thf('6', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 9.84/10.06           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 9.84/10.06      inference('sup+', [status(thm)], ['4', '5'])).
% 9.84/10.06  thf('7', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X2))
% 9.84/10.06           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 9.84/10.06              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 9.84/10.06      inference('sup+', [status(thm)], ['3', '6'])).
% 9.84/10.06  thf('8', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.84/10.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.84/10.06  thf('9', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 9.84/10.06           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 9.84/10.06      inference('sup+', [status(thm)], ['4', '5'])).
% 9.84/10.06  thf('10', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 9.84/10.06           = (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 9.84/10.06      inference('sup+', [status(thm)], ['8', '9'])).
% 9.84/10.06  thf('11', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))
% 9.84/10.06           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 9.84/10.06      inference('sup+', [status(thm)], ['7', '10'])).
% 9.84/10.06  thf(t36_xboole_1, axiom,
% 9.84/10.06    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 9.84/10.06  thf('12', plain,
% 9.84/10.06      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 9.84/10.06      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.84/10.06  thf(t12_xboole_1, axiom,
% 9.84/10.06    (![A:$i,B:$i]:
% 9.84/10.06     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 9.84/10.06  thf('13', plain,
% 9.84/10.06      (![X4 : $i, X5 : $i]:
% 9.84/10.06         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 9.84/10.06      inference('cnf', [status(esa)], [t12_xboole_1])).
% 9.84/10.06  thf('14', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 9.84/10.06      inference('sup-', [status(thm)], ['12', '13'])).
% 9.84/10.06  thf('15', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.84/10.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.84/10.06  thf('16', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 9.84/10.06      inference('demod', [status(thm)], ['14', '15'])).
% 9.84/10.06  thf('17', plain,
% 9.84/10.06      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12))
% 9.84/10.06           = (k3_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 9.84/10.06              (k2_xboole_0 @ X10 @ X12)))),
% 9.84/10.06      inference('cnf', [status(esa)], [t24_xboole_1])).
% 9.84/10.06  thf('18', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 9.84/10.06           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X0))),
% 9.84/10.06      inference('sup+', [status(thm)], ['16', '17'])).
% 9.84/10.06  thf('19', plain,
% 9.84/10.06      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 9.84/10.06      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 9.84/10.06  thf(t21_xboole_1, axiom,
% 9.84/10.06    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 9.84/10.06  thf('20', plain,
% 9.84/10.06      (![X6 : $i, X7 : $i]:
% 9.84/10.06         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 9.84/10.06      inference('cnf', [status(esa)], [t21_xboole_1])).
% 9.84/10.06  thf('21', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 9.84/10.06           = (X0))),
% 9.84/10.06      inference('demod', [status(thm)], ['18', '19', '20'])).
% 9.84/10.06  thf('22', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.84/10.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.84/10.06  thf('23', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]:
% 9.84/10.06         ((X0)
% 9.84/10.06           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 9.84/10.06      inference('demod', [status(thm)], ['11', '21', '22'])).
% 9.84/10.06  thf('24', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.84/10.06      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.84/10.06  thf(t40_xboole_1, axiom,
% 9.84/10.06    (![A:$i,B:$i]:
% 9.84/10.06     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 9.84/10.06  thf('25', plain,
% 9.84/10.06      (![X17 : $i, X18 : $i]:
% 9.84/10.06         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 9.84/10.06           = (k4_xboole_0 @ X17 @ X18))),
% 9.84/10.06      inference('cnf', [status(esa)], [t40_xboole_1])).
% 9.84/10.06  thf('26', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]:
% 9.84/10.06         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 9.84/10.06           = (k4_xboole_0 @ X0 @ X1))),
% 9.84/10.06      inference('sup+', [status(thm)], ['24', '25'])).
% 9.84/10.06  thf('27', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]:
% 9.84/10.06         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.84/10.06           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 9.84/10.06      inference('sup+', [status(thm)], ['23', '26'])).
% 9.84/10.06  thf(t22_xboole_1, axiom,
% 9.84/10.06    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 9.84/10.06  thf('28', plain,
% 9.84/10.06      (![X8 : $i, X9 : $i]:
% 9.84/10.06         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 9.84/10.06      inference('cnf', [status(esa)], [t22_xboole_1])).
% 9.84/10.06  thf(t41_xboole_1, axiom,
% 9.84/10.06    (![A:$i,B:$i,C:$i]:
% 9.84/10.06     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 9.84/10.06       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.84/10.06  thf('29', plain,
% 9.84/10.06      (![X19 : $i, X20 : $i, X21 : $i]:
% 9.84/10.06         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 9.84/10.06           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 9.84/10.06      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.84/10.06  thf('30', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.84/10.06         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 9.84/10.06           = (k4_xboole_0 @ X2 @ X0))),
% 9.84/10.06      inference('sup+', [status(thm)], ['28', '29'])).
% 9.84/10.06  thf('31', plain,
% 9.84/10.06      (![X0 : $i, X1 : $i]:
% 9.84/10.06         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 9.84/10.06           = (k4_xboole_0 @ X0 @ X1))),
% 9.84/10.06      inference('demod', [status(thm)], ['27', '30'])).
% 9.84/10.06  thf('32', plain,
% 9.84/10.06      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 9.84/10.06      inference('demod', [status(thm)], ['2', '31'])).
% 9.84/10.06  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 9.84/10.06  
% 9.84/10.06  % SZS output end Refutation
% 9.84/10.06  
% 9.84/10.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
