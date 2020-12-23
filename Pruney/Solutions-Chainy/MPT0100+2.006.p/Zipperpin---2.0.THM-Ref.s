%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0KRLb91xq1

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:53 EST 2020

% Result     : Theorem 4.09s
% Output     : Refutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   15 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  314 ( 392 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k2_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k2_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','23','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0KRLb91xq1
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.09/4.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.09/4.28  % Solved by: fo/fo7.sh
% 4.09/4.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.09/4.28  % done 2977 iterations in 3.829s
% 4.09/4.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.09/4.28  % SZS output start Refutation
% 4.09/4.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.09/4.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.09/4.28  thf(sk_A_type, type, sk_A: $i).
% 4.09/4.28  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.09/4.28  thf(sk_B_type, type, sk_B: $i).
% 4.09/4.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.09/4.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.09/4.28  thf(t93_xboole_1, conjecture,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( ( k2_xboole_0 @ A @ B ) =
% 4.09/4.28       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.09/4.28  thf(zf_stmt_0, negated_conjecture,
% 4.09/4.28    (~( ![A:$i,B:$i]:
% 4.09/4.28        ( ( k2_xboole_0 @ A @ B ) =
% 4.09/4.28          ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 4.09/4.28    inference('cnf.neg', [status(esa)], [t93_xboole_1])).
% 4.09/4.28  thf('0', plain,
% 4.09/4.28      (((k2_xboole_0 @ sk_A @ sk_B)
% 4.09/4.28         != (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 4.09/4.28             (k3_xboole_0 @ sk_A @ sk_B)))),
% 4.09/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.28  thf(d6_xboole_0, axiom,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( ( k5_xboole_0 @ A @ B ) =
% 4.09/4.28       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 4.09/4.28  thf('1', plain,
% 4.09/4.28      (![X4 : $i, X5 : $i]:
% 4.09/4.28         ((k5_xboole_0 @ X4 @ X5)
% 4.09/4.28           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 4.09/4.28      inference('cnf', [status(esa)], [d6_xboole_0])).
% 4.09/4.28  thf(commutativity_k2_xboole_0, axiom,
% 4.09/4.28    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.09/4.28  thf('2', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.09/4.28  thf('3', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 4.09/4.28           = (k5_xboole_0 @ X1 @ X0))),
% 4.09/4.28      inference('sup+', [status(thm)], ['1', '2'])).
% 4.09/4.28  thf(commutativity_k3_xboole_0, axiom,
% 4.09/4.28    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.09/4.28  thf('4', plain,
% 4.09/4.28      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.09/4.28  thf(t51_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 4.09/4.28       ( A ) ))).
% 4.09/4.28  thf('5', plain,
% 4.09/4.28      (![X18 : $i, X19 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 4.09/4.28           = (X18))),
% 4.09/4.28      inference('cnf', [status(esa)], [t51_xboole_1])).
% 4.09/4.28  thf('6', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 4.09/4.28           = (X0))),
% 4.09/4.28      inference('sup+', [status(thm)], ['4', '5'])).
% 4.09/4.28  thf(t4_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i,C:$i]:
% 4.09/4.28     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 4.09/4.28       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.09/4.28  thf('7', plain,
% 4.09/4.28      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X17)
% 4.09/4.28           = (k2_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 4.09/4.28      inference('cnf', [status(esa)], [t4_xboole_1])).
% 4.09/4.28  thf('8', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.09/4.28  thf('9', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 4.09/4.28           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.09/4.28      inference('sup+', [status(thm)], ['7', '8'])).
% 4.09/4.28  thf('10', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ X1 @ X0)
% 4.09/4.28           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ 
% 4.09/4.28              (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)))),
% 4.09/4.28      inference('sup+', [status(thm)], ['6', '9'])).
% 4.09/4.28  thf('11', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 4.09/4.28           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X0)))),
% 4.09/4.28      inference('sup+', [status(thm)], ['3', '10'])).
% 4.09/4.28  thf('12', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.09/4.28  thf('13', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 4.09/4.28           = (X0))),
% 4.09/4.28      inference('sup+', [status(thm)], ['4', '5'])).
% 4.09/4.28  thf(t17_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 4.09/4.28  thf('14', plain,
% 4.09/4.28      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 4.09/4.28      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.09/4.28  thf(t12_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 4.09/4.28  thf('15', plain,
% 4.09/4.28      (![X6 : $i, X7 : $i]:
% 4.09/4.28         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 4.09/4.28      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.09/4.28  thf('16', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 4.09/4.28      inference('sup-', [status(thm)], ['14', '15'])).
% 4.09/4.28  thf('17', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.09/4.28  thf('18', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 4.09/4.28      inference('demod', [status(thm)], ['16', '17'])).
% 4.09/4.28  thf('19', plain,
% 4.09/4.28      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X17)
% 4.09/4.28           = (k2_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 4.09/4.28      inference('cnf', [status(esa)], [t4_xboole_1])).
% 4.09/4.28  thf('20', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ X0 @ X1)
% 4.09/4.28           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1)))),
% 4.09/4.28      inference('sup+', [status(thm)], ['18', '19'])).
% 4.09/4.28  thf('21', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1))
% 4.09/4.28           = (k2_xboole_0 @ X1 @ X0))),
% 4.09/4.28      inference('sup+', [status(thm)], ['13', '20'])).
% 4.09/4.28  thf('22', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.09/4.28  thf('23', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((k2_xboole_0 @ X0 @ X1)
% 4.09/4.28           = (k2_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 4.09/4.28      inference('demod', [status(thm)], ['11', '12', '21', '22'])).
% 4.09/4.28  thf('24', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.09/4.28  thf('25', plain,
% 4.09/4.28      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 4.09/4.28      inference('demod', [status(thm)], ['0', '23', '24'])).
% 4.09/4.28  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 4.09/4.28  
% 4.09/4.28  % SZS output end Refutation
% 4.09/4.28  
% 4.09/4.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
