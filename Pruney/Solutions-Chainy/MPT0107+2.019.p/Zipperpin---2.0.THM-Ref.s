%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nU43UQHs7C

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:12 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   53 (  58 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  354 ( 389 expanded)
%              Number of equality atoms :   45 (  50 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X24: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['10','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nU43UQHs7C
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:31:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.05/1.29  % Solved by: fo/fo7.sh
% 1.05/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.29  % done 1128 iterations in 0.832s
% 1.05/1.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.05/1.29  % SZS output start Refutation
% 1.05/1.29  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.05/1.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.05/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.05/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.29  thf(t100_xboole_1, conjecture,
% 1.05/1.29    (![A:$i,B:$i]:
% 1.05/1.29     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.05/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.29    (~( ![A:$i,B:$i]:
% 1.05/1.29        ( ( k4_xboole_0 @ A @ B ) =
% 1.05/1.29          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 1.05/1.29    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 1.05/1.29  thf('0', plain,
% 1.05/1.29      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.05/1.29         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(commutativity_k3_xboole_0, axiom,
% 1.05/1.29    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.05/1.29  thf('1', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.29  thf('2', plain,
% 1.05/1.29      (((k4_xboole_0 @ sk_A @ sk_B)
% 1.05/1.29         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('demod', [status(thm)], ['0', '1'])).
% 1.05/1.29  thf('3', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.29  thf(t47_xboole_1, axiom,
% 1.05/1.29    (![A:$i,B:$i]:
% 1.05/1.29     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.05/1.29  thf('4', plain,
% 1.05/1.29      (![X17 : $i, X18 : $i]:
% 1.05/1.29         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 1.05/1.29           = (k4_xboole_0 @ X17 @ X18))),
% 1.05/1.29      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.05/1.29  thf(t98_xboole_1, axiom,
% 1.05/1.29    (![A:$i,B:$i]:
% 1.05/1.29     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.05/1.29  thf('5', plain,
% 1.05/1.29      (![X30 : $i, X31 : $i]:
% 1.05/1.29         ((k2_xboole_0 @ X30 @ X31)
% 1.05/1.29           = (k5_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30)))),
% 1.05/1.29      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.05/1.29  thf('6', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 1.05/1.29           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.29      inference('sup+', [status(thm)], ['4', '5'])).
% 1.05/1.29  thf(t48_xboole_1, axiom,
% 1.05/1.29    (![A:$i,B:$i]:
% 1.05/1.29     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.05/1.29  thf('7', plain,
% 1.05/1.29      (![X19 : $i, X20 : $i]:
% 1.05/1.29         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.05/1.29           = (k3_xboole_0 @ X19 @ X20))),
% 1.05/1.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.29  thf(t3_boole, axiom,
% 1.05/1.29    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.05/1.29  thf('8', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.05/1.29      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.29  thf(l36_xboole_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 1.05/1.29       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.05/1.29  thf('9', plain,
% 1.05/1.29      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.05/1.29         ((k4_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 1.05/1.29           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X4 @ X6)))),
% 1.05/1.29      inference('cnf', [status(esa)], [l36_xboole_1])).
% 1.05/1.29  thf('10', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ k1_xboole_0))
% 1.05/1.29           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.05/1.29      inference('sup+', [status(thm)], ['8', '9'])).
% 1.05/1.29  thf('11', plain,
% 1.05/1.29      (![X19 : $i, X20 : $i]:
% 1.05/1.29         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.05/1.29           = (k3_xboole_0 @ X19 @ X20))),
% 1.05/1.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.05/1.29  thf(t4_boole, axiom,
% 1.05/1.29    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.05/1.29  thf('12', plain,
% 1.05/1.29      (![X24 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X24) = (k1_xboole_0))),
% 1.05/1.29      inference('cnf', [status(esa)], [t4_boole])).
% 1.05/1.29  thf('13', plain,
% 1.05/1.29      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.05/1.29      inference('sup+', [status(thm)], ['11', '12'])).
% 1.05/1.29  thf('14', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.05/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.05/1.29  thf('15', plain,
% 1.05/1.29      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.05/1.29      inference('sup+', [status(thm)], ['13', '14'])).
% 1.05/1.29  thf('16', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 1.05/1.29      inference('cnf', [status(esa)], [t3_boole])).
% 1.05/1.29  thf('17', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.05/1.29      inference('demod', [status(thm)], ['10', '15', '16'])).
% 1.05/1.29  thf('18', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((X1) = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 1.05/1.29      inference('sup+', [status(thm)], ['7', '17'])).
% 1.05/1.29  thf('19', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((X1)
% 1.05/1.29           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.05/1.29      inference('demod', [status(thm)], ['6', '18'])).
% 1.05/1.29  thf('20', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((X0)
% 1.05/1.29           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.05/1.29      inference('sup+', [status(thm)], ['3', '19'])).
% 1.05/1.29  thf(t92_xboole_1, axiom,
% 1.05/1.29    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.05/1.29  thf('21', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 1.05/1.29      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.05/1.29  thf(t91_xboole_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.05/1.29       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.05/1.29  thf('22', plain,
% 1.05/1.29      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.05/1.29         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 1.05/1.29           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 1.05/1.29      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.05/1.29  thf('23', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.05/1.29           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.29      inference('sup+', [status(thm)], ['21', '22'])).
% 1.05/1.29  thf(commutativity_k5_xboole_0, axiom,
% 1.05/1.29    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.05/1.29  thf('24', plain,
% 1.05/1.29      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.05/1.29      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.05/1.29  thf(t5_boole, axiom,
% 1.05/1.29    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.05/1.29  thf('25', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 1.05/1.29      inference('cnf', [status(esa)], [t5_boole])).
% 1.05/1.29  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.05/1.29      inference('sup+', [status(thm)], ['24', '25'])).
% 1.05/1.29  thf('27', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.05/1.29      inference('demod', [status(thm)], ['23', '26'])).
% 1.05/1.29  thf('28', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((k4_xboole_0 @ X0 @ X1)
% 1.05/1.29           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.05/1.29      inference('sup+', [status(thm)], ['20', '27'])).
% 1.05/1.29  thf('29', plain,
% 1.05/1.29      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.05/1.29      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.05/1.29  thf('30', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((k4_xboole_0 @ X0 @ X1)
% 1.05/1.29           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.05/1.29      inference('demod', [status(thm)], ['28', '29'])).
% 1.05/1.29  thf('31', plain,
% 1.05/1.29      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.05/1.29      inference('demod', [status(thm)], ['2', '30'])).
% 1.05/1.29  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 1.05/1.29  
% 1.05/1.29  % SZS output end Refutation
% 1.05/1.29  
% 1.05/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
