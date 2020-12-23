%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SDGKMPzK7X

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:22 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   56 (  62 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  362 ( 405 expanded)
%              Number of equality atoms :   42 (  48 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t70_enumset1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_enumset1 @ A @ A @ B )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t70_enumset1])).

thf('0',plain,(
    ( k1_enumset1 @ sk_A @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k1_tarski @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k5_xboole_0 @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('25',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k2_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','27'])).

thf('29',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SDGKMPzK7X
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 488 iterations in 0.252s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.53/0.71  thf(t70_enumset1, conjecture,
% 0.53/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t70_enumset1])).
% 0.53/0.71  thf('0', plain,
% 0.53/0.71      (((k1_enumset1 @ sk_A @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t69_enumset1, axiom,
% 0.53/0.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.53/0.71  thf('1', plain, (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.53/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.71  thf(t41_enumset1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( k2_tarski @ A @ B ) =
% 0.53/0.71       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      (![X17 : $i, X18 : $i]:
% 0.53/0.71         ((k2_tarski @ X17 @ X18)
% 0.53/0.71           = (k2_xboole_0 @ (k1_tarski @ X17) @ (k1_tarski @ X18)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.53/0.71  thf('3', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k2_tarski @ X0 @ X1)
% 0.53/0.71           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['1', '2'])).
% 0.53/0.71  thf(t7_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.53/0.71  thf('4', plain,
% 0.53/0.71      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.53/0.71      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.53/0.71  thf(t28_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.71  thf('5', plain,
% 0.53/0.71      (![X6 : $i, X7 : $i]:
% 0.53/0.71         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.53/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.53/0.71  thf('6', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.53/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.53/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.53/0.71  thf('7', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.53/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.53/0.71  thf(t100_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.53/0.71  thf('8', plain,
% 0.53/0.71      (![X4 : $i, X5 : $i]:
% 0.53/0.71         ((k4_xboole_0 @ X4 @ X5)
% 0.53/0.71           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.53/0.71  thf('9', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k4_xboole_0 @ X0 @ X1)
% 0.53/0.71           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['7', '8'])).
% 0.53/0.71  thf('10', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.53/0.71           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.53/0.71      inference('sup+', [status(thm)], ['6', '9'])).
% 0.53/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.53/0.71  thf('11', plain,
% 0.53/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.53/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.71  thf('12', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.53/0.71           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.53/0.71      inference('demod', [status(thm)], ['10', '11'])).
% 0.53/0.71  thf(t92_xboole_1, axiom,
% 0.53/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.53/0.71  thf('13', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ X14) = (k1_xboole_0))),
% 0.53/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.53/0.71  thf(t91_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.53/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.53/0.71  thf('14', plain,
% 0.53/0.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.53/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ X13)
% 0.53/0.71           = (k5_xboole_0 @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.53/0.71  thf('15', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.53/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['13', '14'])).
% 0.53/0.71  thf('16', plain,
% 0.53/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.53/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.53/0.71  thf(t5_boole, axiom,
% 0.53/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.53/0.71  thf('17', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.53/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.53/0.71  thf('18', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.53/0.71      inference('sup+', [status(thm)], ['16', '17'])).
% 0.53/0.71  thf('19', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.53/0.71      inference('demod', [status(thm)], ['15', '18'])).
% 0.53/0.71  thf('20', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.53/0.71           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['12', '19'])).
% 0.53/0.71  thf(t98_xboole_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.53/0.71  thf('21', plain,
% 0.53/0.71      (![X15 : $i, X16 : $i]:
% 0.53/0.71         ((k2_xboole_0 @ X15 @ X16)
% 0.53/0.71           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.53/0.71  thf('22', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.53/0.71           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.53/0.71      inference('demod', [status(thm)], ['20', '21'])).
% 0.53/0.71  thf('23', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 0.53/0.71           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['3', '22'])).
% 0.53/0.71  thf('24', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k2_tarski @ X0 @ X1)
% 0.53/0.71           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['1', '2'])).
% 0.53/0.71  thf('25', plain,
% 0.53/0.71      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 0.53/0.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.71  thf(t42_enumset1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.53/0.71       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.53/0.71  thf('26', plain,
% 0.53/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.71         ((k1_enumset1 @ X19 @ X20 @ X21)
% 0.53/0.71           = (k2_xboole_0 @ (k1_tarski @ X19) @ (k2_tarski @ X20 @ X21)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.53/0.71  thf('27', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.71         ((k1_enumset1 @ X0 @ X2 @ X1)
% 0.53/0.71           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['25', '26'])).
% 0.53/0.71  thf('28', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]:
% 0.53/0.71         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 0.53/0.71      inference('demod', [status(thm)], ['23', '24', '27'])).
% 0.53/0.71  thf('29', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.53/0.71      inference('demod', [status(thm)], ['0', '28'])).
% 0.53/0.71  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.53/0.71  
% 0.53/0.71  % SZS output end Refutation
% 0.53/0.71  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
