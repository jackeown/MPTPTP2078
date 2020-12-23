%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0WwC6jY3Oh

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:02 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  296 ( 373 expanded)
%              Number of equality atoms :   33 (  44 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t95_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('2',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X6 ) @ X6 )
      = ( k4_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0WwC6jY3Oh
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 240 iterations in 0.150s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.60  thf(t95_xboole_1, conjecture,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k3_xboole_0 @ A @ B ) =
% 0.39/0.60       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i]:
% 0.39/0.60        ( ( k3_xboole_0 @ A @ B ) =
% 0.39/0.60          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.39/0.60         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.39/0.60             (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(t91_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.60       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.60         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.39/0.60           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.39/0.60         != (k5_xboole_0 @ sk_A @ 
% 0.39/0.60             (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.39/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.60  thf('3', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.60  thf(t46_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      (![X10 : $i, X11 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.39/0.60      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['3', '4'])).
% 0.39/0.60  thf(d6_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k5_xboole_0 @ A @ B ) =
% 0.39/0.60       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         ((k5_xboole_0 @ X2 @ X3)
% 0.39/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.39/0.60      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.39/0.60           = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.39/0.60              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.39/0.60  thf(t40_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      (![X5 : $i, X6 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ (k2_xboole_0 @ X5 @ X6) @ X6)
% 0.39/0.60           = (k4_xboole_0 @ X5 @ X6))),
% 0.39/0.60      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.60  thf('9', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.60  thf(t1_boole, axiom,
% 0.39/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.60  thf('10', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.39/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.60  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.39/0.60           = (k4_xboole_0 @ X1 @ X0))),
% 0.39/0.60      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.39/0.60         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('demod', [status(thm)], ['2', '12'])).
% 0.39/0.60  thf(t48_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (![X12 : $i, X13 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.39/0.60           = (k3_xboole_0 @ X12 @ X13))),
% 0.39/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.60  thf('15', plain,
% 0.39/0.60      (![X2 : $i, X3 : $i]:
% 0.39/0.60         ((k5_xboole_0 @ X2 @ X3)
% 0.39/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.39/0.60      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.39/0.60  thf('16', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.39/0.60           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.39/0.60              (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)))),
% 0.39/0.60      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.60  thf(t41_xboole_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.60       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.60  thf('17', plain,
% 0.39/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.39/0.60           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.60  thf('18', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['3', '4'])).
% 0.39/0.60  thf('19', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.60      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.60  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.60      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.60  thf('21', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i]:
% 0.39/0.60         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.39/0.60           = (k3_xboole_0 @ X1 @ X0))),
% 0.39/0.60      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.39/0.60  thf('22', plain,
% 0.39/0.60      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.39/0.60      inference('demod', [status(thm)], ['13', '21'])).
% 0.39/0.60  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
