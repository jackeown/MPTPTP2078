%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3TmLi9ewUI

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:05 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   59 (  87 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  407 ( 601 expanded)
%              Number of equality atoms :   52 (  80 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t98_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ A @ B )
        = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t98_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
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
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8','9','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('35',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    ( k2_xboole_0 @ sk_B @ sk_A )
 != ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','40','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3TmLi9ewUI
% 0.16/0.37  % Computer   : n011.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 11:09:12 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 178 iterations in 0.095s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(t98_xboole_1, conjecture,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i]:
% 0.41/0.58        ( ( k2_xboole_0 @ A @ B ) =
% 0.41/0.58          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.41/0.58  thf('0', plain,
% 0.41/0.58      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.41/0.58         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(commutativity_k2_xboole_0, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      (((k2_xboole_0 @ sk_B @ sk_A)
% 0.41/0.58         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.41/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.58  thf(t40_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.41/0.58  thf('4', plain,
% 0.41/0.58      (![X6 : $i, X7 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ X7)
% 0.41/0.58           = (k4_xboole_0 @ X6 @ X7))),
% 0.41/0.58      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.41/0.58           = (k4_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.58  thf(d6_xboole_0, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k5_xboole_0 @ A @ B ) =
% 0.41/0.58       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ X2 @ X3)
% 0.41/0.58           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.41/0.58  thf('7', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.41/0.58           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.41/0.58              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 0.41/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.41/0.58  thf(t46_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      (![X11 : $i, X12 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.58  thf(t1_boole, axiom,
% 0.41/0.58    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.58  thf('11', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.41/0.58      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.58  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.41/0.58           = (k4_xboole_0 @ X1 @ X0))),
% 0.41/0.58      inference('demod', [status(thm)], ['7', '8', '9', '12'])).
% 0.41/0.58  thf('14', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ X2 @ X3)
% 0.41/0.58           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.41/0.58  thf('15', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.58  thf('16', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 0.41/0.58           = (k5_xboole_0 @ X1 @ X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['14', '15'])).
% 0.41/0.58  thf('17', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ X2 @ X3)
% 0.41/0.58           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.41/0.58  thf('18', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['16', '17'])).
% 0.41/0.58  thf('19', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.41/0.58           = (k4_xboole_0 @ X1 @ X0))),
% 0.41/0.58      inference('demod', [status(thm)], ['13', '18'])).
% 0.41/0.58  thf('20', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.41/0.58      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.58  thf('21', plain,
% 0.41/0.58      (![X11 : $i, X12 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.41/0.58  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['20', '21'])).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ X2 @ X3)
% 0.41/0.58           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.41/0.58  thf('24', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ X0 @ X0)
% 0.41/0.58           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.41/0.58  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['20', '21'])).
% 0.41/0.58  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.58      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.41/0.58  thf(t91_xboole_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.58       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.41/0.58           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.41/0.58      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.41/0.58  thf('29', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.58           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['27', '28'])).
% 0.41/0.58  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('31', plain,
% 0.41/0.58      (![X11 : $i, X12 : $i]:
% 0.41/0.58         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 0.41/0.58      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.41/0.58  thf('32', plain,
% 0.41/0.58      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['30', '31'])).
% 0.41/0.58  thf('33', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ X2 @ X3)
% 0.41/0.58           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.41/0.58      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.41/0.58  thf('34', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.41/0.58           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['32', '33'])).
% 0.41/0.58  thf(t3_boole, axiom,
% 0.41/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.58  thf('35', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.41/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.41/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.41/0.58  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.41/0.58  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.58      inference('sup+', [status(thm)], ['36', '37'])).
% 0.41/0.58  thf('39', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.41/0.58      inference('demod', [status(thm)], ['29', '38'])).
% 0.41/0.58  thf('40', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         ((k2_xboole_0 @ X0 @ X1)
% 0.41/0.58           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.41/0.58      inference('sup+', [status(thm)], ['19', '39'])).
% 0.41/0.58  thf('41', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.58  thf('42', plain,
% 0.41/0.58      (((k2_xboole_0 @ sk_B @ sk_A) != (k2_xboole_0 @ sk_B @ sk_A))),
% 0.41/0.58      inference('demod', [status(thm)], ['2', '40', '41'])).
% 0.41/0.58  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
