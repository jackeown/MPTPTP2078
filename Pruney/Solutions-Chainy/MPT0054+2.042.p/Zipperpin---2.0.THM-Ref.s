%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J17suWerRf

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:13 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   62 (  85 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   18
%              Number of atoms          :  464 ( 635 expanded)
%              Number of equality atoms :   55 (  78 expanded)
%              Maximal formula depth    :    9 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X14 @ X15 ) @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','40'])).

thf('42',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J17suWerRf
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:39:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 1.82/2.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.82/2.01  % Solved by: fo/fo7.sh
% 1.82/2.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.82/2.01  % done 2057 iterations in 1.555s
% 1.82/2.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.82/2.01  % SZS output start Refutation
% 1.82/2.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.82/2.01  thf(sk_A_type, type, sk_A: $i).
% 1.82/2.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.82/2.01  thf(sk_B_type, type, sk_B: $i).
% 1.82/2.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.82/2.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.82/2.01  thf(t47_xboole_1, conjecture,
% 1.82/2.01    (![A:$i,B:$i]:
% 1.82/2.01     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.82/2.01  thf(zf_stmt_0, negated_conjecture,
% 1.82/2.01    (~( ![A:$i,B:$i]:
% 1.82/2.01        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 1.82/2.01          ( k4_xboole_0 @ A @ B ) ) )),
% 1.82/2.01    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 1.82/2.01  thf('0', plain,
% 1.82/2.01      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 1.82/2.01         != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.82/2.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.01  thf(commutativity_k3_xboole_0, axiom,
% 1.82/2.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.82/2.01  thf('1', plain,
% 1.82/2.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.82/2.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.82/2.01  thf('2', plain,
% 1.82/2.01      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.82/2.01         != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.82/2.01      inference('demod', [status(thm)], ['0', '1'])).
% 1.82/2.01  thf('3', plain,
% 1.82/2.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.82/2.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.82/2.01  thf(t39_xboole_1, axiom,
% 1.82/2.01    (![A:$i,B:$i]:
% 1.82/2.01     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.82/2.01  thf('4', plain,
% 1.82/2.01      (![X12 : $i, X13 : $i]:
% 1.82/2.01         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 1.82/2.01           = (k2_xboole_0 @ X12 @ X13))),
% 1.82/2.01      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.82/2.01  thf(commutativity_k2_xboole_0, axiom,
% 1.82/2.01    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.82/2.01  thf('5', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.82/2.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.82/2.01  thf(t21_xboole_1, axiom,
% 1.82/2.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.82/2.01  thf('6', plain,
% 1.82/2.01      (![X5 : $i, X6 : $i]:
% 1.82/2.01         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 1.82/2.01      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.82/2.01  thf('7', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.82/2.01      inference('sup+', [status(thm)], ['5', '6'])).
% 1.82/2.01  thf('8', plain,
% 1.82/2.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.82/2.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.82/2.01  thf(t22_xboole_1, axiom,
% 1.82/2.01    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.82/2.01  thf('9', plain,
% 1.82/2.01      (![X7 : $i, X8 : $i]:
% 1.82/2.01         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 1.82/2.01      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.82/2.01  thf('10', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.82/2.01      inference('sup+', [status(thm)], ['8', '9'])).
% 1.82/2.01  thf('11', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.82/2.01      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.82/2.01  thf(t40_xboole_1, axiom,
% 1.82/2.01    (![A:$i,B:$i]:
% 1.82/2.01     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.82/2.01  thf('12', plain,
% 1.82/2.01      (![X14 : $i, X15 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ (k2_xboole_0 @ X14 @ X15) @ X15)
% 1.82/2.01           = (k4_xboole_0 @ X14 @ X15))),
% 1.82/2.01      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.82/2.01  thf('13', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.82/2.01           = (k4_xboole_0 @ X0 @ X1))),
% 1.82/2.01      inference('sup+', [status(thm)], ['11', '12'])).
% 1.82/2.01  thf('14', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ X0 @ X0)
% 1.82/2.01           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.82/2.01      inference('sup+', [status(thm)], ['10', '13'])).
% 1.82/2.01  thf('15', plain,
% 1.82/2.01      (![X7 : $i, X8 : $i]:
% 1.82/2.01         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 1.82/2.01      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.82/2.01  thf(t46_xboole_1, axiom,
% 1.82/2.01    (![A:$i,B:$i]:
% 1.82/2.01     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.82/2.01  thf('16', plain,
% 1.82/2.01      (![X19 : $i, X20 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 1.82/2.01      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.82/2.01  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.82/2.01      inference('sup+', [status(thm)], ['15', '16'])).
% 1.82/2.01  thf('18', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.82/2.01      inference('demod', [status(thm)], ['14', '17'])).
% 1.82/2.01  thf('19', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.82/2.01      inference('sup+', [status(thm)], ['7', '18'])).
% 1.82/2.01  thf(t41_xboole_1, axiom,
% 1.82/2.01    (![A:$i,B:$i,C:$i]:
% 1.82/2.01     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.82/2.01       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.82/2.01  thf('20', plain,
% 1.82/2.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 1.82/2.01           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 1.82/2.01      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.82/2.01  thf('21', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.82/2.01      inference('demod', [status(thm)], ['19', '20'])).
% 1.82/2.01  thf('22', plain,
% 1.82/2.01      (![X12 : $i, X13 : $i]:
% 1.82/2.01         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 1.82/2.01           = (k2_xboole_0 @ X12 @ X13))),
% 1.82/2.01      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.82/2.01  thf('23', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 1.82/2.01           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.82/2.01      inference('sup+', [status(thm)], ['21', '22'])).
% 1.82/2.01  thf(t1_boole, axiom,
% 1.82/2.01    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.82/2.01  thf('24', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 1.82/2.01      inference('cnf', [status(esa)], [t1_boole])).
% 1.82/2.01  thf('25', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.82/2.01      inference('demod', [status(thm)], ['23', '24'])).
% 1.82/2.01  thf('26', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.82/2.01      inference('sup+', [status(thm)], ['5', '6'])).
% 1.82/2.01  thf('27', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.82/2.01           = (k4_xboole_0 @ X0 @ X1))),
% 1.82/2.01      inference('sup+', [status(thm)], ['25', '26'])).
% 1.82/2.01  thf('28', plain,
% 1.82/2.01      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.82/2.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.82/2.01  thf('29', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.82/2.01           = (k4_xboole_0 @ X0 @ X1))),
% 1.82/2.01      inference('demod', [status(thm)], ['27', '28'])).
% 1.82/2.01  thf(t23_xboole_1, axiom,
% 1.82/2.01    (![A:$i,B:$i,C:$i]:
% 1.82/2.01     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.82/2.01       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.82/2.01  thf('30', plain,
% 1.82/2.01      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.82/2.01         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 1.82/2.01           = (k2_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 1.82/2.01      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.82/2.01  thf('31', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.01         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.82/2.01           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.82/2.01      inference('sup+', [status(thm)], ['29', '30'])).
% 1.82/2.01  thf('32', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.82/2.01           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.82/2.01      inference('sup+', [status(thm)], ['4', '31'])).
% 1.82/2.01  thf('33', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.82/2.01      inference('sup+', [status(thm)], ['5', '6'])).
% 1.82/2.01  thf('34', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((X0)
% 1.82/2.01           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.82/2.01      inference('demod', [status(thm)], ['32', '33'])).
% 1.82/2.01  thf('35', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.82/2.01           = (k4_xboole_0 @ X0 @ X1))),
% 1.82/2.01      inference('sup+', [status(thm)], ['11', '12'])).
% 1.82/2.01  thf('36', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.82/2.01           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.82/2.01      inference('sup+', [status(thm)], ['34', '35'])).
% 1.82/2.01  thf('37', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.82/2.01      inference('sup+', [status(thm)], ['8', '9'])).
% 1.82/2.01  thf('38', plain,
% 1.82/2.01      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 1.82/2.01           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 1.82/2.01      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.82/2.01  thf('39', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.82/2.01           = (k4_xboole_0 @ X2 @ X0))),
% 1.82/2.01      inference('sup+', [status(thm)], ['37', '38'])).
% 1.82/2.01  thf('40', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.82/2.01           = (k4_xboole_0 @ X0 @ X1))),
% 1.82/2.01      inference('demod', [status(thm)], ['36', '39'])).
% 1.82/2.01  thf('41', plain,
% 1.82/2.01      (![X0 : $i, X1 : $i]:
% 1.82/2.01         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.82/2.01           = (k4_xboole_0 @ X0 @ X1))),
% 1.82/2.01      inference('sup+', [status(thm)], ['3', '40'])).
% 1.82/2.01  thf('42', plain,
% 1.82/2.01      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.82/2.01      inference('demod', [status(thm)], ['2', '41'])).
% 1.82/2.01  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 1.82/2.01  
% 1.82/2.01  % SZS output end Refutation
% 1.82/2.01  
% 1.82/2.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
