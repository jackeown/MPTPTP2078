%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BkPTtU6lgr

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:11 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 100 expanded)
%              Number of leaves         :   17 (  38 expanded)
%              Depth                    :   18
%              Number of atoms          :  491 ( 776 expanded)
%              Number of equality atoms :   58 (  93 expanded)
%              Maximal formula depth    :    9 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X14 ) @ X14 )
      = ( k4_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','21'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','43'])).

thf('45',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BkPTtU6lgr
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.88/2.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.88/2.07  % Solved by: fo/fo7.sh
% 1.88/2.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.88/2.07  % done 2031 iterations in 1.623s
% 1.88/2.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.88/2.07  % SZS output start Refutation
% 1.88/2.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.88/2.07  thf(sk_A_type, type, sk_A: $i).
% 1.88/2.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.88/2.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.88/2.07  thf(sk_B_type, type, sk_B: $i).
% 1.88/2.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.88/2.07  thf(t47_xboole_1, conjecture,
% 1.88/2.07    (![A:$i,B:$i]:
% 1.88/2.07     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.88/2.07  thf(zf_stmt_0, negated_conjecture,
% 1.88/2.07    (~( ![A:$i,B:$i]:
% 1.88/2.07        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 1.88/2.07          ( k4_xboole_0 @ A @ B ) ) )),
% 1.88/2.07    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 1.88/2.07  thf('0', plain,
% 1.88/2.07      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 1.88/2.07         != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.88/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.88/2.07  thf(commutativity_k3_xboole_0, axiom,
% 1.88/2.07    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.88/2.07  thf('1', plain,
% 1.88/2.07      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.88/2.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.88/2.07  thf('2', plain,
% 1.88/2.07      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.88/2.07         != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.88/2.07      inference('demod', [status(thm)], ['0', '1'])).
% 1.88/2.07  thf('3', plain,
% 1.88/2.07      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.88/2.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.88/2.07  thf(t39_xboole_1, axiom,
% 1.88/2.07    (![A:$i,B:$i]:
% 1.88/2.07     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.88/2.07  thf('4', plain,
% 1.88/2.07      (![X11 : $i, X12 : $i]:
% 1.88/2.07         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 1.88/2.07           = (k2_xboole_0 @ X11 @ X12))),
% 1.88/2.07      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.88/2.07  thf(idempotence_k3_xboole_0, axiom,
% 1.88/2.07    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.88/2.07  thf('5', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.88/2.07      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.88/2.07  thf(t23_xboole_1, axiom,
% 1.88/2.07    (![A:$i,B:$i,C:$i]:
% 1.88/2.07     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.88/2.07       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.88/2.07  thf('6', plain,
% 1.88/2.07      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.88/2.07         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 1.88/2.07           = (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)))),
% 1.88/2.07      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.88/2.07  thf('7', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.88/2.07           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 1.88/2.07      inference('sup+', [status(thm)], ['5', '6'])).
% 1.88/2.07  thf(commutativity_k2_xboole_0, axiom,
% 1.88/2.07    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.88/2.07  thf('8', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.88/2.07      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.88/2.07  thf(t22_xboole_1, axiom,
% 1.88/2.07    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.88/2.07  thf('9', plain,
% 1.88/2.07      (![X6 : $i, X7 : $i]:
% 1.88/2.07         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 1.88/2.07      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.88/2.07  thf('10', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.88/2.07      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.88/2.07  thf('11', plain,
% 1.88/2.07      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.88/2.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.88/2.07  thf('12', plain,
% 1.88/2.07      (![X6 : $i, X7 : $i]:
% 1.88/2.07         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 1.88/2.07      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.88/2.07  thf('13', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.88/2.07      inference('sup+', [status(thm)], ['11', '12'])).
% 1.88/2.07  thf('14', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.88/2.07      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.88/2.07  thf(t40_xboole_1, axiom,
% 1.88/2.07    (![A:$i,B:$i]:
% 1.88/2.07     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.88/2.07  thf('15', plain,
% 1.88/2.07      (![X13 : $i, X14 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X14) @ X14)
% 1.88/2.07           = (k4_xboole_0 @ X13 @ X14))),
% 1.88/2.07      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.88/2.07  thf('16', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.88/2.07           = (k4_xboole_0 @ X0 @ X1))),
% 1.88/2.07      inference('sup+', [status(thm)], ['14', '15'])).
% 1.88/2.07  thf('17', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ X0 @ X0)
% 1.88/2.07           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.88/2.07      inference('sup+', [status(thm)], ['13', '16'])).
% 1.88/2.07  thf('18', plain,
% 1.88/2.07      (![X6 : $i, X7 : $i]:
% 1.88/2.07         ((k2_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)) = (X6))),
% 1.88/2.07      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.88/2.07  thf(t46_xboole_1, axiom,
% 1.88/2.07    (![A:$i,B:$i]:
% 1.88/2.07     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.88/2.07  thf('19', plain,
% 1.88/2.07      (![X18 : $i, X19 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ X18 @ (k2_xboole_0 @ X18 @ X19)) = (k1_xboole_0))),
% 1.88/2.07      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.88/2.07  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.88/2.07      inference('sup+', [status(thm)], ['18', '19'])).
% 1.88/2.07  thf('21', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.88/2.07      inference('demod', [status(thm)], ['17', '20'])).
% 1.88/2.07  thf('22', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.88/2.07      inference('sup+', [status(thm)], ['10', '21'])).
% 1.88/2.07  thf(t41_xboole_1, axiom,
% 1.88/2.07    (![A:$i,B:$i,C:$i]:
% 1.88/2.07     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.88/2.07       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.88/2.07  thf('23', plain,
% 1.88/2.07      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 1.88/2.07           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 1.88/2.07      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.88/2.07  thf('24', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k1_xboole_0) = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.88/2.07      inference('demod', [status(thm)], ['22', '23'])).
% 1.88/2.07  thf('25', plain,
% 1.88/2.07      (![X11 : $i, X12 : $i]:
% 1.88/2.07         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 1.88/2.07           = (k2_xboole_0 @ X11 @ X12))),
% 1.88/2.07      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.88/2.07  thf('26', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 1.88/2.07           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.88/2.07      inference('sup+', [status(thm)], ['24', '25'])).
% 1.88/2.07  thf(t1_boole, axiom,
% 1.88/2.07    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.88/2.07  thf('27', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.88/2.07      inference('cnf', [status(esa)], [t1_boole])).
% 1.88/2.07  thf('28', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.88/2.07      inference('demod', [status(thm)], ['26', '27'])).
% 1.88/2.07  thf('29', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.88/2.07      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.88/2.07  thf('30', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.88/2.07           = (k4_xboole_0 @ X0 @ X1))),
% 1.88/2.07      inference('sup+', [status(thm)], ['28', '29'])).
% 1.88/2.07  thf('31', plain,
% 1.88/2.07      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.88/2.07      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.88/2.07  thf('32', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.88/2.07           = (k4_xboole_0 @ X0 @ X1))),
% 1.88/2.07      inference('demod', [status(thm)], ['30', '31'])).
% 1.88/2.07  thf('33', plain,
% 1.88/2.07      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.88/2.07         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 1.88/2.07           = (k2_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X10)))),
% 1.88/2.07      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.88/2.07  thf('34', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.88/2.07         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 1.88/2.07           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.88/2.07      inference('sup+', [status(thm)], ['32', '33'])).
% 1.88/2.07  thf('35', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 1.88/2.07           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.88/2.07      inference('sup+', [status(thm)], ['4', '34'])).
% 1.88/2.07  thf('36', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 1.88/2.07      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.88/2.07  thf('37', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((X0)
% 1.88/2.07           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 1.88/2.07      inference('demod', [status(thm)], ['35', '36'])).
% 1.88/2.07  thf('38', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.88/2.07           = (k4_xboole_0 @ X0 @ X1))),
% 1.88/2.07      inference('sup+', [status(thm)], ['14', '15'])).
% 1.88/2.07  thf('39', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.88/2.07           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.88/2.07      inference('sup+', [status(thm)], ['37', '38'])).
% 1.88/2.07  thf('40', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.88/2.07      inference('sup+', [status(thm)], ['11', '12'])).
% 1.88/2.07  thf('41', plain,
% 1.88/2.07      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 1.88/2.07           = (k4_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 1.88/2.07      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.88/2.07  thf('42', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.88/2.07           = (k4_xboole_0 @ X2 @ X0))),
% 1.88/2.07      inference('sup+', [status(thm)], ['40', '41'])).
% 1.88/2.07  thf('43', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.88/2.07           = (k4_xboole_0 @ X0 @ X1))),
% 1.88/2.07      inference('demod', [status(thm)], ['39', '42'])).
% 1.88/2.07  thf('44', plain,
% 1.88/2.07      (![X0 : $i, X1 : $i]:
% 1.88/2.07         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.88/2.07           = (k4_xboole_0 @ X0 @ X1))),
% 1.88/2.07      inference('sup+', [status(thm)], ['3', '43'])).
% 1.88/2.07  thf('45', plain,
% 1.88/2.07      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 1.88/2.07      inference('demod', [status(thm)], ['2', '44'])).
% 1.88/2.07  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 1.88/2.07  
% 1.88/2.07  % SZS output end Refutation
% 1.88/2.07  
% 1.92/2.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
