%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8YKhYVg9o5

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:11 EST 2020

% Result     : Theorem 28.91s
% Output     : Refutation 28.91s
% Verified   : 
% Statistics : Number of formulae       :   65 (  80 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :  478 ( 593 expanded)
%              Number of equality atoms :   55 (  70 expanded)
%              Maximal formula depth    :    9 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
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

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','41'])).

thf('43',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8YKhYVg9o5
% 0.14/0.38  % Computer   : n019.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 14:03:08 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 28.91/29.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 28.91/29.14  % Solved by: fo/fo7.sh
% 28.91/29.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 28.91/29.14  % done 9491 iterations in 28.646s
% 28.91/29.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 28.91/29.14  % SZS output start Refutation
% 28.91/29.14  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 28.91/29.14  thf(sk_A_type, type, sk_A: $i).
% 28.91/29.14  thf(sk_B_type, type, sk_B: $i).
% 28.91/29.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 28.91/29.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 28.91/29.14  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 28.91/29.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 28.91/29.14  thf(t47_xboole_1, conjecture,
% 28.91/29.14    (![A:$i,B:$i]:
% 28.91/29.14     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 28.91/29.14  thf(zf_stmt_0, negated_conjecture,
% 28.91/29.14    (~( ![A:$i,B:$i]:
% 28.91/29.14        ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) =
% 28.91/29.14          ( k4_xboole_0 @ A @ B ) ) )),
% 28.91/29.14    inference('cnf.neg', [status(esa)], [t47_xboole_1])).
% 28.91/29.14  thf('0', plain,
% 28.91/29.14      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))
% 28.91/29.14         != (k4_xboole_0 @ sk_A @ sk_B))),
% 28.91/29.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.91/29.14  thf(commutativity_k3_xboole_0, axiom,
% 28.91/29.14    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 28.91/29.14  thf('1', plain,
% 28.91/29.14      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 28.91/29.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 28.91/29.14  thf('2', plain,
% 28.91/29.14      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))
% 28.91/29.14         != (k4_xboole_0 @ sk_A @ sk_B))),
% 28.91/29.14      inference('demod', [status(thm)], ['0', '1'])).
% 28.91/29.14  thf('3', plain,
% 28.91/29.14      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 28.91/29.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 28.91/29.14  thf(t39_xboole_1, axiom,
% 28.91/29.14    (![A:$i,B:$i]:
% 28.91/29.14     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 28.91/29.14  thf('4', plain,
% 28.91/29.14      (![X21 : $i, X22 : $i]:
% 28.91/29.14         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 28.91/29.14           = (k2_xboole_0 @ X21 @ X22))),
% 28.91/29.14      inference('cnf', [status(esa)], [t39_xboole_1])).
% 28.91/29.14  thf(commutativity_k2_xboole_0, axiom,
% 28.91/29.14    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 28.91/29.14  thf('5', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 28.91/29.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 28.91/29.14  thf(t1_boole, axiom,
% 28.91/29.14    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 28.91/29.14  thf('6', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 28.91/29.14      inference('cnf', [status(esa)], [t1_boole])).
% 28.91/29.14  thf('7', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 28.91/29.14      inference('sup+', [status(thm)], ['5', '6'])).
% 28.91/29.14  thf(t36_xboole_1, axiom,
% 28.91/29.14    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 28.91/29.14  thf('8', plain,
% 28.91/29.14      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 28.91/29.14      inference('cnf', [status(esa)], [t36_xboole_1])).
% 28.91/29.14  thf(l32_xboole_1, axiom,
% 28.91/29.14    (![A:$i,B:$i]:
% 28.91/29.14     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 28.91/29.14  thf('9', plain,
% 28.91/29.14      (![X5 : $i, X7 : $i]:
% 28.91/29.14         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 28.91/29.14      inference('cnf', [status(esa)], [l32_xboole_1])).
% 28.91/29.14  thf('10', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 28.91/29.14      inference('sup-', [status(thm)], ['8', '9'])).
% 28.91/29.14  thf(t41_xboole_1, axiom,
% 28.91/29.14    (![A:$i,B:$i,C:$i]:
% 28.91/29.14     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 28.91/29.14       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 28.91/29.14  thf('11', plain,
% 28.91/29.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 28.91/29.14           = (k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 28.91/29.14      inference('cnf', [status(esa)], [t41_xboole_1])).
% 28.91/29.14  thf('12', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 28.91/29.14      inference('demod', [status(thm)], ['10', '11'])).
% 28.91/29.14  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 28.91/29.14      inference('sup+', [status(thm)], ['7', '12'])).
% 28.91/29.14  thf('14', plain,
% 28.91/29.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 28.91/29.14           = (k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 28.91/29.14      inference('cnf', [status(esa)], [t41_xboole_1])).
% 28.91/29.14  thf('15', plain,
% 28.91/29.14      (![X21 : $i, X22 : $i]:
% 28.91/29.14         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 28.91/29.14           = (k2_xboole_0 @ X21 @ X22))),
% 28.91/29.14      inference('cnf', [status(esa)], [t39_xboole_1])).
% 28.91/29.14  thf('16', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.91/29.14         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 28.91/29.14           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 28.91/29.14      inference('sup+', [status(thm)], ['14', '15'])).
% 28.91/29.14  thf('17', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 28.91/29.14           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 28.91/29.14      inference('sup+', [status(thm)], ['13', '16'])).
% 28.91/29.14  thf('18', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 28.91/29.14      inference('cnf', [status(esa)], [t1_boole])).
% 28.91/29.14  thf('19', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 28.91/29.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 28.91/29.14  thf(t40_xboole_1, axiom,
% 28.91/29.14    (![A:$i,B:$i]:
% 28.91/29.14     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 28.91/29.14  thf('20', plain,
% 28.91/29.14      (![X23 : $i, X24 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 28.91/29.14           = (k4_xboole_0 @ X23 @ X24))),
% 28.91/29.14      inference('cnf', [status(esa)], [t40_xboole_1])).
% 28.91/29.14  thf('21', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 28.91/29.14           = (k4_xboole_0 @ X0 @ X1))),
% 28.91/29.14      inference('sup+', [status(thm)], ['19', '20'])).
% 28.91/29.14  thf('22', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 28.91/29.14      inference('demod', [status(thm)], ['17', '18', '21'])).
% 28.91/29.14  thf('23', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 28.91/29.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 28.91/29.14  thf(t21_xboole_1, axiom,
% 28.91/29.14    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 28.91/29.14  thf('24', plain,
% 28.91/29.14      (![X12 : $i, X13 : $i]:
% 28.91/29.14         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 28.91/29.14      inference('cnf', [status(esa)], [t21_xboole_1])).
% 28.91/29.14  thf('25', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 28.91/29.14      inference('sup+', [status(thm)], ['23', '24'])).
% 28.91/29.14  thf('26', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 28.91/29.14           = (k4_xboole_0 @ X0 @ X1))),
% 28.91/29.14      inference('sup+', [status(thm)], ['22', '25'])).
% 28.91/29.14  thf('27', plain,
% 28.91/29.14      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 28.91/29.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 28.91/29.14  thf('28', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 28.91/29.14           = (k4_xboole_0 @ X0 @ X1))),
% 28.91/29.14      inference('demod', [status(thm)], ['26', '27'])).
% 28.91/29.14  thf(t23_xboole_1, axiom,
% 28.91/29.14    (![A:$i,B:$i,C:$i]:
% 28.91/29.14     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 28.91/29.14       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 28.91/29.14  thf('29', plain,
% 28.91/29.14      (![X16 : $i, X17 : $i, X18 : $i]:
% 28.91/29.14         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 28.91/29.14           = (k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 28.91/29.14              (k3_xboole_0 @ X16 @ X18)))),
% 28.91/29.14      inference('cnf', [status(esa)], [t23_xboole_1])).
% 28.91/29.14  thf('30', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.91/29.14         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 28.91/29.14           = (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k4_xboole_0 @ X1 @ X0)))),
% 28.91/29.14      inference('sup+', [status(thm)], ['28', '29'])).
% 28.91/29.14  thf('31', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 28.91/29.14           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 28.91/29.14      inference('sup+', [status(thm)], ['4', '30'])).
% 28.91/29.14  thf('32', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 28.91/29.14      inference('sup+', [status(thm)], ['23', '24'])).
% 28.91/29.14  thf('33', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 28.91/29.14      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 28.91/29.14  thf('34', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((X0)
% 28.91/29.14           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 28.91/29.14      inference('demod', [status(thm)], ['31', '32', '33'])).
% 28.91/29.14  thf('35', plain,
% 28.91/29.14      (![X23 : $i, X24 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24)
% 28.91/29.14           = (k4_xboole_0 @ X23 @ X24))),
% 28.91/29.14      inference('cnf', [status(esa)], [t40_xboole_1])).
% 28.91/29.14  thf('36', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 28.91/29.14           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1)))),
% 28.91/29.14      inference('sup+', [status(thm)], ['34', '35'])).
% 28.91/29.14  thf('37', plain,
% 28.91/29.14      (![X25 : $i, X26 : $i, X27 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X27)
% 28.91/29.14           = (k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27)))),
% 28.91/29.14      inference('cnf', [status(esa)], [t41_xboole_1])).
% 28.91/29.14  thf('38', plain,
% 28.91/29.14      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 28.91/29.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 28.91/29.14  thf(t22_xboole_1, axiom,
% 28.91/29.14    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 28.91/29.14  thf('39', plain,
% 28.91/29.14      (![X14 : $i, X15 : $i]:
% 28.91/29.14         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 28.91/29.14      inference('cnf', [status(esa)], [t22_xboole_1])).
% 28.91/29.14  thf('40', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 28.91/29.14      inference('sup+', [status(thm)], ['38', '39'])).
% 28.91/29.14  thf('41', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 28.91/29.14           = (k4_xboole_0 @ X0 @ X1))),
% 28.91/29.14      inference('demod', [status(thm)], ['36', '37', '40'])).
% 28.91/29.14  thf('42', plain,
% 28.91/29.14      (![X0 : $i, X1 : $i]:
% 28.91/29.14         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 28.91/29.14           = (k4_xboole_0 @ X0 @ X1))),
% 28.91/29.14      inference('sup+', [status(thm)], ['3', '41'])).
% 28.91/29.14  thf('43', plain,
% 28.91/29.14      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 28.91/29.14      inference('demod', [status(thm)], ['2', '42'])).
% 28.91/29.14  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 28.91/29.14  
% 28.91/29.14  % SZS output end Refutation
% 28.91/29.14  
% 28.91/29.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
