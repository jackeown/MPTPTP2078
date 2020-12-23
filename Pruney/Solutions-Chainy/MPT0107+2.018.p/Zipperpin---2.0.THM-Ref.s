%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9Xzmha2pKL

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:12 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   67 (  75 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  464 ( 521 expanded)
%              Number of equality atoms :   54 (  61 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('18',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','26'])).

thf('28',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','30'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9Xzmha2pKL
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:41:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.59/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.81  % Solved by: fo/fo7.sh
% 0.59/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.81  % done 757 iterations in 0.344s
% 0.59/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.81  % SZS output start Refutation
% 0.59/0.81  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.81  thf(t100_xboole_1, conjecture,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.81    (~( ![A:$i,B:$i]:
% 0.59/0.81        ( ( k4_xboole_0 @ A @ B ) =
% 0.59/0.81          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.59/0.81    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.59/0.81  thf('0', plain,
% 0.59/0.81      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.59/0.81         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.81  thf('1', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.81  thf('2', plain,
% 0.59/0.81      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.59/0.81         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.81  thf('3', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.81  thf(t47_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.59/0.81  thf('4', plain,
% 0.59/0.81      (![X15 : $i, X16 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.59/0.81           = (k4_xboole_0 @ X15 @ X16))),
% 0.59/0.81      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.59/0.81  thf(t98_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.59/0.81  thf('5', plain,
% 0.59/0.81      (![X24 : $i, X25 : $i]:
% 0.59/0.81         ((k2_xboole_0 @ X24 @ X25)
% 0.59/0.81           = (k5_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X24)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.59/0.81  thf('6', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.59/0.81           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['4', '5'])).
% 0.59/0.81  thf(t48_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.81  thf('7', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.81           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.81  thf(t36_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.81  thf('8', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.59/0.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.81  thf('9', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.59/0.81      inference('sup+', [status(thm)], ['7', '8'])).
% 0.59/0.81  thf(l32_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.81  thf('10', plain,
% 0.59/0.81      (![X4 : $i, X6 : $i]:
% 0.59/0.81         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.81      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.81  thf('11', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['9', '10'])).
% 0.59/0.81  thf(t40_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.59/0.81  thf('12', plain,
% 0.59/0.81      (![X10 : $i, X11 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.59/0.81           = (k4_xboole_0 @ X10 @ X11))),
% 0.59/0.81      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.59/0.81  thf('13', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.81           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.81  thf('14', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.81           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.81  thf('15', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.81      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.81  thf('16', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.81           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.81  thf('17', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.59/0.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.81  thf('18', plain,
% 0.59/0.81      (![X4 : $i, X6 : $i]:
% 0.59/0.81         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.59/0.81      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.81  thf('19', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.81  thf(t41_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.81       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.81  thf('20', plain,
% 0.59/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 0.59/0.81           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.59/0.81  thf('21', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.59/0.81      inference('demod', [status(thm)], ['19', '20'])).
% 0.59/0.81  thf('22', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.59/0.81           = (k3_xboole_0 @ X17 @ X18))),
% 0.59/0.81      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.59/0.81  thf('23', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.59/0.81           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.81  thf(t3_boole, axiom,
% 0.59/0.81    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.81  thf('24', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.81  thf('25', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['23', '24'])).
% 0.59/0.81  thf('26', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.59/0.81           = (X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['16', '25'])).
% 0.59/0.81  thf('27', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) @ 
% 0.59/0.81           k1_xboole_0) = (X0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['11', '26'])).
% 0.59/0.81  thf('28', plain, (![X9 : $i]: ((k4_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.81  thf('29', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.81  thf('30', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((X1)
% 0.59/0.81           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['6', '29'])).
% 0.59/0.81  thf('31', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((X0)
% 0.59/0.81           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['3', '30'])).
% 0.59/0.81  thf(t92_xboole_1, axiom,
% 0.59/0.81    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.59/0.81  thf('32', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.59/0.81  thf(t91_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.81       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.59/0.81  thf('33', plain,
% 0.59/0.81      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.59/0.81         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 0.59/0.81           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.59/0.81  thf('34', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.81           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['32', '33'])).
% 0.59/0.81  thf(commutativity_k5_xboole_0, axiom,
% 0.59/0.81    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.59/0.81  thf('35', plain,
% 0.59/0.81      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.59/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.81  thf(t5_boole, axiom,
% 0.59/0.81    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.81  thf('36', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.59/0.81      inference('cnf', [status(esa)], [t5_boole])).
% 0.59/0.81  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['35', '36'])).
% 0.59/0.81  thf('38', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['34', '37'])).
% 0.59/0.81  thf('39', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.81           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['31', '38'])).
% 0.59/0.81  thf('40', plain,
% 0.59/0.81      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.59/0.81      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.59/0.81  thf('41', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_xboole_0 @ X0 @ X1)
% 0.59/0.81           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['39', '40'])).
% 0.59/0.81  thf('42', plain,
% 0.59/0.81      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['2', '41'])).
% 0.59/0.81  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.59/0.81  
% 0.59/0.81  % SZS output end Refutation
% 0.59/0.81  
% 0.59/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
