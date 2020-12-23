%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DAwXMIZWH1

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:48 EST 2020

% Result     : Theorem 9.69s
% Output     : Refutation 9.69s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 124 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  492 ( 848 expanded)
%              Number of equality atoms :   57 ( 102 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t87_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
          = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['6','43'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) )
 != ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DAwXMIZWH1
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:43:12 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 9.69/9.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.69/9.95  % Solved by: fo/fo7.sh
% 9.69/9.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.69/9.95  % done 8294 iterations in 9.501s
% 9.69/9.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.69/9.95  % SZS output start Refutation
% 9.69/9.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.69/9.95  thf(sk_C_type, type, sk_C: $i).
% 9.69/9.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.69/9.95  thf(sk_A_type, type, sk_A: $i).
% 9.69/9.95  thf(sk_B_type, type, sk_B: $i).
% 9.69/9.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.69/9.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.69/9.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.69/9.95  thf(t87_xboole_1, conjecture,
% 9.69/9.95    (![A:$i,B:$i,C:$i]:
% 9.69/9.95     ( ( r1_xboole_0 @ A @ B ) =>
% 9.69/9.95       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 9.69/9.95         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 9.69/9.95  thf(zf_stmt_0, negated_conjecture,
% 9.69/9.95    (~( ![A:$i,B:$i,C:$i]:
% 9.69/9.95        ( ( r1_xboole_0 @ A @ B ) =>
% 9.69/9.95          ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 9.69/9.95            ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )),
% 9.69/9.95    inference('cnf.neg', [status(esa)], [t87_xboole_1])).
% 9.69/9.95  thf('0', plain,
% 9.69/9.95      (((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 9.69/9.95         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 9.69/9.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.69/9.95  thf(commutativity_k2_xboole_0, axiom,
% 9.69/9.95    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 9.69/9.95  thf('1', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.69/9.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.69/9.95  thf('2', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.69/9.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.69/9.95  thf('3', plain,
% 9.69/9.95      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A))
% 9.69/9.95         != (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 9.69/9.95      inference('demod', [status(thm)], ['0', '1', '2'])).
% 9.69/9.95  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 9.69/9.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.69/9.95  thf(t83_xboole_1, axiom,
% 9.69/9.95    (![A:$i,B:$i]:
% 9.69/9.95     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.69/9.95  thf('5', plain,
% 9.69/9.95      (![X23 : $i, X24 : $i]:
% 9.69/9.95         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 9.69/9.95      inference('cnf', [status(esa)], [t83_xboole_1])).
% 9.69/9.95  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 9.69/9.95      inference('sup-', [status(thm)], ['4', '5'])).
% 9.69/9.95  thf(t3_boole, axiom,
% 9.69/9.95    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 9.69/9.95  thf('7', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 9.69/9.95      inference('cnf', [status(esa)], [t3_boole])).
% 9.69/9.95  thf(t48_xboole_1, axiom,
% 9.69/9.95    (![A:$i,B:$i]:
% 9.69/9.95     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.69/9.95  thf('8', plain,
% 9.69/9.95      (![X16 : $i, X17 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.69/9.95           = (k3_xboole_0 @ X16 @ X17))),
% 9.69/9.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.69/9.95  thf('9', plain,
% 9.69/9.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 9.69/9.95      inference('sup+', [status(thm)], ['7', '8'])).
% 9.69/9.95  thf('10', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 9.69/9.95      inference('cnf', [status(esa)], [t3_boole])).
% 9.69/9.95  thf(t79_xboole_1, axiom,
% 9.69/9.95    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 9.69/9.95  thf('11', plain,
% 9.69/9.95      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 9.69/9.95      inference('cnf', [status(esa)], [t79_xboole_1])).
% 9.69/9.95  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 9.69/9.95      inference('sup+', [status(thm)], ['10', '11'])).
% 9.69/9.95  thf(d7_xboole_0, axiom,
% 9.69/9.95    (![A:$i,B:$i]:
% 9.69/9.95     ( ( r1_xboole_0 @ A @ B ) <=>
% 9.69/9.95       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 9.69/9.95  thf('13', plain,
% 9.69/9.95      (![X2 : $i, X3 : $i]:
% 9.69/9.95         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 9.69/9.95      inference('cnf', [status(esa)], [d7_xboole_0])).
% 9.69/9.95  thf('14', plain,
% 9.69/9.95      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 9.69/9.95      inference('sup-', [status(thm)], ['12', '13'])).
% 9.69/9.95  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.69/9.95      inference('demod', [status(thm)], ['9', '14'])).
% 9.69/9.95  thf('16', plain,
% 9.69/9.95      (![X16 : $i, X17 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 9.69/9.95           = (k3_xboole_0 @ X16 @ X17))),
% 9.69/9.95      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.69/9.95  thf('17', plain,
% 9.69/9.95      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 9.69/9.95      inference('sup+', [status(thm)], ['15', '16'])).
% 9.69/9.95  thf('18', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 9.69/9.95      inference('cnf', [status(esa)], [t3_boole])).
% 9.69/9.95  thf('19', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 9.69/9.95      inference('demod', [status(thm)], ['17', '18'])).
% 9.69/9.95  thf(t52_xboole_1, axiom,
% 9.69/9.95    (![A:$i,B:$i,C:$i]:
% 9.69/9.95     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 9.69/9.95       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 9.69/9.95  thf('20', plain,
% 9.69/9.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 9.69/9.95           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 9.69/9.95              (k3_xboole_0 @ X18 @ X20)))),
% 9.69/9.95      inference('cnf', [status(esa)], [t52_xboole_1])).
% 9.69/9.95  thf('21', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 9.69/9.95           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 9.69/9.95      inference('sup+', [status(thm)], ['19', '20'])).
% 9.69/9.95  thf('22', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.69/9.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.69/9.95  thf('23', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 9.69/9.95           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 9.69/9.95      inference('demod', [status(thm)], ['21', '22'])).
% 9.69/9.95  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.69/9.95      inference('demod', [status(thm)], ['9', '14'])).
% 9.69/9.95  thf(t41_xboole_1, axiom,
% 9.69/9.95    (![A:$i,B:$i,C:$i]:
% 9.69/9.95     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 9.69/9.95       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.69/9.95  thf('25', plain,
% 9.69/9.95      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 9.69/9.95           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 9.69/9.95      inference('cnf', [status(esa)], [t41_xboole_1])).
% 9.69/9.95  thf(t39_xboole_1, axiom,
% 9.69/9.95    (![A:$i,B:$i]:
% 9.69/9.95     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 9.69/9.95  thf('26', plain,
% 9.69/9.95      (![X5 : $i, X6 : $i]:
% 9.69/9.95         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 9.69/9.95           = (k2_xboole_0 @ X5 @ X6))),
% 9.69/9.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.69/9.95  thf('27', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.69/9.95         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 9.69/9.95           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 9.69/9.95      inference('sup+', [status(thm)], ['25', '26'])).
% 9.69/9.95  thf('28', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i]:
% 9.69/9.95         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 9.69/9.95           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)))),
% 9.69/9.95      inference('sup+', [status(thm)], ['24', '27'])).
% 9.69/9.95  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.69/9.95      inference('demod', [status(thm)], ['9', '14'])).
% 9.69/9.95  thf('30', plain,
% 9.69/9.95      (![X5 : $i, X6 : $i]:
% 9.69/9.95         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 9.69/9.95           = (k2_xboole_0 @ X5 @ X6))),
% 9.69/9.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 9.69/9.95  thf('31', plain,
% 9.69/9.95      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 9.69/9.95      inference('sup+', [status(thm)], ['29', '30'])).
% 9.69/9.95  thf('32', plain,
% 9.69/9.95      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 9.69/9.95      inference('sup+', [status(thm)], ['29', '30'])).
% 9.69/9.95  thf(t40_xboole_1, axiom,
% 9.69/9.95    (![A:$i,B:$i]:
% 9.69/9.95     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 9.69/9.95  thf('33', plain,
% 9.69/9.95      (![X8 : $i, X9 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 9.69/9.95           = (k4_xboole_0 @ X8 @ X9))),
% 9.69/9.95      inference('cnf', [status(esa)], [t40_xboole_1])).
% 9.69/9.95  thf('34', plain,
% 9.69/9.95      (![X0 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ k1_xboole_0)
% 9.69/9.95           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 9.69/9.95      inference('sup+', [status(thm)], ['32', '33'])).
% 9.69/9.95  thf('35', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 9.69/9.95      inference('cnf', [status(esa)], [t3_boole])).
% 9.69/9.95  thf('36', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 9.69/9.95      inference('cnf', [status(esa)], [t3_boole])).
% 9.69/9.95  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 9.69/9.95      inference('demod', [status(thm)], ['34', '35', '36'])).
% 9.69/9.95  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.69/9.95      inference('demod', [status(thm)], ['31', '37'])).
% 9.69/9.95  thf('39', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.69/9.95      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 9.69/9.95  thf('40', plain,
% 9.69/9.95      (![X8 : $i, X9 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ X9)
% 9.69/9.95           = (k4_xboole_0 @ X8 @ X9))),
% 9.69/9.95      inference('cnf', [status(esa)], [t40_xboole_1])).
% 9.69/9.95  thf('41', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 9.69/9.95           = (k4_xboole_0 @ X0 @ X1))),
% 9.69/9.95      inference('sup+', [status(thm)], ['39', '40'])).
% 9.69/9.95  thf('42', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i]:
% 9.69/9.95         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.69/9.95      inference('demod', [status(thm)], ['28', '38', '41'])).
% 9.69/9.95  thf('43', plain,
% 9.69/9.95      (![X0 : $i, X1 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 9.69/9.95      inference('demod', [status(thm)], ['23', '42'])).
% 9.69/9.95  thf('44', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 9.69/9.95      inference('sup+', [status(thm)], ['6', '43'])).
% 9.69/9.95  thf(t42_xboole_1, axiom,
% 9.69/9.95    (![A:$i,B:$i,C:$i]:
% 9.69/9.95     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 9.69/9.95       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 9.69/9.95  thf('45', plain,
% 9.69/9.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ (k2_xboole_0 @ X13 @ X15) @ X14)
% 9.69/9.95           = (k2_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ 
% 9.69/9.95              (k4_xboole_0 @ X15 @ X14)))),
% 9.69/9.95      inference('cnf', [status(esa)], [t42_xboole_1])).
% 9.69/9.95  thf('46', plain,
% 9.69/9.95      (![X0 : $i]:
% 9.69/9.95         ((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 9.69/9.95           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)))),
% 9.69/9.95      inference('sup+', [status(thm)], ['44', '45'])).
% 9.69/9.95  thf('47', plain,
% 9.69/9.95      (((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A))
% 9.69/9.95         != (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_C @ sk_A)))),
% 9.69/9.95      inference('demod', [status(thm)], ['3', '46'])).
% 9.69/9.95  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 9.69/9.95  
% 9.69/9.95  % SZS output end Refutation
% 9.69/9.95  
% 9.69/9.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
