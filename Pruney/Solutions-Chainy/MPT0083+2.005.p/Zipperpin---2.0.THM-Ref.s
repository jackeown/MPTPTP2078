%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8EmCZBoKWy

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:16 EST 2020

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   53 (  74 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  358 ( 530 expanded)
%              Number of equality atoms :   33 (  51 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t76_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('10',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['3','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8EmCZBoKWy
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:08 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.73/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.73/0.89  % Solved by: fo/fo7.sh
% 0.73/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.73/0.89  % done 703 iterations in 0.445s
% 0.73/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.73/0.89  % SZS output start Refutation
% 0.73/0.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.73/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.73/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.73/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.73/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.73/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.73/0.89  thf(t76_xboole_1, conjecture,
% 0.73/0.89    (![A:$i,B:$i,C:$i]:
% 0.73/0.89     ( ( r1_xboole_0 @ A @ B ) =>
% 0.73/0.89       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.73/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.73/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.73/0.89        ( ( r1_xboole_0 @ A @ B ) =>
% 0.73/0.89          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.73/0.89    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.73/0.89  thf('0', plain,
% 0.73/0.89      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 0.73/0.89          (k3_xboole_0 @ sk_C @ sk_B))),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf(commutativity_k3_xboole_0, axiom,
% 0.73/0.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.73/0.89  thf('1', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.73/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.73/0.89  thf('2', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.73/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.73/0.89  thf('3', plain,
% 0.73/0.89      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.73/0.89          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.73/0.89      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.73/0.89  thf('4', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.73/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.73/0.89  thf('5', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.73/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.73/0.89  thf(d7_xboole_0, axiom,
% 0.73/0.89    (![A:$i,B:$i]:
% 0.73/0.89     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.73/0.89       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.73/0.89  thf('6', plain,
% 0.73/0.89      (![X2 : $i, X3 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.73/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.73/0.89  thf('7', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.73/0.89      inference('sup-', [status(thm)], ['5', '6'])).
% 0.73/0.89  thf(t16_xboole_1, axiom,
% 0.73/0.89    (![A:$i,B:$i,C:$i]:
% 0.73/0.89     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.73/0.89       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.73/0.89  thf('8', plain,
% 0.73/0.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.73/0.89         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.73/0.89           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.73/0.89      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.73/0.89  thf('9', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.73/0.89           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.73/0.89      inference('sup+', [status(thm)], ['7', '8'])).
% 0.73/0.89  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.73/0.89  thf('10', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 0.73/0.89      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.73/0.89  thf(symmetry_r1_xboole_0, axiom,
% 0.73/0.89    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.73/0.89  thf('11', plain,
% 0.73/0.89      (![X5 : $i, X6 : $i]:
% 0.73/0.89         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.73/0.89      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.73/0.89  thf('12', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.73/0.89      inference('sup-', [status(thm)], ['10', '11'])).
% 0.73/0.89  thf('13', plain,
% 0.73/0.89      (![X2 : $i, X3 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.73/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.73/0.89  thf('14', plain,
% 0.73/0.89      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.73/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.73/0.89  thf('15', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.73/0.89      inference('demod', [status(thm)], ['9', '14'])).
% 0.73/0.89  thf('16', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.73/0.89      inference('sup+', [status(thm)], ['4', '15'])).
% 0.73/0.89  thf('17', plain,
% 0.73/0.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.73/0.89         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.73/0.89           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.73/0.89      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.73/0.89  thf('18', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.73/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.73/0.89  thf('19', plain,
% 0.73/0.89      (![X2 : $i, X4 : $i]:
% 0.73/0.89         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.73/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.73/0.89  thf('20', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.73/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.73/0.89  thf('21', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.73/0.89          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['17', '20'])).
% 0.73/0.89  thf('22', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         (((k1_xboole_0) != (k1_xboole_0))
% 0.73/0.89          | (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['16', '21'])).
% 0.73/0.89  thf('23', plain,
% 0.73/0.89      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0))),
% 0.73/0.89      inference('simplify', [status(thm)], ['22'])).
% 0.73/0.89  thf('24', plain,
% 0.73/0.89      (![X2 : $i, X3 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.73/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.73/0.89  thf('25', plain,
% 0.73/0.89      (![X0 : $i]:
% 0.73/0.89         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))),
% 0.73/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.73/0.89  thf('26', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.73/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.73/0.89  thf('27', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.73/0.89      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.73/0.89  thf('28', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.73/0.89          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['17', '20'])).
% 0.73/0.89  thf('29', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0) != (k1_xboole_0))
% 0.73/0.89          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['27', '28'])).
% 0.73/0.89  thf('30', plain,
% 0.73/0.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.73/0.89         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.73/0.89           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.73/0.89      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.73/0.89  thf('31', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.73/0.89          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2)))),
% 0.73/0.89      inference('demod', [status(thm)], ['29', '30'])).
% 0.73/0.89  thf('32', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.73/0.89          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['26', '31'])).
% 0.73/0.89  thf('33', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ X1 @ k1_xboole_0) != (k1_xboole_0))
% 0.73/0.89          | (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 0.73/0.89             (k3_xboole_0 @ sk_B @ X1)))),
% 0.73/0.89      inference('sup-', [status(thm)], ['25', '32'])).
% 0.73/0.89  thf('34', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 0.73/0.89      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.73/0.89  thf('35', plain,
% 0.73/0.89      (![X2 : $i, X3 : $i]:
% 0.73/0.89         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.73/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.73/0.89  thf('36', plain,
% 0.73/0.89      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.73/0.89      inference('sup-', [status(thm)], ['34', '35'])).
% 0.73/0.89  thf('37', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i]:
% 0.73/0.89         (((k1_xboole_0) != (k1_xboole_0))
% 0.73/0.89          | (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 0.73/0.89             (k3_xboole_0 @ sk_B @ X1)))),
% 0.73/0.89      inference('demod', [status(thm)], ['33', '36'])).
% 0.73/0.89  thf('38', plain,
% 0.73/0.89      (![X0 : $i, X1 : $i]:
% 0.73/0.89         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X1))),
% 0.73/0.89      inference('simplify', [status(thm)], ['37'])).
% 0.73/0.89  thf('39', plain, ($false), inference('demod', [status(thm)], ['3', '38'])).
% 0.73/0.89  
% 0.73/0.89  % SZS output end Refutation
% 0.73/0.89  
% 0.73/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
