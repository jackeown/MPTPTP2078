%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ch5DERf0lB

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:17 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 334 expanded)
%              Number of leaves         :   12 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  440 (3396 expanded)
%              Number of equality atoms :   41 ( 327 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t49_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
        = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t49_xboole_1])).

thf('0',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
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

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X0 ) ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['11','18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','20','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['11','18','19'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['11','18','19'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','30','31'])).

thf('33',plain,(
    ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ch5DERf0lB
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 111 iterations in 0.419s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(t49_xboole_1, conjecture,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.68/0.87       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.68/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.87    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.87        ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.68/0.87          ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )),
% 0.68/0.87    inference('cnf.neg', [status(esa)], [t49_xboole_1])).
% 0.68/0.87  thf('0', plain,
% 0.68/0.87      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.68/0.87         != (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf(commutativity_k2_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.68/0.87  thf('1', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.87  thf(t41_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.68/0.87       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.68/0.87  thf('2', plain,
% 0.68/0.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.68/0.87           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.87  thf(t39_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.87  thf('3', plain,
% 0.68/0.87      (![X4 : $i, X5 : $i]:
% 0.68/0.87         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.68/0.87           = (k2_xboole_0 @ X4 @ X5))),
% 0.68/0.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.68/0.87  thf('4', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.68/0.87           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['2', '3'])).
% 0.68/0.87  thf('5', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.68/0.87           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['1', '4'])).
% 0.68/0.87  thf('6', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.87  thf(t48_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.68/0.87  thf('7', plain,
% 0.68/0.87      (![X9 : $i, X10 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.68/0.87           = (k3_xboole_0 @ X9 @ X10))),
% 0.68/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.87  thf('8', plain,
% 0.68/0.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.68/0.87           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.87  thf('9', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.68/0.87           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.68/0.87      inference('sup+', [status(thm)], ['7', '8'])).
% 0.68/0.87  thf('10', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.68/0.87           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['6', '9'])).
% 0.68/0.87  thf('11', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X0)) @ X2)
% 0.68/0.87           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['5', '10'])).
% 0.68/0.87  thf('12', plain,
% 0.68/0.87      (![X9 : $i, X10 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.68/0.87           = (k3_xboole_0 @ X9 @ X10))),
% 0.68/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.68/0.87  thf('13', plain,
% 0.68/0.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.68/0.87           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.87  thf('14', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.68/0.87           = (k4_xboole_0 @ X2 @ 
% 0.68/0.87              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['12', '13'])).
% 0.68/0.87  thf('15', plain,
% 0.68/0.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.68/0.87           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.68/0.87  thf('16', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.68/0.87           = (k4_xboole_0 @ X2 @ 
% 0.68/0.87              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.68/0.87      inference('demod', [status(thm)], ['14', '15'])).
% 0.68/0.87  thf('17', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.68/0.87           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['6', '9'])).
% 0.68/0.87  thf('18', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.68/0.87           = (k4_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1))),
% 0.68/0.87      inference('demod', [status(thm)], ['16', '17'])).
% 0.68/0.87  thf('19', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.68/0.87           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.68/0.87      inference('sup+', [status(thm)], ['6', '9'])).
% 0.68/0.87  thf('20', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0)
% 0.68/0.87           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.68/0.87      inference('demod', [status(thm)], ['11', '18', '19'])).
% 0.68/0.87  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.87  thf('21', plain,
% 0.68/0.87      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.87  thf('22', plain,
% 0.68/0.87      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.68/0.87         != (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.68/0.87      inference('demod', [status(thm)], ['0', '20', '21'])).
% 0.68/0.87  thf('23', plain,
% 0.68/0.87      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.87  thf('24', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0)
% 0.68/0.87           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.68/0.87      inference('demod', [status(thm)], ['11', '18', '19'])).
% 0.68/0.87  thf('25', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1)
% 0.68/0.87           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.68/0.87      inference('sup+', [status(thm)], ['23', '24'])).
% 0.68/0.87  thf('26', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0)
% 0.68/0.87           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.68/0.87      inference('demod', [status(thm)], ['11', '18', '19'])).
% 0.68/0.87  thf('27', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 0.68/0.87           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['25', '26'])).
% 0.68/0.87  thf('28', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 0.68/0.87           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['25', '26'])).
% 0.68/0.87  thf('29', plain,
% 0.68/0.87      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.68/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.87  thf('30', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.68/0.87           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['28', '29'])).
% 0.68/0.87  thf('31', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.68/0.87           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.68/0.87      inference('sup+', [status(thm)], ['28', '29'])).
% 0.68/0.87  thf('32', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1))
% 0.68/0.87           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.68/0.87      inference('demod', [status(thm)], ['27', '30', '31'])).
% 0.68/0.87  thf('33', plain,
% 0.68/0.87      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.68/0.87         != (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.68/0.87      inference('demod', [status(thm)], ['22', '32'])).
% 0.68/0.87  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.68/0.87  
% 0.68/0.87  % SZS output end Refutation
% 0.68/0.87  
% 0.72/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
