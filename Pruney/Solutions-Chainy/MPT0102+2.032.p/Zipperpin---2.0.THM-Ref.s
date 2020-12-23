%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aEuD3VM8rj

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  369 ( 474 expanded)
%              Number of equality atoms :   46 (  59 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('2',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k5_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ X10 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','31'])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['6','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aEuD3VM8rj
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:33:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 139 iterations in 0.074s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(t95_xboole_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k3_xboole_0 @ A @ B ) =
% 0.20/0.53       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( k3_xboole_0 @ A @ B ) =
% 0.20/0.53          ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t95_xboole_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.20/0.53         != (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.53             (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(commutativity_k5_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.20/0.53         != (k5_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 0.20/0.53             (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.53  thf(t91_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.53       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.20/0.53           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.20/0.53           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.20/0.53         != (k5_xboole_0 @ sk_A @ 
% 0.20/0.53             (k5_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B))))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '5'])).
% 0.20/0.53  thf(t94_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k2_xboole_0 @ A @ B ) =
% 0.20/0.53       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X11 @ X12)
% 0.20/0.53           = (k5_xboole_0 @ (k5_xboole_0 @ X11 @ X12) @ 
% 0.20/0.53              (k3_xboole_0 @ X11 @ X12)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X11 @ X12)
% 0.20/0.53           = (k5_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ 
% 0.20/0.53              (k5_xboole_0 @ X11 @ X12)))),
% 0.20/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.53  thf(t92_xboole_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('11', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.20/0.53           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf(t3_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('14', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf(t48_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.20/0.53           = (k3_xboole_0 @ X5 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf(t2_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.53  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.20/0.53           = (k3_xboole_0 @ X5 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf('22', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X11 @ X12)
% 0.20/0.53           = (k5_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ 
% 0.20/0.53              (k5_xboole_0 @ X11 @ X12)))),
% 0.20/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k2_xboole_0 @ X0 @ X0)
% 0.20/0.53           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.53  thf('25', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.53  thf('26', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ X10) = (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.53  thf('27', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.20/0.53  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['10', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X1 @ X0)
% 0.20/0.53           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['9', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         ((k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9)
% 0.20/0.53           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ X9)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X1 @ X0)
% 0.20/0.53           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '34'])).
% 0.20/0.53  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
