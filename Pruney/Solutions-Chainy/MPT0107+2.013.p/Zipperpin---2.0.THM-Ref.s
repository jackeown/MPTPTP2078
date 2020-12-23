%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ww4vz9g7Tm

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:11 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  314 ( 387 expanded)
%              Number of equality atoms :   39 (  50 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X5 )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','24','25'])).

thf('27',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ww4vz9g7Tm
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:56:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.79  % Solved by: fo/fo7.sh
% 0.55/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.79  % done 559 iterations in 0.324s
% 0.55/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.79  % SZS output start Refutation
% 0.55/0.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.79  thf(t100_xboole_1, conjecture,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.79    (~( ![A:$i,B:$i]:
% 0.55/0.79        ( ( k4_xboole_0 @ A @ B ) =
% 0.55/0.79          ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.55/0.79    inference('cnf.neg', [status(esa)], [t100_xboole_1])).
% 0.55/0.79  thf('0', plain,
% 0.55/0.79      (((k4_xboole_0 @ sk_A @ sk_B)
% 0.55/0.79         != (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.55/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.79  thf(t47_xboole_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.55/0.79  thf('1', plain,
% 0.55/0.79      (![X9 : $i, X10 : $i]:
% 0.55/0.79         ((k4_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10))
% 0.55/0.79           = (k4_xboole_0 @ X9 @ X10))),
% 0.55/0.79      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.55/0.79  thf(d6_xboole_0, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( k5_xboole_0 @ A @ B ) =
% 0.55/0.79       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.55/0.79  thf('2', plain,
% 0.55/0.79      (![X2 : $i, X3 : $i]:
% 0.55/0.79         ((k5_xboole_0 @ X2 @ X3)
% 0.55/0.79           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 0.55/0.79      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.55/0.79  thf('3', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]:
% 0.55/0.79         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.79           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.55/0.79              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.55/0.79      inference('sup+', [status(thm)], ['1', '2'])).
% 0.55/0.79  thf(t48_xboole_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.79  thf('4', plain,
% 0.55/0.79      (![X11 : $i, X12 : $i]:
% 0.55/0.79         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.55/0.79           = (k3_xboole_0 @ X11 @ X12))),
% 0.55/0.79      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.79  thf(t41_xboole_1, axiom,
% 0.55/0.79    (![A:$i,B:$i,C:$i]:
% 0.55/0.79     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.55/0.79       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.55/0.79  thf('5', plain,
% 0.55/0.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.55/0.79           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.55/0.79      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.55/0.79  thf('6', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.79         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.55/0.79           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.55/0.79      inference('sup+', [status(thm)], ['4', '5'])).
% 0.55/0.79  thf(commutativity_k2_xboole_0, axiom,
% 0.55/0.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.55/0.79  thf('7', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.79  thf(t4_boole, axiom,
% 0.55/0.79    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.55/0.79  thf('8', plain,
% 0.55/0.79      (![X13 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.55/0.79      inference('cnf', [status(esa)], [t4_boole])).
% 0.55/0.79  thf(t98_xboole_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.55/0.79  thf('9', plain,
% 0.55/0.79      (![X15 : $i, X16 : $i]:
% 0.55/0.79         ((k2_xboole_0 @ X15 @ X16)
% 0.55/0.79           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.55/0.79      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.55/0.79  thf('10', plain,
% 0.55/0.79      (![X0 : $i]:
% 0.55/0.79         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.79      inference('sup+', [status(thm)], ['8', '9'])).
% 0.55/0.79  thf(t5_boole, axiom,
% 0.55/0.79    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.55/0.79  thf('11', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.55/0.79      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.79  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.55/0.79      inference('demod', [status(thm)], ['10', '11'])).
% 0.55/0.79  thf('13', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.55/0.79  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.55/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.55/0.79  thf(t40_xboole_1, axiom,
% 0.55/0.79    (![A:$i,B:$i]:
% 0.55/0.79     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.55/0.79  thf('15', plain,
% 0.55/0.79      (![X4 : $i, X5 : $i]:
% 0.55/0.79         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X5)
% 0.55/0.79           = (k4_xboole_0 @ X4 @ X5))),
% 0.55/0.79      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.55/0.79  thf('16', plain,
% 0.55/0.79      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.55/0.79      inference('sup+', [status(thm)], ['14', '15'])).
% 0.55/0.79  thf('17', plain,
% 0.55/0.79      (![X13 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.55/0.79      inference('cnf', [status(esa)], [t4_boole])).
% 0.55/0.79  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.79      inference('demod', [status(thm)], ['16', '17'])).
% 0.55/0.79  thf('19', plain,
% 0.55/0.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.79         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.55/0.79           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.55/0.79      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.55/0.79  thf('20', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]:
% 0.55/0.79         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.55/0.79           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.55/0.79      inference('sup+', [status(thm)], ['18', '19'])).
% 0.55/0.79  thf('21', plain,
% 0.55/0.79      (![X13 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.55/0.79      inference('cnf', [status(esa)], [t4_boole])).
% 0.55/0.79  thf('22', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]:
% 0.55/0.79         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.55/0.79      inference('demod', [status(thm)], ['20', '21'])).
% 0.55/0.79  thf('23', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]:
% 0.55/0.79         ((k1_xboole_0) = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.55/0.79      inference('sup+', [status(thm)], ['7', '22'])).
% 0.55/0.79  thf('24', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]:
% 0.55/0.79         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.55/0.79      inference('sup+', [status(thm)], ['6', '23'])).
% 0.55/0.79  thf('25', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.55/0.79      inference('demod', [status(thm)], ['10', '11'])).
% 0.55/0.79  thf('26', plain,
% 0.55/0.79      (![X0 : $i, X1 : $i]:
% 0.55/0.79         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.79           = (k4_xboole_0 @ X1 @ X0))),
% 0.55/0.79      inference('demod', [status(thm)], ['3', '24', '25'])).
% 0.55/0.79  thf('27', plain,
% 0.55/0.79      (((k4_xboole_0 @ sk_A @ sk_B) != (k4_xboole_0 @ sk_A @ sk_B))),
% 0.55/0.79      inference('demod', [status(thm)], ['0', '26'])).
% 0.55/0.79  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.55/0.79  
% 0.55/0.79  % SZS output end Refutation
% 0.55/0.79  
% 0.63/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
