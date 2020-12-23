%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y2CTzdfLxf

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:07 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  352 ( 439 expanded)
%              Number of equality atoms :   39 (  48 expanded)
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

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','17'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['3','26'])).

thf('28',plain,(
    ( k2_xboole_0 @ sk_A @ sk_B )
 != ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Y2CTzdfLxf
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:18:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 519 iterations in 0.196s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(t98_xboole_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i]:
% 0.45/0.65        ( ( k2_xboole_0 @ A @ B ) =
% 0.45/0.65          ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t98_xboole_1])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.45/0.65         != (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t94_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k2_xboole_0 @ A @ B ) =
% 0.45/0.65       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X13 @ X14)
% 0.45/0.65           = (k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ 
% 0.45/0.65              (k3_xboole_0 @ X13 @ X14)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.45/0.65  thf(t91_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.45/0.65       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.65         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 0.45/0.65           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X13 @ X14)
% 0.45/0.65           = (k5_xboole_0 @ X13 @ 
% 0.45/0.65              (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X13 @ X14))))),
% 0.45/0.65      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf(t48_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X6 : $i, X7 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.65           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X6 : $i, X7 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.65           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X6 : $i, X7 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.45/0.65           = (k3_xboole_0 @ X6 @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['6', '7'])).
% 0.45/0.65  thf(t47_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5))
% 0.45/0.65           = (k4_xboole_0 @ X4 @ X5))),
% 0.45/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k4_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X13 @ X14)
% 0.45/0.65           = (k5_xboole_0 @ X13 @ 
% 0.45/0.65              (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X13 @ X14))))),
% 0.45/0.65      inference('demod', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k5_xboole_0 @ X1 @ 
% 0.45/0.65              (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf(t92_xboole_1, axiom,
% 0.45/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.65  thf('13', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ X12) = (k1_xboole_0))),
% 0.45/0.65      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf(t5_boole, axiom,
% 0.45/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.65  thf('15', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (X1))),
% 0.45/0.65      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['5', '16'])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['4', '17'])).
% 0.45/0.65  thf(l98_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k5_xboole_0 @ A @ B ) =
% 0.45/0.65       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X2 : $i, X3 : $i]:
% 0.45/0.65         ((k5_xboole_0 @ X2 @ X3)
% 0.45/0.65           = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.45/0.65      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5))
% 0.45/0.65           = (k4_xboole_0 @ X4 @ X5))),
% 0.45/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5))
% 0.45/0.65           = (k4_xboole_0 @ X4 @ X5))),
% 0.45/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['23', '24'])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('demod', [status(thm)], ['22', '25'])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X13 @ X14)
% 0.45/0.65           = (k5_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.45/0.65      inference('demod', [status(thm)], ['3', '26'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (((k2_xboole_0 @ sk_A @ sk_B) != (k2_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.65      inference('demod', [status(thm)], ['0', '27'])).
% 0.45/0.65  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
