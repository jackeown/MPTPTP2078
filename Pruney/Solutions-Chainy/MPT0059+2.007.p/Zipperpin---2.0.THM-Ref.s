%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UgWjA6iYUH

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:20 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  446 ( 570 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :   10 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t52_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17','18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','26'])).

thf('28',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UgWjA6iYUH
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:01:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 208 iterations in 0.200s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(t52_xboole_1, conjecture,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.46/0.66       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.66        ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.46/0.66          ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t52_xboole_1])).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.46/0.66         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.46/0.66             (k3_xboole_0 @ sk_A @ sk_C)))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t48_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.46/0.66           = (k3_xboole_0 @ X8 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.66  thf(l36_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.46/0.66       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.46/0.66           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.46/0.66      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.46/0.66           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf(t49_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.46/0.66       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.66           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 0.46/0.66           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.46/0.66           = (k3_xboole_0 @ X8 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.46/0.66           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.46/0.66      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.46/0.66           = (k3_xboole_0 @ X8 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.66  thf(t41_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.66       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X5)
% 0.46/0.66           = (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.66           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X2 @ X0))
% 0.46/0.66           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['7', '10'])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.46/0.66           = (k3_xboole_0 @ X8 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X2 @ X0))
% 0.46/0.66           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.66           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['6', '13'])).
% 0.46/0.66  thf(t50_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.46/0.66       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.46/0.66           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ 
% 0.46/0.66              (k3_xboole_0 @ X13 @ X15)))),
% 0.46/0.66      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.66           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 0.46/0.66           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ 
% 0.46/0.66              (k3_xboole_0 @ X13 @ X15)))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.66           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.66           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0)
% 0.46/0.66           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X1)) @ X0))),
% 0.46/0.66      inference('demod', [status(thm)], ['14', '17', '18', '19'])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.66         ((k3_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.66           = (k4_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12))),
% 0.46/0.66      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.46/0.66  thf(t47_xboole_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X6 : $i, X7 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 0.46/0.66           = (k4_xboole_0 @ X6 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 0.46/0.66           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 0.46/0.66           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['20', '23'])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 0.46/0.66           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.46/0.66           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X2) @ X0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['24', '25'])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 0.46/0.66           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['5', '26'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.46/0.66         != (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['0', '27'])).
% 0.46/0.66  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
