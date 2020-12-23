%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ecAWpAhMcE

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   14 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  285 ( 345 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t79_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) ),
    inference('cnf.neg',[status(esa)],[t79_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) )
      = ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','20'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ecAWpAhMcE
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:16:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 145 iterations in 0.088s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(t79_xboole_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t79_xboole_1])).
% 0.21/0.55  thf('0', plain, (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t41_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.55       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.55           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.21/0.55  thf(t39_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.21/0.55           = (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.21/0.55           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf(t48_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.21/0.55           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.55           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.21/0.55           = (k4_xboole_0 @ X2 @ 
% 0.21/0.55              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.55           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.21/0.55           = (k4_xboole_0 @ X2 @ 
% 0.21/0.55              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.55           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['3', '8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.21/0.55           = (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.55           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf(t3_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.55  thf('12', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.21/0.55           = (k3_xboole_0 @ X10 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf(t2_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.55  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 0.21/0.55           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k1_xboole_0)
% 0.21/0.55           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4))
% 0.21/0.55           = (k2_xboole_0 @ X4 @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.21/0.55      inference('demod', [status(thm)], ['11', '20'])).
% 0.21/0.55  thf(d7_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i, X2 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.55  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
