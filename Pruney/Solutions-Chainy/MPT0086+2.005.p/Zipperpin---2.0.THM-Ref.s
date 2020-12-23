%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4TEwsm4PQX

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:28 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  306 ( 366 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','20'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('24',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4TEwsm4PQX
% 0.16/0.39  % Computer   : n008.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 10:31:30 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.40  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 195 iterations in 0.109s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(t79_xboole_1, conjecture,
% 0.39/0.61    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t79_xboole_1])).
% 0.39/0.61  thf('0', plain, (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t41_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.61       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.39/0.61           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.61  thf(t39_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.39/0.61           = (k2_xboole_0 @ X5 @ X6))),
% 0.39/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.39/0.61           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['1', '2'])).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.39/0.61           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.61  thf(t48_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      (![X11 : $i, X12 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.39/0.61           = (k3_xboole_0 @ X11 @ X12))),
% 0.39/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X2 @ 
% 0.39/0.61           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 0.39/0.61           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.39/0.61           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X2 @ 
% 0.39/0.61           (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 0.39/0.61           = (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.39/0.61           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['3', '8'])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.39/0.61           = (k2_xboole_0 @ X5 @ X6))),
% 0.39/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1))
% 0.39/0.61           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 0.39/0.61           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.61  thf(t3_boole, axiom,
% 0.39/0.61    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.61  thf('13', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.39/0.61      inference('cnf', [status(esa)], [t3_boole])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (![X11 : $i, X12 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.39/0.61           = (k3_xboole_0 @ X11 @ X12))),
% 0.39/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.61  thf('15', plain,
% 0.39/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.61  thf(t2_boole, axiom,
% 0.39/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.61  thf('16', plain,
% 0.39/0.61      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.61  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.39/0.61           = (k1_xboole_0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['12', '17'])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5))
% 0.39/0.61           = (k2_xboole_0 @ X5 @ X6))),
% 0.39/0.61      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.61  thf('20', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.39/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k1_xboole_0) = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['11', '20'])).
% 0.39/0.61  thf(t75_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.61          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (![X16 : $i, X17 : $i]:
% 0.39/0.61         ((r1_xboole_0 @ X16 @ X17)
% 0.39/0.61          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ X17))),
% 0.39/0.61      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.61          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.61  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.39/0.61  thf('24', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 0.39/0.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.39/0.61  thf(symmetry_r1_xboole_0, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X2 : $i, X3 : $i]:
% 0.39/0.61         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.39/0.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.39/0.61  thf('26', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.39/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.61  thf('27', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.39/0.61      inference('demod', [status(thm)], ['23', '26'])).
% 0.39/0.61  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
