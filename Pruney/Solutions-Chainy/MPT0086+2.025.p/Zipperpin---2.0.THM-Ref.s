%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sHrhzbBiJO

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:31 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   51 (  73 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  347 ( 503 expanded)
%              Number of equality atoms :   39 (  61 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['12','17','18'])).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','29'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sHrhzbBiJO
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:31:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 299 iterations in 0.130s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(t79_xboole_1, conjecture,
% 0.36/0.60    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t79_xboole_1])).
% 0.36/0.60  thf('0', plain, (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t3_boole, axiom,
% 0.36/0.60    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.60  thf('1', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.60  thf(t48_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (![X10 : $i, X11 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.36/0.60           = (k3_xboole_0 @ X10 @ X11))),
% 0.36/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['1', '2'])).
% 0.36/0.60  thf(t2_boole, axiom,
% 0.36/0.60    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t2_boole])).
% 0.36/0.60  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['3', '4'])).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      (![X10 : $i, X11 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.36/0.60           = (k3_xboole_0 @ X10 @ X11))),
% 0.36/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.60  thf('8', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.60  thf('9', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.36/0.60  thf('10', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.60  thf(t52_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.36/0.60       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X14))
% 0.36/0.60           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.36/0.60              (k3_xboole_0 @ X12 @ X14)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 0.36/0.60           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.36/0.60  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['3', '4'])).
% 0.36/0.60  thf(t41_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.60       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.60           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.36/0.60           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf(t46_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      (![X8 : $i, X9 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.60  thf('18', plain, (![X4 : $i]: ((k4_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.60  thf('19', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.36/0.60      inference('demod', [status(thm)], ['12', '17', '18'])).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      (![X10 : $i, X11 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.36/0.60           = (k3_xboole_0 @ X10 @ X11))),
% 0.36/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.60           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.36/0.60           = (k4_xboole_0 @ X2 @ 
% 0.36/0.60              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.36/0.60      inference('sup+', [status(thm)], ['20', '21'])).
% 0.36/0.60  thf('23', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.60           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.60  thf('24', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.36/0.60           = (k4_xboole_0 @ X2 @ 
% 0.36/0.60              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.36/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.36/0.60           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X0))))),
% 0.36/0.60      inference('sup+', [status(thm)], ['19', '24'])).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.60           = (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.36/0.60  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['3', '4'])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 0.36/0.60           = (k1_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.60         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 0.36/0.60           = (k1_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['25', '28'])).
% 0.36/0.60  thf('30', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['9', '29'])).
% 0.36/0.60  thf(d7_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.60       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      (![X0 : $i, X2 : $i]:
% 0.36/0.60         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.60  thf('32', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.60          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.60  thf('33', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.60      inference('simplify', [status(thm)], ['32'])).
% 0.36/0.60  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
