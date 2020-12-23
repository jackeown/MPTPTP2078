%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u1tTGHrlGQ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  57 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  285 ( 348 expanded)
%              Number of equality atoms :   29 (  35 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t108_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t108_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','12','13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['18','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['0','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u1tTGHrlGQ
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:42:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 211 iterations in 0.090s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(t108_xboole_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.56        ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t108_xboole_1])).
% 0.20/0.56  thf('0', plain, (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t79_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.20/0.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.56  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.56  thf(t83_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i]:
% 0.20/0.56         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.56  thf(t48_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.20/0.56           = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X0 @ X0)
% 0.20/0.56           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf(t3_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.56  thf('8', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.20/0.56           = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf(t2_boole, axiom,
% 0.20/0.56    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.56  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.56  thf(t49_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.20/0.56       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 0.20/0.56           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['7', '12', '13'])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.20/0.56           = (k3_xboole_0 @ X7 @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.20/0.56           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.56  thf('17', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X0 @ X1)
% 0.20/0.56           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('19', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(l32_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X2 : $i, X4 : $i]:
% 0.20/0.56         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.56  thf('21', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))
% 0.20/0.56           = (k4_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.20/0.56           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 0.20/0.56      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i]:
% 0.20/0.56         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.56          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B)),
% 0.20/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.20/0.56      inference('sup+', [status(thm)], ['18', '28'])).
% 0.20/0.56  thf('30', plain, ($false), inference('demod', [status(thm)], ['0', '29'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
