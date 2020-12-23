%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ny6uTeWqX5

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  68 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  270 ( 437 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('22',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['27','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ny6uTeWqX5
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:12:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 221 iterations in 0.078s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(t106_xboole_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.53       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.53          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t28_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf(t49_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.21/0.53       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.53           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.53  thf(t36_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 0.21/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.53          (k3_xboole_0 @ X2 @ X1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['4', '7'])).
% 0.21/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.53  thf('10', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.53  thf(t17_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.21/0.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.53           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.53           = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.53  thf('20', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.21/0.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.53  thf('22', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('24', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('26', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.53           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.21/0.53      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.53  thf(t79_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.21/0.53      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.21/0.53      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.21/0.53      inference('sup+', [status(thm)], ['28', '31'])).
% 0.21/0.53  thf('33', plain, ($false), inference('demod', [status(thm)], ['27', '32'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
