%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XOGeOGukUk

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:32 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   51 (  74 expanded)
%              Number of leaves         :   14 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  288 ( 483 expanded)
%              Number of equality atoms :   19 (  28 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
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

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('24',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['29','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XOGeOGukUk
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.54  % Solved by: fo/fo7.sh
% 0.38/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.54  % done 297 iterations in 0.093s
% 0.38/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.54  % SZS output start Refutation
% 0.38/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.54  thf(t106_xboole_1, conjecture,
% 0.38/0.54    (![A:$i,B:$i,C:$i]:
% 0.38/0.54     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.38/0.54       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.38/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.54        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.38/0.54          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.38/0.54    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.38/0.54  thf('0', plain,
% 0.38/0.54      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('1', plain,
% 0.38/0.54      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.38/0.54      inference('split', [status(esa)], ['0'])).
% 0.38/0.54  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf(t28_xboole_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.54  thf('3', plain,
% 0.38/0.54      (![X7 : $i, X8 : $i]:
% 0.38/0.54         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.38/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.54  thf('4', plain,
% 0.38/0.54      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.54  thf(t49_xboole_1, axiom,
% 0.38/0.54    (![A:$i,B:$i,C:$i]:
% 0.38/0.54     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.38/0.54       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.38/0.54  thf('5', plain,
% 0.38/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.54         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.38/0.54           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.38/0.54      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.38/0.54  thf(t36_xboole_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.54  thf('6', plain,
% 0.38/0.54      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.38/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.54  thf('7', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.54         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.38/0.54          (k3_xboole_0 @ X2 @ X1))),
% 0.38/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.54  thf('8', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.54      inference('sup+', [status(thm)], ['4', '7'])).
% 0.38/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.54  thf('9', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.54  thf('10', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.38/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.54  thf('11', plain,
% 0.38/0.54      (![X7 : $i, X8 : $i]:
% 0.38/0.54         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.38/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.54  thf('12', plain,
% 0.38/0.54      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.54  thf('13', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.54  thf(t48_xboole_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.54  thf('14', plain,
% 0.38/0.54      (![X11 : $i, X12 : $i]:
% 0.38/0.54         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.38/0.54           = (k3_xboole_0 @ X11 @ X12))),
% 0.38/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.54  thf('15', plain,
% 0.38/0.54      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.38/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.38/0.54  thf('16', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.38/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.54  thf('17', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.38/0.54      inference('sup+', [status(thm)], ['13', '16'])).
% 0.38/0.54  thf('18', plain,
% 0.38/0.54      (![X7 : $i, X8 : $i]:
% 0.38/0.54         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.38/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.54  thf('19', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]:
% 0.38/0.54         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.38/0.54           = (k3_xboole_0 @ X1 @ X0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.54  thf('20', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.54  thf('21', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]:
% 0.38/0.54         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.54           = (k3_xboole_0 @ X1 @ X0))),
% 0.38/0.54      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.54  thf('22', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.38/0.54      inference('demod', [status(thm)], ['12', '21'])).
% 0.38/0.54  thf('23', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.38/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.54  thf('24', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.38/0.54      inference('sup+', [status(thm)], ['22', '23'])).
% 0.38/0.54  thf('25', plain,
% 0.38/0.54      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.38/0.54      inference('split', [status(esa)], ['0'])).
% 0.38/0.54  thf('26', plain, (((r1_tarski @ sk_A @ sk_B))),
% 0.38/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.54  thf('27', plain,
% 0.38/0.54      (~ ((r1_xboole_0 @ sk_A @ sk_C)) | ~ ((r1_tarski @ sk_A @ sk_B))),
% 0.38/0.54      inference('split', [status(esa)], ['0'])).
% 0.38/0.54  thf('28', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.54      inference('sat_resolution*', [status(thm)], ['26', '27'])).
% 0.38/0.54  thf('29', plain, (~ (r1_xboole_0 @ sk_A @ sk_C)),
% 0.38/0.54      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.38/0.54  thf('30', plain,
% 0.38/0.54      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.54  thf('31', plain,
% 0.38/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.54         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.38/0.54           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 0.38/0.54      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.38/0.54  thf(t79_xboole_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.38/0.54  thf('32', plain,
% 0.38/0.54      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.38/0.54      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.38/0.54  thf('33', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.54         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.38/0.54      inference('sup+', [status(thm)], ['31', '32'])).
% 0.38/0.54  thf('34', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.38/0.54      inference('sup+', [status(thm)], ['30', '33'])).
% 0.38/0.54  thf('35', plain, ($false), inference('demod', [status(thm)], ['29', '34'])).
% 0.38/0.54  
% 0.38/0.54  % SZS output end Refutation
% 0.38/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
