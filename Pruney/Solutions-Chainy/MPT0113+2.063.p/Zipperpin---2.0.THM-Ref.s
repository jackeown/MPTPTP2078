%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CB8y4koR8Y

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 (  89 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  337 ( 622 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','37'])).

thf('39',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['13','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CB8y4koR8Y
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 171 iterations in 0.060s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.51  thf(t106_xboole_1, conjecture,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.19/0.51       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.51        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.19/0.51          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.19/0.51  thf('0', plain,
% 0.19/0.51      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t28_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      (![X5 : $i, X6 : $i]:
% 0.19/0.51         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.19/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.51  thf(t49_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.19/0.51       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.51         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.19/0.51           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C) = (sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.51  thf(t79_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.19/0.51      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.19/0.51  thf('8', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.19/0.51      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.51  thf('9', plain,
% 0.19/0.51      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('10', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.19/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('12', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['10', '11'])).
% 0.19/0.51  thf('13', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.19/0.51  thf('14', plain,
% 0.19/0.51      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C) = (sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.51  thf(t36_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.51  thf('15', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.19/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.51  thf(l32_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X0 : $i, X2 : $i]:
% 0.19/0.51         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.19/0.51      inference('sup+', [status(thm)], ['14', '17'])).
% 0.19/0.51  thf(t48_xboole_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X9 : $i, X10 : $i]:
% 0.19/0.51         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.19/0.51           = (k3_xboole_0 @ X9 @ X10))),
% 0.19/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      (![X9 : $i, X10 : $i]:
% 0.19/0.51         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.19/0.51           = (k3_xboole_0 @ X9 @ X10))),
% 0.19/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.51  thf('21', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.51           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.51  thf('22', plain,
% 0.19/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.51         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.19/0.51           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.19/0.51      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.51           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X1) @ X0))),
% 0.19/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.19/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]:
% 0.19/0.51         (((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.19/0.51          | (r1_tarski @ (k3_xboole_0 @ X1 @ X1) @ X0))),
% 0.19/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.51        | (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_A) @ sk_B))),
% 0.19/0.51      inference('sup-', [status(thm)], ['18', '25'])).
% 0.19/0.51  thf('27', plain,
% 0.19/0.51      (((k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C) = (sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.51  thf('28', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.19/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.51  thf('29', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.51      inference('sup+', [status(thm)], ['27', '28'])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      (![X5 : $i, X6 : $i]:
% 0.19/0.51         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.19/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      (![X9 : $i, X10 : $i]:
% 0.19/0.51         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.19/0.51           = (k3_xboole_0 @ X9 @ X10))),
% 0.19/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.19/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.19/0.51      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.51  thf('35', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.19/0.51      inference('sup+', [status(thm)], ['31', '34'])).
% 0.19/0.51  thf('36', plain,
% 0.19/0.51      (![X5 : $i, X6 : $i]:
% 0.19/0.51         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.19/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.51  thf('37', plain, (((k3_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.19/0.51      inference('demod', [status(thm)], ['26', '37'])).
% 0.19/0.51  thf('39', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.51      inference('simplify', [status(thm)], ['38'])).
% 0.19/0.51  thf('40', plain, ($false), inference('demod', [status(thm)], ['13', '39'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
