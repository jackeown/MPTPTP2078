%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IrqIFkdqrP

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  92 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  344 ( 614 expanded)
%              Number of equality atoms :   28 (  43 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference('sup+',[status(thm)],['4','7'])).

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
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('30',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['21','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['14','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['13','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IrqIFkdqrP
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 190 iterations in 0.086s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(t106_xboole_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.57       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.57        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.57          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('2', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t28_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.57  thf(t49_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.21/0.57       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.57  thf(t79_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.21/0.57      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 0.21/0.57      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.57  thf('8', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.21/0.57      inference('sup+', [status(thm)], ['4', '7'])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      ((~ (r1_xboole_0 @ sk_A @ sk_C)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('10', plain, (((r1_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('12', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('13', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.57  thf(t36_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.21/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.57  thf(l32_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X2 : $i, X4 : $i]:
% 0.21/0.57         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i]:
% 0.21/0.57         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.21/0.57          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X2 @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.21/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.57           = (k4_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ k1_xboole_0 @ 
% 0.21/0.57           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.21/0.57           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i]:
% 0.21/0.57         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.57  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i]:
% 0.21/0.57         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57          | (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['21', '37'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (r1_tarski @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X0)),
% 0.21/0.57      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.57  thf('40', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.57      inference('sup+', [status(thm)], ['14', '39'])).
% 0.21/0.57  thf('41', plain, ($false), inference('demod', [status(thm)], ['13', '40'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
