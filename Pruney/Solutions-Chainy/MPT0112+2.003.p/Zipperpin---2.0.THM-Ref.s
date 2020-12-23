%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eilIhiqUuh

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:26 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 (  82 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  307 ( 491 expanded)
%              Number of equality atoms :   40 (  60 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t105_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ( ( k4_xboole_0 @ B @ A )
          = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r2_xboole_0 @ A @ B )
          & ( ( k4_xboole_0 @ B @ A )
            = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t105_xboole_1])).

thf('0',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['18','19','20','21','24'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('31',plain,(
    sk_B = sk_A ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_xboole_0 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['0','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4 != X5 )
      | ~ ( r2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('34',plain,(
    ! [X5: $i] :
      ~ ( r2_xboole_0 @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['32','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eilIhiqUuh
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 62 iterations in 0.030s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(t105_xboole_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.19/0.48          ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.19/0.48             ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t105_xboole_1])).
% 0.19/0.48  thf('0', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(d8_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.19/0.48       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ~ (r2_xboole_0 @ X4 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.19/0.48  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf(t28_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.48  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.48  thf(t100_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X7 @ X8)
% 0.19/0.48           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X0 @ X1)
% 0.19/0.48           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['5', '8'])).
% 0.19/0.48  thf('10', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(commutativity_k5_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.48  thf('12', plain, (((k1_xboole_0) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.19/0.48  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X7 : $i, X8 : $i]:
% 0.19/0.48         ((k4_xboole_0 @ X7 @ X8)
% 0.19/0.48           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf(t91_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.19/0.48       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.48         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.19/0.48           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.19/0.48           = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.19/0.48         = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['12', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.48  thf(t98_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i]:
% 0.19/0.48         ((k2_xboole_0 @ X19 @ X20)
% 0.19/0.48           = (k5_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.19/0.48  thf(t5_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.48  thf('23', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.48  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.48      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['18', '19', '20', '21', '24'])).
% 0.19/0.48  thf(t21_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]:
% 0.19/0.48         ((k3_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.19/0.48  thf('27', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.48  thf('29', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.19/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.48  thf('30', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('31', plain, (((sk_B) = (sk_A))),
% 0.19/0.48      inference('sup+', [status(thm)], ['29', '30'])).
% 0.19/0.48  thf('32', plain, ((r2_xboole_0 @ sk_A @ sk_A)),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]: (((X4) != (X5)) | ~ (r2_xboole_0 @ X4 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.19/0.48  thf('34', plain, (![X5 : $i]: ~ (r2_xboole_0 @ X5 @ X5)),
% 0.19/0.48      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.48  thf('35', plain, ($false), inference('sup-', [status(thm)], ['32', '34'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
