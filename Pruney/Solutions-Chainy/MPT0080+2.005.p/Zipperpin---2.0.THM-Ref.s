%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fSocL4S3Zm

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:04 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   56 (  67 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  328 ( 422 expanded)
%              Number of equality atoms :   32 (  37 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['3','22','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fSocL4S3Zm
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:48:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.77/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.97  % Solved by: fo/fo7.sh
% 0.77/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.97  % done 1399 iterations in 0.529s
% 0.77/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.97  % SZS output start Refutation
% 0.77/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.77/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.97  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.97  thf(t73_xboole_1, conjecture,
% 0.77/0.97    (![A:$i,B:$i,C:$i]:
% 0.77/0.97     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.77/0.97       ( r1_tarski @ A @ B ) ))).
% 0.77/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.77/0.97        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.77/0.97            ( r1_xboole_0 @ A @ C ) ) =>
% 0.77/0.97          ( r1_tarski @ A @ B ) ) )),
% 0.77/0.97    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.77/0.97  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf(t28_xboole_1, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.77/0.97  thf('2', plain,
% 0.77/0.97      (![X14 : $i, X15 : $i]:
% 0.77/0.97         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.77/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.97  thf('3', plain,
% 0.77/0.97      (((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 0.77/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.97  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf(d7_xboole_0, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.77/0.97       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.77/0.97  thf('5', plain,
% 0.77/0.97      (![X4 : $i, X5 : $i]:
% 0.77/0.97         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.77/0.97      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.77/0.97  thf('6', plain, (((k3_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.77/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/0.97  thf('7', plain,
% 0.77/0.97      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.97  thf('8', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['6', '7'])).
% 0.77/0.97  thf('9', plain,
% 0.77/0.97      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.97  thf(t23_xboole_1, axiom,
% 0.77/0.97    (![A:$i,B:$i,C:$i]:
% 0.77/0.97     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.77/0.97       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.77/0.97  thf('10', plain,
% 0.77/0.97      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.97         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 0.77/0.97           = (k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ 
% 0.77/0.97              (k3_xboole_0 @ X11 @ X13)))),
% 0.77/0.97      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.77/0.97  thf('11', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.97         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1))
% 0.77/0.97           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['9', '10'])).
% 0.77/0.97  thf('12', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C))
% 0.77/0.97           = (k2_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ k1_xboole_0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['8', '11'])).
% 0.77/0.97  thf(idempotence_k2_xboole_0, axiom,
% 0.77/0.97    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/0.97  thf('13', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 0.77/0.97      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.77/0.97  thf(t7_xboole_1, axiom,
% 0.77/0.97    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.97  thf('14', plain,
% 0.77/0.97      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.77/0.97      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/0.97  thf('15', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.77/0.97      inference('sup+', [status(thm)], ['13', '14'])).
% 0.77/0.97  thf(l32_xboole_1, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/0.97  thf('16', plain,
% 0.77/0.97      (![X8 : $i, X10 : $i]:
% 0.77/0.97         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 0.77/0.97      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.77/0.97  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['15', '16'])).
% 0.77/0.97  thf(t39_xboole_1, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.77/0.97  thf('18', plain,
% 0.77/0.97      (![X16 : $i, X17 : $i]:
% 0.77/0.97         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.77/0.97           = (k2_xboole_0 @ X16 @ X17))),
% 0.77/0.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.77/0.97  thf('19', plain,
% 0.77/0.97      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['17', '18'])).
% 0.77/0.97  thf('20', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ X7) = (X7))),
% 0.77/0.97      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.77/0.97  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.77/0.97      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/0.97  thf('22', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         ((k3_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C))
% 0.77/0.97           = (k3_xboole_0 @ sk_A @ X0))),
% 0.77/0.97      inference('demod', [status(thm)], ['12', '21'])).
% 0.77/0.97  thf('23', plain,
% 0.77/0.97      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.77/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.97  thf('24', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.77/0.97      inference('demod', [status(thm)], ['3', '22', '23'])).
% 0.77/0.97  thf('25', plain,
% 0.77/0.97      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.77/0.97      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/0.97  thf('26', plain,
% 0.77/0.97      (![X14 : $i, X15 : $i]:
% 0.77/0.97         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.77/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.97  thf('27', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.77/0.97      inference('sup-', [status(thm)], ['25', '26'])).
% 0.77/0.97  thf('28', plain,
% 0.77/0.97      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.77/0.97         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 0.77/0.97           = (k2_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ 
% 0.77/0.97              (k3_xboole_0 @ X11 @ X13)))),
% 0.77/0.97      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.77/0.97  thf(commutativity_k2_xboole_0, axiom,
% 0.77/0.97    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.77/0.97  thf('29', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.77/0.97      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.77/0.97  thf('30', plain,
% 0.77/0.97      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 0.77/0.97      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.77/0.97  thf('31', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['29', '30'])).
% 0.77/0.97  thf('32', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.97         (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ 
% 0.77/0.97          (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['28', '31'])).
% 0.77/0.97  thf('33', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.77/0.97      inference('sup+', [status(thm)], ['27', '32'])).
% 0.77/0.97  thf('34', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.77/0.97      inference('sup+', [status(thm)], ['24', '33'])).
% 0.77/0.97  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.77/0.97  
% 0.77/0.97  % SZS output end Refutation
% 0.77/0.97  
% 0.77/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
