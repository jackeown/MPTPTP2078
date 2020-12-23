%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zJHE5YfUXD

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:48 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  307 ( 449 expanded)
%              Number of equality atoms :   30 (  40 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t86_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['12','23'])).

thf('25',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zJHE5YfUXD
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:36:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.49/1.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.49/1.69  % Solved by: fo/fo7.sh
% 1.49/1.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.49/1.69  % done 2742 iterations in 1.245s
% 1.49/1.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.49/1.69  % SZS output start Refutation
% 1.49/1.69  thf(sk_C_type, type, sk_C: $i).
% 1.49/1.69  thf(sk_B_type, type, sk_B: $i).
% 1.49/1.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.49/1.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.49/1.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.49/1.69  thf(sk_A_type, type, sk_A: $i).
% 1.49/1.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.49/1.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.49/1.69  thf(t86_xboole_1, conjecture,
% 1.49/1.69    (![A:$i,B:$i,C:$i]:
% 1.49/1.69     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.49/1.69       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 1.49/1.69  thf(zf_stmt_0, negated_conjecture,
% 1.49/1.69    (~( ![A:$i,B:$i,C:$i]:
% 1.49/1.69        ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.49/1.69          ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )),
% 1.49/1.69    inference('cnf.neg', [status(esa)], [t86_xboole_1])).
% 1.49/1.69  thf('0', plain, (~ (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.49/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.69  thf(t3_boole, axiom,
% 1.49/1.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.49/1.69  thf('1', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.49/1.69      inference('cnf', [status(esa)], [t3_boole])).
% 1.49/1.69  thf(t36_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.49/1.69  thf('2', plain,
% 1.49/1.69      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 1.49/1.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.49/1.69  thf('3', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.49/1.69      inference('sup+', [status(thm)], ['1', '2'])).
% 1.49/1.69  thf(l32_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.49/1.69  thf('4', plain,
% 1.49/1.69      (![X0 : $i, X2 : $i]:
% 1.49/1.69         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 1.49/1.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.49/1.69  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.49/1.69      inference('sup-', [status(thm)], ['3', '4'])).
% 1.49/1.69  thf(t41_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i,C:$i]:
% 1.49/1.69     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.49/1.69       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.49/1.69  thf('6', plain,
% 1.49/1.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.49/1.69         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.49/1.69           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.49/1.69      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.49/1.69  thf('7', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k1_xboole_0)
% 1.49/1.69           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.49/1.69      inference('sup+', [status(thm)], ['5', '6'])).
% 1.49/1.69  thf('8', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 1.49/1.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.49/1.69  thf('9', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         (((k1_xboole_0) != (k1_xboole_0))
% 1.49/1.69          | (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.49/1.69      inference('sup-', [status(thm)], ['7', '8'])).
% 1.49/1.69  thf('10', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.49/1.69      inference('simplify', [status(thm)], ['9'])).
% 1.49/1.69  thf(t12_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.49/1.69  thf('11', plain,
% 1.49/1.69      (![X3 : $i, X4 : $i]:
% 1.49/1.69         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.49/1.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.49/1.69  thf('12', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.49/1.69           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.49/1.69      inference('sup-', [status(thm)], ['10', '11'])).
% 1.49/1.69  thf('13', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.49/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.69  thf('14', plain,
% 1.49/1.69      (![X0 : $i, X2 : $i]:
% 1.49/1.69         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 1.49/1.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.49/1.69  thf('15', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.49/1.69      inference('sup-', [status(thm)], ['13', '14'])).
% 1.49/1.69  thf('16', plain,
% 1.49/1.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.49/1.69         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.49/1.69           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.49/1.69      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.49/1.69  thf('17', plain,
% 1.49/1.69      (![X0 : $i]:
% 1.49/1.69         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.49/1.69           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.49/1.69      inference('sup+', [status(thm)], ['15', '16'])).
% 1.49/1.69  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.49/1.69      inference('sup-', [status(thm)], ['3', '4'])).
% 1.49/1.69  thf('19', plain,
% 1.49/1.69      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 1.49/1.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.49/1.69  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.49/1.69      inference('sup+', [status(thm)], ['18', '19'])).
% 1.49/1.69  thf('21', plain,
% 1.49/1.69      (![X0 : $i, X2 : $i]:
% 1.49/1.69         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 1.49/1.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.49/1.69  thf('22', plain,
% 1.49/1.69      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.49/1.69      inference('sup-', [status(thm)], ['20', '21'])).
% 1.49/1.69  thf('23', plain,
% 1.49/1.69      (![X0 : $i]:
% 1.49/1.69         ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.49/1.69      inference('demod', [status(thm)], ['17', '22'])).
% 1.49/1.69  thf('24', plain,
% 1.49/1.69      (![X0 : $i]:
% 1.49/1.69         ((k1_xboole_0)
% 1.49/1.69           = (k4_xboole_0 @ sk_A @ 
% 1.49/1.69              (k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ X0))))),
% 1.49/1.69      inference('sup+', [status(thm)], ['12', '23'])).
% 1.49/1.69  thf('25', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 1.49/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.49/1.69  thf(t83_xboole_1, axiom,
% 1.49/1.69    (![A:$i,B:$i]:
% 1.49/1.69     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.49/1.69  thf('26', plain,
% 1.49/1.69      (![X11 : $i, X12 : $i]:
% 1.49/1.69         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 1.49/1.69      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.49/1.69  thf('27', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 1.49/1.69      inference('sup-', [status(thm)], ['25', '26'])).
% 1.49/1.69  thf('28', plain,
% 1.49/1.69      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.49/1.69         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 1.49/1.69           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 1.49/1.69      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.49/1.69  thf('29', plain,
% 1.49/1.69      (![X0 : $i]:
% 1.49/1.69         ((k4_xboole_0 @ sk_A @ X0)
% 1.49/1.69           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ X0)))),
% 1.49/1.69      inference('sup+', [status(thm)], ['27', '28'])).
% 1.49/1.69  thf('30', plain,
% 1.49/1.69      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 1.49/1.69      inference('sup+', [status(thm)], ['24', '29'])).
% 1.49/1.69  thf('31', plain,
% 1.49/1.69      (![X0 : $i, X1 : $i]:
% 1.49/1.69         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 1.49/1.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.49/1.69  thf('32', plain,
% 1.49/1.69      ((((k1_xboole_0) != (k1_xboole_0))
% 1.49/1.69        | (r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 1.49/1.69      inference('sup-', [status(thm)], ['30', '31'])).
% 1.49/1.69  thf('33', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))),
% 1.49/1.69      inference('simplify', [status(thm)], ['32'])).
% 1.49/1.69  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 1.49/1.69  
% 1.49/1.69  % SZS output end Refutation
% 1.49/1.69  
% 1.49/1.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
