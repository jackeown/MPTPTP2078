%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Y9TxmoFT4

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:22 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   49 (  71 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  315 ( 451 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t53_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('12',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','27','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Y9TxmoFT4
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 311 iterations in 0.133s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(t53_xboole_1, conjecture,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.39/0.58       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.58        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.39/0.58          ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t53_xboole_1])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.39/0.58         != (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.39/0.58             (k4_xboole_0 @ sk_A @ sk_C)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t49_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.39/0.58       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.58         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 0.39/0.58           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 0.39/0.58      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.39/0.58         != (k4_xboole_0 @ 
% 0.39/0.58             (k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A) @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['0', '1'])).
% 0.39/0.58  thf(t36_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.39/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.58  thf(t12_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i]:
% 0.39/0.58         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.58  thf(t39_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.39/0.58           = (k2_xboole_0 @ X8 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.58  thf('7', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i]:
% 0.39/0.58         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.58  thf('9', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['6', '9'])).
% 0.39/0.58  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf('12', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 0.39/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.39/0.58  thf('14', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.39/0.58      inference('sup+', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf(l32_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X0 : $i, X2 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.58  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf(t41_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.39/0.58       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.39/0.58           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.58           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['16', '17'])).
% 0.39/0.58  thf('19', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X0 : $i, X2 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['18', '21'])).
% 0.39/0.58  thf(t48_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.39/0.58           = (k3_xboole_0 @ X13 @ X14))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 0.39/0.58           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['22', '23'])).
% 0.39/0.58  thf('25', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['10', '11'])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X0 @ X1)
% 0.39/0.58           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.39/0.58      inference('sup+', [status(thm)], ['5', '26'])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.39/0.58           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.39/0.58         != (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['2', '27', '28'])).
% 0.39/0.58  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
