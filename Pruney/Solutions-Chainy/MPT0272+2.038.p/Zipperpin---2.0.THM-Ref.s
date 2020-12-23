%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WVYFlQYzty

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:30 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   53 (  72 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  342 ( 485 expanded)
%              Number of equality atoms :   48 (  69 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30
        = ( k1_tarski @ X29 ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf(t69_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t69_zfmisc_1])).

thf('20',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WVYFlQYzty
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.80/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.80/1.00  % Solved by: fo/fo7.sh
% 0.80/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.00  % done 1109 iterations in 0.564s
% 0.80/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.80/1.00  % SZS output start Refutation
% 0.80/1.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.00  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.80/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.80/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.80/1.00  thf(t51_xboole_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.80/1.00       ( A ) ))).
% 0.80/1.00  thf('0', plain,
% 0.80/1.00      (![X21 : $i, X22 : $i]:
% 0.80/1.00         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.80/1.00           = (X21))),
% 0.80/1.00      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.80/1.00  thf(t46_xboole_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.80/1.00  thf('1', plain,
% 0.80/1.00      (![X12 : $i, X13 : $i]:
% 0.80/1.00         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.80/1.00  thf(l32_xboole_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.80/1.00  thf('2', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.80/1.00      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.80/1.00  thf('3', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (((k1_xboole_0) != (k1_xboole_0))
% 0.80/1.00          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/1.00  thf('4', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.80/1.00      inference('simplify', [status(thm)], ['3'])).
% 0.80/1.00  thf('5', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.80/1.00      inference('sup+', [status(thm)], ['0', '4'])).
% 0.80/1.00  thf(l3_zfmisc_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.80/1.00       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.80/1.00  thf('6', plain,
% 0.80/1.00      (![X29 : $i, X30 : $i]:
% 0.80/1.00         (((X30) = (k1_tarski @ X29))
% 0.80/1.00          | ((X30) = (k1_xboole_0))
% 0.80/1.00          | ~ (r1_tarski @ X30 @ (k1_tarski @ X29)))),
% 0.80/1.00      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.80/1.00  thf('7', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.80/1.00          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['5', '6'])).
% 0.80/1.00  thf(t22_xboole_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.80/1.00  thf('8', plain,
% 0.80/1.00      (![X7 : $i, X8 : $i]:
% 0.80/1.00         ((k2_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)) = (X7))),
% 0.80/1.00      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.80/1.00  thf('9', plain,
% 0.80/1.00      (![X12 : $i, X13 : $i]:
% 0.80/1.00         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.80/1.00  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['8', '9'])).
% 0.80/1.00  thf(t49_xboole_1, axiom,
% 0.80/1.00    (![A:$i,B:$i,C:$i]:
% 0.80/1.00     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.80/1.00       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.80/1.00  thf('11', plain,
% 0.80/1.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.80/1.00         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 0.80/1.00           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 0.80/1.00      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.80/1.00  thf('12', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 0.80/1.00           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['10', '11'])).
% 0.80/1.00  thf(t3_boole, axiom,
% 0.80/1.00    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.80/1.00  thf('13', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.80/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.80/1.00  thf(t48_xboole_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.80/1.00  thf('14', plain,
% 0.80/1.00      (![X16 : $i, X17 : $i]:
% 0.80/1.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.80/1.00           = (k3_xboole_0 @ X16 @ X17))),
% 0.80/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.80/1.00  thf('15', plain,
% 0.80/1.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['13', '14'])).
% 0.80/1.00  thf('16', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['8', '9'])).
% 0.80/1.00  thf('17', plain,
% 0.80/1.00      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/1.00      inference('demod', [status(thm)], ['15', '16'])).
% 0.80/1.00  thf('18', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.80/1.00      inference('demod', [status(thm)], ['12', '17'])).
% 0.80/1.00  thf('19', plain,
% 0.80/1.00      (![X0 : $i, X1 : $i]:
% 0.80/1.00         (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.80/1.00          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup+', [status(thm)], ['7', '18'])).
% 0.80/1.00  thf(t69_zfmisc_1, conjecture,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.80/1.00       ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ))).
% 0.80/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.00    (~( ![A:$i,B:$i]:
% 0.80/1.00        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.80/1.00          ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.80/1.00    inference('cnf.neg', [status(esa)], [t69_zfmisc_1])).
% 0.80/1.00  thf('20', plain,
% 0.80/1.00      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('21', plain,
% 0.80/1.00      ((((k1_xboole_0) != (k1_xboole_0))
% 0.80/1.00        | ((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.80/1.00      inference('sup-', [status(thm)], ['19', '20'])).
% 0.80/1.00  thf('22', plain,
% 0.80/1.00      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.80/1.00      inference('simplify', [status(thm)], ['21'])).
% 0.80/1.00  thf(t100_xboole_1, axiom,
% 0.80/1.00    (![A:$i,B:$i]:
% 0.80/1.00     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.80/1.00  thf('23', plain,
% 0.80/1.00      (![X3 : $i, X4 : $i]:
% 0.80/1.00         ((k4_xboole_0 @ X3 @ X4)
% 0.80/1.00           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.00  thf('24', plain,
% 0.80/1.00      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.80/1.00         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['22', '23'])).
% 0.80/1.00  thf('25', plain,
% 0.80/1.00      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/1.00      inference('demod', [status(thm)], ['15', '16'])).
% 0.80/1.00  thf('26', plain,
% 0.80/1.00      (![X3 : $i, X4 : $i]:
% 0.80/1.00         ((k4_xboole_0 @ X3 @ X4)
% 0.80/1.00           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.80/1.00      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.00  thf('27', plain,
% 0.80/1.00      (![X0 : $i]:
% 0.80/1.00         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['25', '26'])).
% 0.80/1.00  thf('28', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.80/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.80/1.00  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.80/1.00      inference('sup+', [status(thm)], ['27', '28'])).
% 0.80/1.00  thf('30', plain,
% 0.80/1.00      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.80/1.00      inference('demod', [status(thm)], ['24', '29'])).
% 0.80/1.00  thf('31', plain,
% 0.80/1.00      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.80/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.00  thf('32', plain, ($false),
% 0.80/1.00      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.80/1.00  
% 0.80/1.00  % SZS output end Refutation
% 0.80/1.00  
% 0.80/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
