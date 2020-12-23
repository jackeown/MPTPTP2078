%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mB3V6wuAI7

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  61 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  328 ( 416 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t85_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X21 )
      | ( ( k4_xboole_0 @ X19 @ X21 )
       != X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X1 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ X2 ) @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( r1_xboole_0 @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X3 @ X3 ) @ ( k4_xboole_0 @ X2 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X17 @ ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_xboole_0 @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X1 @ X3 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X2 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X17 @ ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mB3V6wuAI7
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 58 iterations in 0.035s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(t85_xboole_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( r1_tarski @ A @ B ) =>
% 0.20/0.49          ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t85_xboole_1])).
% 0.20/0.49  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t7_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.49  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t1_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.20/0.49       ( r1_tarski @ A @ C ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.49          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.49          | (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.49  thf(t43_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.20/0.49       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.49          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.49  thf('7', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf(t21_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.20/0.49  thf(t48_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.20/0.49           = (k3_xboole_0 @ X8 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.49  thf(t83_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X19 : $i, X21 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X19 @ X21) | ((k4_xboole_0 @ X19 @ X21) != (X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X1 @ X0) != (X1))
% 0.20/0.49          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((X0) != (X0))
% 0.20/0.49          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         ((r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.49          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf(t64_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.20/0.49         ( r1_xboole_0 @ B @ D ) ) =>
% 0.20/0.49       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X10 @ X11)
% 0.20/0.49          | ~ (r1_tarski @ X10 @ X12)
% 0.20/0.49          | ~ (r1_tarski @ X11 @ X13)
% 0.20/0.49          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.49          | ~ (r1_tarski @ X3 @ X2)
% 0.20/0.49          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X3))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k4_xboole_0 @ X2 @ X2) @ (k4_xboole_0 @ X1 @ X1))
% 0.20/0.49          | ~ (r1_xboole_0 @ X3 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]:
% 0.20/0.49         (r1_xboole_0 @ (k4_xboole_0 @ X3 @ X3) @ (k4_xboole_0 @ X2 @ X2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '20'])).
% 0.20/0.49  thf(t81_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.20/0.49       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.20/0.49          | ~ (r1_xboole_0 @ X17 @ (k4_xboole_0 @ X16 @ X18)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X10 @ X11)
% 0.20/0.49          | ~ (r1_tarski @ X10 @ X12)
% 0.20/0.49          | ~ (r1_tarski @ X11 @ X13)
% 0.20/0.49          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.20/0.49          | ~ (r1_tarski @ X3 @ X2)
% 0.20/0.49          | (r1_xboole_0 @ X1 @ X3))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X1 @ X3)
% 0.20/0.49          | ~ (r1_tarski @ X3 @ 
% 0.20/0.49               (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X2) @ (k2_xboole_0 @ X1 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X1 : $i]: (r1_xboole_0 @ X1 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.20/0.49          | ~ (r1_xboole_0 @ X17 @ (k4_xboole_0 @ X16 @ X18)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
