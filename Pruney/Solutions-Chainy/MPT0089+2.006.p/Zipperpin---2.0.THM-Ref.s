%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4U0N139Hbz

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   20 (  20 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :   92 (  92 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t82_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t82_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 )
      | ( r1_xboole_0 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['0','7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4U0N139Hbz
% 0.16/0.37  % Computer   : n018.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 17:28:12 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 8 iterations in 0.009s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(t82_xboole_1, conjecture,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i]:
% 0.23/0.49        ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t82_xboole_1])).
% 0.23/0.49  thf('0', plain,
% 0.23/0.49      (~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.23/0.49          (k4_xboole_0 @ sk_B @ sk_A))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t79_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X7 : $i, X8 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X8)),
% 0.23/0.49      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.23/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.23/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.49  thf(t36_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.23/0.49  thf('4', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i]: (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X2)),
% 0.23/0.49      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.23/0.49  thf(t63_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.23/0.49       ( r1_xboole_0 @ A @ C ) ))).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.49         (~ (r1_tarski @ X4 @ X5)
% 0.23/0.49          | ~ (r1_xboole_0 @ X5 @ X6)
% 0.23/0.49          | (r1_xboole_0 @ X4 @ X6))),
% 0.23/0.49      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 0.23/0.49          | ~ (r1_xboole_0 @ X0 @ X2))),
% 0.23/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ (k4_xboole_0 @ X1 @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['3', '6'])).
% 0.23/0.49  thf('8', plain, ($false), inference('demod', [status(thm)], ['0', '7'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
