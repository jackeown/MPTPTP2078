%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.35sVYwecKJ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:48 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  141 ( 193 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t13_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X1 ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_C ) @ ( k2_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['0','11'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.35sVYwecKJ
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:14:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.88/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.88/1.06  % Solved by: fo/fo7.sh
% 0.88/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.88/1.06  % done 734 iterations in 0.604s
% 0.88/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.88/1.06  % SZS output start Refutation
% 0.88/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.88/1.06  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.88/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.88/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.88/1.06  thf(sk_D_type, type, sk_D: $i).
% 0.88/1.06  thf(sk_C_type, type, sk_C: $i).
% 0.88/1.06  thf(t13_xboole_1, conjecture,
% 0.88/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.88/1.06     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.88/1.06       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 0.88/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.88/1.06    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.88/1.06        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.88/1.06          ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )),
% 0.88/1.06    inference('cnf.neg', [status(esa)], [t13_xboole_1])).
% 0.88/1.06  thf('0', plain,
% 0.88/1.06      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_D))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('1', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(t10_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.88/1.06  thf('2', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.88/1.06      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.88/1.06  thf('3', plain, (![X0 : $i]: (r1_tarski @ sk_C @ (k2_xboole_0 @ X0 @ sk_D))),
% 0.88/1.06      inference('sup-', [status(thm)], ['1', '2'])).
% 0.88/1.06  thf(t7_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.88/1.06  thf('4', plain,
% 0.88/1.06      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.88/1.06      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.88/1.06  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(t1_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.88/1.06       ( r1_tarski @ A @ C ) ))).
% 0.88/1.06  thf('6', plain,
% 0.88/1.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X3 @ X4)
% 0.88/1.06          | ~ (r1_tarski @ X4 @ X5)
% 0.88/1.06          | (r1_tarski @ X3 @ X5))),
% 0.88/1.06      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.88/1.06  thf('7', plain,
% 0.88/1.06      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['5', '6'])).
% 0.88/1.06  thf('8', plain, (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.88/1.06      inference('sup-', [status(thm)], ['4', '7'])).
% 0.88/1.06  thf(t8_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.88/1.06       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.88/1.06  thf('9', plain,
% 0.88/1.06      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X8 @ X9)
% 0.88/1.06          | ~ (r1_tarski @ X10 @ X9)
% 0.88/1.06          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.88/1.06      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.88/1.06  thf('10', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]:
% 0.88/1.06         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X1) @ (k2_xboole_0 @ sk_B @ X0))
% 0.88/1.06          | ~ (r1_tarski @ X1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['8', '9'])).
% 0.88/1.06  thf('11', plain,
% 0.88/1.06      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_C) @ (k2_xboole_0 @ sk_B @ sk_D))),
% 0.88/1.06      inference('sup-', [status(thm)], ['3', '10'])).
% 0.88/1.06  thf('12', plain, ($false), inference('demod', [status(thm)], ['0', '11'])).
% 0.88/1.06  
% 0.88/1.06  % SZS output end Refutation
% 0.88/1.06  
% 0.88/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
