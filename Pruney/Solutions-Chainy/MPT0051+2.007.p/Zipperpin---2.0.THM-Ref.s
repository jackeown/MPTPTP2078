%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zDRZhT2Zy6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:05 EST 2020

% Result     : Theorem 24.32s
% Output     : Refutation 24.32s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  207 ( 237 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t44_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
       => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k4_xboole_0 @ X11 @ X10 ) @ ( k4_xboole_0 @ X11 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) @ X3 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X1 ) ) @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ ( k4_xboole_0 @ X11 @ X10 ) @ ( k4_xboole_0 @ X11 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ sk_C ) ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['0','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zDRZhT2Zy6
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:31:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 24.32/24.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 24.32/24.56  % Solved by: fo/fo7.sh
% 24.32/24.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.32/24.56  % done 16820 iterations in 24.097s
% 24.32/24.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 24.32/24.56  % SZS output start Refutation
% 24.32/24.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 24.32/24.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 24.32/24.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 24.32/24.56  thf(sk_A_type, type, sk_A: $i).
% 24.32/24.56  thf(sk_C_type, type, sk_C: $i).
% 24.32/24.56  thf(sk_B_type, type, sk_B: $i).
% 24.32/24.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 24.32/24.56  thf(t44_xboole_1, conjecture,
% 24.32/24.56    (![A:$i,B:$i,C:$i]:
% 24.32/24.56     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 24.32/24.56       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 24.32/24.56  thf(zf_stmt_0, negated_conjecture,
% 24.32/24.56    (~( ![A:$i,B:$i,C:$i]:
% 24.32/24.56        ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 24.32/24.56          ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )),
% 24.32/24.56    inference('cnf.neg', [status(esa)], [t44_xboole_1])).
% 24.32/24.56  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 24.32/24.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.56  thf('1', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 24.32/24.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.32/24.56  thf(t10_xboole_1, axiom,
% 24.32/24.56    (![A:$i,B:$i,C:$i]:
% 24.32/24.56     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 24.32/24.56  thf('2', plain,
% 24.32/24.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 24.32/24.56         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 24.32/24.56      inference('cnf', [status(esa)], [t10_xboole_1])).
% 24.32/24.56  thf('3', plain,
% 24.32/24.56      (![X0 : $i]:
% 24.32/24.56         (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ (k2_xboole_0 @ X0 @ sk_C))),
% 24.32/24.56      inference('sup-', [status(thm)], ['1', '2'])).
% 24.32/24.56  thf(t7_xboole_1, axiom,
% 24.32/24.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 24.32/24.56  thf('4', plain,
% 24.32/24.56      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 24.32/24.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 24.32/24.56  thf(t34_xboole_1, axiom,
% 24.32/24.56    (![A:$i,B:$i,C:$i]:
% 24.32/24.56     ( ( r1_tarski @ A @ B ) =>
% 24.32/24.56       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 24.32/24.56  thf('5', plain,
% 24.32/24.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 24.32/24.56         (~ (r1_tarski @ X9 @ X10)
% 24.32/24.56          | (r1_tarski @ (k4_xboole_0 @ X11 @ X10) @ (k4_xboole_0 @ X11 @ X9)))),
% 24.32/24.56      inference('cnf', [status(esa)], [t34_xboole_1])).
% 24.32/24.56  thf('6', plain,
% 24.32/24.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.32/24.56         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 24.32/24.56          (k4_xboole_0 @ X2 @ X1))),
% 24.32/24.56      inference('sup-', [status(thm)], ['4', '5'])).
% 24.32/24.56  thf(t1_xboole_1, axiom,
% 24.32/24.56    (![A:$i,B:$i,C:$i]:
% 24.32/24.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 24.32/24.56       ( r1_tarski @ A @ C ) ))).
% 24.32/24.56  thf('7', plain,
% 24.32/24.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 24.32/24.56         (~ (r1_tarski @ X6 @ X7)
% 24.32/24.56          | ~ (r1_tarski @ X7 @ X8)
% 24.32/24.56          | (r1_tarski @ X6 @ X8))),
% 24.32/24.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 24.32/24.56  thf('8', plain,
% 24.32/24.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 24.32/24.56         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)) @ X3)
% 24.32/24.56          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X3))),
% 24.32/24.56      inference('sup-', [status(thm)], ['6', '7'])).
% 24.32/24.56  thf('9', plain,
% 24.32/24.56      (![X0 : $i, X1 : $i]:
% 24.32/24.56         (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X1)) @ 
% 24.32/24.56          (k2_xboole_0 @ X0 @ sk_C))),
% 24.32/24.56      inference('sup-', [status(thm)], ['3', '8'])).
% 24.32/24.56  thf('10', plain,
% 24.32/24.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 24.32/24.56         (~ (r1_tarski @ X9 @ X10)
% 24.32/24.56          | (r1_tarski @ (k4_xboole_0 @ X11 @ X10) @ (k4_xboole_0 @ X11 @ X9)))),
% 24.32/24.56      inference('cnf', [status(esa)], [t34_xboole_1])).
% 24.32/24.56  thf('11', plain,
% 24.32/24.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.32/24.56         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ sk_C)) @ 
% 24.32/24.56          (k4_xboole_0 @ X2 @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ X1))))),
% 24.32/24.56      inference('sup-', [status(thm)], ['9', '10'])).
% 24.32/24.56  thf(t38_xboole_1, axiom,
% 24.32/24.56    (![A:$i,B:$i]:
% 24.32/24.56     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 24.32/24.56       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 24.32/24.56  thf('12', plain,
% 24.32/24.56      (![X12 : $i, X13 : $i]:
% 24.32/24.56         (((X12) = (k1_xboole_0))
% 24.32/24.56          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 24.32/24.56      inference('cnf', [status(esa)], [t38_xboole_1])).
% 24.32/24.56  thf('13', plain,
% 24.32/24.56      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)) = (k1_xboole_0))),
% 24.32/24.56      inference('sup-', [status(thm)], ['11', '12'])).
% 24.32/24.56  thf(l32_xboole_1, axiom,
% 24.32/24.56    (![A:$i,B:$i]:
% 24.32/24.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 24.32/24.56  thf('14', plain,
% 24.32/24.56      (![X0 : $i, X1 : $i]:
% 24.32/24.56         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 24.32/24.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 24.32/24.56  thf('15', plain,
% 24.32/24.56      ((((k1_xboole_0) != (k1_xboole_0))
% 24.32/24.56        | (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 24.32/24.56      inference('sup-', [status(thm)], ['13', '14'])).
% 24.32/24.56  thf('16', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 24.32/24.56      inference('simplify', [status(thm)], ['15'])).
% 24.32/24.56  thf('17', plain, ($false), inference('demod', [status(thm)], ['0', '16'])).
% 24.32/24.56  
% 24.32/24.56  % SZS output end Refutation
% 24.32/24.56  
% 24.40/24.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
