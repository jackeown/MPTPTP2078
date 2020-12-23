%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wpwbYhL1pY

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   18 (  18 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    4
%              Number of atoms          :   76 (  76 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t29_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t29_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['2','5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wpwbYhL1pY
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 5 iterations in 0.006s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.45  thf(t29_xboole_1, conjecture,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.45        ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t29_xboole_1])).
% 0.21/0.45  thf('0', plain,
% 0.21/0.45      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_C @ sk_A))),
% 0.21/0.45      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.45  thf(t17_xboole_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.21/0.45      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.45  thf(t10_xboole_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.45         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.45  thf('6', plain, ($false), inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
