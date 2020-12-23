%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JfVGxluBHO

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:46 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   19 (  21 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :   83 (  99 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t10_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ),
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
    ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['2','7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JfVGxluBHO
% 0.14/0.37  % Computer   : n019.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 10:00:08 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 9 iterations in 0.010s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.49  thf(t10_xboole_1, conjecture,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.49        ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t10_xboole_1])).
% 0.23/0.49  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(commutativity_k2_xboole_0, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.23/0.49  thf('2', plain, (~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 0.23/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.49  thf(t7_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.23/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.23/0.49  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t1_xboole_1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.23/0.49       ( r1_tarski @ A @ C ) ))).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.23/0.49         (~ (r1_tarski @ X2 @ X3)
% 0.23/0.49          | ~ (r1_tarski @ X3 @ X4)
% 0.23/0.49          | (r1_tarski @ X2 @ X4))),
% 0.23/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.23/0.49  thf('6', plain,
% 0.23/0.49      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.49  thf('7', plain, (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['3', '6'])).
% 0.23/0.49  thf('8', plain, ($false), inference('demod', [status(thm)], ['2', '7'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
