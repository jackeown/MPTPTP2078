%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iiRpJnPuE4

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  19 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :   71 (  87 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t109_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t109_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
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
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['0','5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iiRpJnPuE4
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:54:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 6 iterations in 0.005s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.45  thf(t109_xboole_1, conjecture,
% 0.22/0.45    (![A:$i,B:$i,C:$i]:
% 0.22/0.45     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.45        ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t109_xboole_1])).
% 0.22/0.45  thf('0', plain, (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(t10_xboole_1, axiom,
% 0.22/0.45    (![A:$i,B:$i,C:$i]:
% 0.22/0.45     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.22/0.45  thf('2', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.45         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.22/0.45      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.22/0.45  thf('3', plain, (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.22/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.45  thf(t43_xboole_1, axiom,
% 0.22/0.45    (![A:$i,B:$i,C:$i]:
% 0.22/0.45     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.22/0.45       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.22/0.45  thf('4', plain,
% 0.22/0.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.45         ((r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X5)
% 0.22/0.45          | ~ (r1_tarski @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.22/0.45      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.22/0.45  thf('5', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ sk_B)),
% 0.22/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.45  thf('6', plain, ($false), inference('demod', [status(thm)], ['0', '5'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
