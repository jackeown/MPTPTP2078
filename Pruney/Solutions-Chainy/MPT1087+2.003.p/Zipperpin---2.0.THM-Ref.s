%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NLuFucL4lO

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:40 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   16 (  18 expanded)
%              Number of leaves         :    8 (   9 expanded)
%              Depth                    :    4
%              Number of atoms          :   51 (  63 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ A ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_finset_1 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( v1_finset_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_finset_1 @ X0 )
      | ( v1_finset_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t15_finset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_finset_1 @ A )
       => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_finset_1])).

thf('3',plain,(
    ~ ( v1_finset_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['4','5'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NLuFucL4lO
% 0.11/0.30  % Computer   : n016.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 15:07:34 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running portfolio for 600 s
% 0.11/0.31  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.31  % Number of cores: 8
% 0.11/0.31  % Python version: Python 3.6.8
% 0.16/0.31  % Running in FO mode
% 0.16/0.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.16/0.42  % Solved by: fo/fo7.sh
% 0.16/0.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.16/0.42  % done 5 iterations in 0.008s
% 0.16/0.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.16/0.42  % SZS output start Refutation
% 0.16/0.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.16/0.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.16/0.42  thf(sk_A_type, type, sk_A: $i).
% 0.16/0.42  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.16/0.42  thf(sk_B_type, type, sk_B: $i).
% 0.16/0.42  thf(t17_xboole_1, axiom,
% 0.16/0.42    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.16/0.42  thf('0', plain,
% 0.16/0.42      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.16/0.42      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.16/0.42  thf(t13_finset_1, axiom,
% 0.16/0.42    (![A:$i,B:$i]:
% 0.16/0.42     ( ( ( r1_tarski @ A @ B ) & ( v1_finset_1 @ B ) ) => ( v1_finset_1 @ A ) ))).
% 0.16/0.42  thf('1', plain,
% 0.16/0.42      (![X4 : $i, X5 : $i]:
% 0.16/0.42         ((v1_finset_1 @ X4) | ~ (r1_tarski @ X4 @ X5) | ~ (v1_finset_1 @ X5))),
% 0.16/0.42      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.16/0.42  thf('2', plain,
% 0.16/0.42      (![X0 : $i, X1 : $i]:
% 0.16/0.42         (~ (v1_finset_1 @ X0) | (v1_finset_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.16/0.42      inference('sup-', [status(thm)], ['0', '1'])).
% 0.16/0.42  thf(t15_finset_1, conjecture,
% 0.16/0.42    (![A:$i,B:$i]:
% 0.16/0.42     ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.16/0.42  thf(zf_stmt_0, negated_conjecture,
% 0.16/0.42    (~( ![A:$i,B:$i]:
% 0.16/0.42        ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.16/0.42    inference('cnf.neg', [status(esa)], [t15_finset_1])).
% 0.16/0.42  thf('3', plain, (~ (v1_finset_1 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.16/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.42  thf('4', plain, (~ (v1_finset_1 @ sk_A)),
% 0.16/0.42      inference('sup-', [status(thm)], ['2', '3'])).
% 0.16/0.42  thf('5', plain, ((v1_finset_1 @ sk_A)),
% 0.16/0.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.42  thf('6', plain, ($false), inference('demod', [status(thm)], ['4', '5'])).
% 0.16/0.42  
% 0.16/0.42  % SZS output end Refutation
% 0.16/0.42  
% 0.16/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
