%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GJ1LC8KkDU

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:40 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   24 (  28 expanded)
%              Number of leaves         :   12 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   99 ( 139 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t9_setfam_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t9_setfam_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_setfam_1 @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('3',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_xboole_0 @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ ( k1_setfam_1 @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GJ1LC8KkDU
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 11 iterations in 0.009s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(t9_setfam_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( r2_hidden @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.19/0.46       ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.46        ( ( ( r2_hidden @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.19/0.46          ( r1_xboole_0 @ ( k1_setfam_1 @ B ) @ C ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t9_setfam_1])).
% 0.19/0.46  thf('0', plain, (~ (r1_xboole_0 @ (k1_setfam_1 @ sk_B) @ sk_C)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t4_setfam_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i]:
% 0.19/0.46         ((r1_tarski @ (k1_setfam_1 @ X6) @ X7) | ~ (r2_hidden @ X7 @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.19/0.46  thf('3', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ sk_A)),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain, ((r1_xboole_0 @ sk_A @ sk_C)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t83_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X3 : $i, X4 : $i]:
% 0.19/0.46         (((k4_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.46  thf('6', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf(t106_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.19/0.46       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         ((r1_xboole_0 @ X0 @ X2)
% 0.19/0.46          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_A) | (r1_xboole_0 @ X0 @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.46  thf('9', plain, ((r1_xboole_0 @ (k1_setfam_1 @ sk_B) @ sk_C)),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '8'])).
% 0.19/0.46  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
