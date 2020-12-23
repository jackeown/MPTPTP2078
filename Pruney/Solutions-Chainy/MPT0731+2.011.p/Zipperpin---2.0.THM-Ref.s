%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TbdBOHdjZc

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    5
%              Number of atoms          :   74 (  82 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t14_ordinal1,conjecture,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( A
       != ( k1_ordinal1 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t14_ordinal1])).

thf('0',plain,
    ( sk_A
    = ( k1_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( sk_A
    = ( k1_ordinal1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k1_ordinal1 @ X5 )
      = ( k2_xboole_0 @ X5 @ ( k1_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['4','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TbdBOHdjZc
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 9 iterations in 0.008s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(t14_ordinal1, conjecture, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t14_ordinal1])).
% 0.21/0.46  thf('0', plain, (((sk_A) = (k1_ordinal1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.21/0.46  thf('1', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_ordinal1 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.21/0.46  thf('2', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.21/0.46      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf(t7_ordinal1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.46  thf('4', plain, (~ (r1_tarski @ sk_A @ sk_A)),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf('5', plain, (((sk_A) = (k1_ordinal1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d1_ordinal1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X5 : $i]: ((k1_ordinal1 @ X5) = (k2_xboole_0 @ X5 @ (k1_tarski @ X5)))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.21/0.46  thf(t7_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.46  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.21/0.46      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.46  thf('10', plain, ($false), inference('demod', [status(thm)], ['4', '9'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
