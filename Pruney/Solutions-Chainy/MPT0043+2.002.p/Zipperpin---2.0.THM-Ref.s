%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qgp3H3X45R

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   19 (  20 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    6
%              Number of atoms          :  101 ( 110 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t36_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) ),
    inference('cnf.neg',[status(esa)],[t36_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['0','7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qgp3H3X45R
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 9 iterations in 0.007s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(t36_xboole_1, conjecture,
% 0.21/0.45    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t36_xboole_1])).
% 0.21/0.45  thf('0', plain, (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(d3_tarski, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.45       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      (![X1 : $i, X3 : $i]:
% 0.21/0.45         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.45  thf(d5_xboole_0, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.45       ( ![D:$i]:
% 0.21/0.45         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.45           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.45         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.45          | (r2_hidden @ X8 @ X5)
% 0.21/0.45          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.45      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.45         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.45      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.45         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.45          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X1 : $i, X3 : $i]:
% 0.21/0.45         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.45      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.21/0.45          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.21/0.45      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.45  thf('8', plain, ($false), inference('demod', [status(thm)], ['0', '7'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
