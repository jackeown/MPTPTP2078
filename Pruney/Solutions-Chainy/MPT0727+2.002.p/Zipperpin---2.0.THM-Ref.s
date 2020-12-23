%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MycSaBEm7N

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   22 (  37 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  100 ( 202 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t7_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( r2_hidden @ A @ B )
          & ( r1_tarski @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t7_ordinal1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['0','6'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('9',plain,(
    ~ ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['0','6'])).

thf('11',plain,(
    $false ),
    inference(demod,[status(thm)],['9','10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MycSaBEm7N
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:52:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 8 iterations in 0.009s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(t7_ordinal1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t7_ordinal1])).
% 0.20/0.49  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t28_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.49  thf('3', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(d4_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.49          | (r2_hidden @ X6 @ X4)
% 0.20/0.49          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.49         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | (r2_hidden @ X0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.49  thf('7', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '6'])).
% 0.20/0.49  thf(antisymmetry_r2_hidden, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.20/0.49  thf('9', plain, (~ (r2_hidden @ sk_A @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '6'])).
% 0.20/0.49  thf('11', plain, ($false), inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
