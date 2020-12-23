%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7h0EJeNkCb

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    5
%              Number of atoms          :  132 ( 152 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X13 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k2_tarski @ X13 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X10: $i,X13: $i] :
      ( r2_hidden @ X13 @ ( k2_tarski @ X13 @ X10 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X7 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('4',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X7 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7h0EJeNkCb
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:55:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 38 iterations in 0.025s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(t47_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.21/0.48       ( r2_hidden @ A @ C ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.21/0.48          ( r2_hidden @ A @ C ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.21/0.48  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d2_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         (((X11) != (X13))
% 0.21/0.48          | (r2_hidden @ X11 @ X12)
% 0.21/0.48          | ((X12) != (k2_tarski @ X13 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X10 : $i, X13 : $i]: (r2_hidden @ X13 @ (k2_tarski @ X13 @ X10))),
% 0.21/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.48  thf(d3_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X4 @ X7)
% 0.21/0.48          | (r2_hidden @ X4 @ X6)
% 0.21/0.48          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.48         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X7))),
% 0.21/0.48      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (r2_hidden @ X1 @ (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.48          | (r2_hidden @ X0 @ X2)
% 0.21/0.48          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ sk_C_1)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ 
% 0.21/0.48               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '8'])).
% 0.21/0.48  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
