%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lp54xEE5BR

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:28 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   18 (  20 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    5
%              Number of atoms          :   93 ( 109 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t55_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          & ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t55_zfmisc_1])).

thf('0',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X7 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X7 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    $false ),
    inference(demod,[status(thm)],['5','6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lp54xEE5BR
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:38 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 12 iterations in 0.013s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(t55_zfmisc_1, conjecture,
% 0.23/0.48    (![A:$i,B:$i,C:$i]:
% 0.23/0.48     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.48        ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & 
% 0.23/0.48             ( r2_hidden @ A @ C ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t55_zfmisc_1])).
% 0.23/0.48  thf('0', plain, ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(d2_tarski, axiom,
% 0.23/0.48    (![A:$i,B:$i,C:$i]:
% 0.23/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.23/0.48       ( ![D:$i]:
% 0.23/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.48         (((X5) != (X7))
% 0.23/0.48          | (r2_hidden @ X5 @ X6)
% 0.23/0.48          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.23/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      (![X4 : $i, X7 : $i]: (r2_hidden @ X7 @ (k2_tarski @ X7 @ X4))),
% 0.23/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.23/0.48  thf(t3_xboole_0, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.23/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.23/0.48  thf('3', plain,
% 0.23/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.23/0.48          | ~ (r2_hidden @ X2 @ X3)
% 0.23/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.23/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.48  thf('4', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.48         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.23/0.48          | ~ (r2_hidden @ X1 @ X2))),
% 0.23/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.48  thf('5', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.23/0.48      inference('sup-', [status(thm)], ['0', '4'])).
% 0.23/0.48  thf('6', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('7', plain, ($false), inference('demod', [status(thm)], ['5', '6'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
