%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YE58zOuO3h

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   21 (  23 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :  119 ( 141 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( ( k3_xboole_0 @ X33 @ ( k1_tarski @ X32 ) )
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('4',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['4'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( X22 = X19 )
      | ( X21
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X19: $i,X22: $i] :
      ( ( X22 = X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_tarski @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YE58zOuO3h
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 43 iterations in 0.024s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(t18_zfmisc_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.47         ( k1_tarski @ A ) ) =>
% 0.21/0.47       ( ( A ) = ( B ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.47            ( k1_tarski @ A ) ) =>
% 0.21/0.47          ( ( A ) = ( B ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.21/0.47         = (k1_tarski @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.21/0.47         = (k1_tarski @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf(l29_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.21/0.47       ( r2_hidden @ B @ A ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X32 : $i, X33 : $i]:
% 0.21/0.47         ((r2_hidden @ X32 @ X33)
% 0.21/0.47          | ((k3_xboole_0 @ X33 @ (k1_tarski @ X32)) != (k1_tarski @ X32)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.47        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.47  thf(d1_tarski, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X22 @ X21)
% 0.21/0.47          | ((X22) = (X19))
% 0.21/0.47          | ((X21) != (k1_tarski @ X19)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X19 : $i, X22 : $i]:
% 0.21/0.47         (((X22) = (X19)) | ~ (r2_hidden @ X22 @ (k1_tarski @ X19)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.47  thf('8', plain, (((sk_A) = (sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.47  thf('9', plain, (((sk_A) != (sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
